/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.LateParentR3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The level-`k` datum of the whole torus lies in the real domain

A6-3 (a), item 1 (the birth-domain transport on the `χ`-support), first step. On the support of the
small-field characteristic function of the whole torus (`Y = univ`, no large-field region) at a
scale `k` whose cube mass is the physical mass (`k > k₀`), the datum `D_k = lift_k ψ_k` of the
background `𝔹_k(W₂(univ))` lies in the real domain `Ψ̃(𝔹_k; 4 (d+1) δ_k)`: the bond, sphere and
direction bounds of `χ_univ ≠ 0` are the landed `parentPsi_pair_over_Y`, `parentPsi_sphere_over_Y`
and `parentPsi_dir_of_chiY_ne_zero`, and no region history enters because every cube is over `Y`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7
  Balaban.SmallField.Def6v2

section Level

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))

/-- **The level-`k` datum of the whole torus in the real domain** (late scales): from
`χ_univ(ψ_k) ≠ 0`, the cube `BgHyp`, and a cube mass equal to the physical mass `ν L^{-2k}`,
`ν > 0`, the field `parentPsi` lies in `Ψ̃(𝔹_k(W₂(univ)); ν L^{-2k}, 4 (d+1) δ_k)` at the unit
vector `h`. -/
theorem inPsiTilde_genW_univ_late (hL : 2 ≤ S.L) {ν : ℝ} (hν : 0 < ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hμ : Cx.cs.mu (j + 1) = sfBgMassAt S.L (j + 1) ν)
    (hχ : Cx.chiY (Set.univ : Set (Torus S.d (n (j + 1)))) ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1))) :
    InPsiTilde (Cx.genW (Set.univ : Set (Torus S.d (n (j + 1)))))
      (sfBgMassAt S.L (j + 1) ν) (4 * (S.d + 1) * Cx.cs.delta (j + 1))
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  have hε : 0 < (S.d + 1) * Cx.cs.delta (j + 1) := by positivity
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  have hm0 : 0 ≤ sfBgMassAt S.L (j + 1) ν := by
    unfold sfBgMassAt physMass; positivity
  have hL1 : 1 ≤ S.L := by omega
  refine ⟨parentPsi_layerConst Cx _ ψk, fun x x' hp => ?_, fun x _ => ?_, fun x hx => ?_, ?_⟩
  · refine (parentPsi_pair_over_Y Cx _ ψk hv hχ hp (Or.inl (Set.mem_univ _))).trans_le ?_
    nlinarith
  · refine (parentPsi_sphere_over_Y Cx _ ψk hv hχ HB (Set.mem_univ _)).trans_le ?_
    nlinarith
  · have hdir := parentPsi_dir_of_chiY_ne_zero Cx hL _ ψk hv hχ hν hμ hx
    have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
    have hmL : sfBgMassAt S.L (j + 1) ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 = ν := physMass_mul_sq _ _
    have h1 : rn (fun i => parentPsi Cx ψk x i - hv i) * Real.sqrt ν < Cx.cs.delta (j + 1) :=
      (lt_div_iff₀ hsq).1 hdir
    have h0 : 0 ≤ rn (fun i => parentPsi Cx ψk x i - hv i) * Real.sqrt ν :=
      mul_nonneg (Real.sqrt_nonneg _) hsq.le
    have h2 : (rn (fun i => parentPsi Cx ψk x i - hv i) * Real.sqrt ν) ^ 2 <
        Cx.cs.delta (j + 1) ^ 2 := pow_lt_pow_left₀ h1 h0 two_ne_zero
    rw [mul_pow, Real.sq_sqrt hν.le] at h2
    refine lt_of_le_of_lt (r3_of_dir hL1 (layerIndex_le_k _ x) (parentPsi Cx ψk x)
      (fun i => hv i) hsum hm0) ?_
    rw [hmL]
    have hd1 : (1 : ℝ) ≤ (S.d + 1) ^ 2 := by nlinarith
    have hδ2 : 0 < Cx.cs.delta (j + 1) ^ 2 := by positivity
    calc 2 * ν * rn (fun i => parentPsi Cx ψk x i - hv i) ^ 2
        = 2 * (rn (fun i => parentPsi Cx ψk x i - hv i) ^ 2 * ν) := by ring
      _ < 2 * Cx.cs.delta (j + 1) ^ 2 := by linarith
      _ ≤ (4 * (S.d + 1) * Cx.cs.delta (j + 1)) ^ 2 := by nlinarith
  · simp only [hsum, sub_self, abs_zero, mul_zero]
    positivity

end Level

end Balaban.LargeField
