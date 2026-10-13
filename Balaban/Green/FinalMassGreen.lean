/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.CoarseOperator
public import Balaban.Green.UnitLattice
public import Balaban.Green.CombesThomas
public import Balaban.Green.BallSums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The massive Green function of the final reference operator (FINAL §3, package 4)

Let `U = unconstrainedUnitOperator d (N₀ L^k) (L^k) N₀ v a` be the scalar Schur-complement
operator on the unit torus `(ℤ/N₀)^d` (fine block size `L^k`, mass `v`, coefficient `a`), viewed
as a complex matrix.  For `0 ≤ v ≤ 1`, `1/2 ≤ a ≤ 2` and `7/(8 L²) < v` we prove

* the gap `Re ⟨u, U u⟩ ≥ g_* ‖u‖²`, `g_* = 7 / (8 L² (8d+3))` (`finalMass_isCoercive`);
* for every `t ≥ 0`, `U + t` is invertible and (for `k ≥ 1`)
  `|(U + t)⁻¹_{xy}| ≤ 2/(g_* + t) · exp(-r_* dist x y)` (`finalMass_resolvent_decay`), with the
  rate `r_* = ctRate (2 + 4 C₀) s_* g_* (ballConst d (s_*/4))` independent of the torus size,
  of `k` and of `t`;
* the same for `U⁻¹` (`finalMass_inverse_decay`).

The distance is the `ℓ¹` torus distance `Green.torusDist` (the metric of `L1Torus`), which is the
one used by `unconstrainedUnitOperator_decay` and by `combesThomas`.

This is the real covariance of the reference operator.  Its identification with the Hessian of the
physical final density (`FINAL-HESSIAN-BRIDGE`), the complex chart, the cut-parameter family
needed for exact locality, and the branch `k_f = 0` are NOT proved here.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

/-- The gap `g_* = 7 / (8 L² (8d+3))` of the final mass operator. -/
noncomputable def finalGap (d L : ℕ) : ℝ := 7 / (8 * (L : ℝ) ^ 2 * (8 * (d : ℝ) + 3))

/-- The entry-decay constant `2 + 4 C₀` of the final mass operator. -/
noncomputable def finalDecayC (d L : ℕ) : ℝ := 2 + 4 * blockDecayConst d L

/-- The Combes–Thomas rate `r_*` of the final mass operator. -/
noncomputable def finalRate (d L : ℕ) : ℝ :=
  ctRate (finalDecayC d L) (blockDecayRate d) (finalGap d L) (ballConst d (blockDecayRate d / 4))

theorem finalGap_pos {d L : ℕ} (hL : 0 < L) : 0 < finalGap d L := by
  unfold finalGap
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

theorem finalDecayC_pos {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 < finalDecayC d L := by
  unfold finalDecayC
  have := blockDecayConst_pos (L := L) hd
  linarith

theorem ballConst_decay_nonneg {d : ℕ} {r : ℝ} (hr : 0 < r) : 0 ≤ ballConst d r := by
  have hq : Real.exp (-r) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h1 : 0 < 1 - Real.exp (-r) := by linarith
  unfold ballConst
  positivity

theorem finalRate_pos {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 < finalRate d L := by
  have hr := blockDecayRate_pos hd
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact ctRate_pos (finalDecayC_pos hd).le hr (finalGap_pos hL)
    (ballConst_decay_nonneg (by positivity))

section Operator

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The operator `U = unconstrainedUnitOperator d (N₀ L^k) (L^k) N₀ v a`, as a complex matrix
indexed by the `ℓ¹` torus (`L1Torus` is `Torus` with the metric `torusDist`). -/
noncomputable abbrev finalOp (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (v a : ℝ) :
    Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  (unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a).map (algebraMap ℝ ℂ)

/-- The real quadratic form of the complexified real matrix `U` is the sum of the real and
imaginary parts' forms. -/
private theorem reQuad_map_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ)
    (v : ι → ℂ) :
    reQuad (U.map (algebraMap ℝ ℂ)) v =
      (fun i => (v i).re) ⬝ᵥ U *ᵥ (fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ U *ᵥ (fun i => (v i).im) := by
  unfold reQuad
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.map_apply, Complex.coe_algebraMap, Complex.star_def, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The real quadratic form of `U` is at least `g_* ‖ψ‖²` in the mass window. -/
theorem finalMass_real_lower (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (ψ : Torus d N₀ → ℝ) :
    finalGap d L * ∑ x, ψ x ^ 2 ≤
      ψ ⬝ᵥ unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a *ᵥ ψ := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have ha0 : 0 < a := by linarith
  have h1 := unconstrainedUnitOperator_lower (ℓ := N₀ * L ^ k) (N := L ^ k) (m := N₀) (mul_comm _ _) hN hd
    hv0 ha0 ψ
  have h2 := unconstrained_gamma_ge (d := d) hv0 hv1 ha
  have hE : 0 ≤ latticeEnergy ψ := latticeEnergy_nonneg ψ
  have hS : 0 ≤ ∑ x, ψ x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hv : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ * ∑ x, ψ x ^ 2 ≤ latticeEnergy ψ + v * ∑ x, ψ x ^ 2 := by
    nlinarith
  have hg : finalGap d L = 1 / (8 * (d : ℝ) + 3) * (7 / 8 * ((L : ℝ) ^ 2)⁻¹) := by
    unfold finalGap; field_simp
  refine le_trans ?_ h1
  rw [hg, mul_assoc]
  calc 1 / (8 * (d : ℝ) + 3) * (7 / 8 * ((L : ℝ) ^ 2)⁻¹ * ∑ x, ψ x ^ 2)
      ≤ 1 / (8 * (d : ℝ) + 3) * (latticeEnergy ψ + v * ∑ x, ψ x ^ 2) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ a / (a + 4 * d + v) * (latticeEnergy ψ + v * ∑ x, ψ x ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)

/-- **Gap** (T2): `Re ⟨u, U u⟩ ≥ g_* ‖u‖²` for complex fields `u`, in the form `IsCoercive`. -/
theorem finalMass_isCoercive (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) :
    IsCoercive (finalOp d L N₀ k v a) (finalGap d L) := by
  intro u
  have hre := finalMass_real_lower (k := k) (L := L) hd hv0 hv1 ha hmass (fun i => (u i).re)
  have him := finalMass_real_lower (k := k) (L := L) hd hv0 hv1 ha hmass (fun i => (u i).im)
  have e0 : reQuad (finalOp d L N₀ k v a) u =
      (fun i => (u i).re) ⬝ᵥ unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a *ᵥ
        (fun i => (u i).re) +
      (fun i => (u i).im) ⬝ᵥ unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a *ᵥ
        (fun i => (u i).im) := reQuad_map_ofReal _ u
  rw [e0]
  have e : sqNorm u = ∑ x, (u x).re ^ 2 + ∑ x, (u x).im ^ 2 := by
    unfold sqNorm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [e, mul_add]
  exact add_le_add hre him

/-- The shared entry-decay and ball-sum hypotheses of `combesThomas` for the final operator. -/
theorem finalMass_entry_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (x y : L1Torus d N₀) :
    ‖finalOp d L N₀ k v a x y‖ ≤
      finalDecayC d L * Real.exp (-blockDecayRate d * dist x y) := by
  have h := unconstrainedUnitOperator_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2 x y
  rw [dist_L1Torus, neg_mul]
  have e : finalOp d L N₀ k v a x y =
      ((unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a x y : ℝ) : ℂ) := rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  simpa [finalDecayC] using h

/-- **Resolvent decay (F.4)** (T3): for `k ≥ 1`, `0 ≤ v ≤ 1`, `1/2 ≤ a ≤ 2`,
`7/(8L²) < v` and every `t ≥ 0`, `U + t` is invertible and
`|(U + t)⁻¹_{xy}| ≤ 2/(g_* + t) · exp(-r_* dist x y)`, with `g_*`, `r_*` independent of the torus
size `N₀`, of `k`, of `v`, `a` and of `t`. -/
theorem finalMass_resolvent_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) :
    IsUnit ((finalOp d L N₀ k v a) + (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)) ∧
      ∀ x y : L1Torus d N₀,
        ‖((finalOp d L N₀ k v a) + (t : ℂ) •
            (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y‖ ≤
          2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hr := blockDecayRate_pos hd
  have hK : ∀ x : L1Torus d N₀, ∑ y, Real.exp (-(blockDecayRate d / 4) * dist x y) ≤
      ballConst d (blockDecayRate d / 4) := fun x => ballSum_L1Torus (d := d) (m := N₀) (by positivity) x
  have hκ : 0 ≤ ballConst d (blockDecayRate d / 4) := ballConst_decay_nonneg (by positivity)
  have := combesThomas (c₀ := finalDecayC d L) (δ₀ := blockDecayRate d) (γ₀ := finalGap d L)
    (κ := ballConst d (blockDecayRate d / 4)) (finalDecayC_pos hd).le hr (finalGap_pos hL) hκ
    (finalMass_entry_decay hd hk hv0 ha1 ha2) hK
    (finalMass_isCoercive hd hv0 hv1 ha1 hmass) ht
  refine ⟨this.1, fun x y => ?_⟩
  have h := this.2 x y
  exact h.trans_eq (by simp only [finalRate, div_eq_mul_inv])

/-- **Inverse decay** (T4): `|(U⁻¹)_{xy}| ≤ (2/g_*) exp(-r_* dist x y)`. -/
theorem finalMass_inverse_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (x y : L1Torus d N₀) :
    ‖((finalOp d L N₀ k v a))⁻¹ x y‖ ≤
      2 / finalGap d L * Real.exp (-finalRate d L * dist x y) := by
  have h := (finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
    (le_refl (0 : ℝ))).2 x y
  simpa using h

end Operator

end Balaban.Green
