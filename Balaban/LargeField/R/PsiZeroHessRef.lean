/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessInput
public import Balaban.Multiscale.ConstraintField

/-!
# The first variation at the reference vector (PSIZERO-HESS §4, row 7)

`blockAvg_sub_le`: the residual `Ψ(x) - Qφ(x)` of a top-layer site is the average over its `k`-block of the
differences `Ψ(y) - φ(y)`, hence bounded by the supremum of these differences.
`firstVar_re_le`: with the residual of every site over a box `Z` bounded by `ρ`, the first variation of a
perturbation `v ∈ SuppSpace Z` is at most `a_k L^{k(d-2)} √|Z| ρ ‖v‖` (the envelope formula (2.6) and the
Cauchy-Schwarz inequality).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Ref

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The residual at a top-layer site is the block average of the differences. -/
theorem residual_vn_le (hk : 1 ≤ k) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer k) {ρ : ℝ}
    (hρ : ∀ y (hy : y ∈ G.blk k x), vn (fun i => φ (⟨y, blk_subset_Ω G hk le_rfl hx hy⟩, i) - D.Ψ y i) ≤ ρ) :
    vn (fun i => D.Ψ x i - blockAvg G φ x i) ≤ ρ := by
  classical
  have hli : G.layerIndex x = k := G.layerIndex_eq hk le_rfl hx
  have hsub := blk_subset_Ω G hk le_rfl hx
  have hcard : ((G.blk k x).card : ℝ) = ((L : ℝ) ^ k) ^ d := by
    rw [card_blk G k le_rfl x]; push_cast; ring
  have hpos : (0 : ℝ) < ((L : ℝ) ^ k) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set c : ℝ := (((L : ℝ) ^ k) ^ d)⁻¹ with hc
  have hΨ : ∀ y ∈ G.blk k x, D.Ψ y = D.Ψ x := fun y hy => D.Ψ_layerConst k hk le_rfl x hx y hy
  have hvec : (WithLp.toLp 2 (fun i => D.Ψ x i - blockAvg G φ x i) : EuclideanSpace ℂ (Fin N)) =
      (c : ℂ) • ∑ y ∈ (G.blk k x).attach, (WithLp.toLp 2 (fun i =>
        D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) : EuclideanSpace ℂ (Fin N)) := by
    ext i
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
    have e1 : ∑ y ∈ (G.blk k x).attach, (D.Ψ (y : Torus d (N₀ * L ^ k)) i -
        φ (⟨y, hsub y.2⟩, i)) = ((G.blk k x).card : ℂ) * D.Ψ x i - ∑ y ∈ G.blk k x, svec G φ y i := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_attach (G.blk k x) (fun y => D.Ψ y i)]
        rw [Finset.sum_congr rfl fun y hy => by rw [hΨ y hy]]
        simp
      · rw [← Finset.sum_attach (G.blk k x) (fun y => svec G φ y i)]
        exact Finset.sum_congr rfl fun y _ => (svec_of_mem G φ ⟨y, hsub y.2⟩ i).symm
    rw [e1]
    unfold blockAvg
    rw [hli]
    have hcq : ((c : ℝ) : ℂ) * ((((L : ℝ) ^ k) ^ d : ℝ) : ℂ) = 1 := by
      rw [hc, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]
    have hcc : ((G.blk k x).card : ℂ) = (((L : ℝ) ^ k) ^ d : ℝ) := by exact_mod_cast hcard
    rw [hcc]
    have hc' : (((((L : ℝ) ^ k) ^ d)⁻¹ : ℝ) : ℂ) = (c : ℂ) := by rw [hc]
    rw [hc']
    linear_combination (-(D.Ψ x i)) * hcq
  have hnorm := calc vn (fun i => D.Ψ x i - blockAvg G φ x i)
      = ‖(WithLp.toLp 2 (fun i => D.Ψ x i - blockAvg G φ x i) : EuclideanSpace ℂ (Fin N))‖ := rfl
    _ = c * ‖∑ y ∈ (G.blk k x).attach, (WithLp.toLp 2 (fun i =>
          D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) : EuclideanSpace ℂ (Fin N))‖ := by
        rw [hvec, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ c * ∑ y ∈ (G.blk k x).attach, ρ := by
        refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun y _ => ?_))
          (by positivity)
        have := hρ y y.2
        calc ‖(WithLp.toLp 2 (fun i => D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) : EuclideanSpace ℂ (Fin N))‖
            = vn (fun i => D.Ψ y i - φ (⟨y, hsub y.2⟩, i)) := rfl
          _ = vn (fun i => φ (⟨y, hsub y.2⟩, i) - D.Ψ y i) := by
              unfold vn
              rw [← norm_neg]
              congr 1
              ext i; simp
          _ ≤ ρ := this
    _ = ρ := by
        rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul, hcard, hc]
        field_simp
  exact hnorm

end Ref

end Balaban.LargeField
