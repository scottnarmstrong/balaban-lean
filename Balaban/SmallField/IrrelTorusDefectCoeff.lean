/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusDefectCauchy

/-!
# The coefficient families of the filed term

For a term family with the anisotropic premises, the four coefficient families of the filed term
(the value, the longitudinal spin sum, the longitudinal field derivative and the second moment
tensor, all at the reference point) are summable over the polymers by the counting weight
(`PremisesTermAniso.summable_coeffs`), and the sum over the polymers of the filed term vanishes
when the four coefficient sums vanish (`PremisesTermAniso.tsum_ttw_add_phitw`).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section Coeff

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

/-- The second moment tensor of one polymer is bounded in the anisotropic Cauchy form. -/
theorem PremisesTermAniso.norm_Sx_le (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    (hr : 0 < r) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A) {X : Finset (Site d)} (hX : X ∈ T.polys)
    (μ ν' : Fin d) :
    ‖Sx T i₀ i₁ ν X μ ν'‖ ≤ (X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
      (2 * (A * (1 + T.dist X))) ^ 2 := by
  have han : AnalyticOnNhd ℂ (T.term X) (polyAniso i₀ ν r X) :=
    (hP.analytic X hX).mono polyAniso_subset_tubeAniso
  have hM : ∀ y ∈ polyAniso i₀ ν r X, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
    fun y hy => hP.bdd_tube X hX y (polyAniso_subset_tubeAniso hy)
  have hd0 : 0 ≤ T.dist X := hP.dist_nonneg X hX
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by positivity
  unfold Sx
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      ((((x.1 - x'.1) μ : ℤ) : ℂ) * (((x.1 - x'.1) ν' : ℤ) : ℂ))‖ ≤
      (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2 * (2 * (A * (1 + T.dist X))) ^ 2)) := by
    refine norm_sum_le_card _ fun x => ?_
    refine norm_sum_le_card _ fun x' => ?_
    rw [norm_mul, norm_mul]
    have hl : (l1 (x.1 - x'.1) : ℝ) ≤ 2 * (A * (1 + T.dist X)) := by
      have := l1_sub_le x.1 x'.1
      have h3 : (l1 (x.1 - x'.1) : ℝ) ≤ l1 x.1 + l1 x'.1 := by exact_mod_cast this
      have h4 : (l1 x.1 : ℝ) ≤ A * (1 + T.dist X) := by
        rw [l1_cast]; exact hP.diam X hX x.1 x.2
      have h5 : (l1 x'.1 : ℝ) ≤ A * (1 + T.dist X) := by
        rw [l1_cast]; exact hP.diam X hX x'.1 x'.2
      linarith
    have hc1 := norm_coord_le (x.1 - x'.1) μ
    have hc2 := norm_coord_le (x.1 - x'.1) ν'
    have hl0 : (0 : ℝ) ≤ l1 (x.1 - x'.1) := Nat.cast_nonneg _
    have hz : ‖(((x.1 - x'.1) μ : ℤ) : ℂ)‖ * ‖(((x.1 - x'.1) ν' : ℤ) : ℂ)‖ ≤
        (2 * (A * (1 + T.dist X))) ^ 2 := by
      have h6 : (l1 (x.1 - x'.1) : ℝ) * l1 (x.1 - x'.1) ≤
          (2 * (A * (1 + T.dist X))) * (2 * (A * (1 + T.dist X))) :=
        mul_le_mul hl hl hl0 (by positivity)
      have h7 := mul_le_mul hc1 hc2 (norm_nonneg _) hl0
      nlinarith
    exact mul_le_mul (aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _)) hz
      (by positivity) (by positivity)
  rw [hcard] at h1
  refine h1.trans (le_of_eq ?_)
  ring

/-- The four coefficient families of the filed term are summable over the polymers. -/
theorem PremisesTermAniso.summable_coeffs (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    (hr : 0 < r) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A) :
    Summable (fun X : T.polys => T.term X.1 (refPt i₀ ν X.1)) ∧
    Summable (fun X : T.polys => ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x) ∧
    Summable (fun X : T.polys =>
      fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1)) ∧
    ∀ μ ν' : Fin d, Summable (fun X : T.polys => Sx T i₀ i₁ ν X.1 μ ν') := by
  have hMle : ∀ (X : T.polys) (a k : ℕ), a ≤ 2 → k ≤ 6 →
      (X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * (E₀ * Real.exp (-κ * T.dist X.1)) ≤
        E₀ * wt κ X.1 (T.dist X.1) := by
    intro X a k ha hk
    have := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
      (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) a k ha hk
    calc _ = E₀ * ((X.1.card : ℝ) ^ a * (1 + T.dist X.1) ^ k * Real.exp (-κ * T.dist X.1)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hE0
  have hMb : ∀ X : T.polys, ∀ y ∈ polyAniso i₀ ν r X.1,
      ‖T.term X.1 y‖ ≤ E₀ * Real.exp (-κ * T.dist X.1) := fun X y hy =>
    hP.bdd_tube X.1 X.2 y (polyAniso_subset_tubeAniso hy)
  have han : ∀ X : T.polys, AnalyticOnNhd ℂ (T.term X.1) (polyAniso i₀ ν r X.1) :=
    fun X => (hP.analytic X.1 X.2).mono polyAniso_subset_tubeAniso
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := hP.count_summable
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Summable.of_norm_bounded (hsum.mul_left E₀) fun X => ?_
    have h1 := hMb X (refPt i₀ ν X.1) (refPt_mem_polyAniso hr)
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    exact h1.trans this
  · refine Summable.of_norm_bounded (hsum.mul_left (E₀ / r)) fun X => ?_
    have h1 : ‖∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x‖ ≤
        (Fintype.card ↥X.1 : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / r) :=
      norm_sum_le_card _ fun x => aniso_norm_tensA_le hr (han X) (hMb X) x
    have := hMle X 1 0 (by norm_num) (by norm_num)
    simp only [pow_one, pow_zero, mul_one] at this
    rw [Fintype.card_coe] at h1
    refine h1.trans ?_
    calc (X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1) / r)
        = ((X.1.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X.1))) / r := by ring
      _ ≤ (E₀ * wt κ X.1 (T.dist X.1)) / r := div_le_div_of_nonneg_right this hr.le
      _ = _ := by ring
  · refine Summable.of_norm_bounded (hsum.mul_left (E₀ / r ^ 2)) fun X => ?_
    have h1 := aniso_norm_fderiv_inr_self_le hr (han X) (hMb X)
    have := hMle X 0 0 (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at this
    refine h1.trans ?_
    calc E₀ * Real.exp (-κ * T.dist X.1) / r ^ 2
        ≤ (E₀ * wt κ X.1 (T.dist X.1)) / r ^ 2 :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = _ := by ring
  · intro μ ν'
    refine Summable.of_norm_bounded
      (hsum.mul_left (E₀ * (4 / r ^ 2 * (2 * A) ^ 2))) fun X => ?_
    have h1 := hP.norm_Sx_le hr hE0 hA X.2 μ ν'
    have h2 := hMle X 2 2 le_rfl (by norm_num)
    refine h1.trans ?_
    calc (X.1.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X.1)) / r ^ 2) *
          (2 * (A * (1 + T.dist X.1))) ^ 2
        = (4 / r ^ 2 * (2 * A) ^ 2) * ((X.1.card : ℝ) ^ 2 * (1 + T.dist X.1) ^ 2 *
            (E₀ * Real.exp (-κ * T.dist X.1))) := by ring
      _ ≤ (4 / r ^ 2 * (2 * A) ^ 2) * (E₀ * wt κ X.1 (T.dist X.1)) := by
          have : 0 ≤ (4 / r ^ 2 * (2 * A) ^ 2) := by positivity
          exact mul_le_mul_of_nonneg_left h2 this
      _ = _ := by ring


/-- The filed term of the polymers is summable, and its sum vanishes when the four coefficient
sums vanish (the renormalization conditions and the vanishing second moment matrix). -/
theorem PremisesTermAniso.tsum_ttw_add_phitw (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    (hr : 0 < r) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A)
    (hV : ∑' X : T.polys, T.term X.1 (refPt i₀ ν X.1) = 0)
    (hb : ∑' X : T.polys,
      fderiv ℂ (T.term X.1) (refPt i₀ ν X.1) (Pi.single (Sum.inr i₀) 1) = 0)
    (hpsi : ∑' X : T.polys, ∑ x : ↥X.1, tensA i₀ ν X.1 (T.term X.1) x = 0)
    (hmom : ∀ μ ν' : Fin d, ∑' X : T.polys, Sx T i₀ i₁ ν X.1 μ ν' = 0)
    (ψ : Site d → Spin N) (b : Spin N) :
    Summable (fun X : T.polys => Ttw T i₀ ν X.1 ψ b + Phitw T i₀ i₁ ν X.1 ψ) ∧
    ∑' X : T.polys, (Ttw T i₀ ν X.1 ψ b + Phitw T i₀ i₁ ν X.1 ψ) = 0 := by
  obtain ⟨S_v, S_s, S_d, S_x⟩ := hP.summable_coeffs hr hE0 hA
  have hT : Summable (fun X : T.polys => Ttw T i₀ ν X.1 ψ b) := by
    unfold Ttw
    exact (S_v.add (S_s.mul_left (uInv ψ - 1))).add (S_d.mul_left (vInv ψ b - ν))
  have hP' : Summable (fun X : T.polys => Phitw T i₀ i₁ ν X.1 ψ) := by
    unfold Phitw
    refine Summable.mul_left _ ?_
    refine summable_sum fun μ _ => summable_sum fun μ' _ => ?_
    exact (S_x μ μ').mul_left _
  refine ⟨hT.add hP', ?_⟩
  rw [Summable.tsum_add hT hP']
  have h1 : ∑' X : T.polys, Ttw T i₀ ν X.1 ψ b = 0 := by
    unfold Ttw
    rw [Summable.tsum_add (S_v.add (S_s.mul_left (uInv ψ - 1))) (S_d.mul_left (vInv ψ b - ν)),
      Summable.tsum_add S_v (S_s.mul_left (uInv ψ - 1)), tsum_mul_left, tsum_mul_left,
      hV, hpsi, hb]
    ring
  have h2 : ∑' X : T.polys, Phitw T i₀ i₁ ν X.1 ψ = 0 := by
    unfold Phitw
    rw [tsum_mul_left]
    have : ∑' X : T.polys, ∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X.1 μ μ' = 0 := by
      rw [Summable.tsum_finsetSum (fun μ _ => summable_sum fun μ' _ =>
        (S_x μ μ').mul_left _)]
      refine Finset.sum_eq_zero fun μ _ => ?_
      rw [Summable.tsum_finsetSum (fun μ' _ => (S_x μ μ').mul_left _)]
      refine Finset.sum_eq_zero fun μ' _ => ?_
      rw [tsum_mul_left, hmom μ μ', mul_zero]
    rw [this, mul_zero]
  rw [h1, h2, add_zero]

end Coeff

end Balaban.SmallField
