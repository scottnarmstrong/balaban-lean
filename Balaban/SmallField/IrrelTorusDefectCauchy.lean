/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoCtx

/-!
# Cauchy form of the filed term

For a term analytic and bounded on the anisotropic polydisc and a datum with the anisotropic
properties, the filed term `T_X + Φ_{y,X}` of one polymer is bounded by `C M t^4`, `t = 1 + d_j(X)`,
with `C` depending only on `N`, `Λ`, the diameter constant and the linear count constant. The
longitudinal radius `r²` and the transverse radius `r` cancel the denominators of the Cauchy
bounds. No membership of the datum in a domain of terms is used: the datum enters through its
frame, its adjacent differences and its longitudinal field component only.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section Lite

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r A Λ M σ ε K₂ t : ℝ} {X : Finset (Site d)}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}

/-- The second order part `Φ_{y,X}` of the filed term in the anisotropic Cauchy form. -/
theorem norm_phitw_le_of_data (dat : DataHypAniso Dom ν σ ε K₂ ψ b)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hr : 0 < r) (han : AnalyticOnNhd ℂ (T.term X) (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖T.term X c‖ ≤ M)
    (hdiam : ∀ x ∈ X, (l1 x : ℝ) ≤ A * t) :
    ‖Phitw T i₀ i₁ ν X ψ‖ ≤
      (X.card : ℝ) ^ 2 * M * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
  obtain ⟨u, R, fr⟩ := exists_frame i₀ dat.toDataHyp hτ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (refPt_mem_polyAniso hr))
  have hΛ : 0 ≤ Λ := by
    by_contra h
    push Not at h
    nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hσε : σ * ε ≤ Λ * r := by nlinarith
  have hσε0 : 0 ≤ σ * ε := by positivity
  rw [fr.phitw_eq hτ, norm_neg]
  have hrot : ∀ x : Site d, ‖rotDiff R ψ x‖ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := by
    intro x
    have h := norm_mulVec_le (R := R) (B := 40) (by norm_num) (fun i k => by
      have := fr.bd i k; simpa [rotBound] using this) (ψ x - ψ 0)
    have h2 := norm_sub_le_l1 (ψ := ψ) (δ := σ * ε) dat.adj 0 x
    simp only [zero_add] at h2
    unfold rotDiff
    calc ‖R.mulVec (ψ x - ψ 0)‖ ≤ N * 40 * ‖ψ x - ψ 0‖ := h
      _ ≤ N * 40 * ((l1 x : ℝ) * (σ * ε)) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hGm : ∀ μ μ', ‖gradTensor i₀ R ψ μ μ'‖ ≤ N * (N * 40 * (σ * ε)) ^ 2 := by
    intro μ μ'
    have hφ : ∀ ν', ‖rotDiff R ψ (eU ν')‖ ≤ N * 40 * (σ * ε) := fun ν' => by
      have := hrot (eU ν')
      rwa [l1_eU, Nat.cast_one, one_mul] at this
    refine (norm_dotT_le i₀ _ _).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hφ μ) (hφ μ') (norm_nonneg _) (by positivity)) hN
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hcr2 : 0 ≤ 4 * M / r ^ 2 := by positivity
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      wquad (gradTensor i₀ R ψ) x.1 x'.1‖ ≤ (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * M / r ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2)))) := by
    refine norm_sum_le_card _ fun x => ?_
    refine norm_sum_le_card _ fun x' => ?_
    rw [norm_mul]
    refine mul_le_mul (aniso_norm_D2_basis_le hr han hM (anisoWt_inl _) (anisoWt_inl _)) ?_
      (norm_nonneg _) (by positivity)
    refine (norm_wquad_le _ hGm x.1 x'.1).trans ?_
    have hl : (l1 (x.1 - x'.1) : ℝ) ≤ 2 * (A * t) := by
      have := l1_sub_le x.1 x'.1
      have h3 : (l1 (x.1 - x'.1) : ℝ) ≤ l1 x.1 + l1 x'.1 := by exact_mod_cast this
      have h4 := hdiam x.1 x.2
      have h5 := hdiam x'.1 x'.2
      linarith
    have hl0 : (0 : ℝ) ≤ l1 (x.1 - x'.1) := Nat.cast_nonneg _
    have : 0 ≤ (N : ℝ) * (N * 40 * (σ * ε)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 hl 2) this
  unfold Lx
  rw [norm_mul]
  have h2 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [h2, hcard] at *
  have h3 : (N * (N * 40 * (σ * ε)) ^ 2) ≤ (N * (N * 40 * (Λ * r)) ^ 2) := by gcongr
  calc 1 / 4 * ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        wquad (gradTensor i₀ R ψ) x.1 x'.1‖
      ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) *
        (4 * M / r ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (σ * ε)) ^ 2))))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 1 / 4 * ((X.card : ℝ) * ((X.card : ℝ) *
        (4 * M / r ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * (Λ * r)) ^ 2))))) := by gcongr
    _ = (X.card : ℝ) ^ 2 * M * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
        field_simp


/-- The first order part `T_X` of the filed term in the anisotropic Cauchy form. -/
theorem norm_ttw_le_of_data (dat : DataHypAniso Dom ν σ ε K₂ ψ b)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hr : 0 < r) (han : AnalyticOnNhd ℂ (T.term X) (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖T.term X c‖ ≤ M) :
    ‖Ttw T i₀ ν X ψ b‖ ≤ M * (1 + Λ * (X.card : ℝ) + Λ ^ 2) := by
  obtain ⟨u, R, fr⟩ := exists_frame i₀ dat.toDataHyp hτ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (refPt_mem_polyAniso hr))
  have hΛ : 0 ≤ Λ := by
    by_contra h
    push Not at h
    nlinarith
  have hα : ‖uInv ψ - 1‖ ≤ Λ * r := by
    rw [fr.uInv_eq hτ]
    refine fr.u_close.trans ?_
    have h1 : σ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hβ : ‖vInv ψ b - ν‖ ≤ Λ ^ 2 * r ^ 2 := by
    refine dat.b_long.trans ?_
    have h1 : σ ^ 2 ≤ 1 := by nlinarith
    have h2 : ε ^ 2 ≤ (Λ * r) ^ 2 := pow_le_pow_left₀ hε.le hεΛ 2
    calc σ ^ 2 * ε ^ 2 ≤ 1 * ε ^ 2 := by gcongr
      _ ≤ (Λ * r) ^ 2 := by linarith
      _ = _ := by ring
  have hv0 : ‖T.term X (refPt i₀ ν X)‖ ≤ M := hM _ (refPt_mem_polyAniso hr)
  have hs : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ ≤ (X.card : ℝ) * (M / r) := by
    have := norm_sum_le_card _ fun x => aniso_norm_tensA_le hr han hM x
    rwa [Fintype.card_coe] at this
  have hd : ‖fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ ≤ M / r ^ 2 :=
    aniso_norm_fderiv_inr_self_le hr han hM
  unfold Ttw
  calc _ ≤ ‖T.term X (refPt i₀ ν X)‖ + ‖(uInv ψ - 1) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ +
        ‖(vInv ψ b - ν) * fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M + (Λ * r) * ((X.card : ℝ) * (M / r)) + (Λ ^ 2 * r ^ 2) * (M / r ^ 2) := by
        rw [norm_mul, norm_mul]
        gcongr
    _ = M * (1 + Λ * (X.card : ℝ) + Λ ^ 2) := by field_simp

/-- **Cauchy form of the filed term** (`T_X + Φ_{y,X}`): with the linear count bound
`|X| ≤ H t`, `t = 1 + d_j(X) ≥ 1`, the sum is bounded by `C M t^4`, where `M` bounds the term on
the anisotropic polydisc and `C` depends on `N`, `Λ`, `A`, `H` only. -/
theorem norm_ttw_add_phitw_le_of_data (dat : DataHypAniso Dom ν σ ε K₂ ψ b)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hr : 0 < r) (han : AnalyticOnNhd ℂ (T.term X) (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖T.term X c‖ ≤ M)
    (hdiam : ∀ x ∈ X, (l1 x : ℝ) ≤ A * t) (ht : 1 ≤ t) {H : ℝ} (hH : 0 ≤ H)
    (hcard : (X.card : ℝ) ≤ H * t) :
    ‖Ttw T i₀ ν X ψ b + Phitw T i₀ i₁ ν X ψ‖ ≤
      (1 + Λ * H + Λ ^ 2 + H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2)) * (M * t ^ 4) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (refPt_mem_polyAniso hr))
  have hΛ : 0 ≤ Λ := by
    by_contra h
    push Not at h
    nlinarith
  have hc0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have h1 := norm_ttw_le_of_data dat hσ hσ1 hε hεΛ hτ hr han hM
  have h2 := norm_phitw_le_of_data (i₁ := i₁) dat hσ hσ1 hε hεΛ hτ hr han hM hdiam
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht
  have hK : 0 ≤ (N : ℝ) * (N * 40 * Λ) ^ 2 := by positivity
  have e1 : Λ * (X.card : ℝ) ≤ Λ * H * t ^ 4 := by
    calc Λ * (X.card : ℝ) ≤ Λ * (H * t) := by gcongr
      _ = Λ * H * t := by ring
      _ ≤ Λ * H * t ^ 4 := by
        have : t ≤ t ^ 4 := by nlinarith [pow_le_pow_right₀ ht (by norm_num : 1 ≤ 4)]
        have : 0 ≤ Λ * H := by positivity
        nlinarith
  have e2 : (X.card : ℝ) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) ≤
      H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2) * t ^ 4 := by
    calc (X.card : ℝ) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2))
        ≤ (H * t) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
          gcongr
      _ = H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2) * t ^ 4 := by ring
  have e4 : Λ ^ 2 ≤ Λ ^ 2 * t ^ 4 := by nlinarith [sq_nonneg Λ]
  have hsum : M * (1 + Λ * (X.card : ℝ) + Λ ^ 2) +
      (X.card : ℝ) ^ 2 * M * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) ≤
      M * ((1 + Λ * H + Λ ^ 2 + H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2)) * t ^ 4) := by
    have : (X.card : ℝ) ^ 2 * M * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) =
        M * ((X.card : ℝ) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2))) := by ring
    rw [this, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ hM0
    nlinarith
  calc _ ≤ M * ((1 + Λ * H + Λ ^ 2 + H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2)) * t ^ 4) := hsum
    _ = _ := by ring

end Lite

end Balaban.SmallField
