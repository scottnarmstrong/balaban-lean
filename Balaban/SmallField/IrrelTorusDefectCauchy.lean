/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoCtx

/-!
# Cauchy form of the filed term

For a term family with the anisotropic premises and data in the anisotropic class, the filed
term `T_X + Φ_{y,X}` of one polymer is bounded by `C E₀ (1 + d_j(X))^4 e^{-κ d_j(X)}`, with `C`
depending only on `N`, `Λ`, the diameter constant and the linear count constant. The longitudinal
radius `r²` and the transverse radius `r` cancel the denominators of the Cauchy bounds.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section CtxAniso

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ Λ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem CtxAniso.norm_phitw_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖Phitw T i₀ i₁ ν X ψ‖ ≤
      (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X)) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
  have hr := c.rpos
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  rw [c.frame.phitw_eq c.τle, norm_neg]
  have h := c.Lq_le hX
  have hσε : σ * ε ≤ Λ * r := by
    have := c.σle; have := c.εle; have := c.εpos; nlinarith
  have hσε0 : 0 ≤ σ * ε := by have := c.σpos; have := c.εpos; positivity
  have h3 : (N * (N * 40 * (σ * ε)) ^ 2) ≤ (N * (N * 40 * (Λ * r)) ^ 2) := by
    gcongr
  refine h.trans ?_
  have e : (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X) / r ^ 2) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * (Λ * r)) ^ 2)) =
      (X.card : ℝ) ^ 2 * (E₀ * Real.exp (-κ * T.dist X)) *
        ((2 * (A * (1 + T.dist X))) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by
    field_simp
  rw [← e]
  gcongr


theorem CtxAniso.norm_ttw_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖Ttw T i₀ ν X ψ b‖ ≤
      (E₀ * Real.exp (-κ * T.dist X)) * (1 + Λ * (X.card : ℝ) + Λ ^ 2) := by
  have hr := c.rpos
  have han := c.analytic_poly hX
  have hM := c.hM hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hΛ := c.Λnn
  have hα : ‖uInv ψ - 1‖ ≤ Λ * r := by
    rw [c.uInv_eq]
    refine c.frame.u_close.trans ?_
    have h1 : σ ^ 2 ≤ 1 := by have := c.σle; have := c.σpos; nlinarith
    have := c.εle; have := c.εpos
    nlinarith
  have hβ : ‖vInv ψ b - ν‖ ≤ Λ ^ 2 * r ^ 2 := by
    refine c.dat.b_long.trans ?_
    have h1 : σ ^ 2 ≤ 1 := by have := c.σle; have := c.σpos; nlinarith
    have h2 : ε ^ 2 ≤ (Λ * r) ^ 2 := pow_le_pow_left₀ c.εpos.le c.εle 2
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
`|X| ≤ H (1 + d_j(X))`, the sum is bounded by `C E₀ e^{-κ d_j(X)} (1 + d_j(X))^4`, with `C`
depending on `N, Λ, A, H` only. -/
theorem CtxAniso.norm_ttw_add_phitw_le (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {H : ℝ} (hH : 0 ≤ H)
    (hcard : (X.card : ℝ) ≤ H * (1 + T.dist X)) :
    ‖Ttw T i₀ ν X ψ b + Phitw T i₀ i₁ ν X ψ‖ ≤
      (1 + Λ * H + Λ ^ 2 + H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2)) *
        (E₀ * (1 + T.dist X) ^ 4 * Real.exp (-κ * T.dist X)) := by
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have hΛ := c.Λnn
  have hE := c.E0nn
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hc0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have h1 := c.norm_ttw_le hX
  have h2 := c.norm_phitw_le hX
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
  have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht1
  have hK : 0 ≤ (N : ℝ) * (N * 40 * Λ) ^ 2 := by positivity
  have hcard2 : (X.card : ℝ) ^ 2 ≤ (H * t) ^ 2 := pow_le_pow_left₀ hc0 hcard 2
  have e1 : Λ * (X.card : ℝ) ≤ Λ * H * t ^ 4 := by
    calc Λ * (X.card : ℝ) ≤ Λ * (H * t) := by gcongr
      _ = Λ * H * t := by ring
      _ ≤ Λ * H * t ^ 4 := by
        have : t ≤ t ^ 4 := by nlinarith [pow_le_pow_right₀ ht1 (by norm_num : 1 ≤ 4)]
        have : 0 ≤ Λ * H := by positivity
        nlinarith
  have e2 : (X.card : ℝ) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) ≤
      H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2) * t ^ 4 := by
    calc (X.card : ℝ) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2))
        ≤ (H * t) ^ 2 * ((2 * (A * t)) ^ 2 * (N * (N * 40 * Λ) ^ 2)) := by gcongr
      _ = H ^ 2 * (2 * A) ^ 2 * (N * (N * 40 * Λ) ^ 2) * t ^ 4 := by ring
  have e3 : 1 ≤ t ^ 4 := ht4
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
    _ = _ := by rw [hMdef]; ring

end CtxAniso

end Balaban.SmallField
