/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoIrrel
public import Balaban.SmallField.RenormTermwiseCrude

/-!
# Lemma 3.2 (iii) on the anisotropic domain, all scales

* `termwise_crude_aniso`: the crude bound `|I(y,X)| ≤ C E₀ e^{-(κ-1) d_j(X)}` on the anisotropic
  domain for `σ ≤ Σ_m` (any fixed `Σ_m`), as soon as `σ² ε ≤ 1/4`; the longitudinal field
  derivative costs `1/r²` and is compensated by the longitudinal bound `b_long` of
  `DataHypAniso`;
* `termwise_irrelevant_aniso_all_scales`: the combination with `termwise_irrelevant_aniso_scaled`,
  the bound `C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}` for every `0 < s ≤ 1`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

section CrudeA

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem PremisesTermAniso.bdd_poly (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ∀ y ∈ polyAniso i₀ ν r X, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
  fun y hy => hP.bdd_tube X hX y (polyAniso_subset_tubeAniso hy)

theorem PremisesTermAniso.analytic_poly (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    AnalyticOnNhd ℂ (T.term X) (polyAniso i₀ ν r X) :=
  (hP.analytic X hX).mono polyAniso_subset_tubeAniso

theorem Sx_le_aniso (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (hr : 0 < r)
    (hE0 : 0 ≤ E₀) (hA : 0 ≤ A) {X : Finset (Site d)} (hX : X ∈ T.polys) (μ ν' : Fin d) :
    ‖Sx T i₀ i₁ ν X μ ν'‖ ≤ (X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
      (2 * (A * (1 + T.dist X))) ^ 2 := by
  have han := hP.analytic_poly hX
  have hM := hP.bdd_poly hX
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

theorem crude_T_aniso (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (hr : 0 < r)
    (hE0 : 0 ≤ E₀) {X : Finset (Site d)} (hX : X ∈ T.polys) {ψ : Site d → Spin N} {b : Spin N}
    {τ B : ℝ} (hα : ‖uInv ψ - 1‖ ≤ τ) (hβ : ‖vInv ψ b - ν‖ ≤ B) (hτ : 0 ≤ τ) :
    ‖Ttw T i₀ ν X ψ b‖ ≤ E₀ * Real.exp (-κ * T.dist X) *
      (1 + (X.card : ℝ) * (τ / r) + B / r ^ 2) := by
  have han := hP.analytic_poly hX
  have hMb := hP.bdd_poly hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have b_v0 : ‖T.term X (refPt i₀ ν X)‖ ≤ M := hMb _ (refPt_mem_polyAniso hr)
  have b_s : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ ≤ (X.card : ℝ) * (M / r) := by
    have := norm_sum_le_card _ fun x => aniso_norm_tensA_le hr han hMb x
    rwa [Fintype.card_coe] at this
  have b_d : ‖fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ ≤ M / r ^ 2 :=
    aniso_norm_fderiv_inr_self_le hr han hMb
  unfold Ttw
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := mul_le_mul hα b_s (norm_nonneg _) hτ
  have h2 := mul_le_mul hβ b_d (norm_nonneg _) (le_trans (norm_nonneg _) hβ)
  have e1 : τ * ((X.card : ℝ) * (M / r)) = M * ((X.card : ℝ) * (τ / r)) := by
    field_simp
  have e2 : B * (M / r ^ 2) = M * (B / r ^ 2) := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

theorem crude_A_aniso (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (hr : 0 < r)
    (hE0 : 0 ≤ E₀) {X : Finset (Site d)} (hX : X ∈ T.polys) {ψ : Site d → Spin N} {b : Spin N}
    {σ ε K₂ : ℝ} (dat : DataHyp Dom ν σ ε K₂ ψ b) :
    ‖Ax T i₀ ν ψ X‖ ≤ E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) * (σ ^ 2 * ε / r)) := by
  have han := hP.analytic_poly hX
  have hMb := hP.bdd_poly hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hτ0 : 0 ≤ σ ^ 2 * ε := le_trans (norm_nonneg _) (dat.sq 0)
  have hga : ∀ x, ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖ ≤ 2 * (σ ^ 2 * ε) := by
    intro x
    have h1 := dat.sq x
    have h2 := dat.sq 0
    calc ‖dot (ψ x) (ψ x) - dot (ψ 0) (ψ 0)‖
        = ‖(dot (ψ x) (ψ x) - 1) - (dot (ψ 0) (ψ 0) - 1)‖ := by ring_nf
      _ ≤ ‖dot (ψ x) (ψ x) - 1‖ + ‖dot (ψ 0) (ψ 0) - 1‖ := norm_sub_le _ _
      _ ≤ 2 * (σ ^ 2 * ε) := by linarith
  unfold Ax
  rw [norm_mul]
  have h1 : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))‖ ≤
      (Fintype.card ↥X : ℝ) * (M / r * (2 * (σ ^ 2 * ε))) := by
    refine norm_sum_le_card _ fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (aniso_norm_tensA_le hr han hMb x) (hga x.1) (norm_nonneg _) (by positivity)
  rw [Fintype.card_coe] at h1
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  have e : M * ((X.card : ℝ) * (σ ^ 2 * ε / r)) =
      1 / 2 * ((X.card : ℝ) * (M / r * (2 * (σ ^ 2 * ε)))) := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

theorem crude_Phi_aniso (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (hr : 0 < r)
    (hE0 : 0 ≤ E₀) (hA : 0 ≤ A) {X : Finset (Site d)} (hX : X ∈ T.polys)
    {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ} (dat : DataHyp Dom ν σ ε K₂ ψ b)
    (hg : 9 / 16 ≤ ‖dot (ψ 0) (ψ 0)‖) :
    ‖Phitw T i₀ i₁ ν X ψ‖ ≤ (d : ℝ) ^ 2 * (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2) := by
  unfold Phitw
  rw [norm_mul]
  have h14 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [h14]
  have hterm : ∀ μ μ' : Fin d, ‖gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'‖ ≤
      (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2) := by
    intro μ μ'
    rw [norm_mul]
    have hd0 := hP.dist_nonneg X hX
    exact mul_le_mul (norm_gradInv_le dat hg μ μ') (Sx_le_aniso hP hr hE0 hA hX μ μ')
      (norm_nonneg _) (by positivity)
  have hsum : ‖∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'‖ ≤
      (d : ℝ) * ((d : ℝ) * ((N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2))) := by
    have := norm_sum_le_card (fun μ => ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ')
      (c := (d : ℝ) * ((N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2))) fun μ => by
      have := norm_sum_le_card (fun μ' => gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ')
        (c := (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2)) (hterm μ)
      simpa using this
    simpa using this
  calc 1 / 4 * ‖∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'‖
      ≤ 1 / 4 * ((d : ℝ) * ((d : ℝ) * _)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ _ := by
        have : 0 ≤ (d : ℝ) ^ 2 * (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
          ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / r ^ 2) *
            (2 * (A * (1 + T.dist X))) ^ 2) := by
          have hd0 := hP.dist_nonneg X hX
          positivity
        nlinarith

/-- **Lemma 3.2 (iii), crude range, anisotropic domain**: for `σ ≤ Σ_m` (any fixed `Σ_m`) and
`σ² ε ≤ 1/4`, `|I(y,X)| ≤ C E₀ e^{-(κ-1) d_j(X)}`. -/
theorem termwise_crude_aniso (d N : ℕ) (A Λ Sm : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < r → 0 < ε → ε ≤ Λ * r → 0 < σ → σ ≤ Sm → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ E₀ →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨Cw, hCw0, hCw⟩ := weight_absorb A hA d
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hΛ0 : 0 ≤ Λ := by linarith
  set Qm : ℝ := Sm ^ 2 * Λ with hQm
  set Qb : ℝ := Sm ^ 2 * Λ ^ 2 with hQb
  set c₁ : ℝ := N + 8 * (N : ℝ) ^ 2 with hc₁
  have hQ0 : 0 ≤ Qm := by positivity
  have hQb0 : 0 ≤ Qb := by positivity
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C0 : ℝ := 2 + 2 * Qm + Qb + 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0 * Cw, by positivity, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hε hεΛ hσ hσSm hτ hE0
  obtain ⟨u, huU, hus, hu1, hu34, hg⟩ := crude_frame i₀ dat.toDataHyp hτ
  have hτ0 : 0 ≤ σ ^ 2 * ε := le_trans (norm_nonneg _) (dat.sq 0)
  have hq := crude_ratio hr hε hεΛ hσ hσSm
  have hq0 : 0 ≤ σ ^ 2 * ε / r := by positivity
  have hεr : ε / r ≤ Λ := by rw [div_le_iff₀ hr]; linarith
  have hβ : ‖vInv ψ b - ν‖ ≤ σ ^ 2 * ε ^ 2 := dat.b_long
  have hbT := crude_T_aniso hP hr hE0 hX (ψ := ψ) (b := b) (τ := σ ^ 2 * ε)
    (B := σ ^ 2 * ε ^ 2) (by rw [huU]; exact hu1) hβ hτ0
  have hbA := crude_A_aniso hP hr hE0 hX dat.toDataHyp
  have hbΦ := crude_Phi_aniso hP hr hE0 hA hX dat.toDataHyp hg
  have hd0 := hP.dist_nonneg X hX
  have hP1 : (1 : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hP.zero_mem X hX⟩
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by positivity
  have hcard := card_le_of_diam_aniso hP hX
  have hab := hCw κ (T.dist X) (X.card : ℝ) hd0 (Nat.cast_nonneg _) hcard
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  set P : ℝ := (X.card : ℝ) with hPdef
  set t : ℝ := 1 + T.dist X with htdef
  have ht1 : 1 ≤ t := by rw [htdef]; linarith
  have hP2 : 1 ≤ P ^ 2 := one_le_pow₀ hP1
  have ht6 : 1 ≤ t ^ 6 := one_le_pow₀ ht1
  have hW : 1 ≤ P ^ 2 * t ^ 6 := one_le_mul_of_one_le_of_one_le hP2 ht6
  have hMY : M ≤ M * (P ^ 2 * t ^ 6) := le_mul_of_one_le_right hM0 hW
  have hPMY : P * M ≤ M * (P ^ 2 * t ^ 6) := by
    have h1 : P ≤ P ^ 2 := le_self_pow₀ hP1 (by norm_num)
    have h2 : P ^ 2 ≤ P ^ 2 * t ^ 6 := le_mul_of_one_le_right (by positivity) ht6
    calc P * M = M * P := mul_comm _ _
      _ ≤ M * (P ^ 2 * t ^ 6) := mul_le_mul_of_nonneg_left (h1.trans h2) hM0
  have hP2tY : M * (P ^ 2 * t ^ 2) ≤ M * (P ^ 2 * t ^ 6) := by
    have : P ^ 2 * t ^ 2 ≤ P ^ 2 * t ^ 6 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by norm_num)) (by positivity)
    exact mul_le_mul_of_nonneg_left this hM0
  have hY0 : 0 ≤ M * (P ^ 2 * t ^ 6) := by positivity
  -- T
  have hB1 : σ ^ 2 * ε ^ 2 / r ^ 2 ≤ Qb := by
    have e : σ ^ 2 * ε ^ 2 / r ^ 2 = σ ^ 2 * (ε / r) ^ 2 := by field_simp
    rw [e]
    have h1 : σ ^ 2 ≤ Sm ^ 2 := pow_le_pow_left₀ hσ.le hσSm 2
    have h2 : (ε / r) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) hεr 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
  have hT1 : ‖Ttw T i₀ ν X ψ b‖ ≤ M * (1 + P * Qm + Qb) := by
    refine hbT.trans ?_
    apply mul_le_mul_of_nonneg_left _ hM0
    have h1 : P * (σ ^ 2 * ε / r) ≤ P * Qm := mul_le_mul_of_nonneg_left hq (by linarith)
    linarith
  have hA1 : ‖Ax T i₀ ν ψ X‖ ≤ M * (P * Qm) := by
    refine hbA.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by linarith)) hM0
  have hΦ1 : ‖Phitw T i₀ i₁ ν X ψ‖ ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 *
      (M * (P ^ 2 * t ^ 2)) := by
    refine hbΦ.trans ?_
    have hr' : (σ * ε) ^ 2 / r ^ 2 ≤ Sm ^ 2 * Λ ^ 2 := by
      have e : (σ * ε) ^ 2 / r ^ 2 = σ ^ 2 * (ε / r) ^ 2 := by field_simp
      rw [e]
      have h1 : σ ^ 2 ≤ Sm ^ 2 := pow_le_pow_left₀ hσ.le hσSm 2
      have h2 : (ε / r) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) hεr 2
      exact mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    have e : (d : ℝ) ^ 2 * c₁ * (σ * ε) ^ 2 *
        (P ^ 2 * (4 * M / r ^ 2) * (2 * (A * t)) ^ 2) =
        16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) * ((σ * ε) ^ 2 / r ^ 2) := by
      field_simp
      ring
    have e' : (1 + T.dist X) = t := rfl
    rw [e'] at *
    rw [e]
    have h16 : 0 ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) := by positivity
    calc _ ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) * (Sm ^ 2 * Λ ^ 2) :=
          mul_le_mul_of_nonneg_left hr' h16
      _ = _ := by ring
  have hsplit : ‖Itw T i₀ i₁ ν X ψ b‖ ≤ ‖T.term X (pack X ψ b)‖ + ‖Ttw T i₀ ν X ψ b‖ +
      ‖Ax T i₀ ν ψ X‖ + ‖Phitw T i₀ i₁ ν X ψ‖ := by
    unfold Itw
    exact ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _)) le_rfl)) le_rfl)).trans
      (by linarith [norm_nonneg (T.term X (pack X ψ b))])
  have b_e : ‖T.term X (pack X ψ b)‖ ≤ M := hP.bdd_dom X hX (ψ, b) dat.mem
  have x2 : P * M * Qm ≤ (M * (P ^ 2 * t ^ 6)) * Qm := mul_le_mul_of_nonneg_right hPMY hQ0
  have x3 : M * Qb ≤ (M * (P ^ 2 * t ^ 6)) * Qb := mul_le_mul_of_nonneg_right hMY hQb0
  have x4 : 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 2)) ≤
      16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 6)) :=
    mul_le_mul_of_nonneg_left hP2tY (by positivity)
  have e1 : M * (1 + P * Qm + Qb) = M + P * M * Qm + M * Qb := by ring
  have e2 : M * (P * Qm) = P * M * Qm := by ring
  have hfin : ‖Itw T i₀ i₁ ν X ψ b‖ ≤ C0 * (M * (P ^ 2 * t ^ 6)) := by
    have : C0 * (M * (P ^ 2 * t ^ 6)) =
        2 * (M * (P ^ 2 * t ^ 6)) + 2 * ((M * (P ^ 2 * t ^ 6)) * Qm) +
        (M * (P ^ 2 * t ^ 6)) * Qb +
        16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 6)) := by
      rw [hC0]; ring
    rw [this]
    rw [e1] at hT1
    rw [e2] at hA1
    linarith
  calc ‖Itw T i₀ i₁ ν X ψ b‖ ≤ C0 * (M * (P ^ 2 * t ^ 6)) := hfin
    _ = C0 * E₀ * (Real.exp (-κ * T.dist X) * (P ^ 2 * t ^ 6)) := by rw [hMdef]; ring
    _ ≤ C0 * E₀ * (Cw * Real.exp (-(κ - 1) * T.dist X)) := by
        have : 0 ≤ C0 * E₀ := mul_nonneg hC00 hE0
        exact mul_le_mul_of_nonneg_left hab this
    _ = _ := by ring

/-- **Lemma 3.2 (iii) on the anisotropic domain, all scales**: for every `0 < s ≤ 1` (so that also
the last `n₁` scales are covered), with `σ = C₀ s`, `ε/r ≤ K_R s^{(d-2)/2 - γ}` and
`0 ≤ d + α₃`: `|I(y,X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`. -/
theorem termwise_irrelevant_aniso_all_scales (d N : ℕ) (A Λ Ksig α₁ γ C₀ KR : ℝ) (hA : 0 ≤ A)
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hC₀ : 0 < C₀)
    (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (s σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d))
      (_ : X ∈ T.polys),
      0 < s → s ≤ 1 → σ = C₀ * s → ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        CI * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨C1, hC10, hC1⟩ := termwise_irrelevant_aniso_scaled d N A Λ Ksig α₁ γ C₀ KR hA hΛ hKsig
    hα0 hα1 hC₀
  obtain ⟨Cc, hCc0, hCc⟩ := termwise_crude_aniso d N A Λ C₀ hA hΛ
  set e : ℝ := (d : ℝ) + (1 - 2 * γ - α₁) with he
  refine ⟨max C1 (Cc * C₀ ^ e), by positivity, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hs1 hσs hR hr hr1 hε hεΛ hτ hν hνσ
    hE0 hK
  have hσ : 0 < σ := by rw [hσs]; positivity
  have hse : 0 < s ^ e := Real.rpow_pos_of_pos hs _
  have hEx : 0 ≤ Real.exp (-(κ - 1) * T.dist X) := (Real.exp_pos _).le
  by_cases hσ1 : σ ≤ 1
  · have h := hC1 T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hσs hR hr hr1 hε hεΛ hσ1 hτ
      hν hνσ hE0 hK
    refine h.trans ?_
    have : 0 ≤ E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X) := by positivity
    calc C1 * E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)
        = C1 * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) := by ring
      _ ≤ max C1 (Cc * C₀ ^ e) * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  · push Not at hσ1
    have hσm : σ ≤ C₀ := by rw [hσs]; nlinarith
    have h := hCc T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hε hεΛ hσ hσm hτ hE0
    refine h.trans ?_
    have hs0 : 1 / C₀ < s := by
      rw [div_lt_iff₀ hC₀]; rw [hσs] at hσ1; linarith
    have h1 : 1 ≤ C₀ ^ e * s ^ e := by
      rw [← Real.mul_rpow hC₀.le hs.le]
      exact Real.one_le_rpow (by rw [div_lt_iff₀ hC₀] at hs0; nlinarith) hα₃
    have : 0 ≤ Cc * E₀ * Real.exp (-(κ - 1) * T.dist X) := by positivity
    calc Cc * E₀ * Real.exp (-(κ - 1) * T.dist X)
        ≤ Cc * E₀ * Real.exp (-(κ - 1) * T.dist X) * (C₀ ^ e * s ^ e) :=
          le_mul_of_one_le_right this h1
      _ = Cc * C₀ ^ e * E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X) := by ring
      _ ≤ max C1 (Cc * C₀ ^ e) * E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X) := by
          have : 0 ≤ E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X) := by positivity
          calc Cc * C₀ ^ e * E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)
              = (Cc * C₀ ^ e) * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) := by ring
            _ ≤ max C1 (Cc * C₀ ^ e) * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) this
            _ = _ := by ring

end CrudeA

end Balaban.SmallField
