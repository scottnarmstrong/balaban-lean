/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwise

/-!
# Lemma 3.2 (iii): the crude range

For the scales where `σ = C₀ s` is not small the proof of Theorem 2.1 does not apply, and the
source uses the crude bound (Corollary 2.2): `|I| ≤ C E₀ e^{-(κ-1)d_j(X)}`.
`termwise_crude`: this bound holds for `σ ≤ Σ_m` (any fixed `Σ_m`) as soon as `σ² ε ≤ 1/4`; it
uses only `PremisesTerm`, the data conditions (Σ1) (the differences `adj`, the squares `sq`, the
field `b_close`) and the Cauchy estimates; no (Σ2) and no smallness of `σ`.
`termwise_irrelevant_all_scales`: the combination with `termwise_irrelevant_scaled`, the bound
`C_I E₀ s^{d+α₃} e^{-(κ-1)d_j(X)}` for every `0 < s ≤ 1`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

theorem norm_dot_le (v w : Spin N) : ‖dot v w‖ ≤ N * (‖v‖ * ‖w‖) := by
  unfold dot
  calc ‖∑ i, v i * w i‖ ≤ ∑ i, ‖v i * w i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, ‖v‖ * ‖w‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm w i) (norm_nonneg _) (norm_nonneg _)
    _ = N * (‖v‖ * ‖w‖) := by simp

section Crude

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem Sx_le_tw (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A)
    {X : Finset (Site d)} (hX : X ∈ T.polys) (μ ν' : Fin d) :
    ‖Sx T i₀ i₁ ν X μ ν'‖ ≤ (X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
      (2 * (A * (1 + T.dist X))) ^ 2 := by
  have hok := hP.termOK hρ hX
  have hM : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
    fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
  have hd0 : 0 ≤ T.dist X := hP.dist_nonneg X hX
  have hcard : (Fintype.card ↥X : ℝ) = X.card := by simp
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by positivity
  unfold Sx
  have h1 : ‖∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
      ((((x.1 - x'.1) μ : ℤ) : ℂ) * (((x.1 - x'.1) ν' : ℤ) : ℂ))‖ ≤
      (Fintype.card ↥X : ℝ) * ((Fintype.card ↥X : ℝ) *
        (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2 * (2 * (A * (1 + T.dist X))) ^ 2)) := by
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
    exact mul_le_mul (hok.norm_D2_basis_le hM _ _) hz (by positivity) (by positivity)
  rw [hcard] at h1
  refine h1.trans (le_of_eq ?_)
  ring

theorem norm_fwd_le {ψ : Site d → Spin N} {σ ε K₂ : ℝ} {b : Spin N}
    (dat : DataHyp Dom ν σ ε K₂ ψ b) (μ : Fin d) : ‖ψ (eU μ) - ψ 0‖ ≤ σ * ε := by
  simpa [eU] using dat.adj 0 μ

theorem norm_gradInv_le {ψ : Site d → Spin N} {σ ε K₂ : ℝ} {b : Spin N}
    (dat : DataHyp Dom ν σ ε K₂ ψ b) (hg : 9 / 16 ≤ ‖dot (ψ 0) (ψ 0)‖) (μ μ' : Fin d) :
    ‖gradInv ψ μ μ'‖ ≤ (N + 8 * N ^ 2) * (σ * ε) ^ 2 := by
  have hs0 : 0 ≤ σ * ε := le_trans (norm_nonneg _) (norm_fwd_le dat μ)
  have h1 := norm_fwd_le dat μ
  have h2 := norm_fwd_le dat μ'
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have t1 : ‖dot (ψ (eU μ) - ψ 0) (ψ (eU μ') - ψ 0)‖ ≤ N * (σ * ε) ^ 2 := by
    refine (norm_dot_le _ _).trans ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hs0) hn
  have t2 : ‖dot (ψ 0) (ψ (eU μ) - ψ 0)‖ ≤ N * (2 * (σ * ε)) := by
    refine (norm_dot_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul dat.bdd0 h1 (norm_nonneg _) (by norm_num)) hn
  have t3 : ‖dot (ψ 0) (ψ (eU μ') - ψ 0)‖ ≤ N * (2 * (σ * ε)) := by
    refine (norm_dot_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul dat.bdd0 h2 (norm_nonneg _) (by norm_num)) hn
  unfold gradInv
  refine (norm_sub_le _ _).trans ?_
  have t4 : ‖dot (ψ 0) (ψ (eU μ) - ψ 0) * dot (ψ 0) (ψ (eU μ') - ψ 0) / dot (ψ 0) (ψ 0)‖ ≤
      8 * N ^ 2 * (σ * ε) ^ 2 := by
    rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
    have := mul_le_mul t2 t3 (norm_nonneg _) (by positivity)
    nlinarith [sq_nonneg (N * (σ * ε)), norm_nonneg (dot (ψ 0) (ψ 0))]
  linarith

/-- Facts on the frame of the data. -/
theorem crude_frame {ψ : Site d → Spin N} {σ ε K₂ : ℝ} {b : Spin N} (i₀ : Fin N)
    (dat : DataHyp Dom ν σ ε K₂ ψ b) (hτ : σ ^ 2 * ε ≤ 1 / 4) :
    ∃ u : ℂ, uInv ψ = u ∧ u * u = dot (ψ 0) (ψ 0) ∧ ‖u - 1‖ ≤ σ ^ 2 * ε ∧ 3 / 4 ≤ ‖u‖ ∧
      9 / 16 ≤ ‖dot (ψ 0) (ψ 0)‖ := by
  obtain ⟨u, R, hF⟩ := exists_frame i₀ dat hτ
  have hu34 : 3 / 4 ≤ ‖u‖ := by
    have := norm_sub_norm_le (1 : ℂ) u
    rw [norm_sub_rev] at this
    simp at this
    have := hF.u_close
    linarith
  refine ⟨u, hF.uInv_eq hτ, hF.u_sq, hF.u_close, hu34, ?_⟩
  rw [← hF.u_sq, norm_mul]
  nlinarith

theorem crude_beta {ψ : Site d → Spin N} {σ ε K₂ S2 : ℝ} {b : Spin N}
    (dat : DataHyp Dom ν σ ε K₂ ψ b) {u : ℂ} (huU : uInv ψ = u) (hus : u * u = dot (ψ 0) (ψ 0))
    (hu1 : ‖u - 1‖ ≤ σ ^ 2 * ε) (hu34 : 3 / 4 ≤ ‖u‖) (hν : 0 ≤ ν) (hνS : ν ≤ S2) :
    ‖vInv ψ b - ν‖ ≤ (S2 + 3 * N) * (σ ^ 2 * ε) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hu : u ≠ 0 := by
    intro h; rw [h] at hu34; simp at hu34; linarith
  have hτ0 : 0 ≤ σ ^ 2 * ε := le_trans (norm_nonneg _) hu1
  set eb : Spin N := b - (ν : ℂ) • ψ 0 with heb
  have hebn : ‖eb‖ ≤ σ ^ 2 * ε := dat.b_close
  have hb : b = (ν : ℂ) • ψ 0 + eb := by rw [heb]; abel
  have hdot : dot (ψ 0) b = (ν : ℂ) * (u * u) + dot (ψ 0) eb := by
    rw [hb, dot_add_right, dot_smul_right, hus]
  have e1 : vInv ψ b - ν = (ν : ℂ) * (u - 1) + dot (ψ 0) eb / u := by
    unfold vInv
    rw [huU, hdot]
    field_simp
    ring
  rw [e1]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(ν : ℂ) * (u - 1)‖ ≤ S2 * (σ ^ 2 * ε) := by
    rw [norm_mul]
    have hν' : ‖(ν : ℂ)‖ = ν := by simp [abs_of_nonneg hν]
    rw [hν']
    exact mul_le_mul hνS hu1 (norm_nonneg _) (hν.trans hνS)
  have h2 : ‖dot (ψ 0) eb / u‖ ≤ 3 * N * (σ ^ 2 * ε) := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    have h3 := (norm_dot_le (ψ 0) eb).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul dat.bdd0 hebn (norm_nonneg _) (by norm_num)) hn)
    have h4 : 0 ≤ (N : ℝ) * (σ ^ 2 * ε) := mul_nonneg hn hτ0
    nlinarith
  linarith

/-- The ratio bound. -/
theorem crude_ratio {σ ε ρ Λ Sm : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hεΛ : ε ≤ Λ * ρ) (hσ : 0 < σ)
    (hσSm : σ ≤ Sm) : σ ^ 2 * ε / ρ ≤ Sm ^ 2 * Λ := by
  rw [div_le_iff₀ hρ]
  have : σ ^ 2 ≤ Sm ^ 2 := pow_le_pow_left₀ hσ.le hσSm 2
  have hΛ : 0 ≤ Λ := by
    by_contra h; push Not at h; nlinarith
  calc σ ^ 2 * ε ≤ σ ^ 2 * (Λ * ρ) := by gcongr
    _ ≤ Sm ^ 2 * (Λ * ρ) := by gcongr
    _ = Sm ^ 2 * Λ * ρ := by ring

theorem crude_T {T : TermFamily d N} {i₀ i₁ : Fin N} {ρ E₀ κ A K₀ : ℝ}
    (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {ψ : Site d → Spin N} {b : Spin N} {τ B : ℝ}
    (hα : ‖uInv ψ - 1‖ ≤ τ) (hβ : ‖vInv ψ b - ν‖ ≤ B) (hτ : 0 ≤ τ) :
    ‖Ttw T i₀ ν X ψ b‖ ≤ E₀ * Real.exp (-κ * T.dist X) *
      (1 + (X.card : ℝ) * (τ / ρ) + B / ρ) := by
  have hok := hP.termOK hρ hX
  have hMb : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
    fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have b_v0 : ‖T.term X (refPt i₀ ν X)‖ ≤ M := hMb _ (mem_ball_self hρ)
  have b_s : ‖∑ x : ↥X, tensA i₀ ν X (T.term X) x‖ ≤ (X.card : ℝ) * (M / ρ) := by
    have := norm_sum_le_card _ fun x => hok.norm_tensA_le hMb x
    rwa [Fintype.card_coe] at this
  have b_d : ‖fderiv ℂ (T.term X) (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ ≤ M / ρ := by
    have h1 := norm_fderiv_apply_le hρ hok.analytic_ball hMb
      (Pi.single (Sum.inr i₀) (1 : ℂ) : Cfg d N X)
    have h2 := norm_single_one_le (Sum.inr i₀ : Idx d N X)
    refine h1.trans ?_
    calc M * ‖(Pi.single (Sum.inr i₀) (1 : ℂ) : Cfg d N X)‖ / ρ ≤ M * 1 / ρ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hM0) hρ.le
      _ = M / ρ := by rw [mul_one]
  unfold Ttw
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := mul_le_mul hα b_s (norm_nonneg _) hτ
  have h2 := mul_le_mul hβ b_d (norm_nonneg _) (le_trans (norm_nonneg _) hβ)
  have e1 : τ * ((X.card : ℝ) * (M / ρ)) = M * ((X.card : ℝ) * (τ / ρ)) := by
    field_simp
  have e2 : B * (M / ρ) = M * (B / ρ) := by field_simp
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

theorem crude_A {T : TermFamily d N} {i₀ i₁ : Fin N} {ρ E₀ κ A K₀ : ℝ}
    (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ}
    (dat : DataHyp Dom ν σ ε K₂ ψ b) :
    ‖Ax T i₀ ν ψ X‖ ≤ E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) * (σ ^ 2 * ε / ρ)) := by
  have hok := hP.termOK hρ hX
  have hMb : ∀ y ∈ ball (refPt i₀ ν X) ρ, ‖T.term X y‖ ≤ E₀ * Real.exp (-κ * T.dist X) :=
    fun y hy => hP.bdd_tube X hX y (ball_subset_tube i₀ ν ρ X hy)
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
      (Fintype.card ↥X : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε))) := by
    refine norm_sum_le_card _ fun x => ?_
    rw [norm_mul]
    exact mul_le_mul (hok.norm_tensA_le hMb x) (hga x.1) (norm_nonneg _) (by positivity)
  rw [Fintype.card_coe] at h1
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  have e : M * ((X.card : ℝ) * (σ ^ 2 * ε / ρ)) =
      1 / 2 * ((X.card : ℝ) * (M / ρ * (2 * (σ ^ 2 * ε)))) := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

theorem crude_Phi {T : TermFamily d N} {i₀ i₁ : Fin N} {ρ E₀ κ A K₀ : ℝ}
    (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) (hA : 0 ≤ A)
    {X : Finset (Site d)} (hX : X ∈ T.polys) {ψ : Site d → Spin N} {b : Spin N} {σ ε K₂ : ℝ}
    (dat : DataHyp Dom ν σ ε K₂ ψ b) (hg : 9 / 16 ≤ ‖dot (ψ 0) (ψ 0)‖) :
    ‖Phitw T i₀ i₁ ν X ψ‖ ≤ (d : ℝ) ^ 2 * (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2) := by
  unfold Phitw
  rw [norm_mul]
  have h14 : ‖-(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  rw [h14]
  have hterm : ∀ μ μ' : Fin d, ‖gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'‖ ≤
      (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2) := by
    intro μ μ'
    rw [norm_mul]
    have hd0 := hP.dist_nonneg X hX
    exact mul_le_mul (norm_gradInv_le dat hg μ μ') (Sx_le_tw hP hρ hE0 hA hX μ μ')
      (norm_nonneg _) (by positivity)
  have hsum : ‖∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'‖ ≤
      (d : ℝ) * ((d : ℝ) * ((N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2))) := by
    have := norm_sum_le_card (fun μ => ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ')
      (c := (d : ℝ) * ((N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2))) fun μ => by
      have := norm_sum_le_card (fun μ' => gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ')
        (c := (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
      ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
        (2 * (A * (1 + T.dist X))) ^ 2)) (hterm μ)
      simpa using this
    simpa using this
  calc 1 / 4 * ‖∑ μ, ∑ μ', gradInv ψ μ μ' * Sx T i₀ i₁ ν X μ μ'‖
      ≤ 1 / 4 * ((d : ℝ) * ((d : ℝ) * _)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ _ := by
        have : 0 ≤ (d : ℝ) ^ 2 * (N + 8 * (N : ℝ) ^ 2) * (σ * ε) ^ 2 *
          ((X.card : ℝ) ^ 2 * (4 * (E₀ * Real.exp (-κ * T.dist X)) / ρ ^ 2) *
            (2 * (A * (1 + T.dist X))) ^ 2) := by
          have hd0 := hP.dist_nonneg X hX
          positivity
        nlinarith

/-- **Lemma 3.2 (iii), crude range**: for `σ ≤ Σ_m` (any fixed `Σ_m`) and `σ² ε ≤ 1/4`,
`|I(y,X)| ≤ C E₀ e^{-(κ-1) d_j(X)}`. -/
theorem termwise_crude (d N : ℕ) (A Λ Sm : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → 0 < σ → σ ≤ Sm → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨Cw, hCw0, hCw⟩ := weight_absorb A hA d
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hΛ0 : 0 ≤ Λ := by linarith
  set Qm : ℝ := Sm ^ 2 * Λ with hQm
  set c₁ : ℝ := N + 8 * (N : ℝ) ^ 2 with hc₁
  have hQ0 : 0 ≤ Qm := by positivity
  have hc₁0 : 0 ≤ c₁ := by positivity
  set C0 : ℝ := 2 + 2 * Qm + (Sm ^ 2 + 3 * N) * Qm + 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2
    with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨C0 * Cw, by positivity, ?_⟩
  intro T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hρ hρ1 hε hεΛ hσ hσSm hτ hν hνσ hE0
  obtain ⟨u, huU, hus, hu1, hu34, hg⟩ := crude_frame i₀ dat hτ
  have hS2 : ν ≤ Sm ^ 2 := hνσ.trans (pow_le_pow_left₀ hσ.le hσSm 2)
  have hτ0 : 0 ≤ σ ^ 2 * ε := le_trans (norm_nonneg _) (dat.sq 0)
  have hq := crude_ratio hρ hε hεΛ hσ hσSm
  have hq0 : 0 ≤ σ ^ 2 * ε / ρ := by positivity
  have hβ := crude_beta dat huU hus hu1 hu34 hν hS2
  have hbT := crude_T hP hρ hE0 hX (ψ := ψ) (b := b) (τ := σ ^ 2 * ε)
    (B := (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε)) (by rw [huU]; exact hu1) hβ hτ0
  have hbA := crude_A hP hρ hE0 hX dat
  have hbΦ := crude_Phi hP hρ hE0 hA hX dat hg
  have hd0 := hP.dist_nonneg X hX
  have hP1 : (1 : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, hP.zero_mem X hX⟩
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by positivity
  have hcard := card_le_of_diam hP hX
  have hab := hCw κ (T.dist X) (X.card : ℝ) hd0 (Nat.cast_nonneg _) hcard
  -- abbreviations
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
  have hT1 : ‖Ttw T i₀ ν X ψ b‖ ≤ M * (1 + P * Qm + (Sm ^ 2 + 3 * N) * Qm) := by
    refine hbT.trans ?_
    have e : (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε) / ρ = (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε / ρ) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hM0
    have : 0 ≤ Sm ^ 2 + 3 * (N : ℝ) := by positivity
    have h1 : P * (σ ^ 2 * ε / ρ) ≤ P * Qm := mul_le_mul_of_nonneg_left hq (by linarith)
    have h2 : (Sm ^ 2 + 3 * N) * (σ ^ 2 * ε / ρ) ≤ (Sm ^ 2 + 3 * N) * Qm :=
      mul_le_mul_of_nonneg_left hq this
    linarith
  have hA1 : ‖Ax T i₀ ν ψ X‖ ≤ M * (P * Qm) := by
    refine hbA.trans ?_
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by linarith)) hM0
  have hΦ1 : ‖Phitw T i₀ i₁ ν X ψ‖ ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 *
      (M * (P ^ 2 * t ^ 2)) := by
    refine hbΦ.trans ?_
    have hr : (σ * ε) ^ 2 / ρ ^ 2 ≤ Sm ^ 2 * Λ ^ 2 := by
      have hε' : ε / ρ ≤ Λ := by rw [div_le_iff₀ hρ]; linarith
      have e : (σ * ε) ^ 2 / ρ ^ 2 = σ ^ 2 * (ε / ρ) ^ 2 := by field_simp
      rw [e]
      have h1 : σ ^ 2 ≤ Sm ^ 2 := pow_le_pow_left₀ hσ.le hσSm 2
      have h2 : (ε / ρ) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) hε' 2
      exact mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    have e : (d : ℝ) ^ 2 * c₁ * (σ * ε) ^ 2 *
        (P ^ 2 * (4 * M / ρ ^ 2) * (2 * (A * t)) ^ 2) =
        16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) * ((σ * ε) ^ 2 / ρ ^ 2) := by
      field_simp
      ring
    have e' : (1 + T.dist X) = t := rfl
    rw [e'] at *
    rw [e]
    have h16 : 0 ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) := by positivity
    calc _ ≤ 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * (M * (P ^ 2 * t ^ 2)) * (Sm ^ 2 * Λ ^ 2) :=
          mul_le_mul_of_nonneg_left hr h16
      _ = _ := by ring
  -- assemble
  have hsplit : ‖Itw T i₀ i₁ ν X ψ b‖ ≤ ‖T.term X (pack X ψ b)‖ + ‖Ttw T i₀ ν X ψ b‖ +
      ‖Ax T i₀ ν ψ X‖ + ‖Phitw T i₀ i₁ ν X ψ‖ := by
    unfold Itw
    exact ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _)) le_rfl)) le_rfl)).trans (by linarith [norm_nonneg (T.term X (pack X ψ b))])
  have b_e : ‖T.term X (pack X ψ b)‖ ≤ M := hP.bdd_dom X hX (ψ, b) dat.mem
  have hB0 : 0 ≤ Sm ^ 2 + 3 * (N : ℝ) := by positivity
  have x2 : P * M * Qm ≤ (M * (P ^ 2 * t ^ 6)) * Qm := mul_le_mul_of_nonneg_right hPMY hQ0
  have x3 : M * ((Sm ^ 2 + 3 * N) * Qm) ≤ (M * (P ^ 2 * t ^ 6)) * ((Sm ^ 2 + 3 * N) * Qm) :=
    mul_le_mul_of_nonneg_right hMY (by positivity)
  have x4 : 16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 2)) ≤
      16 * (d : ℝ) ^ 2 * c₁ * A ^ 2 * Sm ^ 2 * Λ ^ 2 * (M * (P ^ 2 * t ^ 6)) :=
    mul_le_mul_of_nonneg_left hP2tY (by positivity)
  have e1 : M * (1 + P * Qm + (Sm ^ 2 + 3 * N) * Qm) =
      M + P * M * Qm + M * ((Sm ^ 2 + 3 * N) * Qm) := by ring
  have e2 : M * (P * Qm) = P * M * Qm := by ring
  have hfin : ‖Itw T i₀ i₁ ν X ψ b‖ ≤ C0 * (M * (P ^ 2 * t ^ 6)) := by
    have : C0 * (M * (P ^ 2 * t ^ 6)) =
        2 * (M * (P ^ 2 * t ^ 6)) + 2 * ((M * (P ^ 2 * t ^ 6)) * Qm) +
        (M * (P ^ 2 * t ^ 6)) * ((Sm ^ 2 + 3 * N) * Qm) +
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

/-- **Lemma 3.2 (iii), all scales**: for every `0 < s ≤ 1` (so that also the last `n₁` scales are
covered), with `σ = C₀ s`, `ε/ρ ≤ K_R s^{(d-2)/2 - γ}` and `0 ≤ d + α₃`:
`|I(y,X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`.  For `σ ≤ 1` this is
`termwise_irrelevant_scaled`; for `σ > 1` (`s > 1/C₀`) it is the crude bound `termwise_crude`,
`s^{d+α₃} ≥ C₀^{-(d+α₃)}`. -/
theorem termwise_irrelevant_all_scales (d N : ℕ) (A Λ Ksig α₁ γ C₀ KR : ℝ) (hA : 0 ≤ A)
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hC₀ : 0 < C₀)
    (hα₃ : 0 ≤ (d : ℝ) + (1 - 2 * γ - α₁)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (s σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < s → s ≤ 1 → σ = C₀ * s → ε / ρ ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        CI * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨C1, hC10, hC1⟩ := termwise_irrelevant_scaled d N A Λ Ksig α₁ γ C₀ KR hA hΛ hKsig hα0 hα1 hC₀
  obtain ⟨Cc, hCc0, hCc⟩ := termwise_crude d N A Λ C₀ hA hΛ
  set e : ℝ := (d : ℝ) + (1 - 2 * γ - α₁) with he
  refine ⟨max C1 (Cc * C₀ ^ e), by positivity, ?_⟩
  intro T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hs1 hσs hR hρ hρ1 hε hεΛ hτ hν hνσ hE0 hK
  have hσ : 0 < σ := by rw [hσs]; positivity
  have hse : 0 < s ^ e := Real.rpow_pos_of_pos hs _
  have hEx : 0 ≤ Real.exp (-(κ - 1) * T.dist X) := (Real.exp_pos _).le
  by_cases hσ1 : σ ≤ 1
  · have h := hC1 T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hσs hR hρ hρ1 hε hεΛ hσ1 hτ hν hνσ
      hE0 hK
    refine h.trans ?_
    have : 0 ≤ E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X) := by positivity
    calc C1 * E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)
        = C1 * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) := by ring
      _ ≤ max C1 (Cc * C₀ ^ e) * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  · push Not at hσ1
    have hσm : σ ≤ C₀ := by rw [hσs]; nlinarith
    have h := hCc T i₀ i₁ ν ρ E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hρ hρ1 hε hεΛ hσ hσm hτ hν hνσ hE0
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
      _ = (Cc * C₀ ^ e) * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) := by ring
      _ ≤ max C1 (Cc * C₀ ^ e) * (E₀ * s ^ e * Real.exp (-(κ - 1) * T.dist X)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = _ := by ring

end Crude

end Balaban.SmallField
