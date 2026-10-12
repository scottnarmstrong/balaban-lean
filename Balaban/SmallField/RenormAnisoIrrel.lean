/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoCtx
public import Balaban.SmallField.RenormTermwiseIrrel

/-!
# Lemma 3.2 (iii) on the anisotropic domain: the termwise irrelevance bound

* `smallBndA_le`, `tailBndA_le`: the real inequalities for the explicit bounds of
  `CtxAniso.small_case` and `CtxAniso.tail_case` (the landed `smallBnd_le`, `tailBnd_le` with the
  gauge constant `C₁ + Λ` in place of `C₁`);
* `CtxAniso.itw_bound_raw_aniso`: the per-term bound before the polynomial weight is absorbed;
* `termwise_irrelevant_aniso`: under `PremisesTermAniso` (analyticity and the bound on
  `TubeAniso i₀ ν r X`, spin radius `r`, longitudinal field radius `r²`) and `DataHypAniso`,
  `‖I(y,X)‖ ≤ C E₀ e^{-(κ-1) d_j(X)} σ^{3-α₁} (ε/r)²`;
* `termwise_irrelevant_aniso_scaled`: with `σ = C₀ s` and the source scale ratio
  `ε/r ≤ K_R s^{(d-2)/2 - γ}`, the bound `C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`, `α₃ = 1 - 2γ - α₁`.

With `r ≍ ε_j` (the class radius) and `ε = ε_k`, this is P1 Lemma 3.8 / Proposition 3.10
termwise: `|I(y,X)| ≤ C E₀ σ^{3-α₁} (ε_k/ε_j)² e^{-(κ-1) d_j(X)}`.
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-! ### Real inequalities -/

section Num

variable {N : ℕ} {A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ}

theorem NumCtx.t1A (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    2 * M * ((sZ0A N Λ σ (r * ρ) + sD N A σ (r * ρ) t) / ρ) ^ 3 ≤
      2 * (cZA N Λ + cK1 N A) ^ 3 * Λ * sizeY M P t Tσ r := by
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N (by linarith [h.hΛ])
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := h.hA; positivity
  have eq : (sZ0A N Λ σ (r * ρ) + sD N A σ (r * ρ) t) / ρ =
      (cZA N Λ * σ ^ 2 + cK1 N A * t * σ) * r := by
    have := h.hρ
    unfold sZ0A sD; field_simp
  rw [eq]
  have h1 := zr_le (κ1 := cK1 N A) hCZ h.hS.pos h.hS.le_one h.ht h.hr
  have hM := h.hM
  have h0 : 0 ≤ (cZA N Λ * σ ^ 2 + cK1 N A * t * σ) * r := by
    have := h.hS.pos; have := h.hr
    have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
    positivity
  calc 2 * M * ((cZA N Λ * σ ^ 2 + cK1 N A * t * σ) * r) ^ 3
      ≤ 2 * M * (((cZA N Λ + cK1 N A) * r * σ * t)) ^ 3 := by gcongr
    _ ≤ _ := cube_term (c := cZA N Λ + cK1 N A) (Λ := Λ) (M := M) (r := r) (σ := σ) (t := t)
          (P := P) (Tσ := Tσ) (by positivity) h.hM h.hr h.hrΛ h.hS.pos h.hS.cube h.ht h.hP

theorem NumCtx.t2A (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    2 * M * (sZ0A N Λ σ (r * ρ) / ρ) ^ 3 ≤
      2 * (cZA N Λ + cK1 N A) ^ 3 * Λ * sizeY M P t Tσ r := by
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N (by linarith [h.hΛ])
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := h.hA; positivity
  have eq : sZ0A N Λ σ (r * ρ) / ρ = cZA N Λ * σ ^ 2 * r := by
    have := h.hρ
    unfold sZ0A; field_simp
  rw [eq]
  have h1 := z0r_le (κ1 := cK1 N A) hCZ hK1 h.hS.pos h.hS.le_one h.ht h.hr
  have hM := h.hM
  have h0 : 0 ≤ cZA N Λ * σ ^ 2 * r := by
    have := h.hS.pos; have := h.hr; positivity
  calc 2 * M * (cZA N Λ * σ ^ 2 * r) ^ 3
      ≤ 2 * M * (((cZA N Λ + cK1 N A) * r * σ * t)) ^ 3 := by gcongr
    _ ≤ _ := cube_term (c := cZA N Λ + cK1 N A) (Λ := Λ) (M := M) (r := r) (σ := σ) (t := t)
          (P := P) (Tσ := Tσ) (by positivity) h.hM h.hr h.hrΛ h.hS.pos h.hS.cube h.ht h.hP

theorem NumCtx.t3A (h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁) :
    4 * M * (sZ0A N Λ σ (r * ρ) / ρ) * (sD N A σ (r * ρ) t / ρ) ≤
      4 * cZA N Λ * cK1 N A * sizeY M P t Tσ r := by
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N (by linarith [h.hΛ])
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; have := h.hA; positivity
  have hρ := h.hρ
  have eq : 4 * M * (sZ0A N Λ σ (r * ρ) / ρ) * (sD N A σ (r * ρ) t / ρ) =
      4 * cZA N Λ * cK1 N A * M * (t * σ ^ 3 * r ^ 2) := by
    unfold sZ0A sD; field_simp
  rw [eq]
  have hσ := h.hS.pos
  have ht0 : 0 < t := lt_of_lt_of_le one_pos h.ht
  have hM := h.hM
  have hcube := h.hS.cube
  have ht1 : t ≤ t ^ 6 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 6 := pow_le_pow_right₀ h.ht (by norm_num)
  have hP2' : 1 ≤ P ^ 2 := by nlinarith [h.hP]
  have hT0 := h.hT0
  calc 4 * cZA N Λ * cK1 N A * M * (t * σ ^ 3 * r ^ 2)
      = 4 * cZA N Λ * cK1 N A * M * (t * σ ^ 3 * r ^ 2 * 1) := by ring
    _ ≤ 4 * cZA N Λ * cK1 N A * M * (t ^ 6 * Tσ * r ^ 2 * P ^ 2) := by
        gcongr
    _ = _ := by unfold sizeY; ring

end Num

theorem smallBndA_le (N : ℕ) (A Λ Kc : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) (hKc : 0 ≤ Kc) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBndA N A Λ M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N (by linarith)
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; positivity
  have hΛ0 : 0 ≤ Λ := by linarith
  have hc3 : 0 ≤ cC3 N A Λ := by unfold cC3; positivity
  refine ⟨2 * (cZA N Λ + cK1 N A) ^ 3 * Λ + 2 * (cZA N Λ + cK1 N A) ^ 3 * Λ +
    4 * cZA N Λ * cK1 N A + cC3 N A Λ * (1 + cC3 N A Λ) + 2 * cC3 N A Λ ^ 2 +
    2 * N * cK1 N A ^ 2 + (38400 * N ^ 3 * A ^ 3 * Kc + 57600 * N ^ 3 * A ^ 4 * Kc ^ 2),
    by positivity, ?_⟩
  intro M ρ ν σ r K₂ t P Tσ Sσ α₁ hM hρ hρ1 hr hrΛ hν hνσ ht hP hK0 hK hS
  have h : NumCtx N A Λ Kc M ρ ν σ r K₂ t P Tσ Sσ α₁ :=
    ⟨hA, hΛ, hKc, hM, hρ, hρ1, hr, hrΛ, hν, hνσ, ht, hP, hK0, hK, hS⟩
  have e1 := h.t1A
  have e2 := h.t2A
  have e3 := h.t3A
  have e4 := h.t4
  have e5 := h.t5
  have e6 := h.t6
  have e7 := h.t7
  unfold sizeY at e1 e2 e3 e4 e5 e6 e7
  unfold smallBndA
  linarith

theorem tailBndA_le (N : ℕ) (A Λ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hΛ0 : 0 ≤ Λ := by linarith
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N hΛ0
  have hK1 : 0 ≤ cK1 N A := by unfold cK1; positivity
  set c2 : ℝ := cZA N Λ + cK1 N A with hc2
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨(2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (16 * c2 ^ 4 * Λ ^ 2), by positivity, ?_⟩
  intro M ρ σ r t P Tσ Sσ α₁ hM hρ hr hrΛ ht hP htail hS
  have hσ := hS.pos
  have hσ1 := hS.le_one
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have hPP : P ≤ P ^ 2 := by nlinarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  -- first: tailBnd ≤ C M P² t²
  have h1 : tailBnd N A M ρ σ (r * ρ) t P ≤
      (2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (M * P ^ 2 * t ^ 2) := by
    unfold tailBnd
    have e : P * (σ ^ 2 * (r * ρ) / ρ) = P * σ ^ 2 * r := by field_simp
    have e2 : (σ * (r * ρ) / ρ) = σ * r := by field_simp
    rw [e, e2]
    have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
    have hr1 : r * σ ^ 2 ≤ Λ := by
      have := mul_le_mul_of_nonneg_left hσ2 hr.le
      linarith
    have hσr : (σ * r) ^ 2 ≤ Λ ^ 2 := by
      have : σ * r ≤ Λ := by nlinarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have a1 : P * σ ^ 2 * r ≤ Λ * (P ^ 2 * t ^ 2) := by
      have h1 : P * (σ ^ 2 * r) ≤ P * Λ := mul_le_mul_of_nonneg_left (by linarith) hP0.le
      have h2 : Λ * P ≤ Λ * P ^ 2 := mul_le_mul_of_nonneg_left hPP hΛ0
      have h3 : Λ * P ^ 2 ≤ Λ * (P ^ 2 * t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hΛ0
        nlinarith [sq_nonneg P]
      nlinarith
    have a2 : 6400 * (N : ℝ) ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * r) ^ 2 ≤
        6400 * N ^ 3 * A ^ 2 * Λ ^ 2 * (P ^ 2 * t ^ 2) := by
      have hc : 0 ≤ 6400 * (N : ℝ) ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 := by positivity
      calc 6400 * (N : ℝ) ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * r) ^ 2
          ≤ 6400 * N ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * Λ ^ 2 := mul_le_mul_of_nonneg_left hσr hc
        _ = _ := by ring
    have a3 : (2 : ℝ) ≤ 2 * (P ^ 2 * t ^ 2) := by nlinarith
    have : M * (2 + P * σ ^ 2 * r + 6400 * N ^ 3 * A ^ 2 * P ^ 2 * t ^ 2 * (σ * r) ^ 2) ≤
        M * ((2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (P ^ 2 * t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      linarith
    linarith [this]
  -- second: use the tail condition
  have h2 : 1 ≤ (2 * c2 * t * σ * r) ^ 4 := one_le_pow₀ htail.le
  have hT := hS.quart
  have hT0 : 0 ≤ Tσ := le_trans (by positivity) hS.cube
  have h3 : M * P ^ 2 * t ^ 2 ≤ 16 * c2 ^ 4 * Λ ^ 2 * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2) := by
    have hr4 : r ^ 4 ≤ Λ ^ 2 * r ^ 2 := by
      have : r ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hr.le hrΛ 2
      nlinarith [pow_pos hr 2]
    calc M * P ^ 2 * t ^ 2 = M * P ^ 2 * t ^ 2 * 1 := by ring
      _ ≤ M * P ^ 2 * t ^ 2 * (2 * c2 * t * σ * r) ^ 4 := by gcongr
      _ = 16 * c2 ^ 4 * (M * P ^ 2 * t ^ 6 * σ ^ 4 * r ^ 4) := by ring
      _ ≤ 16 * c2 ^ 4 * (M * P ^ 2 * t ^ 6 * Tσ * (Λ ^ 2 * r ^ 2)) := by gcongr
      _ = _ := by ring
  have hC : 0 ≤ 2 + Λ + 6400 * (N : ℝ) ^ 3 * A ^ 2 * Λ ^ 2 := by positivity
  calc _ ≤ (2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) * (M * P ^ 2 * t ^ 2) := h1
    _ ≤ (2 + Λ + 6400 * N ^ 3 * A ^ 2 * Λ ^ 2) *
        (16 * c2 ^ 4 * Λ ^ 2 * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hC
    _ = _ := by ring

/-! ### The per-term bound -/

section CtxAniso

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ Λ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

/-- The per-term bound of the local part `Dlt X = 𝓔 - 𝓔(const) - A_X + L_X` before the
polynomial weights are absorbed: `≤ (C_s + C_t) E₀ e^{-κ d_j(X)} |X|² (1 + d_j(X))⁶ σ^{3-α₁}
(ε/r)²`. -/
theorem CtxAniso.dlt_bound_raw (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBndA N A Λ M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      (Cs + Ct) * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  have hr := c.rpos
  have hεpos := c.εpos
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  set q : ℝ := ε / r with hq
  have hq0 : 0 < q := by positivity
  have hqε : ε = q * r := by rw [hq]; field_simp
  have hqΛ : q ≤ Λ := by rw [hq, div_le_iff₀ hr]; exact c.εle
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hT0 : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos c.σpos _).le
  have hfin : ∀ C : ℝ, 0 ≤ C → C ≤ Cs + Ct → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * q ^ 2) →
      ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ (Cs + Ct) * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) *
        (σ ^ (3 - α₁) * q ^ 2) := by
    intro C hC hle h
    refine h.trans ?_
    have hw : 0 ≤ M * ((X.card : ℝ) ^ 2 * t ^ 6) :=
      mul_nonneg hM0 (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 6))
    have : 0 ≤ σ ^ (3 - α₁) * q ^ 2 := mul_nonneg hT0 (sq_nonneg q)
    calc C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * q ^ 2)
        = C * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) * (σ ^ (3 - α₁) * q ^ 2) := by ring
      _ ≤ (Cs + Ct) * (M * ((X.card : ℝ) ^ 2 * t ^ 6)) * (σ ^ (3 - α₁) * q ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hw) this
  rw [Dlt]
  by_cases hsm : (cZA N Λ + cK1 N A) * t * σ * ε ≤ r / 2
  · have h1 := c.small_case hX hsm
    have h2 := hCs M r ν σ q K₂ t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hr c.rle hq0 hqΛ
      c.ν0 c.νσ ht1 hP c.dat.K2_nonneg (by rw [← hqε]; exact hK) hS
    rw [← hqε] at h2
    exact hfin Cs hCs0 (by linarith) (h1.trans h2)
  · have h1 := c.tail_case hX
    have hlt : 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * q := by
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_right hcon hr.le
      rw [hqε] at hsm
      nlinarith
    have h2 := hCt M r σ q t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hr hq0 hqΛ ht1 hP hlt hS
    rw [← hqε] at h2
    exact hfin Ct hCt0 (by linarith) (h1.trans h2)

/-- **The per-term bound of `I(y,X)`** before the polynomial weight is absorbed: the local
part contributes `σ³ (ε/r)²`, the constant-field potential `σ⁴ (ε/r)²`. -/
theorem CtxAniso.itw_bound_raw_aniso (c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R)
    {Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBndA N A Λ M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cZA N Λ + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)} (hX : X ∈ T.polys) :
    ‖Itw T i₀ i₁ ν X ψ b‖ ≤
      (Cs + Ct + 12 * cZA N Λ ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have h1 := c.dlt_bound_raw hCs0 hCt0 hα0 hα1 hCs hCt hK hX
  have h2 := c.constant_potential_aniso hX
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X) := by have := c.E0nn; positivity
  have ht6 : (1 : ℝ) ≤ (1 + T.dist X) ^ 6 := one_le_pow₀ (by linarith)
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  have hs4 : σ ^ 4 ≤ σ ^ (3 - α₁) := hS.quart
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N c.Λnn
  have hr2 : 12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * cZA N Λ ^ 2 *
        (σ ^ 4 * (ε / r) ^ 2) ≤
      12 * cZA N Λ ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
    have hq : 0 ≤ (ε / r) ^ 2 := sq_nonneg _
    have hPP : (X.card : ℝ) ≤ (X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 := by nlinarith
    calc 12 * (X.card : ℝ) * (E₀ * Real.exp (-κ * T.dist X)) * cZA N Λ ^ 2 *
          (σ ^ 4 * (ε / r) ^ 2)
        = 12 * cZA N Λ ^ 2 * (E₀ * Real.exp (-κ * T.dist X) * (X.card : ℝ)) *
            (σ ^ 4 * (ε / r) ^ 2) := by ring
      _ ≤ 12 * cZA N Λ ^ 2 *
          (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
          (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
          have : 0 ≤ 12 * cZA N Λ ^ 2 := by positivity
          gcongr
  rw [c.itw_eq]
  refine (norm_add_le _ _).trans ?_
  have hcomb : (Cs + Ct) *
      (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
      (σ ^ (3 - α₁) * (ε / r) ^ 2) +
      12 * cZA N Λ ^ 2 *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) =
      (Cs + Ct + 12 * cZA N Λ ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by ring
  rw [← hcomb]
  exact add_le_add h1 (h2.trans hr2)

end CtxAniso

/-! ### The termwise irrelevance theorem -/

theorem card_le_of_diam_aniso {T : TermFamily d N} {i₀ i₁ : Fin N} {ν r E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom)
    {X : Finset (Site d)} (hX : X ∈ T.polys) :
    (X.card : ℝ) ≤ (2 * (A * (1 + T.dist X)) + 1) ^ d := by
  classical
  set Rr : ℝ := A * (1 + T.dist X) with hRr
  have hR0 : 0 ≤ Rr := by
    have h0 := hP.diam X hX 0 (hP.zero_mem X hX)
    refine le_trans ?_ h0
    simp
  set m : ℤ := ⌊Rr⌋ with hm
  have hm0 : 0 ≤ m := Int.floor_nonneg.mpr hR0
  have hsub : X ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-m) m) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro μ
    have h1 := hP.diam X hX x hx
    have h2 : |x μ| ≤ ∑ ν, |x ν| := Finset.single_le_sum (f := fun ν => |x ν|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
    have h3 : ((|x μ| : ℤ) : ℝ) ≤ Rr := by
      refine le_trans ?_ h1
      exact_mod_cast h2
    have h4 : |x μ| ≤ m := Int.le_floor.mpr h3
    exact Finset.mem_Icc.mpr (abs_le.mp h4)
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hc
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hc
  have hc' : (X.card : ℝ) ≤ (((m + 1 - -m).toNat : ℕ) : ℝ) ^ d := by exact_mod_cast hc
  refine hc'.trans ?_
  have hm1 : (((m + 1 - -m).toNat : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by
    have : ((m + 1 - -m).toNat : ℤ) = m + 1 - -m := Int.toNat_of_nonneg (by omega)
    have h2 : (((m + 1 - -m).toNat : ℕ) : ℝ) = (((m + 1 - -m).toNat : ℤ) : ℝ) := by
      norm_cast
    rw [h2, this]; push_cast; ring
  rw [hm1]
  have hmR : (m : ℝ) ≤ Rr := Int.floor_le Rr
  have h5 : 2 * (m : ℝ) + 1 ≤ 2 * Rr + 1 := by linarith
  have h6 : 0 ≤ 2 * (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := by exact_mod_cast hm0
    linarith
  exact pow_le_pow_left₀ h6 h5 d

/-- **Lemma 3.2 (iii) on the anisotropic domain** (P1 Lemma 3.8, Proposition 3.10, termwise):
for a polymer `X ∈ T.polys` and data satisfying `DataHypAniso`,
`‖I(y,X)‖ ≤ C E₀ e^{-(κ-1) d_j(X)} σ^{3-α₁} (ε/r)²`, where the terms are analytic and bounded on
`TubeAniso i₀ ν r X` (spin radius `r`, longitudinal field radius `r²`); no renormalization
condition is used.  The constant `C` depends on `d, N, A, Λ, K_σ, α₁` only. -/
theorem termwise_irrelevant_aniso (d N : ℕ) (A Λ Ksig α₁ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d)) (_ : X ∈ T.polys),
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → 0 < σ → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν →
      ν ≤ σ ^ 2 → 0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
  obtain ⟨Cs, hCs0, hCs⟩ := smallBndA_le N A Λ Ksig hA hΛ hKsig
  obtain ⟨Ct, hCt0, hCt⟩ := tailBndA_le N A Λ hA hΛ
  obtain ⟨Cw, hCw0, hCw⟩ := weight_absorb A hA d
  have hCZ : 0 ≤ cZA N Λ := cZA_nonneg N (by linarith)
  refine ⟨(Cs + Ct + 12 * cZA N Λ ^ 2) * Cw, by positivity, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ hE0 hK
  obtain ⟨u, R, hF⟩ := exists_frame i₀ dat.toDataHyp hτ
  have c : CtxAniso T i₀ i₁ ν r E₀ κ A K₀ Λ Dom ψ b σ ε K₂ u R :=
    ⟨hP, dat, hF, hσ, hσ1, hε, hεΛ, hr, hr1, hν, hνσ, hE0, hA, hτ⟩
  have h := c.itw_bound_raw_aniso hCs0 hCt0 hα0 hα1 hCs hCt hK hX
  refine h.trans ?_
  have hd0 := hP.dist_nonneg X hX
  have hcard := card_le_of_diam_aniso hP hX
  have hab := hCw κ (T.dist X) (X.card : ℝ) hd0 (Nat.cast_nonneg _) hcard
  have hT0 : 0 ≤ σ ^ (3 - α₁) * (ε / r) ^ 2 :=
    mul_nonneg (Real.rpow_pos_of_pos hσ _).le (sq_nonneg _)
  have hCsum : 0 ≤ Cs + Ct + 12 * cZA N Λ ^ 2 := by positivity
  calc (Cs + Ct + 12 * cZA N Λ ^ 2) *
        (E₀ * Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2)
      = (Cs + Ct + 12 * cZA N Λ ^ 2) * E₀ *
        (Real.exp (-κ * T.dist X) * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by ring
    _ ≤ (Cs + Ct + 12 * cZA N Λ ^ 2) * E₀ * (Cw * Real.exp (-(κ - 1) * T.dist X)) *
        (σ ^ (3 - α₁) * (ε / r) ^ 2) := by
        have : 0 ≤ (Cs + Ct + 12 * cZA N Λ ^ 2) * E₀ := mul_nonneg hCsum hE0
        gcongr
    _ = _ := by ring

/-- **Lemma 3.2 (iii) on the anisotropic domain, the form (3.1)**: with `σ = C₀ s` and the source
scale ratio `ε/r = ε_k/ε_j ≤ K_R s^{(d-2)/2 - γ}`, `α₃ = 1 - 2γ - α₁`:
`|I(y,X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)}`. -/
theorem termwise_irrelevant_aniso_scaled (d N : ℕ) (A Λ Ksig α₁ γ C₀ KR : ℝ) (hA : 0 ≤ A)
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hC₀ : 0 < C₀) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν r E₀ κ K₀ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : PremisesTermAniso T i₀ i₁ ν r E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (s σ ε K₂ : ℝ) (_ : DataHypAniso Dom ν σ ε K₂ ψ b) (X : Finset (Site d))
      (_ : X ∈ T.polys),
      0 < s → σ = C₀ * s → ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ) →
      0 < r → r ≤ 1 → 0 < ε → ε ≤ Λ * r → σ ≤ 1 → σ ^ 2 * ε ≤ 1 / 4 → 0 ≤ ν → ν ≤ σ ^ 2 →
      0 ≤ E₀ → K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖Itw T i₀ i₁ ν X ψ b‖ ≤
        CI * E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) * Real.exp (-(κ - 1) * T.dist X) := by
  obtain ⟨C, hC0, hC⟩ := termwise_irrelevant_aniso d N A Λ Ksig α₁ hA hΛ hKsig hα0 hα1
  refine ⟨C * (C₀ ^ (3 - α₁) * KR ^ 2), by positivity, ?_⟩
  intro T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b s σ ε K₂ dat X hX hs hσs hR hr hr1 hε hεΛ hσ1 hτ hν hνσ
    hE0 hK
  have hσ : 0 < σ := by rw [hσs]; positivity
  have h := hC T i₀ i₁ ν r E₀ κ K₀ Dom hP ψ b σ ε K₂ dat X hX hr hr1 hε hεΛ hσ hσ1 hτ hν hνσ
    hE0 hK
  refine h.trans ?_
  have hr0 : 0 ≤ ε / r := by positivity
  have h1 : (ε / r) ^ 2 ≤ KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) := by
    have := pow_le_pow_left₀ hr0 hR 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
    ring_nf
  have h2 : σ ^ (3 - α₁) = C₀ ^ (3 - α₁) * s ^ (3 - α₁) := by
    rw [hσs, Real.mul_rpow hC₀.le hs.le]
  have h3 : s ^ (3 - α₁) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)) =
      s ^ ((d : ℝ) + (1 - 2 * γ - α₁)) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have hs0 : 0 ≤ s ^ (3 - α₁) := (Real.rpow_pos_of_pos hs _).le
  calc C * E₀ * Real.exp (-(κ - 1) * T.dist X) * (σ ^ (3 - α₁) * (ε / r) ^ 2)
      ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) *
        (C₀ ^ (3 - α₁) * s ^ (3 - α₁) * (KR ^ 2 * s ^ (2 * (((d : ℝ) - 2) / 2 - γ)))) := by
        rw [h2]
        have : 0 ≤ C * E₀ * Real.exp (-(κ - 1) * T.dist X) := by positivity
        gcongr
    _ = C * (C₀ ^ (3 - α₁) * KR ^ 2) * E₀ *
        (s ^ (3 - α₁) * s ^ (2 * (((d : ℝ) - 2) / 2 - γ))) *
        Real.exp (-(κ - 1) * T.dist X) := by ring
    _ = _ := by rw [h3]

end Balaban.SmallField
