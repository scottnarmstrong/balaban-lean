/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormNumeric

/-!
# Assembly: Theorem 2.1 (a) for the family of polymers containing the origin

`Dlt X` is `𝓔(0,X;ψ,b) - 𝓔(0,X;ψ(0),b) - A_X + L_X`.  We show `‖Dlt X‖ ≤ C E₀ wt(X) σ^{3-α₁} (ε/ρ)²`
(small polymers by `small_case`, large ones by `tail_case`), sum over `X`, and use the vanishing of
`Σ_X L_X` (second moment, isotropy).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The per-polymer quantity `𝓔(0,X;ψ,b) - 𝓔(0,X;ψ(0),b) - A_X + L_X`. -/
noncomputable def Dlt (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Site d → Spin N) (b : Spin N) (X : Finset (Site d)) : ℂ :=
  T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
    - (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))
    + (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
        wquad (gradTensor i₀ R ψ) x.1 x'.1

/-- `A_X = ½ Σ_x a_X(x) (g(x) - g(0))`. -/
noncomputable def Ax (T : TermFamily d N) (i₀ : Fin N) (ν : ℝ) (ψ : Site d → Spin N)
    (X : Finset (Site d)) : ℂ :=
  (1 / 2 : ℂ) * ∑ x : ↥X, tensA i₀ ν X (T.term X) x * (dot (ψ x.1) (ψ x.1) - dot (ψ 0) (ψ 0))

/-- `L_X = ¼ Σ_{x,x'} B_X(x,x') wquad`. -/
noncomputable def Lx (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Site d → Spin N) (X : Finset (Site d)) : ℂ :=
  (1 / 4 : ℂ) * ∑ x : ↥X, ∑ x' : ↥X, tensB i₀ i₁ ν X (T.term X) x x' *
    wquad (gradTensor i₀ R ψ) x.1 x'.1

theorem Dlt_eq (T : TermFamily d N) (i₀ i₁ : Fin N) (ν : ℝ) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψ : Site d → Spin N) (b : Spin N) (X : Finset (Site d)) :
    Dlt T i₀ i₁ ν R ψ b X = T.term X (pack X ψ b) - T.term X (pack X (fun _ => ψ 0) b)
      - Ax T i₀ ν ψ X + Lx T i₀ i₁ ν R ψ X := rfl

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {σ ε K₂ : ℝ} {u : ℂ} {R : Matrix (Fin N) (Fin N) ℂ}

theorem Ctx.dlt_bound (c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R) {Λ Kc α₁ Cs Ct : ℝ} (hCs0 : 0 ≤ Cs) (hCt0 : 0 ≤ Ct)
    (hα0 : 0 < α₁) (hα1 : α₁ < 1) (hΛ : 1 ≤ Λ) (hKc : 0 ≤ Kc)
    (hCs : ∀ (M ρ ν σ r K₂ t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → ρ ≤ 1 → 0 < r →
      r ≤ Λ → 0 ≤ ν → ν ≤ σ ^ 2 → 1 ≤ t → 1 ≤ P → 0 ≤ K₂ → K₂ ≤ Kc * Sσ * (r * ρ) →
      SigPow σ α₁ Tσ Sσ →
      smallBnd N A M ρ ν σ (r * ρ) K₂ t P ≤ Cs * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hCt : ∀ (M ρ σ r t P Tσ Sσ α₁ : ℝ), 0 ≤ M → 0 < ρ → 0 < r → r ≤ Λ → 1 ≤ t →
      1 ≤ P → 1 < 2 * (cC1 N + cK1 N A) * t * σ * r → SigPow σ α₁ Tσ Sσ →
      tailBnd N A M ρ σ (r * ρ) t P ≤ Ct * (M * P ^ 2 * t ^ 6 * Tσ * r ^ 2))
    (hεΛ : ε ≤ Λ * ρ) (hK : K₂ ≤ Kc * σ ^ (2 - α₁) * ε) {X : Finset (Site d)}
    (hX : X ∈ T.polys) :
    ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤
      (Cs + Ct) * (E₀ * wt κ X (T.dist X)) * (σ ^ (3 - α₁) * (ε / ρ) ^ 2) := by
  have hρ := c.ρpos
  have hεpos := c.εpos
  have hd0 : 0 ≤ T.dist X := c.hyp.dist_nonneg X hX
  have hS := sigPow σ α₁ c.σpos c.σle hα0 hα1
  set r : ℝ := ε / ρ with hr
  have hr0 : 0 < r := by positivity
  have hrε : ε = r * ρ := by rw [hr]; field_simp
  have hrΛ : r ≤ Λ := by rw [hr, div_le_iff₀ hρ]; linarith
  set t : ℝ := 1 + T.dist X with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith
  have hP : (1 : ℝ) ≤ X.card := by exact_mod_cast c.card_pos hX
  set M : ℝ := E₀ * Real.exp (-κ * T.dist X) with hMdef
  have hM0 : 0 ≤ M := by have := c.E0nn; positivity
  have hwt := wt_ge (κ := κ) X hd0 (c.card_pos hX) 2 6 le_rfl le_rfl
  have hMP : M * (X.card : ℝ) ^ 2 * t ^ 6 ≤ E₀ * wt κ X (T.dist X) := by
    calc M * (X.card : ℝ) ^ 2 * t ^ 6 = E₀ * ((X.card : ℝ) ^ 2 * (1 + T.dist X) ^ 6 *
          Real.exp (-κ * T.dist X)) := by rw [hMdef, ht]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwt c.E0nn
  have hT0 : 0 ≤ σ ^ (3 - α₁) := (Real.rpow_pos_of_pos c.σpos _).le
  have hfin : ∀ C : ℝ, 0 ≤ C → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ C * (M * (X.card : ℝ) ^ 2 * t ^ 6 *
      σ ^ (3 - α₁) * r ^ 2) → ‖Dlt T i₀ i₁ ν R ψ b X‖ ≤ C * (E₀ * wt κ X (T.dist X)) *
      (σ ^ (3 - α₁) * r ^ 2) := by
    intro C hC h
    refine h.trans ?_
    calc C * (M * (X.card : ℝ) ^ 2 * t ^ 6 * σ ^ (3 - α₁) * r ^ 2)
        = C * ((M * (X.card : ℝ) ^ 2 * t ^ 6) * (σ ^ (3 - α₁) * r ^ 2)) := by ring
      _ ≤ C * ((E₀ * wt κ X (T.dist X)) * (σ ^ (3 - α₁) * r ^ 2)) := by
          gcongr
      _ = _ := by ring
  have hfin' : ∀ C : ℝ, 0 ≤ C → C ≤ Cs + Ct → C * (E₀ * wt κ X (T.dist X)) *
      (σ ^ (3 - α₁) * r ^ 2) ≤ (Cs + Ct) * (E₀ * wt κ X (T.dist X)) *
      (σ ^ (3 - α₁) * r ^ 2) := by
    intro C hC hle
    have hw : 0 ≤ E₀ * wt κ X (T.dist X) := by
      have := c.E0nn
      have : 0 ≤ wt κ X (T.dist X) := by
        unfold wt
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) 6))
          (Real.exp_pos _).le
      exact mul_nonneg c.E0nn this
    have : 0 ≤ σ ^ (3 - α₁) * r ^ 2 := mul_nonneg hT0 (sq_nonneg r)
    gcongr
  by_cases hsm : (cC1 N + cK1 N A) * t * σ * ε ≤ ρ / 2
  · have h1 := c.small_case hX hsm
    have h2 := hCs M ρ ν σ r K₂ t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hρ c.ρle hr0 hrΛ
      c.ν0 c.νσ ht1 hP c.dat.K2_nonneg (by rw [← hrε]; exact hK) hS
    rw [← hrε] at h2
    have := hfin (Cs) hCs0 (h1.trans h2)
    have h3 := hfin' Cs hCs0 (by linarith)
    exact this.trans h3
  · have h1 := c.tail_case hX
    have hlt : 1 < 2 * (cC1 N + cK1 N A) * t * σ * r := by
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_right hcon hρ.le
      rw [hrε] at hsm
      nlinarith
    have h2 := hCt M ρ σ r t X.card (σ ^ (3 - α₁)) (σ ^ (2 - α₁)) α₁ hM0 hρ hr0 hrΛ ht1 hP hlt hS
    rw [← hrε] at h2
    have := hfin Ct hCt0 (h1.trans h2)
    have h3 := hfin' Ct hCt0 (by linarith)
    exact this.trans h3

end Balaban.SmallField
