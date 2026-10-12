/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormIso

/-!
# Theorem 2.1 (I-6, local form)

`renormalization_local`: under the premises (H.2)–(H.5) (`Premises`) and the properties (Σ1), (Σ2)
of the configuration (`DataHyp`), for `σ ≤ σ₁`:

* `‖𝓥(ψ(0), b)‖ ≤ C E₀ σ⁴ (ε/ρ)²`;
* `‖𝓔(0;ψ,b) - 𝓥(ψ(0), b) - A_0(ψ)‖ ≤ C E₀ σ^{3-α₁} (ε/ρ)²`,

with constants `C, σ₁` depending only on `(N, A, Λ, K_Σ, K₀)` (not on `d`, the polymers or the
terms).  `A_0(ψ) = ½ Σ_x a(x) (ψ(x)·ψ(x) - ψ(0)·ψ(0))`; its sum over a torus vanishes
(`Aterm_torus_sum`).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

theorem renormalization_local (N : ℕ) (A Λ Ksig α₁ K₀ : ℝ) (hA : 0 ≤ A) (hΛ : 1 ≤ Λ)
    (hKsig : 0 ≤ Ksig) (hK₀ : 0 ≤ K₀) (hα0 : 0 < α₁) (hα1 : α₁ < 1) :
    ∃ C σ₁ : ℝ, 0 ≤ C ∧ 0 < σ₁ ∧ ∀ {d : ℕ} (T : TermFamily d N) (i₀ i₁ : Fin N)
      (ν ρ E₀ κ : ℝ) (Dom : Set ((Site d → Spin N) × Spin N))
      (_ : Premises T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (ψ : Site d → Spin N) (b : Spin N)
      (σ ε K₂ : ℝ) (_ : DataHyp Dom ν σ ε K₂ ψ b),
      0 < ρ → ρ ≤ 1 → 0 < ε → ε ≤ Λ * ρ → 0 < σ → σ ≤ σ₁ → 0 ≤ ν → ν ≤ σ ^ 2 → 0 ≤ E₀ →
      K₂ ≤ Ksig * σ ^ (2 - α₁) * ε →
      ‖potential T (ψ 0) b‖ ≤ C * E₀ * σ ^ 4 * (ε / ρ) ^ 2 ∧
      ‖energy T ψ b - potential T (ψ 0) b - Aterm T i₀ ν ψ‖ ≤
        C * E₀ * σ ^ (3 - α₁) * (ε / ρ) ^ 2 := by
  obtain ⟨Cs, hCs0, hCs⟩ := smallBnd_le N A Λ Ksig hA hΛ hKsig
  obtain ⟨Ct, hCt0, hCt⟩ := tailBnd_le N A Λ hA hΛ
  have hC1 : 1 ≤ cC1 N := by unfold cC1; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  have hΛ0 : 0 < Λ := by linarith
  refine ⟨2 * K₀ * cC1 N ^ 2 + (Cs + Ct) * K₀, 1 / (2 * Λ * cC1 N), by positivity, by positivity, ?_⟩
  intro d T i₀ i₁ ν ρ E₀ κ Dom hyp ψ b σ ε K₂ dat hρ hρ1 hε hεΛ hσ hσ₁ hν hνσ hE0 hK
  set σ₁ : ℝ := 1 / (2 * Λ * cC1 N) with hσ₁def
  have hσ₁pos : 0 < σ₁ := by positivity
  have hσ₁le : σ₁ ≤ 1 / 2 := by
    rw [hσ₁def, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hσ1 : σ ≤ 1 := by linarith
  have hσσ : σ ^ 2 ≤ σ₁ ^ 2 := pow_le_pow_left₀ hσ.le hσ₁ 2
  -- smallness
  have hΛσ : cC1 N * Λ * σ ^ 2 ≤ 1 / 4 := by
    calc cC1 N * Λ * σ ^ 2 ≤ cC1 N * Λ * σ₁ ^ 2 := by gcongr
      _ = 1 / (4 * Λ * cC1 N) := by rw [hσ₁def]; field_simp; ring
      _ ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hτ : σ ^ 2 * ε ≤ 1 / 4 := by
    calc σ ^ 2 * ε ≤ σ ^ 2 * (Λ * ρ) := by gcongr
      _ = σ ^ 2 * Λ * ρ := by ring
      _ ≤ σ ^ 2 * Λ * 1 := mul_le_mul_of_nonneg_left hρ1 (by positivity)
      _ ≤ cC1 N * Λ * σ ^ 2 := by
        have : 0 ≤ Λ * σ ^ 2 := by positivity
        nlinarith
      _ ≤ 1 / 4 := hΛσ
  have hZ0 : sZ0 N σ ε ≤ ρ / 2 := by
    unfold sZ0
    calc cC1 N * (σ ^ 2 * ε) ≤ cC1 N * (σ ^ 2 * (Λ * ρ)) := by gcongr
      _ = (cC1 N * Λ * σ ^ 2) * ρ := by ring
      _ ≤ 1 / 4 * ρ := by gcongr
      _ ≤ ρ / 2 := by linarith
  obtain ⟨u, R, hF⟩ := exists_frame i₀ dat hτ
  have c : Ctx T i₀ i₁ ν ρ E₀ κ A K₀ Dom ψ b σ ε K₂ u R :=
    ⟨hyp, dat, hF, hσ, hσ1, hε, hρ, hρ1, hν, hνσ, hE0, hA, hτ⟩
  have hL := Lx_tsum_zero hyp hρ hE0 hA R ψ
  refine ⟨?_, ?_⟩
  · have h1 := c.potential_bound hZ0
    refine h1.trans ?_
    have e : 2 * E₀ * K₀ * (sZ0 N σ ε / ρ) ^ 2 = 2 * K₀ * cC1 N ^ 2 * E₀ * σ ^ 4 * (ε / ρ) ^ 2 := by
      unfold sZ0; field_simp
    rw [e]
    have : 0 ≤ E₀ * σ ^ 4 * (ε / ρ) ^ 2 := by positivity
    have h2 : 0 ≤ (Cs + Ct) * K₀ := by positivity
    nlinarith
  · have h1 := c.interaction_bound hCs0 hCt0 hα0 hα1 hCs hCt hεΛ hK hL
    refine h1.trans ?_
    have hT : 0 ≤ σ ^ (3 - α₁) * (ε / ρ) ^ 2 := mul_nonneg (Real.rpow_nonneg hσ.le _) (sq_nonneg _)
    have h2 : 0 ≤ 2 * K₀ * cC1 N ^ 2 := by positivity
    nlinarith [mul_nonneg hE0 hT]

end Balaban.SmallField
