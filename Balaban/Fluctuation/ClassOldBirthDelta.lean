/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldBirthConsts
public import Balaban.Localization.I5Close
public import Balaban.Localization.I5FluctFacts
import Mathlib.Tactic.Positivity

/-!
# The closeness radius `δ₃` and the fluctuation radius `δfl` as multiples of `ε_k`

`ChainNum.close` asks `N · composedCloseBound(…, C_{Ξ1} ε′, r₀) ≤ δ₃`, and `composedCloseBound` is
linear in the radius (`closeConst` is linear in its last argument).  The smallest admissible
choice `δ₃ = N · composedCloseBound(…)` is at most `c₃ ε_k` with
`c₃ = N C_{Ξ1} L^{-α} · composedCloseBound(…, 1, r₀)`, and `c₃` is at most `η` as soon as
`γ_w (r₀ − 4dL³) L^{m₁} / L ≥ log (Λ₀ / η)`.  `FlNum.flb` asks `N (5 K₂″ δ₁ + δ₁) ≤ δfl` for the
free radius `δ₁`; with `δ₁ ≤ c_δ ε_k` the choice `δfl = N (5 K₂″ δ₁ + δ₁)` is at most
`c_fl ε_k`, `c_fl = N (5 K₂″ + 1) c_δ`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

theorem composedCloseBound_smul (d L N m₁ : ℕ) [NeZero L] (BG κ δ r₀ : ℝ) :
    composedCloseBound d L N m₁ BG κ δ r₀ = δ * composedCloseBound d L N m₁ BG κ 1 r₀ := by
  unfold composedCloseBound closeConst
  ring

theorem delta3_nonneg {d L N m₁ : ℕ} [NeZero L] {BG κ eps r₀ δ₃ : ℝ} (hBG : 0 ≤ BG)
    (hd : 0 < d) (heps : 0 ≤ eps)
    (hδ₃ : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀) : 0 ≤ δ₃ := by
  have h0 : 0 ≤ xiC1 d := by unfold xiC1; positivity
  rw [hδ₃]
  have := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG (mul_nonneg h0 heps) hd
  positivity

/-- **`δ₃ ≤ c₃ ε_k`.**  The choice `δ₃ = N · composedCloseBound(…, C_{Ξ1} ε′, r₀)` (the smallest
value allowed by `ChainNum.close`) satisfies `δ₃ ≤ c₃ ε_k` with
`c₃ = N C_{Ξ1} L^{-α} composedCloseBound(…, 1, r₀)`, for `ε′ ≤ ε_{k+1}`. -/
theorem delta3_le_of_close {d L N m₁ k : ℕ} [NeZero L] {BG κ eps r₀ δ₃ α α₀ c₃ : ℝ}
    (hα₀ : 0 ≤ α₀) (hα : 0 ≤ α) (hBG : 0 ≤ BG) (hd : 0 < d)
    (hepsK : eps ≤ epsSeq L α α₀ (k + 1))
    (hδ₃ : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀)
    (hc₃ : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀) :
    δ₃ ≤ c₃ * epsSeq L α α₀ k := by
  have h0 : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hc1 := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG (zero_le_one) hd
  have hs := epsSeq_succ_le_of_le L α α₀ hα₀ hα (le_refl k)
  have he : eps ≤ (L : ℝ) ^ (-α) * epsSeq L α α₀ k := hepsK.trans hs
  rw [hδ₃, hc₃, composedCloseBound_smul d L N m₁ BG κ (xiC1 d * eps) r₀]
  have : xiC1 d * eps ≤ xiC1 d * ((L : ℝ) ^ (-α) * epsSeq L α α₀ k) :=
    mul_le_mul_of_nonneg_left he h0
  have h2 : N * ((xiC1 d * eps) * composedCloseBound d L N m₁ BG κ 1 r₀) ≤
      N * ((xiC1 d * ((L : ℝ) ^ (-α) * epsSeq L α α₀ k)) *
        composedCloseBound d L N m₁ BG κ 1 r₀) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hc1) (Nat.cast_nonneg _)
  calc _ ≤ _ := h2
    _ = _ := by ring

/-- **`c₃` is small for a long decay length.**  If `Λ₀ = N C_{Ξ1} · 10 e^{2dγ_w} closeConst(…,
lemma53Const)` is positive, `η > 0` and
`log (Λ₀ / η) ≤ γ_w (r₀ − 4dL³) L^{m₁} / L`, then `c₃ ≤ η` (`α ≥ 0`). -/
theorem c3_le_of_decay {d L N m₁ : ℕ} [NeZero L] {BG κ r₀ α η c₃ : ℝ} (hα : 0 ≤ α)
    (hBG : 0 ≤ BG) (hd : 0 < d) (hη : 0 < η)
    (hΛ : 0 < N * xiC1 d * (10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * 1)))
    (hM : Real.log ((N * xiC1 d * (10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * 1))) / η) ≤
      gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))
    (hc₃ : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀) :
    c₃ ≤ η := by
  set Λ := N * xiC1 d * (10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * 1)) with hΛdef
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hq : (L : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hq0 : 0 ≤ (L : ℝ) ^ (-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hexp : Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) ≤
      η / Λ := by
    have h1 : Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) ≤
        Real.exp (-Real.log (Λ / η)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg (Real.log (Λ / η)), Real.exp_log (div_pos hΛ hη), inv_div] at h1
    exact h1
  have hc1 := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
    hBG (zero_le_one) hd
  have hB : composedCloseBound d L N m₁ BG κ 1 r₀ =
      10 * Real.exp (gammaW d * (2 * d)) * closeConst d L N BG κ (lemma53Const d L * 1) *
        Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := rfl
  have hN : 0 ≤ (N : ℝ) * xiC1 d := by
    have : 0 ≤ xiC1 d := by unfold xiC1; positivity
    positivity
  have h1 : c₃ ≤ N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀ := by
    rw [hc₃]
    have : (N : ℝ) * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀ =
        (N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀) * (L : ℝ) ^ (-α) := by ring
    rw [this]
    have h2 : 0 ≤ N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀ := by positivity
    calc _ ≤ (N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀) * 1 :=
          mul_le_mul_of_nonneg_left hq h2
      _ = _ := mul_one _
  have h3 : N * xiC1 d * composedCloseBound d L N m₁ BG κ 1 r₀ =
      Λ * Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
    rw [hB, hΛdef]; ring
  have h4 : Λ * Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) ≤ η := by
    calc _ ≤ Λ * (η / Λ) := mul_le_mul_of_nonneg_left hexp hΛ.le
      _ = η := by field_simp
  linarith

/-- **`δfl ≤ c_fl ε_k`.**  The choice `δfl = N (5 K₂″ δ₁ + δ₁)` (the smallest value allowed by
`FlNum.flb`) satisfies `δfl ≤ c_fl ε_k`, `c_fl = N (5 K₂″ + 1) c_δ`, when the free fluctuation
radius satisfies `δ₁ ≤ c_δ ε_k`. -/
theorem deltafl_le_of_flb {d L N k : ℕ} [NeZero L] {BG₂ κ δ₁ δfl α α₀ cδ cfl : ℝ}
    (hBG₂ : 0 ≤ BG₂) (hd : 0 < d) (hδ₁ : 0 ≤ δ₁)
    (hδ₁k : δ₁ ≤ cδ * epsSeq L α α₀ k)
    (hδfl : δfl = N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁))
    (hcfl : cfl = N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) * cδ) :
    0 ≤ δfl ∧ δfl ≤ cfl * epsSeq L α α₀ k := by
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
  have hK := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  refine ⟨by rw [hδfl]; positivity, ?_⟩
  rw [hδfl, hcfl]
  have h : 0 ≤ (N : ℝ) * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) := by positivity
  calc (N : ℝ) * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁)
      = (N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1)) * δ₁ := by ring
    _ ≤ (N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1)) * (cδ * epsSeq L α α₀ k) :=
        mul_le_mul_of_nonneg_left hδ₁k h
    _ = _ := by ring

end Balaban.Fluctuation
