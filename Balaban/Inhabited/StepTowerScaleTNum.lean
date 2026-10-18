/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScaleT
public import Balaban.Inhabited.BgSettingDataNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The numerical conditions of the chain scale with the step radius

`ChainNum` and `FlNum` (the smallness conditions of `BgSetting`, `FlSetting`) are monotone in the
step radius `ε'` and in the constants `δ₃`, `δ_fl`, and their lower bounds
`N · closeBound(ε') ≤ δ₃`, `N (5 K₂' δ₁ + δ₁) ≤ δ_fl` are linear in `ε'`, `δ₁ = ε'`.  So a
solution `(ε', δ₃, δ_fl)` gives the solution `(λ ε', λ δ₃, λ δ_fl)` for every `λ ∈ (0, 1]`
(`ChainNum.scale`, `FlNum.scale`).  With `exists_stepTower_shrink` this yields the towers at
all smaller radii with the constants `δ₃, δ_fl` proportional to the radius
(`exists_stepTower_scale_num`), and the room condition of the class chain at scale `k`
(`room_of_scale`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited

section Num

variable {d L N m₁ : ℕ} [NeZero L] {BG BG₂ κ r₀ eps δ₃ δfl l : ℝ}

/-- **`ChainNum` at the radius `l ε'` with `l δ₃`, `0 < l ≤ 1`.** -/
theorem _root_.Balaban.Localization.ChainNum.scale (h : ChainNum d L N m₁ BG κ r₀ eps δ₃) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    ChainNum d L N m₁ BG κ r₀ (l * eps) (l * δ₃) := by
  have he := h.eps_pos
  have hd := h.δ₃_nn
  have hX : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  have hC : 0 ≤ scaledC0 d ^ 2 := sq_nonneg _
  have hK1 : 0 ≤ bgK1 d L N := (bgK1_pos d L N).le
  have hc2 : 0 ≤ cK2 d L N := (cK2_pos d L N).le
  have hx2 : 0 ≤ xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hp : (0 : ℝ) ≤ (4 * d + 6) * (2 * d + 1) := by positivity
  have h1 : l * eps ≤ eps := by nlinarith
  have h2 : l * δ₃ ≤ δ₃ := by nlinarith
  have h1' : 0 ≤ eps - l * eps := by linarith
  have h2' : 0 ≤ δ₃ - l * δ₃ := by linarith
  have a1 := mul_nonneg hp h1'
  have a2 := mul_nonneg hX h1'
  have a3 := mul_nonneg (mul_nonneg hX hC) h1'
  have a4 := mul_nonneg (mul_nonneg hK1 (mul_nonneg hX hC)) h1'
  have a5 := mul_nonneg hc2 h2'
  have a6 := mul_nonneg (mul_nonneg hp hC) h1'
  have a7 := mul_nonneg (mul_nonneg hp hx2) h2'
  have a8 := mul_nonneg (mul_nonneg hX hx2) h2'
  have a9 := mul_nonneg (mul_nonneg hX hC) h1'
  exact {
    eps_pos := by positivity
    small1 := by linarith [h.small1]
    th1 := by linarith [h.th1]
    c7le := by linarith [h.c7le]
    small₁ := by linarith [h.small₁]
    δ₃_nn := by positivity
    δ₃_le_one := by linarith [h.δ₃_le_one]
    c1 := by linarith [h.c1]
    star := by linarith [h.star]
    K1s := by linarith [h.K1s]
    sm := by linarith [h.sm]
    small₂ := by linarith [h.small₂]
    th2 := by linarith [h.th2]
    close := by
      have := h.close
      rw [composedCloseBound_linear] at this ⊢
      nlinarith }

/-- **`FlNum` at the radius `l ε'` with `l δ₃`, `δ₁ = l ε'`, `l δ_fl`, `0 < l ≤ 1`.** -/
theorem _root_.Balaban.Localization.FlNum.scale (h : FlNum d L N BG BG₂ κ eps δ₃ eps δfl) (hl0 : 0 < l) (hl1 : l ≤ 1)
    (he : 0 < eps) (hd : 0 ≤ δ₃) (hd0 : 0 < d) (hBG : 0 ≤ BG) (hBG₂ : 0 ≤ BG₂) :
    FlNum d L N BG BG₂ κ (l * eps) (l * δ₃) (l * eps) (l * δfl) := by
  have hX : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  have hC : 0 ≤ scaledC0 d ^ 2 := sq_nonneg _
  have hK1 : 0 ≤ bgK1 d L N := (bgK1_pos d L N).le
  have hc2 : 0 ≤ cK2 d L N := (cK2_pos d L N).le
  have hx2 : 0 ≤ xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hBG hd0).le
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd0; linarith
  have hk0 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hp : (0 : ℝ) ≤ (4 * d + 6) * (2 * d + 1) := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have h1' : 0 ≤ eps - l * eps := by nlinarith
  have h2' : 0 ≤ δ₃ - l * δ₃ := by nlinarith
  have hdf : 0 ≤ δfl := h.δfl_nn
  have h3' : 0 ≤ δfl - l * δfl := by nlinarith
  have a1 := mul_nonneg hX h1'
  have a2 := mul_nonneg hK4 (mul_nonneg hX h1')
  have a3 := mul_nonneg (mul_nonneg hX hC) h1'
  have a4 := mul_nonneg (mul_nonneg hX hx2) h2'
  have a5 := mul_nonneg hX (mul_nonneg hx2 h3')
  have a6 := mul_nonneg hc2 h3'
  have a7 := mul_nonneg (mul_nonneg hK1 (mul_nonneg hX hC)) h1'
  have a8 := mul_nonneg (mul_nonneg hK1 (mul_nonneg hX hx2)) h2'
  have a9 := mul_nonneg (mul_nonneg hp hC) h1'
  have a10 := mul_nonneg (mul_nonneg hp hx2) h2'
  have a11 := mul_nonneg (mul_nonneg hp hx2) h3'
  have a12 := mul_nonneg hp h1'
  exact {
    δ₁_pos := by positivity
    δ₁_le := by nlinarith [h.δ₁_le]
    B_le := by linarith [h.B_le]
    B_one := by linarith [h.B_one]
    phi_lt := by linarith [h.phi_lt]
    flb := by linarith [mul_le_mul_of_nonneg_left h.flb hl0.le]
    δfl_nn := by positivity
    δfl_le_one := by linarith [h.δfl_le_one]
    c1_f := by linarith [h.c1_f]
    star_f := by linarith [h.star_f]
    K1s_f := by linarith [h.K1s_f]
    sm_f := by linarith [h.sm_f]
    small₃ := by linarith [h.small₃]
    th₃ := by linarith [h.th₃] }

end Num

/-- **Towers at every smaller radius, with proportional `δ₃`, `δ_fl`.**  For every `m₀` and floor
`κlo` there are `κmin ≥ κlo`, a tower `T`, constants `δ₃`, `δ_fl`, `κ_dec` with the numerical
premises of `exists_stepTower_base_rate`, and for every `l ∈ (0, 1]` a tower `T'` with the same
parameters as `T` except the radius `T'.t = l T.t`, for which `ChainNum` and `FlNum` hold with
`l δ₃`, `l δ_fl`. -/
theorem exists_stepTower_scale_num (m₀ : ℕ) (κlo : ℝ) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ),
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      ∀ l : ℝ, 0 < l → l ≤ 1 → ∃ T' : StepTower κmin, T'.t = l * T.t ∧ T'.m₁ = T.m₁ ∧
        T'.c = T.c ∧ T'.BG = T.BG ∧ T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧
        T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' ∧
        ChainNum 3 3 2 T'.m₁ T'.BG T'.κ 324 T'.t (l * δ₃) ∧
        FlNum 3 3 2 T'.BG T'.BG₂ T'.κ T'.t (l * δ₃) T'.t (l * δfl) := by
  obtain ⟨κmin, hlo, T, δ₃, δfl, κdec, h1, h2, h3, h4⟩ := exists_stepTower_base_rate m₀ κlo
  refine ⟨κmin, hlo, T, δ₃, δfl, κdec, h3, h4, h1, h2, fun l hl0 hl1 => ?_⟩
  have ht := T.t_pos
  obtain ⟨T', hT, hm, hc, hB, hk, hc₂, hB₂, hδc, hδ, hδ'⟩ :=
    exists_stepTower_shrink T (t' := l * T.t) (by positivity) (by nlinarith)
  refine ⟨T', hT, hm, hc, hB, hk, hc₂, hB₂, hδc, hδ, hδ', ?_, ?_⟩
  · rw [hm, hB, hk, hT]
    exact h1.scale hl0 hl1
  · rw [hB, hB₂, hk, hT]
    obtain ⟨hC⟩ := T.core
    exact h2.scale hl0 hl1 ht h1.δ₃_nn (by norm_num) hC.hS.fam.2.1
      hC.hS2.fam.2.1

end Balaban.Inhabited
