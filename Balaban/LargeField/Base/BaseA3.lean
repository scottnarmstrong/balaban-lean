/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseWitnessGainQRS
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constant `A₃` of the first-component gain with the constants the landed bridge supports

LFR row 9 takes `A₃ := ¼ min{8γ₀A₀²/(6^d(9K₁)²), A₁²/8}` (P6 (3.9)).  The landed bridge
`χ_1 = 0 ⟹ ψ_1 ∉ Ψ̃(·; δ/(6K₁))` (`R/ChiBridge.lean`) and `violation_gain_real` give, for one failed
test, the exponent `γ₀ p_0²/(8 a (6K₁)² m)` with `m` the overlap of the cube neighbourhoods, which is
below the exponent of P6 (3.7)-(3.8).  In the typing, `A₃` is a free positive constant (`Typing.A₃`,
`1` in the witness of `PrefixInput`), and `A₀` is chosen after it (`∃ A₀' ∀ A₀ ≥ A₀'`, LFR §I.1.4), so
the smaller exponent costs only a larger `A₀`:

* `gainBridge`: the exponent `γ₀ p²/(8 a (6K₁)² m)` of one failed test;
* `two_A3_le_gain_of_A0`: `2 A₃ λ^{2p₀} ≤ c p²` as soon as `p ≥ A₀ λ^{p₀}` and `2 A₃ ≤ c A₀²`;
* `exists_A0_for_A3`: for every `A₃` and `c > 0` there is `A₀'` with `2 A₃ ≤ c A₀²` for `A₀ ≥ A₀'`;
* `two_A3_le_gainBridge`, `two_A3_le_gainR_of_A1`: the premises `hQ`, `hR`, `hS` of
  `baseFirst_operator_majorant_of_fiveShares` for the gains `n · gainBridge …`, `n · gainR …` and
  an arbitrary `A₃`, under `A₀ ≥ A₀'` and `A₁² ≥ 8 A₃`.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The exponent of one failed `χ'_1` or `χ_1` test with the tolerance `δ/(6K₁)` of the landed bridge:
`γ₀ p²/(8 a (6K₁)² m)`, `m` the overlap of the cube neighbourhoods. -/
noncomputable def gainBridge (γ₀ K₁ a m p : ℝ) : ℝ := γ₀ / (8 * a * (6 * K₁) ^ 2 * m) * p ^ 2

/-- `2 A₃ λ^{2p₀} ≤ c p²` from `p ≥ A₀ λ^{p₀}` and `2 A₃ ≤ c A₀²`. -/
theorem two_A3_le_gain_of_A0 {A₃ c A₀ lam P : ℝ} {p₀ : ℕ} (hc : 0 ≤ c) (hA₀ : 0 ≤ A₀)
    (hl : 0 ≤ lam) (hP : A₀ * lam ^ p₀ ≤ P) (hA : 2 * A₃ ≤ c * A₀ ^ 2) :
    2 * A₃ * lam ^ (2 * p₀) ≤ c * P ^ 2 := by
  have h0 : 0 ≤ A₀ * lam ^ p₀ := by positivity
  have h1 : (A₀ * lam ^ p₀) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ h0 hP 2
  have h2 : 0 ≤ lam ^ (2 * p₀) := by positivity
  calc 2 * A₃ * lam ^ (2 * p₀) ≤ c * A₀ ^ 2 * lam ^ (2 * p₀) :=
        mul_le_mul_of_nonneg_right hA h2
    _ = c * (A₀ * lam ^ p₀) ^ 2 := by ring
    _ ≤ c * P ^ 2 := mul_le_mul_of_nonneg_left h1 hc

/-- For every `A₃` and `c > 0` the condition `2 A₃ ≤ c A₀²` holds for all large `A₀`. -/
theorem exists_A0_for_A3 (A₃ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ A₀' : ℝ, 0 < A₀' ∧ ∀ A₀ : ℝ, A₀' ≤ A₀ → 2 * A₃ ≤ c * A₀ ^ 2 := by
  refine ⟨1 + 2 * |A₃| / c, by positivity, fun A₀ hA => ?_⟩
  have h1 : 1 ≤ A₀ := by
    have : 0 ≤ 2 * |A₃| / c := by positivity
    linarith
  have h2 : 2 * |A₃| / c ≤ A₀ := by linarith
  have h3 : 2 * |A₃| ≤ c * A₀ := by
    rw [div_le_iff₀ hc] at h2; linarith
  have : A₀ ≤ A₀ ^ 2 := by nlinarith
  nlinarith [le_abs_self A₃, mul_le_mul_of_nonneg_left this hc.le]

/-- The premise `hQ`/`hS` of `baseFirst_operator_majorant_of_fiveShares` for the gain
`n · gainBridge`, for an arbitrary `A₃`, when `2 A₃ ≤ γ₀ A₀²/(8 a (6K₁)² m)`. -/
theorem two_A3_le_gainBridge {γ₀ K₁ a m A₃ A₀ lam P : ℝ} {p₀ : ℕ} (hγ : 0 ≤ γ₀) (hK : 0 < K₁)
    (ha : 0 < a) (hm : 0 < m) (hA₀ : 0 ≤ A₀) (hl : 0 ≤ lam) (hP : A₀ * lam ^ p₀ ≤ P)
    (hA : 2 * A₃ ≤ γ₀ / (8 * a * (6 * K₁) ^ 2 * m) * A₀ ^ 2) (n : ℝ) (hn : 0 ≤ n) :
    2 * A₃ * lam ^ (2 * p₀) * n ≤ n * gainBridge γ₀ K₁ a m P := by
  have hc : 0 ≤ γ₀ / (8 * a * (6 * K₁) ^ 2 * m) := by positivity
  rw [mul_comm n]
  exact mul_le_mul_of_nonneg_right (two_A3_le_gain_of_A0 hc hA₀ hl hP hA) hn

/-- The premise `hR` for an arbitrary `A₃` when `8 A₃ ≤ A₁²`: `2 A₃ ≤ A₁²/4`. -/
theorem two_A3_le_gainR_of_A1 {A₃ A₁ lam P : ℝ} {p₀ : ℕ} (hA₁ : 0 ≤ A₁) (hl : 0 ≤ lam)
    (hP : A₁ * lam ^ p₀ ≤ P) (hA : 8 * A₃ ≤ A₁ ^ 2) (n : ℝ) (hn : 0 ≤ n) :
    2 * A₃ * lam ^ (2 * p₀) * n ≤ n * gainR P := by
  have := two_A3_le_gain_of_A0 (A₃ := A₃) (c := 1 / 4) (A₀ := A₁) (lam := lam) (P := P)
    (p₀ := p₀) (by norm_num) hA₁ hl hP (by linarith)
  unfold gainR
  rw [mul_comm n]
  exact mul_le_mul_of_nonneg_right (by linarith) hn

end Balaban.LargeField
