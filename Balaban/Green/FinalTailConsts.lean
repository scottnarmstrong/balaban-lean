/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailBridge
public import Balaban.Inhabited.DAPhysicalCutoff
public import Balaban.LargeField.Analytic.Constants
public import Balaban.LargeField.Counter.Params
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The exponents of the tail activity (W892, blocker 5, leaf L2)

Leaf L2 of `notes/phase1/FINALPHYS3.md` section 7.  With `ℓ = log β`, `ρ = pLog A₁ p β`
(so `ρ²/4 = (A₁²/4) ℓ^{2p}`), `p₂(β) = A₂ ℓ^{p₂}` and `H = H₀ ℓ`, the hypotheses
`hq`, `hbp` of `norm_setIntegral_blocksSplit_le_exp` hold for all large `β` exactly when the
exponents satisfy `p₂ < 2p`, or `p₂ = 2p` and `A₂ < A₁²/4` (and `1 ≤ p`).  For `p₂ > 2p`, or
`p₂ = 2p` and `A₂ > A₁²/4`, the required inequality fails for all large `β`
(`not_tail_exponent_of_lt`).  With `p = p₀` the typing condition `2 p₀ > p₂` gives it
(`tail_exponent_of_typing_ok`).
-/

@[expose] public section

namespace Balaban.Green

open Balaban.LargeField Balaban.Inhabited

/-- Core growth comparison in `ℓ`. -/
theorem tail_exponent_core {A₁ A₂ H₀ C : ℝ} {p p₂ : ℕ} (hA₁ : 0 < A₁) (hp : 1 ≤ p)
    (hexp : p₂ < 2 * p ∨ (p₂ = 2 * p ∧ A₂ < A₁ ^ 2 / 4)) :
    ∃ ℓ₀ : ℝ, ∀ ℓ : ℝ, ℓ₀ ≤ ℓ → A₂ * ℓ ^ p₂ + H₀ * ℓ + C ≤ A₁ ^ 2 / 4 * ℓ ^ (2 * p) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * p = n + 1 := ⟨2 * p - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  -- a: the leading coefficient of A₂ ℓ^{p₂} at the exponent n+1
  obtain ⟨a, ha, hpa⟩ : ∃ a : ℝ, a < A₁ ^ 2 / 4 ∧
      ∀ ℓ : ℝ, 1 ≤ ℓ → A₂ * ℓ ^ p₂ ≤ a * ℓ ^ (n + 1) + |A₂| * ℓ ^ n := by
    rcases hexp with h | ⟨h, hA⟩
    · refine ⟨0, by positivity, fun ℓ hℓ => ?_⟩
      have : ℓ ^ p₂ ≤ ℓ ^ n := pow_le_pow_right₀ hℓ (by omega)
      have h0 : (0:ℝ) ≤ ℓ ^ n := by positivity
      nlinarith [abs_nonneg A₂, le_abs_self A₂, mul_le_mul_of_nonneg_left this (abs_nonneg A₂),
        mul_le_mul_of_nonneg_right (le_abs_self A₂) (by positivity : (0:ℝ) ≤ ℓ ^ p₂)]
    · refine ⟨A₂, hA, fun ℓ hℓ => ?_⟩
      rw [h, hn]; nlinarith [abs_nonneg A₂, pow_nonneg (by linarith : (0:ℝ) ≤ ℓ) n]
  set δ := A₁ ^ 2 / 4 - a with hδ
  have hδ0 : 0 < δ := by linarith
  set K := |A₂| + |H₀| + |C| with hK
  refine ⟨max 1 (K / δ), fun ℓ hℓ => ?_⟩
  have h1 : 1 ≤ ℓ := le_trans (le_max_left _ _) hℓ
  have h2 : K / δ ≤ ℓ := le_trans (le_max_right _ _) hℓ
  have hKl : K ≤ δ * ℓ := by rwa [div_le_iff₀ hδ0, mul_comm] at h2
  have h0 : (0:ℝ) ≤ ℓ ^ n := by positivity
  have hℓn : ℓ ≤ ℓ ^ n := by simpa using pow_le_pow_right₀ h1 hn1
  have hC : C ≤ |C| * ℓ ^ n := by
    nlinarith [le_abs_self C, abs_nonneg C, one_le_pow₀ h1 (n := n)]
  have hH : H₀ * ℓ ≤ |H₀| * ℓ ^ n := by
    nlinarith [le_abs_self H₀, abs_nonneg H₀, mul_le_mul_of_nonneg_left hℓn (abs_nonneg H₀)]
  have := hpa ℓ h1
  rw [hn]
  have h3 : K * ℓ ^ n ≤ δ * ℓ * ℓ ^ n := mul_le_mul_of_nonneg_right hKl h0
  have h4 : δ * ℓ * ℓ ^ n = δ * ℓ ^ (n + 1) := by ring
  have h5 : A₁ ^ 2 / 4 * ℓ ^ (n + 1) = a * ℓ ^ (n + 1) + δ * ℓ ^ (n + 1) := by rw [hδ]; ring
  have h6 : K * ℓ ^ n = |A₂| * ℓ ^ n + |H₀| * ℓ ^ n + |C| * ℓ ^ n := by rw [hK]; ring
  linarith

/-- **L2: the tail exponent against `p₂ + H`.**  Let `1 ≤ p`, `A₁ > 0`, and either `p₂ < 2p`, or
`p₂ = 2p` and `A₂ < A₁²/4`.  For every real `c` and `H₀`, `m`, `W' = dim W`, all `β` above a
threshold satisfy
`c + A₂ (log β)^{p₂} ≤ pLog A₁ p β ^2/4 - log m - (W'/2) log 2 - H₀ log β`
(`β > 1`).  Together with `c = 0` this contains `hq`, `hbp` of
`norm_setIntegral_blocksSplit_le_exp` with `h = H₀ log β = HRun H₀ b j`, `p = p₂(β)`. -/
theorem tail_exponent_eventually {A₁ A₂ H₀ c : ℝ} {p p₂ : ℕ} (hA₁ : 0 < A₁) (hp : 1 ≤ p)
    (hexp : p₂ < 2 * p ∨ (p₂ = 2 * p ∧ A₂ < A₁ ^ 2 / 4)) (m W' : ℕ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      c + A₂ * Real.log β ^ p₂ ≤
        pLog A₁ p β ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2 - H₀ * Real.log β := by
  obtain ⟨ℓ₀, h⟩ := tail_exponent_core (A₂ := A₂) (H₀ := H₀)
    (C := c + Real.log m + (W' : ℝ) / 2 * Real.log 2) hA₁ hp hexp
  refine ⟨Real.exp (max ℓ₀ 1) + 1, by linarith [Real.exp_pos (max ℓ₀ 1)], fun β hβ => ?_⟩
  have hβ0 : 0 < β := by linarith [Real.exp_pos (max ℓ₀ 1)]
  have hl : max ℓ₀ 1 ≤ Real.log β := by
    rw [Real.le_log_iff_exp_le hβ0]; linarith
  have := h (Real.log β) (le_trans (le_max_left _ _) hl)
  have e : pLog A₁ p β ^ 2 / 4 = A₁ ^ 2 / 4 * Real.log β ^ (2 * p) := by
    unfold pLog; ring
  rw [e]; linarith

/-- The two sides of `hq`/`hbp` of `norm_setIntegral_blocksSplit_le_exp`, in the exact
form of that theorem: for `b ≥ 0`, `A₂ ≥ 0`, all large `β` satisfy `hq` and `hbp` with
`ρ = pLog A₁ p β`, `p = A₂ (log β)^{p₂}`, `h = H₀ log β`. -/
theorem tail_exponent_hq_hbp {A₁ A₂ H₀ b : ℝ} {p p₂ : ℕ} (hA₁ : 0 < A₁) (hA₂ : 0 ≤ A₂)
    (hp : 1 ≤ p) (hb : 0 ≤ b) (hexp : p₂ < 2 * p ∨ (p₂ = 2 * p ∧ A₂ < A₁ ^ 2 / 4)) (m W' : ℕ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      0 ≤ pLog A₁ p β ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2 - H₀ * Real.log β ∧
      b + A₂ * Real.log β ^ p₂ ≤
        pLog A₁ p β ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2 - H₀ * Real.log β := by
  obtain ⟨β₁, h1, hβ₁⟩ := tail_exponent_eventually (c := b) hA₁ hp hexp m W' (H₀ := H₀)
    (A₂ := A₂)
  refine ⟨β₁, h1, fun β hβ => ?_⟩
  have hl : 0 < Real.log β := Real.log_pos (by linarith)
  have := hβ₁ β hβ
  exact ⟨by nlinarith [mul_nonneg hA₂ (pow_nonneg hl.le p₂)], this⟩

/-- The comparison in the notation of the setting: `p₂(β_j) = p2Run A₂ p₂ bs j`,
`H_j = HRun H₀ bs j`, for a sequence with `bs j` large. -/
theorem tail_exponent_run {A₁ A₂ H₀ b : ℝ} {p p₂ : ℕ} (hA₁ : 0 < A₁) (hA₂ : 0 ≤ A₂)
    (hp : 1 ≤ p) (hb : 0 ≤ b) (hexp : p₂ < 2 * p ∨ (p₂ = 2 * p ∧ A₂ < A₁ ^ 2 / 4)) (m W' : ℕ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ (bs : ℕ → ℝ) (j : ℕ), β₀ ≤ bs j →
      0 ≤ pLog A₁ p (bs j) ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2 - HRun H₀ bs j ∧
      b + p2Run A₂ p₂ bs j ≤
        pLog A₁ p (bs j) ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2 - HRun H₀ bs j := by
  obtain ⟨β₀, h1, h⟩ := tail_exponent_hq_hbp hA₁ hA₂ hp hb hexp m W' (H₀ := H₀)
  exact ⟨β₀, h1, fun bs j hj => h (bs j) hj⟩

/-- **The landed typing constraints.**  For `T` with `T.Ok` and the exponent `p` of `p₁` equal
to `p₀`, `p₂ < 2p` holds (`2 p₀ > p₂`, condition (K)); `p₀ ≥ 1` since `p₂ ≥ 2d + 3`. -/
theorem tail_exponent_of_typing_ok {T : Typing} (hT : T.Ok) :
    1 ≤ T.p0 ∧ T.p2 < 2 * T.p0 := by
  have h1 := hT.p0_gt
  have h2 := hT.p2_ge
  exact ⟨by omega, h1⟩

/-- Necessity: if `2p < p₂` the inequality fails for all large `β` (so the exponent condition
is sharp in the exponents). -/
theorem not_tail_exponent_of_lt {A₁ A₂ H₀ c : ℝ} {p p₂ : ℕ} (hA₂ : 0 < A₂)
    (hH : 0 ≤ H₀) (hlt : 2 * p < p₂) :
    ∃ ℓ₀ : ℝ, ∀ ℓ : ℝ, ℓ₀ ≤ ℓ →
      ¬ (c + A₂ * ℓ ^ p₂ ≤ A₁ ^ 2 / 4 * ℓ ^ (2 * p) - H₀ * ℓ) := by
  obtain ⟨k, hk⟩ : ∃ k, p₂ = 2 * p + k + 1 := ⟨p₂ - 2 * p - 1, by omega⟩
  refine ⟨max 1 ((A₁ ^ 2 / 4 + |H₀| + |c| + 1) / A₂), fun ℓ hℓ => ?_⟩
  have h1 : 1 ≤ ℓ := le_trans (le_max_left _ _) hℓ
  have h2 : (A₁ ^ 2 / 4 + |H₀| + |c| + 1) / A₂ ≤ ℓ := le_trans (le_max_right _ _) hℓ
  rw [div_le_iff₀ hA₂] at h2
  have hP : (1:ℝ) ≤ ℓ ^ (2 * p) := one_le_pow₀ h1
  have hQ : ℓ ^ (2 * p) * ℓ ≤ ℓ ^ p₂ := by
    rw [← pow_succ]; exact pow_le_pow_right₀ h1 (by omega)
  have hQ0 : (0:ℝ) ≤ ℓ ^ (2 * p) := by positivity
  have hℓp : ℓ ≤ ℓ ^ p₂ := by simpa using pow_le_pow_right₀ h1 (by omega : 1 ≤ p₂)
  intro hcon
  have e1 : A₂ * ℓ ^ p₂ ≥ (A₁ ^ 2 / 4 + |H₀| + |c| + 1) * ℓ ^ (2 * p) := by
    nlinarith [mul_le_mul_of_nonneg_left hQ hA₂.le]
  have hl0 : 0 ≤ H₀ * ℓ := mul_nonneg hH (by linarith)
  have hcc : -|c| ≤ c := neg_abs_le c
  nlinarith [abs_nonneg H₀, abs_nonneg c, mul_le_mul_of_nonneg_left hP (abs_nonneg H₀),
    mul_le_mul_of_nonneg_left hP (abs_nonneg c)]

end Balaban.Green
