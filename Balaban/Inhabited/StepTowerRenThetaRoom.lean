/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Room at the towers of step radius `(1 + c r₀) ε_{k+1}`

The radii of the towers whose chart contains the renormalized datum: step radius
`t_k = λ ε_{k+1}`, `λ = 1 + K₂ (3/2) r₀`, closeness bound `δ₃ = Q t_k`, fluctuation radius
`δ₁ = min(t_k, η λ ε_k)` and bound `δ_fl = F δ₁`.  The room `t_k + K₂ δ₃ + K₂ δ_fl ≤ ε_j`
(`j ≤ k`) is against the *class* radii `ε_j`, not `λ ε_j`; it holds when
`K₂ (3/2) r₀ (3 + q) ≤ 1 - q` (`ren_room`), because the gap `ε_{k+1} ≤ q ε_k` leaves the slack
`q + (1 - q)/2 + (1 - q)/4 = (3 + q)/4 < 1` at `λ = 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

/-- **The scale factor is at most `4 / (3 + q)`.**  From `K (3/2) r₀ (3 + q) ≤ 1 - q`. -/
theorem ren_lam_le {K r₀ q lam : ℝ} (h : K * ((3 / 2 : ℝ) * r₀) * (3 + q) ≤ 1 - q)
    (hlam : lam = 1 + K * ((3 / 2 : ℝ) * r₀)) : lam * (3 + q) ≤ 4 := by
  rw [hlam]; nlinarith

/-- **The room against the class radii.**  For `ε` antitone, positive with `ε_{j+1} ≤ q ε_j`,
`0 ≤ Q`, `0 < F`, `K Q ≤ (1 - q)/(2q)`, `η = (1 - q)/(4 K F)` and `λ (3 + q) ≤ 4`, `1 ≤ λ`, the
radii `t = λ ε_{k+1}`, `δ₃ = Q t`, `δ₁ = min(t, η λ ε_k)`, `δ_fl = F δ₁` satisfy
`t + K δ₃ + K δ_fl ≤ ε_j` for every `j ≤ k`. -/
theorem ren_room {ε : ℕ → ℝ} {K Q F η q lam : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hK : 0 < K)
    (hQ : 0 ≤ Q) (hF : 0 < F) (hKQ : K * Q ≤ (1 - q) / (2 * q))
    (hη : η = (1 - q) / (4 * K * F)) (hanti : Antitone ε) (hpos : ∀ j, 0 < ε j)
    (hgap : ∀ j, ε (j + 1) ≤ q * ε j) (hl1 : 1 ≤ lam) (hl : lam * (3 + q) ≤ 4) (k : ℕ) :
    ∀ j ≤ k, lam * ε (k + 1) + K * (Q * (lam * ε (k + 1))) +
      K * (F * min (lam * ε (k + 1)) (η * (lam * ε k))) ≤ ε j := by
  intro j hj
  have hl0 : 0 < lam := by linarith
  have hk0 := hpos k
  have hKFη : K * F * η = (1 - q) / 4 := by
    rw [hη]; field_simp
  have hmin : min (lam * ε (k + 1)) (η * (lam * ε k)) ≤ η * (lam * ε k) := min_le_right _ _
  have h1 : K * (F * min (lam * ε (k + 1)) (η * (lam * ε k))) ≤
      K * F * η * (lam * ε k) := by
    have := mul_le_mul_of_nonneg_left hmin (mul_nonneg hK.le hF.le)
    calc _ = K * F * min (lam * ε (k + 1)) (η * (lam * ε k)) := by ring
      _ ≤ K * F * (η * (lam * ε k)) := this
      _ = _ := by ring
  have hkq : q * (K * Q) ≤ (1 - q) / 2 := by
    have h := mul_le_mul_of_nonneg_left hKQ hq0.le
    have e : q * ((1 - q) / (2 * q)) = (1 - q) / 2 := by field_simp
    linarith
  have h2 : lam * ε (k + 1) ≤ lam * (q * ε k) :=
    mul_le_mul_of_nonneg_left (hgap k) hl0.le
  have h3 : lam * ε (k + 1) + K * (Q * (lam * ε (k + 1))) =
      (1 + K * Q) * (lam * ε (k + 1)) := by ring
  have h4 : (1 + K * Q) * (lam * ε (k + 1)) ≤ (1 + K * Q) * (lam * (q * ε k)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : (1 + K * Q) * (lam * (q * ε k)) ≤ (q + (1 - q) / 2) * (lam * ε k) := by
    have : (1 + K * Q) * (lam * (q * ε k)) = (q + q * (K * Q)) * (lam * ε k) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h6 : (q + (1 - q) / 2 + (1 - q) / 4) * (lam * ε k) ≤ ε k := by
    have : (q + (1 - q) / 2 + (1 - q) / 4) * lam ≤ 1 := by nlinarith
    nlinarith
  rw [hKFη] at h1
  have h7 : ε k ≤ ε j := hanti hj
  nlinarith

end Balaban.Inhabited
