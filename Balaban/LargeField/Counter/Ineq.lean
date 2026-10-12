module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# Real inequalities behind the budget cases (Part I, §I.5.4)

Pure inequalities between real numbers; the statements of §I.5.4 reduce to these once the
quantities `τ`, `g`, `E`, `Φ`, `D̄` are fixed.
-/

@[expose] public section

namespace Balaban.LargeField.Ineq

/-- Case (1a): the new cubes pay for a restart with a short spine. -/
theorem small_pay {m r E τ g Φ : ℝ} (hm : 0 ≤ m) (hr : 1 ≤ r) (hE : 0 ≤ E) (hΦ : 0 ≤ Φ)
    (hτ : E + 1 ≤ τ) (hg : E + Φ + 1 ≤ g) :
    (m + r - 1) * E + Φ + 1 ≤ m * τ + r * g := by
  nlinarith [mul_nonneg hm (show 0 ≤ τ - E by linarith),
    mul_nonneg (show 0 ≤ r - 1 by linarith) (show 0 ≤ g - E by linarith)]

/-- Case (1b) and its analogues: a long spine after a restart is paid for either by the
contraction of the old spines `v H` or by the number `m + r - 1` of joining segments. -/
theorem big_pay {m r E τ g v H D B Pw Φ : ℝ} (hm : 0 ≤ m) (hr : 0 ≤ r) (hmr : 1 ≤ m + r)
    (hE : 0 ≤ E) (hτ : E + 1 ≤ τ) (hg : E + 1 ≤ g) (hv : 1 ≤ v) (hH : 0 ≤ H)
    (hDB : D ≤ B) (hB : 0 < B) (hlen : Pw ≤ H + (m + r - 1) * D)
    (h3 : Φ + 1 ≤ 1 / 2 * Pw) (h4 : Φ + 1 ≤ Pw / (2 * B)) :
    (m + r - 1) * E + Φ + 1 ≤ m * τ + r * g + v * H := by
  have hmτ : m * (E + 1) ≤ m * τ := by gcongr
  have hrg : r * (E + 1) ≤ r * g := by gcongr
  by_cases hH2 : Pw / 2 ≤ H
  · have : H ≤ v * H := by nlinarith
    nlinarith
  · push Not at hH2
    have h1 : Pw - H ≤ (m + r - 1) * D := by linarith
    have h2 : (m + r - 1) * D ≤ (m + r - 1) * B := by
      have : 0 ≤ m + r - 1 := by linarith
      gcongr
    have h5 : Pw / (2 * B) < m + r - 1 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith

/-- Case 2b/2a: a shift `Δ ≤ (m - 1) K` of the ripeness time is paid by `(m - 1) τ`. -/
theorem shift_pay {m Δ K Ab E τ : ℝ} (hm : 1 ≤ m) (hΔ : Δ ≤ (m - 1) * K) (hAb : 0 ≤ Ab)
    (hK : K * Ab + E ≤ τ) : Δ * Ab + (m - 1) * E ≤ (m - 1) * τ := by
  have h1 : Δ * Ab ≤ (m - 1) * K * Ab := by gcongr
  have h2 : (m - 1) * (K * Ab + E) ≤ (m - 1) * τ := by
    apply mul_le_mul_of_nonneg_left hK; linarith
  nlinarith

/-- Case 2b with a long spine: either the contracted old spines or the number of parts pay. -/
theorem pre_big {m E τ Φ Q : ℝ} (hm : 2 ≤ m) (hE : 0 ≤ E) (hτ : E + 1 ≤ τ) (hQ0 : 0 ≤ Q)
    (hQ : Φ ≤ Q ∨ Φ + 1 ≤ m) : Φ + (m - 1) * E + 1 ≤ m * τ + m + Q := by
  have hmτ : m * (E + 1) ≤ m * τ := by gcongr
  rcases hQ with h | h
  · nlinarith
  · nlinarith

end Balaban.LargeField.Ineq
