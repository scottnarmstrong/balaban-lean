/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.MarkedCoupled
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 3.3 of OBSERVABLES.md: the Cauchy radii (three cases)

The marks of the observable terms are analytic in the field parameter `z` (the composite domain
`ψ_k^{(j)}(ψ^{(k)}(θ) + zψ')`, `|z| < r₀`) and the measure in the coupling `σ`
(`|σ| < r₁ = c c₁ β_k^{1/2} / p₁`), OBSERVABLES (B4), P9 p. 503.  The radius `r₀` is one of three
cases, according to the function being localized:

* `RadiusCase.background`: `r₀ = c c₁ / p₁` (the background `φ_k` and `G^{(j)}`);
* `RadiusCase.old`: `r₀ = c α ε_{j+1} / p₁` (the terms `M^{(j)}`, `R^{ij}` of an old scale `j ≤ k`);
* `RadiusCase.new`: `r₀ = c α ε_{k+1} / p₁` (the new scale `k + 1`).

`two_variable_schwarz` is the form of the Cauchy estimates used in (3.5), (3.6), (3.37)-(3.41): a
function holomorphic and bounded on a bidisc that vanishes on the faces `σ = 0` and `z = 0` is
bounded by `B |σ||z| / (r₁ r₀)` (two applications of the Schwarz lemma);
`inv_div_sq_le` is `r₁/(r₁ - 1)² ≤ 4/r₁` for `r₁ ≥ 2`.
-/

@[expose] public section

namespace Balaban.Observables

open Metric

/-- The three cases of the field radius `r₀` (P9 p. 503). -/
inductive RadiusCase
  /-- `r₀ = c c₁ / p₁` -/
  | background
  /-- `r₀ = c α ε_{j+1} / p₁` -/
  | old
  /-- `r₀ = c α ε_{k+1} / p₁` -/
  | new

/-- The coupling radius `r₁ = c c₁ β_k^{1/2} / p₁`. -/
noncomputable def couplingRadius (c c₁ βk p₁ : ℝ) : ℝ := c * c₁ * Real.sqrt βk / p₁

/-- The field radius `r₀` in each of the three cases; `εo = ε_{j+1}`, `εn = ε_{k+1}`. -/
noncomputable def fieldRadius (c c₁ α εo εn p₁ : ℝ) : RadiusCase → ℝ
  | .background => c * c₁ / p₁
  | .old => c * α * εo / p₁
  | .new => c * α * εn / p₁

theorem fieldRadius_pos {c c₁ α εo εn p₁ : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hα : 0 < α)
    (hεo : 0 < εo) (hεn : 0 < εn) (hp : 0 < p₁) (case : RadiusCase) :
    0 < fieldRadius c c₁ α εo εn p₁ case := by
  cases case <;> simp only [fieldRadius] <;> positivity

theorem couplingRadius_pos {c c₁ βk p₁ : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hβ : 0 < βk)
    (hp : 0 < p₁) : 0 < couplingRadius c c₁ βk p₁ := by
  unfold couplingRadius
  have := Real.sqrt_pos.2 hβ
  positivity

/-- `r₁ ≥ 2` once `2 p₁ ≤ c c₁ √β_k`. -/
theorem two_le_couplingRadius {c c₁ βk p₁ : ℝ} (hp : 0 < p₁)
    (h : 2 * p₁ ≤ c * c₁ * Real.sqrt βk) : 2 ≤ couplingRadius c c₁ βk p₁ := by
  unfold couplingRadius
  rw [le_div_iff₀ hp]
  linarith

/-- `r/(r - 1)² ≤ 4/r` for `r ≥ 2`. -/
theorem inv_div_sq_le {r : ℝ} (hr : 2 ≤ r) : r / (r - 1) ^ 2 ≤ 4 / r := by
  have h1 : 0 < r - 1 := by linarith
  have h2 : 0 < r := by linarith
  rw [div_le_div_iff₀ (by positivity) h2]
  nlinarith

/-- **Two-variable Schwarz lemma.**  If `f` is holomorphic in each variable on the bidisc
`|σ| < r₁`, `|z| < r₀`, bounded by `B`, and vanishes on `σ = 0` and on `z = 0`, then
`|f(σ, z)| ≤ B |σ| |z| / (r₁ r₀)`. -/
theorem two_variable_schwarz {f : ℂ → ℂ → ℂ} {r₁ r₀ B : ℝ} (h₁ : 0 < r₁) (h₀ : 0 < r₀)
    (hσ : ∀ z, ‖z‖ < r₀ → DifferentiableOn ℂ (fun σ => f σ z) (ball 0 r₁))
    (hz : ∀ σ, ‖σ‖ < r₁ → DifferentiableOn ℂ (fun z => f σ z) (ball 0 r₀))
    (hB : ∀ σ z, ‖σ‖ < r₁ → ‖z‖ < r₀ → ‖f σ z‖ ≤ B)
    (hf₁ : ∀ z, f 0 z = 0) (hf₀ : ∀ σ, f σ 0 = 0)
    {σ z : ℂ} (hs : ‖σ‖ < r₁) (hzz : ‖z‖ < r₀) :
    ‖f σ z‖ ≤ B * ‖σ‖ * ‖z‖ / (r₁ * r₀) := by
  have step1 : ∀ w, ‖w‖ < r₀ → ‖f σ w‖ ≤ B * ‖σ‖ / r₁ := fun w hw =>
    norm_le_mul_div_of_vanish_zero h₁ (hσ w hw) (fun s hs' => hB s w hs' hw) (hf₁ w) hs
  have := norm_le_mul_div_of_vanish_zero h₀ (hz σ hs) step1 (hf₀ σ) hzz
  calc ‖f σ z‖ ≤ B * ‖σ‖ / r₁ * ‖z‖ / r₀ := this
    _ = B * ‖σ‖ * ‖z‖ / (r₁ * r₀) := by field_simp

end Balaban.Observables
