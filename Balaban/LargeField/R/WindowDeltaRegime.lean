/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Analytic.Constants
public import Balaban.SmallField.Xi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential

/-!
# The regime `3 d L δ_j ≲ ε_{j+1}` from the running constants (blocker 4)

The tolerances of the domain conditions are `δ_j = (β_j a)^{-1/2} p₀(β_j)`
(P5 p. 498, `deltaRun`), the radii of the class domain `Ξ^c` are
`ε_j = α₀ (1 + ∑_{m ≥ j} m^{-2}) L^{-jα}` (P4 (H.1), `epsSeq`) with `d - 2 - 2α = 2γ`, `γ > 0`.
The a priori bound `δ_j ≤ δ̄(λ̂_j) = e A₀ λ̂_j^{p₀} e^{-λ̂_j / 2}` (`deltaRun_le_bar`) decays like
`L^{-(d-2) j / 2} λ̂_j^{p₀}`, which is faster than `L^{-α j}` by the factor `L^{-γ j}` against the
polynomial `λ̂_j^{p₀}`.  Hence, for `λ̂_0 = log (β a) + 1` large against the constants, every `j`
satisfies `C δ_j ≤ ε_{j+1}`, with `C = (2 K₁ + 2) · 3 d L` for the passage of `XiCOneReal` from a
real datum of radius `3 d L δ_j` (`xiCOneReal_of_inDomainR`).

* `deltaBar_lamHat_le_epsSeq`: the comparison of `δ̄(λ̂_j)` with `ε_{j+1}`, for all `j`;
* `deltaRun_le_epsSeq`: the same for the running `δ_j` under `RunningHyp`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.SmallField

/-- The a priori value at the scale `j`: `λ̂_j = λ̂_0 + j θ`. -/
theorem lamHat_eq_add (d L : ℕ) (β a : ℝ) (j : ℕ) :
    lamHat d L β a j = lamHat d L β a 0 + (j : ℝ) * thetaOf d L := by
  unfold lamHat
  push_cast
  ring

/-- **`C δ̄(λ̂_j) ≤ ε_{j+1}` for every `j`** once `λ̂_0` is large against `C`, `A₀`, `p₀`, `α₀`
and `γ`: with `κ = γ / (2 (d - 2))`, the condition is
`C e A₀ p₀! κ^{-p₀} L^α ≤ α₀ e^{λ̂_0 / 4}`. -/
theorem deltaBar_lamHat_le_epsSeq {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {α γ α₀ : ℝ} (hα : 0 ≤ α)
    (hα₀ : 0 < α₀) (hγ : 0 < γ) (hrel : (d : ℝ) - 2 - 2 * α = 2 * γ) {A0 C : ℝ} (hA0 : 0 ≤ A0)
    (hC : 0 ≤ C) (p0 : ℕ) {β a : ℝ} (hx0 : 0 ≤ lamHat d L β a 0)
    (hcond : C * (Real.exp 1 * A0 * (p0.factorial : ℝ) / (γ / (2 * ((d : ℝ) - 2))) ^ p0) *
        (L : ℝ) ^ α ≤ α₀ * Real.exp (lamHat d L β a 0 / 4)) (j : ℕ) :
    C * deltaBar A0 p0 (lamHat d L β a j) ≤ epsSeq L α α₀ (j + 1) := by
  set x0 := lamHat d L β a 0 with hx0def
  set θ := thetaOf d L with hθ
  have hD : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hL1 : (1 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL1
  have hθeq : θ = ((d : ℝ) - 2) * Real.log L := by
    rw [hθ]; unfold thetaOf
    rw [Nat.cast_sub (by omega : 2 ≤ d)]
    push_cast
    ring
  set κ : ℝ := γ / (2 * ((d : ℝ) - 2)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ4 : κ ≤ 1 / 4 := by
    rw [hκ, div_le_iff₀ (by positivity)]
    nlinarith
  set t := lamHat d L β a j with ht
  have htj : t = x0 + (j : ℝ) * θ := lamHat_eq_add d L β a j
  have ht0 : 0 ≤ t := by
    rw [htj]; have : 0 ≤ (j : ℝ) * θ := by rw [hθeq]; positivity
    linarith
  -- polynomial against exponential
  have hpoly : t ^ p0 ≤ (p0.factorial : ℝ) * Real.exp (κ * t) / κ ^ p0 := by
    have h := Real.pow_div_factorial_le_exp (κ * t) (by positivity) p0
    rw [div_le_iff₀ (by positivity)] at h
    rw [le_div_iff₀ (by positivity)]
    calc t ^ p0 * κ ^ p0 = (κ * t) ^ p0 := by rw [mul_pow]; ring
      _ ≤ Real.exp (κ * t) * p0.factorial := h
      _ = _ := by ring
  -- the exponential decay in `j`
  have hD' : (d : ℝ) - 2 = 2 * α + 2 * γ := by linarith
  have hkθ : (1 / 2 - κ) * θ = (α + γ / 2) * Real.log L := by
    rw [hθeq, hκ, hD']
    have h2 : (0 : ℝ) < 2 * α + 2 * γ := by linarith
    field_simp
    ring
  have hLpow : ((L : ℝ) ^ (-α)) ^ j = Real.exp (-(α * Real.log L) * j) := by
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_nat_mul]
    congr 1
    ring
  have hdec : Real.exp (κ * t - t / 2) ≤ Real.exp (-(x0 / 4)) * ((L : ℝ) ^ (-α)) ^ j := by
    rw [hLpow, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have e1 : κ * t - t / 2 = -((1 / 2 - κ) * x0) - (1 / 2 - κ) * θ * j := by
      rw [htj]; ring
    rw [e1, hkθ]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h1 : x0 / 4 ≤ (1 / 2 - κ) * x0 := by nlinarith
    have h2 : α * Real.log L * j ≤ (α + γ / 2) * Real.log L * j := by
      have : 0 ≤ γ / 2 * Real.log L * j := by positivity
      nlinarith
    nlinarith
  -- assemble
  have hE : Real.exp 1 * A0 * t ^ p0 * Real.exp (-t / 2) ≤
      Real.exp 1 * A0 * ((p0.factorial : ℝ) / κ ^ p0) * (Real.exp (-(x0 / 4)) * ((L : ℝ) ^ (-α)) ^ j) := by
    have hexp : Real.exp (κ * t) * Real.exp (-t / 2) = Real.exp (κ * t - t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp 1 * A0 * t ^ p0 * Real.exp (-t / 2)
        ≤ Real.exp 1 * A0 * ((p0.factorial : ℝ) * Real.exp (κ * t) / κ ^ p0) * Real.exp (-t / 2) := by
          gcongr
      _ = Real.exp 1 * A0 * ((p0.factorial : ℝ) / κ ^ p0) * Real.exp (κ * t - t / 2) := by
          rw [← hexp]; ring
      _ ≤ _ := by gcongr
  have hα₀' : α₀ * ((L : ℝ) ^ (-α)) ^ (j + 1) ≤ epsSeq L α α₀ (j + 1) := by
    unfold epsSeq
    have h1 := epsTail_pos (j + 1)
    have hq : 0 ≤ ((L : ℝ) ^ (-α)) ^ (j + 1) := by positivity
    have : 1 ≤ epsTail (j + 1) := by
      unfold epsTail
      have : 0 ≤ ∑' m : ℕ, if j + 1 ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
        tsum_nonneg fun m => by split_ifs <;> positivity
      linarith
    nlinarith [mul_nonneg hα₀.le hq]
  refine le_trans ?_ hα₀'
  unfold deltaBar
  have hLa : 0 < (L : ℝ) ^ α := by positivity
  have hLm : ((L : ℝ) ^ (-α)) = ((L : ℝ) ^ α)⁻¹ := Real.rpow_neg (by positivity) α
  have hc2 : C * (Real.exp 1 * A0 * ((p0.factorial : ℝ) / κ ^ p0)) ≤ α₀ * Real.exp (x0 / 4) * ((L : ℝ) ^ (-α)) := by
    rw [hLm, ← div_eq_mul_inv, le_div_iff₀ hLa]
    calc C * (Real.exp 1 * A0 * ((p0.factorial : ℝ) / κ ^ p0)) * (L : ℝ) ^ α
        = C * (Real.exp 1 * A0 * (p0.factorial : ℝ) / κ ^ p0) * (L : ℝ) ^ α := by ring
      _ ≤ _ := hcond
  calc C * (Real.exp 1 * A0 * t ^ p0 * Real.exp (-t / 2))
      ≤ C * (Real.exp 1 * A0 * ((p0.factorial : ℝ) / κ ^ p0) *
          (Real.exp (-(x0 / 4)) * ((L : ℝ) ^ (-α)) ^ j)) := by gcongr
    _ = (C * (Real.exp 1 * A0 * ((p0.factorial : ℝ) / κ ^ p0))) *
          (Real.exp (-(x0 / 4)) * ((L : ℝ) ^ (-α)) ^ j) := by ring
    _ ≤ (α₀ * Real.exp (x0 / 4) * ((L : ℝ) ^ (-α))) *
          (Real.exp (-(x0 / 4)) * ((L : ℝ) ^ (-α)) ^ j) := by gcongr
    _ = α₀ * ((L : ℝ) ^ (-α)) ^ (j + 1) := by
          have : Real.exp (x0 / 4) * Real.exp (-(x0 / 4)) = 1 := by
            rw [← Real.exp_add]; simp
          calc (α₀ * Real.exp (x0 / 4) * ((L : ℝ) ^ (-α))) *
              (Real.exp (-(x0 / 4)) * ((L : ℝ) ^ (-α)) ^ j)
              = α₀ * (Real.exp (x0 / 4) * Real.exp (-(x0 / 4))) * (((L : ℝ) ^ (-α)) * ((L : ℝ) ^ (-α)) ^ j) := by ring
            _ = _ := by rw [this, pow_succ']; ring

/-- **`C δ_j ≤ ε_{j+1}` for every `j` for the running tolerances `δ_j = (β_j a)^{-1/2} p₀(β_j)`**
under the running hypothesis (I.2): the range condition is `3 ≤ λ̂_0` and
`C e A₀ p₀! κ^{-p₀} L^α ≤ α₀ e^{λ̂_0 / 4}` with `κ = γ / (2 (d - 2))`, `d - 2 - 2α = 2γ`
(the regime `λ = log (β a)` large of P5–P7 against the fixed `α₀`). -/
theorem deltaRun_le_epsSeq {d L : ℕ} {β ν a ε : ℝ} {b nu : ℕ → ℝ}
    (h : RunningHyp d L β ν a ε b nu) (hd3 : 3 ≤ d) {α γ α₀ : ℝ} (hα : 0 ≤ α) (hα₀ : 0 < α₀)
    (hγ : 0 < γ) (hrel : (d : ℝ) - 2 - 2 * α = 2 * γ) {A0 C : ℝ} (hA0 : 0 ≤ A0) (hC : 0 ≤ C)
    (p0 : ℕ) (h3 : 3 ≤ lamHat d L β a 0)
    (hcond : C * (Real.exp 1 * A0 * (p0.factorial : ℝ) / (γ / (2 * ((d : ℝ) - 2))) ^ p0) *
        (L : ℝ) ^ α ≤ α₀ * Real.exp (lamHat d L β a 0 / 4)) (j : ℕ) :
    C * deltaRun A0 p0 a b j ≤ epsSeq L α α₀ (j + 1) :=
  le_trans (mul_le_mul_of_nonneg_left (h.deltaRun_le_bar hA0 p0 h3 j) hC)
    (deltaBar_lamHat_le_epsSeq hd3 h.hL hα hα₀ hγ hrel hA0 hC p0 (by linarith) hcond j)

end Balaban.LargeField
