/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolvent
public import Balaban.LargeField.Base.BaseResolventDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# BASE-KERNEL-3 Theorem 1.1: decay of the base resolvent and its square root

The estimate (1.7) for `A_e(s)` on the chart domain `D = G.Ω 1` with the `ℓ¹` torus distance
`siteDist`: given block row/column-sum bound `J` and range `R` of `A_e(s)` (`baseOp`), and
`J (e^{gR} - 1) ≤ c/4`, the resolvent and the Stieltjes inverse square root decay like `e^{-g d}`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset
open scoped Matrix.Norms.L2Operator

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The `ℓ¹` torus distance between two chart sites. -/
noncomputable def siteDist (G : GeneratingSet d L N₀ 1 ϱ) (z w : G.Ω 1) : ℝ :=
  torusDist d (N₀ * L ^ 1) z.1 w.1

section Dist

variable (G : GeneratingSet d L N₀ 1 ϱ)

theorem siteDist_self (z : G.Ω 1) : siteDist G z z = 0 := torusDist_self_eq_zero _

theorem siteDist_comm (z w : G.Ω 1) : siteDist G z w = siteDist G w z :=
  torusDist_comm_gen _ _

theorem siteDist_triangle (z y w : G.Ω 1) : siteDist G z w ≤ siteDist G z y + siteDist G y w := by
  exact dist_triangle (show L1Torus d (N₀ * L ^ 1) from z.1) y.1 w.1

end Dist

section Decay

variable (G : GeneratingSet d L N₀ 1 ϱ) {N : ℕ}

/-- **BASE-KERNEL-3 Theorem 1.1, (1.7).**  Let `J` bound the block row and column sums of `A_e(s)`
and `R ≥ 0` its site range.  If `g ≥ 0` and `J (e^{gR} - 1) ≤ c/4`, then for `x ≥ 0` the
`(z,w)` block of the resolvent `𝒞_{e,x}(s)` satisfies `‖·‖_op ≤ (c/4 + x)⁻¹ e^{-g d(z,w)}`. -/
theorem baseResolvent_block_decay {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)
    {J R g x : ℝ} (hx : 0 ≤ x)
    (hR : ∀ z y, blockOf (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s)) z y ≠ 0 →
      siteDist G z y ≤ R) (hR0 : 0 ≤ R)
    (hrow : ∀ z, ∑ y, ‖blockOf (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α s)) z y‖ ≤ J)
    (hcol : ∀ y, ∑ z, ‖blockOf (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α s)) z y‖ ≤ J)
    (hg : 0 ≤ g) (hJ : J * (Real.exp (g * R) - 1) ≤ baseCoercivity L / 4) (z w : G.Ω 1) :
    ‖blockOf (baseResolvent N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s) x) z w‖ ≤
      (baseCoercivity L / 4 + x)⁻¹ * Real.exp (-g * siteDist G z w) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc := baseCoercivity_pos hL
  have hcoer := baseOp_isCoercive_of_close G hν ha hα hη0 hη hs e he
  have h := (resolvent_block_decay (siteDist G) (siteDist_self G) (siteDist_comm G)
    (siteDist_triangle G) (by linarith : 0 < baseCoercivity L / 2) hcoer hx hR hR0 hrow hcol hg
    (by linarith)).2 z w
  have e2 : baseCoercivity L / 2 / 2 = baseCoercivity L / 4 := by ring
  rw [e2] at h
  exact h

/-- **BASE-KERNEL-3 Theorem 1.1, (1.7), square root.**  Under the same hypotheses
`‖A_e(s)^{-1/2}(z,w)‖_op ≤ √(4/c) e^{-g d(z,w)}`. -/
theorem baseSqrt_block_decay [Nonempty (G.Ω 1 × Fin N)] {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) {s : FineBond d L N₀ → ℂ}
    (hs : s ∈ baseParamNbhd G η) (e : G.Ω 1 → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1)
    {J R g : ℝ}
    (hR : ∀ z y, blockOf (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s)) z y ≠ 0 →
      siteDist G z y ≤ R) (hR0 : 0 ≤ R)
    (hrow : ∀ z, ∑ y, ‖blockOf (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α s)) z y‖ ≤ J)
    (hcol : ∀ y, ∑ z, ‖blockOf (baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a ν α s)) z y‖ ≤ J)
    (hg : 0 ≤ g) (hJ : J * (Real.exp (g * R) - 1) ≤ baseCoercivity L / 4) (z w : G.Ω 1) :
    ‖blockOf (Balaban.Localization.sqrtMat (baseOp N (fun z i => (e z i : ℂ))
        (baseHamiltonian G a ν α s))) z w‖ ≤
      Real.sqrt (4 / baseCoercivity L) * Real.exp (-g * siteDist G z w) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc := baseCoercivity_pos hL
  have hcoer := baseOp_isCoercive_of_close G hν ha hα hη0 hη hs e he
  have h := sqrtMat_block_decay (siteDist G) (siteDist_self G) (siteDist_comm G)
    (siteDist_triangle G) (by linarith : 0 < baseCoercivity L / 2) hcoer hR hR0 hrow hcol hg
    (by linarith) z w
  have e2 : (Real.sqrt (baseCoercivity L / 2 / 2))⁻¹ = Real.sqrt (4 / baseCoercivity L) := by
    rw [← Real.sqrt_inv]; congr 1; field_simp; ring
  rw [e2] at h
  exact h

end Decay

end Balaban.LargeField.Base
