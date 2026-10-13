/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormThetaChart
public import Balaban.Inhabited.StepTowerRenSol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The margin of the chart inclusion at the general tower

For `R : StepTowerRenSolG d L N κmin`, with renormalization radius `εren = R.t` and parameter
radius `R.r₀`, every numerical field of `ThetaChartMargin d L N R.t εs R.r₀` follows from the
fields of the tower, where `εs = R.t + xiK2 d L N * ((3/2) * R.t * R.r₀)`.  The fixed `3, 3, 2`
statement `thetaChartMargin_of_stepTowerRenSol` is the case `d = L = 3`, `N = 2`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization

/-- **The margin at the general tower**: every field of
`ThetaChartMargin d L N R.t εs R.r₀`, `εs = R.t + xiK2 d L N * ((3/2) * R.t * R.r₀)`, follows from
the fields of the tower. -/
theorem thetaChartMargin_of_stepTowerRenSolG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) :
    ThetaChartMargin d L N R.t (R.t + xiK2 d L N * ((3 / 2 : ℝ) * R.t * R.r₀)) R.r₀ := by
  obtain ⟨hC⟩ := R.core
  have ht := R.t_pos
  have hr := R.r₀_pos
  have hrle := R.r₀_le
  have hd : 0 < d := by have := R.hd; omega
  have hds1 : deltaStar d L N ≤ 1 := deltaStar_le_one
  have hδ : (3 / 2 : ℝ) * R.t * R.r₀ ≤ 2 * R.t := by nlinarith
  have hxt : 0 ≤ xiC1 d * R.t := by have := one_le_xiC1 d; positivity
  have hxc : xiC1 d * R.t ≤ bgC1 d L N := hC.c7le.trans (c7_le_bgC1 d L N R.BG R.κ)
  refine ⟨ht, hr, by positivity, ?_, hC.small1, ?_, ?_, R.sol_margin.le, ?_, rfl⟩
  · linarith [R.t_cap]
  · have h1 := R.bg1_cap
    have h2 := compC4_ge d
    have h3 := bgK1_ge_one (d := d) (L := L) (N := N)
    have h4 : xiC1 d * R.t ≤ 2 * (compC4 d * (bgK1 d L N * (xiC1 d * R.t))) := by
      have : bgK1 d L N * (xiC1 d * R.t) ≥ xiC1 d * R.t := by nlinarith
      nlinarith
    nlinarith
  · linarith [R.t_cap]
  · have h1 := (bgC1_facts (d := d) (L := L) (N := N) hd hxc).2.2.2
    have h2 := R.bg0_cap
    have h3 := cK2_pos d L N
    nlinarith

end Balaban.Inhabited
