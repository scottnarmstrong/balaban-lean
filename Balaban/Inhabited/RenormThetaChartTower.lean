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
# The margin of the chart inclusion at the shared tower

For a tower `R : StepTowerRenSol κmin`, with renormalization radius `εren = R.t` and parameter
radius `R.r₀`, every numerical field of `ThetaChartMargin 3 3 2 R.t εs R.r₀` follows from the fields
of the tower, where `εs = R.t + xiK2 3 3 2 * ((3/2) * R.t * R.r₀)`.  Hence `ThetaChartMargin` is
inhabited.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization

/-- **The margin at the tower**: every field of `ThetaChartMargin 3 3 2 R.t εs R.r₀`,
`εs = R.t + xiK2 3 3 2 * ((3/2) * R.t * R.r₀)`, follows from the fields of the tower. -/
theorem thetaChartMargin_of_stepTowerRenSol {κmin : ℝ} (R : StepTowerRenSol κmin) :
    ThetaChartMargin 3 3 2 R.t (R.t + xiK2 3 3 2 * ((3 / 2 : ℝ) * R.t * R.r₀)) R.r₀ := by
  obtain ⟨hC⟩ := R.core
  have ht := R.t_pos
  have hr := R.r₀_pos
  have hrle := R.r₀_le
  have hd : 0 < 3 := by norm_num
  have hds1 : deltaStar 3 3 2 ≤ 1 := deltaStar_le_one
  have hδ : (3 / 2 : ℝ) * R.t * R.r₀ ≤ 2 * R.t := by nlinarith
  have hxt : 0 ≤ xiC1 3 * R.t := by have := one_le_xiC1 3; positivity
  have hxc : xiC1 3 * R.t ≤ bgC1 3 3 2 := hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)
  refine ⟨ht, hr, by positivity, ?_, hC.small1, ?_, ?_, R.sol_margin.le, ?_, rfl⟩
  · linarith [R.t_cap]
  · have h1 := R.bg1_cap
    have h2 := compC4_ge 3
    have h3 := bgK1_ge_one (d := 3) (L := 3) (N := 2)
    have h4 : xiC1 3 * R.t ≤ 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * R.t))) := by
      have : bgK1 3 3 2 * (xiC1 3 * R.t) ≥ xiC1 3 * R.t := by nlinarith
      nlinarith
    nlinarith
  · linarith [R.t_cap]
  · have h1 := (bgC1_facts (d := 3) (L := 3) (N := 2) hd hxc).2.2.2
    have h2 := R.bg0_cap
    have h3 := cK2_pos 3 3 2
    nlinarith

/-- `ThetaChartMargin` is inhabited, at the radii of the shared tower. -/
theorem exists_thetaChartMargin (κmin : ℝ) :
    ∃ (εren εstep r₀ : ℝ), Nonempty (ThetaChartMargin 3 3 2 εren εstep r₀) := by
  obtain ⟨R⟩ := exists_stepTowerRenSol κmin
  exact ⟨_, _, _, ⟨thetaChartMargin_of_stepTowerRenSol R⟩⟩

end Balaban.Inhabited
