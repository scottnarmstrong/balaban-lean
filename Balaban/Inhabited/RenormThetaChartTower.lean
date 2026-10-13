/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Fluctuation.RenormThetaChart
public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.RenormThetaChartTowerG
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
  exact thetaChartMargin_of_stepTowerRenSolG R.toG

/-- `ThetaChartMargin` is inhabited, at the radii of the shared tower. -/
theorem exists_thetaChartMargin (κmin : ℝ) :
    ∃ (εren εstep r₀ : ℝ), Nonempty (ThetaChartMargin 3 3 2 εren εstep r₀) := by
  obtain ⟨R⟩ := exists_stepTowerRenSol κmin
  exact ⟨_, _, _, ⟨thetaChartMargin_of_stepTowerRenSol R⟩⟩

end Balaban.Inhabited
