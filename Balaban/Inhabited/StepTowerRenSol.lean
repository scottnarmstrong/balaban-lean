/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenEnd
public import Balaban.Inhabited.StepTowerRenEndG
public import Balaban.Inhabited.TowerCoreRatesRenSol
public import Balaban.Fluctuation.RenormExpLemma35
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower with the renormalized solution

`StepTowerRenSol κmin` extends `StepTowerRenEnd κmin` by the margin `K₁ ξ₁ t < δ_*` and the two
radius margins `K₁ ξ₁ t + 3 r₀ ≤ δ_*`, `8 t r₀ ≤ δ_*` of `exists_isRenSol` at `r_F = r₀`.
`StepTowerRenSolG` is the general record and `StepTowerRenSol.toG` the bridge; the producers
`exists_stepTowerRenSolG`, `exists_stepTowerRenSol` are in `Balaban.Inhabited.StepTowerGProducers`.
At every scale,
`exists_isRenSol_scale_of_tower` gives the renormalized solution `F` and
`renEndpoint_scale_of_tower` the endpoint `s = 1` with no hypothesis besides the tower and the
scale conditions.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- The shared tower with the endpoint margin and the margins of the renormalized solution. -/
structure StepTowerRenSol (κmin : ℝ) extends StepTowerRenEnd κmin where
  sol_margin : bgK1 3 3 2 * (xiC1 3 * t) < deltaStar 3 3 2
  sol_K : bgK1 3 3 2 * (xiC1 3 * t) + 3 * r₀ ≤ deltaStar 3 3 2
  sol_ζ : 8 * t * r₀ ≤ deltaStar 3 3 2

/-- The general tower with the endpoint margin and the margins of the renormalized solution. -/
structure StepTowerRenSolG (d L N : ℕ) [NeZero L] (κmin : ℝ) extends
    StepTowerRenEndG d L N κmin where
  sol_margin : bgK1 d L N * (xiC1 d * t) < deltaStar d L N
  sol_K : bgK1 d L N * (xiC1 d * t) + 3 * r₀ ≤ deltaStar d L N
  sol_ζ : 8 * t * r₀ ≤ deltaStar d L N

/-- **The bridge**: the fixed `3, 3, 2` record with the solution margins is a general one. -/
noncomputable def StepTowerRenSol.toG {κmin : ℝ} (T : StepTowerRenSol κmin) :
    StepTowerRenSolG 3 3 2 κmin :=
  { T.toStepTowerRenEnd.toG with
    sol_margin := T.sol_margin
    sol_K := T.sol_K
    sol_ζ := T.sol_ζ }

namespace StepTowerRenSol

variable {κmin : ℝ} (T : StepTowerRenSol κmin)

@[simp] theorem toG_toStepTowerRenEndG :
    T.toG.toStepTowerRenEndG = T.toStepTowerRenEnd.toG := rfl
@[simp] theorem toG_r₀ : T.toG.r₀ = T.r₀ := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl

end StepTowerRenSol

/-- A general tower with the solution margins at `3, 3, 2` with `κ₀ = a_Ent + 2` and `m₀ = 1`
gives a fixed tower with the solution margins. -/
theorem StepTowerRenSolG.nonempty_fixed_of_three {κmin : ℝ} (T : StepTowerRenSolG 3 3 2 κmin)
    (h0 : T.κ0 = aEnt 3 3 + 2) (hm : T.m₀ = 1) : Nonempty (StepTowerRenSol κmin) := by
  exact ⟨StepTowerRenSol.mk (StepTowerRenEnd.mk (StepTowerRen.mk (T.toStepTowerG.ofThree h0 hm)
    T.ren_margin T.r₀ T.r₀_pos T.r₀_le T.D₀_le_one T.D₀_le_star T.D₁_le_star) T.end_margin)
    T.sol_margin T.sol_K T.sol_ζ⟩

end Balaban.Inhabited
