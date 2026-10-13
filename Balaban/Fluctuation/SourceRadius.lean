/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceRadiusCarriers
public import Balaban.Fluctuation.SourceFamilyRelative
public import Balaban.Inhabited.SourceExponentFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical source carriers at a general radius: the comparison with the landed carriers

The carriers `l1BallRho`, `physSΛRho`, `physVRho`, `physVqRho`, `physFibreRho` and their basic
lemmas are in `SourceRadiusCarriers.lean`; `physInclScaled_image_subset_rho` is in
`SourceFamilyRelative.lean`.  Here are the statements that need the later files of the source lane:

* `physVqRho_one`, `physFibreRho_one`: at `ρ = 1` the carrier is the landed `physVq`, `physFibre`
  (by `rfl`);
* `sourceSlice_mem_restricted_rho`: `∑ |g| < q ≤ ρ`, `max 1 ρ ≤ β` give `g/β ∈ l1BallEta (q/β)`
  (the landed `sourceSlice_mem_restricted` is the case `ρ = 1`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.Background
  Balaban.SmallField Finset Metric

section Carriers

variable {d L N₁ m₁ k K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The scaled slice: `∑ |g| < q ≤ ρ` and `max 1 ρ ≤ β` give `g/β ∈ l1BallEta (q/β)`. -/
theorem sourceSlice_mem_restricted_rho {ρ β q : ℝ} (hβ : max 1 ρ ≤ β)
    {g : CTorus d L N₁ m₁ K → Fin N → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < q) (hq : q ≤ ρ) :
    (fun y i => g y i / (β : ℂ)) ∈ l1BallEta d L N₁ m₁ K N (q / β) :=
  sourceSlice_mem_restricted_radius hβ hg hq

variable (S : StepSetting d L N₁ m₁ k N ϱ)

theorem physVqRho_one (a₁ ν eps q : ℝ) :
    physVqRho (N := N) S a₁ ν eps 1 q = physVq S a₁ ν eps q := rfl

theorem physFibreRho_one (a₁ ν eps : ℝ) :
    physFibreRho (N := N) S a₁ ν eps 1 = physFibre S a₁ ν eps := rfl

end Carriers

end Balaban.Fluctuation
