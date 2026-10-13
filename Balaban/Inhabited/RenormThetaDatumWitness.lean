/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormThetaDatum
public import Balaban.Inhabited.DetPackageFromTower

/-!
# The determinant part of the new energy function at the shared tower

For a shared tower `T : StepTower κmin` the family `E` of `detPackage_fromTower` is a family of
`DetExpansionLocC` records at the step `T.step k hk N₁ ν β p₁`.  This file evaluates the
determinant part `renE0θ_det` of the new energy function with this family:

* at `ξ = 0`, if the datum `D'` of the step is in the chart at radius `T.t`, it equals the
  determinant term of the step;
* for every datum and `ξ` its sum over collar hulls is the sum over all sets of cubes.

Only the determinant part is treated; no chart inclusion for `ξ ≠ 0` is asserted.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.SmallField Balaban.Localization

theorem renE0θ_det_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (εren : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t (towerDetRate T.κ)
          (towerDetConst T.κ),
      (XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
          (k + 1) 1 T.t (T.step k hk N₁ ν β p₁).D' →
        ∀ z, renE0θ_det εren E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z D ξ, ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
            (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull,
          (E z).detGrouped (renThetaDatum (T.step k hk N₁ ν β p₁) εren D ξ) X =
          renE0θ_det εren E z D ξ := by
  obtain ⟨E, -⟩ := detPackage_fromTower T k hk N₁ h3N hN5 hν0 hν β p₁
  exact ⟨E, fun hD z => renE0θ_det_zero εren E z hD,
    fun z D ξ => renE0θ_det_eq_sum_collar εren E z D ξ⟩

end Balaban.Inhabited
