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

open Balaban Balaban.Fluctuation Balaban.SmallField Balaban.Localization Balaban.Inhabited.LevelStep

/-- **The determinant part of the new energy function at the general tower.**  For
`T : StepTowerG d L N κmin` and `L = 2 q + 1`, the family `E` of `StepTowerG.detPackage_fromTowerG`
is a family of `DetExpansionLocC` records at the step `T.step k hk N₁ ν β p₁`; at `ξ = 0`, if the
datum of the step is in the chart at radius `T.t`, `renE0θ_det` is the determinant term of the
step, and for every datum and `ξ` its sum over centred collar hulls is the sum over all sets of
cubes.  Determinant part only. -/
theorem StepTowerG.renE0θ_det_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {q : ℕ} (hLq : L = 2 * q + 1)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) (εren : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
          (k + 1) 1 T.t (T.step k hk N₁ ν β p₁).D' →
        ∀ z, renE0θ_det εren E z (T.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z, ∑ i,
            (T.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ z D ξ, ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁)
            (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))).image (detCollarHullC q),
          (E z).detGroupedC q (renThetaDatum (T.step k hk N₁ ν β p₁) εren D ξ) X =
          renE0θ_det εren E z D ξ := by
  obtain ⟨E, -⟩ := T.detPackage_fromTowerG hLq k hk N₁ hLN hN5 hν0 hν β p₁
  refine ⟨E, fun hD z => renE0θ_det_zero εren E z hD, fun z D ξ => ?_⟩
  unfold renE0θ_det
  exact sum_detCollarGroupedC q (fun T' => (E z).term (renThetaDatum _ εren D ξ) T')

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
  classical
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h := T.toG.renE0θ_det_fromTowerG (q := 1) rfl k hk N₁ h3N hN5 hν0 (by simpa using hν)
    β p₁ εren
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTower.toG_m₁, StepTower.toG_κ, StepTower.toG_t, StepTower.toG_BG,
    StepTower.toG_δ] at h
  have e1 : (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate T.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) = towerDetConst T.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  have e3 : (detCollarHullC (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) (m₀ := 1) 1) =
      detCollarHull := funext fun X => detCollarHullC_one hN X
  obtain ⟨E, h0, hs⟩ := h
  refine ⟨E, h0, fun z D ξ => ?_⟩
  rw [e3] at hs
  refine Eq.trans (Finset.sum_congr rfl fun X _ => ?_) (hs z D ξ)
  exact ((E z).detGroupedC_one hN _ X).symm

end Balaban.Inhabited
