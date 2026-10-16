/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LatPairGeom
public import Balaban.Fluctuation.LocalClassChart
public import Balaban.Localization.SharpX0Distance

/-!
# The symmetry data between the local generating sets of `Y` and `r Y`

`localB_collar_symmData`: for `r` in the paving group `pavingSymGroup L m₀ (k + 1)` and the
collars `Y⁺`, `(r Y)⁺` (so that `Ω_i(𝔹_{k+1}((r Y)⁺)) = r Ω_i(𝔹_{k+1}(Y⁺))`,
`localB_collar_pavingGS`), the generating sets `𝔹 = 𝔹_{k+1}(Y⁺)`, `𝔹' = 𝔹_{k+1}((r Y)⁺)` carry:

* a lattice symmetry `LatSymm 𝔹 𝔹' r`, and `r` preserves the unit blocks;
* a transport `τ` of the centres of the covers `coverOf 𝔹 → coverOf 𝔹'` (the fields `hidx`,
  `hchi`, `hbox`, `hqset`), keeping the layer and moving a centre to the centre of the image cube;
* a transport `τb` of the block indices (the fields `hbidx`, `hblayer`, `hbump`, `hbbase`);
* a bijection `u` of the unit points matching the unit blocks.

These are the symmetry hypotheses of `localB_eTermHat_evTerm_lat` for `𝔹 → 𝔹'`
(`LatPairGeom.lean`: closure induction over the generators of the paving group).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.GsSpec Balaban.LargeField Balaban.Localization.DecEquiv
  Balaban.Localization.DetDecCov Balaban.Localization.DetUnitIncidence Finset

section Data

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- **The symmetry data between `𝔹_{k+1}(Y⁺)` and `𝔹_{k+1}((r Y)⁺)`** for `r` in the paving group. -/
theorem localB_collar_symmData (hk : k + 1 ≤ k + 1) (hm₁ : 2 ≤ m₁) {m₀ : ℕ}
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    {Y Yp Yp' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ r '' Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    Nonempty (LatSymm (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
      (localB (k + 1) hk Yp' (le_refl (minSep L (L ^ m₁)))) r) ∧
    UnitBlockPres r ∧
    (∃ τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1)),
      (∀ q, τ q ∈ (coverOf (localB (k + 1) hk Yp' (le_refl (minSep L (L ^ m₁))))).cubeIdx ↔
        q ∈ (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx) ∧
      (∀ q x, (coverOf (localB (k + 1) hk Yp' (le_refl (minSep L (L ^ m₁))))).chi (τ q) (r x) =
        (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).chi q x) ∧
      (∀ q x, r x ∈ intBox (τ q) ↔ x ∈ intBox q) ∧
      (∀ q q', τ q' ∈ (coverOf (localB (k + 1) hk Yp' (le_refl (minSep L (L ^ m₁))))).Qset (τ q) ↔
        q' ∈ (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).Qset q) ∧
      (∀ q, (τ q).1 = q.1) ∧
      (∀ q ∈ (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx,
        SameCell (L ^ (q.1 + m₁)) (r q.2) (τ q).2)) ∧
    (∃ τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1)),
      (∀ q, τb q ∈ blockIdx (localB (k + 1) hk Yp' (le_refl (minSep L (L ^ m₁)))) ↔
        q ∈ blockIdx (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ∧
      (∀ q, (τb q).1 = q.1) ∧
      (∀ q x, Background.bump (τb q).1 (τb q).2 (r x) = Background.bump q.1 q.2 x) ∧
      (∀ q ∈ blockIdx (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))),
        jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 (r.symm (τb q).2) =
          jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 q.2)) ∧
    (∃ u : unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) ≃
        unitPts (localB (k + 1) hk Yp' (le_refl (minSep L (L ^ m₁)))),
      ∀ (y : unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
        (x : CTorus d L N₁ m₁ (k + 1)),
        unitBlock (r x) = (u y : UnitTorus d L N₁ m₁ k) ↔
          unitBlock x = (y : UnitTorus d L N₁ m₁ k)) := by
  have hΩ := mem_Ω_iff_of_image (localB_collar_pavingGS hk (le_refl (minSep L (L ^ m₁))) hr hYp
    hYp')
  have hcs : L ^ (k + 1 + m₁) ∣ cellSide L m₀ m₁ (k + 1) := pow_dvd_pow L (by omega)
  have hbs : L ^ (k + 1) ∣ cellSide L m₀ m₁ (k + 1) := pow_dvd_pow L (by omega)
  obtain ⟨S⟩ := nonempty_latSymm_of_mem_symGroupBy hbs hr hΩ
  have hU := unitBlockPres_of_mem_symGroupBy hbs hr
  obtain ⟨τ, H⟩ := exists_cubeAct_of_mem_symGroupBy hcs hr
  obtain ⟨τb, Hb⟩ := exists_blockAct_of_mem_symGroupBy hbs hr
  obtain ⟨c1, c2, c3, c4⟩ := coverData_of_cubeAct hΩ
    (localB_cubeAligned hk _ (le_refl (minSep L (L ^ m₁))) hm₁) H
  obtain ⟨b1, b2, b3, b4⟩ := blockData_of_blockAct hΩ Hb
  refine ⟨⟨S⟩, hU, ⟨τ, c1, c2, c3, c4, H.1, fun q hq => ?_⟩, ⟨τb, b1, b2, b3, b4⟩,
    exists_unitAct_pair S hU⟩
  have hq' := (mem_cubeIdx _).1 hq
  have e : τ q = (q.1, (τ (q.1, q.2)).2) := Prod.ext (H.1 q) rfl
  rw [e]
  exact (H.2.2.2.2 q.1 q.2 q.2 hq'.1.2 hq'.2.2).2 (SameCell.refl _ _)

end Data

end Balaban.Localization
