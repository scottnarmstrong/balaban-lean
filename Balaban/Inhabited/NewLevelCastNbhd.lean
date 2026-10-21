/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.CastLocalBCorr
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSet

/-!
# The cube-index neighbourhood of corresponding sets on two tori

`castNbhd` (the set `Z` of the generating set `Gk` of the settings) of corresponding sets
`Y' = boxMap '' Y` of the finer tori correspond: `castNbhd_boxMap_iff`, `castNbhd_image`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
  Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.GsSpec Balaban.Fluctuation

section Nbhd

variable {d L NA NB m' k : ℕ} [NeZero NA] [NeZero NB] [NeZero L]

local notation "bmF" => boxMap ((NA * L ^ m') * L ^ (k + 1)) ((NB * L ^ m') * L ^ (k + 1))
local notation "bmF'" => boxMap ((NB * L ^ m') * L ^ (k + 1)) ((NA * L ^ m') * L ^ (k + 1))

/-- **The cube-index neighbourhoods of corresponding sets correspond on the box.** -/
theorem castNbhd_boxMap_iff {R ρx : ℕ} {Y : Set (CTorus d L NA m' (k + 1))}
    {Y' : Set (CTorus d L NB m' (k + 1))}
    (hY : ∀ y ∈ Y, InBox d R ((NA * L ^ m') * L ^ (k + 1)) y)
    (hYY : Y' = bmF '' Y)
    (hmA : 2 * (R + (5 * L + 2) * (L ^ k * L ^ m')) < NA * L ^ m' * L ^ (k + 1))
    (hmB : 2 * (R + (5 * L + 2) * (L ^ k * L ^ m')) < NB * L ^ m' * L ^ (k + 1))
    {x : CTorus d L NA m' (k + 1)} (hx : InBox d ρx ((NA * L ^ m') * L ^ (k + 1)) x)
    (hρB : 2 * ρx + 1 < NB * L ^ m' * L ^ (k + 1)) :
    bmF x ∈ castNbhd (N₁' := NB) (m₁' := m') Y' ↔ x ∈ castNbhd (N₁' := NA) (m₁' := m') Y := by
  have hs0 : 0 < L ^ k * L ^ m' :=
    Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
  have h2 : L ^ k * L ^ m' ≤ (5 * L + 2) * (L ^ k * L ^ m') :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hY' : ∀ y ∈ Y', InBox d R ((NB * L ^ m') * L ^ (k + 1)) y := by
    intro y hy
    rw [hYY] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    exact inBox_boxMap (by omega) (hY y0 hy0)
  have eqv : ∀ y : CTorus d L NA m' (k + 1), InBox d R ((NA * L ^ m') * L ^ (k + 1)) y →
      (bmF y ∈ Y' ↔ y ∈ Y) := by
    intro y hy
    rw [hYY]
    constructor
    · rintro ⟨y0, hy0, h⟩
      have : y0 = y := boxMap_inj (hm' := (by omega : 2 * R + 1 < (NB * L ^ m') * L ^ (k + 1)))
        (hY y0 hy0) hy h
      exact this ▸ hy0
    · exact fun h => ⟨y, h, rfl⟩
  have hcA : 2 * ((R : ℤ) / ((L ^ k * L ^ m' : ℕ) : ℤ) + 1 + (5 * L : ℕ)) + 2 <
      ((NA * L ^ (k + 1 - k) : ℕ) : ℤ) :=
    cube_margin (a := NA * L ^ m' * L ^ (k + 1)) (s := L ^ k * L ^ m') (c := NA * L ^ (k + 1 - k))
      (ρ := R) (m := 5 * L) (cube_card_eq (by omega)) hs0 hmA
  have hcB : 2 * ((R : ℤ) / ((L ^ k * L ^ m' : ℕ) : ℤ) + 1 + (5 * L : ℕ)) + 2 <
      ((NB * L ^ (k + 1 - k) : ℕ) : ℤ) :=
    cube_margin (a := NB * L ^ m' * L ^ (k + 1)) (s := L ^ k * L ^ m') (c := NB * L ^ (k + 1 - k))
      (ρ := R) (m := 5 * L) (cube_card_eq (by omega)) hs0 hmB
  exact exists_near_boxMap_iff (n := k) (k := k + 1) (by omega) hs0 hY hY' eqv hx hρB
    (by omega) (by omega)
    hcA hcB

/-- **The cube-index neighbourhood of the image is the image of the neighbourhood.** -/
theorem castNbhd_image {R : ℕ} {Y : Set (CTorus d L NA m' (k + 1))}
    {Y' : Set (CTorus d L NB m' (k + 1))}
    (hY : ∀ y ∈ Y, InBox d R ((NA * L ^ m') * L ^ (k + 1)) y)
    (hYY : Y' = bmF '' Y)
    (hmA : 2 * (R + (5 * L + 2) * (L ^ k * L ^ m')) < NA * L ^ m' * L ^ (k + 1))
    (hmB : 2 * (R + (5 * L + 2) * (L ^ k * L ^ m')) < NB * L ^ m' * L ^ (k + 1)) :
    castNbhd (N₁' := NB) (m₁' := m') Y' = bmF '' castNbhd (N₁' := NA) (m₁' := m') Y := by
  have hs0 : 0 < L ^ k * L ^ m' :=
    Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
  have hsplit : (5 * L + 2) * (L ^ k * L ^ m') = (5 * L + 1) * (L ^ k * L ^ m') + L ^ k * L ^ m' := by
    ring
  have hY' : ∀ y ∈ Y', InBox d R ((NB * L ^ m') * L ^ (k + 1)) y := by
    intro y hy
    rw [hYY] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    exact inBox_boxMap (by omega) (hY y0 hy0)
  have hρB : 2 * (R + (5 * L + 1) * (L ^ k * L ^ m')) + 1 < NB * L ^ m' * L ^ (k + 1) := by omega
  ext z'
  constructor
  · intro hz'
    obtain ⟨y', hy', hd⟩ := hz'
    have hzb : InBox d (R + (5 * L + 1) * (L ^ k * L ^ m')) ((NB * L ^ m') * L ^ (k + 1)) z' :=
      inBox_of_cubeNear (k := k + 1) (n := k) (by omega) (hY' y' hy') hmB hd
    have hza : InBox d (R + (5 * L + 1) * (L ^ k * L ^ m')) ((NA * L ^ m') * L ^ (k + 1))
        (bmF' z') := inBox_boxMap (by omega) hzb
    have hzz : bmF (bmF' z') = z' := boxMap_boxMap (by omega) hzb
    refine ⟨bmF' z', ?_, hzz⟩
    rw [← castNbhd_boxMap_iff hY hYY hmA hmB hza hρB, hzz]
    exact ⟨y', hy', hd⟩
  · rintro ⟨z, hz, rfl⟩
    have hzb : InBox d (R + (5 * L + 1) * (L ^ k * L ^ m')) ((NA * L ^ m') * L ^ (k + 1)) z := by
      obtain ⟨y, hy, hd⟩ := hz
      exact inBox_of_cubeNear (k := k + 1) (n := k) (by omega) (hY y hy) hmA hd
    exact (castNbhd_boxMap_iff hY hYY hmA hmB hzb hρB).2 hz

end Nbhd

end Balaban.Polymer.TwoTorusStep
