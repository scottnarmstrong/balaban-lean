/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonCells
public import Balaban.Inhabited.NewLevelCanonGeomDef
public import Balaban.Inhabited.NewLevelCanonLocal
public import Balaban.Inhabited.NewLevelCastNbhd
public import Balaban.Inhabited.NewLevelCubeImage
public import Balaban.Polymer.CastLocalBCorr

/-!
# Canonical covers whose generating sets are the cast local sets of the settings

`CanonCoverCast m₀ s hcA hcB F F'`: for the admissible pairs, `Gk = castG hc (𝔹_k(Z'))` with `Z'` the
cube-index neighbourhood `castNbhd` of the polymer `X ∪ □(y)` and its set `X̂`, and `Gj = castG hc (𝔹_j(X̂))`,
as produced by `settings_family_castLocalB_hat_Gk` on the finer tori `(N_A, m₁ + s)`.  The polymers
correspond under `boxMap` (`polySet_boxMap`, `hatSet_boxMap`, `castNbhd_image`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Polymer.TwoTorusStep
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField

section Cast

variable {d L N₁ N₂ NA NB m₁ k N : ℕ} [NeZero N₁] [NeZero N₂] [NeZero NA] [NeZero NB] [NeZero L]
  {ϱ ϱ₁ ϱ₁' : ℝ}

/-- The fine set whose cube-index neighbourhood is the set `Z` of `Gk`: the cast of `X ∪ □(y)` and `X̂`. -/
def kernelSet (m₀ s : ℕ) (j : ℕ) (y : CTorus d L N₁ m₁ (k + 1))
    (X : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L NA (m₁ + s) (k + 1)) :=
  {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ polySet m₀ j y X ∪ hatSet m₀ j X}

/-- The fine polymer of `Gj`: the cast of `X̂`. -/
def hatFine (m₀ s : ℕ) (j : ℕ) (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    Set (CTorus d L NA (m₁ + s) (k + 1)) :=
  {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ hatSet m₀ j X}

/-- **Canonical covers whose generating sets are the cast local sets of the settings** (for the
admissible pairs of both tori). -/
structure CanonCoverCast (m₀ s : ℕ) (hcA : NA * L ^ (m₁ + s) = N₁ * L ^ m₁)
    (hcB : NB * L ^ (m₁ + s) = N₂ * L ^ m₁) (F : CanonCover d L N₁ m₁ k ϱ ϱ₁)
    (F' : CanonCover d L N₂ m₁ k ϱ ϱ₁') where
  hs₁ : ϱ₁ ≤ minSep L (L ^ (m₁ + s))
  hs₁' : ϱ₁' ≤ minSep L (L ^ (m₁ + s))
  hs₂ : ϱ ≤ minSep L (L ^ (m₁ + s))
  hGk : ∀ j y X (_h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d m₀ k),
    F.GkC j y X = castG hcA (localB k (Nat.le_succ k)
      (castNbhd (N₁' := NA) (m₁' := m₁ + s) (kernelSet (NA := NA) m₀ s j y X)) hs₁)
  hGj : ∀ j y X (h : (j, y, X) ∈ AdmPairs L N₁ m₁ k d m₀ k),
    F.GjC j y X = castG hcA (localB j (Nat.le_succ_of_le h.2.1) (hatFine (NA := NA) m₀ s j X) hs₂)
  hGk' : ∀ j y X (_h : (j, y, X) ∈ AdmPairs L N₂ m₁ k d m₀ k),
    F'.GkC j y X = castG hcB (localB k (Nat.le_succ k)
      (castNbhd (N₁' := NB) (m₁' := m₁ + s) (kernelSet (NA := NB) m₀ s j y X)) hs₁')
  hGj' : ∀ j y X (h : (j, y, X) ∈ AdmPairs L N₂ m₁ k d m₀ k),
    F'.GjC j y X = castG hcB (localB j (Nat.le_succ_of_le h.2.1) (hatFine (NA := NB) m₀ s j X) hs₂)

omit [NeZero N₁] [NeZero N₂] in
/-- The fine sets over corresponding coarse sets correspond. -/
theorem fine_image {a a' b b' : ℕ} [NeZero a] [NeZero a'] [NeZero b] [NeZero b'] (ha : a = a')
    (hb : b = b') (S : Set (Torus d a')) :
    {x' : Torus d b | (torusCast x' : Torus d b') ∈ boxMap a' b' '' S} =
      boxMap a b '' {x : Torus d a | (torusCast x : Torus d a') ∈ S} := by
  ext x'
  constructor
  · rintro ⟨z, hz, h⟩
    refine ⟨torusCast z, ?_, ?_⟩
    · show (torusCast (torusCast z : Torus d a) : Torus d a') ∈ S
      rw [torusCast_torusCast ha.symm]; exact hz
    · rw [boxMap_torusCast ha.symm hb.symm z, h, torusCast_torusCast hb]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨torusCast x, hx, boxMap_torusCast ha hb x⟩

/-- **`□(y) ∪ X` of the image is the image of `□(y) ∪ X`.** -/
theorem polySet_boxMap {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₂) (hjk : j ≤ k) (hL : 2 ≤ L)
    {R : ℕ} {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hy : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 2 * (R + 2 * (L * cellSide L m₀ m₁ j)) + L * cellSide L m₀ m₁ j + 1 <
      (N₁ * L ^ m₁) * L ^ (k + 1)) :
    polySet m₀ j (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) y)
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) '' X) =
      boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) '' polySet m₀ j y X := by
  have hd1 := cellSide_dvd (K := k + 1) (m₁ := m₁) (L := L) (N₁ := N₁) hN (by omega : j ≤ k + 1)
  have hd2 := cellSide_dvd (K := k + 1) (m₁ := m₁) (L := L) (N₁ := N₂) hN' (by omega : j ≤ k + 1)
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hh : L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j ≤ L * cellSide L m₀ m₁ j := by
    have : L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j = (L / 2 + 1) * cellSide L m₀ m₁ j := by
      ring
    rw [this]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold polySet
  rw [Set.image_union]
  congr 1
  exact (image_cubeAt_boxMap ha0 hd1 hd2 hh hn hy).symm

/-- **The fine set of the kernel of the image is the image of the fine set.** -/
theorem kernelSet_boxMap {m₀ s j : ℕ} (hcA : NA * L ^ (m₁ + s) = N₁ * L ^ m₁)
    (hcB : NB * L ^ (m₁ + s) = N₂ * L ^ m₁) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₂) (hjk : j ≤ k)
    (hL : 2 ≤ L) {R : ℕ} {y : CTorus d L N₁ m₁ (k + 1)} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hy : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hX : ∀ x ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * (R + 2 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j)) +
      (2 * (L / 2) + 1) * cellSide L m₀ m₁ j + 1 < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    kernelSet (NA := NB) m₀ s j
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) y)
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) '' X) =
      boxMap ((NA * L ^ (m₁ + s)) * L ^ (k + 1)) ((NB * L ^ (m₁ + s)) * L ^ (k + 1)) ''
        kernelSet (NA := NA) m₀ s j y X := by
  have hA : NA * L ^ (m₁ + s) * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by rw [hcA]
  have hB : NB * L ^ (m₁ + s) * L ^ (k + 1) = N₂ * L ^ m₁ * L ^ (k + 1) := by rw [hcB]
  have hLa : L * cellSide L m₀ m₁ j ≤ (2 * (L / 2) + 1) * cellSide L m₀ m₁ j :=
    Nat.mul_le_mul_right _ (by omega)
  have hpoly := polySet_boxMap hN hN' hjk hL hy (X := X) (by
    have : L * cellSide L m₀ m₁ j ≤ (2 * (L / 2) + 1) * cellSide L m₀ m₁ j := hLa
    omega)
  have hhat := hatSet_boxMap (N₂ := N₂) (k := k + 1) hN hN' (by omega) hX hn
  have hsets : polySet m₀ j (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) y)
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) '' X) ∪
      hatSet m₀ j (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) '' X) =
      boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) ''
        (polySet m₀ j y X ∪ hatSet m₀ j X) := by
    rw [hpoly, hhat, Set.image_union]
  unfold kernelSet
  rw [hsets]
  exact fine_image hA hB _

/-- **The fine set of `X̂` of the image is the image of the fine set of `X̂`.** -/
theorem hatFine_boxMap {m₀ s j : ℕ} (hcA : NA * L ^ (m₁ + s) = N₁ * L ^ m₁)
    (hcB : NB * L ^ (m₁ + s) = N₂ * L ^ m₁) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₂) (hjk : j ≤ k)
    {R : ℕ} {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : ∀ x ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 2 * (R + 2 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j)) +
      (2 * (L / 2) + 1) * cellSide L m₀ m₁ j + 1 < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    hatFine (NA := NB) m₀ s j
        (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₂ * L ^ m₁) * L ^ (k + 1)) '' X) =
      boxMap ((NA * L ^ (m₁ + s)) * L ^ (k + 1)) ((NB * L ^ (m₁ + s)) * L ^ (k + 1)) ''
        hatFine (NA := NA) m₀ s j X := by
  have hA : NA * L ^ (m₁ + s) * L ^ (k + 1) = N₁ * L ^ m₁ * L ^ (k + 1) := by rw [hcA]
  have hB : NB * L ^ (m₁ + s) * L ^ (k + 1) = N₂ * L ^ m₁ * L ^ (k + 1) := by rw [hcB]
  unfold hatFine
  rw [hatSet_boxMap (N₂ := N₂) (k := k + 1) hN hN' (by omega) hX hn]
  exact fine_image hA hB _

end Cast

end Balaban.Inhabited
