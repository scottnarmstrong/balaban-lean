/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonCells
public import Balaban.Inhabited.NewLevelCanonGeomDef
public import Balaban.Polymer.LocalBBoxCorr

/-!
# The geometry of canonical covers built from local generating sets

`CanonCoverLocal F F'`: the generating sets `Gk`, `Gj` of the canonical covers of two tori are the local
generating sets `𝔹_n(P)` of polymers `P` (`localB`).  `hgeom_of_local` proves `HGeom` for them: the margin
`Z` is the union of the `L^{k+1}`-cells of the sites within `zRad` of the polymer, the neighbours and the
polymers of `Gk`, `Gj`; the correspondence of the generating sets is `gsCorr_localB` and
`gsIso_localB_on`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LocalCover Balaban.Polymer Balaban.SmallField.Def6
  Balaban.Polymer.TwoTorusStep Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec
  Balaban.LargeField

section Local

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ₁ ϱ₁' : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))

/-- **Canonical covers whose generating sets are local generating sets of polymers.** -/
structure CanonCoverLocal (F : CanonCover d L N₁ m₁ k ϱ ϱ₁) (F' : CanonCover d L N₁' m₁ k ϱ ϱ₁') where
  nK : ℕ → ℕ
  nJ : ℕ → ℕ
  hnK : ∀ j, nK j ≤ k + 1
  hnJ : ∀ j, nJ j ≤ k + 1
  hsepK : ϱ₁ ≤ minSep L (L ^ m₁)
  hsepK' : ϱ₁' ≤ minSep L (L ^ m₁)
  hsepJ : ϱ ≤ minSep L (L ^ m₁)
  PK : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
    Set (CTorus d L N₁ m₁ (k + 1))
  PJ : ℕ → CTorus d L N₁ m₁ (k + 1) → Set (CTorus d L N₁ m₁ (k + 1)) →
    Set (CTorus d L N₁ m₁ (k + 1))
  PK' : ℕ → CTorus d L N₁' m₁ (k + 1) → Set (CTorus d L N₁' m₁ (k + 1)) →
    Set (CTorus d L N₁' m₁ (k + 1))
  PJ' : ℕ → CTorus d L N₁' m₁ (k + 1) → Set (CTorus d L N₁' m₁ (k + 1)) →
    Set (CTorus d L N₁' m₁ (k + 1))
  hGk : ∀ j y X, F.GkC j y X = localB (nK j) (hnK j) (PK j y X) hsepK
  hGj : ∀ j y X, F.GjC j y X = localB (nJ j) (hnJ j) (PJ j y X) hsepJ
  hGk' : ∀ j y X, F'.GkC j y X = localB (nK j) (hnK j) (PK' j y X) hsepK'
  hGj' : ∀ j y X, F'.GjC j y X = localB (nJ j) (hnJ j) (PJ' j y X) hsepJ

/-- **Non-vacuity**: for admissible separations there are canonical covers with local generating sets. -/
theorem exists_canonCoverLocal (hsepK : ϱ₁ ≤ minSep L (L ^ m₁)) (hsepK' : ϱ₁' ≤ minSep L (L ^ m₁))
    (hsepJ : ϱ ≤ minSep L (L ^ m₁)) :
    ∃ (F : CanonCover d L N₁ m₁ k ϱ ϱ₁) (F' : CanonCover d L N₁' m₁ k ϱ ϱ₁'),
      Nonempty (CanonCoverLocal F F') := by
  refine ⟨⟨fun _ _ _ => ∅, fun _ _ _ => ∅,
    fun _ _ _ => localB 0 (Nat.zero_le _) ∅ hsepK, fun _ _ _ => localB 0 (Nat.zero_le _) ∅ hsepJ, 0⟩,
    ⟨fun _ _ _ => ∅, fun _ _ _ => ∅,
    fun _ _ _ => localB 0 (Nat.zero_le _) ∅ hsepK', fun _ _ _ => localB 0 (Nat.zero_le _) ∅ hsepJ, 0⟩,
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _, hsepK, hsepK', hsepJ,
      fun _ _ _ => ∅, fun _ _ _ => ∅, fun _ _ _ => ∅, fun _ _ _ => ∅,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩⟩

/-- The radius of the margin: the support radius of the data of `𝔹_n(P)`, `n ≤ k + 1`, plus one. -/
def zRad (L m₁ k : ℕ) : ℕ := 11 * L ^ (m₁ + (k + 1)) + 2

/-- The sites within sup-distance `r` of a set. -/
def nearSet (r : ℕ) (P : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {x | ∃ w ∈ P, supDist x w ≤ r}

/-- The sites of a pair and of its generating-set polymers. -/
def canonPts {F : CanonCover d L N₁ m₁ k ϱ ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ ϱ₁'}
    (LC : CanonCoverLocal F F') (j : ℕ) (y₀ : CTorus d L N₁ m₁ (k + 1))
    (X₀ : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  insert y₀ X₀ ∪ {y | ∃ μ : Fin d, y = y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1))} ∪
    LC.PK j y₀ X₀ ∪ LC.PJ j y₀ X₀

/-- **The margin of a pair**: the union of the `L^{k+1}`-cells of the sites within `zRad` of its
points; it is closed under the blocks of every generating set (sides at most `L^{k+1}`, nested). -/
def canonZ {F : CanonCover d L N₁ m₁ k ϱ ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ ϱ₁'}
    (LC : CanonCoverLocal F F') (j : ℕ) (y₀ : CTorus d L N₁ m₁ (k + 1))
    (X₀ : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {y | ∃ x ∈ nearSet (zRad L m₁ k) (canonPts LC j y₀ X₀), SameCell (L ^ (k + 1)) y x}

omit [NeZero N₁] [NeZero L] in
theorem layerIndex_le_top {N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ' : ℝ}
    (G : GeneratingSet d L N₀ K ϱ') (x : Torus d (N₀ * L ^ K)) : G.layerIndex x ≤ K := by
  by_cases hx : x ∈ G.Ω 1
  · exact (G.layerIndex_spec hx).2.1
  · have : ¬ ∃ j, 1 ≤ j ∧ j ≤ K ∧ x ∈ G.layer j := fun ⟨j, h1, h2, h3⟩ =>
      hx (G.layer_subset h1 h2 h3)
    unfold GeneratingSet.layerIndex
    simp [this]

omit [NeZero N₁] [NeZero L] in
/-- The size margins of the local generating sets. -/
theorem margins_of_big {R n N₀ : ℕ} (hn : n ≤ k + 1)
    (hbig : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₀) [NeZero L] :
    (∀ n' ≤ n, 2 * (R + 1 + 6 * n * L ^ (n + m₁) + (5 * L + 2) * (L ^ n' * L ^ m₁)) < N₀) ∧
    2 * (R + 6 * n * L ^ (n + m₁) + 1 + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₀ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have e1 : L ^ (n + m₁) ≤ L ^ (k + 1 + m₁) := Nat.pow_le_pow_right hL (by omega)
  have h6 : 6 * n * L ^ (n + m₁) ≤ 6 * (k + 1) * L ^ (k + 1 + m₁) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 6 hn) e1
  refine ⟨fun n' hn' => ?_, ?_⟩
  · have e2 : L ^ n' * L ^ m₁ ≤ L ^ (k + 1 + m₁) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hL (by omega)
    have h5 : (5 * L + 2) * (L ^ n' * L ^ m₁) ≤ (5 * L + 2) * L ^ (k + 1 + m₁) :=
      Nat.mul_le_mul_left _ e2
    generalize 6 * n * L ^ (n + m₁) = a at h6 ⊢
    generalize (5 * L + 2) * (L ^ n' * L ^ m₁) = b at h5 ⊢
    generalize 6 * (k + 1) * L ^ (k + 1 + m₁) = c at h6 hbig
    generalize (5 * L + 2) * L ^ (k + 1 + m₁) = e at h5 hbig
    omega
  · generalize 6 * n * L ^ (n + m₁) = a at h6 ⊢
    generalize 6 * (k + 1) * L ^ (k + 1 + m₁) = c at h6 hbig
    have : 0 ≤ (5 * L + 2) * L ^ (k + 1 + m₁) := Nat.zero_le _
    generalize (5 * L + 2) * L ^ (k + 1 + m₁) = e at this hbig
    omega

end Local

end Balaban.Inhabited
