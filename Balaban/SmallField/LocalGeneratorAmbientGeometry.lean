/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorSource
public import Balaban.SmallField.Def6

/-!
# The local generator inside the whole-level generator

The layers of the minimal generator of a polymer lie in the corresponding whole-level layers.
This is the geometric part of comparing the local and ambient small-field charts.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- Every layer of the local generator lies in the whole-level generator at level `j`. -/
theorem localB_omega_subset_levelGS (i : ℕ) :
    (localB j hj X hsep).Ω i ⊆
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj).Ω i := by
  classical
  by_cases hi : i ≤ j
  · simp [levelGS, hi]
  · have hji : j < i := by omega
    rw [localB_Ω_of_gt hji]
    exact Finset.empty_subset _

/-- The local generator precedes the whole-level generator, even when their separation indices
are different. -/
theorem localB_precedes_levelGS :
    Precedes (localB j hj X hsep)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) := by
  intro i _ _
  exact localB_omega_subset_levelGS i

/-- A local generator at level `j` also precedes every higher whole-level generator. -/
theorem localB_precedes_levelGS_of_le {t : ℕ} (hjt : j ≤ t) (ht : t ≤ k) :
    Precedes (localB j hj X hsep)
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') t ht) := by
  intro i _ _
  classical
  by_cases hi : i ≤ t
  · simp [levelGS, hi]
  · have hji : j < i := by omega
    rw [localB_Ω_of_gt hji]
    exact Finset.empty_subset _

/-- The local union of field and collar sites lies in the first domain of a whole-level
generator whenever that generator has a nonempty first level. -/
theorem localB_dataSites_subset_levelGS_omega_one {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ k)
    {x : CTorus d L N₁ m₁ k} (_hx : x ∈ dataSites (localB j hj X hsep)) :
    x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') t ht).Ω 1 := by
  classical
  simp [levelGS, ht1]

end Balaban.SmallField.GsSpec
