/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorSource
public import Balaban.SmallField.Def6InfShapes

/-!
# The local generating set of a class polymer

A polymer of `𝒟_j` is a union of aligned cells of side `L ^ (j + m₀ + m₁)`, a multiple of the side
`L ^ m₁ L ^ j` of the cubes on which `localB` is built.  Hence a polymer is a union of those cubes
(`isPolyDom_cubeUnion`) and `gsSpecStrong_localB` applies to every polymer of the class
(`gsSpecStrong_localB_of_isPolyDom`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField Finset

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- Two sites of the same `L ^ m₁ L ^ j`-cube lie in the same cell of side `cellSide`. -/
theorem cbase_cellSide_eq_of_fineCube {m₀ j : ℕ} (hjk : j ≤ k) {x y : CTorus d L N₁ m₁ k}
    (h : fineCubeIdx (L ^ m₁) N₁ L k j (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) =
      fineCubeIdx (L ^ m₁) N₁ L k j (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k))) :
    cbase (cellSide L m₀ m₁ j) y = cbase (cellSide L m₀ m₁ j) x := by
  have hL := NeZero.pos L
  have e : L ^ m₁ * N₁ * L ^ k = (L ^ j * L ^ m₁) * (N₁ * L ^ (k - j)) := by
    have : L ^ k = L ^ j * L ^ (k - j) := by rw [← pow_add]; congr 1; omega
    rw [this]; ring
  have hv : ∀ z : CTorus d L N₁ m₁ k, ∀ μ,
      ((torusCast z : Torus d (L ^ m₁ * N₁ * L ^ k)) μ).val = (z μ).val := fun z μ =>
    torusCast_val (by rw [mul_comm (L ^ m₁) N₁]) z μ
  funext μ
  have h1 := congrFun h μ
  have e1 := blockCoord_val (N := L ^ j * L ^ m₁) (m := N₁ * L ^ (k - j)) e
    ((torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) μ)
  have e2 := blockCoord_val (N := L ^ j * L ^ m₁) (m := N₁ * L ^ (k - j)) e
    ((torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) μ)
  have h2 : (y μ).val / (L ^ j * L ^ m₁) = (x μ).val / (L ^ j * L ^ m₁) := by
    rw [← hv y μ, ← hv x μ, ← e1, ← e2]
    have h3 : (blockCoord (L ^ j * L ^ m₁) (N₁ * L ^ (k - j))
        ((torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) μ)) =
        (blockCoord (L ^ j * L ^ m₁) (N₁ * L ^ (k - j))
        ((torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) μ)) := by
      simpa [fineCubeIdx, blockMap_apply] using h1
    rw [h3]
  have h4 : (y μ).val / cellSide L m₀ m₁ j = (x μ).val / cellSide L m₀ m₁ j := by
    have : cellSide L m₀ m₁ j = (L ^ j * L ^ m₁) * L ^ m₀ := by
      rw [cellSide_eq_mul, pow_add]; ring
    rw [this, ← Nat.div_div_eq_div_mul (y μ).val, ← Nat.div_div_eq_div_mul (x μ).val, h2]
  simp only [cbase, h4]

/-- **A polymer of `𝒟_j` is a union of the cubes of side `L ^ m₁ L ^ j`** on which `localB` is
built. -/
theorem isPolyDom_cubeUnion {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X) :
    ∀ x ∈ X, ∀ y : CTorus d L N₁ m₁ k,
      fineCubeIdx (L ^ m₁) N₁ L k j (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k)) =
        fineCubeIdx (L ^ m₁) N₁ L k j (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) → y ∈ X := by
  intro x hx y hy
  obtain ⟨-, ⟨𝒦, hK1, hK2⟩, -⟩ := hX
  obtain ⟨b, hb, hzb⟩ := hK2 x hx
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) hN hjk
  have hcell := cell_subset_cube hdvd ha0 (hK1 b hb).1 hzb
  have hc : cbase (cellSide L m₀ m₁ j) y = cbase (cellSide L m₀ m₁ j) x :=
    cbase_cellSide_eq_of_fineCube (m₀ := m₀) hjk hy
  have : y ∈ Localization.box (cbase (cellSide L m₀ m₁ j) x) (cellSide L m₀ m₁ j) := by
    rw [← hc]; exact mem_box_cbase ha0 y
  exact (hK1 b hb).2 (hcell this)

variable {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- **`gsSpecStrong_localB` for every polymer of the class.** -/
theorem gsSpecStrong_localB_of_isPolyDom {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hj1 : 1 ≤ j)
    (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X) :
    GsSpecStrong j hj X (localB j hj X hsep) :=
  gsSpecStrong_localB hj1 (isPolyDom_cubeUnion hj hN hX)

end Balaban.SmallField.GsSpec
