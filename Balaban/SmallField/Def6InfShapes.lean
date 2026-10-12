/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfPoly
public import Balaban.SmallField.Def6InfD2
public import Balaban.SmallField.Def6BridgeInfSum

/-!
# Def-6: polymers as unions of blocks, and the density at the origin as a sum over shapes

* `IsPolyDom.block_closed`: a polymer of `𝒟_j` is a union of `j`-blocks;
* `polysAt_zero_eq_image`: the polymers of `𝒟_j` containing the origin are the lifts `Ypoly X'` of
  the shapes `liftPolys`;
* `Eloc_zero_eq_sum`: `Eloc` at the origin is the finite sum over the shapes `liftPolys` of the
  terms `E j 0 (Ypoly X')`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Blocks

/-- Two sites of the same `j`-block have the same cell. -/
theorem cbase_cellSide_eq_of_jBlock {m₀ j : ℕ} (hjk : j ≤ k) {z z' : CTorus d L N₁ m₁ k}
    (h : jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z') :
    cbase (cellSide L m₀ m₁ j) z = cbase (cellSide L m₀ m₁ j) z' := by
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  funext μ
  have h1 := congrFun h μ
  simp only [jBlock, blockMap_apply] at h1
  have e1 := blockCoord_val (side_eq hjk) (z μ)
  have e2 := blockCoord_val (side_eq hjk) (z' μ)
  have h2 : (z μ).val / L ^ j = (z' μ).val / L ^ j := by
    rw [← e1, ← e2, h1]
  have h3 : (z μ).val / cellSide L m₀ m₁ j = (z' μ).val / cellSide L m₀ m₁ j := by
    rw [cellSide_eq_mul, ← Nat.div_div_eq_div_mul, h2, Nat.div_div_eq_div_mul]
  simp only [cbase, h3]

/-- **A polymer of `𝒟_j` is a union of `j`-blocks.** -/
theorem IsPolyDom.block_closed {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j Y)
    {z z' : CTorus d L N₁ m₁ k} (hz : z ∈ Y)
    (h : jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z') : z' ∈ Y := by
  obtain ⟨-, ⟨𝒦, hK1, hK2⟩, -⟩ := hY
  obtain ⟨b, hb, hzb⟩ := hK2 z hz
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) hN hjk
  have hcell := cell_subset_cube hdvd ha0 (hK1 b hb).1 hzb
  have hc : cbase (cellSide L m₀ m₁ j) z' = cbase (cellSide L m₀ m₁ j) z :=
    (cbase_cellSide_eq_of_jBlock (m₀ := m₀) hjk h).symm
  have : z' ∈ box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) := by
    rw [← hc]; exact mem_box_cbase ha0 z'
  exact (hK1 b hb).2 (hcell this)

end Blocks


section Shapes

variable {P : Consts} {j : ℕ}

open Classical in
/-- **The polymers of `𝒟_j` containing the origin are the lifts of the shapes `liftPolys`.** -/
theorem polysAt_zero_eq_image (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁) :
    polysAt P.m₀ j (0 : CTorus d L N₁ m₁ k) =
      (fun X' => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ''
        liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j := by
  ext Y
  constructor
  · rintro ⟨hY, h0⟩
    set X' : Finset (Fin d → ℤ) := (Finset.univ.filter (fun y => y ∈ Y)).image
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j) with hX'
    have hmem : ∀ z, z ∈ X' ↔ ∃ y₀ ∈ Y, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y₀ = z := by
      intro z; simp [hX']
    have hYeq : Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Y := by
      ext z
      constructor
      · intro hz
        obtain ⟨y₀, hy₀, hyz⟩ := (hmem _).1 hz
        refine IsPolyDom.block_closed hjk hN hY hy₀ ?_
        funext μ
        have := congrFun hyz μ
        simp only [unlift] at this
        exact ZMod.valMinAbs_inj.1 (by exact_mod_cast this)
      · intro hz
        exact (hmem _).2 ⟨z, hz, rfl⟩
    refine ⟨X', ⟨?_, ?_, ?_⟩, hYeq⟩
    · exact (hmem _).2 ⟨0, h0, unlift_zero j⟩
    · intro z hz μ
      obtain ⟨y₀, -, rfl⟩ := (hmem _).1 hz
      have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
        have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
      simp only [unlift]
      rw [ZMod.coe_valMinAbs]
    · rw [hYeq]; exact hY
  · rintro ⟨X', ⟨h0, -, hX⟩, rfl⟩
    exact ⟨hX, zero_mem_Ypoly h0⟩

open Classical in
/-- **`Eloc` at the origin as a finite sum over the shapes.** -/
theorem Eloc_zero_eq_sum (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁) (Tm : Terms d L N₁ m₁ k N ϱ)
    (ψ h : Fld d L N₁ m₁ k N) :
    Eloc P.m₀ Tm j (0 : CTorus d L N₁ m₁ k) ψ h =
      ∑ X' ∈ (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j).toFinset,
        Tm.E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ψ h := by
  unfold Eloc
  rw [polysAt_zero_eq_image hjk hN]
  rw [finsum_mem_image (g := fun X' => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
    (f := fun Y => Tm.E j 0 Y ψ h) (liftPolys_injOn hjk)]
  exact finsum_mem_eq_finite_toFinset_sum _ _

end Shapes

end Balaban.SmallField.Def6
