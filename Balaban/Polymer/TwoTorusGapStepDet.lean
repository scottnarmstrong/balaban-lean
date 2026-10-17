/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsFull
public import Balaban.Polymer.TwoTorusGapIdentFamily

/-!
# The determinant terms at the cells of a polymer (item 24, blocker 7)

Coordinates: the block index of a site of the centred box lies in a centred box of the coarse torus
(`inBox_jBlock`), cubes of a finite set are determined by their sites (`eq_of_sitesOf_eq`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Coord

variable {d : ℕ}

/-- **The block index of a site of the box lies in the coarse box.** -/
theorem inBox_jBlock {L N₀ k j r rc : ℕ} [NeZero L] [NeZero N₀] (hj : j ≤ k)
    (hrc : r < L ^ j * rc) (hc : 2 * rc + 1 < N₀ * L ^ (k - j)) (x : Torus d (N₀ * L ^ k))
    (hx : InBox d r (N₀ * L ^ k) x) : InBox d rc (N₀ * L ^ (k - j)) (jBlock d L N₀ k j x) := by
  have ha : 0 < L ^ j := pow_pos (NeZero.pos L) j
  intro μ
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = (x μ).valMinAbs := ⟨_, rfl⟩
  have hxμ : x μ = ((ξ : ℤ) : ZMod (N₀ * L ^ k)) := by rw [hξ, ZMod.coe_valMinAbs]
  have hξr : |ξ| ≤ r := by rw [hξ]; exact hx μ
  have hq : |ξ / ((L ^ j : ℕ) : ℤ)| ≤ rc := by
    have hapos : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast ha
    have hrc' : (r : ℤ) < ((L ^ j : ℕ) : ℤ) * rc := by exact_mod_cast hrc
    rw [abs_le] at hξr ⊢
    constructor
    · exact (Int.le_ediv_iff_mul_le hapos).2 (by nlinarith)
    · exact (Int.ediv_lt_iff_lt_mul hapos).2 (by nlinarith) |>.le
  have e1 : jBlock d L N₀ k j x μ = (((ξ / ((L ^ j : ℕ) : ℤ) : ℤ)) : ZMod (N₀ * L ^ (k - j))) := by
    show blockCoord (L ^ j) _ (x μ) = _
    rw [hxμ]
    exact blockCoord_intCast (side_eq hj) ha ξ
  rw [e1, valMinAbs_intCast_of_abs_le hc hq]
  exact hq

end Coord

section Cubes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **A finite set of single-cell cubes is determined by its sites.** -/
theorem eq_of_sitesOf_eq (hN : L ^ m₀ ∣ N₁)
    {Y₁ Y₂ : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (h : sitesOf Y₁ = sitesOf Y₂) : Y₁ = Y₂ := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha := cellSide_pos (L := L) m₀ m₁ K
  have key : ∀ {A B : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K
      Set.univ)}, sitesOf A = sitesOf B → ∀ b ∈ A, b ∈ B := by
    intro A B hAB b hb
    have h1 : b.1 ∈ sitesOf A := mem_sitesOf.2 ⟨b, hb, mem_box_self _ ha⟩
    rw [hAB] at h1
    obtain ⟨c, hc, hbc⟩ := mem_sitesOf.1 h1
    have e1 := cbase_eq_of_mem_box hdvd c.2.1 hbc
    have e2 := cbase_eq_of_mem_box hdvd b.2.1 (mem_box_self b.1 ha)
    have : b = c := Subtype.ext (e2.symm.trans e1)
    rwa [this]
  ext b
  exact ⟨key h b, key h.symm b⟩

end Cubes

end Balaban.Polymer.TwoTorusStep
