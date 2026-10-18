/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerHullPlusGeom

/-!
# The size of the hull of a thickened cube set (`StepTowerHullPlusSize`)

Let `S` be a set of cubes of index one with `sitesOf S` a polymer of index one, and let
`sitesOf S ⊆ X` be a site set each of whose sites lies in a cell of side `a_{m₀}` that is equal or
`*`-adjacent to the cell of a site of `sitesOf S` (for `X = thickSet G (sitesOf S)` this is
`thickSet_cellNear`).  For `L ≥ 3`:

* `cellCount_piHull_thick_le`: the `π′`-hull of `X` has at most `3^d L^{2d} |S|` cells of side
  `a_{m₀}`;
* `sizeJ_piHull_thick_le`: `d_{m₀}(hull X) ≤ d_1(sitesOf S) + (3^d L^{2d} |S|) · 6 d L`; the tree
  of index one of `sitesOf S` is joined to a cell of the hull by three links of cost `2 d L`
  (inside a box of index one, inside the aligned box of `exists_box_of_cellNear`, inside the box
  of the hull containing the cell);
* `sizeJ_piHull_thick_le_dExt`: `d_{m₀}(hull X) ≤ α′ (1 + dExt S)`,
  `α′ = 1 + 3^d L^{2d} c₁ · 6 d L`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer Balaban.SmallField
  Balaban.SmallField.Def6

section Size

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **Cells of the hull of a thickened set.** -/
theorem cellCount_piHull_thick_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ))
    {X : Set (CTorus d L N₁ m₁ K)}
    (hnear : ∀ s ∈ X, ∃ x ∈ sitesOf S, CellNear (L := L) (N₁ := N₁) (m₁ := m₁) m₀ K x s) :
    cellCount (cellSide L m₀ m₁ K) (sitesOf (piHull m₀ X)) ≤
      L ^ d * L ^ d * (S.card * 3 ^ d) := by
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hM).trans hN
  have ha1 := cellSide_dvd (K := K) (m₁ := m₁) hN1 (le_refl K)
  have ha10 := cellSide_pos (L := L) 1 m₁ K
  have hdiv : cellSide L 1 m₁ K ∣ cellSide L m₀ m₁ K := by
    unfold cellSide; exact pow_dvd_pow L (by omega)
  have hch := chosenOne_piHull (m₀ := m₀) hN X
  set Q : Finset (Fin d → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-1 : ℤ) 1 with hQ
  have hQc : Q.card = 3 ^ d := by simp [hQ]
  set W : Finset (CTorus d L N₁ m₁ K) := (S ×ˢ Q).image fun p =>
    cbase (cellSide L m₀ m₁ K) p.1.1 + fun μ => (((cellSide L m₀ m₁ K : ℤ) * p.2 μ : ℤ) :
      ZMod (N₁ * L ^ m₁ * L ^ K)) with hW
  have hmeet : ∀ b ∈ piBases m₀ X, ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ K) := by
    intro b hb
    obtain ⟨hal, s, hsb, hsX⟩ := hb
    obtain ⟨x, hxS, q, hq, hcb⟩ := hnear s hsX
    obtain ⟨β, hβ, hxβ⟩ := mem_sitesOf.1 hxS
    have e1 : cbase (cellSide L 1 m₁ K) x = β.1 := cbase_eq_of_mem_box ha1 β.2.1 hxβ
    have e2 : cbase (cellSide L m₀ m₁ K) x = cbase (cellSide L m₀ m₁ K) β.1 := by
      calc cbase (cellSide L m₀ m₁ K) x
          = cbase (cellSide L m₀ m₁ K) (cbase (cellSide L 1 m₁ K) x) :=
            (cbase_cbase_of_dvd_hull ha10 hdiv x).symm
        _ = _ := by rw [e1]
    refine ⟨cbase (cellSide L m₀ m₁ K) s, ?_, ?_⟩
    · rw [hW, Finset.mem_image]
      refine ⟨(β, fun μ => q μ), ?_, ?_⟩
      · rw [Finset.mem_product]
        refine ⟨hβ, ?_⟩
        rw [hQ, Fintype.mem_piFinset]
        intro μ
        have := hq μ
        rw [Finset.mem_Icc]
        rw [abs_le] at this
        exact_mod_cast this
      · simp only
        rw [← e2]
        exact hcb.symm
    · exact cell_subset_cube ha ha0 hal hsb (mem_box_self _ ha0)
  have h := cellCount_le ha ha0 (fun b hb => hb.1) hch.2 hmeet
  refine h.trans (Nat.mul_le_mul_left _ (Finset.card_image_le.trans ?_))
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, hQc]

open Classical in
/-- **The size of the hull of a thickened set against the size of the set.** -/
theorem sizeJ_piHull_thick_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀) (hL : 3 ≤ L)
    {S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)}
    (hS : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) 1 K (sitesOf S))
    {X : Set (CTorus d L N₁ m₁ K)} (hSX : sitesOf S ⊆ X)
    (hnear : ∀ s ∈ X, ∃ x ∈ sitesOf S, CellNear (L := L) (N₁ := N₁) (m₁ := m₁) m₀ K x s)
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ X))) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ X)) ≤
      dExt S + ((L ^ d * L ^ d * (S.card * 3 ^ d) : ℕ) : ℝ) * (6 * d * L) := by
  set Y := sitesOf (piHull m₀ X) with hYdef
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have ha10 := cellSide_pos (L := L) 1 m₁ K
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hdiv : cellSide L 1 m₁ K ∣ cellSide L m₀ m₁ K := by
    unfold cellSide; exact pow_dvd_pow L (by omega)
  have hle : cellSide L 1 m₁ K ≤ cellSide L m₀ m₁ K := Nat.le_of_dvd ha0 hdiv
  have hYDj : IsDj m₀ K Y := isDj_of_isPolyDom hY
  have hSDj : IsDj 1 K (sitesOf S) := isDj_of_isPolyDom hS
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, he⟩ := treeLenCovOne_attained 1 K (sitesOf S) (by
    obtain ⟨𝒦, W, E, h⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hSDj
    obtain ⟨a, b, c, d⟩ := chosen_of_admissible h
    exact ⟨𝒦, W, E, a, b, c, d⟩)
  have hSY : sitesOf S ⊆ Y := hSX.trans (subset_sitesOf_piHull hN X)
  have hω : ∀ x y : CTorus d L N₁ m₁ K, 0 ≤ scaleW L m₀ m₁ K x y := fun x y => by
    unfold scaleW; positivity
  have haR : ((cellSide L m₀ m₁ K : ℕ) : ℝ) = (L : ℝ) ^ (m₀ + m₁ + K) := by
    unfold cellSide; push_cast; congr 1; ring
  have hc : ∀ x ∈ Y, ∀ y ∈ Y, scaleW L m₀ m₁ K x y ≤ (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹ :=
    fun x y _ _ => by unfold scaleW; rw [haR]
  have hapos : (0 : ℝ) < ((cellSide L m₀ m₁ K : ℕ) : ℝ) := by exact_mod_cast ha0
  have hcost1 : 2 * ((d : ℝ) * ((L * cellSide L 1 m₁ K : ℕ) : ℝ) *
      (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) ≤ 2 * d * L := by
    have : ((L * cellSide L 1 m₁ K : ℕ) : ℝ) * (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹ ≤ L := by
      rw [← div_eq_mul_inv, div_le_iff₀ hapos]
      have : (cellSide L 1 m₁ K : ℝ) ≤ cellSide L m₀ m₁ K := by exact_mod_cast hle
      push_cast
      nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hcost2 : 2 * ((d : ℝ) * ((L * cellSide L m₀ m₁ K : ℕ) : ℝ) *
      (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) = 2 * d * L := by
    push_cast; field_simp
  have hboxY : ∀ b ∈ piBases m₀ X, box b (L * cellSide L m₀ m₁ K) ⊆ Y := fun b hb => by
    rw [hYdef, sitesOf_piHull hN]
    exact Set.subset_iUnion₂ (s := fun b (_ : b ∈ piBases m₀ X) =>
      box b (L * cellSide L m₀ m₁ K)) b hb
  have hlink : ∀ b ∈ fullCover m₀ K Y, ∃ p ∈ W,
      Linked Y (scaleW L m₀ m₁ K) (6 * d * L) p b := by
    intro b hb
    have hbY : b ∈ Y := hb.2 (mem_box_self b (Nat.mul_pos hL0 ha0))
    have hbY' := hbY
    rw [hYdef, sitesOf_piHull hN] at hbY'
    obtain ⟨b₀, hb₀, hbb₀⟩ := Set.mem_iUnion₂.1 hbY'
    obtain ⟨hal0, s, hsb₀, hsX⟩ := hb₀
    obtain ⟨x, hxS, hxs⟩ := hnear s hsX
    obtain ⟨b', hb'al, hxb', hsb'⟩ := exists_box_of_cellNear (m₁ := m₁) hN hL hxs
    have hb'P : b' ∈ piBases m₀ X := ⟨hb'al, s, hsb', hsX⟩
    obtain ⟨κ, hκ, hxκ⟩ := h1.2 x hxS
    obtain ⟨w, hwW, hwκ⟩ := h4 κ hκ
    have hκY : box κ (L * cellSide L 1 m₁ K) ⊆ Y := (h1.1 κ hκ).2.trans hSY
    have l1 := linked_box_pair (R := Y) (ω := scaleW L m₀ m₁ K) hω κ (L * cellSide L 1 m₁ K)
      (c := (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) hκY hc hwκ hxκ
    have l2 := linked_box_pair (R := Y) (ω := scaleW L m₀ m₁ K) hω b' (L * cellSide L m₀ m₁ K)
      (c := (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) (hboxY b' hb'P) hc hxb' hsb'
    have l3 := linked_box_pair (R := Y) (ω := scaleW L m₀ m₁ K) hω b₀ (L * cellSide L m₀ m₁ K)
      (c := (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) (hboxY b₀ ⟨hal0, s, hsb₀, hsX⟩) hc hsb₀ hbb₀
    refine ⟨w, hwW, Covers.mono_c (Linked.trans hω (Linked.trans hω l1 l2) l3) ?_⟩
    linarith
  obtain ⟨W', E', g1, g2, g3, g4⟩ := extend_tree_of_linked (m₀ := m₀) (j := K) hω h2
    (h3.trans hSY) (ρ := 6 * d * L) (by positivity) hlink
  have hcc := cellCount_piHull_thick_le (m₁ := m₁) (K := K) hN hM S hnear
  have hccR : (cellCount (cellSide L m₀ m₁ K) Y : ℝ) ≤
      ((L ^ d * L ^ d * (S.card * 3 ^ d) : ℕ) : ℝ) := by
    exact_mod_cast hcc
  have hcostle : bondCost (scaleW L m₀ m₁ K) E ≤ bondCost (scaleW L 1 m₁ K) E := by
    unfold bondCost scaleW
    refine Finset.sum_le_sum fun _ _ => ?_
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_right₀ (by exact_mod_cast hL0) (by omega)
  have hdE : dExt S = treeLenCovOne 1 K (sitesOf S) := dExt_eq_sizeJ_of_isPolyDom hS
  calc sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y
      = treeLenCovOne m₀ K Y := rfl
    _ ≤ bondCost (scaleW L m₀ m₁ K) E' := treeLenCovOne_le_of_chosen (fullCover_chosen hYDj) g1 g2 g3
    _ ≤ bondCost (scaleW L m₀ m₁ K) E +
        (cellCount (cellSide L m₀ m₁ K) Y : ℝ) * (6 * d * L) := g4
    _ ≤ dExt S + ((L ^ d * L ^ d * (S.card * 3 ^ d) : ℕ) : ℝ) * (6 * d * L) := by
        rw [hdE, ← he]
        have : (0 : ℝ) ≤ 6 * d * L := by positivity
        nlinarith

end Size

end Balaban.Inhabited
