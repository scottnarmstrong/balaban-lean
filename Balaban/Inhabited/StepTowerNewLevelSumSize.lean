/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLabelsHull
public import Balaban.Fluctuation.LocalClassDensityFamilyNumA
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Localization.TreeLengthPaper
public import Balaban.Localization.BlockCount

/-!
# The size of the hull of a cube set of index one (`StepTowerNewLevelSumSize`)

For a set `S` of cubes of index one and level `K` whose sites form a polymer of index one, the
`π′`-hull `Y = sitesOf (piHull m₀ (sitesOf S))` of index `m₀ ≥ 1` has at most `L^{2d} |S|` cells
of side `a_{m₀}` (`cellCount_piHull_le`), and its size of index `m₀` satisfies
`d_{m₀}(Y) ≤ d_1(sitesOf S) + 4 d L · L^{2d} |S|` (`sizeJ_piHull_le`): the optimal tree of index
one for `sitesOf S` is joined to every `π′`-cube of index `m₀` inside `Y` by two paths, one inside
the `π′`-cube of index one through a point of `S` met by it, one inside the `π′`-cube of index `m₀`,
each of cost at most `2 d L` in the units of index `m₀`.  With `|S| ≤ c₁ (1 + d_1)` this is
`sizeJ_piHull_le_dExt`: `d_{m₀}(Y) ≤ (1 + 4 d L · L^{2d} c₁) (1 + d_1(sitesOf S))`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer Balaban.SmallField
  Balaban.SmallField.Def6

section Size

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **Cells of the hull.**  The `π′`-hull of index `m₀ ≥ 1` of the sites of a set `S` of cubes of
index one contains at most `L^{2d} |S|` aligned cells of side `a_{m₀}`. -/
theorem cellCount_piHull_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)) :
    cellCount (cellSide L m₀ m₁ K) (sitesOf (piHull m₀ (sitesOf S))) ≤
      L ^ d * L ^ d * S.card := by
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hM).trans hN
  have ha1 := cellSide_dvd (K := K) (m₁ := m₁) hN1 (le_refl K)
  have ha10 := cellSide_pos (L := L) 1 m₁ K
  have hdiv : cellSide L 1 m₁ K ∣ cellSide L m₀ m₁ K := by
    unfold cellSide; exact pow_dvd_pow L (by omega)
  have hch := chosenOne_piHull (m₀ := m₀) hN (sitesOf S)
  have hmeet : ∀ b ∈ piBases m₀ (sitesOf S),
      ∃ x ∈ S.image (fun c => c.1), x ∈ box b (L * cellSide L m₀ m₁ K) := by
    intro b hb
    obtain ⟨hal, s, hsb, hsS⟩ := hb
    obtain ⟨β, hβ, hsβ⟩ := mem_sitesOf.1 hsS
    refine ⟨β.1, Finset.mem_image_of_mem _ hβ, ?_⟩
    have e1 : cbase (cellSide L 1 m₁ K) s = β.1 := cbase_eq_of_mem_box ha1 β.2.1 hsβ
    have e2 : cbase (cellSide L m₀ m₁ K) s = cbase (cellSide L m₀ m₁ K) β.1 := by
      calc cbase (cellSide L m₀ m₁ K) s
          = cbase (cellSide L m₀ m₁ K) (cbase (cellSide L 1 m₁ K) s) :=
            (cbase_cbase_of_dvd_hull ha10 hdiv s).symm
        _ = _ := by rw [e1]
    refine cell_subset_cube ha ha0 hal hsb ?_
    rw [e2]
    exact mem_box_cbase ha0 β.1
  have h := cellCount_le ha ha0 (fun b hb => hb.1) hch.2 hmeet
  exact h.trans (Nat.mul_le_mul_left _ (Finset.card_image_le.trans Finset.card_image_le))

open Classical in
/-- **The size of the hull against the size of the set.**  For `S` of index one with
`sitesOf S` a polymer of index one and `m₀ ≥ 1`:
`d_{m₀}(hull) ≤ d_1(sitesOf S) + (L^{2d} |S|) · 4 d L`. -/
theorem sizeJ_piHull_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    {S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)}
    (hS : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) 1 K (sitesOf S)) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ (sitesOf S))) ≤
      dExt S + ((L ^ d * L ^ d * S.card : ℕ) : ℝ) * (4 * d * L) := by
  set Y := sitesOf (piHull m₀ (sitesOf S)) with hY
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have ha10 := cellSide_pos (L := L) 1 m₁ K
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hdiv : cellSide L 1 m₁ K ∣ cellSide L m₀ m₁ K := by
    unfold cellSide; exact pow_dvd_pow L (by omega)
  have hle : cellSide L 1 m₁ K ≤ cellSide L m₀ m₁ K := Nat.le_of_dvd ha0 hdiv
  have hYpoly := isPolyDom_sitesOf_piHull_of_isPolyDom (m₀ := m₀) hN hS
  have hYDj : IsDj m₀ K Y := isDj_of_isPolyDom hYpoly
  have hSDj : IsDj 1 K (sitesOf S) := isDj_of_isPolyDom hS
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, he⟩ := treeLenCovOne_attained 1 K (sitesOf S) (by
    obtain ⟨𝒦, W, E, h⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hSDj
    obtain ⟨a, b, c, d⟩ := chosen_of_admissible h
    exact ⟨𝒦, W, E, a, b, c, d⟩)
  have hSY : sitesOf S ⊆ Y := subset_sitesOf_piHull hN _
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
  have hlink : ∀ b ∈ fullCover m₀ K Y, ∃ p ∈ W,
      Linked Y (scaleW L m₀ m₁ K) (4 * d * L) p b := by
    intro b hb
    have hbY : b ∈ Y := hb.2 (mem_box_self b (Nat.mul_pos hL0 ha0))
    have hbY' := hbY
    rw [hY, sitesOf_piHull hN] at hbY'
    obtain ⟨b₀, hb₀, hbb₀⟩ := Set.mem_iUnion₂.1 hbY'
    obtain ⟨hal0, s, hsb₀, hsS⟩ := hb₀
    have hb₀Y : box b₀ (L * cellSide L m₀ m₁ K) ⊆ Y := by
      rw [hY, sitesOf_piHull hN]
      exact Set.subset_iUnion₂ (s := fun b (_ : b ∈ piBases m₀ (sitesOf S)) =>
        box b (L * cellSide L m₀ m₁ K)) b₀ ⟨hal0, s, hsb₀, hsS⟩
    obtain ⟨κ, hκ, hsκ⟩ := h1.2 s hsS
    obtain ⟨w, hwW, hwκ⟩ := h4 κ hκ
    have hκY : box κ (L * cellSide L 1 m₁ K) ⊆ Y := (h1.1 κ hκ).2.trans hSY
    have l1 := linked_box_pair (R := Y) (ω := scaleW L m₀ m₁ K) hω κ (L * cellSide L 1 m₁ K)
      (c := (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) hκY hc hwκ hsκ
    have l2 := linked_box_pair (R := Y) (ω := scaleW L m₀ m₁ K) hω b₀ (L * cellSide L m₀ m₁ K)
      (c := (((cellSide L m₀ m₁ K : ℕ) : ℝ))⁻¹) hb₀Y hc hsb₀ hbb₀
    refine ⟨w, hwW, Covers.mono_c (Linked.trans hω l1 l2) ?_⟩
    linarith
  obtain ⟨W', E', g1, g2, g3, g4⟩ := extend_tree_of_linked (m₀ := m₀) (j := K) hω h2
    (h3.trans hSY) (ρ := 4 * d * L) (by positivity) hlink
  have hcc := cellCount_piHull_le (m₁ := m₁) (K := K) hN hM S
  have hccR : (cellCount (cellSide L m₀ m₁ K) Y : ℝ) ≤ ((L ^ d * L ^ d * S.card : ℕ) : ℝ) := by
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
        (cellCount (cellSide L m₀ m₁ K) Y : ℝ) * (4 * d * L) := g4
    _ ≤ dExt S + ((L ^ d * L ^ d * S.card : ℕ) : ℝ) * (4 * d * L) := by
        rw [hdE, ← he]
        have : (0 : ℝ) ≤ 4 * d * L := by positivity
        nlinarith

open Classical in
/-- **The size of the hull against `dExt` of the set of cubes.**  If the `π′`-hull of index
`m₀ ≥ 1` of `sitesOf S` is a polymer of index `m₀`, then, with `α = 1 + L^{2d} c₁ · 4 d L`,
`d_{m₀}(hull) ≤ α (1 + dExt S)`, where `dExt S` is the size of index one (`Mbig` if `sitesOf S`
is not a polymer of index one). -/
theorem sizeJ_piHull_le_dExt (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ))
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K
      (sitesOf (piHull m₀ (sitesOf S)))) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ (sitesOf S))) ≤
      (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) * (1 + dExt S) := by
  have hc1 := one_le_c1 d L
  have hq : (0 : ℝ) ≤ ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L) := by positivity
  have hd0 := dExt_nonneg S
  by_cases htop : dOmega 1 K Set.univ (sitesOf S) = ⊤
  · have hM' : dExt S = Mbig d L N₁ m₁ K := dExt_eq_Mbig htop
    have h1 := sizeJ_le_ncard_sq hY
    have h2 : (sitesOf (piHull m₀ (sitesOf S))).ncard ≤ Fintype.card (CTorus d L N₁ m₁ K) := by
      calc _ ≤ (Set.univ : Set (CTorus d L N₁ m₁ K)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = _ := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    have h3 : ((sitesOf (piHull m₀ (sitesOf S))).ncard : ℝ) ^ 2 ≤ Mbig d L N₁ m₁ K := by
      unfold Mbig
      have : ((sitesOf (piHull m₀ (sitesOf S))).ncard : ℝ) ≤ Fintype.card (CTorus d L N₁ m₁ K) := by
        exact_mod_cast h2
      nlinarith [Nat.cast_nonneg (α := ℝ) (sitesOf (piHull m₀ (sitesOf S))).ncard]
    rw [hM'] at hd0 ⊢
    nlinarith
  · have hne : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      exact htop (h ▸ dOmega_empty)
    obtain ⟨hS, hdE⟩ := isPolyDom_and_dExt_eq_sizeJ hne htop
    have h1 := sizeJ_piHull_le hN hM hS
    have h2 := card_le_dExt (m₀ := 1) (j := K) (Ω := Set.univ) ((pow_dvd_pow L hM).trans hN) le_rfl S
    have h2' : ((L ^ d * L ^ d * S.card : ℕ) : ℝ) ≤
        ((L ^ d * L ^ d : ℕ) : ℝ) * (c1 d L * (1 + dExt S)) := by
      push_cast
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ d * (L : ℝ) ^ d)
      linarith
    have h4 : (0 : ℝ) ≤ 4 * d * L := by positivity
    have := mul_le_mul_of_nonneg_right h2' h4
    nlinarith

end Size

end Balaban.Inhabited
