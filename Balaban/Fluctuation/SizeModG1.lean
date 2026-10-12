/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reduction to `treeLenCovOne` and (G1) (FLUCTUATION.md Lemma 1.2)

* `dcovMod_of_subset`: for `X ⊆ Ω` the modular size is the landed `treeLenCovOne`.
* `G1_cellCount`: `n_π(X ∩ Ω) ≤ c₁ (1 + d^cov_j(X mod Ω^c))`.
* `G1_card`: `|X| ≤ c₁ a^d (1 + d^cov_j(X))` for `X ∈ 𝒟_j` (`|X|` in fine sites, `a = M L^j`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

section Reduction

omit [NeZero N₁] [NeZero L] in
/-- For `X ⊆ Ω` an admissible pair for the modular size is a chosen family and a structure. -/
theorem modAdmissible_iff_chosen {Ω X 𝒦 : Set (CTorus d L N₁ m₁ K)} (hXΩ : X ⊆ Ω)
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)} :
    ModAdmissible m₀ j Ω X 𝒦 W E ↔
      ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W := by
  have hX : X ∩ Ω = X := Set.inter_eq_left.2 hXΩ
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨h1, fun z hz => ?_⟩, h3, h4, h5⟩
    rw [hX] at h2
    obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (h2 hz)
    exact ⟨b, hb, hzb⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    refine ⟨h1, ?_, h3, h4, h5⟩
    rw [hX]
    intro z hz
    obtain ⟨b, hb, hzb⟩ := h2 z hz
    exact Set.mem_iUnion₂.2 ⟨b, hb, hzb⟩

omit [NeZero N₁] [NeZero L] in
theorem treeLenCovOne_le_of_chosen {X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h1 : ChosenOne m₀ j X 𝒦) (h2 : ConnStruct W E) (h3 : (↑W ⊆ X)) (h4 : MeetsOne m₀ j 𝒦 W) :
    treeLenCovOne m₀ j X ≤ bondCost (scaleW L m₀ m₁ j) E := by
  refine csInf_le ⟨0, ?_⟩ ⟨𝒦, W, E, h1, h2, h3, h4, rfl⟩
  rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
  exact bondCost_scaleW_nonneg E

/-- **The remark of FLUCTUATION.md §1.2**: for `X ⊆ Ω` the modular covering size reduces to
`d^cov_j(X)`, i.e. `treeLenCovOne`. -/
theorem dcovMod_of_subset {Ω X : Set (CTorus d L N₁ m₁ K)} (hXΩ : X ⊆ Ω) :
    dcovMod m₀ j Ω X = treeLenCovOne m₀ j X := by
  by_cases hex : ∃ 𝒦 W E, ModAdmissible m₀ j Ω X 𝒦 W E
  · obtain ⟨𝒦, W, E, hE, hcost⟩ := exists_admissible_eq_dcovMod hex
    obtain ⟨h1, h2, h3, h4⟩ := (modAdmissible_iff_chosen hXΩ).1 hE
    obtain ⟨𝒦', W', E', h1', h2', h3', h4', hc'⟩ :=
      treeLenCovOne_attained m₀ j X ⟨𝒦, W, E, h1, h2, h3, h4⟩
    refine le_antisymm ?_ ?_
    · rw [← hc']
      exact dcovMod_le_of_admissible ((modAdmissible_iff_chosen hXΩ).2 ⟨h1', h2', h3', h4'⟩)
    · rw [← hcost]
      exact treeLenCovOne_le_of_chosen h1 h2 h3 h4
  · have htop : dcovModE m₀ j Ω X = ⊤ := by
      refine le_antisymm le_top (le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E =>
        le_iInf fun h => absurd ⟨𝒦, W, E, h⟩ hex)
    have hnone : ¬ ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧
        MeetsOne m₀ j 𝒦 W := fun ⟨𝒦, W, E, h⟩ =>
      hex ⟨𝒦, W, E, (modAdmissible_iff_chosen hXΩ).2 h⟩
    have hemp : {x | ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧
        MeetsOne m₀ j 𝒦 W ∧ x = bondCost (scaleW L m₀ m₁ j) E} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x ⟨𝒦, W, E, h1, h2, h3, h4, _⟩ => hnone ⟨𝒦, W, E, h1, h2, h3, h4⟩
    unfold dcovMod treeLenCovOne
    rw [htop, hemp]
    simp

end Reduction

section G1

/-- **(G1), cube count.**  `n_π(X ∩ Ω) ≤ c₁ (1 + d^cov_j(X mod Ω^c))`, where `n_π(X ∩ Ω)` is the
number of `π_j`-cubes contained in `X ∩ Ω`. -/
theorem G1_cellCount (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω X : Set (CTorus d L N₁ m₁ K)}
    (hX : DjMod m₀ j Ω X) :
    (cellCount (cellSide L m₀ m₁ j) (X ∩ Ω) : ℝ) ≤ c1 d L * (1 + dcovMod m₀ j Ω X) := by
  obtain ⟨𝒦, W, E, hE, hcost⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) hX.1)
  rw [← hcost]
  exact cellCount_le_of_admissible hN hj hE

open Classical in
/-- Number of fine sites in a union of cells: `|X| ≤ a^d · n_π(X)`. -/
theorem ncard_le_of_isPiPrimeUnion (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPiPrimeUnion m₀ j X) :
    (X.ncard : ℝ) ≤ ((cellSide L m₀ m₁ j : ℕ) : ℝ) ^ d *
      cellCount (cellSide L m₀ m₁ j) X := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have hXfin : X.ncard = (Finset.univ.filter (· ∈ X)).card := by
    rw [Set.ncard_eq_toFinset_card' X]; congr 1; ext; simp
  set F := Finset.univ.filter (· ∈ X) with hF
  have hmap : ∀ x ∈ F, cbase a x ∈ Finset.univ.filter
      (fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ box b a ⊆ X) := by
    intro x hx
    have hx' : x ∈ X := by simpa [hF] using hx
    obtain ⟨b, hb1, hb2, hb3⟩ := hX x hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨aligned_cbase x, (cell_subset_cube hdvd ha0 hb1 hb2).trans hb3⟩
  have hfib : ∀ t ∈ Finset.univ.filter (fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ box b a ⊆ X),
      (F.filter fun x => cbase a x = t).card ≤ a ^ d := by
    intro t _
    have hsub : (F.filter fun x => cbase a x = t) ⊆
        (Fintype.piFinset fun _ : Fin d => Finset.range a).image
          (fun w : Fin d → ℕ => t + natT w) := by
      intro x hx
      have hxt := (Finset.mem_filter.1 hx).2
      obtain ⟨w, hw, hxw⟩ := (hxt ▸ mem_box_cbase ha0 x : x ∈ box t a)
      exact Finset.mem_image.2 ⟨w, by simpa using hw, hxw.symm⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range a).card := Finset.card_image_le
      _ = a ^ d := by simp [Fintype.card_piFinset]
  have key := Finset.card_le_mul_card_image_of_maps_to hmap (a ^ d) hfib
  have key' : F.card ≤ a ^ d * cellCount a X := by
    unfold cellCount
    simpa [mul_comm] using key
  rw [hXfin]
  exact_mod_cast key'

/-- **(G1), site count.**  For `X ∈ 𝒟_j`: `|X| ≤ c₁ a^d (1 + d^cov_j(X))` with `a = M L^j` (the
number of fine sites; in units of scale-`j` sites divide by `L^{jd}`). -/
theorem G1_card (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ j X) :
    (X.ncard : ℝ) ≤ c1 d L * ((cellSide L m₀ m₁ j : ℕ) : ℝ) ^ d * (1 + treeLenCovOne m₀ j X) := by
  have h1 := ncard_le_of_isPiPrimeUnion hN hj hX.2.1
  have h2 := G1_cellCount hN hj (Ω := Set.univ) (X := X)
    ⟨hX, fun z hz => absurd (Set.mem_univ z) hz⟩
  rw [Set.inter_univ, dcovMod_of_subset (Set.subset_univ X)] at h2
  have hc : 0 ≤ c1 d L := by unfold c1; positivity
  calc (X.ncard : ℝ) ≤ _ := h1
    _ ≤ ((cellSide L m₀ m₁ j : ℕ) : ℝ) ^ d * (c1 d L * (1 + treeLenCovOne m₀ j X)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end G1

end Balaban.Fluctuation
