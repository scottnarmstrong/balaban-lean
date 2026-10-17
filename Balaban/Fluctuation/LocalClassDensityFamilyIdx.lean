/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActDecay
public import Balaban.Localization.TreeLengthPaper
public import Balaban.Localization.BlockCount

/-!
# The size at the block index `1` of a domain of index `M` (`LocalClassDensityFamilyIdx`)

The activities of the inherited labels of a class of index `M = C.m₀` decay in the size
`d^cov_M(Y)` of their domains, while the labels of (M1) have the block index `1` and the size
`d^cov_1(Y)`.  This file compares the two sizes and gives the bound condition `hnumH` of
`classActivityFamily_labelAct` for every index `M ≥ 1`.

* `cellCount_le_pow_mul_cellCount`: a set that is a union of cells of side `r a` contains at most
  `r^d` times as many cells of side `a` (`card_aligned_in_box_mul`).
* `treeLenCovOne_one_le_cellCount`: `d^cov_1(Y) ≤ L^{M-1} d^cov_M(Y) + 2 d L^M · #cells_1(Y)` for a
  domain `Y ∈ 𝒟_j` of index `M`: the optimal tree of index `M` is extended to every cube of index
  `1` of `Y` inside the cubes of index `M` (`extend_tree_of_linked`, `linked_box_pair`), and its
  bonds cost `L^{M-1}` times more at the index `1`.
* `treeLenCovOne_one_le_index`: `d^cov_1(Y) ≤ A_M d^cov_M(Y) + B_M` with
  `B_M = 2 d L^M (L^{M-1})^d c₁` and `A_M = L^{M-1} + B_M` (the cells of index `M` number at most
  `c₁ (1 + d^cov_M(Y))`, `cellCount_le_of_admissible`).
* `classActivityDomains_isDj_index`: the domains of the activity family are domains of `𝒟_{k+1}`
  of the index `C.m₀`.
* `classActivity_hnumH_of_index`: `hnumH` for every index `C.m₀ ≥ 1`, under the rate condition
  `κ_H A_M ≤ 2 κ_dec` and the per-domain condition
  `(∑_{τ : Y ∈ polyDom τ} 2E₀ e^{-κ₀ d(X_τ)}) e^{κ_H B_M} ≤ ε_C`.

The rate condition is not a constant: the slope `A_M` grows like `L^{d(M-1)}` and is attained up to
a factor depending on `d` by domains made of many cells (a tree meeting all cubes of index `1` of
`n^d` cells of index `M` has `≍ n^d L^{d(M-1)}` bonds of the length of a cube of index `1`, a tree
meeting the `n^d` cells has `≍ n^d` bonds of the length of a cube of index `M`).  It asks the rate
of the inherited terms in the size of index `M` to be `L^{d(M-1)}` times the rate `κ_H` of the
labels in the size of index `1`; the amplitude `ε_C` only absorbs the constant `e^{κ_H B_M}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.Polymer Finset

section Compare

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- **Cells of side `a` against cells of side `r a`.**  If every point `y` of `Y` has its cell of
side `r a` inside `Y`, then `Y` contains at most `r^d` times as many aligned cells of side `a` as
aligned cells of side `r a`. -/
theorem cellCount_le_pow_mul_cellCount {a r : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    (hr : 0 < r) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : ∀ y ∈ Y, box (cbase (r * a) y) (r * a) ⊆ Y) :
    cellCount a Y ≤ r ^ d * cellCount (r * a) Y := by
  classical
  unfold cellCount
  refine Finset.card_le_mul_card_image_of_maps_to (f := cbase (r * a)) ?_ (r ^ d) ?_
  · intro b hb
    obtain ⟨-, hbY⟩ := (Finset.mem_filter.1 hb).2
    have hbYm : b ∈ Y := hbY (mem_box_self b ha0)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨aligned_cbase b, hY b hbYm⟩
  · intro c hc
    have hcal : Aligned (r * a) c := (Finset.mem_filter.1 hc).2.1
    refine le_trans (Finset.card_le_card ?_)
      (card_aligned_in_box_mul ha ha0 r (aligned_of_dvd (dvd_mul_left a r) hcal))
    intro b hb
    obtain ⟨hbs, hbc⟩ := Finset.mem_filter.1 hb
    obtain ⟨hal, -⟩ := (Finset.mem_filter.1 hbs).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hal, ?_⟩
    rw [← hbc]
    exact mem_box_cbase (Nat.mul_pos hr ha0) b

/-- **The size of index `1` against the size of index `M`, with the cells of index `1`.**  For a
domain `Y ∈ 𝒟_j` of index `M ≥ 1` (`L^M ∣ N₁`, `j ≤ K`):
`d^cov_1(Y) ≤ L^{M-1} d^cov_M(Y) + 2 d L^M · #cells_1(Y)`, `#cells_1` the number of aligned cells of
side `cellSide L 1 m₁ j` in `Y`.  Every cube of index `1` contained in `Y` lies in a cube of the
optimal chosen family of index `M`, which the optimal tree meets; the two points are linked inside
that cube at the cost `2 d L^M` (`linked_box_pair`), and `extend_tree_of_linked` adds all of
them. -/
theorem treeLenCovOne_one_le_cellCount {M j : ℕ} (hM : 1 ≤ M) (hN : L ^ M ∣ N₁) (hj : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj M j Y) :
    treeLenCovOne 1 j Y ≤ (L : ℝ) ^ (M - 1) * treeLenCovOne M j Y +
      (cellCount (cellSide L 1 m₁ j) Y : ℝ) * (2 * d * (L : ℝ) ^ M) := by
  classical
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hY1 : IsDj 1 j Y := isDj_of_le_m₀ hN hj hM hY
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, he⟩ := treeLenCovOne_attained M j Y (by
    obtain ⟨𝒦, W, E, h⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hY
    obtain ⟨a, b, c, d⟩ := chosen_of_admissible h
    exact ⟨𝒦, W, E, a, b, c, d⟩)
  have ha1R : ((cellSide L 1 m₁ j : ℕ) : ℝ) = (L : ℝ) ^ (1 + m₁ + j) := by
    unfold cellSide; push_cast; congr 1; ring
  have haMR : ((cellSide L M m₁ j : ℕ) : ℝ) = (L : ℝ) ^ (M + m₁ + j) := by
    unfold cellSide; push_cast; congr 1; ring
  have hpow : (L : ℝ) ^ (M + m₁ + j) = (L : ℝ) ^ (M - 1) * (L : ℝ) ^ (1 + m₁ + j) := by
    rw [← pow_add]; congr 1; omega
  have hω : ∀ x y : CTorus d L N₁ m₁ K, 0 ≤ scaleW L 1 m₁ j x y := fun x y => by
    unfold scaleW; positivity
  have hlink : ∀ b ∈ fullCover 1 j Y, ∃ p ∈ W,
      Linked Y (scaleW L 1 m₁ j) (2 * d * (L : ℝ) ^ M) p b := by
    intro b hb
    have hbY : b ∈ Y := hb.2 (mem_box_self b (Nat.mul_pos hL0 (cellSide_pos 1 m₁ j)))
    obtain ⟨Q, hQ, hbQ⟩ := h1.2 b hbY
    obtain ⟨p, hpW, hpQ⟩ := h4 Q hQ
    refine ⟨p, hpW, ?_⟩
    have := linked_box_pair (R := Y) (ω := scaleW L 1 m₁ j) hω Q (L * cellSide L M m₁ j)
      (c := (((cellSide L 1 m₁ j : ℕ) : ℝ))⁻¹) (h1.1 Q hQ).2 (fun x y _ _ => by
        unfold scaleW; rw [ha1R]) hpQ hbQ
    refine Covers.mono_c this (le_of_eq ?_)
    have hM' : (L : ℝ) ^ M = (L : ℝ) * (L : ℝ) ^ (M - 1) := by
      rw [← pow_succ']; congr 1; omega
    push_cast
    rw [haMR, ha1R, hpow, hM']
    field_simp
  obtain ⟨W', E', g1, g2, g3, g4⟩ :=
    extend_tree_of_linked (m₀ := 1) (j := j) hω h2 h3 (by positivity) hlink
  have hcost : bondCost (scaleW L 1 m₁ j) E = (L : ℝ) ^ (M - 1) * bondCost (scaleW L M m₁ j) E := by
    unfold bondCost scaleW
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [hpow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hLR), one_mul]
  calc treeLenCovOne 1 j Y ≤ bondCost (scaleW L 1 m₁ j) E' :=
        treeLenCovOne_le_of_chosen (fullCover_chosen hY1) g1 g2 g3
    _ ≤ bondCost (scaleW L 1 m₁ j) E +
        (cellCount (cellSide L 1 m₁ j) Y : ℝ) * (2 * d * (L : ℝ) ^ M) := g4
    _ = _ := by rw [hcost, he]

/-- **The size of index `1` against the size of index `M`.**  For a domain `Y ∈ 𝒟_j` of index
`M ≥ 1` (`L^M ∣ N₁`, `j ≤ K`): `d^cov_1(Y) ≤ A_M d^cov_M(Y) + B_M` with
`B_M = 2 d L^M (L^{M-1})^d c₁` and `A_M = L^{M-1} + B_M`: `treeLenCovOne_one_le_cellCount`, the
cells of index `1` are at most `(L^{M-1})^d` times the cells of index `M`
(`cellCount_le_pow_mul_cellCount`), and these at most `c₁ (1 + d^cov_M(Y))`
(`cellCount_le_of_admissible` for the optimal tree). -/
theorem treeLenCovOne_one_le_index {M j : ℕ} (hM : 1 ≤ M) (hN : L ^ M ∣ N₁) (hj : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj M j Y) :
    treeLenCovOne 1 j Y ≤
      ((L : ℝ) ^ (M - 1) + 2 * d * (L : ℝ) ^ M * (((L ^ (M - 1)) ^ d : ℕ) : ℝ) * c1 d L) *
        treeLenCovOne M j Y + 2 * d * (L : ℝ) ^ M * (((L ^ (M - 1)) ^ d : ℕ) : ℝ) * c1 d L := by
  classical
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hM).trans hN
  have hcell := treeLenCovOne_one_le_cellCount hM hN hj hY
  -- cells of index `1` against cells of index `M`
  have haM : cellSide L M m₁ j = L ^ (M - 1) * cellSide L 1 m₁ j := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  have hYc : ∀ y ∈ Y, box (cbase (L ^ (M - 1) * cellSide L 1 m₁ j) y)
      (L ^ (M - 1) * cellSide L 1 m₁ j) ⊆ Y := by
    intro y hy
    obtain ⟨b, hb, hyb, hbY⟩ := hY.2.1 y hy
    rw [← haM]
    exact (cell_subset_cube (cellSide_dvd hN hj) (cellSide_pos M m₁ j) hb hyb).trans hbY
  have hcc := cellCount_le_pow_mul_cellCount (cellSide_dvd hN1 hj) (cellSide_pos 1 m₁ j)
    (pow_pos hL0 (M - 1)) hYc
  rw [← haM] at hcc
  have hccR : (cellCount (cellSide L 1 m₁ j) Y : ℝ) ≤
      (((L ^ (M - 1)) ^ d : ℕ) : ℝ) * (cellCount (cellSide L M m₁ j) Y : ℝ) := by
    exact_mod_cast hcc
  -- cells of index `M` against the size of index `M`
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, he⟩ := treeLenCovOne_attained M j Y (by
    obtain ⟨𝒦, W, E, h⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hY
    obtain ⟨a, b, c, d⟩ := chosen_of_admissible h
    exact ⟨𝒦, W, E, a, b, c, d⟩)
  have hcM := cellCount_le_of_admissible hN hj (admissible_of_chosen h1 h2 h3 h4)
  rw [Set.inter_univ, he] at hcM
  have hR0 : (0 : ℝ) ≤ (((L ^ (M - 1)) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc10 : 0 ≤ c1 d L := by unfold c1; positivity
  have hdL : (0 : ℝ) ≤ 2 * d * (L : ℝ) ^ M := by positivity
  have hdM := treeLenCovOne_nonneg M j Y
  have hstep : (cellCount (cellSide L 1 m₁ j) Y : ℝ) ≤
      (((L ^ (M - 1)) ^ d : ℕ) : ℝ) * (c1 d L * (1 + treeLenCovOne M j Y)) :=
    hccR.trans (mul_le_mul_of_nonneg_left hcM hR0)
  calc treeLenCovOne 1 j Y ≤ (L : ℝ) ^ (M - 1) * treeLenCovOne M j Y +
        (cellCount (cellSide L 1 m₁ j) Y : ℝ) * (2 * d * (L : ℝ) ^ M) := hcell
    _ ≤ (L : ℝ) ^ (M - 1) * treeLenCovOne M j Y +
        ((((L ^ (M - 1)) ^ d : ℕ) : ℝ) * (c1 d L * (1 + treeLenCovOne M j Y))) *
          (2 * d * (L : ℝ) ^ M) := by
        gcongr
    _ = _ := by ring

end Compare

section HnumH

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **The domains of the activity family are domains of `𝒟_{k+1}` of the index of the class**
(`isDj_of_polyDom`). -/
theorem classActivityDomains_isDj_index {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hcov : ∀ τ, CovSetup S.G' C.m₀ (jL τ) (XL τ) (𝒦X τ))
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ (jL τ)) E₀ = treeLenCovOne C.m₀ (jL τ) (XL τ))
    (hd : 3 ≤ d) (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) :
    ∀ Y ∈ 𝒴C, IsDj C.m₀ (k + 1) Y := by
  intro Y hY
  rw [h𝒴, Finset.mem_biUnion] at hY
  obtain ⟨τ, -, hYτ⟩ := hY
  exact isDj_of_polyDom S.hG' (hcov τ) hd (hopt τ) hYτ

open Classical in
/-- **The bound condition of the activity family for every index of the class.**  If
`1 ≤ C.m₀`, `L^{C.m₀} ∣ N₁`, the domains of `𝒴C` are domains of `𝒟_{k+1}` of the index `C.m₀`,
`E₀ ≥ 0`, `κ_H ≥ 0`, the rate condition `κ_H A_M ≤ 2 κ_dec` holds and on every domain `Y` of `𝒴C`
`(∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ)}) e^{κ_H B_M} ≤ ε_C`
(`A_M`, `B_M` of `treeLenCovOne_one_le_index`, `M = C.m₀`), then
`∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{C.m₀}(Y)} ≤ ε_C e^{-κ_H d^cov_1(Y)}`
(the hypothesis `hnumH` of `classActivityFamily_labelAct`). -/
theorem classActivity_hnumH_of_index {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ) (hm1 : 1 ≤ C.m₀) (hN : L ^ C.m₀ ∣ N₁)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj C.m₀ (k + 1) Y)
    {E₀ κ₀ κdec κH εC : ℝ} (hE₀ : 0 ≤ E₀) (hκH : 0 ≤ κH)
    (hrate : κH * ((L : ℝ) ^ (C.m₀ - 1) + 2 * d * (L : ℝ) ^ C.m₀ *
      (((L ^ (C.m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L) ≤ 2 * κdec)
    (hres : ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
        2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) else 0) *
      Real.exp (κH * (2 * d * (L : ℝ) ^ C.m₀ * (((L ^ (C.m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L)) ≤
        εC) :
    ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
        2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' C.m₀ Y)
      else 0) ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
  intro Y hY
  set B : ℝ := 2 * d * (L : ℝ) ^ C.m₀ * (((L ^ (C.m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L with hB
  set A : ℝ := (L : ℝ) ^ (C.m₀ - 1) + B with hA
  have hd : treeLenCov S.G' C.m₀ Y = treeLenCovOne C.m₀ (k + 1) Y :=
    treeLenCov_eq_treeLenCovOne S.hG' C.m₀ Y
  have hcmp : treeLenCovOne 1 (k + 1) Y ≤ A * treeLenCovOne C.m₀ (k + 1) Y + B :=
    treeLenCovOne_one_le_index hm1 hN le_rfl (h𝒴dj Y hY)
  have hdM := treeLenCovOne_nonneg (m₁ := m₁) (N₁ := N₁) (L := L) (d := d) (K := k + 1) C.m₀
    (k + 1) Y
  have hexp : Real.exp (-(2 * κdec * treeLenCov S.G' C.m₀ Y)) ≤
      Real.exp (κH * B) * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
    rw [← Real.exp_add, hd]
    refine Real.exp_le_exp.2 ?_
    have h1 : κH * treeLenCovOne 1 (k + 1) Y ≤ κH * (A * treeLenCovOne C.m₀ (k + 1) Y + B) :=
      mul_le_mul_of_nonneg_left hcmp hκH
    have h2 : κH * A * treeLenCovOne C.m₀ (k + 1) Y ≤ 2 * κdec * treeLenCovOne C.m₀ (k + 1) Y :=
      mul_le_mul_of_nonneg_right hrate hdM
    nlinarith
  calc (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ) -
            2 * κdec * treeLenCov S.G' C.m₀ Y)
        else 0)
      ≤ ∑ τ, (if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) else 0) *
          (Real.exp (κH * B) * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y)) := by
        refine Finset.sum_le_sum fun τ _ => ?_
        split_ifs
        · rw [sub_eq_add_neg, Real.exp_add]
          have h0 : 0 ≤ 2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) := by
            positivity
          have h3 := mul_le_mul_of_nonneg_left hexp h0
          calc 2 * E₀ * (Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) *
                Real.exp (-(2 * κdec * treeLenCov S.G' C.m₀ Y)))
              = 2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) *
                Real.exp (-(2 * κdec * treeLenCov S.G' C.m₀ Y)) := by ring
            _ ≤ _ := h3
        · rw [zero_mul]
    _ = ((∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          2 * E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ)) else 0) *
          Real.exp (κH * B)) * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun τ _ => ?_
        ring
    _ ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y) :=
        mul_le_mul_of_nonneg_right (hres Y hY) (Real.exp_pos _).le

end HnumH

end Balaban.Fluctuation
