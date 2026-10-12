/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.BackgroundChangeCompare
public import Balaban.Localization.BlockCount
public import Balaban.Fluctuation.SizeModCells
import Balaban.Polymer.Animals
import Balaban.Fluctuation.SizeModSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Entropy of multiscale polymer domains through a point (FLUCTUATION.md §4.2, Step 4)

The multiscale polymer domains `Y ∈ 𝒟(𝔹_{k+1})` (`IsMultiDom`) are determined by the `π_n`-cubes
(over all layers `n`) that they contain (`cellsOf`, `cellsOf_injOn`), and these form a connected
set of vertices of the graph `cellGraphM` (`cellsOf_connected`).  Under the separation
`ϱ ≥ 4 d L^{1+m₀+m₁}` two adjacent cubes lie in layers `n, n'` with `|n - n'| ≤ 1`
(`cell_adj_layers`), and the graph has maximal degree `cellDeg d L = 3^d (2 + L^d)`
(`cellGraphM_degree_le`).  The block count of `Localization/BlockCount.lean` (`blockCount_fam`,
`n(Y) ≤ L^{2d} 3^{d+1} L (d̃^cov(Y) + 1)`) and the lattice-animal count of
`Polymer/Animals.lean` give

* `multiscale_entropy`: `∑_{Y ∋ x₀} e^{-κ d̃^cov(Y)} ≤ K₀^{ms}(d, L)` for `κ ≥ a_ms(d, L) + 1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

section Arith

theorem aligned_of_dvd {d n a a' : ℕ} (h : a' ∣ a) {b : Torus d n} (hb : Aligned a b) :
    Aligned a' b := fun μ => 
  Nat.mod_eq_zero_of_dvd (dvd_trans h (Nat.dvd_of_mod_eq_zero (hb μ)))

theorem cbase_cbase_of_dvd {d n a a' : ℕ} [NeZero n] (ha0 : 0 < a) (h : a ∣ a') (z : Torus d n) :
    cbase a' (cbase a z) = cbase a' z := by
  funext μ
  have hlt : a * ((z μ).val / a) < n := by
    calc a * ((z μ).val / a) ≤ (z μ).val := Nat.mul_div_le _ _
      _ < n := ZMod.val_lt _
  simp only [cbase]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  obtain ⟨t, rfl⟩ := h
  rw [Nat.mul_div_mul_left _ _ ha0, Nat.div_div_eq_div_mul]

end Arith

section Cells

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- A `π_n`-cube of the layer `n`, labelled by `(n, aligned base)`. -/
def IsCell (v : ℕ × CTorus d L N₁ m₁ K) : Prop :=
  1 ≤ v.1 ∧ v.1 ≤ K ∧ Aligned (cellSide L m₀ m₁ v.1) v.2 ∧
    box v.2 (cellSide L m₀ m₁ v.1) ⊆ (G.layer v.1 : Set (CTorus d L N₁ m₁ K))

/-- Two cells are adjacent when some of their sites are nearest neighbours. -/
def CellAdj (v v' : ℕ × CTorus d L N₁ m₁ K) : Prop :=
  ∃ s ∈ box v.2 (cellSide L m₀ m₁ v.1), ∃ s' ∈ box v'.2 (cellSide L m₀ m₁ v'.1), Nbr s s'

omit [NeZero N₁] [NeZero L] in
theorem CellAdj.symm {v v' : ℕ × CTorus d L N₁ m₁ K} (h : CellAdj m₀ v v') : CellAdj m₀ v' v := by
  obtain ⟨s, hs, s', hs', hn⟩ := h
  exact ⟨s', hs', s, hs, hn.symm⟩

/-- The graph of multiscale cells. -/
def cellGraphM : SimpleGraph (ℕ × CTorus d L N₁ m₁ K) where
  Adj v v' := v ≠ v' ∧ IsCell G m₀ v ∧ IsCell G m₀ v' ∧ CellAdj m₀ v v'
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

omit [NeZero N₁] [NeZero L] in
theorem cellSide_succ (n : ℕ) : cellSide L m₀ m₁ (n + 1) = L * cellSide L m₀ m₁ n := by
  unfold cellSide
  rw [show n + 1 + m₀ + m₁ = (n + m₀ + m₁) + 1 by ring, pow_succ]
  ring

/-- Adjacent cells lie in adjacent layers. -/
theorem cell_adj_layers (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hL : 1 ≤ L)
    {v v' : ℕ × CTorus d L N₁ m₁ K} (hv : IsCell G m₀ v) (hv' : IsCell G m₀ v')
    (h : CellAdj m₀ v v') : v.1 ≤ v'.1 + 1 ∧ v'.1 ≤ v.1 + 1 := by
  obtain ⟨s, hs, s', hs', hn⟩ := h
  obtain ⟨h1, h2, -, hsub⟩ := hv
  obtain ⟨h1', h2', -, hsub'⟩ := hv'
  have hsl : s ∈ G.layer v.1 := Finset.mem_coe.1 (hsub hs)
  have hsl' : s' ∈ G.layer v'.1 := Finset.mem_coe.1 (hsub' hs')
  have hdist : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) s s' ≤
      4 * d * (L : ℝ) ^ (v.1 + (m₀ + m₁)) := by
    have h1 := torusDist_le_mul_supDist s s'
    have h2 : (LargeField.supDist s s' : ℝ) ≤ 1 := by exact_mod_cast supDist_nbr hn
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ (v.1 + (m₀ + m₁)) :=
      one_le_pow₀ (by exact_mod_cast hL)
    have h3 := mul_le_mul_of_nonneg_left h2 hd0
    nlinarith [mul_nonneg hd0 (sub_nonneg.2 hL1)]
  have := layer_near G m₀ hϱ hL h1 h2 hsl hdist
  rwa [G.layerIndex_eq h1' h2' hsl'] at this


/-- The three ways in which two cells can be adjacent. -/
theorem cell_adj_cases (hN : L ^ m₀ ∣ N₁) (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ)
    (hL : 1 ≤ L) {v v' : ℕ × CTorus d L N₁ m₁ K} (hv : IsCell G m₀ v) (hv' : IsCell G m₀ v')
    (h : CellAdj m₀ v v') :
    (v'.1 = v.1 ∧ Near 1 (cellSide L m₀ m₁ v.1) v.2 v'.2) ∨
    (v'.1 = v.1 + 1 ∧ ∃ c, Near 1 (cellSide L m₀ m₁ v.1) v.2 c ∧
        Aligned (cellSide L m₀ m₁ v.1) c ∧ v'.2 = cbase (cellSide L m₀ m₁ (v.1 + 1)) c) ∨
    (v'.1 + 1 = v.1 ∧ ∃ c, Near 1 (cellSide L m₀ m₁ v.1) v.2 c ∧
        Aligned (cellSide L m₀ m₁ v.1) c ∧ v'.2 ∈ box c (cellSide L m₀ m₁ v.1)) := by
  have hlay := cell_adj_layers G m₀ hϱ hL hv hv' h
  obtain ⟨s, hs, s', hs', hn⟩ := h
  obtain ⟨n, b⟩ := v
  obtain ⟨n', b'⟩ := v'
  obtain ⟨h1, h2, hal, -⟩ := hv
  obtain ⟨h1', h2', hal', -⟩ := hv'
  simp only at *
  have hdv := cellSide_dvd (m₁ := m₁) (K := K) hN h2
  have hdv' := cellSide_dvd (m₁ := m₁) (K := K) hN h2'
  have ha0 := cellSide_pos (L := L) m₀ m₁ n
  have ha0' := cellSide_pos (L := L) m₀ m₁ n'
  have hcb : cbase (cellSide L m₀ m₁ n) s = b := cbase_eq_of_mem_box hdv hal hs
  have hcb' : cbase (cellSide L m₀ m₁ n') s' = b' := cbase_eq_of_mem_box hdv' hal' hs'
  have hnear := near_cbase_of_nbr hdv ha0 hn
  rw [hcb] at hnear
  have hcases : n' = n ∨ n' = n + 1 ∨ n' + 1 = n := by omega
  rcases hcases with rfl | rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    rwa [hcb'] at hnear
  · right; left
    refine ⟨rfl, cbase (cellSide L m₀ m₁ n) s', hnear, aligned_cbase s', ?_⟩
    rw [cbase_cbase_of_dvd ha0 ?_, hcb']
    rw [cellSide_succ]; exact dvd_mul_left _ _
  · right; right
    refine ⟨rfl, cbase (cellSide L m₀ m₁ (n' + 1)) s', hnear, aligned_cbase s', ?_⟩
    have hc : Aligned (cellSide L m₀ m₁ n') (cbase (cellSide L m₀ m₁ (n' + 1)) s') :=
      aligned_of_dvd (by rw [cellSide_succ]; exact dvd_mul_left _ _) (aligned_cbase s')
    have hsc : s' ∈ box (cbase (cellSide L m₀ m₁ (n' + 1)) s') (L * cellSide L m₀ m₁ n') := by
      rw [← cellSide_succ]; exact mem_box_cbase (cellSide_pos m₀ m₁ _) s'
    have := cell_subset_cube hdv' ha0' hc hsc
    rw [hcb'] at this
    have h3 := this (mem_box_self _ ha0')
    simp only [cellSide_succ] at h3 ⊢
    exact h3


open Classical in
/-- The candidate neighbours of a cell label. -/
noncomputable def cellCand (v : ℕ × CTorus d L N₁ m₁ K) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  let nr : Finset (CTorus d L N₁ m₁ K) := Finset.univ.filter fun c =>
    Near 1 (cellSide L m₀ m₁ v.1) v.2 c ∧ Aligned (cellSide L m₀ m₁ v.1) c
  nr.image (fun b => (v.1, b)) ∪
  nr.image (fun c => (v.1 + 1, cbase (cellSide L m₀ m₁ (v.1 + 1)) c)) ∪
  nr.biUnion (fun c => (Finset.univ.filter fun x : CTorus d L N₁ m₁ K =>
      Aligned (cellSide L m₀ m₁ (v.1 - 1)) x ∧ x ∈ box c (cellSide L m₀ m₁ v.1)).image
        (fun b => (v.1 - 1, b)))

/-- The maximal degree of the cell graph. -/
def cellDeg (d L : ℕ) : ℕ := 3 ^ d + 3 ^ d + 3 ^ d * L ^ d

theorem card_cellCand_le (hN : L ^ m₀ ∣ N₁) {v : ℕ × CTorus d L N₁ m₁ K} (hv : IsCell G m₀ v) :
    (cellCand m₀ v).card ≤ cellDeg d L := by
  classical
  obtain ⟨h1, h2, hal, -⟩ := hv
  have hn : (Finset.univ.filter fun c : CTorus d L N₁ m₁ K =>
      Near 1 (cellSide L m₀ m₁ v.1) v.2 c ∧ Aligned (cellSide L m₀ m₁ v.1) c).card ≤ 3 ^ d :=
    le_trans (Finset.card_le_card (t := Finset.univ.filter fun c : CTorus d L N₁ m₁ K =>
      Near 1 (cellSide L m₀ m₁ v.1) v.2 c) (fun c hc => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢; exact hc.1))
      (by simpa using card_near_le (d := d) (n := (N₁ * L ^ m₁) * L ^ K) 1 (cellSide L m₀ m₁ v.1) v.2)
  unfold cellCand
  simp only
  refine (Finset.card_union_le _ _).trans ?_
  refine (Nat.add_le_add (Finset.card_union_le _ _) le_rfl).trans ?_
  unfold cellDeg
  refine Nat.add_le_add (Nat.add_le_add (Finset.card_image_le.trans hn)
    (Finset.card_image_le.trans hn)) ?_
  refine (Finset.card_biUnion_le_card_mul _ _ (L ^ d) fun c hc => ?_).trans
    (Nat.mul_le_mul hn le_rfl)
  refine Finset.card_image_le.trans ?_
  obtain ⟨-, hca⟩ := (Finset.mem_filter.1 hc).2
  have hdv := cellSide_dvd (m₁ := m₁) (K := K) hN (show v.1 - 1 ≤ K by omega)
  have hsucc : cellSide L m₀ m₁ v.1 = L * cellSide L m₀ m₁ (v.1 - 1) := by
    have := cellSide_succ (L := L) (m₁ := m₁) m₀ (v.1 - 1)
    rwa [show v.1 - 1 + 1 = v.1 by omega] at this
  have hca' : Aligned (cellSide L m₀ m₁ (v.1 - 1)) c :=
    aligned_of_dvd (by rw [hsucc]; exact dvd_mul_left _ _) hca
  rw [hsucc]
  exact card_aligned_in_cube hdv (cellSide_pos m₀ m₁ _) hca'


theorem cellGraphM_adj {v v' : ℕ × CTorus d L N₁ m₁ K} :
    (cellGraphM G m₀).Adj v v' ↔ v ≠ v' ∧ IsCell G m₀ v ∧ IsCell G m₀ v' ∧ CellAdj m₀ v v' :=
  Iff.rfl

theorem cell_mem_cand (hN : L ^ m₀ ∣ N₁) (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ)
    (hL : 1 ≤ L) {v v' : ℕ × CTorus d L N₁ m₁ K} (h : (cellGraphM G m₀).Adj v v') :
    v' ∈ cellCand m₀ v := by
  classical
  obtain ⟨-, hv, hv', hadj⟩ := h
  have hcases := cell_adj_cases G m₀ hN hϱ hL hv hv' hadj
  obtain ⟨n, b⟩ := v
  obtain ⟨n', b'⟩ := v'
  obtain ⟨h1, h2, hal, -⟩ := hv
  obtain ⟨h1', h2', hal', -⟩ := hv'
  simp only at *
  unfold cellCand
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Prod.mk.injEq]
  rcases hcases with ⟨rfl, hn⟩ | ⟨rfl, c, hn, hca, rfl⟩ | ⟨hh, c, hn, hca, hb⟩
  · left; left
    exact ⟨b', ⟨hn, hal'⟩, rfl, rfl⟩
  · left; right
    exact ⟨c, ⟨hn, hca⟩, rfl, rfl⟩
  · right
    refine ⟨c, ⟨hn, hca⟩, b', ⟨?_, hb⟩, by omega, rfl⟩
    have : n' = n - 1 := by omega
    rw [← this]; exact hal'

noncomputable instance cellGraphM_locFinite : (cellGraphM G m₀).LocallyFinite := fun v => by
  classical
  refine Set.Finite.fintype (Set.Finite.subset
    ((Finset.Icc 1 K ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ K))).finite_toSet) ?_)
  intro v' hv'
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := hv'
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Icc, Finset.mem_univ,
    and_true]
  exact ⟨h1, h2⟩

theorem cellGraphM_degree_le (hN : L ^ m₀ ∣ N₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) (hL : 1 ≤ L)
    (v : ℕ × CTorus d L N₁ m₁ K) : (cellGraphM G m₀).degree v ≤ cellDeg d L := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hv : IsCell G m₀ v
  · refine le_trans (Finset.card_le_card ?_) (card_cellCand_le G m₀ hN hv)
    intro v' hv'
    rw [SimpleGraph.mem_neighborFinset] at hv'
    exact cell_mem_cand G m₀ hN hϱ hL hv'
  · have : (cellGraphM G m₀).neighborFinset v = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v' hv' => hv ?_
      rw [SimpleGraph.mem_neighborFinset] at hv'
      exact hv'.2.1
    rw [this]; simp


/-- **Multiscale polymer domains** `𝒟(𝔹_{k+1})` with a finite covering size: connected subsets of
`Ω₁` that have a chosen family (in every layer `Λ_n`, `Y ∩ Λ_n` is a union of `π'_n`-cubes
contained in it) and a connected structure in `Y` meeting every chosen cube, so that `d̃^cov(Y)`
is the infimum of a nonempty set (LOCALIZATION.md Def-L8). -/
def IsMultiDom (Y : Set (CTorus d L N₁ m₁ K)) : Prop :=
  Y ⊆ (G.Ω 1 : Set (CTorus d L N₁ m₁ K)) ∧ SiteConnected Y ∧
    ∃ 𝒦 W E, ChosenFamily G m₀ Y 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ Y) ∧ MeetsFam m₀ 𝒦 W

open Classical in
/-- The `π_n`-cubes (over all layers) contained in `Y`, as labels `(n, base)`. -/
noncomputable def cellsOf (Y : Set (CTorus d L N₁ m₁ K)) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  (Finset.Icc 1 K ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ K))).filter fun v =>
    IsCell G m₀ v ∧ box v.2 (cellSide L m₀ m₁ v.1) ⊆ Y

theorem mem_cellsOf {Y : Set (CTorus d L N₁ m₁ K)} {v : ℕ × CTorus d L N₁ m₁ K} :
    v ∈ cellsOf G m₀ Y ↔ IsCell G m₀ v ∧ box v.2 (cellSide L m₀ m₁ v.1) ⊆ Y := by
  classical
  unfold cellsOf
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.1, h.1.2.1⟩, h⟩

theorem card_cellsOf (Y : Set (CTorus d L N₁ m₁ K)) :
    (cellsOf G m₀ Y).card = blockCountFam G m₀ Y := by
  classical
  unfold blockCountFam cellCount cellsOf
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
  by_cases h : Aligned (cellSide L m₀ m₁ n) b ∧
      box b (cellSide L m₀ m₁ n) ⊆ Y ∩ (G.layer n : Set (CTorus d L N₁ m₁ K))
  · have h' : IsCell G m₀ (n, b) ∧ box b (cellSide L m₀ m₁ n) ⊆ Y :=
      ⟨⟨hn1, hnK, h.1, fun x hx => (h.2 hx).2⟩, fun x hx => (h.2 hx).1⟩
    simp only [h, h']
  · have h' : ¬ (IsCell G m₀ (n, b) ∧ box b (cellSide L m₀ m₁ n) ⊆ Y) := by
      rintro ⟨⟨-, -, ha, hl⟩, hY⟩
      exact h ⟨ha, fun x hx => ⟨hY hx, hl hx⟩⟩
    simp only [h, h', ↓reduceIte]


/-- The `π_n`-cube (`n` the layer index) containing the site `z`. -/
noncomputable def cellOfSite (z : CTorus d L N₁ m₁ K) : ℕ × CTorus d L N₁ m₁ K :=
  (G.layerIndex z, cbase (cellSide L m₀ m₁ (G.layerIndex z)) z)

theorem cellOfSite_mem (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsMultiDom G m₀ Y)
    {z : CTorus d L N₁ m₁ K} (hz : z ∈ Y) :
    cellOfSite G m₀ z ∈ cellsOf G m₀ Y ∧
      z ∈ box (cellOfSite G m₀ z).2 (cellSide L m₀ m₁ (cellOfSite G m₀ z).1) := by
  obtain ⟨hΩ, -, 𝒦, W, E, hch, -⟩ := hY
  obtain ⟨h1, h2, hzl⟩ := G.layerIndex_spec (hΩ hz)
  set n := G.layerIndex z with hn
  have hdv := cellSide_dvd (m₁ := m₁) (K := K) hN h2
  have ha0 := cellSide_pos (L := L) m₀ m₁ n
  obtain ⟨hch1, hch2⟩ := hch n h1 h2
  obtain ⟨b, hb, hzb⟩ := hch2 z hz (Finset.mem_coe.2 hzl)
  obtain ⟨hbal, hbY, hbl⟩ := hch1 b hb
  have hsub := cell_subset_cube hdv ha0 hbal hzb
  refine ⟨(mem_cellsOf G m₀).2 ⟨⟨h1, h2, aligned_cbase z, hsub.trans hbl⟩, hsub.trans hbY⟩, ?_⟩
  exact mem_box_cbase ha0 z

theorem eq_biUnion_cells (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsMultiDom G m₀ Y) :
    Y = ⋃ v ∈ cellsOf G m₀ Y, box v.2 (cellSide L m₀ m₁ v.1) := by
  ext z
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · intro hz
    exact ⟨_, (cellOfSite_mem G m₀ hN hY hz).1, (cellOfSite_mem G m₀ hN hY hz).2⟩
  · rintro ⟨v, hv, hzv⟩
    exact ((mem_cellsOf G m₀).1 hv).2 hzv

theorem cellsOf_injOn (hN : L ^ m₀ ∣ N₁) {Y Y' : Set (CTorus d L N₁ m₁ K)}
    (hY : IsMultiDom G m₀ Y) (hY' : IsMultiDom G m₀ Y') (h : cellsOf G m₀ Y = cellsOf G m₀ Y') :
    Y = Y' := by
  rw [eq_biUnion_cells G m₀ hN hY, eq_biUnion_cells G m₀ hN hY', h]

theorem cellOfSite_adj (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsMultiDom G m₀ Y) {z z' : CTorus d L N₁ m₁ K} (hz : z ∈ Y) (hz' : z' ∈ Y)
    (hn : Nbr z z') :
    cellOfSite G m₀ z = cellOfSite G m₀ z' ∨
      (cellGraphM G m₀).Adj (cellOfSite G m₀ z) (cellOfSite G m₀ z') := by
  by_cases h : cellOfSite G m₀ z = cellOfSite G m₀ z'
  · exact Or.inl h
  · right
    obtain ⟨hv, hbz⟩ := cellOfSite_mem G m₀ hN hY hz
    obtain ⟨hv', hbz'⟩ := cellOfSite_mem G m₀ hN hY hz'
    exact ⟨h, ((mem_cellsOf G m₀).1 hv).1, ((mem_cellsOf G m₀).1 hv').1, z, hbz, z', hbz', hn⟩

theorem cellsOf_connected (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsMultiDom G m₀ Y) (hne : Y.Nonempty) :
    ((cellGraphM G m₀).induce ((cellsOf G m₀ Y : Finset _) : Set (ℕ × CTorus d L N₁ m₁ K))).Connected := by
  classical
  have hmem : ∀ z ∈ Y, cellOfSite G m₀ z ∈ ((cellsOf G m₀ Y : Finset _) : Set (ℕ × CTorus d L N₁ m₁ K)) :=
    fun z hz => Finset.mem_coe.2 (cellOfSite_mem G m₀ hN hY hz).1
  obtain ⟨z0, hz0⟩ := hne
  have key : ∀ z, Relation.ReflTransGen (fun u v => u ∈ Y ∧ v ∈ Y ∧ Nbr u v) z0 z →
      ∃ hz : z ∈ Y, ((cellGraphM G m₀).induce ((cellsOf G m₀ Y : Finset _) :
        Set (ℕ × CTorus d L N₁ m₁ K))).Reachable ⟨cellOfSite G m₀ z0, hmem z0 hz0⟩
          ⟨cellOfSite G m₀ z, hmem z hz⟩ := by
    intro z h
    induction h with
    | refl => exact ⟨hz0, SimpleGraph.Reachable.refl _⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hr⟩ := ih
      refine ⟨hbc.2.1, hr.trans ?_⟩
      rcases cellOfSite_adj G m₀ hN hY hb hbc.2.1 hbc.2.2 with he | ha
      · have : (⟨cellOfSite G m₀ b, hmem b hb⟩ : ((cellsOf G m₀ Y : Finset _) :
            Set (ℕ × CTorus d L N₁ m₁ K))) = ⟨cellOfSite G m₀ c, hmem c hbc.2.1⟩ := Subtype.ext he
        rw [this]
      · exact SimpleGraph.Adj.reachable (by simpa using ha)
  have : Nonempty ((cellsOf G m₀ Y : Finset _) : Set (ℕ × CTorus d L N₁ m₁ K)) :=
    ⟨⟨cellOfSite G m₀ z0, hmem z0 hz0⟩⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  have hself : ∀ w ∈ cellsOf G m₀ Y, w.2 ∈ Y ∧ cellOfSite G m₀ w.2 = w := by
    intro w hw
    obtain ⟨⟨h1, h2, hal, hl⟩, hsub⟩ := (mem_cellsOf G m₀).1 hw
    have ha0 := cellSide_pos (L := L) m₀ m₁ w.1
    have hself := mem_box_self w.2 ha0
    refine ⟨hsub hself, ?_⟩
    have hli : G.layerIndex w.2 = w.1 := G.layerIndex_eq h1 h2 (Finset.mem_coe.1 (hl hself))
    have hcb : cbase (cellSide L m₀ m₁ w.1) w.2 = w.2 :=
      cbase_eq_of_mem_box (cellSide_dvd hN h2) hal hself
    unfold cellOfSite
    rw [hli, hcb]
  obtain ⟨hu1, hu2⟩ := hself u (Finset.mem_coe.1 hu)
  obtain ⟨hv1, hv2⟩ := hself v (Finset.mem_coe.1 hv)
  obtain ⟨_, hru⟩ := key u.2 (hY.2.1 z0 hz0 u.2 hu1)
  obtain ⟨_, hrv⟩ := key v.2 (hY.2.1 z0 hz0 v.2 hv1)
  have e1 : (⟨cellOfSite G m₀ u.2, hmem u.2 hu1⟩ : ((cellsOf G m₀ Y : Finset _) :
      Set (ℕ × CTorus d L N₁ m₁ K))) = ⟨u, hu⟩ := Subtype.ext hu2
  have e2 : (⟨cellOfSite G m₀ v.2, hmem v.2 hv1⟩ : ((cellsOf G m₀ Y : Finset _) :
      Set (ℕ × CTorus d L N₁ m₁ K))) = ⟨v, hv⟩ := Subtype.ext hv2
  rw [e1] at hru
  rw [e2] at hrv
  exact hru.symm.trans hrv


end Cells

section Entropy

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- The block-count constant `L^{2d} 3^{d+1} L` of `blockCount_fam`. -/
def cBlock (d L : ℕ) : ℕ := L ^ (2 * d) * (3 ^ (d + 1) * L)

/-- **`a_ent` for multiscale domains**: the exponential growth rate of the number of multiscale
polymer domains through a point with `d̃^cov < ℓ + 1`. -/
noncomputable def aMulti (d L : ℕ) : ℝ :=
  2 * (cBlock d L : ℝ) * Real.log (2 * (cellDeg d L : ℝ) ^ 2)

/-- **`K₀` for multiscale domains.** -/
noncomputable def K0Multi (d L : ℕ) : ℝ := Real.exp (aMulti d L) / (1 - Real.exp (-1))

theorem one_le_cellDeg (d L : ℕ) : 1 ≤ cellDeg d L := by
  unfold cellDeg
  have : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem aMulti_nonneg (d L : ℕ) : 0 ≤ aMulti d L := by
  unfold aMulti
  have h1 : (1 : ℝ) ≤ cellDeg d L := by exact_mod_cast one_le_cellDeg d L
  have : 0 ≤ Real.log (2 * (cellDeg d L : ℝ) ^ 2) :=
    Real.log_nonneg (by nlinarith)
  positivity

open Classical in
/-- **Entropy of multiscale polymer domains through a point**: for `κ ≥ a_multi + 1`,
`∑_{Y ∋ x₀} e^{-κ d̃^cov(Y)} ≤ K₀`, the sum over the multiscale polymer domains `Y` containing `x₀`
(LOCALIZATION.md §4.0, Consequences (1): the block-count bound and the animal bound). -/
theorem multiscale_entropy (hN : L ^ m₀ ∣ N₁)
    (hϱ : (4 * d * L * (L : ℝ) ^ (m₀ + m₁) : ℝ) ≤ ϱ) {x₀ : CTorus d L N₁ m₁ K}
    {κ : ℝ} (hκ : aMulti d L + 1 ≤ κ) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) =>
        IsMultiDom G m₀ Y ∧ x₀ ∈ Y), Real.exp (-κ * treeLenCov G m₀ Y) ≤ K0Multi d L := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine sum_exp_le _ _ (fun Y _ => treeLenCov_nonneg G m₀ Y) (aMulti_nonneg d L) hκ
    (fun ℓ => ?_)
  set F := Finset.univ.filter (fun Y : Set (CTorus d L N₁ m₁ K) => IsMultiDom G m₀ Y ∧ x₀ ∈ Y)
  set Nℓ : ℕ := cBlock d L * (ℓ + 2) with hNℓ
  set H := cellGraphM G m₀
  set v₀ := cellOfSite G m₀ x₀
  let A : Finset (Finset (ℕ × CTorus d L N₁ m₁ K)) :=
    (Finset.range (Nℓ + 1)).biUnion fun n => Balaban.Polymer.animals H v₀ n
  have hmaps : ∀ Y ∈ F.filter (fun Y => treeLenCov G m₀ Y < ℓ + 1), cellsOf G m₀ Y ∈ A := by
    intro Y hY
    obtain ⟨hYF, hlt⟩ := Finset.mem_filter.1 hY
    obtain ⟨hMD, hx⟩ := (Finset.mem_filter.1 hYF).2
    have hbc := blockCount_fam G (m₀ := m₀) hN hϱ hL hMD.2.2
    rw [← card_cellsOf] at hbc
    have hn : (cellsOf G m₀ Y).card ≤ Nℓ := by
      have h1 : ((cellsOf G m₀ Y).card : ℝ) < (cBlock d L : ℝ) * (ℓ + 2) := by
        refine lt_of_le_of_lt hbc ?_
        have : (L : ℝ) ^ (2 * d) * (3 ^ (d + 1) * L) = (cBlock d L : ℝ) := by
          unfold cBlock; push_cast; ring
        rw [this]
        have hc : (0 : ℝ) < cBlock d L := by
          unfold cBlock; positivity
        nlinarith
      have h2 : ((cellsOf G m₀ Y).card : ℝ) ≤ (Nℓ : ℝ) := by
        refine h1.le.trans_eq ?_
        rw [hNℓ]; push_cast; ring
      exact_mod_cast h2
    refine Finset.mem_biUnion.2 ⟨(cellsOf G m₀ Y).card, Finset.mem_range.2 (by omega), ?_⟩
    rw [Balaban.Polymer.mem_animals]
    exact ⟨(cellOfSite_mem G m₀ hN hMD hx).1, rfl, cellsOf_connected G m₀ hN hMD ⟨x₀, hx⟩⟩
  have hinj : Set.InjOn (cellsOf G m₀) ((F.filter (fun Y => treeLenCov G m₀ Y < ℓ + 1) : Finset _) :
      Set (Set (CTorus d L N₁ m₁ K))) := by
    intro Y hY Y' hY' h
    have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).1
    have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hY')).1
    exact cellsOf_injOn G m₀ hN (Finset.mem_filter.1 h1).2.1 (Finset.mem_filter.1 h2).2.1 h
  have hcardA : A.card ≤ (Nℓ + 1) * (cellDeg d L) ^ (2 * Nℓ) := by
    refine (Finset.card_biUnion_le).trans ?_
    calc ∑ n ∈ Finset.range (Nℓ + 1), (Balaban.Polymer.animals H v₀ n).card
        ≤ ∑ _n ∈ Finset.range (Nℓ + 1), (cellDeg d L) ^ (2 * Nℓ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          refine (Balaban.Polymer.card_animals_le H (cellGraphM_degree_le G m₀ hN hϱ hL) v₀ n).trans ?_
          exact Nat.pow_le_pow_right (one_le_cellDeg d L) (by
            have := Finset.mem_range.1 hn; omega)
      _ = (Nℓ + 1) * (cellDeg d L) ^ (2 * Nℓ) := by simp
  have hcard : (F.filter (fun Y => treeLenCov G m₀ Y < ℓ + 1)).card ≤ (Nℓ + 1) * (cellDeg d L) ^ (2 * Nℓ) :=
    (Finset.card_le_card_of_injOn _ hmaps hinj).trans hcardA
  have hnat : (Nℓ + 1) * (cellDeg d L) ^ (2 * Nℓ) ≤ (2 * (cellDeg d L) ^ 2) ^ Nℓ := by
    calc (Nℓ + 1) * (cellDeg d L) ^ (2 * Nℓ) ≤ 2 ^ Nℓ * ((cellDeg d L) ^ 2) ^ Nℓ :=
          Nat.mul_le_mul (Nat.lt_two_pow_self : Nℓ < 2 ^ Nℓ) (by rw [pow_mul])
      _ = (2 * (cellDeg d L) ^ 2) ^ Nℓ := (mul_pow _ _ _).symm
  have hreal : ((F.filter (fun Y => treeLenCov G m₀ Y < ℓ + 1)).card : ℝ) ≤
      (2 * (cellDeg d L : ℝ) ^ 2) ^ Nℓ := by
    exact_mod_cast hcard.trans hnat
  refine hreal.trans ?_
  have hpos : (0 : ℝ) < 2 * (cellDeg d L : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ cellDeg d L := by exact_mod_cast one_le_cellDeg d L
    positivity
  have hlog : 0 ≤ Real.log (2 * (cellDeg d L : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ cellDeg d L := by exact_mod_cast one_le_cellDeg d L
    exact Real.log_nonneg (by nlinarith)
  have e1 : (2 * (cellDeg d L : ℝ) ^ 2) ^ Nℓ =
      Real.exp (Nℓ * Real.log (2 * (cellDeg d L : ℝ) ^ 2)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpos]
  rw [e1]
  refine Real.exp_le_exp.2 ?_
  unfold aMulti
  rw [hNℓ]; push_cast
  have hc : (0 : ℝ) ≤ cBlock d L := Nat.cast_nonneg _
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg hc hlog) hℓ]

end Entropy

end Balaban.Fluctuation
