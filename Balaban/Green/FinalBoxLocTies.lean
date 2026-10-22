/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocW5
public import Balaban.Green.FinalBoxLocCut

/-!
# The macro cover in the local form; the constraint on the cut constants (A6-3, item (L4))

The patches of the cut family `boxCut` are the boxes `B_z × Fin N` of the macro cells
(`spinBoxPatch`), which are the block patches of the finsets `macBoxF z` (`blockPatch_macBoxF`).
The geometry of the macro cover gives the constants of the count of rooted families:

* `cellGraph_degree_le`: a box meets at most `16^d` boxes (`macTags_near_card`), so the cell graph
  has degree at most `16^d`;
* `card_boxes_mem_le`: a block lies in at most `7^d` boxes (`macBox_overlap`);
* `macCellCount`, `macCellCount_union_le`, `macCellCount_macBoxF_le`: the number of macro cells
  meeting a set of blocks (B2's `cellCount`) is subadditive, and at most `16^d` on a box;
* `exp_macCellCount_rootRegion_le`: `e^{a · #cells(R ∪ ⋃_{z ∈ C} B_z)} ≤ e^{a · #cells(R)} θ^{|C|}`,
  `θ = e^{a 16^d}` — the weight hypothesis of `sum_norm_localFormOf_le_of_coef`.

**The constraint (`BoxCutTies`).**  At the cut radius `κ` and the cell rate `a`: `1 ≤ κ`, the macro
size `M_cut` large (`4 pdB e^{pdH κ} ≤ M_cut`, `8 κ 7^d ≤ pdEps M_cut`, the hypotheses of the tagged
family), and `(16^d)² e^{a 16^d} e^{-(κ - 1)} ≤ 1/2` (the count converges with ratio `1/2`).
`BoxCutConsts d L k M_c v a κ α` bundles the hypotheses of the cut family `boxCut` at the level `k`
(mass `v`, weight `a`, macro side `M_c`, cut radius `κ`) with `BoxCutTies` at the cell rate `α`;
`boxCutConsts_exists`.  With
`M_cut = M`, the cube side of the class at the scale `k` in `k`-blocks, the cells are the cubes of
the scale `k` (`M ∣ N₀ = M n_k`) and lie inside the cubes of the scale `k + 1` (side `M L`).
`PrefixInput` fixes `M = c M₁ = L^{m₀ + m₁}` with `c ≥ 14`, `M₁ ≥ 1`, `L ≤ M`, `R₀(d, L) ≤ 5 L M₁` and
no upper bound on `M`: the constraint asks `m₀ + m₁` large (for `κ` fixed first), compatible with
`PrefixInput` (its witness `prefixInput_exists` takes `m₁ = 3`; `prefixTyping0` is parametric in
`m₁`).
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization

section Cover

variable {d N₀ M N : ℕ} [NeZero N₀]

theorem blockPatch_macBoxF :
    blockPatch N (macBoxF d N₀ M) = spinBoxPatch d N₀ M N := by
  funext z
  ext p
  simp [blockPatch, blockSites, spinBoxPatch, mem_macBoxF]

open Classical in
/-- **The degree of the cell graph of the macro cover is at most `16^d`.** -/
theorem cellGraph_degree_le (hM : 0 < M) (z : MacIdx d N₀ M) :
    (cellGraph (blockPatch N (macBoxF d N₀ M))).degree z ≤ 16 ^ d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine (Finset.card_le_card fun w hw => ?_).trans (macTags_near_card hM z)
  rw [SimpleGraph.mem_neighborFinset] at hw
  obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hw
  have hmeet : ∃ p, p ∈ macBox d N₀ M w ∧ p ∈ macBox d N₀ M z := by
    rcases hr with ⟨p, h1, h2⟩ | ⟨p, h1, h2⟩
    · exact ⟨p.1, mem_macBoxF.1 h2, mem_macBoxF.1 h1⟩
    · exact ⟨p.1, mem_macBoxF.1 h1, mem_macBoxF.1 h2⟩
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmeet⟩

open Classical in
/-- A block lies in at most `7^d` boxes. -/
theorem card_boxes_mem_le (hM : 0 < M) (x : L1Torus d N₀) :
    (Finset.univ.filter fun z : MacIdx d N₀ M => x ∈ macBoxF d N₀ M z).card ≤ 7 ^ d := by
  refine le_trans (le_of_eq ?_) (macBox_overlap hM x)
  congr 1
  ext z
  simp [mem_macBoxF]

/-- **The cell count** of a set of blocks: the number of macro cells meeting it, i.e. of the cells
`macZ x` of its blocks (the count of B2's `BoxLocalForm`, on the general torus). -/
def macCellCount (d N₀ M : ℕ) [NeZero N₀] (Y : Finset (L1Torus d N₀)) : ℕ :=
  (Y.image (macZ (d := d) M)).card

theorem macCellCount_union_le (A B : Finset (L1Torus d N₀)) :
    macCellCount d N₀ M (A ∪ B) ≤ macCellCount d N₀ M A + macCellCount d N₀ M B := by
  classical
  unfold macCellCount
  rw [Finset.image_union]
  exact Finset.card_union_le _ _

theorem macCellCount_macBoxF_le (hM : 0 < M) (z : MacIdx d N₀ M) :
    macCellCount d N₀ M (macBoxF d N₀ M z) ≤ 16 ^ d := by
  classical
  unfold macCellCount
  refine (Finset.card_le_card fun w hw => ?_).trans (macTags_near_card hM z)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x,
    macCore_subset_box _ hM (mem_macCore_macZ x), mem_macBoxF.1 hx⟩

theorem macCellCount_rootRegion_le (hM : 0 < M) (R : Finset (L1Torus d N₀))
    (C : Finset (MacIdx d N₀ M)) :
    macCellCount d N₀ M (rootRegion R (macBoxF d N₀ M) C) ≤ macCellCount d N₀ M R + 16 ^ d * C.card := by
  classical
  unfold rootRegion
  refine (macCellCount_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  induction C using Finset.induction_on with
  | empty => simp [macCellCount]
  | @insert z C hz ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem hz]
    refine (macCellCount_union_le _ _).trans ?_
    have := macCellCount_macBoxF_le (N₀ := N₀) hM z
    nlinarith

/-- **The weight of a region**: `e^{a · #cells(R ∪ ⋃_{z ∈ C} B_z)} ≤ e^{a · #cells(R)} θ^{|C|}`,
`θ = e^{a 16^d}`, for `a ≥ 0`. -/
theorem exp_macCellCount_rootRegion_le (hM : 0 < M) {a : ℝ} (ha : 0 ≤ a)
    (R : Finset (L1Torus d N₀)) (C : Finset (MacIdx d N₀ M)) :
    Real.exp (a * macCellCount d N₀ M (rootRegion R (macBoxF d N₀ M) C)) ≤
      Real.exp (a * macCellCount d N₀ M R) * Real.exp (a * 16 ^ d) ^ C.card := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
  have h := macCellCount_rootRegion_le (N₀ := N₀) hM R C
  have h' : (macCellCount d N₀ M (rootRegion R (macBoxF d N₀ M) C) : ℝ) ≤
      macCellCount d N₀ M R + 16 ^ d * C.card := by exact_mod_cast h
  nlinarith

end Cover

/-- **The constraint on the constants of the cut family** at the cut radius `κ` and the cell rate
`a`: `1 ≤ κ`; the macro size `M_cut` satisfies the hypotheses of the tagged family
(`4 pdB e^{pdH κ} ≤ M_cut`, `8 κ 7^d ≤ pdEps M_cut`); and the ratio of the count of rooted families
is at most `1/2`: `(16^d)² e^{a 16^d} e^{-(κ - 1)} ≤ 1/2`. -/
def BoxCutTies (d L Mcut : ℕ) (κ a : ℝ) : Prop :=
  1 ≤ κ ∧ 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ Mcut ∧ 8 * κ * 7 ^ d ≤ pdEps d L * Mcut ∧
    0 ≤ a ∧ ((16 ^ d : ℕ) : ℝ) ^ 2 * (Real.exp (a * 16 ^ d) * Real.exp (-(κ - 1))) ≤ 1 / 2

/-- **`BoxCutTies` is satisfiable** (rule 10): for every `d`, `L ≥ 1` and rate `a ≥ 0`, the
radius `κ = 1 + a 16^d + 2 d log 16 + log 2` and every macro size `M_cut` at least
`max (4 pdB e^{pdH κ}) (8 κ 7^d / pdEps)` satisfy the constraint. -/
theorem boxCutTies_exists (d L : ℕ) [NeZero L] {a : ℝ} (ha : 0 ≤ a) :
    ∃ κ : ℝ, ∀ Mcut : ℕ, 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ Mcut →
      8 * κ * 7 ^ d ≤ pdEps d L * Mcut → BoxCutTies d L Mcut κ a := by
  refine ⟨1 + a * 16 ^ d + 2 * d * Real.log 16 + Real.log 2, fun Mcut h1 h2 => ?_⟩
  have hlog16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h16 : 0 ≤ a * 16 ^ d := by positivity
  have hdd : (0 : ℝ) ≤ 2 * d * Real.log 16 := by positivity
  refine ⟨by linarith, h1, h2, ha, ?_⟩
  have e1 : ((16 ^ d : ℕ) : ℝ) ^ 2 = Real.exp (2 * d * Real.log 16) := by
    rw [show (2 : ℝ) * d * Real.log 16 = (2 * d : ℕ) * Real.log 16 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    push_cast; ring
  rw [e1, ← Real.exp_add, ← Real.exp_add]
  have : 2 * d * Real.log 16 + (a * 16 ^ d +
      -(1 + a * 16 ^ d + 2 * d * Real.log 16 + Real.log 2 - 1)) = -Real.log 2 := by ring
  rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- **The constants of the cut family** at the level `k`. -/
structure BoxCutConsts (d L k Mc : ℕ) [NeZero L] (v a κ α : ℝ) : Prop where
  hd : 0 < d
  hk : 1 ≤ k
  hv0 : 0 ≤ v
  hv1 : v ≤ 1
  ha1 : 1 / 2 ≤ a
  ha2 : a ≤ 2
  hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v
  hM : 0 < Mc
  ties : BoxCutTies d L Mc κ α

/-- **`BoxCutConsts` is satisfiable** (rule 10): `v = a = 1`, the radius `κ` of
`boxCutTies_exists` and every macro side above its bounds. -/
theorem boxCutConsts_exists (d L k : ℕ) [NeZero L] (hd : 0 < d) (hk : 1 ≤ k) {α : ℝ}
    (hα : 0 ≤ α) :
    ∃ κ : ℝ, ∀ Mc : ℕ, 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ Mc →
      8 * κ * 7 ^ d ≤ pdEps d L * Mc → BoxCutConsts d L k Mc 1 1 κ α := by
  obtain ⟨κ, hκ⟩ := boxCutTies_exists d L hα
  refine ⟨κ, fun Mc h1 h2 => ?_⟩
  have hT := hκ Mc h1 h2
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hMc : 0 < Mc := by
    have hε := pdEps_pos (d := d) (L := L) hd
    have h7 : (0 : ℝ) < 7 ^ d := by positivity
    have : (0 : ℝ) < pdEps d L * Mc := lt_of_lt_of_le (by nlinarith [hT.1]) h2
    have : (0 : ℝ) < Mc := pos_of_mul_pos_right this hε.le
    exact_mod_cast this
  exact ⟨hd, hk, zero_le_one, le_rfl, by norm_num, by norm_num, by linarith, hMc, hT⟩

end Balaban.Green
