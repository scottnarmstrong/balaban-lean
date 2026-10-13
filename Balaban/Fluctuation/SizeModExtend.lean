/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCellPath
public import Balaban.Fluctuation.SizeModCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Growth of the modular covering size with the region

Packages (2)-(3) of `notes/phase1/VMOD-38.md` §4, in abstract form: finite geometry on the fine
torus `CTorus d L N₁ m₁ K`; no history and no fields.  With `a = cellSide L m₀ m₁ j`:

* **Cells of a union of cells.**  `cellsIn m₀ j S` (landed, `SizeModStruct`) is the finite set of
  bases of the cells contained in `S`; `CellReach` is reachability through `CAdj` (bases
  differing by `a` in one coordinate) inside it; `cellCompBases`, `cellComp` and `cellComps` are
  the connected components of the cell graph (the sets of bases, the unions of the cells, and the
  family of these unions).  `siteConnected_iff_cellReach`: a union of cells is `SiteConnected`
  exactly when its cell graph is connected.  `cell_struct`/`cellComp_struct`: the corners of the
  cells of a connected cell set `Q` lie in a connected structure inside `⋃ Q` of cost at most
  `|Q| - 1` (via `assemble`; no spanning tree is needed).
* **The extension.**  `modAdmissible_extend` (T3): if `Ω₋ ⊆ Ω₊` are unions of cells, `X ∈ 𝒟_j`,
  every cell-component of `X ∩ Ω₋ᶜ` is contained in `Ω₊` or disjoint from it, and `(𝒦, W, E)` is
  `ModAdmissible` for `(Ω₋, X)`, then there is a `ModAdmissible` triple for `(Ω₊, X)` whose cost
  exceeds that of `E` by at most `(d L + d + 3) · #cells(X ∩ (Ω₊ ∖ Ω₋))` (in fact by at most
  `(d L + 1) · #cells`).  `dcovMod_le_add_of_region_grow` (T4) and
  `dcovModE_le_add_of_region_grow` are the resulting inequalities between the sizes.

The construction is one application of `assemble` to the nerve whose nodes are the old structure
`(W, E)` and the corners of the newly active cells; two newly active cells are joined at cost
`1` (`linked_cell_adj`), a newly active cell next to an old active cell is joined to the old
structure at cost `d L + 1` (an old chosen box covers the old cell; `linked_box_site_corner`),
and, when `X` has no old active cell, one corner is joined to an old vertex at cost `d`.  The
hypothesis on the components (`hsplit`) is what makes the nerve connected: a chain of cells of
`X` from a newly active cell to an old active cell cannot pass through an inactive cell.

Typing data: `L^{m₀} ∣ N₁` (cells tile the torus) and `j ≤ K`.

**What is not proved here.**  The application to the operation `R` (the identification of `Ω₋`,
`Ω₊` with the raw and post regions, `hsplit` from the component structure of the removed
components, the count of newly active cells by the removed components) and the analytic charge
are NOT proved here.  The hypothesis `hsplit` cannot be dropped: if a newly active cell is
enclosed inside `X` by a long corridor of cells that stay inactive (cells of `X ∩ Ω₋ᶜ` outside
`Ω₊` forming a component of `X ∩ Ω₋ᶜ` that meets `Ω₊` only in one end), joining that cell to the
old structure costs the corridor length, which is not bounded by a constant times the number of
newly active cells.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

section Comps

variable (m₀ j : ℕ)

/-- Reachability between bases of cells of the union of cells `Z` through adjacent cells
(`CAdj`: bases differing by `a` in one coordinate) contained in `Z`. -/
def CellReach (Z : Set (CTorus d L N₁ m₁ K)) (b b' : CTorus d L N₁ m₁ K) : Prop :=
  Relation.ReflTransGen (fun u v => CAdj (cellSide L m₀ m₁ j) u v ∧
    u ∈ cellsIn m₀ j Z ∧ v ∈ cellsIn m₀ j Z) b b'

open Classical in
/-- The bases of the cell-component of the cell with base `b` in `Z`. -/
noncomputable def cellCompBases (Z : Set (CTorus d L N₁ m₁ K)) (b : CTorus d L N₁ m₁ K) :
    Finset (CTorus d L N₁ m₁ K) :=
  (cellsIn m₀ j Z).filter (CellReach m₀ j Z b)

/-- The cell-component of the cell with base `b` in `Z`: the union of its cells. -/
def cellComp (Z : Set (CTorus d L N₁ m₁ K)) (b : CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  ⋃ t ∈ (cellCompBases m₀ j Z b : Set (CTorus d L N₁ m₁ K)), box t (cellSide L m₀ m₁ j)

/-- The connected components (as sets of sites) of the cell graph of `Z`. -/
def cellComps (Z : Set (CTorus d L N₁ m₁ K)) : Set (Set (CTorus d L N₁ m₁ K)) :=
  {Q | ∃ b ∈ cellsIn m₀ j Z, Q = cellComp m₀ j Z b}

variable {m₀ j}

theorem mem_cellCompBases {Z : Set (CTorus d L N₁ m₁ K)} {b t : CTorus d L N₁ m₁ K} :
    t ∈ cellCompBases m₀ j Z b ↔ t ∈ cellsIn m₀ j Z ∧ CellReach m₀ j Z b t := by
  classical
  simp [cellCompBases]

theorem CellReach.mem {Z : Set (CTorus d L N₁ m₁ K)} {b b' : CTorus d L N₁ m₁ K}
    (h : CellReach m₀ j Z b b') (hb : b ∈ cellsIn m₀ j Z) : b' ∈ cellsIn m₀ j Z := by
  induction h with
  | refl => exact hb
  | tail _ hbc _ => exact hbc.2.2

theorem mem_box_cellComp {Z : Set (CTorus d L N₁ m₁ K)} {b : CTorus d L N₁ m₁ K}
    (hb : b ∈ cellsIn m₀ j Z) : box b (cellSide L m₀ m₁ j) ⊆ cellComp m₀ j Z b := by
  intro x hx
  simp only [cellComp, Set.mem_iUnion, Finset.mem_coe]
  exact ⟨b, mem_cellCompBases.2 ⟨hb, Relation.ReflTransGen.refl⟩, hx⟩

theorem box_subset_cellComp {Z : Set (CTorus d L N₁ m₁ K)} {b t : CTorus d L N₁ m₁ K}
    (ht : t ∈ cellCompBases m₀ j Z b) : box t (cellSide L m₀ m₁ j) ⊆ cellComp m₀ j Z b := by
  intro x hx
  simp only [cellComp, Set.mem_iUnion, Finset.mem_coe]
  exact ⟨t, ht, hx⟩

/-- **A union of cells is `SiteConnected` iff its cell graph is connected** (forward direction:
the cells of nearest-neighbour sites are equal or adjacent). -/
theorem cellReach_of_siteConnected (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hXu : IsPiUnion m₀ j X) (hc : SiteConnected X)
    {b b' : CTorus d L N₁ m₁ K} (hb : b ∈ cellsIn m₀ j X) (hb' : b' ∈ cellsIn m₀ j X) :
    CellReach m₀ j X b b' := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hbal := (mem_cellsIn.1 hb).1
  have hbal' := (mem_cellsIn.1 hb').1
  have hbX := mem_of_mem_cellsIn hb
  have hb'X := mem_of_mem_cellsIn hb'
  have key : ∀ y, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ Nbr u v) b y →
      CellReach m₀ j X b (cbase (cellSide L m₀ m₁ j) y) := by
    intro y hy
    induction hy with
    | refl =>
      rw [cbase_eq_of_mem_box hdvd hbal (mem_box_self b ha0)]
      exact Relation.ReflTransGen.refl
    | @tail c y' _ hcy ih =>
      rcases cbase_nbr hdvd ha0 hcy.2.2 with h | h
      · rw [h]; exact ih
      · exact ih.tail ⟨h, cbase_mem_cellsIn hN hj hXu hcy.1, cbase_mem_cellsIn hN hj hXu hcy.2.1⟩
  have := key b' (hc b hbX b' hb'X)
  rwa [cbase_eq_of_mem_box hdvd hbal' (mem_box_self b' ha0)] at this

/-- `CellReach` between cells of `Z` gives nearest-neighbour reachability of the corners. -/
theorem siteReach_of_cellReach {Z : Set (CTorus d L N₁ m₁ K)} {b b' : CTorus d L N₁ m₁ K}
    (h : CellReach m₀ j Z b b') :
    Relation.ReflTransGen (fun u v => u ∈ Z ∧ v ∈ Z ∧ Nbr u v) b b' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.trans (siteReach_of_linked (R := Z) (ω := scaleW L m₀ m₁ j) (c := 1) ?_)
    exact linked_cell_adj (mem_cellsIn.1 hbc.2.1).2 (mem_cellsIn.1 hbc.2.2).2 hbc.1

/-- **A union of cells is `SiteConnected` iff its cell graph is connected.** -/
theorem siteConnected_iff_cellReach (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hXu : IsPiUnion m₀ j X) :
    SiteConnected X ↔ ∀ b ∈ cellsIn m₀ j X, ∀ b' ∈ cellsIn m₀ j X, CellReach m₀ j X b b' := by
  constructor
  · intro hc b hb b' hb'
    exact cellReach_of_siteConnected hN hj hXu hc hb hb'
  · intro h x hx y hy
    have toCorner : ∀ z ∈ X, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ Nbr u v)
        (cbase (cellSide L m₀ m₁ j) z) z := fun z hz =>
      siteReach_of_linked (linked_cell_corner (hXu.cell hN hj hz)
        (mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z))
    refine (rtg_symm (fun u v huv => ⟨huv.2.1, huv.1, huv.2.2.symm⟩) (toCorner x hx)).trans ?_
    exact (siteReach_of_cellReach (h _ (cbase_mem_cellsIn hN hj hXu hx) _
      (cbase_mem_cellsIn hN hj hXu hy))).trans (toCorner y hy)

omit [NeZero N₁] in
/-- **Spanning structure through the corners of a connected set of cells** (T2): if every cell
of the finite set `Q` lies in `R` and `Q` is connected through adjacent cells of `Q` from `v₀`,
the corners of `Q` lie in a connected structure inside `R` of cost at most `|Q| - 1`. -/
theorem cell_struct {R : Set (CTorus d L N₁ m₁ K)} (Q : Finset (CTorus d L N₁ m₁ K))
    (v₀ : CTorus d L N₁ m₁ K) (hv₀ : v₀ ∈ Q)
    (hQR : ∀ t ∈ Q, box t (cellSide L m₀ m₁ j) ⊆ R)
    (hreach : ∀ v ∈ Q, Relation.ReflTransGen
      (fun u v => CAdj (cellSide L m₀ m₁ j) u v ∧ u ∈ Q ∧ v ∈ Q) v₀ v) :
    Covers R (scaleW L m₀ m₁ j) ((Q.card : ℝ) - 1) Q := by
  classical
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have key := assemble (R := R) (ω := scaleW L m₀ m₁ j) (scaleW_nonneg (m₀ := m₀) (j := j)) Q
    (CAdj (cellSide L m₀ m₁ j)) v₀ hv₀ hreach (fun v => ({v} : Finset (CTorus d L N₁ m₁ K)))
    (fun _ => 0) ?_ 1 ?_
  · simp only [Finset.sum_const_zero, zero_add, mul_one] at key
    simpa using key
  · intro v hv
    refine ⟨{v}, ∅, connStruct_singleton v, ?_, subset_rfl, by simp [bondCost]⟩
    simpa using hQR v hv (mem_box_self v ha0)
  · intro u hu v hv huv
    exact ⟨u, by simp, v, by simp, linked_cell_adj (hQR u hu) (hQR v hv) huv⟩

/-- **Spanning structure of a cell-component** (T2): the corners of the cells of the
cell-component of `b` in `Z` lie in a connected structure inside the component of cost at most
`#cells - 1`. -/
theorem cellComp_struct {Z : Set (CTorus d L N₁ m₁ K)} {b : CTorus d L N₁ m₁ K}
    (hb : b ∈ cellsIn m₀ j Z) :
    Covers (cellComp m₀ j Z b) (scaleW L m₀ m₁ j)
      (((cellCompBases m₀ j Z b).card : ℝ) - 1) (cellCompBases m₀ j Z b) := by
  refine cell_struct _ b (mem_cellCompBases.2 ⟨hb, Relation.ReflTransGen.refl⟩)
    (fun t ht => box_subset_cellComp ht) ?_
  intro v hv
  obtain ⟨hvZ, hvr⟩ := mem_cellCompBases.1 hv
  have : ∀ y, CellReach m₀ j Z b y → Relation.ReflTransGen
      (fun u v => CAdj (cellSide L m₀ m₁ j) u v ∧ u ∈ cellCompBases m₀ j Z b ∧
        v ∈ cellCompBases m₀ j Z b) b y := by
    intro y hy
    induction hy with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c y' hr hcy ih =>
      refine ih.tail ⟨hcy.1, ?_, ?_⟩
      · exact mem_cellCompBases.2 ⟨CellReach.mem (m₀ := m₀) (j := j) hr hb, hr⟩
      · exact mem_cellCompBases.2 ⟨hcy.2.2, hr.tail hcy⟩
  exact this v hvr

end Comps

end Balaban.Fluctuation
