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

section Extend

variable {m₀ j : ℕ}

/-- The nerve of the extension: the node `none` is the old structure, the node `some q` is the
corner of the newly active cell with base `q`.  The old structure is joined to `q` when
`P q` (some old vertex is linked to `q`, at the cost allowed for one link); two newly active
cells are joined when they are adjacent. -/
def nerveH (a : ℕ) (P : CTorus d L N₁ m₁ K → Prop) :
    Option (CTorus d L N₁ m₁ K) → Option (CTorus d L N₁ m₁ K) → Prop
  | none, some q => P q
  | some q, some q' => CAdj a q q'
  | _, _ => False

/-- **T3: the extension of an admissible triple to a larger region.**  Let `Ωm ⊆ Ωp` be unions
of cells, `X ∈ 𝒟_j`, and suppose every cell-component of `X ∩ Ωmᶜ` is contained in `Ωp` or
disjoint from `Ωp` (so that a newly active component is never enclosed, inside `X`, by cells
that stay inactive).  Then every admissible triple `(𝒦, W, E)` for `(Ωm, X)` extends to an
admissible triple for `(Ωp, X)` whose cost exceeds that of `E` by at most
`(d L + d + 3) · #cells(X ∩ (Ωp ∖ Ωm))`; the proof gives `(d L + 1) · #cells`. -/
theorem modAdmissible_extend (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X Ωm Ωp 𝒦 : Set (CTorus d L N₁ m₁ K)} {W : Finset (CTorus d L N₁ m₁ K)}
    {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ j X) (hΩm : IsPiUnion m₀ j Ωm) (hΩp : IsPiUnion m₀ j Ωp)
    (hsplit : ∀ Q ∈ cellComps m₀ j (X ∩ Ωmᶜ), Q ⊆ Ωp ∨ Disjoint Q Ωp)
    (h : ModAdmissible m₀ j Ωm X 𝒦 W E) :
    ∃ (𝒦' : Set (CTorus d L N₁ m₁ K)) (W' : Finset (CTorus d L N₁ m₁ K))
      (E' : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ModAdmissible m₀ j Ωp X 𝒦' W' E' ∧
        bondCost (scaleW L m₀ m₁ j) E' ≤ bondCost (scaleW L m₀ m₁ j) E +
          ((d : ℝ) * L + d + 3) * ((cellsIn m₀ j (X ∩ (Ωp \ Ωm))).card : ℝ) := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  obtain ⟨hXne, hXp, hXc⟩ := hX
  have hXu : IsPiUnion m₀ j X := hXp.isPiUnion hN hj
  have hcΩm : IsPiUnion m₀ j Ωmᶜ := hΩm.compl hN hj
  obtain ⟨hK1, hcov, hconn, hWX, hmeet⟩ := h
  set a := cellSide L m₀ m₁ j with ha
  set ρ : ℝ := (d : ℝ) * L + 1 with hρ
  have hdL : (0 : ℝ) ≤ (d : ℝ) * L := by positivity
  set A := cellsIn m₀ j (X ∩ (Ωp \ Ωm)) with hA
  have memA : ∀ t, t ∈ A ↔ t ∈ cellsIn m₀ j X ∧ box t a ⊆ Ωp ∧ box t a ⊆ Ωmᶜ := by
    intro t
    simp only [hA, mem_cellsIn, Set.subset_inter_iff, Set.sdiff_eq]
    tauto
  have memC : ∀ t, t ∈ cellsIn m₀ j X → box t a ⊆ Ωmᶜ → t ∈ cellsIn m₀ j (X ∩ Ωmᶜ) := by
    intro t ht htc
    exact mem_cellsIn.2 ⟨(mem_cellsIn.1 ht).1, Set.subset_inter (mem_cellsIn.1 ht).2 htc⟩
  have hs : ∀ c c', c ∈ cellsIn m₀ j (X ∩ Ωmᶜ) → c' ∈ cellsIn m₀ j (X ∩ Ωmᶜ) →
      CAdj a c c' → box c a ⊆ Ωp → box c' a ⊆ Ωp := by
    intro c c' hc hc' hadj hcΩ
    rcases hsplit (cellComp m₀ j (X ∩ Ωmᶜ) c) ⟨c, hc, rfl⟩ with h1 | h1
    · refine (box_subset_cellComp (b := c) (t := c') ?_).trans h1
      exact mem_cellCompBases.2 ⟨hc',
        (Relation.ReflTransGen.single ⟨hadj, hc, hc'⟩ : CellReach m₀ j (X ∩ Ωmᶜ) c c')⟩
    · exfalso
      have hcm : c ∈ cellComp m₀ j (X ∩ Ωmᶜ) c := mem_box_cellComp hc (mem_box_self c ha0)
      exact Set.disjoint_left.1 h1 hcm (hcΩ (mem_box_self c ha0))
  have dich : ∀ t ∈ cellsIn m₀ j X, box t a ⊆ Ωm ∨ box t a ⊆ Ωmᶜ := fun t ht =>
    cell_dichotomy hN hj hΩm (mem_cellsIn.1 ht).1
  have hbx : ∀ q, ∃ b, q ∈ X → (Aligned a b ∧ q ∈ box b (L * a) ∧ box b (L * a) ⊆ X) := by
    intro q
    by_cases hq : q ∈ X
    · obtain ⟨b, hb⟩ := hXp q hq
      exact ⟨b, fun _ => hb⟩
    · exact ⟨q, fun h => absurd h hq⟩
  choose bx hbx using hbx
  obtain ⟨P, hP⟩ : ∃ P : CTorus d L N₁ m₁ K → Prop,
      ∀ q, P q ↔ ∃ w ∈ W, Linked X (scaleW L m₀ m₁ j) ρ w q := ⟨_, fun _ => Iff.rfl⟩
  have oldLink : ∀ p ∈ cellsIn m₀ j (X ∩ Ωm), ∀ q ∈ cellsIn m₀ j X, CAdj a p q → P q := by
    intro p hp q hq hadj
    have hpm := mem_cellsIn.1 hp
    have hpX : p ∈ X ∩ Ωm := hpm.2 (mem_box_self p ha0)
    obtain ⟨b₀, hb₀, hpb⟩ := Set.mem_iUnion₂.1 (hcov hpX)
    obtain ⟨w, hwW, hwb⟩ := hmeet b₀ hb₀
    have h1 := linked_box_site_corner (R := X) b₀ (hK1 b₀ hb₀).2 hwb hpb
    have h2 : Linked X (scaleW L m₀ m₁ j) 1 p q :=
      linked_cell_adj (hpm.2.trans Set.inter_subset_left) (mem_cellsIn.1 hq).2 hadj
    refine (hP q).2 ⟨w, hwW, ?_⟩
    exact Covers.mono_c (Linked.trans (scaleW_nonneg (m₀ := m₀) (j := j)) h1 h2) (le_of_eq rfl)
  obtain ⟨S, hS⟩ : ∃ S : Finset (Option (CTorus d L N₁ m₁ K)), S = insert none (A.image some) :=
    ⟨_, rfl⟩
  have hSnone : (none : Option (CTorus d L N₁ m₁ K)) ∈ S := by rw [hS]; simp
  have hSsome : ∀ q, some q ∈ S ↔ q ∈ A := by intro q; rw [hS]; simp
  have hcard : S.card = A.card + 1 := by
    rw [hS, Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective _)]
  have hsum : (∑ v ∈ S, (Option.elim v (bondCost (scaleW L m₀ m₁ j) E) (fun _ => (0 : ℝ)))) =
      bondCost (scaleW L m₀ m₁ j) E := by
    rw [hS, Finset.sum_insert (by simp), Finset.sum_image (fun x _ y _ h => Option.some.inj h)]
    simp
  have reach : ∀ q ∈ A, Relation.ReflTransGen (fun u v => nerveH a P u v ∧ u ∈ S ∧ v ∈ S)
      none (some q) := by
    intro q hq
    have hqm := (memA q).1 hq
    by_cases hold : ∃ z ∈ X, z ∈ Ωm
    · obtain ⟨z, hzX, hzΩ⟩ := hold
      have ht₀ : cbase a z ∈ cellsIn m₀ j X := cbase_mem_cellsIn hN hj hXu hzX
      have ht₀Ω : box (cbase a z) a ⊆ Ωm := hΩm.cell hN hj hzΩ
      have hpath : CellReach m₀ j X q (cbase a z) :=
        cellReach_of_siteConnected hN hj hXu hXc hqm.1 ht₀
      have F : ∀ c, CellReach m₀ j X c (cbase a z) → box c a ⊆ Ωp →
          box c a ⊆ Ωm ∨ Relation.ReflTransGen (fun u v => nerveH a P u v ∧ u ∈ S ∧ v ∈ S)
            none (some c) := by
        intro c hc
        induction hc using Relation.ReflTransGen.head_induction_on with
        | refl => intro _; exact Or.inl ht₀Ω
        | @head c c' hcc' hrest ih =>
          intro hcΩ
          rcases dich c hcc'.2.1 with hco | hcc
          · exact Or.inl hco
          · right
            have hcA : c ∈ A := (memA c).2 ⟨hcc'.2.1, hcΩ, hcc⟩
            have hSc : some c ∈ S := (hSsome c).2 hcA
            rcases dich c' hcc'.2.2 with hc'o | hc'c
            · have hc'old : c' ∈ cellsIn m₀ j (X ∩ Ωm) :=
                mem_cellsIn.2 ⟨(mem_cellsIn.1 hcc'.2.2).1,
                  Set.subset_inter (mem_cellsIn.1 hcc'.2.2).2 hc'o⟩
              exact Relation.ReflTransGen.single
                ⟨oldLink c' hc'old c hcc'.2.1 (CAdj.symm hcc'.1), hSnone, hSc⟩
            · have hc'Ω := hs c c' (memC c hcc'.2.1 hcc) (memC c' hcc'.2.2 hc'c) hcc'.1 hcΩ
              rcases ih hc'Ω with h1 | h1
              · exact absurd (h1 (mem_box_self c' ha0)) (hc'c (mem_box_self c' ha0))
              · have hc'A : c' ∈ A := (memA c').2 ⟨hcc'.2.2, hc'Ω, hc'c⟩
                exact h1.tail ⟨(CAdj.symm hcc'.1), (hSsome c').2 hc'A, hSc⟩
      rcases F q hpath hqm.2.1 with h1 | h1
      · exact absurd (h1 (mem_box_self q ha0)) (hqm.2.2 (mem_box_self q ha0))
      · exact h1
    · push Not at hold
      have hnotΩ : ∀ c ∈ cellsIn m₀ j X, box c a ⊆ Ωmᶜ := fun c hc x hx hxΩ =>
        hold x ((mem_cellsIn.1 hc).2 hx) hxΩ
      have hall : ∀ c ∈ cellsIn m₀ j X, c ∈ A := by
        intro c hc
        have hrq : CellReach m₀ j X q c := cellReach_of_siteConnected hN hj hXu hXc hqm.1 hc
        have key : ∀ c', CellReach m₀ j X q c' → box c' a ⊆ Ωp := by
          intro c' hc'
          induction hc' with
          | refl => exact hqm.2.1
          | @tail u v _ huv ih =>
            exact hs u v (memC u huv.2.1 (hnotΩ u huv.2.1)) (memC v huv.2.2 (hnotΩ v huv.2.2))
              huv.1 ih
        exact (memA c).2 ⟨hc, key c hrq, hnotΩ c hc⟩
      obtain ⟨w₀, hw₀⟩ := hconn.1
      have hw₀X : w₀ ∈ X := hWX (Finset.mem_coe.2 hw₀)
      have ht₀ : cbase a w₀ ∈ cellsIn m₀ j X := cbase_mem_cellsIn hN hj hXu hw₀X
      have hdρ : (d : ℝ) ≤ ρ := by
        rw [hρ]
        nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
      have hlink : P (cbase a w₀) :=
        (hP _).2 ⟨w₀, hw₀, Covers.mono_c (Linked.symm (linked_cell_corner (hXu.cell hN hj hw₀X)
          (mem_box_cbase ha0 w₀))) hdρ⟩
      have hr : CellReach m₀ j X (cbase a w₀) q :=
        cellReach_of_siteConnected hN hj hXu hXc ht₀ hqm.1
      have hsome : Relation.ReflTransGen (fun u v => nerveH a P u v ∧ u ∈ S ∧ v ∈ S)
          (some (cbase a w₀)) (some q) := by
        have gen : ∀ y, CellReach m₀ j X (cbase a w₀) y →
            Relation.ReflTransGen (fun u v => nerveH a P u v ∧ u ∈ S ∧ v ∈ S)
              (some (cbase a w₀)) (some y) := by
          intro y hy
          induction hy with
          | refl => exact Relation.ReflTransGen.refl
          | @tail u v _ huv ih =>
            exact ih.tail ⟨huv.1, (hSsome u).2 (hall u huv.2.1), (hSsome v).2 (hall v huv.2.2)⟩
        exact gen q hr
      exact (Relation.ReflTransGen.single
        ⟨hlink, hSnone, (hSsome _).2 (hall _ ht₀)⟩).trans hsome
  have key := assemble (R := X) (ω := scaleW L m₀ m₁ j)
    (scaleW_nonneg (m₀ := m₀) (j := j)) S (nerveH a P) none hSnone
    (fun v hv => by
      rcases v with _ | q
      · exact Relation.ReflTransGen.refl
      · exact reach q ((hSsome q).1 hv))
    (fun v => Option.elim v W (fun q => ({q} : Finset (CTorus d L N₁ m₁ K))))
    (fun v => Option.elim v (bondCost (scaleW L m₀ m₁ j) E) (fun _ => (0 : ℝ)))
    (fun v hv => by
      rcases v with _ | q
      · exact ⟨W, E, hconn, hWX, subset_rfl, le_rfl⟩
      · have hqX : q ∈ X := mem_of_mem_cellsIn ((memA q).1 ((hSsome q).1 hv)).1
        exact ⟨{q}, ∅, connStruct_singleton q, by simpa using hqX, subset_rfl, by simp [bondCost]⟩)
    ρ
    (fun u hu v hv huv => by
      rcases u with _ | p <;> rcases v with _ | q
      · exact huv.elim
      · obtain ⟨w, hw, hl⟩ := (hP q).1 huv
        exact ⟨w, hw, q, Finset.mem_singleton_self q, hl⟩
      · exact huv.elim
      · have hp := (memA p).1 ((hSsome p).1 hu)
        have hq := (memA q).1 ((hSsome q).1 hv)
        exact ⟨p, Finset.mem_singleton_self p, q, Finset.mem_singleton_self q,
          Covers.mono_c (linked_cell_adj (mem_cellsIn.1 hp.1).2 (mem_cellsIn.1 hq.1).2 huv)
            (by rw [hρ]; linarith)⟩)
  obtain ⟨W', E', hc', hW'X, hsubW, hcost⟩ := key
  rw [hsum, hcard] at hcost
  refine ⟨𝒦 ∪ bx '' (A : Set (CTorus d L N₁ m₁ K)), W', E', ⟨?_, ?_, hc', hW'X, ?_⟩, ?_⟩
  · rintro b (hb | ⟨q, hq, rfl⟩)
    · exact hK1 b hb
    · have hqX : q ∈ X := mem_of_mem_cellsIn ((memA q).1 (Finset.mem_coe.1 hq)).1
      exact ⟨(hbx q hqX).1, (hbx q hqX).2.2⟩
  · rintro z ⟨hzX, hzΩ⟩
    by_cases hz : z ∈ Ωm
    · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov ⟨hzX, hz⟩)
      exact Set.mem_iUnion₂.2 ⟨b, Or.inl hb, hzb⟩
    · have htA : cbase a z ∈ A := (memA _).2 ⟨cbase_mem_cellsIn hN hj hXu hzX,
        hΩp.cell hN hj hzΩ, hcΩm.cell hN hj hz⟩
      have htX : cbase a z ∈ X := mem_of_mem_cellsIn ((memA _).1 htA).1
      obtain ⟨hbal, htb, -⟩ := hbx _ htX
      have e : cbase a (cbase a z) = cbase a z :=
        cbase_eq_of_mem_box hdvd (aligned_cbase z) (mem_box_self _ ha0)
      have := cell_subset_cube hdvd ha0 hbal htb
      rw [e] at this
      exact Set.mem_iUnion₂.2 ⟨bx (cbase a z), Or.inr ⟨_, Finset.mem_coe.2 htA, rfl⟩,
        this (mem_box_cbase ha0 z)⟩
  · rintro b (hb | ⟨q, hq, rfl⟩)
    · obtain ⟨x, hx, hxb⟩ := hmeet b hb
      exact ⟨x, hsubW (Finset.mem_biUnion.2 ⟨none, hSnone, hx⟩), hxb⟩
    · have hqX : q ∈ X := mem_of_mem_cellsIn ((memA q).1 (Finset.mem_coe.1 hq)).1
      exact ⟨q, hsubW (Finset.mem_biUnion.2 ⟨some q, (hSsome q).2 (Finset.mem_coe.1 hq),
        Finset.mem_singleton_self q⟩), (hbx q hqX).2.1⟩
  · have hn : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    push_cast at hcost
    rw [hρ] at hcost
    nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hn]

/-- **T4: the modular size grows by at most a constant times the number of newly active cells.**
For `X ∈ 𝒟_j`, unions of cells `Ω₋`, `Ω₊`, and the component hypothesis `hsplit` of
`modAdmissible_extend`:
`dcovMod(Ω₊, X) ≤ dcovMod(Ω₋, X) + (d L + d + 3) · #cells(X ∩ (Ω₊ ∖ Ω₋))`.  (Monotonicity
`Ω₋ ⊆ Ω₊` is not used; for `Ω₋ ⊆ Ω₊` it gives the two-sided control of the growth.) -/
theorem dcovMod_le_add_of_region_grow (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X Ωm Ωp : Set (CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ j X) (hΩm : IsPiUnion m₀ j Ωm) (hΩp : IsPiUnion m₀ j Ωp)
    (hsplit : ∀ Q ∈ cellComps m₀ j (X ∩ Ωmᶜ), Q ⊆ Ωp ∨ Disjoint Q Ωp) :
    dcovMod m₀ j Ωp X ≤ dcovMod m₀ j Ωm X +
      ((d : ℝ) * L + d + 3) * ((cellsIn m₀ j (X ∩ (Ωp \ Ωm))).card : ℝ) := by
  obtain ⟨𝒦, W, E, hadm, hE⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj
    (m₀ := m₀) (j := j) (Ω := Ωm) hX)
  obtain ⟨𝒦', W', E', hadm', hcost⟩ := modAdmissible_extend hN hj hX hΩm hΩp hsplit hadm
  rw [← hE]
  exact (dcovMod_le_of_admissible hadm').trans hcost

/-- The `ENNReal` form of `dcovMod_le_add_of_region_grow`, for `dcovModE`. -/
theorem dcovModE_le_add_of_region_grow (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {X Ωm Ωp : Set (CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ j X) (hΩm : IsPiUnion m₀ j Ωm) (hΩp : IsPiUnion m₀ j Ωp)
    (hsplit : ∀ Q ∈ cellComps m₀ j (X ∩ Ωmᶜ), Q ⊆ Ωp ∨ Disjoint Q Ωp) :
    dcovModE m₀ j Ωp X ≤ dcovModE m₀ j Ωm X +
      ENNReal.ofReal (((d : ℝ) * L + d + 3) * ((cellsIn m₀ j (X ∩ (Ωp \ Ωm))).card : ℝ)) := by
  obtain ⟨𝒦, W, E, hadm, hE⟩ := exists_admissible_eq_dcovModE (exists_admissible_of_IsDj
    (m₀ := m₀) (j := j) (Ω := Ωm) hX)
  obtain ⟨𝒦', W', E', hadm', hcost⟩ := modAdmissible_extend hN hj hX hΩm hΩp hsplit hadm
  rw [← hE]
  refine (dcovModE_le_of_admissible hadm').trans ?_
  rw [← ENNReal.ofReal_add (bondCost_scaleW_nonneg E) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hcost

end Extend

end Balaban.Fluctuation
