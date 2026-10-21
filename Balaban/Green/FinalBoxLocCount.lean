/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocSum
public import Balaban.Polymer.Animals

/-!
# The count of the rooted families of cells (A6-3, box localization, item (L4))

The coefficients of the rooted Lemma AE live on the families `C` of cells joined to the root `S`
of a term through overlapping patches.  A rooted family is the disjoint union of its components
(`compOf`), each a connected set of cells (an animal of the cell graph `cellGraph`, cells adjacent
when their patches meet) containing a cell whose patch meets `S`.  Assigning each component to its
least root cell (for a fixed enumeration of the cells) is injective, so for nonnegative weights
`w`:

  `∑_{C rooted at S} ∏_{i ∈ C} w_i ≤ ∏_{i : P i ∩ S ≠ ∅} (1 + ∑_{K ∋ i animal} ∏_{l ∈ K} w_l)`

(`sum_rooted_prod_le`).  With `w ≡ e^{-c}` and a degree bound `Δ` of the cell graph, the inner sums
are at most `η = ∑_{n ≥ 1} Δ^{2(n-1)} e^{-cn}` (`sum_animals_exp_le`, by `card_animals_le`).
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization

section Graph

variable {ι Ω : Type*} (P : ι → Set Ω)

/-- **The cell graph**: two distinct cells are adjacent when their patches meet. -/
def cellGraph : SimpleGraph ι := SimpleGraph.fromRel fun i j => (P i ∩ P j).Nonempty

theorem cellGraph_adj {i j : ι} (hij : i ≠ j) (h : (P i ∩ P j).Nonempty) :
    (cellGraph P).Adj i j :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨hij, Or.inl h⟩

end Graph

section Comp

variable {ι Ω : Type*} {P : ι → Set Ω}

theorem cellAdj_symm {C : Finset ι} {i j : ι} (h : CellAdj P C i j) : CellAdj P C j i :=
  ⟨h.2.1, h.1, by rw [Set.inter_comm]; exact h.2.2⟩

theorem reflTransGen_cellAdj_symm {C : Finset ι} {i j : ι}
    (h : Relation.ReflTransGen (CellAdj P C) i j) : Relation.ReflTransGen (CellAdj P C) j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (cellAdj_symm hbc) ih

open Classical in
/-- The component of the cell `i` in the family `C`: the cells of `C` joined to `i` through
overlapping patches of cells of `C`. -/
noncomputable def compOf (P : ι → Set Ω) (C : Finset ι) (i : ι) : Finset ι :=
  C.filter fun j => Relation.ReflTransGen (CellAdj P C) i j

theorem mem_compOf {C : Finset ι} {i j : ι} :
    j ∈ compOf P C i ↔ j ∈ C ∧ Relation.ReflTransGen (CellAdj P C) i j := by
  classical
  unfold compOf; exact Finset.mem_filter

theorem compOf_subset (C : Finset ι) (i : ι) : compOf P C i ⊆ C := fun _ h =>
  (mem_compOf.1 h).1

theorem self_mem_compOf {C : Finset ι} {i : ι} (hi : i ∈ C) : i ∈ compOf P C i :=
  mem_compOf.2 ⟨hi, Relation.ReflTransGen.refl⟩

theorem compOf_eq_of_mem {C : Finset ι} {i j : ι} (hj : j ∈ compOf P C i) :
    compOf P C j = compOf P C i := by
  obtain ⟨-, hij⟩ := mem_compOf.1 hj
  ext l
  simp only [mem_compOf]
  constructor
  · rintro ⟨hl, hjl⟩; exact ⟨hl, hij.trans hjl⟩
  · rintro ⟨hl, hil⟩; exact ⟨hl, (reflTransGen_cellAdj_symm hij).trans hil⟩

/-- Two components are equal or disjoint. -/
theorem compOf_eq_or_disjoint (C : Finset ι) (i j : ι) :
    compOf P C i = compOf P C j ∨ Disjoint (compOf P C i) (compOf P C j) := by
  by_cases h : Disjoint (compOf P C i) (compOf P C j)
  · exact Or.inr h
  · left
    obtain ⟨l, hli, hlj⟩ := Finset.not_disjoint_iff.1 h
    rw [← compOf_eq_of_mem hli, ← compOf_eq_of_mem hlj]

/-- **A component is an animal of the cell graph.** -/
theorem isAnimal_compOf {C : Finset ι} {i : ι} (hi : i ∈ C) :
    Polymer.IsAnimal (cellGraph P) (compOf P C i) := by
  rw [Polymer.isAnimal_iff]
  set K := compOf P C i with hK
  have hin : ∀ x, Relation.ReflTransGen (CellAdj P C) i x →
      Relation.ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ (cellGraph P).Adj a b) i x := by
    intro x h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hib hbc ih =>
      by_cases hbc' : b = c
      · subst hbc'; exact ih
      · refine ih.tail ⟨mem_compOf.2 ⟨hbc.1, hib⟩, mem_compOf.2 ⟨hbc.2.1, hib.tail hbc⟩,
          cellGraph_adj P hbc' hbc.2.2⟩
  have hsymm : ∀ a b, Relation.ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ (cellGraph P).Adj a b) a b →
      Relation.ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ (cellGraph P).Adj a b) b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih
  refine ⟨⟨i, self_mem_compOf hi⟩, fun x hx y hy => ?_⟩
  have hx' := hin x (mem_compOf.1 hx).2
  have hy' := hin y (mem_compOf.1 hy).2
  exact (hsymm _ _ hx').trans hy'

/-- **The component of a cell of a rooted family contains a root cell.** -/
theorem exists_root_mem_compOf {S : Set Ω} {C : Finset ι} (hC : IsRootedFamily P S C) {i : ι}
    (hi : i ∈ C) : ∃ l ∈ compOf P C i, (P l ∩ S).Nonempty := by
  obtain ⟨j, hj, hjS, hji⟩ := hC i hi
  exact ⟨j, mem_compOf.2 ⟨hj, reflTransGen_cellAdj_symm hji⟩, hjS⟩

end Comp

section Count

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Set Ω}

open Classical in
/-- The root cells of `S`: the cells whose patch meets `S`. -/
noncomputable def rootCells (P : ι → Set Ω) (S : Set Ω) : Finset ι :=
  Finset.univ.filter fun i => (P i ∩ S).Nonempty

omit [DecidableEq ι] in
theorem mem_rootCells {S : Set Ω} {i : ι} : i ∈ rootCells P S ↔ (P i ∩ S).Nonempty := by
  classical
  unfold rootCells; simp

open Classical in
/-- The animals of the cell graph containing the cell `i`. -/
noncomputable def animalsAt (P : ι → Set Ω) (i : ι) : Finset (Finset ι) :=
  Finset.univ.filter fun K => Polymer.IsAnimal (cellGraph P) K ∧ i ∈ K

theorem mem_animalsAt {i : ι} {K : Finset ι} :
    K ∈ animalsAt P i ↔ Polymer.IsAnimal (cellGraph P) K ∧ i ∈ K := by
  classical
  unfold animalsAt; simp

open Classical in
/-- The leader assignment of a rooted family: at a root cell `i`, the component of `i` if `i` is
the least root cell of its component (for the enumeration `Fintype.equivFin`), else `∅`. -/
noncomputable def leaderComp (P : ι → Set Ω) (S : Set Ω) (C : Finset ι) (i : ι) : Finset ι :=
  if i ∈ C ∧ ∀ l ∈ compOf P C i, (P l ∩ S).Nonempty →
      (Fintype.equivFin ι i : ℕ) ≤ (Fintype.equivFin ι l : ℕ) then compOf P C i else ∅

theorem leaderComp_subset (S : Set Ω) (C : Finset ι) (i : ι) : leaderComp P S C i ⊆ C := by
  classical
  unfold leaderComp
  split_ifs
  · exact compOf_subset C i
  · exact Finset.empty_subset _

/-- Every cell of a rooted family lies in the leader component of some root cell. -/
theorem exists_leaderComp_mem {S : Set Ω} {C : Finset ι} (hC : IsRootedFamily P S C) {c : ι}
    (hc : c ∈ C) : ∃ l ∈ rootCells P S, c ∈ leaderComp P S C l := by
  classical
  obtain ⟨l₀, hl₀, hl₀S⟩ := exists_root_mem_compOf hC hc
  have hne : ((compOf P C c).filter fun l => (P l ∩ S).Nonempty).Nonempty :=
    ⟨l₀, Finset.mem_filter.2 ⟨hl₀, hl₀S⟩⟩
  obtain ⟨l, hl, hmin⟩ := Finset.exists_min_image _ (fun l => (Fintype.equivFin ι l : ℕ)) hne
  obtain ⟨hlK, hlS⟩ := Finset.mem_filter.1 hl
  have hlC : l ∈ C := compOf_subset C c hlK
  have hKl : compOf P C l = compOf P C c := compOf_eq_of_mem hlK
  refine ⟨l, mem_rootCells.2 hlS, ?_⟩
  unfold leaderComp
  split_ifs with hcond
  · rw [hKl]; exact self_mem_compOf hc
  · exact absurd ⟨hlC, fun l' hl' hl'S => hmin l' (Finset.mem_filter.2 ⟨hKl ▸ hl', hl'S⟩)⟩ hcond

/-- **A rooted family is the union of its leader components.** -/
theorem biUnion_leaderComp {S : Set Ω} {C : Finset ι} (hC : IsRootedFamily P S C) :
    (rootCells P S).biUnion (leaderComp P S C) = C := by
  ext c
  constructor
  · intro h
    obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 h
    exact leaderComp_subset S C l hl
  · intro hc
    obtain ⟨l, hl, hcl⟩ := exists_leaderComp_mem hC hc
    exact Finset.mem_biUnion.2 ⟨l, hl, hcl⟩

/-- The leader components of distinct root cells are disjoint. -/
theorem disjoint_leaderComp (S : Set Ω) (C : Finset ι) {i j : ι} (hiS : (P i ∩ S).Nonempty)
    (hjS : (P j ∩ S).Nonempty) (hij : i ≠ j) :
    Disjoint (leaderComp P S C i) (leaderComp P S C j) := by
  classical
  unfold leaderComp
  split_ifs with hi hj
  · rcases compOf_eq_or_disjoint (P := P) C i j with h | h
    · exfalso
      have hjK : j ∈ compOf P C i := h ▸ self_mem_compOf hj.1
      have hiK : i ∈ compOf P C j := h ▸ self_mem_compOf hi.1
      have h1 := hi.2 j hjK hjS
      have h2 := hj.2 i hiK hiS
      exact hij ((Fintype.equivFin ι).injective (Fin.ext (le_antisymm h1 h2)))
    · exact h
  all_goals simp

/-- A leader component is empty or an animal containing its root cell. -/
theorem leaderComp_mem (S : Set Ω) (C : Finset ι) (i : ι) :
    leaderComp P S C i ∈ insert ∅ (animalsAt P i) := by
  classical
  unfold leaderComp
  split_ifs with h
  · exact Finset.mem_insert_of_mem (mem_animalsAt.2 ⟨isAnimal_compOf h.1, self_mem_compOf h.1⟩)
  · exact Finset.mem_insert_self _ _

theorem empty_not_mem_animalsAt (i : ι) : (∅ : Finset ι) ∉ animalsAt P i := fun h =>
  Finset.notMem_empty i (mem_animalsAt.1 h).2

open Classical in
/-- **The count of the rooted families**: for nonnegative weights,
`∑_{C rooted at S} ∏_{i ∈ C} w_i ≤ ∏_{i root cell} (1 + ∑_{K ∋ i animal} ∏_{l ∈ K} w_l)`. -/
theorem sum_rooted_prod_le (S : Set Ω) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C), ∏ c ∈ C, w c ≤
      ∏ i ∈ rootCells P S, (1 + ∑ K ∈ animalsAt P i, ∏ l ∈ K, w l) := by
  set R := rootCells P S with hR
  -- the leader assignment as a function on the root cells
  let Φ : Finset ι → (R → Finset ι) := fun C i => leaderComp P S C i.1
  have hprod : ∀ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C),
      ∏ c ∈ C, w c = ∏ i : R, ∏ l ∈ Φ C i, w l := by
    intro C hC
    have hCr := (Finset.mem_filter.1 hC).2
    conv_lhs => rw [← biUnion_leaderComp hCr]
    rw [Finset.prod_biUnion fun i hi j hj hij =>
      disjoint_leaderComp S C (mem_rootCells.1 hi) (mem_rootCells.1 hj) hij]
    exact (Finset.prod_coe_sort R fun i => ∏ l ∈ leaderComp P S C i, w l).symm
  have hinj : Set.InjOn Φ ↑(Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C)) := by
    intro C hC C' hC' h
    have h1 := biUnion_leaderComp (Finset.mem_filter.1 hC).2
    have h2 := biUnion_leaderComp (Finset.mem_filter.1 hC').2
    rw [← h1, ← h2]
    refine Finset.biUnion_congr rfl fun i hi => ?_
    exact congrFun h ⟨i, hi⟩
  have hsub : (Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C)).image Φ ⊆
      Fintype.piFinset fun i : R => insert ∅ (animalsAt P i.1) := by
    intro F hF
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hF
    exact Fintype.mem_piFinset.2 fun i => leaderComp_mem S C i.1
  calc ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C), ∏ c ∈ C, w c
      = ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C),
          ∏ i : R, ∏ l ∈ Φ C i, w l := Finset.sum_congr rfl hprod
    _ = ∑ F ∈ (Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C)).image Φ,
          ∏ i : R, ∏ l ∈ F i, w l :=
        (Finset.sum_image (f := fun F : R → Finset ι => ∏ i : R, ∏ l ∈ F i, w l) hinj).symm
    _ ≤ ∑ F ∈ Fintype.piFinset (fun i : R => insert ∅ (animalsAt P i.1)),
          ∏ i : R, ∏ l ∈ F i, w l :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun F _ _ =>
          Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun l _ => hw l
    _ = ∏ i : R, ∑ K ∈ insert ∅ (animalsAt P i.1), ∏ l ∈ K, w l :=
        (Finset.prod_univ_sum (fun i : R => insert ∅ (animalsAt P i.1))
          (fun _ K => ∏ l ∈ K, w l)).symm
    _ = ∏ i ∈ R, (1 + ∑ K ∈ animalsAt P i, ∏ l ∈ K, w l) := by
        rw [← Finset.prod_coe_sort R]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Finset.sum_insert (empty_not_mem_animalsAt i.1), Finset.prod_empty]

/-- A sum over a union of finsets is at most the sum of the sums, for nonnegative terms. -/
theorem sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β] {s : Finset β}
    {t : β → Finset α} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ b ∈ s, ∑ a ∈ t b, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hb]
    have h := Finset.sum_union_inter (s₁ := t b) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ a ∈ t b ∩ s.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
    linarith

open Classical in
/-- **The count of the rooted families through a cell, by leaders**: for nonnegative weights and a
cell `i₀`, `∑_{C rooted at S, i₀ ∈ C} ∏_C w` is at most the sum over the root cells `l` of
`(∑_{K ∋ i₀, l animal} ∏_K w) ∏_{i root} (1 + ∑_{K ∋ i} ∏_K w)`. -/
theorem sum_rooted_mem_prod_le_leaders (S : Set Ω) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i₀ : ι) :
    ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧ i₀ ∈ C), ∏ c ∈ C, w c ≤
      ∑ l ∈ rootCells P S, (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ m ∈ K, w m) *
        ∏ i ∈ rootCells P S, (1 + ∑ K ∈ animalsAt P i, ∏ l ∈ K, w l) := by
  set R := rootCells P S with hR
  set A : ι → ℝ := fun i => ∑ K ∈ animalsAt P i, ∏ l ∈ K, w l with hA
  have hA0 : ∀ i, 0 ≤ A i := fun i => Finset.sum_nonneg fun K _ => Finset.prod_nonneg fun l _ => hw l
  have hW0 : ∀ K : Finset ι, 0 ≤ ∏ l ∈ K, w l := fun K => Finset.prod_nonneg fun l _ => hw l
  let Φ : Finset ι → (R → Finset ι) := fun C i => leaderComp P S C i.1
  -- the families through `i₀` whose cell `i₀` lies in the leader component of `l`
  have hcover : Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧ i₀ ∈ C) ⊆
      R.biUnion fun l => Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
        i₀ ∈ leaderComp P S C l) := by
    intro C hC
    obtain ⟨hCr, hi₀⟩ := (Finset.mem_filter.1 hC).2
    obtain ⟨l, hl, hil⟩ := exists_leaderComp_mem hCr hi₀
    exact Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_filter.2 ⟨Finset.mem_univ _, hCr, hil⟩⟩
  have hfix : ∀ l ∈ R, ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
        i₀ ∈ leaderComp P S C l), ∏ c ∈ C, w c ≤
      (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ m ∈ K, w m) * ∏ i ∈ R, (1 + A i) := by
    intro l hl
    let t : R → Finset (Finset ι) := fun i =>
      if i.1 = l then (animalsAt P l).filter (fun K => i₀ ∈ K) else insert ∅ (animalsAt P i.1)
    have hprod : ∀ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
        i₀ ∈ leaderComp P S C l), ∏ c ∈ C, w c = ∏ i : R, ∏ m ∈ Φ C i, w m := by
      intro C hC
      have hCr := (Finset.mem_filter.1 hC).2.1
      conv_lhs => rw [← biUnion_leaderComp hCr]
      rw [Finset.prod_biUnion fun i hi j hj hij =>
        disjoint_leaderComp S C (mem_rootCells.1 hi) (mem_rootCells.1 hj) hij]
      exact (Finset.prod_coe_sort R fun i => ∏ m ∈ leaderComp P S C i, w m).symm
    have hinj : Set.InjOn Φ ↑(Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
        i₀ ∈ leaderComp P S C l)) := by
      intro C hC C' hC' h
      have h1 := biUnion_leaderComp (Finset.mem_filter.1 hC).2.1
      have h2 := biUnion_leaderComp (Finset.mem_filter.1 hC').2.1
      rw [← h1, ← h2]
      exact Finset.biUnion_congr rfl fun i hi => congrFun h ⟨i, hi⟩
    have hsub : (Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
        i₀ ∈ leaderComp P S C l)).image Φ ⊆ Fintype.piFinset t := by
      intro F hF
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hF
      refine Fintype.mem_piFinset.2 fun i => ?_
      show leaderComp P S C i.1 ∈ t i
      by_cases hil : i.1 = l
      · simp only [t, hil, ↓reduceIte]
        have hmem := leaderComp_mem (P := P) S C l
        have hin := (Finset.mem_filter.1 hC).2.2
        rcases Finset.mem_insert.1 hmem with h0 | h0
        · rw [h0] at hin; exact absurd hin (Finset.notMem_empty _)
        · exact Finset.mem_filter.2 ⟨h0, hin⟩
      · simp only [t, hil, ↓reduceIte]
        exact leaderComp_mem S C i.1
    have hl' : (⟨l, hl⟩ : R) ∈ (Finset.univ : Finset R) := Finset.mem_univ _
    calc ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
          i₀ ∈ leaderComp P S C l), ∏ c ∈ C, w c
        = ∑ F ∈ (Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
            i₀ ∈ leaderComp P S C l)).image Φ, ∏ i : R, ∏ m ∈ F i, w m := by
          rw [Finset.sum_congr rfl hprod]
          exact (Finset.sum_image (f := fun F : R → Finset ι => ∏ i : R, ∏ m ∈ F i, w m)
            hinj).symm
      _ ≤ ∑ F ∈ Fintype.piFinset t, ∏ i : R, ∏ m ∈ F i, w m :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun F _ _ =>
            Finset.prod_nonneg fun i _ => hW0 _
      _ = ∏ i : R, ∑ K ∈ t i, ∏ m ∈ K, w m :=
          (Finset.prod_univ_sum t (fun _ K => ∏ m ∈ K, w m)).symm
      _ = (∑ K ∈ t ⟨l, hl⟩, ∏ m ∈ K, w m) *
            ∏ i ∈ (Finset.univ : Finset R).erase ⟨l, hl⟩, ∑ K ∈ t i, ∏ m ∈ K, w m :=
          (Finset.mul_prod_erase _ _ hl').symm
      _ ≤ (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ m ∈ K, w m) *
            ∏ i : R, (1 + A i.1) := by
          have ht : t ⟨l, hl⟩ = (animalsAt P l).filter (fun K => i₀ ∈ K) := by simp [t]
          rw [ht]
          refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun K _ => hW0 K)
          have hrest : ∀ i ∈ (Finset.univ : Finset R).erase ⟨l, hl⟩,
              ∑ K ∈ t i, ∏ m ∈ K, w m = 1 + A i.1 := by
            intro i hi
            have hne : i.1 ≠ l := fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h)
            simp only [t, hne, ↓reduceIte]
            rw [Finset.sum_insert (empty_not_mem_animalsAt i.1), Finset.prod_empty]
          rw [Finset.prod_congr rfl hrest, ← Finset.mul_prod_erase _ (fun i : R => 1 + A i.1) hl']
          have h1 : (1 : ℝ) ≤ 1 + A l := by linarith [hA0 l]
          have h0 : 0 ≤ ∏ i ∈ (Finset.univ : Finset R).erase ⟨l, hl⟩, (1 + A i.1) :=
            Finset.prod_nonneg fun i _ => by linarith [hA0 i.1]
          nlinarith
      _ = (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ m ∈ K, w m) *
            ∏ i ∈ R, (1 + A i) := by
          rw [← Finset.prod_coe_sort R (fun i => 1 + A i)]
  calc ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧ i₀ ∈ C), ∏ c ∈ C, w c
      ≤ ∑ C ∈ R.biUnion (fun l => Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
          i₀ ∈ leaderComp P S C l)), ∏ c ∈ C, w c :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun C _ _ => hW0 C
    _ ≤ ∑ l ∈ R, ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧
          i₀ ∈ leaderComp P S C l), ∏ c ∈ C, w c :=
        sum_biUnion_le_of_nonneg fun C => hW0 C
    _ ≤ ∑ l ∈ R, (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ m ∈ K, w m) *
          ∏ i ∈ R, (1 + A i) := Finset.sum_le_sum hfix

open Classical in
/-- **The count of the rooted families through a cell**: for nonnegative weights and a cell `i₀`,
`∑_{C rooted at S, i₀ ∈ C} ∏_{C} w ≤ (∑_{K ∋ i₀ animal} |K| ∏_K w) ∏_{i root} (1 + ∑_{K ∋ i} ∏_K w)`. -/
theorem sum_rooted_mem_prod_le (S : Set Ω) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i₀ : ι) :
    ∑ C ∈ Finset.univ.filter (fun C : Finset ι => IsRootedFamily P S C ∧ i₀ ∈ C), ∏ c ∈ C, w c ≤
      (∑ K ∈ animalsAt P i₀, (K.card : ℝ) * ∏ l ∈ K, w l) *
        ∏ i ∈ rootCells P S, (1 + ∑ K ∈ animalsAt P i, ∏ l ∈ K, w l) := by
  set R := rootCells P S with hR
  have hW0 : ∀ K : Finset ι, 0 ≤ ∏ l ∈ K, w l := fun K => Finset.prod_nonneg fun l _ => hw l
  have hA0 : ∀ i, 0 ≤ ∑ K ∈ animalsAt P i, ∏ l ∈ K, w l := fun i =>
    Finset.sum_nonneg fun K _ => hW0 K
  have hswap : ∑ l ∈ R, ∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ m ∈ K, w m ≤
      ∑ K ∈ animalsAt P i₀, (K.card : ℝ) * ∏ m ∈ K, w m := by
    have e : ∀ l, (animalsAt P l).filter (fun K => i₀ ∈ K) =
        (animalsAt P i₀).filter (fun K => l ∈ K) := by
      intro l; ext K; simp only [Finset.mem_filter, mem_animalsAt]; tauto
    simp only [e]
    rw [Finset.sum_comm' (t' := animalsAt P i₀) (s' := fun K => R.filter (fun l => l ∈ K))]
    · refine Finset.sum_le_sum fun K _ => ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (hW0 K)
      exact_mod_cast Finset.card_le_card fun l hl => (Finset.mem_filter.1 hl).2
    · intro l K
      simp only [Finset.mem_filter]
      tauto
  refine (sum_rooted_mem_prod_le_leaders S w hw i₀).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hswap (Finset.prod_nonneg fun i _ => by linarith [hA0 i])

open Classical in
/-- **The animal sum at a cell**: with a degree bound `Δ` of the cell graph,
`∑_{K ∋ i animal} e^{-c|K|} ≤ ∑_{n < |ι|} Δ^{2n} e^{-c(n+1)}` (`card_animals_le`). -/
theorem sum_animalsAt_exp_le {Δ : ℕ} (hΔ : ∀ v, (cellGraph P).degree v ≤ Δ) (c : ℝ) (i : ι) :
    ∑ K ∈ animalsAt P i, Real.exp (-c * K.card) ≤
      ∑ n ∈ Finset.range (Fintype.card ι), (Δ : ℝ) ^ (2 * n) * Real.exp (-c * (n + 1)) := by
  have hmaps : ∀ K ∈ animalsAt P i, K.card - 1 ∈ Finset.range (Fintype.card ι) := by
    intro K hK
    have hpos : 0 < K.card := Finset.card_pos.2 ⟨i, (mem_animalsAt.1 hK).2⟩
    have hle : K.card ≤ Fintype.card ι := Finset.card_le_univ _
    rw [Finset.mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun n _ => ?_
  have hcard : ((animalsAt P i).filter fun K => K.card - 1 = n).card ≤ Δ ^ (2 * n) := by
    calc _ ≤ (Polymer.animals (cellGraph P) i (n + 1)).card := by
          refine Finset.card_le_card fun K hK => ?_
          obtain ⟨hK1, hK2⟩ := Finset.mem_filter.1 hK
          obtain ⟨hA, hiK⟩ := mem_animalsAt.1 hK1
          have hpos : 0 < K.card := Finset.card_pos.2 ⟨i, hiK⟩
          exact (Polymer.mem_animals _).2 ⟨hiK, by omega, hA.2⟩
      _ ≤ Δ ^ (2 * (n + 1 - 1)) := Polymer.card_animals_le _ hΔ i (n + 1)
      _ = Δ ^ (2 * n) := by simp
  have hterm : ∀ K ∈ (animalsAt P i).filter fun K => K.card - 1 = n,
      Real.exp (-c * K.card) = Real.exp (-c * (n + 1)) := by
    intro K hK
    obtain ⟨hK1, hK2⟩ := Finset.mem_filter.1 hK
    have hpos : 0 < K.card := Finset.card_pos.2 ⟨i, (mem_animalsAt.1 hK1).2⟩
    have : (K.card : ℝ) = n + 1 := by
      have : K.card = n + 1 := by omega
      exact_mod_cast this
    rw [this]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le

/-- The geometric bound: for `Δ² e^{-c} < 1`,
`∑_{n < m} Δ^{2n} e^{-c(n+1)} ≤ e^{-c} / (1 - Δ² e^{-c})`. -/
theorem sum_range_pow_exp_le {Δ : ℕ} {c : ℝ} (hq : (Δ : ℝ) ^ 2 * Real.exp (-c) < 1) (m : ℕ) :
    ∑ n ∈ Finset.range m, (Δ : ℝ) ^ (2 * n) * Real.exp (-c * (n + 1)) ≤
      Real.exp (-c) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-c)) := by
  set q := (Δ : ℝ) ^ 2 * Real.exp (-c) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have e : ∀ n : ℕ, (Δ : ℝ) ^ (2 * n) * Real.exp (-c * (n + 1)) = Real.exp (-c) * q ^ n := by
    intro n
    rw [hqdef, mul_pow, ← pow_mul, ← Real.exp_nat_mul, ← mul_assoc, mul_comm (Real.exp (-c)),
      mul_assoc, ← Real.exp_add]
    congr 2; ring
  simp only [e, ← Finset.mul_sum]
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hq0 hq
  simpa using this

end Count

end Balaban.Green
