module

public import Balaban.Polymer.Sized

/-!
# Decomposition of a sum over families into a polymer gas

Let `E` be a finite set of elementary objects with charged supports `cs : E → Finset B`; two objects
are in contact when their supports meet.  For a family `D ⊆ E` its components are the classes of
the reachability relation inside `D`.  If an admissibility predicate `A` on families is local (a
family is admissible iff each of its components is), then
`∑_{D admissible} ∏_{t ∈ D} w t = Ξ(K)`, the partition function of the polymer gas whose polymers
are the nonempty block sets `Y` and whose activity is the sum, over the admissible connected
families with union `Y`, of the products of the weights (`decomposition`).  This is the
combinatorial core of the Mayer layer (POLYMER.md §3.7 (i)) and of GAS (§3.9).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Reach

variable {E B : Type*} (cs : E → Finset B)

/-- Two objects are in contact when their charged supports meet. -/
def Contact (a b : E) : Prop := ¬ Disjoint (cs a) (cs b)

theorem Contact.symm {a b : E} (h : Contact cs a b) : Contact cs b a := fun hd => h hd.symm

/-- Reachability inside the family `D` through chains of contacts. -/
def Reach (D : Finset E) (a b : E) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ D ∧ y ∈ D ∧ Contact cs x y) a b

theorem Reach.refl (D : Finset E) (a : E) : Reach cs D a a := Relation.ReflTransGen.refl

theorem Reach.trans {D : Finset E} {a b c : E} (h : Reach cs D a b) (h' : Reach cs D b c) :
    Reach cs D a c := Relation.ReflTransGen.trans h h'

theorem Reach.single {D : Finset E} {a b : E} (ha : a ∈ D) (hb : b ∈ D) (h : Contact cs a b) :
    Reach cs D a b := Relation.ReflTransGen.single ⟨ha, hb, h⟩

theorem Reach.symm {D : Finset E} {a b : E} (h : Reach cs D a b) : Reach cs D b a := by
  induction h with
  | refl => exact Reach.refl cs _ _
  | tail _ hbc ih =>
    exact (Reach.single cs hbc.2.1 hbc.1 (hbc.2.2.symm cs)).trans cs ih

theorem Reach.mono {D D' : Finset E} (hD : D ⊆ D') {a b : E} (h : Reach cs D a b) :
    Reach cs D' a b := by
  induction h with
  | refl => exact Reach.refl cs _ _
  | tail _ hbc ih => exact ih.trans cs (Reach.single cs (hD hbc.1) (hD hbc.2.1) hbc.2.2)

/-- A family closed under contacts with the ambient family `D` is a union of classes. -/
theorem reach_stays {D D' : Finset E} (hcl : ∀ x ∈ D', ∀ y ∈ D, Contact cs x y → y ∈ D')
    {a b : E} (ha : a ∈ D') (h : Reach cs D a b) : b ∈ D' ∧ Reach cs D' a b := by
  induction h with
  | refl => exact ⟨ha, Reach.refl cs _ _⟩
  | tail _ hbc ih =>
    have hc : _ ∈ D' := hcl _ ih.1 _ hbc.2.1 hbc.2.2
    exact ⟨hc, ih.2.trans cs (Reach.single cs ih.1 hc hbc.2.2)⟩


variable {cs}

/-- The component of `t` in `D`. -/
def comp (cs : E → Finset B) (D : Finset E) (t : E) : Finset E := D.filter (fun s => Reach cs D t s)

/-- The union of the charged supports of a family. -/
def unionCs (cs : E → Finset B) (D : Finset E) : Finset B := D.biUnion cs

/-- A nonempty family connected through contacts. -/
def ConnSet (cs : E → Finset B) (D : Finset E) : Prop := D.Nonempty ∧ ∀ s ∈ D, ∀ s' ∈ D, Reach cs D s s'

/-- The members of `D` supported inside `Y`. -/
def rs (cs : E → Finset B) (D : Finset E) (Y : Finset B) : Finset E := D.filter (fun t => cs t ⊆ Y)

theorem mem_comp {D : Finset E} {t s : E} : s ∈ comp cs D t ↔ s ∈ D ∧ Reach cs D t s := by
  simp [comp]

theorem mem_unionCs {D : Finset E} {b : B} : b ∈ unionCs cs D ↔ ∃ t ∈ D, b ∈ cs t := by
  simp [unionCs]

theorem mem_rs {D : Finset E} {Y : Finset B} {t : E} : t ∈ rs cs D Y ↔ t ∈ D ∧ cs t ⊆ Y := by
  simp [rs]

theorem self_mem_comp {D : Finset E} {t : E} (ht : t ∈ D) : t ∈ comp cs D t :=
  mem_comp.mpr ⟨ht, Reach.refl cs _ _⟩

theorem comp_subset (D : Finset E) (t : E) : comp cs D t ⊆ D := Finset.filter_subset _ _

theorem comp_closed {D : Finset E} {t : E} {x y : E} (hx : x ∈ comp cs D t) (hy : y ∈ D)
    (hxy : Contact cs x y) : y ∈ comp cs D t := by
  rw [mem_comp] at hx ⊢
  exact ⟨hy, hx.2.trans cs (Reach.single cs hx.1 hy hxy)⟩

theorem connSet_comp {D : Finset E} {t : E} (ht : t ∈ D) : ConnSet cs (comp cs D t) := by
  refine ⟨⟨t, self_mem_comp ht⟩, fun s hs s' hs' => ?_⟩
  rw [mem_comp] at hs hs'
  have h : Reach cs D s s' := hs.2.symm.trans cs hs'.2
  exact (reach_stays cs (D' := comp cs D t)
    (fun x hx y hy hxy => comp_closed hx hy hxy) (mem_comp.mpr hs) h).2

theorem comp_eq_of_mem {D : Finset E} {t t' : E} (h : t' ∈ comp cs D t) :
    comp cs D t' = comp cs D t := by
  rw [mem_comp] at h
  ext s
  rw [mem_comp, mem_comp]
  constructor
  · exact fun hs => ⟨hs.1, h.2.trans cs hs.2⟩
  · exact fun hs => ⟨hs.1, h.2.symm.trans cs hs.2⟩

end Reach


section Fiber

variable {E B : Type*} [Fintype E] [Fintype B] {cs : E → Finset B} {A : Finset E → Prop}

/-- The polymers: nonempty block sets. -/
abbrev NePoly (B : Type*) := {Y : Finset B // Y.Nonempty}

variable (cs A) in
/-- The admissible connected families with union `Y`. -/
def Cfam (Y : Finset B) : Finset (Finset E) :=
  Finset.univ.filter (fun C => ConnSet cs C ∧ A C ∧ unionCs cs C = Y)

variable (cs A) in
/-- The families whose components have the unions `Γ`. -/
def Fib (Γ : Finset (NePoly B)) : Finset (Finset E) :=
  Finset.univ.filter (fun D => (∀ t ∈ D, ∃ Y ∈ Γ, cs t ⊆ Y.1) ∧
    ∀ Y ∈ Γ, ConnSet cs (rs cs D Y.1) ∧ unionCs cs (rs cs D Y.1) = Y.1 ∧ A (rs cs D Y.1))

variable (cs A) in
/-- The activity of the polymer `Y`: the sum over admissible connected families with union `Y`. -/
def polyAct (w : E → ℂ) (Y : NePoly B) : ℂ := ∑ C ∈ Cfam cs A Y.1, ∏ t ∈ C, w t

omit [Fintype B] in
theorem not_subset_of_disjoint {s Y Y' : Finset B} (hd : Disjoint Y Y') (hne : s.Nonempty)
    (h : s ⊆ Y) : ¬ s ⊆ Y' := fun h' => by
  obtain ⟨b, hb⟩ := hne
  exact Finset.disjoint_left.mp hd (h hb) (h' hb)

omit [Fintype B] in
theorem mem_Cfam {Y : Finset B} {C : Finset E} :
    C ∈ Cfam cs A Y ↔ ConnSet cs C ∧ A C ∧ unionCs cs C = Y := by simp [Cfam]

theorem mem_Fib {Γ : Finset (NePoly B)} {D : Finset E} :
    D ∈ Fib cs A Γ ↔ (∀ t ∈ D, ∃ Y ∈ Γ, cs t ⊆ Y.1) ∧
      ∀ Y ∈ Γ, ConnSet cs (rs cs D Y.1) ∧ unionCs cs (rs cs D Y.1) = Y.1 ∧ A (rs cs D Y.1) := by
  simp [Fib]

omit [Fintype B] in
theorem sub_of_mem_Cfam {Y : Finset B} {C : Finset E} (h : C ∈ Cfam cs A Y) {t : E} (ht : t ∈ C) :
    cs t ⊆ Y := by
  rw [mem_Cfam] at h
  rw [← h.2.2]
  exact Finset.subset_biUnion_of_mem cs ht

omit [Fintype E] [Fintype B] in
theorem rs_eq_self {C : Finset E} {Y : Finset B} (h : ∀ t ∈ C, cs t ⊆ Y) : rs cs C Y = C :=
  Finset.filter_true_of_mem h

omit [Fintype E] [Fintype B] in
theorem rs_eq_empty {C : Finset E} {Y : Finset B} (h : ∀ t ∈ C, ¬ cs t ⊆ Y) : rs cs C Y = ∅ :=
  Finset.filter_false_of_mem h

omit [Fintype E] [Fintype B] in
theorem rs_union (C D : Finset E) (Y : Finset B) : rs cs (C ∪ D) Y = rs cs C Y ∪ rs cs D Y :=
  Finset.filter_union _ _ _

theorem fib_nonempty (hA0 : ∀ D, A D → ∀ t ∈ D, (cs t).Nonempty) {Γ : Finset (NePoly B)}
    {D : Finset E} (hD : D ∈ Fib cs A Γ) {t : E} (ht : t ∈ D) : (cs t).Nonempty := by
  obtain ⟨h1, h2⟩ := mem_Fib.mp hD
  obtain ⟨Y, hY, hY'⟩ := h1 t ht
  exact hA0 _ (h2 Y hY).2.2 t (mem_rs.mpr ⟨ht, hY'⟩)

omit [Fintype B] in
theorem cfam_nonempty (hA0 : ∀ D, A D → ∀ t ∈ D, (cs t).Nonempty) {Y : Finset B}
    {C : Finset E} (hC : C ∈ Cfam cs A Y) {t : E} (ht : t ∈ C) : (cs t).Nonempty :=
  hA0 _ (mem_Cfam.mp hC).2.1 t ht

theorem sum_fib (hA0 : ∀ D, A D → ∀ t ∈ D, (cs t).Nonempty) (w : E → ℂ)
    (Γ : Finset (NePoly B)) (hΓ : ∀ Y ∈ Γ, ∀ Y' ∈ Γ, Y ≠ Y' → Disjoint Y.1 Y'.1) :
    ∑ D ∈ Fib cs A Γ, ∏ t ∈ D, w t = ∏ Y ∈ Γ, polyAct cs A w Y := by
  induction Γ using Finset.induction_on with
  | empty =>
    have : Fib cs A (∅ : Finset (NePoly B)) = {∅ } := by
      ext D
      simp only [mem_Fib, Finset.notMem_empty, false_and, exists_false, imp_false, Finset.mem_singleton]
      constructor
      · intro h; exact Finset.eq_empty_of_forall_notMem (fun t ht => h.1 t ht)
      · intro h; subst h; exact ⟨fun t ht => by simp at ht, fun Y hY => by simp at hY⟩
    simp [this]
  | insert Y Γ hY ih =>
    have hΓ' : ∀ Y₁ ∈ Γ, ∀ Y₂ ∈ Γ, Y₁ ≠ Y₂ → Disjoint Y₁.1 Y₂.1 := fun a ha b hb hab =>
      hΓ a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hYd : ∀ Y' ∈ Γ, Disjoint Y.1 Y'.1 := fun Y' hY' =>
      hΓ Y (Finset.mem_insert_self _ _) Y' (Finset.mem_insert_of_mem hY')
        (fun h => hY (h ▸ hY'))
    rw [Finset.prod_insert hY, ← ih hΓ']
    unfold polyAct
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    symm
    refine Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun D => (rs cs D Y.1, D.filter (fun t => ¬ cs t ⊆ Y.1)))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨C, D'⟩ hp
      simp only [Finset.mem_product] at hp
      obtain ⟨hC, hD'⟩ := hp
      have hCY : ∀ t ∈ C, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC ht
      have hD'n : ∀ t ∈ D', ¬ cs t ⊆ Y.1 := fun t ht hsub => by
        obtain ⟨Y', hY', hsub'⟩ := (mem_Fib.mp hD').1 t ht
        exact not_subset_of_disjoint (hYd Y' hY').symm (fib_nonempty hA0 hD' ht) hsub' hsub
      have hCn : ∀ Y' ∈ Γ, ∀ t ∈ C, ¬ cs t ⊆ Y'.1 := fun Y' hY' t ht =>
        not_subset_of_disjoint (hYd Y' hY') (cfam_nonempty hA0 hC ht) (hCY t ht)
      show C ∪ D' ∈ Fib cs A (insert Y Γ)
      rw [mem_Fib]
      refine ⟨fun t ht => ?_, fun Y'' hY'' => ?_⟩
      · rcases Finset.mem_union.mp ht with h | h
        · exact ⟨Y, Finset.mem_insert_self _ _, hCY t h⟩
        · obtain ⟨Y', hY', hs⟩ := (mem_Fib.mp hD').1 t h
          exact ⟨Y', Finset.mem_insert_of_mem hY', hs⟩
      · rcases Finset.mem_insert.mp hY'' with rfl | h
        · rw [rs_union, rs_eq_self hCY, rs_eq_empty hD'n, Finset.union_empty]
          have := mem_Cfam.mp hC
          exact ⟨this.1, this.2.2, this.2.1⟩
        · rw [rs_union, rs_eq_empty (hCn Y'' h), Finset.empty_union]
          exact (mem_Fib.mp hD').2 Y'' h
    · intro D hD
      obtain ⟨h1, h2⟩ := mem_Fib.mp hD
      have hY2 := h2 Y (Finset.mem_insert_self _ _)
      rw [Finset.mem_product]
      show rs cs D Y.1 ∈ Cfam cs A Y.1 ∧ D.filter (fun t => ¬ cs t ⊆ Y.1) ∈ Fib cs A Γ
      refine ⟨mem_Cfam.mpr ⟨hY2.1, hY2.2.2, hY2.2.1⟩, ?_⟩
      rw [mem_Fib]
      have hnc : ∀ t ∈ D, ¬ cs t ⊆ Y.1 → ∃ Y' ∈ Γ, cs t ⊆ Y'.1 := fun t ht hn => by
        obtain ⟨Y', hY', hs⟩ := h1 t ht
        rcases Finset.mem_insert.mp hY' with rfl | h
        · exact absurd hs hn
        · exact ⟨Y', h, hs⟩
      refine ⟨fun t ht => ?_, fun Y' hY' => ?_⟩
      · rw [Finset.mem_filter] at ht
        exact hnc t ht.1 ht.2
      · have heq : rs cs (D.filter (fun t => ¬ cs t ⊆ Y.1)) Y'.1 = rs cs D Y'.1 := by
          ext t
          simp only [mem_rs, Finset.mem_filter]
          constructor
          · exact fun h => ⟨h.1.1, h.2⟩
          · rintro ⟨ht, hs⟩
            refine ⟨⟨ht, ?_⟩, hs⟩
            have hne := hA0 _ (h2 Y' (Finset.mem_insert_of_mem hY')).2.2 t (mem_rs.mpr ⟨ht, hs⟩)
            exact not_subset_of_disjoint (hYd Y' hY').symm hne hs
        rw [heq]
        exact h2 Y' (Finset.mem_insert_of_mem hY')
    · rintro ⟨C, D'⟩ hp
      simp only [Finset.mem_product] at hp
      obtain ⟨hC, hD'⟩ := hp
      have hCY : ∀ t ∈ C, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC ht
      have hD'n : ∀ t ∈ D', ¬ cs t ⊆ Y.1 := fun t ht hsub => by
        obtain ⟨Y', hY', hsub'⟩ := (mem_Fib.mp hD').1 t ht
        exact not_subset_of_disjoint (hYd Y' hY').symm (fib_nonempty hA0 hD' ht) hsub' hsub
      simp only [rs_union, rs_eq_self hCY, rs_eq_empty hD'n, Finset.union_empty, Finset.filter_union]
      rw [Finset.filter_false_of_mem (fun t ht hn => hn (hCY t ht)),
        Finset.filter_true_of_mem hD'n, Finset.empty_union]
    · intro D _
      show rs cs D Y.1 ∪ D.filter (fun t => ¬ cs t ⊆ Y.1) = D
      exact Finset.filter_union_filter_not_eq _ _
    · rintro ⟨C, D'⟩ hp
      simp only [Finset.mem_product] at hp
      obtain ⟨hC, hD'⟩ := hp
      have hCY : ∀ t ∈ C, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC ht
      have hD'n : ∀ t ∈ D', ¬ cs t ⊆ Y.1 := fun t ht hsub => by
        obtain ⟨Y', hY', hsub'⟩ := (mem_Fib.mp hD').1 t ht
        exact not_subset_of_disjoint (hYd Y' hY').symm (fib_nonempty hA0 hD' ht) hsub' hsub
      have hdisj : Disjoint C D' := Finset.disjoint_left.mpr (fun t htC htD => hD'n t htD (hCY t htC))
      exact (Finset.prod_union hdisj).symm

variable (cs) in
/-- The unions of the components of `D`. -/
def Gam (D : Finset E) : Finset (NePoly B) :=
  Finset.univ.filter (fun Y => ∃ t ∈ D, unionCs cs (comp cs D t) = Y.1)

omit [Fintype E] [Fintype B] in
theorem rs_unionCs_comp {D : Finset E} (hD : ∀ t ∈ D, (cs t).Nonempty) {t₀ : E} :
    rs cs D (unionCs cs (comp cs D t₀)) = comp cs D t₀ := by
  ext s
  rw [mem_rs]
  constructor
  · rintro ⟨hs, hsub⟩
    obtain ⟨b, hb⟩ := hD s hs
    obtain ⟨s', hs', hbs'⟩ := mem_unionCs.mp (hsub hb)
    have hcont : Contact cs s' s := fun hd => Finset.disjoint_left.mp hd hbs' hb
    exact comp_closed hs' hs hcont
  · intro hs
    exact ⟨comp_subset D t₀ hs, fun b hb => mem_unionCs.mpr ⟨s, hs, hb⟩⟩

omit [Fintype E] [Fintype B] in
theorem unionCs_comp_nonempty {D : Finset E} (hD : ∀ t ∈ D, (cs t).Nonempty) {t : E} (ht : t ∈ D) :
    (unionCs cs (comp cs D t)).Nonempty := by
  obtain ⟨b, hb⟩ := hD t ht
  exact ⟨b, mem_unionCs.mpr ⟨t, self_mem_comp ht, hb⟩⟩

omit [Fintype E] in
theorem gam_disjoint {D : Finset E} {Y₁ Y₂ : NePoly B} (h₁ : Y₁ ∈ Gam cs D) (h₂ : Y₂ ∈ Gam cs D)
    (hne : Y₁ ≠ Y₂) : Disjoint Y₁.1 Y₂.1 := by
  simp only [Gam, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
  obtain ⟨t₁, ht₁, e₁⟩ := h₁
  obtain ⟨t₂, ht₂, e₂⟩ := h₂
  by_contra hd
  obtain ⟨b, hb₁, hb₂⟩ := Finset.not_disjoint_iff.mp hd
  rw [← e₁] at hb₁
  rw [← e₂] at hb₂
  obtain ⟨s₁, hs₁, hbs₁⟩ := mem_unionCs.mp hb₁
  obtain ⟨s₂, hs₂, hbs₂⟩ := mem_unionCs.mp hb₂
  have hcont : Contact cs s₁ s₂ := fun hd => Finset.disjoint_left.mp hd hbs₁ hbs₂
  have h12 : s₂ ∈ comp cs D t₁ := by
    have := comp_closed (cs := cs) hs₁ (comp_subset D t₂ hs₂) hcont
    exact this
  apply hne
  apply Subtype.ext
  rw [← e₁, ← e₂, ← comp_eq_of_mem h12, comp_eq_of_mem hs₂]

theorem fib_gam (hA0 : ∀ D, A D → ∀ t ∈ D, (cs t).Nonempty)
    (hLoc : ∀ D, A D ↔ ∀ t ∈ D, A (comp cs D t)) {D : Finset E} (hD : A D) :
    D ∈ Fib cs A (Gam cs D) := by
  have hne := hA0 D hD
  rw [mem_Fib]
  refine ⟨fun t ht => ?_, fun Y hY => ?_⟩
  · refine ⟨⟨unionCs cs (comp cs D t), unionCs_comp_nonempty hne ht⟩, ?_, ?_⟩
    · simp only [Gam, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨t, ht, rfl⟩
    · exact fun b hb => mem_unionCs.mpr ⟨t, self_mem_comp ht, hb⟩
  · simp only [Gam, Finset.mem_filter, Finset.mem_univ, true_and] at hY
    obtain ⟨t, ht, e⟩ := hY
    rw [← e, rs_unionCs_comp hne]
    exact ⟨connSet_comp ht, rfl, (hLoc D).mp hD t ht⟩

theorem comp_eq_rs {Γ : Finset (NePoly B)} (hΓ : ∀ Y ∈ Γ, ∀ Y' ∈ Γ, Y ≠ Y' → Disjoint Y.1 Y'.1)
    {D : Finset E} (hD : D ∈ Fib cs A Γ) {Y : NePoly B} (hY : Y ∈ Γ) {t : E} (ht : t ∈ D)
    (hsub : cs t ⊆ Y.1) : comp cs D t = rs cs D Y.1 := by
  obtain ⟨h1, h2⟩ := mem_Fib.mp hD
  have htY : t ∈ rs cs D Y.1 := mem_rs.mpr ⟨ht, hsub⟩
  ext s
  constructor
  · intro hs
    rw [mem_comp] at hs
    refine (reach_stays cs (D' := rs cs D Y.1) (fun x hx y hy hxy => ?_) htY hs.2).1
    rw [mem_rs] at hx ⊢
    refine ⟨hy, ?_⟩
    obtain ⟨Y', hY', hyY'⟩ := h1 y hy
    obtain ⟨b, hb⟩ := Finset.not_disjoint_iff.mp hxy
    have : Y = Y' := by
      by_contra hne
      exact Finset.disjoint_left.mp (hΓ Y hY Y' hY' hne) (hx.2 hb.1) (hyY' hb.2)
    exact this ▸ hyY'
  · intro hs
    rw [mem_comp]
    have hconn := (h2 Y hY).1.2 t htY s hs
    exact ⟨(mem_rs.mp hs).1, Reach.mono cs (Finset.filter_subset _ _) hconn⟩

theorem gam_fib (hLoc : ∀ D, A D ↔ ∀ t ∈ D, A (comp cs D t)) {Γ : Finset (NePoly B)}
    (hΓ : ∀ Y ∈ Γ, ∀ Y' ∈ Γ, Y ≠ Y' → Disjoint Y.1 Y'.1) {D : Finset E} (hD : D ∈ Fib cs A Γ) :
    A D ∧ Gam cs D = Γ := by
  obtain ⟨h1, h2⟩ := mem_Fib.mp hD
  refine ⟨(hLoc D).mpr (fun t ht => ?_), ?_⟩
  · obtain ⟨Y, hY, hsub⟩ := h1 t ht
    rw [comp_eq_rs hΓ hD hY ht hsub]
    exact (h2 Y hY).2.2
  · ext Y
    simp only [Gam, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, e⟩
      obtain ⟨Y', hY', hsub⟩ := h1 t ht
      rw [comp_eq_rs hΓ hD hY' ht hsub, (h2 Y' hY').2.1] at e
      have : Y = Y' := Subtype.ext e.symm
      exact this ▸ hY'
    · intro hY
      obtain ⟨t, ht⟩ := (h2 Y hY).1.1
      rw [mem_rs] at ht
      exact ⟨t, ht.1, by rw [comp_eq_rs hΓ hD hY ht.1 ht.2]; exact (h2 Y hY).2.1⟩

/-- **Decomposition of a sum over admissible families into a polymer gas.** -/
theorem decomposition (hA0 : ∀ D, A D → ∀ t ∈ D, (cs t).Nonempty)
    (hLoc : ∀ D, A D ↔ ∀ t ∈ D, A (comp cs D t)) (w : E → ℂ) :
    ∑ D ∈ Finset.univ.filter A, ∏ t ∈ D, w t =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (polyAct cs A w) := by
  have hcompat : ∀ Γ : Finset (NePoly B),
      Compat (shareBlock (Subtype.val : NePoly B → Finset B)) Γ ↔
        ∀ Y ∈ Γ, ∀ Y' ∈ Γ, Y ≠ Y' → Disjoint Y.1 Y'.1 := by
    intro Γ
    unfold Compat
    refine forall₄_congr (fun x _ y _ => ?_)
    rw [lnk_shareBlock]
    unfold shareBlock
    constructor
    · exact fun h hxy => not_not.mp (h hxy)
    · exact fun h hxy hn => hn (h hxy)
  unfold Xi
  rw [← Finset.sum_fiberwise_of_maps_to (g := Gam cs)
    (t := (Finset.univ : Finset (Finset (NePoly B))).filter
      (Compat (shareBlock (Subtype.val : NePoly B → Finset B)))) ]
  · refine Finset.sum_congr rfl (fun Γ hΓ => ?_)
    rw [Finset.mem_filter, hcompat] at hΓ
    rw [← sum_fib hA0 w Γ hΓ.2]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hD, rfl⟩
      exact fib_gam hA0 hLoc hD
    · intro hD
      obtain ⟨h1, h2⟩ := gam_fib hLoc hΓ.2 hD
      exact ⟨h1, h2⟩
  · intro D hD
    rw [Finset.mem_filter] at hD ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hcompat]
    exact fun Y hY Y' hY' hne => gam_disjoint hY hY' hne

end Fiber

section Powerset

/-- The sum over nonempty subfamilies of the products of nonnegative weights. -/
theorem sum_powerset_erase_le {T : Type*} (r : T → ℝ) (hr : ∀ t, 0 ≤ r t) (S : Finset T) :
    ∑ C ∈ S.powerset.erase ∅, ∏ t ∈ C, r t ≤ Real.exp (∑ t ∈ S, r t) - 1 := by
  have h1 : ∏ t ∈ S, (1 + r t) = ∑ C ∈ S.powerset, ∏ t ∈ C, r t := Finset.prod_one_add S
  have h2 := Finset.add_sum_erase S.powerset (fun C => ∏ t ∈ C, r t) (Finset.empty_mem_powerset S)
  have h3 := Real.prod_one_add_le_exp_sum S hr
  simp only [Finset.prod_empty] at h2
  linarith

end Powerset

end Balaban.Polymer
