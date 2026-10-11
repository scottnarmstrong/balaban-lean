module

public import Mathlib

/-!
# The Ursell function of a finite graph and its vertex-removal recursion

For a simple graph `G` on a type `ι` and a finite vertex set `S`, `ursell G S` is the signed count
`∑ (-1)^{|H|}` over the connected spanning edge sets `H` of `G` restricted to `S` (the Ursell
function `φ^T` of the polymer expansion).  The main result is the vertex-removal recursion
`ursell_insert_rec`: for `v ∉ U` and `u0 ∈ U`,

`φ(U ∪ {v}) = - ∑_{T ∋ u0, T ⊆ U, T meets N(v)} φ(T) φ((U \ T) ∪ {v})`,

obtained from the decomposition of a connected graph on `U ∪ {v}` along the component of `u0`
in the graph with `v` deleted.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer

variable {ι : Type*}

/-- Reachability along the edges of a finite edge set. -/
def Rch (H : Finset (Sym2 ι)) : ι → ι → Prop :=
  Relation.ReflTransGen (fun a b => s(a, b) ∈ H)

/-- The edges of `G` with both ends in `S`. -/
def edgesIn (G : SimpleGraph ι) (S : Finset ι) : Finset (Sym2 ι) :=
  S.sym2.filter (· ∈ G.edgeSet)

/-- `H` connects all the vertices of `S`. -/
def Conn (S : Finset ι) (H : Finset (Sym2 ι)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, Rch H x y

/-- The Ursell function of `G` on the vertex set `S`: the signed number of connected spanning
edge sets. -/
def ursell (G : SimpleGraph ι) (S : Finset ι) : ℤ :=
  ∑ H ∈ (edgesIn G S).powerset.filter (Conn S), (-1 : ℤ) ^ H.card

theorem mem_edgesIn {G : SimpleGraph ι} {S : Finset ι} {e : Sym2 ι} :
    e ∈ edgesIn G S ↔ e ∈ G.edgeSet ∧ ∀ z ∈ e, z ∈ S := by
  simp only [edgesIn, Finset.mem_filter, Finset.mem_sym2_iff]
  exact and_comm

theorem mk_mem_edgesIn {G : SimpleGraph ι} {S : Finset ι} {a b : ι} :
    s(a, b) ∈ edgesIn G S ↔ G.Adj a b ∧ a ∈ S ∧ b ∈ S := by
  rw [mem_edgesIn]
  simp [SimpleGraph.mem_edgeSet]

namespace Rch

variable {H H' : Finset (Sym2 ι)} {a b c : ι}

theorem refl : Rch H a a := Relation.ReflTransGen.refl

theorem single (h : s(a, b) ∈ H) : Rch H a b := Relation.ReflTransGen.single h

theorem trans (h₁ : Rch H a b) (h₂ : Rch H b c) : Rch H a c := Relation.ReflTransGen.trans h₁ h₂

theorem symm (h : Rch H a b) : Rch H b a := by
  induction h with
  | refl => exact refl
  | tail _ hbc ih => exact (single (by rwa [Sym2.eq_swap])).trans ih

theorem mono (hH : H ⊆ H') (h : Rch H a b) : Rch H' a b := by
  induction h with
  | refl => exact refl
  | tail _ hbc ih => exact ih.trans (single (hH hbc))

/-- A predicate closed under the edges of `H` propagates along reachability. -/
theorem closed {A : ι → Prop} (hA : ∀ x y, s(x, y) ∈ H → A x → A y) (h : Rch H a b) (ha : A a) :
    A b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hA _ _ hbc ih

/-- Reachability inside an `H`-closed set only uses the edges inside it. -/
theorem filter {A : ι → Prop} (hA : ∀ x y, s(x, y) ∈ H → A x → A y) (h : Rch H a b) (ha : A a) :
    Rch (H.filter (fun e => ∀ z ∈ e, A z)) a b := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
    have hb : A b := closed hA ‹Rch H a b› ha
    have hc : A c := hA _ _ hbc hb
    refine ih.trans (single ?_)
    simp only [Finset.mem_filter]
    refine ⟨hbc, ?_⟩
    intro z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact hb
    · exact hc

end Rch

/-- Signed count of the nonempty subsets of a finite set. -/
theorem sum_nonempty_powerset_neg_one_pow (s : Finset ι) :
    ∑ W ∈ s.powerset.filter Finset.Nonempty, (-1 : ℤ) ^ W.card = -(if s.Nonempty then 1 else 0) := by
  have h := Finset.sum_powerset_neg_one_pow_card (x := s)
  have h2 : ∑ W ∈ s.powerset, (-1 : ℤ) ^ W.card
      = (-1 : ℤ) ^ (∅ : Finset ι).card + ∑ W ∈ s.powerset.filter Finset.Nonempty, (-1 : ℤ) ^ W.card := by
    rw [← Finset.sum_filter_add_sum_filter_not s.powerset Finset.Nonempty]
    rw [add_comm]
    congr 1
    have : s.powerset.filter (fun W => ¬ W.Nonempty) = {∅} := by
      ext W
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
        Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
    rw [this, Finset.sum_singleton]
  rw [h2] at h
  by_cases hs : s.Nonempty
  · have : s ≠ ∅ := hs.ne_empty
    simp only [this, ite_false] at h
    simp only [hs, ite_true]
    simp only [Finset.card_empty, pow_zero] at h
    linarith
  · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst this
    simp [Finset.filter_singleton]


/-! ### Decomposition along the component of `u0` in the graph with `v` removed -/

section Decomposition

variable [DecidableEq ι]

/-- The edges of `H` not touching `v`. -/
def hp (v : ι) (H : Finset (Sym2 ι)) : Finset (Sym2 ι) := H.filter (fun e => v ∉ e)

/-- The component of `u0` in `H` with `v` removed, inside `U`. -/
def Tf (v : ι) (U : Finset ι) (u0 : ι) (H : Finset (Sym2 ι)) : Finset ι :=
  U.filter (fun x => Rch (hp v H) u0 x)

/-- The edges of `H` inside the component. -/
def H1f (v : ι) (U : Finset ι) (u0 : ι) (H : Finset (Sym2 ι)) : Finset (Sym2 ι) :=
  H.filter (fun e => ∀ z ∈ e, z ∈ Tf v U u0 H)

/-- The neighbours of `v` in the component, through `H`. -/
def W1f (v : ι) (U : Finset ι) (u0 : ι) (H : Finset (Sym2 ι)) : Finset ι :=
  (Tf v U u0 H).filter (fun w => s(v, w) ∈ H)

/-- The edges of `H` inside `v` together with the rest of `U`. -/
def Hrf (v : ι) (U : Finset ι) (u0 : ι) (H : Finset (Sym2 ι)) : Finset (Sym2 ι) :=
  H.filter (fun e => ∀ z ∈ e, z ∈ insert v (U \ Tf v U u0 H))

/-- Reassembly of the three parts. -/
def Hb (v : ι) (H1 : Finset (Sym2 ι)) (W : Finset ι) (Hr : Finset (Sym2 ι)) :
    Finset (Sym2 ι) :=
  H1 ∪ W.image (fun w => s(v, w)) ∪ Hr

variable {G : SimpleGraph ι} {v : ι} {U : Finset ι} {u0 : ι} {H : Finset (Sym2 ι)}

theorem mem_Tf {x : ι} : x ∈ Tf v U u0 H ↔ x ∈ U ∧ Rch (hp v H) u0 x := by
  simp [Tf]

theorem Tf_subset : Tf v U u0 H ⊆ U := fun _ hx => (mem_Tf.mp hx).1

theorem mem_hp {e : Sym2 ι} : e ∈ hp v H ↔ e ∈ H ∧ v ∉ e := by simp [hp]

omit [DecidableEq ι] in
/-- The ends of an edge cannot lie both in `T` and in a set disjoint from `T`. -/
theorem no_both {T R : Finset ι} (hTR : Disjoint T R) (e : Sym2 ι) (h1 : ∀ z ∈ e, z ∈ T)
    (h2 : ∀ z ∈ e, z ∈ R) : False := by
  induction e using Sym2.ind with
  | _ a b =>
    exact Finset.disjoint_left.mp hTR (h1 a (Sym2.mem_mk_left a b)) (h2 a (Sym2.mem_mk_left a b))


theorem Tf_step (hv : v ∉ U) (hH : H ⊆ edgesIn G (insert v U)) {a b : ι} (hab : s(a, b) ∈ H)
    (ha : a ∈ Tf v U u0 H) (hvb : v ≠ b) : b ∈ Tf v U u0 H := by
  have hbU : b ∈ U := by
    have := (mk_mem_edgesIn.mp (hH hab)).2.2
    rcases Finset.mem_insert.mp this with h | h
    · exact absurd h.symm hvb
    · exact h
  have hva : v ≠ a := fun h => hv (h ▸ Tf_subset ha)
  refine mem_Tf.mpr ⟨hbU, (mem_Tf.mp ha).2.trans (Rch.single ?_)⟩
  refine mem_hp.mpr ⟨hab, ?_⟩
  rw [Sym2.mem_iff]
  rintro (h | h)
  · exact hva h
  · exact hvb h

/-- Every edge of `H` lies in the component, or joins `v` to it, or lies in the rest. -/
theorem classify (hv : v ∉ U) (hH : H ⊆ edgesIn G (insert v U)) {e : Sym2 ι} (he : e ∈ H) :
    (∀ z ∈ e, z ∈ Tf v U u0 H) ∨ (∃ w ∈ Tf v U u0 H, e = s(v, w)) ∨
      (∀ z ∈ e, z ∈ insert v (U \ Tf v U u0 H)) := by
  induction e using Sym2.ind with
  | _ a b =>
  obtain ⟨hab, ha, hb⟩ := mk_mem_edgesIn.mp (hH he)
  have hne : a ≠ b := hab.ne
  by_cases hav : v = a
  · subst hav
    have hbU : b ∈ U := by
      rcases Finset.mem_insert.mp hb with h | h
      · exact absurd h.symm hne
      · exact h
    by_cases hbT : b ∈ Tf v U u0 H
    · exact Or.inr (Or.inl ⟨b, hbT, rfl⟩)
    · refine Or.inr (Or.inr ?_)
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hbU, hbT⟩)
  by_cases hbv : v = b
  · subst hbv
    have haU : a ∈ U := by
      rcases Finset.mem_insert.mp ha with h | h
      · exact absurd h.symm hav
      · exact h
    by_cases haT : a ∈ Tf v U u0 H
    · exact Or.inr (Or.inl ⟨a, haT, Sym2.eq_swap⟩)
    · refine Or.inr (Or.inr ?_)
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨haU, haT⟩)
      · exact Finset.mem_insert_self _ _
  by_cases haT : a ∈ Tf v U u0 H
  · refine Or.inl ?_
    have hbT : b ∈ Tf v U u0 H := Tf_step hv hH he haT hbv
    intro z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact haT
    · exact hbT
  by_cases hbT : b ∈ Tf v U u0 H
  · exact absurd (Tf_step hv hH (by rwa [Sym2.eq_swap]) hbT hav) haT
  · refine Or.inr (Or.inr ?_)
    have haU : a ∈ U := by
      rcases Finset.mem_insert.mp ha with h | h
      · exact absurd h.symm hav
      · exact h
    have hbU : b ∈ U := by
      rcases Finset.mem_insert.mp hb with h | h
      · exact absurd h.symm hbv
      · exact h
    intro z hz
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨haU, haT⟩)
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hbU, hbT⟩)

theorem H1f_sub (hH : H ⊆ edgesIn G (insert v U)) :
    H1f v U u0 H ⊆ edgesIn G (Tf v U u0 H) := by
  intro e he
  rw [H1f, Finset.mem_filter] at he
  exact mem_edgesIn.mpr ⟨(mem_edgesIn.mp (hH he.1)).1, he.2⟩

theorem conn_H1f (hv : v ∉ U) (hu0 : u0 ∈ U) (hH : H ⊆ edgesIn G (insert v U)) :
    Conn (Tf v U u0 H) (H1f v U u0 H) := by
  have u0T : u0 ∈ Tf v U u0 H := mem_Tf.mpr ⟨hu0, Rch.refl⟩
  have key : ∀ z ∈ Tf v U u0 H, Rch (H1f v U u0 H) u0 z := by
    intro z hz
    have h1 := Rch.filter (A := fun x => x ∈ Tf v U u0 H) (H := hp v H) ?_ (mem_Tf.mp hz).2 u0T
    · refine Rch.mono ?_ h1
      intro e he
      rw [Finset.mem_filter] at he
      exact Finset.mem_filter.mpr ⟨(mem_hp.mp he.1).1, he.2⟩
    · intro a b hab ha
      have hab' := mem_hp.mp hab
      refine Tf_step hv hH hab'.1 ha ?_
      intro h
      exact hab'.2 (h ▸ Sym2.mem_mk_right a b)
  intro x hx y hy
  exact (key x hx).symm.trans (key y hy)

theorem W1f_sub (hH : H ⊆ edgesIn G (insert v U)) :
    W1f v U u0 H ⊆ (Tf v U u0 H).filter (G.Adj v) := by
  intro w hw
  rw [W1f, Finset.mem_filter] at hw
  exact Finset.mem_filter.mpr ⟨hw.1, (mk_mem_edgesIn.mp (hH hw.2)).1⟩

theorem W1f_nonempty (hv : v ∉ U) (hu0 : u0 ∈ U) (hH : H ⊆ edgesIn G (insert v U))
    (hc : Conn (insert v U) H) : (W1f v U u0 H).Nonempty := by
  have u0T : u0 ∈ Tf v U u0 H := mem_Tf.mpr ⟨hu0, Rch.refl⟩
  have key : ∀ b, Rch H u0 b → b ∈ Tf v U u0 H ∨ ∃ w ∈ Tf v U u0 H, s(v, w) ∈ H := by
    intro b hb
    induction hb with
    | refl => exact Or.inl u0T
    | @tail b c _ hbc ih =>
      rcases ih with hbT | hw
      · by_cases hcv : v = c
        · subst hcv
          exact Or.inr ⟨b, hbT, by rwa [Sym2.eq_swap]⟩
        · exact Or.inl (Tf_step hv hH hbc hbT hcv)
      · exact Or.inr hw
  have := key v (hc u0 (Finset.mem_insert_of_mem hu0) v (Finset.mem_insert_self _ _))
  rcases this with hvT | ⟨w, hw, hwH⟩
  · exact absurd (Tf_subset hvT) hv
  · exact ⟨w, Finset.mem_filter.mpr ⟨hw, hwH⟩⟩

theorem Hrf_sub (hH : H ⊆ edgesIn G (insert v U)) :
    Hrf v U u0 H ⊆ edgesIn G (insert v (U \ Tf v U u0 H)) := by
  intro e he
  rw [Hrf, Finset.mem_filter] at he
  exact mem_edgesIn.mpr ⟨(mem_edgesIn.mp (hH he.1)).1, he.2⟩

theorem conn_Hrf (hv : v ∉ U) (hH : H ⊆ edgesIn G (insert v U)) (hc : Conn (insert v U) H) :
    Conn (insert v (U \ Tf v U u0 H)) (Hrf v U u0 H) := by
  set T := Tf v U u0 H with hT
  have hRS : insert v (U \ T) ⊆ insert v U :=
    Finset.insert_subset_insert _ Finset.sdiff_subset
  have hTR : Disjoint T (insert v (U \ T)) := by
    rw [Finset.disjoint_left]
    intro x hxT hxR
    rcases Finset.mem_insert.mp hxR with h | h
    · exact hv (h ▸ Tf_subset hxT)
    · exact (Finset.mem_sdiff.mp h).2 hxT
  have hclosed : ∀ a b, s(a, b) ∈ Hrf v U u0 H → a ∈ insert v (U \ T) → b ∈ insert v (U \ T) := by
    intro a b hab _
    exact (Finset.mem_filter.mp hab).2 b (Sym2.mem_mk_right a b)
  have main : ∀ x ∈ insert v (U \ T), ∀ y, Rch H x y →
      Rch (Hrf v U u0 H) x y ∨ (y ∈ T ∧ Rch (Hrf v U u0 H) x v) := by
    intro x hx y hy
    induction hy with
    | refl => exact Or.inl Rch.refl
    | @tail y z _ hyz ih =>
      have notboth : y ∈ T → Rch (Hrf v U u0 H) x y → False := fun hyT h =>
        Finset.disjoint_left.mp hTR hyT (Rch.closed hclosed h hx)
      rcases classify hv hH hyz with hA | ⟨w, hwT, hw⟩ | hC
      · have hyT : y ∈ T := hA y (Sym2.mem_mk_left y z)
        have hzT : z ∈ T := hA z (Sym2.mem_mk_right y z)
        rcases ih with h | ⟨_, h⟩
        · exact absurd h (notboth hyT)
        · exact Or.inr ⟨hzT, h⟩
      · rcases Sym2.eq_iff.mp hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with h | ⟨hyT, _⟩
          · exact Or.inr ⟨hwT, h⟩
          · exact absurd (Tf_subset hyT) hv
        · rcases ih with h | ⟨_, h⟩
          · exact absurd h (notboth hwT)
          · exact Or.inl h
      · have hyz' : s(y, z) ∈ Hrf v U u0 H := Finset.mem_filter.mpr ⟨hyz, hC⟩
        have hyR : y ∈ insert v (U \ T) := hC y (Sym2.mem_mk_left y z)
        rcases ih with h | ⟨hyT, _⟩
        · exact Or.inl (h.trans (Rch.single hyz'))
        · exact absurd hyR (fun h => Finset.disjoint_left.mp hTR hyT h)
  intro x hx y hy
  rcases main x hx y (hc x (hRS hx) y (hRS hy)) with h | ⟨hyT, _⟩
  · exact h
  · exact absurd hy (fun h => Finset.disjoint_left.mp hTR hyT h)

/-- The data of a decomposition: the component `T`, a connected spanning set inside it, the
attachment points `W` of `v`, and a connected spanning set on `v` and the rest. -/
structure Tgt (G : SimpleGraph ι) (v : ι) (U : Finset ι) (u0 : ι) (T : Finset ι)
    (H1 : Finset (Sym2 ι)) (W : Finset ι) (Hr : Finset (Sym2 ι)) : Prop where
  TU : T ⊆ U
  u0T : u0 ∈ T
  sub1 : H1 ⊆ edgesIn G T
  conn1 : Conn T H1
  subW : W ⊆ T.filter (G.Adj v)
  neW : W.Nonempty
  subr : Hr ⊆ edgesIn G (insert v (U \ T))
  connr : Conn (insert v (U \ T)) Hr

section Backward

variable {T : Finset ι} {H1 : Finset (Sym2 ι)} {W : Finset ι} {Hr : Finset (Sym2 ι)}

theorem mem_Hb {e : Sym2 ι} :
    e ∈ Hb v H1 W Hr ↔ e ∈ H1 ∨ (∃ w ∈ W, e = s(v, w)) ∨ e ∈ Hr := by
  simp only [Hb, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ((h | ⟨w, hw, rfl⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨w, hw, rfl⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨w, hw, rfl⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨w, hw, rfl⟩)
    · exact Or.inr h

theorem Tgt.vT (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) : v ∉ T := fun hh => hv (h.TU hh)

theorem Tgt.disj (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) :
    Disjoint T (insert v (U \ T)) := by
  rw [Finset.disjoint_left]
  intro x hxT hxR
  rcases Finset.mem_insert.mp hxR with hh | hh
  · exact hv (hh ▸ h.TU hxT)
  · exact (Finset.mem_sdiff.mp hh).2 hxT

theorem Tgt.W_T (h : Tgt G v U u0 T H1 W Hr) {w : ι} (hw : w ∈ W) : w ∈ T :=
  (Finset.mem_filter.mp (h.subW hw)).1

theorem Tgt.W_adj (h : Tgt G v U u0 T H1 W Hr) {w : ι} (hw : w ∈ W) : G.Adj v w :=
  (Finset.mem_filter.mp (h.subW hw)).2

theorem Hb_sub (h : Tgt G v U u0 T H1 W Hr) : Hb v H1 W Hr ⊆ edgesIn G (insert v U) := by
  intro e he
  rcases mem_Hb.mp he with h1 | ⟨w, hw, rfl⟩ | hr
  · obtain ⟨hg, hz⟩ := mem_edgesIn.mp (h.sub1 h1)
    exact mem_edgesIn.mpr ⟨hg, fun z hz' => Finset.mem_insert_of_mem (h.TU (hz z hz'))⟩
  · exact mk_mem_edgesIn.mpr ⟨h.W_adj hw, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (h.TU (h.W_T hw))⟩
  · obtain ⟨hg, hz⟩ := mem_edgesIn.mp (h.subr hr)
    refine mem_edgesIn.mpr ⟨hg, fun z hz' => ?_⟩
    rcases Finset.mem_insert.mp (hz z hz') with rfl | hh
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hh).1

theorem conn_Hb (h : Tgt G v U u0 T H1 W Hr) : Conn (insert v U) (Hb v H1 W Hr) := by
  have key : ∀ x ∈ insert v U, Rch (Hb v H1 W Hr) x v := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · exact Rch.refl
    by_cases hxT : x ∈ T
    · obtain ⟨w, hw⟩ := h.neW
      have h1 : Rch H1 x w := h.conn1 x hxT w (h.W_T hw)
      refine (Rch.mono ?_ h1).trans (Rch.single ?_)
      · intro e he; exact mem_Hb.mpr (Or.inl he)
      · exact mem_Hb.mpr (Or.inr (Or.inl ⟨w, hw, Sym2.eq_swap⟩))
    · have h2 := h.connr x (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hxU, hxT⟩)) v
        (Finset.mem_insert_self _ _)
      exact Rch.mono (fun e he => mem_Hb.mpr (Or.inr (Or.inr he))) h2
  intro x hx y hy
  exact (key x hx).trans (key y hy).symm

theorem Tf_Hb (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) :
    Tf v U u0 (Hb v H1 W Hr) = T := by
  have hdisj := h.disj hv
  ext x
  rw [mem_Tf]
  constructor
  · rintro ⟨hxU, hx⟩
    refine Rch.closed (A := fun y => y ∈ T) ?_ hx h.u0T
    intro a b hab ha
    obtain ⟨habH, hvab⟩ := mem_hp.mp hab
    rcases mem_Hb.mp habH with h1 | ⟨w, hw, hew⟩ | hr
    · exact (mem_edgesIn.mp (h.sub1 h1)).2 b (Sym2.mem_mk_right a b)
    · exact absurd (hew ▸ Sym2.mem_mk_left v w) hvab
    · exfalso
      exact Finset.disjoint_left.mp hdisj ha ((mem_edgesIn.mp (h.subr hr)).2 a (Sym2.mem_mk_left a b))
  · intro hxT
    refine ⟨h.TU hxT, ?_⟩
    refine Rch.mono ?_ (h.conn1 u0 h.u0T x hxT)
    intro e he
    refine mem_hp.mpr ⟨mem_Hb.mpr (Or.inl he), ?_⟩
    intro hve
    exact h.vT hv ((mem_edgesIn.mp (h.sub1 he)).2 v hve)

theorem H1f_Hb (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) :
    H1f v U u0 (Hb v H1 W Hr) = H1 := by
  have hdisj := h.disj hv
  ext e
  rw [H1f, Finset.mem_filter, Tf_Hb hv h]
  constructor
  · rintro ⟨he, hz⟩
    rcases mem_Hb.mp he with h1 | ⟨w, hw, rfl⟩ | hr
    · exact h1
    · exact absurd (hz v (Sym2.mem_mk_left v w)) (h.vT hv)
    · exact (no_both hdisj e hz (mem_edgesIn.mp (h.subr hr)).2).elim
  · intro h1
    exact ⟨mem_Hb.mpr (Or.inl h1), (mem_edgesIn.mp (h.sub1 h1)).2⟩

theorem W1f_Hb (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) :
    W1f v U u0 (Hb v H1 W Hr) = W := by
  have hdisj := h.disj hv
  ext w
  rw [W1f, Finset.mem_filter, Tf_Hb hv h]
  constructor
  · rintro ⟨hwT, he⟩
    rcases mem_Hb.mp he with h1 | ⟨w', hw', hew⟩ | hr
    · exact absurd ((mem_edgesIn.mp (h.sub1 h1)).2 v (Sym2.mem_mk_left v w)) (h.vT hv)
    · have := Sym2.eq_iff.mp hew
      rcases this with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · exact hw'
      · exact hw'
    · exact absurd hwT (fun hh => Finset.disjoint_left.mp hdisj hh
        ((mem_edgesIn.mp (h.subr hr)).2 w (Sym2.mem_mk_right v w)))
  · intro hw
    exact ⟨h.W_T hw, mem_Hb.mpr (Or.inr (Or.inl ⟨w, hw, rfl⟩))⟩

theorem Hrf_Hb (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) :
    Hrf v U u0 (Hb v H1 W Hr) = Hr := by
  have hdisj := h.disj hv
  ext e
  rw [Hrf, Finset.mem_filter, Tf_Hb hv h]
  constructor
  · rintro ⟨he, hz⟩
    rcases mem_Hb.mp he with h1 | ⟨w, hw, rfl⟩ | hr
    · exact (no_both hdisj e (mem_edgesIn.mp (h.sub1 h1)).2 hz).elim
    · exact absurd (hz w (Sym2.mem_mk_right v w)) (fun hh => Finset.disjoint_left.mp hdisj (h.W_T hw) hh)
    · exact hr
  · intro hr
    exact ⟨mem_Hb.mpr (Or.inr (Or.inr hr)), (mem_edgesIn.mp (h.subr hr)).2⟩

theorem card_Hb (hv : v ∉ U) (h : Tgt G v U u0 T H1 W Hr) :
    (Hb v H1 W Hr).card = H1.card + W.card + Hr.card := by
  have hdisj := h.disj hv
  have hinj : Function.Injective (fun w : ι => s(v, w)) := fun a b hab => (Sym2.congr_right.mp hab)
  have d1 : Disjoint H1 (W.image (fun w => s(v, w))) := by
    rw [Finset.disjoint_left]
    intro e he hew
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hew
    exact h.vT hv ((mem_edgesIn.mp (h.sub1 he)).2 v (Sym2.mem_mk_left v w))
  have d2 : Disjoint (H1 ∪ W.image (fun w => s(v, w))) Hr := by
    rw [Finset.disjoint_left]
    intro e he her
    rcases Finset.mem_union.mp he with h1 | hew
    · exact no_both hdisj e (mem_edgesIn.mp (h.sub1 h1)).2 (mem_edgesIn.mp (h.subr her)).2
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hew
      exact Finset.disjoint_left.mp hdisj (h.W_T hw)
        ((mem_edgesIn.mp (h.subr her)).2 w (Sym2.mem_mk_right v w))
  rw [Hb, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
    Finset.card_image_of_injective _ hinj]

end Backward

section Forward

theorem tgt_forward (hv : v ∉ U) (hu0 : u0 ∈ U) (hH : H ⊆ edgesIn G (insert v U))
    (hc : Conn (insert v U) H) :
    Tgt G v U u0 (Tf v U u0 H) (H1f v U u0 H) (W1f v U u0 H) (Hrf v U u0 H) where
  TU := Tf_subset
  u0T := mem_Tf.mpr ⟨hu0, Rch.refl⟩
  sub1 := H1f_sub hH
  conn1 := conn_H1f hv hu0 hH
  subW := W1f_sub hH
  neW := W1f_nonempty hv hu0 hH hc
  subr := Hrf_sub hH
  connr := conn_Hrf hv hH hc

theorem Hb_forward (hv : v ∉ U) (hH : H ⊆ edgesIn G (insert v U)) :
    Hb v (H1f v U u0 H) (W1f v U u0 H) (Hrf v U u0 H) = H := by
  ext e
  rw [mem_Hb]
  constructor
  · rintro (h1 | ⟨w, hw, rfl⟩ | hr)
    · exact (Finset.mem_filter.mp h1).1
    · exact (Finset.mem_filter.mp hw).2
    · exact (Finset.mem_filter.mp hr).1
  · intro he
    rcases classify (u0 := u0) hv hH he with hA | ⟨w, hw, rfl⟩ | hC
    · exact Or.inl (Finset.mem_filter.mpr ⟨he, hA⟩)
    · exact Or.inr (Or.inl ⟨w, Finset.mem_filter.mpr ⟨hw, he⟩, rfl⟩)
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨he, hC⟩))

end Forward

omit [DecidableEq ι] in
theorem prod3 {α β γ : Type*} (B : Finset α) (A : Finset β) (C : Finset γ) (g : α → ℤ)
    (h : β → ℤ) (k : γ → ℤ) :
    (∑ a ∈ B, g a) * (∑ b ∈ A, h b) * (∑ c ∈ C, k c)
      = ∑ x ∈ B ×ˢ (A ×ˢ C), g x.1 * (h x.2.1 * k x.2.2) := by
  have inner : (∑ b ∈ A, h b) * (∑ c ∈ C, k c) = ∑ y ∈ A ×ˢ C, h y.1 * k y.2 := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
  rw [mul_assoc, inner, Finset.sum_mul_sum, Finset.sum_product]

end Decomposition

/-- The vertex-removal recursion for the Ursell function. -/
theorem ursell_insert_rec [DecidableEq ι] (G : SimpleGraph ι) {v : ι} {U : Finset ι}
    (hv : v ∉ U) {u0 : ι} (hu0 : u0 ∈ U) :
    ursell G (insert v U) =
      ∑ T ∈ U.powerset.filter (fun T => u0 ∈ T),
        (-(if (T.filter (G.Adj v)).Nonempty then 1 else 0 : ℤ)) * ursell G T *
          ursell G (insert v (U \ T)) := by
  have hR : ∀ T ∈ U.powerset.filter (fun T => u0 ∈ T),
      (-(if (T.filter (G.Adj v)).Nonempty then 1 else 0 : ℤ)) * ursell G T *
          ursell G (insert v (U \ T)) =
        ∑ x ∈ ((T.filter (G.Adj v)).powerset.filter Finset.Nonempty) ×ˢ
            (((edgesIn G T).powerset.filter (Conn T)) ×ˢ
              ((edgesIn G (insert v (U \ T))).powerset.filter (Conn (insert v (U \ T))))),
          (-1 : ℤ) ^ x.1.card * ((-1 : ℤ) ^ x.2.1.card * (-1 : ℤ) ^ x.2.2.card) := by
    intro T _
    rw [← prod3 (g := fun W : Finset ι => (-1 : ℤ) ^ W.card)
      (h := fun H : Finset (Sym2 ι) => (-1 : ℤ) ^ H.card)
      (k := fun H : Finset (Sym2 ι) => (-1 : ℤ) ^ H.card), sum_nonempty_powerset_neg_one_pow]
    rfl
  rw [Finset.sum_congr rfl hR, ursell]
  rw [Finset.sum_sigma' (s := U.powerset.filter (fun T => u0 ∈ T))
    (t := fun T => ((T.filter (G.Adj v)).powerset.filter Finset.Nonempty) ×ˢ
            (((edgesIn G T).powerset.filter (Conn T)) ×ˢ
              ((edgesIn G (insert v (U \ T))).powerset.filter (Conn (insert v (U \ T))))))
    (f := fun T x => (-1 : ℤ) ^ x.1.card * ((-1 : ℤ) ^ x.2.1.card * (-1 : ℤ) ^ x.2.2.card))]
  refine Finset.sum_bij'
    (fun H _ => (⟨Tf v U u0 H, (W1f v U u0 H, (H1f v U u0 H, Hrf v U u0 H))⟩ :
      (_ : Finset ι) × (Finset ι × (Finset (Sym2 ι) × Finset (Sym2 ι)))))
    (fun x _ => Hb v x.2.2.1 x.2.1 x.2.2.2) ?_ ?_ ?_ ?_ ?_
  · intro H hHm
    rw [Finset.mem_filter, Finset.mem_powerset] at hHm
    have ht := tgt_forward hv hu0 hHm.1 hHm.2
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product]
    exact ⟨⟨Tf_subset, ht.u0T⟩, ⟨ht.subW, ht.neW⟩, ⟨ht.sub1, ht.conn1⟩, ⟨ht.subr, ht.connr⟩⟩
  · rintro ⟨T, W, H1, Hr⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hx
    obtain ⟨⟨hTU, hu0T⟩, ⟨hW, hWne⟩, ⟨h1, c1⟩, ⟨hr, cr⟩⟩ := hx
    have ht : Tgt G v U u0 T H1 W Hr := ⟨hTU, hu0T, h1, c1, hW, hWne, hr, cr⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Hb_sub ht, conn_Hb ht⟩
  · intro H hHm
    rw [Finset.mem_filter, Finset.mem_powerset] at hHm
    exact Hb_forward hv hHm.1
  · rintro ⟨T, W, H1, Hr⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hx
    obtain ⟨⟨hTU, hu0T⟩, ⟨hW, hWne⟩, ⟨h1, c1⟩, ⟨hr, cr⟩⟩ := hx
    have ht : Tgt G v U u0 T H1 W Hr := ⟨hTU, hu0T, h1, c1, hW, hWne, hr, cr⟩
    simp only [Tf_Hb hv ht, W1f_Hb hv ht, H1f_Hb hv ht, Hrf_Hb hv ht]
  · intro H hHm
    rw [Finset.mem_filter, Finset.mem_powerset] at hHm
    have ht := tgt_forward (u0 := u0) hv hu0 hHm.1 hHm.2
    have hcard := card_Hb hv ht
    rw [Hb_forward hv hHm.1] at hcard
    simp only [hcard, pow_add]
    ring

/-! ### Basic values and invariance -/

section Invariance

theorem edgesIn_empty (G : SimpleGraph ι) : edgesIn G (∅ : Finset ι) = ∅ := by
  ext e
  simp only [mem_edgesIn, Finset.notMem_empty, iff_false, not_and]
  intro _ h
  induction e using Sym2.ind with
  | _ a b => exact (h a (Sym2.mem_mk_left a b)).elim

theorem edgesIn_singleton (G : SimpleGraph ι) (a : ι) : edgesIn G {a} = ∅ := by
  ext e
  simp only [mem_edgesIn, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
  intro he h
  induction e using Sym2.ind with
  | _ x y =>
    have hx := h x (Sym2.mem_mk_left x y)
    have hy := h y (Sym2.mem_mk_right x y)
    exact (G.mem_edgeSet.mp he).ne (hx.trans hy.symm)

theorem ursell_empty (G : SimpleGraph ι) : ursell G ∅ = 1 := by
  have : (edgesIn G (∅ : Finset ι)).powerset.filter (Conn ∅) = {∅} := by
    rw [edgesIn_empty]
    ext H
    simp only [Finset.powerset_empty, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  rw [ursell, this]
  simp

theorem ursell_singleton (G : SimpleGraph ι) (a : ι) : ursell G {a} = 1 := by
  have : (edgesIn G {a}).powerset.filter (Conn {a}) = {∅} := by
    rw [edgesIn_singleton]
    ext H
    simp only [Finset.powerset_empty, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      refine ⟨rfl, fun x hx y hy => ?_⟩
      rw [Finset.mem_singleton] at hx hy
      subst hx; subst hy; exact Rch.refl
  rw [ursell, this]
  simp

/-- The Ursell function only depends on the adjacency inside the vertex set. -/
theorem ursell_congr {G G' : SimpleGraph ι} {S : Finset ι}
    (h : ∀ x ∈ S, ∀ y ∈ S, G.Adj x y ↔ G'.Adj x y) : ursell G S = ursell G' S := by
  have : edgesIn G S = edgesIn G' S := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [mk_mem_edgesIn, mk_mem_edgesIn]
      constructor
      · rintro ⟨hab, ha, hb⟩; exact ⟨(h a ha b hb).mp hab, ha, hb⟩
      · rintro ⟨hab, ha, hb⟩; exact ⟨(h a ha b hb).mpr hab, ha, hb⟩
  rw [ursell, ursell, this]

end Invariance

section Comap

variable {ι' : Type*}

/-- The induced embedding on unordered pairs. -/
def sym2Emb (f : ι' ↪ ι) : Sym2 ι' ↪ Sym2 ι := ⟨Sym2.map f, Sym2.map.injective f.injective⟩

theorem sym2Emb_mk (f : ι' ↪ ι) (a b : ι') : sym2Emb f s(a, b) = s(f a, f b) := rfl

theorem edgesIn_map (f : ι' ↪ ι) (G : SimpleGraph ι) (S' : Finset ι') :
    edgesIn G (S'.map f) = (edgesIn (G.comap f) S').map (sym2Emb f) := by
  ext e
  rw [Finset.mem_map]
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hxy, hx, hy⟩ := mk_mem_edgesIn.mp he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      exact ⟨s(a, b), mk_mem_edgesIn.mpr ⟨by simpa using hxy, ha, hb⟩, rfl⟩
  · rintro ⟨e', he', rfl⟩
    induction e' using Sym2.ind with
    | _ a b =>
      obtain ⟨hab, ha, hb⟩ := mk_mem_edgesIn.mp he'
      exact mk_mem_edgesIn.mpr ⟨by simpa using hab, Finset.mem_map_of_mem _ ha,
        Finset.mem_map_of_mem _ hb⟩

theorem rch_map_iff (f : ι' ↪ ι) (H' : Finset (Sym2 ι')) (a b : ι') :
    Rch (H'.map (sym2Emb f)) (f a) (f b) ↔ Rch H' a b := by
  constructor
  · intro h
    have key : ∀ y, Rch (H'.map (sym2Emb f)) (f a) y → ∃ b, y = f b ∧ Rch H' a b := by
      intro y hy
      induction hy with
      | refl => exact ⟨a, rfl, Rch.refl⟩
      | @tail y z _ hyz ih =>
        obtain ⟨b, rfl, hb⟩ := ih
        obtain ⟨e', he', hee⟩ := Finset.mem_map.mp hyz
        induction e' using Sym2.ind with
        | _ p q =>
          rw [sym2Emb_mk] at hee
          rcases Sym2.eq_iff.mp hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have := f.injective h1
            subst this
            exact ⟨q, h2.symm, hb.trans (Rch.single he')⟩
          · have := f.injective h2
            subst this
            exact ⟨p, h1.symm, hb.trans (Rch.single (by rwa [Sym2.eq_swap]))⟩
    obtain ⟨b', hb', hr⟩ := key _ h
    rw [f.injective hb']
    exact hr
  · intro h
    induction h with
    | refl => exact Rch.refl
    | tail _ hbc ih =>
      exact ih.trans (Rch.single (Finset.mem_map.mpr ⟨_, hbc, rfl⟩))

/-- Invariance of the Ursell function under embeddings of the vertex type. -/
theorem ursell_comap (f : ι' ↪ ι) (G : SimpleGraph ι) (S' : Finset ι') :
    ursell (G.comap f) S' = ursell G (S'.map f) := by
  rw [ursell, ursell, edgesIn_map]
  refine Finset.sum_nbij (fun H => H.map (sym2Emb f)) ?_ ?_ ?_ ?_
  · intro H hH
    rw [Finset.mem_filter, Finset.mem_powerset] at hH ⊢
    refine ⟨Finset.map_subset_map.mpr hH.1, ?_⟩
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact (rch_map_iff f H a b).mpr (hH.2 a ha b hb)
  · intro H _ K _ hHK
    exact Finset.map_injective _ hHK
  · intro K hK
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hK
    refine ⟨(edgesIn (G.comap f) S').filter (fun e => sym2Emb f e ∈ K), ?_, ?_⟩
    · have hmap : ((edgesIn (G.comap f) S').filter (fun e => sym2Emb f e ∈ K)).map (sym2Emb f) = K := by
        ext x
        rw [Finset.mem_map]
        constructor
        · rintro ⟨e, he, rfl⟩
          exact (Finset.mem_filter.mp he).2
        · intro hx
          obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp (hK.1 hx)
          exact ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro a ha b hb
      rw [← rch_map_iff f, hmap]
      exact hK.2 _ (Finset.mem_map_of_mem _ ha) _ (Finset.mem_map_of_mem _ hb)
    · ext x
      rw [Finset.mem_map]
      constructor
      · rintro ⟨e, he, rfl⟩
        exact (Finset.mem_filter.mp he).2
      · intro hx
        obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp (hK.1 hx)
        exact ⟨e, Finset.mem_filter.mpr ⟨he, hx⟩, rfl⟩
  · intro H _
    rw [Finset.card_map]

end Comap

/-- Reachability along edges of `G` implies reachability in `G`. -/
theorem Rch.reachable [Fintype ι] {G : SimpleGraph ι} {H : Finset (Sym2 ι)} (hH : H ⊆ edgesIn G Finset.univ)
    {x y : ι} (h : Rch H x y) : G.Reachable x y := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hbc ih =>
    have := (mk_mem_edgesIn.mp (hH hbc)).1
    exact ih.trans (SimpleGraph.Adj.reachable this)

/-- The Ursell function of a disconnected graph vanishes. -/
theorem ursell_eq_zero_of_not_preconnected [Fintype ι] {G : SimpleGraph ι} (hG : ¬ G.Preconnected) :
    ursell G Finset.univ = 0 := by
  unfold ursell
  refine Finset.sum_eq_zero (fun H hH => ?_)
  exfalso
  rw [Finset.mem_filter, Finset.mem_powerset] at hH
  apply hG
  intro x y
  exact Rch.reachable hH.1 (hH.2 x (Finset.mem_univ _) y (Finset.mem_univ _))

end Balaban.Polymer
