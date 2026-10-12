module

public import Balaban.LargeField.Geometry.Components
import Mathlib.Tactic.Linarith

/-!
# Hull rounds and the hull closure (Part I, Definitions I.3.2-I.3.3, Lemma I.3.4)

For the width `ω` and the critical side `b`, one *hull round* adds the hull box of every small
component of side `≤ b`:
`H_b(X) = X ∪ ⋃ {Hull(C) : C a component of X, C small, side C ≤ b}`.
The *hull closure* `Hull_b(X)` is the `N`-fold iterate, `N = |𝕋|`. (Version 1.1 of Part I labels the
closure as an extension of P6 p. 22, audit P1-06.)

Main results:
* `Balaban.LargeField.hullRound`, `hullClosure`, `hulledIn`;
* `box_linked`, `hull_linked`: a box is linked for every `ω ≥ 2`;
* `hullClosure_fixed`, `hullClosure_box`, `hullRound_comp_iff`, `hullClosure_comp_contains`
  (Lemma I.3.4 (a)-(d));
* `hullClosure_inter_comp`: the closure of `X ∩ Z'`, `Z'` a component of the closure, is `Z'`
  (used for locality, Lemma I.3.9 (c)).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ}

section Fin

variable [NeZero n]

/-- The finite set underlying a set of the finite torus. -/
noncomputable def finOf (X : Set (Torus d n)) : Finset (Torus d n) := (Set.toFinite X).toFinset

@[simp] theorem mem_finOf {X : Set (Torus d n)} {x : Torus d n} : x ∈ finOf X ↔ x ∈ X := by
  simp [finOf]

@[simp] theorem coe_finOf (X : Set (Torus d n)) : (finOf X : Set (Torus d n)) = X := by
  ext; simp

theorem finOf_subset_finOf {X Y : Set (Torus d n)} (h : X ⊆ Y) : finOf X ⊆ finOf Y := by
  intro x hx; rw [mem_finOf] at hx ⊢; exact h hx

end Fin

/-! ### Boxes are linked -/

section Box

variable [NeZero n] {ω : ℕ}

theorem supDist_update_le_one (x : Torus d n) (i : Fin d) (c c' : ZMod n)
    (h : c' = c + 1) : supDist (Function.update x i c) (Function.update x i c') ≤ 1 := by
  refine supDist_le_iff.mpr fun j => ?_
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    rw [h, show c - (c + 1) = -1 by ring, cycNorm_neg]
    exact (cycNorm_le_iff _ _).mpr ⟨1, by simp, by simp⟩
  · simp [Function.update_of_ne hj, cycNorm]

omit [NeZero n] in
theorem box_update_mem {a : Torus d n} {s : Fin d → ℕ} {x : Torus d n} (i : Fin d) {q : ℕ}
    (hq : q < s i) (hx : x ∈ box a s) : Function.update x i (a i + (q : ZMod n)) ∈ box a s := by
  intro j
  by_cases hj : j = i
  · subst hj; exact ⟨q, hq, by simp⟩
  · simp only [Function.update_of_ne hj]; exact hx j

/-- Moving one coordinate inside a box. -/
theorem box_linked_coord (hω : 2 ≤ ω) {a : Torus d n} {s : Fin d → ℕ} {x : Torus d n}
    (hx : x ∈ box a s) (i : Fin d) {q : ℕ} (hq : q < s i) :
    Linked ω (box a s) x (Function.update x i (a i + (q : ZMod n))) := by
  obtain ⟨p, hp, hxp⟩ := hx i
  set f : ℕ → Torus d n := fun q => Function.update x i (a i + (q : ZMod n)) with hf
  have hxf : x = f p := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [hf, hxp]
    · simp [hf, Function.update_of_ne hj]
  have key : ∀ q, q < s i → Linked ω (box a s) (f 0) (f q) := by
    intro q
    induction q with
    | zero => intro _; exact Linked.refl _
    | succ q ih =>
      intro hq
      refine (ih (by omega)).trans (Linked.single (box_update_mem i (by omega) hx)
        (box_update_mem i hq hx) ?_)
      have h1 : supDist (f q) (f (q + 1)) ≤ 1 :=
        supDist_update_le_one x i (a i + (q : ZMod n)) (a i + ((q + 1 : ℕ) : ZMod n))
          (by push_cast; ring)
      omega
  have h := (key p hp).symm.trans (key q hq)
  rw [← hxf] at h
  exact h

/-- Any two points of a box are linked inside it (for `ω ≥ 2`). -/
theorem box_linked (hω : 2 ≤ ω) {a : Torus d n} {s : Fin d → ℕ} {x y : Torus d n}
    (hx : x ∈ box a s) (hy : y ∈ box a s) : Linked ω (box a s) x y := by
  classical
  let z : Finset (Fin d) → Torus d n := fun S => fun i => if i ∈ S then y i else x i
  have hz : ∀ S, z S ∈ box a s := by
    intro S i
    by_cases hi : i ∈ S
    · simpa [z, hi] using hy i
    · simpa [z, hi] using hx i
  have key : ∀ S, Linked ω (box a s) x (z S) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact Linked.refl _
    | insert i S hi ih =>
      refine ih.trans ?_
      obtain ⟨q, hq, hyq⟩ := hy i
      have e : z (insert i S) = Function.update (z S) i (a i + (q : ZMod n)) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [z, hyq]
        · simp [z, hj]
      rw [e]
      exact box_linked_coord hω (hz S) i hq
  have e : z Finset.univ = y := by funext i; simp [z]
  simpa [e] using key Finset.univ

theorem hull_linked (hω : 2 ≤ ω) {X : Set (Torus d n)} (hne : X.Nonempty) (hX : IsSmall X)
    {x y : Torus d n} (hx : x ∈ hull X) (hy : y ∈ hull X) : Linked ω (hull X) x y := by
  obtain ⟨a, s, h, -, -⟩ := hull_eq_box hne hX
  rw [h] at hx hy ⊢
  exact box_linked hω hx hy

end Box

/-! ### Components: small facts -/

section Comps

variable [NeZero n] {ω : ℕ} {X : Finset (Torus d n)}

/-- Components are closed under `ω`-close points of `X`. -/
theorem mem_comp_of_close {Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) {y z : Torus d n}
    (hy : y ∈ Y) (hz : z ∈ X) (h : supDist y z < ω) : z ∈ Y :=
  (mem_comp_iff hY hy).mpr ⟨hz, Linked.single (comp_subset hY hy) hz h⟩

theorem comp_eq_of_mem {Y Y' : Finset (Torus d n)} (hY : Y ∈ comps ω X) (hY' : Y' ∈ comps ω X)
    {y : Torus d n} (hy : y ∈ Y) (hy' : y ∈ Y') : Y = Y' := by
  ext x
  rw [mem_comp_iff hY hy, mem_comp_iff hY' hy']

theorem mem_comp_of_linked {Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) {y z : Torus d n}
    (hy : y ∈ Y) (hz : z ∈ X) (h : Linked ω (X : Set (Torus d n)) y z) : z ∈ Y :=
  (mem_comp_iff hY hy).mpr ⟨hz, h⟩

end Comps

/-! ### Hull rounds and closure -/

section Closure

variable [NeZero n]

/-- One hull round `H_b(X)` (Definition I.3.2). -/
noncomputable def hullRound (ω b : ℕ) (X : Set (Torus d n)) : Set (Torus d n) :=
  X ∪ {y | ∃ Y ∈ comps ω (finOf X), IsSmall (Y : Set (Torus d n)) ∧
    side (Y : Set (Torus d n)) ≤ b ∧ y ∈ hull (Y : Set (Torus d n))}

/-- The canonical hull closure `Hull_b(X) = X_N`, `N = |𝕋|` (Definition I.3.3). -/
noncomputable def hullClosure (ω b : ℕ) (X : Set (Torus d n)) : Set (Torus d n) :=
  (hullRound ω b)^[Fintype.card (Torus d n)] X

/-- `C` is *hulled in round `t`*: a small component of `X_t` of side `≤ b`. -/
def hulledIn (ω b : ℕ) (X : Set (Torus d n)) (t : ℕ) (C : Finset (Torus d n)) : Prop :=
  C ∈ comps ω (finOf ((hullRound ω b)^[t] X)) ∧ IsSmall (C : Set (Torus d n)) ∧
    side (C : Set (Torus d n)) ≤ b

variable {ω b : ℕ}

theorem subset_hullRound (X : Set (Torus d n)) : X ⊆ hullRound ω b X := Set.subset_union_left

theorem iter_mono_of_le (X : Set (Torus d n)) {s t : ℕ} (h : s ≤ t) :
    (hullRound ω b)^[s] X ⊆ (hullRound ω b)^[t] X := by
  induction t, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ t _ ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (subset_hullRound _)

theorem subset_hullClosure (X : Set (Torus d n)) : X ⊆ hullClosure ω b X :=
  iter_mono_of_le X (Nat.zero_le _)

/-- Stabilization: once a round does not change the set, it never does. -/
theorem iter_stable {X : Set (Torus d n)} {t : ℕ}
    (h : (hullRound ω b)^[t + 1] X = (hullRound ω b)^[t] X) (s : ℕ) (hs : t ≤ s) :
    (hullRound ω b)^[s] X = (hullRound ω b)^[t] X := by
  induction s, hs using Nat.le_induction with
  | base => rfl
  | succ s _ ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [Function.iterate_succ_apply'] at h
    exact h

/-- **Lemma I.3.4 (a)**: `X_{N+1} = X_N`. -/
theorem hullRound_closure_eq (X : Set (Torus d n)) :
    hullRound ω b (hullClosure ω b X) = hullClosure ω b X := by
  set N := Fintype.card (Torus d n) with hN
  have key : (hullRound ω b)^[N + 1] X = (hullRound ω b)^[N] X := by
    by_contra hne
    have hstrict : ∀ t ≤ N, (hullRound ω b)^[t] X ≠ (hullRound ω b)^[t + 1] X := by
      intro t ht heq
      apply hne
      have h1 := iter_stable (ω := ω) (b := b) (X := X) (t := t) heq.symm
      rw [h1 (N + 1) (by omega), h1 N ht]
    have hcard : ∀ t ≤ N + 1, t ≤ ((hullRound ω b)^[t] X).ncard := by
      intro t
      induction t with
      | zero => intro _; exact Nat.zero_le _
      | succ t ih =>
        intro ht
        have h1 := ih (by omega)
        have h2 : (hullRound ω b)^[t] X ⊂ (hullRound ω b)^[t + 1] X :=
          ssubset_of_subset_of_ne (iter_mono_of_le X (Nat.le_succ t)) (hstrict t (by omega))
        have := Set.ncard_lt_ncard h2 (Set.toFinite _)
        omega
    have h1 := hcard (N + 1) le_rfl
    have h2 : ((hullRound ω b)^[N + 1] X).ncard ≤ N := by
      rw [hN, ← Nat.card_eq_fintype_card]
      exact Set.ncard_le_card _
    omega
  show hullRound ω b ((hullRound ω b)^[N] X) = (hullRound ω b)^[N] X
  rw [← Function.iterate_succ_apply' (hullRound ω b) N X]
  exact key

theorem iter_subset_hullClosure (X : Set (Torus d n)) {t : ℕ} (ht : t ≤ Fintype.card (Torus d n)) :
    (hullRound ω b)^[t] X ⊆ hullClosure ω b X := iter_mono_of_le X ht

/-- Hull boxes of the small components of a set lie in the next round. -/
theorem hull_subset_hullRound {X : Set (Torus d n)} {Y : Finset (Torus d n)}
    (hY : Y ∈ comps ω (finOf X)) (hs : IsSmall (Y : Set (Torus d n)))
    (hb : side (Y : Set (Torus d n)) ≤ b) : hull (Y : Set (Torus d n)) ⊆ hullRound ω b X :=
  fun _ hy => Or.inr ⟨Y, hY, hs, hb, hy⟩

/-- A box through a point of a component of a superset lies in that component. -/
theorem hull_subset_comp (hω : 2 ≤ ω) {X : Set (Torus d n)} {Y : Finset (Torus d n)}
    (hY : Y ∈ comps ω (finOf X)) (hs : IsSmall (Y : Set (Torus d n)))
    (hsub : hull (Y : Set (Torus d n)) ⊆ X) : hull (Y : Set (Torus d n)) ⊆ (Y : Set (Torus d n)) := by
  obtain ⟨y0, hy0⟩ := comp_nonempty hY
  intro y hy
  have hl := hull_linked hω ⟨y0, hy0⟩ hs (subset_hull _ hy0) hy
  have hl' : Linked ω ((finOf X : Finset (Torus d n)) : Set (Torus d n)) y0 y := by
    rw [coe_finOf]; exact hl.mono hsub
  exact mem_comp_of_linked hY hy0 (mem_finOf.mpr (hsub hy)) hl'

/-- **Lemma I.3.4 (b)**: every small component of side `≤ b` of the closure is a box. -/
theorem hullClosure_box (hω : 2 ≤ ω) (X : Set (Torus d n)) {C : Finset (Torus d n)}
    (hC : C ∈ comps ω (finOf (hullClosure ω b X))) (hs : IsSmall (C : Set (Torus d n)))
    (hb : side (C : Set (Torus d n)) ≤ b) : (C : Set (Torus d n)) = hull (C : Set (Torus d n)) := by
  have hsub : hull (C : Set (Torus d n)) ⊆ hullClosure ω b X := by
    have := hull_subset_hullRound hC hs hb
    rwa [hullRound_closure_eq] at this
  exact Set.Subset.antisymm (subset_hull _) (hull_subset_comp hω hC hs hsub)

/-- **Lemma I.3.4 (c)**, first part: a component of `X` lies in a component of `H_b(X)`. -/
theorem comp_subset_comp_hullRound {X : Set (Torus d n)} {C : Finset (Torus d n)}
    (hC : C ∈ comps ω (finOf X)) : ∃ C' ∈ comps ω (finOf (hullRound ω b X)), C ⊆ C' :=
  comp_mono (finOf_subset_finOf (subset_hullRound X)) hC

/-- **Lemma I.3.4 (c)**, second part: a component `C'` of `H_b(X)` is the union of the components
of `X` contained in it and of the hull boxes of those of them that are small of side `≤ b`. -/
theorem hullRound_comp_iff (hω : 2 ≤ ω) {X : Set (Torus d n)} {C' : Finset (Torus d n)}
    (hC' : C' ∈ comps ω (finOf (hullRound ω b X))) {y : Torus d n} :
    y ∈ C' ↔ ∃ C ∈ comps ω (finOf X), C ⊆ C' ∧ (y ∈ C ∨ (IsSmall (C : Set (Torus d n)) ∧
      side (C : Set (Torus d n)) ≤ b ∧ y ∈ hull (C : Set (Torus d n)))) := by
  constructor
  · intro hy
    have hyH := comp_subset hC' hy
    rw [mem_finOf] at hyH
    rcases hyH with hyX | ⟨Y, hY, hs, hb, hyY⟩
    · obtain ⟨C, hC, hyC⟩ := mem_comp_self (ω := ω) (mem_finOf.mpr hyX)
      obtain ⟨C'', hC'', hCC''⟩ := comp_subset_comp_hullRound (b := b) hC
      have : C'' = C' := comp_eq_of_mem hC'' hC' (hCC'' hyC) hy
      exact ⟨C, hC, this ▸ hCC'', Or.inl hyC⟩
    · obtain ⟨y0, hy0⟩ := comp_nonempty hY
      obtain ⟨C'', hC'', hYC''⟩ := comp_subset_comp_hullRound (b := b) hY
      have hsub := hull_subset_hullRound (b := b) hY hs hb
      have hl := hull_linked hω ⟨y0, hy0⟩ hs (subset_hull _ hy0) hyY
      have hl' : Linked ω ((finOf (hullRound ω b X) : Finset (Torus d n)) : Set (Torus d n)) y0 y := by
        rw [coe_finOf]; exact hl.mono hsub
      have hyC'' : y ∈ C'' := mem_comp_of_linked hC'' (hYC'' hy0) (mem_finOf.mpr (hsub hyY)) hl'
      have : C'' = C' := comp_eq_of_mem hC'' hC' hyC'' hy
      exact ⟨Y, hY, this ▸ hYC'', Or.inr ⟨hs, hb, hyY⟩⟩
  · rintro ⟨C, hC, hCC', hy | ⟨hs, hb, hyY⟩⟩
    · exact hCC' hy
    · obtain ⟨y0, hy0⟩ := comp_nonempty hC
      have hsub := hull_subset_hullRound (b := b) hC hs hb
      have hl := hull_linked hω ⟨y0, hy0⟩ hs (subset_hull _ hy0) hyY
      have hl' : Linked ω ((finOf (hullRound ω b X) : Finset (Torus d n)) : Set (Torus d n)) y0 y := by
        rw [coe_finOf]; exact hl.mono hsub
      exact mem_comp_of_linked hC' (hCC' hy0) (mem_finOf.mpr (hsub hyY)) hl'

/-- **Lemma I.3.4 (c)**, third part: every component of `X_t` (`t ≤ N`... any `t`) contains a
component of `X`. -/
theorem iter_comp_contains (hω : 2 ≤ ω) (X : Set (Torus d n)) (t : ℕ)
    {C' : Finset (Torus d n)} (hC' : C' ∈ comps ω (finOf ((hullRound ω b)^[t] X))) :
    ∃ C ∈ comps ω (finOf X), C ⊆ C' := by
  induction t generalizing C' with
  | zero => exact ⟨C', hC', subset_rfl⟩
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at hC'
    obtain ⟨y, hy⟩ := comp_nonempty hC'
    obtain ⟨C, hC, hCC', -⟩ := (hullRound_comp_iff hω hC').mp hy
    obtain ⟨C0, hC0, hC0C⟩ := ih hC
    exact ⟨C0, hC0, hC0C.trans hCC'⟩

/-- **Lemma I.3.4 (c)**: every component of the closure contains a component of `X`. -/
theorem hullClosure_comp_contains (hω : 2 ≤ ω) (X : Set (Torus d n)) {C' : Finset (Torus d n)}
    (hC' : C' ∈ comps ω (finOf (hullClosure ω b X))) : ∃ C ∈ comps ω (finOf X), C ⊆ C' :=
  iter_comp_contains hω X _ hC'

/-! ### Locality of the closure -/

/-- Inside a component `Z'` of a superset, linkage in `A` and in `A ∩ Z'` agree. -/
theorem linked_inter_comp {A Xc : Set (Torus d n)} {Z' : Finset (Torus d n)}
    (hA : A ⊆ Xc) (hZ' : Z' ∈ comps ω (finOf Xc)) {x y : Torus d n} (hx : x ∈ Z')
    (h : Linked ω A x y) : y ∈ Z' ∧ Linked ω (A ∩ (Z' : Set (Torus d n))) x y := by
  induction h with
  | refl => exact ⟨hx, Linked.refl _⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hl⟩ := ih
    refine ⟨mem_comp_of_close hZ' hb (mem_finOf.mpr (hA hbc.2.1)) hbc.2.2, ?_⟩
    exact hl.trans (Linked.single ⟨hbc.1, hb⟩ ⟨hbc.2.1,
      mem_comp_of_close hZ' hb (mem_finOf.mpr (hA hbc.2.1)) hbc.2.2⟩ hbc.2.2)

/-- One round commutes with intersection with a component of a superset that contains
the round's output. -/
theorem hullRound_inter_comp (hω : 2 ≤ ω) {A Xc : Set (Torus d n)} {Z' : Finset (Torus d n)}
    (hA : A ⊆ Xc) (hHA : hullRound ω b A ⊆ Xc) (hZ' : Z' ∈ comps ω (finOf Xc)) :
    hullRound ω b (A ∩ (Z' : Set (Torus d n))) = hullRound ω b A ∩ (Z' : Set (Torus d n)) := by
  -- comps of `A ∩ Z'` through a point `c` of `Z'`
  have hcls : ∀ c ∈ Z', c ∈ A → linkClass ω (finOf A) c = linkClass ω (finOf (A ∩ (Z' : Set _))) c := by
    intro c hc hcA
    ext y
    rw [mem_linkClass, mem_linkClass]
    constructor
    · rintro ⟨hy, hl⟩
      rw [coe_finOf] at hl
      obtain ⟨hyZ, hl'⟩ := linked_inter_comp hA hZ' hc hl
      exact ⟨mem_finOf.mpr ⟨mem_finOf.mp hy, hyZ⟩, by rw [coe_finOf]; exact hl'⟩
    · rintro ⟨hy, hl⟩
      rw [coe_finOf] at hl
      exact ⟨mem_finOf.mpr (mem_finOf.mp hy).1, by rw [coe_finOf]; exact hl.mono Set.inter_subset_left⟩
  ext y
  constructor
  · rintro (hy | ⟨Y', hY', hs, hb, hyY'⟩)
    · exact ⟨subset_hullRound _ hy.1, hy.2⟩
    · obtain ⟨c, hc⟩ := comp_nonempty hY'
      have hcA : c ∈ A ∩ (Z' : Set _) := mem_finOf.mp (comp_subset hY' hc)
      obtain ⟨Y, hY, hcY⟩ := mem_comp_self (ω := ω) (mem_finOf.mpr hcA.1)
      have hYeq : Y = Y' := by
        obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY'
        have hzc : c ∈ linkClass ω (finOf (A ∩ (Z' : Set _))) z := hc
        have : linkClass ω (finOf (A ∩ (Z' : Set _))) z = linkClass ω (finOf (A ∩ (Z' : Set _))) c := by
          ext w
          rw [mem_linkClass, mem_linkClass]
          have hl := (mem_linkClass.mp hzc).2
          constructor
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.symm.trans hl2⟩
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.trans hl2⟩
        rw [this, ← hcls c hcA.2 hcA.1]
        obtain ⟨z', hz', rfl⟩ := mem_comps_iff.mp hY
        have : linkClass ω (finOf A) z' = linkClass ω (finOf A) c := by
          ext w
          rw [mem_linkClass, mem_linkClass]
          have hl := (mem_linkClass.mp hcY).2
          constructor
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.symm.trans hl2⟩
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.trans hl2⟩
        exact this
      subst hYeq
      have hyH : y ∈ hullRound ω b A := hull_subset_hullRound hY hs hb hyY'
      refine ⟨hyH, ?_⟩
      have hsubA : hull (Y : Set (Torus d n)) ⊆ Xc := fun z hz => hHA (hull_subset_hullRound hY hs hb hz)
      have hl := hull_linked hω ⟨c, hc⟩ hs (subset_hull _ hc) hyY'
      have hl' : Linked ω ((finOf Xc : Finset (Torus d n)) : Set (Torus d n)) c y := by
        rw [coe_finOf]; exact hl.mono hsubA
      exact mem_comp_of_linked hZ' hcA.2 (mem_finOf.mpr (hsubA hyY')) hl'
  · rintro ⟨hy | ⟨Y, hY, hs, hb, hyY⟩, hyZ⟩
    · exact Or.inl ⟨hy, hyZ⟩
    · right
      obtain ⟨c, hc⟩ := comp_nonempty hY
      have hcA : c ∈ A := mem_finOf.mp (comp_subset hY hc)
      have hsubA : hull (Y : Set (Torus d n)) ⊆ Xc := fun z hz => hHA (hull_subset_hullRound hY hs hb hz)
      have hl := hull_linked hω ⟨c, hc⟩ hs (subset_hull _ hc) hyY
      have hl' : Linked ω ((finOf Xc : Finset (Torus d n)) : Set (Torus d n)) y c := by
        rw [coe_finOf]; exact hl.symm.mono hsubA
      have hcZ : c ∈ Z' := mem_comp_of_linked hZ' hyZ (mem_finOf.mpr (hA hcA)) hl'
      have hY2 : Y ∈ comps ω (finOf (A ∩ (Z' : Set _))) := by
        obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY
        have hzY : c ∈ linkClass ω (finOf A) z := hc
        have e1 : linkClass ω (finOf A) z = linkClass ω (finOf A) c := by
          ext w
          rw [mem_linkClass, mem_linkClass]
          have hl := (mem_linkClass.mp hzY).2
          constructor
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.symm.trans hl2⟩
          · rintro ⟨hw, hl2⟩; exact ⟨hw, hl.trans hl2⟩
        rw [e1, hcls c hcZ hcA]
        exact mem_comps_iff.mpr ⟨c, mem_finOf.mpr ⟨hcA, hcZ⟩, rfl⟩
      exact ⟨Y, hY2, hs, hb, hyY⟩

/-- **Locality of the closure** (used for Lemma I.3.9 (c)): if `Z'` is a component of
`Hull_b(X)`, then the closure of `X ∩ Z'` is `Z'`. -/
theorem hullClosure_inter_comp (hω : 2 ≤ ω) (X : Set (Torus d n)) {Z' : Finset (Torus d n)}
    (hZ' : Z' ∈ comps ω (finOf (hullClosure ω b X))) :
    hullClosure ω b (X ∩ (Z' : Set (Torus d n))) = (Z' : Set (Torus d n)) := by
  set N := Fintype.card (Torus d n) with hN
  have hZsub : (Z' : Set (Torus d n)) ⊆ hullClosure ω b X := by
    intro z hz; exact mem_finOf.mp (comp_subset hZ' hz)
  have key : ∀ t ≤ N, (hullRound ω b)^[t] (X ∩ (Z' : Set (Torus d n))) =
      (hullRound ω b)^[t] X ∩ (Z' : Set (Torus d n)) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      exact hullRound_inter_comp hω (iter_subset_hullClosure X (by omega))
        (by rw [← Function.iterate_succ_apply' (hullRound ω b) t X]
            exact iter_subset_hullClosure X ht) hZ'
  show (hullRound ω b)^[N] (X ∩ (Z' : Set (Torus d n))) = _
  rw [key N le_rfl]
  exact Set.inter_eq_right.mpr hZsub

end Closure

end Balaban.LargeField
