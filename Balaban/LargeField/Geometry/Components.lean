module

public import Balaban.LargeField.Geometry.Small
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.Linarith

/-!
# Components (Part I, Definition I.2.11 and Lemma I.2.12)

For an integer width `ω` and a finite `X ⊂ 𝕋_k`, two points are *linked in `X`*
(`Linked ω X`) if there is a chain in `X` with consecutive index distances `< ω`. The components
`comps ω X : Finset (Finset _)` are the classes of this relation.

* `comps_sep` (a): distinct components are at distance `≥ ω`;
* `exists_comp_of_linked`, `comp_mono` (b);
* `exists_comp_of_close` (d);
* `comp_diam_le` (c): a component inside `ν` boxes of side `≤ b` has sup-diameter
  `≤ ν (b - 1) + (ν - 1)(ω - 1)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ}

/-- `x, y` are linked in `X` for the width `ω`: a chain in `X` with consecutive index distances
`< ω`. -/
def Linked (ω : ℕ) (X : Set (Torus d n)) : Torus d n → Torus d n → Prop :=
  Relation.ReflTransGen fun a b => a ∈ X ∧ b ∈ X ∧ supDist a b < ω

open Classical in
/-- The class of `x` in `X`: the points of `X` linked to `x`. -/
noncomputable def linkClass (ω : ℕ) (X : Finset (Torus d n)) (x : Torus d n) : Finset (Torus d n) :=
  X.filter fun y => Linked ω (X : Set (Torus d n)) x y

/-- The components of `X`: the classes of `Linked ω X` on `X`. -/
noncomputable def comps (ω : ℕ) (X : Finset (Torus d n)) : Finset (Finset (Torus d n)) :=
  X.image (linkClass ω X)

theorem mem_linkClass {ω : ℕ} {X : Finset (Torus d n)} {x y : Torus d n} :
    y ∈ linkClass ω X x ↔ y ∈ X ∧ Linked ω (X : Set (Torus d n)) x y := by
  classical
  simp [linkClass]

section Basic

variable {ω : ℕ}

theorem Linked.refl (x : Torus d n) {Z : Set (Torus d n)} : Linked ω Z x x :=
  Relation.ReflTransGen.refl

theorem Linked.trans {Z : Set (Torus d n)} {x y z : Torus d n} (h1 : Linked ω Z x y)
    (h2 : Linked ω Z y z) : Linked ω Z x z :=
  Relation.ReflTransGen.trans h1 h2

theorem Linked.single {Z : Set (Torus d n)} {x y : Torus d n} (hx : x ∈ Z) (hy : y ∈ Z)
    (h : supDist x y < ω) : Linked ω Z x y :=
  Relation.ReflTransGen.single ⟨hx, hy, h⟩

theorem Linked.mono {Z Z' : Set (Torus d n)} (hZ : Z ⊆ Z') {x y : Torus d n}
    (h : Linked ω Z x y) : Linked ω Z' x y := by
  induction h with
  | refl => exact Linked.refl _
  | tail _ hab ih => exact ih.trans (Linked.single (hZ hab.1) (hZ hab.2.1) hab.2.2)

theorem Linked.mem_left {Z : Set (Torus d n)} {x y : Torus d n} (h : Linked ω Z x y) (hne : x ≠ y) :
    x ∈ Z := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨hx, _, _⟩, _⟩
  · exact absurd h hne
  · exact hx

end Basic

section Comps

variable [NeZero n] {ω : ℕ} {X : Finset (Torus d n)}

theorem Linked.symm {Z : Set (Torus d n)} {x y : Torus d n} (h : Linked ω Z x y) :
    Linked ω Z y x := by
  induction h with
  | refl => exact Linked.refl _
  | tail _ hab ih =>
    exact (Linked.single hab.2.1 hab.1 (by rw [supDist_comm]; exact hab.2.2)).trans ih

theorem Linked.mem_right {Z : Set (Torus d n)} {x y : Torus d n} (h : Linked ω Z x y)
    (hne : x ≠ y) : y ∈ Z := h.symm.mem_left hne.symm

omit [NeZero n] in
theorem mem_comps_iff {Y : Finset (Torus d n)} :
    Y ∈ comps ω X ↔ ∃ x ∈ X, Y = linkClass ω X x := by
  unfold comps
  simp only [Finset.mem_image]
  constructor <;> rintro ⟨x, hx, h⟩ <;> exact ⟨x, hx, h.symm⟩

/-- Membership in the class of `y`. -/
theorem mem_comp_iff {Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) {y : Torus d n} (hy : y ∈ Y)
    {x : Torus d n} : x ∈ Y ↔ x ∈ X ∧ Linked ω (X : Set (Torus d n)) y x := by
  obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY
  rw [mem_linkClass] at hy ⊢
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, hy.2.symm.trans h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, hy.2.trans h⟩

omit [NeZero n] in
theorem comp_subset {Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) : Y ⊆ X := by
  obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY
  exact fun y hy => (mem_linkClass.mp hy).1

omit [NeZero n] in
theorem mem_comp_self {x : Torus d n} (hx : x ∈ X) :
    ∃ Y ∈ comps ω X, x ∈ Y :=
  ⟨_, mem_comps_iff.mpr ⟨x, hx, rfl⟩, mem_linkClass.mpr ⟨hx, Linked.refl _⟩⟩

omit [NeZero n] in
theorem comp_nonempty {Y : Finset (Torus d n)} (hY : Y ∈ comps ω X) : Y.Nonempty := by
  obtain ⟨z, hz, rfl⟩ := mem_comps_iff.mp hY
  exact ⟨z, mem_linkClass.mpr ⟨hz, Linked.refl _⟩⟩
/-- **Lemma I.2.12 (a)**: distinct components are at distance `≥ ω`. -/
theorem comps_sep {Y Y' : Finset (Torus d n)} (hY : Y ∈ comps ω X) (hY' : Y' ∈ comps ω X)
    (hne : Y ≠ Y') {y y' : Torus d n} (hy : y ∈ Y) (hy' : y' ∈ Y') : ω ≤ supDist y y' := by
  by_contra hlt
  push Not at hlt
  have hyX := comp_subset hY hy
  have hy'X := comp_subset hY' hy'
  have hl : Linked ω (X : Set (Torus d n)) y y' := Linked.single hyX hy'X hlt
  apply hne
  ext x
  rw [mem_comp_iff hY hy, mem_comp_iff hY' hy']
  constructor
  · rintro ⟨hx, h⟩; exact ⟨hx, hl.symm.trans h⟩
  · rintro ⟨hx, h⟩; exact ⟨hx, hl.trans h⟩

/-- **Lemma I.2.12 (d)**: points of `X` at distance `< ω` lie in the same component. -/
theorem exists_comp_of_close {x y : Torus d n} (hx : x ∈ X) (hy : y ∈ X) (h : supDist x y < ω) :
    ∃ Y ∈ comps ω X, x ∈ Y ∧ y ∈ Y := by
  obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := ω) hx
  exact ⟨Y, hY, hxY, (mem_comp_iff hY hxY).mpr ⟨hy, Linked.single hx hy h⟩⟩

/-- **Lemma I.2.12 (b)**: a set `S ⊆ X` whose points are pairwise linked in `X` lies in one
component (if nonempty). -/
theorem exists_comp_of_linked {S : Finset (Torus d n)} (hS : S ⊆ X) (hne : S.Nonempty)
    (hlink : ∀ s ∈ S, ∀ t ∈ S, Linked ω (X : Set (Torus d n)) s t) :
    ∃ Y ∈ comps ω X, S ⊆ Y := by
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨Y, hY, h0⟩ := mem_comp_self (ω := ω) (hS hs0)
  exact ⟨Y, hY, fun t ht => (mem_comp_iff hY h0).mpr ⟨hS ht, hlink s0 hs0 t ht⟩⟩

/-- **Lemma I.2.12 (b)**: if `X ⊆ X'`, each component of `X` lies in one component of `X'`. -/
theorem comp_mono {X' : Finset (Torus d n)} (hXX : X ⊆ X') {Y : Finset (Torus d n)}
    (hY : Y ∈ comps ω X) : ∃ Y' ∈ comps ω X', Y ⊆ Y' := by
  obtain ⟨y0, hy0⟩ := comp_nonempty hY
  obtain ⟨Y', hY', h0⟩ := mem_comp_self (ω := ω) (hXX (comp_subset hY hy0))
  refine ⟨Y', hY', fun t ht => (mem_comp_iff hY' h0).mpr ⟨hXX (comp_subset hY ht), ?_⟩⟩
  exact ((mem_comp_iff hY hy0).mp ht).2.mono (by exact_mod_cast hXX)

/-- Two points of a box of side `≤ b` are within `b - 1`. -/
theorem supDist_le_of_mem_box {a : Torus d n} {s : Fin d → ℕ} {b : ℕ} (hs : ∀ i, s i ≤ b)
    {y y' : Torus d n} (hy : y ∈ box a s) (hy' : y' ∈ box a s) : supDist y y' ≤ b - 1 := by
  refine supDist_le_iff.mpr fun i => (cycNorm_le_iff _ _).mpr ?_
  obtain ⟨j, hj, hyj⟩ := hy i
  obtain ⟨j', hj', hyj'⟩ := hy' i
  have h1 := hs i
  refine ⟨(j : ℤ) - j', ?_, ?_⟩
  · rw [abs_le]
    constructor <;> push_cast [Nat.cast_sub (by omega : 1 ≤ b)] <;> omega
  · rw [hyj, hyj']; push_cast; ring

/-- **Lemma I.2.12 (c)**: if a component `Y` lies in the union of `ν` boxes of side `≤ b`, then
its sup-diameter is `≤ ν (b - 1) + (ν - 1)(ω - 1)` (in particular `≤ ν (b + ω)`). -/
theorem comp_diam_le {ι : Type*} [Fintype ι] {b : ℕ} (hω : 1 ≤ ω) (a : ι → Torus d n)
    (s : ι → Fin d → ℕ) (hs : ∀ j i, s j i ≤ b) {Y : Finset (Torus d n)} (hY : Y ∈ comps ω X)
    (hcov : ∀ y ∈ Y, ∃ j, y ∈ box (a j) (s j)) :
    ∀ y ∈ Y, ∀ y' ∈ Y, supDist y y' ≤
      Fintype.card ι * (b - 1) + (Fintype.card ι - 1) * (ω - 1) := by
  classical
  let Adj : ι → ι → Prop := fun j k =>
    ∃ w ∈ Y, w ∈ box (a j) (s j) ∧ ∃ w' ∈ Y, w' ∈ box (a k) (s k) ∧ supDist w w' < ω
  let G : SimpleGraph ι := SimpleGraph.fromRel Adj
  -- reachability
  have hreach : ∀ y ∈ Y, ∀ j, y ∈ box (a j) (s j) → ∀ y', Linked ω (X : Set (Torus d n)) y y' →
      ∀ k, y' ∈ box (a k) (s k) → G.Reachable j k := by
    intro y hy j hyj y' hl
    induction hl with
    | refl =>
      intro k hyk
      by_cases hjk : j = k
      · subst hjk; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable
          ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hjk, Or.inl ⟨y, hy, hyj, y, hy, hyk, by
            rw [supDist_self]; omega⟩⟩)
    | @tail z y'' hyz hzy' ih =>
      intro k hy''k
      have hzY : z ∈ Y := (mem_comp_iff hY hy).mpr ⟨hzy'.1, hyz⟩
      have hy''Y : y'' ∈ Y := (mem_comp_iff hY hy).mpr ⟨hzy'.2.1, hyz.trans (Linked.single hzy'.1 hzy'.2.1 hzy'.2.2)⟩
      obtain ⟨c, hc⟩ := hcov z hzY
      have h1 := ih c hc
      by_cases hck : c = k
      · subst hck; exact h1
      · exact h1.trans (SimpleGraph.Adj.reachable
          ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hck, Or.inl ⟨z, hzY, hc, y'', hy''Y, hy''k, hzy'.2.2⟩⟩))
  -- walk bound
  have hwalk : ∀ (j k : ι) (p : G.Walk j k), ∀ y ∈ Y, ∀ y' ∈ Y, y ∈ box (a j) (s j) →
      y' ∈ box (a k) (s k) →
      supDist y y' ≤ (p.length + 1) * (b - 1) + p.length * (ω - 1) := by
    intro j k p
    induction p with
    | nil =>
      intro y _ y' _ hy hy'
      simpa using supDist_le_of_mem_box (hs _) hy hy'
    | @cons j k' k hadj p ih =>
      intro y hy y' hy' hyj hyk
      obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).mp hadj
      obtain ⟨w, hwY, hwj, w', hw'Y, hw'k, hww⟩ : ∃ w ∈ Y, w ∈ box (a j) (s j) ∧
          ∃ w' ∈ Y, w' ∈ box (a k') (s k') ∧ supDist w w' < ω := by
        rcases hr with h | ⟨w, hw, hwk, w', hw', hw'k, hd⟩
        · exact h
        · exact ⟨w', hw', hw'k, w, hw, hwk, by rw [supDist_comm]; exact hd⟩
      have h1 := supDist_le_of_mem_box (hs _) hyj hwj
      have h2 := ih w' hw'Y y' hy' hw'k hyk
      have h3 := supDist_triangle y w y'
      have h4 := supDist_triangle w w' y'
      rw [SimpleGraph.Walk.length_cons]
      have : (p.length + 1 + 1) * (b - 1) + (p.length + 1) * (ω - 1) =
          (b - 1) + (ω - 1) + ((p.length + 1) * (b - 1) + p.length * (ω - 1)) := by ring
      rw [this]
      omega
  intro y hy y' hy'
  obtain ⟨j, hj⟩ := hcov y hy
  obtain ⟨k, hk⟩ := hcov y' hy'
  obtain ⟨q⟩ := hreach y hy j hj y' (((mem_comp_iff hY hy).mp hy').2) k hk
  have hlt := q.bypass_isPath.length_lt
  have hb := hwalk j k q.bypass y hy y' hy' hj hk
  set L := q.bypass.length with hL
  calc supDist y y' ≤ (L + 1) * (b - 1) + L * (ω - 1) := hb
    _ ≤ Fintype.card ι * (b - 1) + (Fintype.card ι - 1) * (ω - 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (Nat.mul_le_mul_right _ (by omega))

end Comps

end Balaban.LargeField
