/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PolymerGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Connected lattice structures, tree length and (GM2) (LOCALIZATION.md §4.2)

A *connected structure* `(W, E)` on the torus is a nonempty finite set `W` of sites together with
a finite set `E` of oriented nearest-neighbour bonds between sites of `W` such that `W` is
connected through `E`.  Its *cost* for a bond weight `ω` is `∑_{(x,y) ∈ E} ω x y`.  A spanning tree
of `(W, E)` has no larger cost, so infima over connected structures equal infima over trees
(the only property of trees used is connectedness).  `Covers R ω c A` says that some connected
structure inside the region `R`, of cost at most `c`, contains the set `A`; `Linked R ω c x y` is
`Covers R ω c {x, y}`.

`assemble` is the combinatorial heart of (GM2): nodes of a connected "nerve" carry covers, adjacent
nodes are linked at cost `ρ`, and then all node sets are covered at cost `∑ σ + (#nodes - 1) ρ`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section Struct

variable {d n : ℕ}

/-- A connected lattice structure: vertices `W`, oriented bonds `E`. -/
def ConnStruct (W : Finset (Torus d n)) (E : Finset (Torus d n × Torus d n)) : Prop :=
  W.Nonempty ∧ (∀ p ∈ E, p.1 ∈ W ∧ p.2 ∈ W ∧ Nbr p.1 p.2) ∧
    ∀ x ∈ W, ∀ y ∈ W, Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x y

/-- The cost of a set of bonds for the weight `ω`. -/
def bondCost (ω : Torus d n → Torus d n → ℝ) (E : Finset (Torus d n × Torus d n)) : ℝ :=
  ∑ p ∈ E, ω p.1 p.2

theorem bondCost_union_le {ω : Torus d n → Torus d n → ℝ} (hω : ∀ x y, 0 ≤ ω x y)
    (E E' : Finset (Torus d n × Torus d n)) :
    bondCost ω (E ∪ E') ≤ bondCost ω E + bondCost ω E' := by
  unfold bondCost
  have := Finset.sum_union_inter (s₁ := E) (s₂ := E') (f := fun p => ω p.1 p.2)
  have h0 : 0 ≤ ∑ p ∈ E ∩ E', ω p.1 p.2 := Finset.sum_nonneg fun p _ => hω _ _
  linarith

theorem ConnStruct.union {W W' : Finset (Torus d n)} {E E' : Finset (Torus d n × Torus d n)}
    (h : ConnStruct W E) (h' : ConnStruct W' E') (hz : ∃ z, z ∈ W ∧ z ∈ W') :
    ConnStruct (W ∪ W') (E ∪ E') := by
  refine ⟨h.1.mono Finset.subset_union_left, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨a, b, c⟩ := h.2.1 p hp
      exact ⟨Finset.mem_union_left _ a, Finset.mem_union_left _ b, c⟩
    · obtain ⟨a, b, c⟩ := h'.2.1 p hp
      exact ⟨Finset.mem_union_right _ a, Finset.mem_union_right _ b, c⟩
  · obtain ⟨z, hzW, hzW'⟩ := hz
    have hsymm : ∀ a b : Torus d n, ((a, b) ∈ E ∪ E' ∨ (b, a) ∈ E ∪ E') →
        ((b, a) ∈ E ∪ E' ∨ (a, b) ∈ E ∪ E') := fun a b h => h.symm
    have m1 : ∀ x y, Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x y →
        Relation.ReflTransGen (fun a b => (a, b) ∈ E ∪ E' ∨ (b, a) ∈ E ∪ E') x y := fun x y hxy =>
      Relation.ReflTransGen.mono (fun a b hab => by
        rcases hab with hab | hab
        · exact Or.inl (Finset.mem_union_left _ hab)
        · exact Or.inr (Finset.mem_union_left _ hab)) x y hxy
    have m2 : ∀ x y, Relation.ReflTransGen (fun a b => (a, b) ∈ E' ∨ (b, a) ∈ E') x y →
        Relation.ReflTransGen (fun a b => (a, b) ∈ E ∪ E' ∨ (b, a) ∈ E ∪ E') x y := fun x y hxy =>
      Relation.ReflTransGen.mono (fun a b hab => by
        rcases hab with hab | hab
        · exact Or.inl (Finset.mem_union_right _ hab)
        · exact Or.inr (Finset.mem_union_right _ hab)) x y hxy
    have toZ : ∀ x ∈ W ∪ W', Relation.ReflTransGen
        (fun a b => (a, b) ∈ E ∪ E' ∨ (b, a) ∈ E ∪ E') x z := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact m1 _ _ (h.2.2 x hx z hzW)
      · exact m2 _ _ (h'.2.2 x hx z hzW')
    intro x hx y hy
    exact (toZ x hx).trans (rtg_symm (fun a b hab => hab.symm) (toZ y hy))

theorem connStruct_singleton (x : Torus d n) : ConnStruct ({x} : Finset (Torus d n)) ∅ := by
  refine ⟨Finset.singleton_nonempty _, by simp, ?_⟩
  intro a ha b hb
  rw [Finset.mem_singleton] at ha hb
  rw [ha, hb]

theorem connStruct_edge {x y : Torus d n} (h : Nbr x y) :
    ConnStruct ({x, y} : Finset (Torus d n)) {(x, y)} := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨by simp, by simp, h⟩
  · intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    have hxy : Relation.ReflTransGen (fun a b => (a, b) ∈ ({(x, y)} : Finset _) ∨
        (b, a) ∈ ({(x, y)} : Finset _)) x y :=
      Relation.ReflTransGen.single (Or.inl (by simp))
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hxy
    · exact rtg_symm (fun a b hab => hab.symm) hxy
    · exact Relation.ReflTransGen.refl

variable (R : Set (Torus d n)) (ω : Torus d n → Torus d n → ℝ)

/-- Some connected structure inside `R` of cost at most `c` contains `A`. -/
def Covers (c : ℝ) (A : Finset (Torus d n)) : Prop :=
  ∃ W E, ConnStruct W E ∧ (↑W ⊆ R) ∧ A ⊆ W ∧ bondCost ω E ≤ c

/-- `x` and `y` lie in a common connected structure in `R` of cost at most `c`. -/
def Linked (c : ℝ) (x y : Torus d n) : Prop := Covers R ω c {x, y}

variable {R ω}

theorem Covers.mono_A {c : ℝ} {A B : Finset (Torus d n)} (h : Covers R ω c A) (hB : B ⊆ A) :
    Covers R ω c B := by
  obtain ⟨W, E, h1, h2, h3, h4⟩ := h
  exact ⟨W, E, h1, h2, hB.trans h3, h4⟩

theorem Covers.mono_c {c c' : ℝ} {A : Finset (Torus d n)} (h : Covers R ω c A) (hc : c ≤ c') :
    Covers R ω c' A := by
  obtain ⟨W, E, h1, h2, h3, h4⟩ := h
  exact ⟨W, E, h1, h2, h3, h4.trans hc⟩

theorem Covers.mono_R {R' : Set (Torus d n)} {c : ℝ} {A : Finset (Torus d n)}
    (h : Covers R ω c A) (hR : R ⊆ R') : Covers R' ω c A := by
  obtain ⟨W, E, h1, h2, h3, h4⟩ := h
  exact ⟨W, E, h1, h2.trans hR, h3, h4⟩

theorem Covers.join (hω : ∀ x y, 0 ≤ ω x y) {c₁ c₂ : ℝ} {A B : Finset (Torus d n)}
    (h1 : Covers R ω c₁ A) (h2 : Covers R ω c₂ B) (hz : ∃ z, z ∈ A ∧ z ∈ B) :
    Covers R ω (c₁ + c₂) (A ∪ B) := by
  obtain ⟨W, E, a1, a2, a3, a4⟩ := h1
  obtain ⟨W', E', b1, b2, b3, b4⟩ := h2
  obtain ⟨z, hzA, hzB⟩ := hz
  refine ⟨W ∪ W', E ∪ E', a1.union b1 ⟨z, a3 hzA, b3 hzB⟩, ?_, ?_, ?_⟩
  · rw [Finset.coe_union]; exact Set.union_subset a2 b2
  · exact Finset.union_subset_union a3 b3
  · exact (bondCost_union_le hω E E').trans (add_le_add a4 b4)

theorem Linked.refl {c : ℝ} (hc : 0 ≤ c) {x : Torus d n} (hx : x ∈ R) :
    Linked R ω c x x := by
  refine ⟨{x}, ∅, connStruct_singleton x, ?_, by simp, ?_⟩
  · simpa using hx
  · simpa [bondCost] using hc

theorem Linked.symm {c : ℝ} {x y : Torus d n} (h : Linked R ω c x y) : Linked R ω c y x := by
  rw [Linked, Finset.pair_comm] at h
  exact h

theorem Linked.trans (hω : ∀ x y, 0 ≤ ω x y) {c c' : ℝ} {x y z : Torus d n}
    (h : Linked R ω c x y) (h' : Linked R ω c' y z) : Linked R ω (c + c') x z := by
  have := Covers.join hω h h' ⟨y, by simp, by simp⟩
  refine this.mono_A ?_
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at ha ⊢
  rcases ha with rfl | rfl
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem Linked.step {c : ℝ} {x y : Torus d n} (hn : Nbr x y) (hx : x ∈ R) (hy : y ∈ R)
    (hc : ω x y ≤ c) : Linked R ω c x y := by
  refine ⟨{x, y}, {(x, y)}, connStruct_edge hn, ?_, subset_rfl, ?_⟩
  · intro a ha
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> assumption
  · simpa [bondCost] using hc

theorem exists_cross {α : Type*} {r : α → α → Prop} {S : Finset α} {s w : α}
    (hsw : Relation.ReflTransGen r s w) (hs : s ∈ S) (hw : w ∉ S) :
    ∃ u ∈ S, ∃ v ∉ S, r u v := by
  induction hsw with
  | refl => exact absurd hs hw
  | @tail b c _ hbc ih =>
    by_cases hb : b ∈ S
    · exact ⟨b, hb, c, hw, hbc⟩
    · exact ih hb

/-- **Assembly along a connected nerve.**  Nodes `v ∈ S` carry covers `A v` of cost `σ v`;
adjacent nodes (`H u v`) contain linked points at cost `ρ`; the nerve is connected from `v₀`.
Then all the node sets are covered at cost `∑ σ + (|S| - 1) ρ`. -/
theorem assemble (hω : ∀ x y, 0 ≤ ω x y) {V : Type*} [DecidableEq V] (S : Finset V)
    (H : V → V → Prop) (v₀ : V) (hv₀ : v₀ ∈ S)
    (hreach : ∀ v ∈ S, Relation.ReflTransGen (fun u v => H u v ∧ u ∈ S ∧ v ∈ S) v₀ v)
    (A : V → Finset (Torus d n)) (σ : V → ℝ) (hσ : ∀ v ∈ S, Covers R ω (σ v) (A v)) (ρ : ℝ)
    (hlink : ∀ u ∈ S, ∀ v ∈ S, H u v → ∃ a ∈ A u, ∃ b ∈ A v, Linked R ω ρ a b) :
    Covers R ω (∑ v ∈ S, σ v + ((S.card : ℝ) - 1) * ρ) (S.biUnion A) := by
  have key : ∀ k : ℕ, k + 1 ≤ S.card → ∃ S' ⊆ S, S'.card = k + 1 ∧ v₀ ∈ S' ∧
      Covers R ω (∑ v ∈ S', σ v + k * ρ) (S'.biUnion A) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨{v₀}, by simpa using hv₀, by simp, by simp, ?_⟩
      simpa using hσ v₀ hv₀
    | succ k ih =>
      intro hk
      obtain ⟨S', hS'S, hcard, hv₀S', hcov⟩ := ih (by omega)
      obtain ⟨w, hwS, hwS'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S') (t := S)
        (by omega)
      obtain ⟨u, huS', v, hvS', hH, huS, hvS⟩ : ∃ u ∈ S', ∃ v ∉ S', H u v ∧ u ∈ S ∧ v ∈ S := by
        obtain ⟨u, hu, v, hv, h⟩ := exists_cross (hreach w hwS) hv₀S' hwS'
        exact ⟨u, hu, v, hv, h⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hlink u huS v hvS hH
      refine ⟨insert v S', Finset.insert_subset hvS hS'S, by rw [Finset.card_insert_of_notMem hvS', hcard],
        Finset.mem_insert_of_mem hv₀S', ?_⟩
      have c1 : Covers R ω ((∑ v ∈ S', σ v + k * ρ) + ρ) (S'.biUnion A ∪ {a, b}) :=
        Covers.join hω hcov hab ⟨a, Finset.mem_biUnion.2 ⟨u, huS', ha⟩, by simp⟩
      have c2 := Covers.join hω c1 (hσ v hvS) ⟨b, by simp, hb⟩
      refine (c2.mono_c ?_).mono_A ?_
      · rw [Finset.sum_insert hvS']
        push_cast
        linarith
      · intro x hx
        rw [Finset.biUnion_insert] at hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inr hx
        · exact Or.inl (Or.inl hx)
  have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨v₀, hv₀⟩
  obtain ⟨S', hS'S, hcard, -, hcov⟩ := key (S.card - 1) (by omega)
  have : S' = S := Finset.eq_of_subset_of_card_le hS'S (by omega)
  subst this
  have e : ((S'.card - 1 : ℕ) : ℝ) = (S'.card : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]; simp
  rw [e] at hcov
  exact hcov

/-- A monotone lattice path from the corner `b` of a box to `b + w` has `∑ w` steps. -/
theorem linked_box (hω : ∀ x y, 0 ≤ ω x y) (b : Torus d n) (w : Fin d → ℕ) {c : ℝ}
    (hR : ∀ w' : Fin d → ℕ, (∀ μ, w' μ ≤ w μ) → b + natT w' ∈ R)
    (hc : ∀ x ∈ R, ∀ y ∈ R, ω x y ≤ c) :
    Linked R ω ((∑ μ, w μ : ℕ) * c) b (b + natT w) := by
  have key := chain_of_steps (d := d) (fun (m : ℕ) (x y : Torus d n) => Linked R ω (m * c) x y)
    (fun w' => b + natT w')
    (by
      have := Linked.refl (ω := ω) (c := ((0 : ℕ) : ℝ) * c) (by simp) (x := b + natT 0)
        (by simpa [natT_zero] using hR 0 (fun μ => Nat.zero_le _))
      simpa using this)
    (fun {m m' x y z} h h' => by
      have := Linked.trans hω h h'
      refine Covers.mono_c this (le_of_eq ?_)
      push_cast; ring)
    (∑ μ, w μ) w rfl ?_
  · simpa [natT_zero] using key
  · intro w' μ hw'
    have h1 : b + natT w' ∈ R := hR w' (fun ν => by
      have := hw' ν; simp only [Pi.add_apply] at this; omega)
    have h2 : b + natT (w' + Pi.single μ 1) ∈ R := hR _ (fun ν => by
      have := hw' ν; simpa using this)
    have hn : Nbr (b + natT w') (b + natT (w' + Pi.single μ 1)) := by
      refine ⟨μ, Or.inl ?_⟩
      rw [natT_add, natT_single, add_assoc]
    have := Linked.step hn h1 h2 (hc _ h1 _ h2)
    simpa using this

/-- Every point of a box inside `R` is joined to the corner of the box at cost
`d s c` (`s` the side, `c` a bound for the bond weights in `R`). -/
theorem linked_corner (hω : ∀ x y, 0 ≤ ω x y) (b : Torus d n) (s : ℕ) {c : ℝ}
    (hbox : box b s ⊆ R) (hc : ∀ x ∈ R, ∀ y ∈ R, ω x y ≤ c) {x : Torus d n} (hx : x ∈ box b s) :
    Linked R ω (d * s * c) b x := by
  have hxR : x ∈ R := hbox hx
  have hc0 : 0 ≤ c := (hω x x).trans (hc x hxR x hxR)
  obtain ⟨w, hw, rfl⟩ := hx
  have h := linked_box hω b w (c := c)
    (fun w' hw' => hbox ⟨w', fun μ => lt_of_le_of_lt (hw' μ) (hw μ), rfl⟩) hc
  refine Covers.mono_c h ?_
  have : ((∑ μ, w μ : ℕ) : ℝ) ≤ d * s := by
    have h1 : ∑ μ, w μ ≤ ∑ _μ : Fin d, s := Finset.sum_le_sum fun μ _ => (hw μ).le
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    exact_mod_cast h1
  exact mul_le_mul_of_nonneg_right this hc0

/-- Two points of a box inside `R` are joined at cost `2 d s c`. -/
theorem linked_box_pair (hω : ∀ x y, 0 ≤ ω x y) (b : Torus d n) (s : ℕ) {c : ℝ}
    (hbox : box b s ⊆ R) (hc : ∀ x ∈ R, ∀ y ∈ R, ω x y ≤ c) {x y : Torus d n}
    (hx : x ∈ box b s) (hy : y ∈ box b s) : Linked R ω (2 * (d * s * c)) x y := by
  have h1 := (linked_corner hω b s hbox hc hx).symm
  have h2 := linked_corner hω b s hbox hc hy
  refine Covers.mono_c (Linked.trans hω h1 h2) (le_of_eq (by ring))

end Struct

/-! ### Weights and the cell graph of `D(P)` -/

section Weights

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- The bond weight of the tree length `d̃_{k+1}` of `𝔹_{k+1}` (`K = k+1`): a bond whose endpoints
have layers `n, n'` counts `M⁻¹ ℓ_{min(n,n')}⁻¹ = (M ℓ_{min})⁻¹`, `M = L ^ (m₀ + m₁)`,
`ℓ_n = L ^ n` (the length `|Γ|_𝔹 = ∑_n ℓ_n⁻¹ |Γ ∩ Λ_n|` of the paper; a bond across an interface
is counted with the finer layer, which is the larger weight). -/
noncomputable def bondW (x y : CTorus d L N₁ m₁ K) : ℝ :=
  ((L : ℝ) ^ (m₀ + m₁))⁻¹ * ((L : ℝ) ^ (min (G.layerIndex x) (G.layerIndex y)))⁻¹

theorem bondW_nonneg (x y : CTorus d L N₁ m₁ K) : 0 ≤ bondW G m₀ x y := by
  unfold bondW; positivity

theorem bondW_le_one (x y : CTorus d L N₁ m₁ K) : bondW G m₀ x y ≤ 1 := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  unfold bondW
  have h1 : ((L : ℝ) ^ (m₀ + m₁))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have h2 : ((L : ℝ) ^ (min (G.layerIndex x) (G.layerIndex y)))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have h3 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁))⁻¹ := by positivity
  nlinarith [inv_nonneg.2 (pow_nonneg (by linarith : (0:ℝ) ≤ L) (min (G.layerIndex x) (G.layerIndex y)))]

theorem bondW_of_layer {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K) {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ G.layer n) (hy : y ∈ G.layer n) :
    bondW G m₀ x y = ((cellSide L m₀ m₁ n : ℕ) : ℝ)⁻¹ := by
  unfold bondW cellSide
  rw [G.layerIndex_eq hn1 hnK hx, G.layerIndex_eq hn1 hnK hy, min_self, ← mul_inv, ← pow_add]
  push_cast
  congr 2; ring

/-- Adjacency of cells of side `a` (aligned bases differing by `a` in one coordinate). -/
def CAdj {n : ℕ} (a : ℕ) (x y : Torus d n) : Prop :=
  ∃ μ : Fin d, y = x + natT (Pi.single μ a) ∨ x = y + natT (Pi.single μ a)

variable {G m₀}

theorem box_subset_Dsites {q : ℕ × CTorus d L N₁ m₁ K} {b : CTorus d L N₁ m₁ K}
    (hN : L ^ m₀ ∣ N₁) (hq : q.1 ≤ K) (hb : b ∈ Dbases G m₀ q) :
    box b (cellSide L m₀ m₁ q.1) ⊆ Dsites G m₀ q := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hq
  have ha0 := cellSide_pos (L := L) m₀ m₁ q.1
  simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  obtain ⟨hal, hD⟩ := hb
  simp only [Dsites, Set.mem_iUnion] at hD
  obtain ⟨b', hb', hbm⟩ := hD
  have h1 := cell_subset_cube hdvd ha0 hb'.1 hbm
  rw [cbase_eq_of_mem_box hdvd hal (mem_box_self b ha0)] at h1
  intro x hx
  simp only [Dsites, Set.mem_iUnion]
  exact ⟨b', hb', h1 hx⟩

theorem mem_Dsites_of_mem_Dbases {q : ℕ × CTorus d L N₁ m₁ K} {b : CTorus d L N₁ m₁ K}
    (hb : b ∈ Dbases G m₀ q) : b ∈ Dsites G m₀ q := by
  simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact hb.2

theorem cbase_mem_Dbases (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    cbase (cellSide L m₀ m₁ q.1) q.2 ∈ Dbases G m₀ q := by
  obtain ⟨b, hb⟩ := exists_Dcubes hU hN hq
  simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨aligned_cbase _, cellOf_subset_Dsites hb ?_⟩
  exact mem_box_self _ (cellSide_pos m₀ m₁ q.1)

theorem add_mem_Dbases {q : ℕ × CTorus d L N₁ m₁ K} {b' : CTorus d L N₁ m₁ K}
    (hN : L ^ m₀ ∣ N₁) (hq : q.1 ≤ K) (hb' : b' ∈ Dcubes G m₀ q) (v : Fin d → ℕ)
    (hv : ∀ μ, v μ < L) :
    b' + natT (fun μ => cellSide L m₀ m₁ q.1 * v μ) ∈ Dbases G m₀ q := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hq
  simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨aligned_add_natT hdvd hb'.1 (fun μ => Nat.mul_mod_right _ _), ?_⟩
  simp only [Dsites, Set.mem_iUnion]
  refine ⟨b', hb', _, fun μ => ?_, rfl⟩
  have := hv μ
  calc cellSide L m₀ m₁ q.1 * v μ < cellSide L m₀ m₁ q.1 * L :=
        Nat.mul_lt_mul_of_pos_left this (cellSide_pos m₀ m₁ q.1)
    _ = L * cellSide L m₀ m₁ q.1 := Nat.mul_comm _ _

theorem Dsites_bondW {q : ℕ × CTorus d L N₁ m₁ K} (hq1 : 1 ≤ q.1) (hqK : q.1 ≤ K)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ Dsites G m₀ q) (hy : y ∈ Dsites G m₀ q) :
    bondW G m₀ x y = ((cellSide L m₀ m₁ q.1 : ℕ) : ℝ)⁻¹ :=
  bondW_of_layer G m₀ hq1 hqK (Dsites_subset_layer q hx) (Dsites_subset_layer q hy)

/-- Adjacent cells of `D(P)` are linked at cost `1` (`a` bonds of weight `a⁻¹`). -/
theorem linked_cell_step {q : ℕ × CTorus d L N₁ m₁ K} (hN : L ^ m₀ ∣ N₁) (hq1 : 1 ≤ q.1)
    (hqK : q.1 ≤ K) {u v : CTorus d L N₁ m₁ K} (hu : u ∈ Dbases G m₀ q) (hv : v ∈ Dbases G m₀ q)
    {μ : Fin d} (h : v = u + natT (Pi.single μ (cellSide L m₀ m₁ q.1))) :
    Linked (Dsites G m₀ q) (bondW G m₀) 1 u v := by
  set a := cellSide L m₀ m₁ q.1 with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ q.1
  have hbox := box_subset_Dsites hN hqK hu
  have hR : ∀ w' : Fin d → ℕ, (∀ ν, w' ν ≤ (Pi.single μ a : Fin d → ℕ) ν) →
      u + natT w' ∈ Dsites G m₀ q := by
    intro w' hw'
    by_cases hlt : w' μ < a
    · refine hbox ⟨w', fun ν => ?_, rfl⟩
      by_cases hν : ν = μ
      · subst hν; exact hlt
      · have := hw' ν; simp [Pi.single_eq_of_ne hν] at this; omega
    · have hμ : w' μ = a := by
        have := hw' μ; simp at this; omega
      have : w' = Pi.single μ a := by
        funext ν
        by_cases hν : ν = μ
        · subst hν; simpa using hμ
        · have := hw' ν; simp [Pi.single_eq_of_ne hν] at this; simp [Pi.single_eq_of_ne hν, this]
      rw [this, ← h]
      exact mem_Dsites_of_mem_Dbases hv
  have hc : ∀ x ∈ Dsites G m₀ q, ∀ y ∈ Dsites G m₀ q, bondW G m₀ x y ≤ (a : ℝ)⁻¹ :=
    fun x hx y hy => (Dsites_bondW hq1 hqK hx hy).le
  have := linked_box (bondW_nonneg G m₀) u (Pi.single μ a) hR hc
  rw [← h] at this
  refine Covers.mono_c this (le_of_eq ?_)
  have hs : (∑ ν, (Pi.single μ a : Fin d → ℕ) ν) = a := by simp
  rw [hs]
  have : (a : ℝ) ≠ 0 := by positivity
  field_simp

/-- The cells of `D(P)` are connected through adjacent cells: every aligned base `b ∈ D(P)` is
joined to the base `c₀` of `□(P)` inside `D(P)`. -/
theorem reach_Dbases (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) {b : CTorus d L N₁ m₁ K} (hb : b ∈ Dbases G m₀ q) :
    Relation.ReflTransGen (fun u v => CAdj (cellSide L m₀ m₁ q.1) u v ∧ u ∈ Dbases G m₀ q ∧
      v ∈ Dbases G m₀ q) (cbase (cellSide L m₀ m₁ q.1) q.2) b := by
  obtain ⟨⟨h1, hqK⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  set a := cellSide L m₀ m₁ q.1 with ha
  have hdvd : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd (K := K) (m₁ := m₁) hN hqK
  have ha0 : 0 < a := cellSide_pos m₀ m₁ q.1
  set B := Dbases G m₀ q with hB
  set c0 := cbase a q.2 with hc0
  have hc0B : c0 ∈ B := cbase_mem_Dbases hU hN hq
  have hbD := hb
  simp only [hB, Dbases, Finset.mem_filter, Finset.mem_univ, true_and] at hbD
  obtain ⟨hbal, hbS⟩ := hbD
  simp only [Dsites, Set.mem_iUnion] at hbS
  obtain ⟨b', hb', hbm⟩ := hbS
  have hc0m : c0 ∈ box b' (L * a) := hb'.2.1 (mem_box_self c0 ha0)
  have hsymm : ∀ x y, (CAdj a x y ∧ x ∈ B ∧ y ∈ B) → (CAdj a y x ∧ y ∈ B ∧ x ∈ B) :=
    fun x y h => ⟨by obtain ⟨μ, hμ⟩ := h.1; exact ⟨μ, hμ.symm⟩, h.2.2, h.2.1⟩
  -- the chain from the corner `b'` to `b' + a u`
  have chain : ∀ u : Fin d → ℕ, (∀ μ, u μ < L) →
      Relation.ReflTransGen (fun x y => CAdj a x y ∧ x ∈ B ∧ y ∈ B) b'
        (b' + natT (fun μ => a * u μ)) := by
    intro u hu
    have key := chain_of_steps (d := d)
      (fun (_ : ℕ) (x y : CTorus d L N₁ m₁ K) =>
        Relation.ReflTransGen (fun x y => CAdj a x y ∧ x ∈ B ∧ y ∈ B) x y)
      (fun v => b' + natT (fun μ => a * v μ)) Relation.ReflTransGen.refl (fun h h' => h.trans h')
      (∑ μ, u μ) u rfl ?_
    · have e : b' + natT (fun μ => a * (0 : Fin d → ℕ) μ) = b' := by
        rw [show (fun μ => a * (0 : Fin d → ℕ) μ) = (0 : Fin d → ℕ) from by funext μ; simp,
          natT_zero, add_zero]
      beta_reduce at key
      rw [e] at key
      exact key
    · intro v μ hv
      have hv' : ∀ ν, v ν < L := fun ν => by
        have := hv ν; simp only [Pi.add_apply] at this; have := hu ν; omega
      have hv'' : ∀ ν, (v + Pi.single μ 1 : Fin d → ℕ) ν < L := fun ν => by
        have h1 : (v + Pi.single μ 1 : Fin d → ℕ) ν ≤ u ν := hv ν
        have := hu ν; omega
      have m1 := add_mem_Dbases (G := G) hN hqK hb' v hv'
      have m2 := add_mem_Dbases (G := G) hN hqK hb' (v + Pi.single μ 1) hv''
      refine Relation.ReflTransGen.single ⟨⟨μ, Or.inl ?_⟩, m1, m2⟩
      rw [add_assoc, ← natT_add]
      congr 2
      funext ν
      by_cases h : ν = μ
      · subst h; simp [mul_add]
      · simp [Pi.single_eq_of_ne h]
  have hwa : ∀ (w : Fin d → ℕ) (x : CTorus d L N₁ m₁ K), x = b' + natT w → Aligned a x →
      (∀ μ, w μ < L * a) → ∃ u : Fin d → ℕ, (∀ μ, u μ < L) ∧ x = b' + natT (fun μ => a * u μ) := by
    intro w x hx hxal hw
    have hwm : ∀ μ, w μ % a = 0 := fun μ => by
      have := mod_of_aligned_add hdvd hb'.1 (w := w) μ
      rw [← hx] at this
      rw [← this]; exact hxal μ
    refine ⟨fun μ => w μ / a, fun μ => ?_, ?_⟩
    · show w μ / a < L
      rw [Nat.div_lt_iff_lt_mul ha0]; exact hw μ
    · rw [hx]
      congr 2
      funext μ
      exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hwm μ))).symm
  obtain ⟨w, hw, hbw⟩ := hbm
  obtain ⟨w0, hw0, hc0w⟩ := hc0m
  obtain ⟨u, hu, hbu⟩ := hwa w b hbw hbal hw
  obtain ⟨u0, hu0, hc0u⟩ := hwa w0 c0 hc0w (aligned_cbase _) hw0
  have h1 := chain u hu
  have h2 := chain u0 hu0
  rw [← hbu] at h1
  rw [← hc0u] at h2
  exact (rtg_symm hsymm h2).trans h1

/-- **The cells of `D(P)` are covered** by a connected structure inside `D(P)` of cost
`#cells - 1` (a spanning tree of the cell graph, each adjacent pair at cost `1`). -/
theorem covers_Dbases (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) :
    Covers (Dsites G m₀ q) (bondW G m₀) (((Dbases G m₀ q).card : ℝ) - 1) (Dbases G m₀ q) := by
  classical
  obtain ⟨⟨h1, hqK⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  have key := assemble (R := Dsites G m₀ q) (bondW_nonneg G m₀) (Dbases G m₀ q)
    (CAdj (cellSide L m₀ m₁ q.1)) (cbase (cellSide L m₀ m₁ q.1) q.2) (cbase_mem_Dbases hU hN hq)
    (fun b hb => reach_Dbases hU hN hq hb) (fun v => ({v} : Finset (CTorus d L N₁ m₁ K)))
    (fun _ => 0) ?_ 1 ?_
  · simp only [Finset.sum_const_zero, zero_add, mul_one] at key
    simpa using key
  · intro v hv
    refine ⟨{v}, ∅, connStruct_singleton v, ?_, subset_rfl, by simp [bondCost]⟩
    simpa using mem_Dsites_of_mem_Dbases hv
  · intro u hu v hv huv
    refine ⟨u, by simp, v, by simp, ?_⟩
    obtain ⟨μ, h | h⟩ := huv
    · exact linked_cell_step hN h1 hqK hu hv h
    · exact (linked_cell_step hN h1 hqK hv hu h).symm

end Weights

/-! ### (GM2) -/

section GM2

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

/-- The constant bond weight `M⁻¹ ℓ_j⁻¹` of the tree length `d_j` (all bonds of the unit lattice
count the same). -/
noncomputable def scaleW (L m₀ m₁ j : ℕ) {α : Type*} (_ _ : α) : ℝ := ((L : ℝ) ^ (m₀ + m₁ + j))⁻¹

/-- `W` meets every `π'_n`-cube (aligned box of side `L a_n`) contained in `Y ∩ Λ_n`,
`1 ≤ n ≤ K`. -/
def MeetsCubes (Y : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ n, 1 ≤ n → n ≤ K → ∀ b, Aligned (cellSide L m₀ m₁ n) b →
    box b (L * cellSide L m₀ m₁ n) ⊆ Y → box b (L * cellSide L m₀ m₁ n) ⊆ ↑(G.layer n) →
      ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ n)

/-- `W` meets every `π'_j`-cube contained in `X`. -/
def MeetsCubesAt (j : ℕ) (X : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K)) : Prop :=
  ∀ b, Aligned (cellSide L m₀ m₁ j) b → box b (L * cellSide L m₀ m₁ j) ⊆ X →
    ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ j)

/-- **The tree length `d̃_{k+1}(Y)`** (`K = k+1`): the infimum of `∑ bondW` over connected
structures in `Y` meeting every `π'_n`-cube contained in `Y ∩ Λ_n`. -/
noncomputable def dTilde (Y : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  sInf {x | ∃ W E, ConnStruct W E ∧ (↑W ⊆ Y) ∧ MeetsCubes G m₀ Y W ∧ x = bondCost (bondW G m₀) E}

/-- **The tree length `d_j(X)`**: the infimum of the number of bonds times `M⁻¹ ℓ_j⁻¹` over
connected structures in `X` meeting every `π'_j`-cube contained in `X`. -/
noncomputable def dScale (j : ℕ) (X : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  sInf {x | ∃ W E, ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsCubesAt m₀ j X W ∧
    x = bondCost (scaleW L m₀ m₁ j) E}

/-- The geometric data of `X₁` used by (GM2), (GM3): `Λ_n` is a union of `π'_n`-cubes, the
`π_n`-cubes tile the torus, and `X₁ ⊆ Λ_K` is a union of `π'_K`-cubes. -/
structure PolySetup (X₁ : Set (CTorus d L N₁ m₁ K)) : Prop where
  hU : LayerUnion G m₀
  hN : L ^ m₀ ∣ N₁
  X₁_layer : X₁ ⊆ ↑(G.layer K)
  X₁_cubes : ∀ x ∈ X₁, ∃ b, Aligned (cellSide L m₀ m₁ K) b ∧
    x ∈ box b (L * cellSide L m₀ m₁ K) ∧ box b (L * cellSide L m₀ m₁ K) ⊆ X₁

/-- The geometric data of (GM2): `X ⊆ X₁ ⊆ Λ_K`, `X₁` a union of `π'_K`-cubes each of which
contains a `π'_j`-cube lying in `X`, and `j < K`. -/
structure GM2Setup (j : ℕ) (X X₁ : Set (CTorus d L N₁ m₁ K)) : Prop
    extends PolySetup G m₀ X₁ where
  hjK : j + 1 ≤ K
  X_sub : X ⊆ X₁
  contains : ∀ b, Aligned (cellSide L m₀ m₁ K) b → box b (L * cellSide L m₀ m₁ K) ⊆ X₁ →
    ∃ b', Aligned (cellSide L m₀ m₁ j) b' ∧ box b' (L * cellSide L m₀ m₁ j) ⊆ X ∧
      box b' (L * cellSide L m₀ m₁ j) ⊆ box b (L * cellSide L m₀ m₁ K)

variable {G m₀}

/-- A point of the parameter cube is joined to the base of its cell inside `D(P)` at cost `d`. -/
theorem attach_some (hU : LayerUnion G m₀) (hN : L ^ m₀ ∣ N₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) {z : CTorus d L N₁ m₁ K} (hz : z ∈ Pset m₁ q) :
    Linked (Dsites G m₀ q) (bondW G m₀) d (cbase (cellSide L m₀ m₁ q.1) q.2) z := by
  obtain ⟨⟨h1, hqK⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  have hbox := box_subset_Dsites hN hqK (cbase_mem_Dbases hU hN hq)
  have hc : ∀ x ∈ Dsites G m₀ q, ∀ y ∈ Dsites G m₀ q,
      bondW G m₀ x y ≤ ((cellSide L m₀ m₁ q.1 : ℕ) : ℝ)⁻¹ :=
    fun x hx y hy => (Dsites_bondW h1 hqK hx hy).le
  have := linked_corner (bondW_nonneg G m₀) _ _ hbox hc (Pset_subset_cellOf m₀ q hz)
  refine Covers.mono_c this (le_of_eq ?_)
  have : ((cellSide L m₀ m₁ q.1 : ℕ) : ℝ) ≠ 0 := by
    have := cellSide_pos (L := L) m₀ m₁ q.1; positivity
  field_simp

/-- A point of `X₁` is joined, inside `X₁`, to a point of the tree `Γ₀` at cost `2 d L`. -/
theorem attach_none {j : ℕ} {X X₁ : Set (CTorus d L N₁ m₁ K)} (hS : GM2Setup G m₀ j X X₁)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hmeet : MeetsCubesAt m₀ j X W₀)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₁) :
    ∃ q ∈ W₀, Linked X₁ (bondW G m₀) (2 * d * L) x q := by
  have hK : 1 ≤ K := by have := hS.hjK; omega
  obtain ⟨b, hbal, hxb, hbX⟩ := hS.X₁_cubes x hx
  obtain ⟨b', hb'al, hb'X, hb'sub⟩ := hS.contains b hbal hbX
  obtain ⟨q, hqW, hqb'⟩ := hmeet b' hb'al hb'X
  have hqb : q ∈ box b (L * cellSide L m₀ m₁ K) := hb'sub hqb'
  have hc : ∀ x ∈ X₁, ∀ y ∈ X₁, bondW G m₀ x y ≤ ((cellSide L m₀ m₁ K : ℕ) : ℝ)⁻¹ :=
    fun x hx y hy => (bondW_of_layer G m₀ hK le_rfl (hS.X₁_layer hx) (hS.X₁_layer hy)).le
  refine ⟨q, hqW, ?_⟩
  have := linked_box_pair (bondW_nonneg G m₀) _ _ hbX hc hxb hqb
  refine Covers.mono_c this (le_of_eq ?_)
  have : ((cellSide L m₀ m₁ K : ℕ) : ℝ) ≠ 0 := by
    have := cellSide_pos (L := L) m₀ m₁ K; positivity
  push_cast
  field_simp

/-! #### The nerve -/

section Nerve

variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ K}

/-- The sites of the nodes of the nerve: `none` is `X₁`, `some i` is the parameter cube `P_i`. -/
def nodeSites (X₁ : Set (CTorus d L N₁ m₁ K)) (c : ι → ℕ × CTorus d L N₁ m₁ K) :
    Option ι → Set (CTorus d L N₁ m₁ K)
  | none => X₁
  | some i => Pset m₁ (c i)

/-- Two nodes are adjacent when their sites meet or contain nearest neighbours. -/
def Nerve (X₁ : Set (CTorus d L N₁ m₁ K)) (c : ι → ℕ × CTorus d L N₁ m₁ K) (u v : Option ι) :
    Prop :=
  ∃ z ∈ nodeSites X₁ c u, ∃ z' ∈ nodeSites X₁ c v, z = z' ∨ Nbr z z'

omit [NeZero N₁] [NeZero L] in
theorem Nerve.symm {X₁ : Set (CTorus d L N₁ m₁ K)} {u v : Option ι} (h : Nerve X₁ c u v) :
    Nerve X₁ c v u := by
  obtain ⟨z, hz, z', hz', h⟩ := h
  exact ⟨z', hz', z, hz, h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩

omit [NeZero N₁] [NeZero L] in
/-- The nerve of a connected family is connected from `X₁`. -/
theorem reach_nerve [DecidableEq ι] (X₁ : Set (CTorus d L N₁ m₁ K)) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C) :
    ∀ o ∈ Finset.insertNone C, Relation.ReflTransGen
      (fun u v => Nerve X₁ c u v ∧ u ∈ Finset.insertNone C ∧ v ∈ Finset.insertNone C) none o := by
  have key : ∀ y ∈ X₁, ∀ z, Relation.ReflTransGen
      (fun a b => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧
        a ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C ∧
        b ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C) y z →
      ∃ ν ∈ Finset.insertNone C, z ∈ nodeSites X₁ c ν ∧ Relation.ReflTransGen
        (fun u v => Nerve X₁ c u v ∧ u ∈ Finset.insertNone C ∧ v ∈ Finset.insertNone C) none ν := by
    intro y hy z hyz
    induction hyz with
    | refl => exact ⟨none, Finset.none_mem_insertNone, hy, Relation.ReflTransGen.refl⟩
    | @tail b z' _ hbz ih =>
      obtain ⟨ν, hν, hbν, hreach⟩ := ih
      have hz' := hbz.2.2
      rcases hz' with hz' | hz'
      · refine ⟨none, Finset.none_mem_insertNone, hz', hreach.trans (Relation.ReflTransGen.single
          ⟨⟨b, hbν, z', hz', Or.inr hbz.1.2⟩, hν, Finset.none_mem_insertNone⟩)⟩
      · simp only [Set.mem_iUnion] at hz'
        obtain ⟨j, hj, hz'⟩ := hz'
        refine ⟨some j, Finset.some_mem_insertNone.2 hj, hz', hreach.trans
          (Relation.ReflTransGen.single ⟨⟨b, hbν, z', hz', Or.inr hbz.1.2⟩, hν,
            Finset.some_mem_insertNone.2 hj⟩)⟩
  intro o ho
  cases o with
  | none => exact Relation.ReflTransGen.refl
  | some i =>
    have hi : i ∈ C := Finset.some_mem_insertNone.1 ho
    obtain ⟨y, hy, hyz⟩ : ∃ y ∈ X₁, Relation.ReflTransGen
        (fun a b => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj a b ∧
          a ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C ∧
          b ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C) y (c i).2 :=
      hconn i hi (self_mem_Pset (c i))
    obtain ⟨ν, hν, hzν, hreach⟩ := key y hy _ hyz
    exact hreach.trans (Relation.ReflTransGen.single ⟨⟨(c i).2, hzν, (c i).2,
      self_mem_Pset (c i), Or.inl rfl⟩, hν, ho⟩)

/-- The cost bound for linking neighbouring nodes of the nerve. -/
noncomputable def gm2Rho (d L : ℕ) : ℝ := 2 * d + 1 + 2 * d * L

/-- The sets covered at the nodes: `Γ₀` at `none`, the cells of `D(P_i)` at `some i`. -/
noncomputable def nodeSet (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ) (c : ι → ℕ × CTorus d L N₁ m₁ K)
    (W₀ : Finset (CTorus d L N₁ m₁ K)) : Option ι → Finset (CTorus d L N₁ m₁ K)
  | none => W₀
  | some i => Dbases G m₀ (c i)

variable {X X₁ : Set (CTorus d L N₁ m₁ K)} {j : ℕ} {C : Finset ι}

theorem Dsites_subset_Ysites {i : ι} (hi : i ∈ C) :
    Dsites G m₀ (c i) ⊆ Ysites G m₀ c X₁ C := fun _ hx =>
  Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, hx⟩)

theorem Pset_subset_Ysites (hS : GM2Setup G m₀ j X X₁) (hc : ∀ i, c i ∈ cubeIdx G) {i : ι}
    (hi : i ∈ C) : Pset m₁ (c i) ⊆ Ysites G m₀ c X₁ C :=
  (Pset_subset_Dsites hS.hU hS.hN (hc i)).trans (Dsites_subset_Ysites hi)

theorem link_some_none (hS : GM2Setup G m₀ j X X₁) (hc : ∀ i, c i ∈ cubeIdx G)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hmeet : MeetsCubesAt m₀ j X W₀) {i : ι} (hi : i ∈ C)
    (h : Nerve X₁ c (some i) none) :
    ∃ a ∈ Dbases G m₀ (c i), ∃ b ∈ W₀,
      Linked (Ysites G m₀ c X₁ C) (bondW G m₀) (gm2Rho d L) a b := by
  obtain ⟨z, hz, z', hz', hzz⟩ := h
  have hz : z ∈ Pset m₁ (c i) := hz
  have hz' : z' ∈ X₁ := hz'
  obtain ⟨q, hqW, hq⟩ := attach_none hS hmeet hz'
  refine ⟨cbase (cellSide L m₀ m₁ (c i).1) (c i).2, cbase_mem_Dbases hS.hU hS.hN (hc i), q, hqW, ?_⟩
  have hzR : z ∈ Ysites G m₀ c X₁ C := Pset_subset_Ysites hS hc hi hz
  have hz'R : z' ∈ Ysites G m₀ c X₁ C := subset_Ysites (G := G) (m₀ := m₀) (c := c) X₁ C hz'
  have h1 : Linked (Ysites G m₀ c X₁ C) (bondW G m₀) d _ z :=
    (attach_some hS.hU hS.hN (hc i) hz).mono_R (Dsites_subset_Ysites hi)
  have h2 : Linked (Ysites G m₀ c X₁ C) (bondW G m₀) 1 z z' := by
    rcases hzz with rfl | hn
    · exact Linked.refl (by norm_num) hzR
    · exact Linked.step hn hzR hz'R (bondW_le_one G m₀ _ _)
  have h3 : Linked (Ysites G m₀ c X₁ C) (bondW G m₀) (2 * d * L) z' q :=
    hq.mono_R (subset_Ysites (G := G) (m₀ := m₀) (c := c) X₁ C)
  have := ((h1.trans (bondW_nonneg G m₀) h2).trans (bondW_nonneg G m₀) h3)
  refine Covers.mono_c this ?_
  unfold gm2Rho; linarith

theorem link_some_some (hS : GM2Setup G m₀ j X X₁) (hc : ∀ i, c i ∈ cubeIdx G) {i i' : ι}
    (hi : i ∈ C) (hi' : i' ∈ C) (h : Nerve X₁ c (some i) (some i')) :
    ∃ a ∈ Dbases G m₀ (c i), ∃ b ∈ Dbases G m₀ (c i'),
      Linked (Ysites G m₀ c X₁ C) (bondW G m₀) (gm2Rho d L) a b := by
  obtain ⟨z, hz, z', hz', hzz⟩ := h
  have hz : z ∈ Pset m₁ (c i) := hz
  have hz' : z' ∈ Pset m₁ (c i') := hz'
  refine ⟨cbase (cellSide L m₀ m₁ (c i).1) (c i).2, cbase_mem_Dbases hS.hU hS.hN (hc i),
    cbase (cellSide L m₀ m₁ (c i').1) (c i').2, cbase_mem_Dbases hS.hU hS.hN (hc i'), ?_⟩
  have hzR : z ∈ Ysites G m₀ c X₁ C := Pset_subset_Ysites hS hc hi hz
  have hz'R : z' ∈ Ysites G m₀ c X₁ C := Pset_subset_Ysites hS hc hi' hz'
  have h1 : Linked (Ysites G m₀ c X₁ C) (bondW G m₀) d _ z :=
    (attach_some hS.hU hS.hN (hc i) hz).mono_R (Dsites_subset_Ysites hi)
  have h2 : Linked (Ysites G m₀ c X₁ C) (bondW G m₀) 1 z z' := by
    rcases hzz with rfl | hn
    · exact Linked.refl (by norm_num) hzR
    · exact Linked.step hn hzR hz'R (bondW_le_one G m₀ _ _)
  have h3 : Linked (Ysites G m₀ c X₁ C) (bondW G m₀) d _ z' :=
    (attach_some hS.hU hS.hN (hc i') hz').mono_R (Dsites_subset_Ysites hi')
  have := ((h1.trans (bondW_nonneg G m₀) h2).trans (bondW_nonneg G m₀) h3.symm)
  refine Covers.mono_c this ?_
  unfold gm2Rho; have : (0 : ℝ) ≤ 2 * d * L := by positivity
  linarith

theorem link_nerve (hS : GM2Setup G m₀ j X X₁) (hc : ∀ i, c i ∈ cubeIdx G)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hW₀X : ↑W₀ ⊆ X) (hne : W₀.Nonempty)
    (hmeet : MeetsCubesAt m₀ j X W₀) {u v : Option ι} (hu : u ∈ Finset.insertNone C)
    (hv : v ∈ Finset.insertNone C) (h : Nerve X₁ c u v) :
    ∃ a ∈ nodeSet G m₀ c W₀ u, ∃ b ∈ nodeSet G m₀ c W₀ v,
      Linked (Ysites G m₀ c X₁ C) (bondW G m₀) (gm2Rho d L) a b := by
  cases u with
  | none =>
    cases v with
    | none =>
      obtain ⟨q, hq⟩ := hne
      refine ⟨q, hq, q, hq, Linked.refl (by unfold gm2Rho; positivity)
        (subset_Ysites (G := G) (m₀ := m₀) (c := c) X₁ C (hS.X_sub (hW₀X hq)))⟩
    | some j' =>
      have hj' : j' ∈ C := Finset.some_mem_insertNone.1 hv
      obtain ⟨a, ha, b, hb, hl⟩ := link_some_none hS hc hmeet hj' h.symm
      exact ⟨b, hb, a, ha, hl.symm⟩
  | some i =>
    have hi : i ∈ C := Finset.some_mem_insertNone.1 hu
    cases v with
    | none => exact link_some_none hS hc hmeet hi h
    | some j' => exact link_some_some hS hc hi (Finset.some_mem_insertNone.1 hv) h

theorem meets_Y (hS : GM2Setup G m₀ j X X₁) (hc : ∀ i, c i ∈ cubeIdx G)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} (hmeet : MeetsCubesAt m₀ j X W₀)
    {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : (Finset.insertNone C).biUnion (nodeSet G m₀ c W₀) ⊆ W) :
    MeetsCubes G m₀ (Ysites G m₀ c X₁ C) W := by
  intro n hn1 hnK b hbal hbY hbL
  have ha0 := cellSide_pos (L := L) m₀ m₁ n
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hS.hN hnK
  have hbQ : b ∈ box b (L * cellSide L m₀ m₁ n) :=
    mem_box_self b (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) ha0)
  by_cases hQX : box b (L * cellSide L m₀ m₁ n) ⊆ X₁
  · -- the cube lies in `X₁`, hence `n = K`
    have hnK' : n = K := by
      by_contra hne
      have hK1 : 1 ≤ K := by omega
      have h1 := hbL hbQ
      have h2 := hS.X₁_layer (hQX hbQ)
      exact G.layer_disjoint hn1 hnK hK1 le_rfl hne (Finset.mem_coe.1 h1) (Finset.mem_coe.1 h2)
    subst hnK'
    obtain ⟨b', hb'al, hb'X, hb'sub⟩ := hS.contains b hbal hQX
    obtain ⟨q, hqW, hqb'⟩ := hmeet b' hb'al hb'X
    refine ⟨q, hW (Finset.mem_biUnion.2 ⟨none, Finset.none_mem_insertNone, hqW⟩), hb'sub hqb'⟩
  · obtain ⟨z, hzQ, hzX⟩ := Set.not_subset.1 hQX
    rcases hbY hzQ with hzX₁ | hzD
    · exact absurd hzX₁ hzX
    · obtain ⟨i, hi, hzD⟩ := Set.mem_iUnion₂.1 hzD
      obtain ⟨⟨hi1, hiK⟩, -, -⟩ := (mem_cubeIdx G).1 (hc i)
      have hzn : z ∈ G.layer n := Finset.mem_coe.1 (hbL hzQ)
      have hzi : z ∈ G.layer (c i).1 := Finset.mem_coe.1 (Dsites_subset_layer (c i) hzD)
      have hni : (c i).1 = n := by
        by_contra hne
        exact G.layer_disjoint hi1 hiK hn1 hnK hne hzi hzn
      obtain ⟨b'', hb'', hzb''⟩ : ∃ b'' ∈ Dcubes G m₀ (c i),
          z ∈ box b'' (L * cellSide L m₀ m₁ (c i).1) := by
        simpa only [Dsites, Set.mem_iUnion, exists_prop] using hzD
      have hal'' : Aligned (cellSide L m₀ m₁ n) b'' := hni ▸ hb''.1
      have hzb''' : z ∈ box b'' (L * cellSide L m₀ m₁ n) := hni ▸ hzb''
      have hsub := cell_subset_cube hdvd ha0 hal'' hzb'''
      have hsubQ := cell_subset_cube hdvd ha0 hbal hzQ
      have hx : cbase (cellSide L m₀ m₁ n) z ∈ Dbases G m₀ (c i) := by
        simp only [Dbases, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hni]
        refine ⟨aligned_cbase _, ?_⟩
        simp only [Dsites, Set.mem_iUnion, exists_prop]
        refine ⟨b'', hb'', ?_⟩
        rw [hni]
        exact hsub (mem_box_self _ ha0)
      exact ⟨_, hW (Finset.mem_biUnion.2 ⟨some i, Finset.some_mem_insertNone.2 hi, hx⟩),
        hsubQ (mem_box_self _ ha0)⟩

end Nerve

omit [NeZero L] in
/-- The arithmetic of (GM2): `G₀ - 1 + ρ ≤ d G₀` for `d ≥ 3`. -/
theorem gm2_arith (hd : 3 ≤ d) (hL : 1 ≤ L) :
    (((2 * L + 1) ^ d : ℕ) : ℝ) - 1 + gm2Rho d L ≤ d * (((2 * L + 1) ^ d : ℕ) : ℝ) := by
  have hb : d ≤ (2 * L + 1) ^ (d - 1) := by
    have := one_add_mul_le_pow (a := (2 * L : ℤ)) (by omega) (d - 1)
    have h2 : (1 + ((d - 1 : ℕ) : ℤ) * (2 * L)) ≤ (1 + 2 * L : ℤ) ^ (d - 1) := this
    have h3 : (d : ℤ) ≤ (1 + 2 * L : ℤ) ^ (d - 1) := by
      have : ((d - 1 : ℕ) : ℤ) * (2 * L) ≥ ((d - 1 : ℕ) : ℤ) := by
        have : (1 : ℤ) ≤ 2 * L := by omega
        nlinarith [Int.natCast_nonneg (d - 1)]
      have : ((d - 1 : ℕ) : ℤ) + 1 = d := by omega
      linarith
    exact_mod_cast (by simpa [add_comm] using h3 : (d : ℤ) ≤ ((2 * L + 1 : ℕ) : ℤ) ^ (d - 1))
  have hpow : (2 * L + 1) ^ d = (2 * L + 1) * (2 * L + 1) ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have key : d * (2 * L + 2) ≤ (d - 1) * (2 * L + 1) ^ d := by
    rw [hpow]
    have h1 : d * (2 * L + 1) ≤ (2 * L + 1) * (2 * L + 1) ^ (d - 1) := by
      rw [mul_comm d]; exact Nat.mul_le_mul_left _ hb
    have h2 : d * (2 * L + 2) ≤ 2 * (d * (2 * L + 1)) := by nlinarith
    have h3 : 2 * (d * (2 * L + 1)) ≤ (d - 1) * (d * (2 * L + 1)) :=
      Nat.mul_le_mul_right _ (by omega)
    calc d * (2 * L + 2) ≤ (d - 1) * (d * (2 * L + 1)) := h2.trans h3
      _ ≤ (d - 1) * ((2 * L + 1) * (2 * L + 1) ^ (d - 1)) := Nat.mul_le_mul_left _ h1
  have keyR : (d : ℝ) * (2 * L + 2) ≤ ((d : ℝ) - 1) * (((2 * L + 1) ^ d : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 key
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)] at this ⊢
    exact this
  unfold gm2Rho
  nlinarith

section Main

variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ K}
variable {X X₁ : Set (CTorus d L N₁ m₁ K)} {j : ℕ}

/-- **(GM2), tree form.**  Let `Γ₀ = (W₀, E₀)` be a connected structure in `X` meeting every
`π'_j`-cube contained in `X`.  Then for every connected family `𝒞` there is a connected structure
`Γ` in `Y[𝒞]` meeting every `π'_n`-cube contained in `Y[𝒞] ∩ Λ_n` whose `bondW`-cost is at most
`L⁻¹ · (M⁻¹ ℓ_j⁻¹ |E₀|) + d (2L+1)^d |𝒞|`. -/
theorem gm2_tree [DecidableEq ι] (hS : GM2Setup G m₀ j X X₁) (hd : 3 ≤ d)
    (hc : ∀ i, c i ∈ cubeIdx G) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C)
    {W₀ : Finset (CTorus d L N₁ m₁ K)} {E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hΓ : ConnStruct W₀ E₀) (hΓX : ↑W₀ ⊆ X) (hmeet : MeetsCubesAt m₀ j X W₀) :
    ∃ (W : Finset (CTorus d L N₁ m₁ K)) (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W E ∧ (↑W ⊆ Ysites G m₀ c X₁ C) ∧
        MeetsCubes G m₀ (Ysites G m₀ c X₁ C) W ∧
        bondCost (bondW G m₀) E ≤ (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀ +
          d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  classical
  have hK : 1 ≤ K := by have := hS.hjK; omega
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  set R := Ysites G m₀ c X₁ C with hR
  set ω := bondW G m₀ with hω
  set σ₀ : ℝ := (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀ with hσ₀
  -- the cover of `Γ₀`
  have cov₀ : Covers R ω σ₀ W₀ := by
    refine ⟨W₀, E₀, hΓ, fun x hx => subset_Ysites (G := G) (m₀ := m₀) (c := c) X₁ C
      (hS.X_sub (hΓX hx)), subset_rfl, ?_⟩
    unfold bondCost
    rw [hσ₀]
    unfold bondCost
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, -⟩ := hΓ.2.1 p hp
    have h1' := hS.X₁_layer (hS.X_sub (hΓX h1))
    have h2' := hS.X₁_layer (hS.X_sub (hΓX h2))
    rw [hω, bondW_of_layer G m₀ hK le_rfl h1' h2']
    unfold scaleW cellSide
    push_cast
    rw [← mul_inv, ← pow_succ']
    apply inv_anti₀ (by positivity)
    exact pow_le_pow_right₀ hLR (by have := hS.hjK; omega)
  -- assembly along the nerve
  let σ : Option ι → ℝ := fun o => o.elim σ₀ (fun i => ((Dbases G m₀ (c i)).card : ℝ) - 1)
  have key := assemble (R := R) (ω := ω) (bondW_nonneg G m₀) (Finset.insertNone C)
    (Nerve X₁ c) none Finset.none_mem_insertNone (reach_nerve X₁ C hconn)
    (nodeSet G m₀ c W₀) σ ?_ (gm2Rho d L) ?_
  rotate_left
  · intro o ho
    cases o with
    | none => exact cov₀
    | some i =>
      exact (covers_Dbases hS.hU hS.hN (hc i)).mono_R
        (Dsites_subset_Ysites (Finset.some_mem_insertNone.1 ho))
  · intro u hu v hv h
    exact link_nerve hS hc hΓX hΓ.1 hmeet hu hv h
  obtain ⟨W, E, hconnW, hWR, hAW, hcost⟩ := key
  refine ⟨W, E, hconnW, hWR, meets_Y hS hc hmeet hAW, hcost.trans ?_⟩
  -- the cost bound
  have hsum : ∑ o ∈ Finset.insertNone C, σ o =
      σ₀ + ∑ i ∈ C, (((Dbases G m₀ (c i)).card : ℝ) - 1) := by
    rw [Finset.sum_insertNone]
    rfl
  have hcardS : ((Finset.insertNone C).card : ℝ) - 1 = C.card := by
    rw [Finset.card_insertNone]; push_cast; ring
  have hG : ∀ i ∈ C, ((Dbases G m₀ (c i)).card : ℝ) - 1 ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) - 1 := by
    intro i _
    have := card_Dbases_le (G := G) (m₀ := m₀) hS.hN (((mem_cubeIdx G).1 (hc i)).1.2)
    have : ((Dbases G m₀ (c i)).card : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hsum2 : ∑ i ∈ C, (((Dbases G m₀ (c i)).card : ℝ) - 1) ≤
      C.card * ((((2 * L + 1) ^ d : ℕ) : ℝ) - 1) := by
    calc _ ≤ ∑ _i ∈ C, ((((2 * L + 1) ^ d : ℕ) : ℝ) - 1) := Finset.sum_le_sum hG
      _ = _ := by simp; ring
  rw [hsum, hcardS]
  have ha := gm2_arith (L := L) hd hL1
  have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left ha hC0]

/-- **(GM2).**  `d̃_{k+1}(Y[𝒞]) ≤ L⁻¹ d_j(X) + d (2L+1)^d |𝒞|` (`K = k+1`, `j ≤ k`), for the tree
lengths `dTilde`, `dScale` defined above, provided `X` carries at least one connected structure
meeting its `π'_j`-cubes. -/
theorem gm2 [DecidableEq ι] (hS : GM2Setup G m₀ j X X₁) (hd : 3 ≤ d)
    (hc : ∀ i, c i ∈ cubeIdx G) (C : Finset ι)
    (hconn : IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C)
    (hX : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsCubesAt m₀ j X W₀) :
    dTilde G m₀ (Ysites G m₀ c X₁ C) ≤ (L : ℝ)⁻¹ * dScale m₀ j X +
      d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set B : ℝ := d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card with hB
  have hbdd : BddBelow {x | ∃ W E, ConnStruct W E ∧ (↑W ⊆ Ysites G m₀ c X₁ C) ∧
      MeetsCubes G m₀ (Ysites G m₀ c X₁ C) W ∧ x = bondCost (bondW G m₀) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨W, E, -, -, -, rfl⟩
    exact Finset.sum_nonneg fun p _ => bondW_nonneg G m₀ _ _
  have key : (dTilde G m₀ (Ysites G m₀ c X₁ C) - B) * L ≤ dScale m₀ j X := by
    obtain ⟨W₀, E₀, h1, h2, h3⟩ := hX
    refine le_csInf ⟨_, W₀, E₀, h1, h2, h3, rfl⟩ ?_
    rintro x ⟨W₀', E₀', h1', h2', h3', rfl⟩
    obtain ⟨W, E, hW1, hW2, hW3, hW4⟩ := gm2_tree hS hd hc C hconn h1' h2' h3'
    have hle : dTilde G m₀ (Ysites G m₀ c X₁ C) ≤ bondCost (bondW G m₀) E :=
      csInf_le hbdd ⟨W, E, hW1, hW2, hW3, rfl⟩
    have : dTilde G m₀ (Ysites G m₀ c X₁ C) - B ≤ (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀' := by
      linarith
    calc (dTilde G m₀ (Ysites G m₀ c X₁ C) - B) * L
        ≤ ((L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ j) E₀') * L :=
          mul_le_mul_of_nonneg_right this hL.le
      _ = bondCost (scaleW L m₀ m₁ j) E₀' := by field_simp
  have : dTilde G m₀ (Ysites G m₀ c X₁ C) - B ≤ (L : ℝ)⁻¹ * dScale m₀ j X := by
    rw [inv_mul_eq_div, le_div_iff₀ hL]; exact key
  linarith

end Main

end GM2

end Balaban.Localization
