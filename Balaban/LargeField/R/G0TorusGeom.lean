/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Geometry.Components
public import Balaban.LargeField.Geometry.DomainsMod
public import Balaban.Localization.PolymerGeometry
public import Balaban.Polymer.Support

/-!
# G0: nearest-neighbour connectivity on the torus

The torus facts behind the connectedness of the supports of the gas of removed clusters (the
animals of (H-op), LFR Lemma III.10.5):

* `nn_path_of_supDist_le_one`: two points at sup-distance `≤ 1` are joined by a nearest-neighbour
  path through points whose coordinates are those of one of the two endpoints;
* `nn_path_in_ball`: a point of the sup-ball `B(x, r)` is joined to `x` by a nearest-neighbour path
  inside the ball (along a geodesic, `exists_geodesic`);
* `isAnimal_latGraph_of_base`: a nonempty set all of whose points are joined to one of them by
  nearest-neighbour paths inside the set is an animal of the cube graph `latGraph`;
* `isAnimal_nbhd_of_linked`: the `r`-neighbourhood of a set whose points are linked at
  sup-distance `< ω ≤ r` is an animal; `nbhd_reach_of_near`: two such neighbourhoods of sets at
  sup-distance `≤ 2r` are joined inside their union.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset Balaban

namespace Balaban.LargeField.G0

variable {d n : ℕ} [NeZero n]

/-- A residue of cyclic norm at most `1` is `0`, `1` or `-1`. -/
theorem eq_of_cycNorm_le_one {c : ZMod n} (h : cycNorm n c ≤ 1) : c = 0 ∨ c = 1 ∨ c = -1 := by
  obtain ⟨t, ht, rfl⟩ := (cycNorm_le_iff c 1).mp h
  have h1 : -1 ≤ t := by have := abs_le.mp ht; exact_mod_cast this.1
  have h2 : t ≤ 1 := by have := abs_le.mp ht; exact_mod_cast this.2
  interval_cases t <;> simp

omit [NeZero n] in
/-- `NNAdj` is symmetric. -/
theorem nnAdj_symm {a b : Torus d n} (h : NNAdj a b) : NNAdj b a := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

/-- **A sup-distance-one step is a nearest-neighbour path** through points whose coordinates are
those of one of the two endpoints. -/
theorem nn_path_of_supDist_le_one {P : Torus d n → Prop} {p q : Torus d n}
    (h : supDist p q ≤ 1) (hP : ∀ z : Torus d n, (∀ i, z i = p i ∨ z i = q i) → P z) :
    Relation.ReflTransGen (fun u v => P u ∧ P v ∧ NNAdj u v) p q := by
  set δ : Torus d n := q - p with hδ
  have hδ1 : ∀ i, δ i = 0 ∨ δ i = 1 ∨ δ i = -1 := fun i => by
    apply eq_of_cycNorm_le_one
    have := cycNorm_le_supDist p q i
    rw [hδ, Pi.sub_apply, cycNorm_sub_comm]
    omega
  set z : Finset (Fin d) → Torus d n := fun T => p + ∑ μ ∈ T, Pi.single μ (δ μ) with hz
  have hzc : ∀ T i, z T i = p i ∨ z T i = q i := by
    intro T i
    simp only [hz, Pi.add_apply, Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_ite_eq]
    by_cases hi : i ∈ T
    · right
      simp only [hi, ↓reduceIte, hδ, Pi.sub_apply]
      abel
    · left
      simp [hi]
  have key : ∀ T : Finset (Fin d),
      Relation.ReflTransGen (fun u v => P u ∧ P v ∧ NNAdj u v) p (z T) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa [hz] using Relation.ReflTransGen.refl
    | insert a T ha ih =>
      have e : z (insert a T) = z T + Pi.single a (δ a) := by
        simp only [hz, Finset.sum_insert ha]
        abel
      rw [e]
      rcases hδ1 a with h0 | h1 | hm
      · rw [h0, Pi.single_zero, add_zero]
        exact ih
      · refine ih.tail ⟨hP _ (hzc T), ?_, ⟨a, Or.inl (by rw [h1])⟩⟩
        rw [← e]; exact hP _ (hzc _)
      · refine ih.tail ⟨hP _ (hzc T), ?_, ⟨a, Or.inr ?_⟩⟩
        · rw [← e]; exact hP _ (hzc _)
        · rw [hm, add_assoc, ← Pi.single_add, neg_add_cancel, Pi.single_zero, add_zero]
  have hfin : z Finset.univ = q := by
    simp only [hz, Finset.univ_sum_single, hδ]
    abel
  rw [← hfin]
  exact key Finset.univ

/-- **A point of the sup-ball `B(x, r)` is joined to `x` inside the ball.** -/
theorem nn_path_in_ball (x q : Torus d n) {r : ℕ} (hq : supDist x q ≤ r) :
    Relation.ReflTransGen (fun u v => supDist x u ≤ r ∧ supDist x v ≤ r ∧ NNAdj u v) x q := by
  obtain ⟨g, hg0, hgt, hg⟩ := exists_geodesic x q
  set t := supDist x q with ht
  have key : ∀ i, i ≤ t →
      Relation.ReflTransGen (fun u v => supDist x u ≤ r ∧ supDist x v ≤ r ∧ NNAdj u v) x (g i) := by
    intro i
    induction i with
    | zero => intro _; rw [hg0]
    | succ i ih =>
      intro hi
      have hi' : i ≤ t := by omega
      have h1 := (hg i hi').1
      have h2 := (hg (i + 1) hi).1
      have hstep := (hg i hi').2 (by omega)
      refine (ih hi').trans (nn_path_of_supDist_le_one hstep.le fun z hz => ?_)
      rw [supDist_le_iff]
      intro j
      rcases hz j with hzj | hzj
      · rw [hzj]
        have := cycNorm_le_supDist x (g i) j
        omega
      · rw [hzj]
        have := cycNorm_le_supDist x (g (i + 1)) j
        omega
  rw [← hgt]
  exact key t le_rfl

omit [NeZero n] in
/-- Nearest-neighbour paths inside a set are paths of the cube graph. -/
theorem rtg_latGraph_of_nn {X : Finset (Torus d n)} {p q : Torus d n}
    (h : Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ NNAdj u v) p q) :
    Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ (Localization.latGraph d n).Adj u v) p q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    rename_i b c _
    by_cases hbc' : b = c
    · rw [← hbc']; exact ih
    · exact ih.tail ⟨hbc.1, hbc.2.1, hbc', hbc.2.2⟩

omit [NeZero n] in
/-- **A nonempty set all of whose points are joined to a base point by nearest-neighbour paths
inside the set is an animal of the cube graph.** -/
theorem isAnimal_latGraph_of_base {X : Finset (Torus d n)} {x₀ : Torus d n} (hx₀ : x₀ ∈ X)
    (h : ∀ q ∈ X, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ NNAdj u v) x₀ q) :
    Polymer.IsAnimal (Localization.latGraph d n) X := by
  rw [Polymer.isAnimal_iff]
  refine ⟨⟨x₀, hx₀⟩, fun p hp q hq => ?_⟩
  have hsymm : ∀ {a b}, Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ NNAdj u v) a b →
      Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ NNAdj u v) b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, nnAdj_symm hbc.2.2⟩ ih
  exact rtg_latGraph_of_nn ((hsymm (h p hp)).trans (h q hq))

/-- **The cube graph has degree at most `2d`**: the neighbours of `v` are among `v ± e_μ`. -/
theorem latGraph_degree_le (v : Torus d n) : (Localization.latGraph d n).degree v ≤ 2 * d := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (Localization.latGraph d n).neighborFinset v ⊆
      (Finset.univ : Finset (Fin d × Bool)).image
        (fun p => if p.2 then v + Pi.single p.1 1 else v - Pi.single p.1 1) := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    obtain ⟨μ, h | h⟩ := hw.2
    · exact Finset.mem_image.mpr ⟨(μ, true), Finset.mem_univ _, by simp [h]⟩
    · exact Finset.mem_image.mpr ⟨(μ, false), Finset.mem_univ _, by simp [h]⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, mul_comm]

/-- Nearest-neighbour reachability inside a set. -/
def NNReach (X : Finset (Torus d n)) (a b : Torus d n) : Prop :=
  Relation.ReflTransGen (fun u v => u ∈ X ∧ v ∈ X ∧ NNAdj u v) a b

omit [NeZero n] in
theorem NNReach.symm {X : Finset (Torus d n)} {a b : Torus d n} (h : NNReach X a b) :
    NNReach X b a := by
  unfold NNReach at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, nnAdj_symm hbc.2.2⟩ ih

omit [NeZero n] in
theorem NNReach.trans {X : Finset (Torus d n)} {a b c : Torus d n} (h : NNReach X a b)
    (h' : NNReach X b c) : NNReach X a c :=
  Relation.ReflTransGen.trans h h'

/-- A point of a sup-ball contained in `X` is reached from the centre inside `X`. -/
theorem nnReach_of_ball {X : Finset (Torus d n)} {c q : Torus d n} {r : ℕ}
    (hball : ∀ z, supDist c z ≤ r → z ∈ X) (hq : supDist c q ≤ r) : NNReach X c q := by
  unfold NNReach
  exact Relation.ReflTransGen.mono (fun _ _ huv => ⟨hball _ huv.1, hball _ huv.2.1, huv.2.2⟩) _ _
    (nn_path_in_ball c q hq)

/-- Points linked at sup-distance `< ω` inside `Z` are reached inside `X` when `X` contains the
`r`-balls around the points of `Z`, `ω ≤ r`. -/
theorem nnReach_of_linked {X : Finset (Torus d n)} {Z : Set (Torus d n)} {ω r : ℕ} (hωr : ω ≤ r)
    (hball : ∀ a ∈ Z, ∀ z, supDist a z ≤ r → z ∈ X) {x y : Torus d n}
    (h : Linked ω Z x y) : NNReach X x y := by
  unfold Linked at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    exact ih.trans (nnReach_of_ball (hball _ hbc.1) (by omega))

/-- **The union of the `r`-neighbourhoods of a chain of linked sets is an animal.**  The sets
`Z i`, `i ∈ C`, are nonempty, each linked at sup-distance `< ω ≤ r`, and the family is connected
under "some points at sup-distance `≤ 2r`". -/
theorem isAnimal_biUnion_nbhd {ι : Type*} {C : Finset ι} (Z : ι → Finset (Torus d n)) {ω r : ℕ}
    (hωr : ω ≤ r) {i₀ : ι} (hi₀ : i₀ ∈ C) (hZne : ∀ i ∈ C, (Z i).Nonempty)
    (hlink : ∀ i ∈ C, ∀ x ∈ Z i, ∀ y ∈ Z i, Linked ω (Z i : Set (Torus d n)) x y)
    (hconn : ∀ j ∈ C, Relation.ReflTransGen
      (fun a b => a ∈ C ∧ b ∈ C ∧ ∃ x ∈ Z a, ∃ y ∈ Z b, supDist x y ≤ 2 * r) i₀ j) :
    Polymer.IsAnimal (Localization.latGraph d n)
      (Finset.univ.filter (· ∈ ⋃ i ∈ C, nbhd r (Z i : Set (Torus d n)))) := by
  set U := Finset.univ.filter (· ∈ ⋃ i ∈ C, nbhd r (Z i : Set (Torus d n))) with hU
  have hball : ∀ i ∈ C, ∀ a ∈ (Z i : Set (Torus d n)), ∀ z, supDist a z ≤ r → z ∈ U := by
    intro i hi a ha z hz
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    exact ⟨i, hi, mem_nbhd.mpr ⟨a, ha, by rw [supDist_comm]; exact hz⟩⟩
  obtain ⟨x₀, hx₀⟩ := hZne i₀ hi₀
  -- every point of every `Z j` is reached from `x₀`
  have hreach : ∀ j ∈ C, ∀ y ∈ Z j, NNReach U x₀ y := by
    intro j hj
    have hc := hconn j hj
    induction hc with
    | refl =>
      intro y hy
      exact nnReach_of_linked hωr (hball i₀ hi₀) (hlink i₀ hi₀ x₀ hx₀ y hy)
    | tail _ hab ih =>
      rename_i a b _
      obtain ⟨ha, hb, x, hx, y', hy', hxy⟩ := hab
      intro y hy
      obtain ⟨z, hxz, hzy⟩ := exists_split (a := r) (b := r) (by omega : supDist x y' ≤ r + r)
      have h1 : NNReach U x₀ x := ih ha x hx
      have h2 : NNReach U x z := nnReach_of_ball (hball a ha x hx) hxz
      have h3 : NNReach U z y' :=
        (nnReach_of_ball (hball b hb y' hy') (by rw [supDist_comm]; exact hzy)).symm
      have h4 : NNReach U y' y :=
        nnReach_of_linked hωr (hball b hb) (hlink b hb y' hy' y hy)
      exact ((h1.trans h2).trans h3).trans h4
  refine isAnimal_latGraph_of_base (x₀ := x₀)
    (hball i₀ hi₀ x₀ hx₀ x₀ (by rw [supDist_self]; exact Nat.zero_le _)) fun q hq => ?_
  simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    at hq
  obtain ⟨j, hj, hqj⟩ := hq
  obtain ⟨x, hx, hqx⟩ := mem_nbhd.mp hqj
  exact (hreach j hj x hx).trans
    (nnReach_of_ball (hball j hj x hx) (by rw [supDist_comm]; exact hqx))

end Balaban.LargeField.G0
