module

public import Balaban.Polymer.Local
public import Balaban.Polymer.Lattice

/-!
# Support of the local terms on block polymers

For block polymers (nonempty `H`-connected block sets), connectedness of a block set is the same as
path-connectedness inside the set (`isAnimal_iff`), the union of the members of a cluster with
connected incompatibility graph is again connected (`isAnimal_unionOf`), and hence the local term
`P(Y)` vanishes unless `Y` is itself a polymer (`PY_eq_zero_of_not_isAnimal`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Animal

variable {B : Type*} (H : SimpleGraph B)

/-- Connectedness of a block set as path-connectedness inside the set. -/
theorem isAnimal_iff (X : Finset B) :
    IsAnimal H X ↔ X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X,
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ H.Adj a b) x y := by
  constructor
  · rintro ⟨hne, hc⟩
    refine ⟨hne, fun x hx y hy => ?_⟩
    have hr := hc.preconnected ⟨x, hx⟩ ⟨y, hy⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    exact Relation.ReflTransGen.lift (fun a : (X : Set B) => (a : B))
      (r := (H.induce (X : Set B)).Adj) (p := fun a b => a ∈ X ∧ b ∈ X ∧ H.Adj a b)
      (fun a b hab => ⟨a.2, b.2, hab⟩) _ _ hr
  · rintro ⟨hne, hp⟩
    refine ⟨hne, ?_⟩
    have : Nonempty (X : Set B) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have key : ∀ y, Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ H.Adj a b) a y →
        ∀ hy : y ∈ X, (H.induce (X : Set B)).Reachable ⟨a, ha⟩ ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | tail hab hbc ih =>
        intro hc
        exact (ih hbc.1).trans (SimpleGraph.Adj.reachable hbc.2.2)
    exact key b (hp a ha b hb) hb

variable {H}

/-- The union of the members of a cluster with connected incompatibility graph is connected. -/
theorem isAnimal_unionOf {n : ℕ} (X : Fin (n + 1) → BlockPolymer H)
    (hc : (clusterGraph (overlap H) X).Connected) :
    IsAnimal H (unionOf (fun Z : BlockPolymer H => Z.1) X) := by
  set U := unionOf (fun Z : BlockPolymer H => Z.1) X with hU
  have hmem : ∀ i, ∀ p ∈ (X i).1, p ∈ U := fun i p hp => by
    simp only [hU, unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hp⟩
  have hin : ∀ i, ∀ p ∈ (X i).1, ∀ q ∈ (X i).1,
      Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro i p hp q hq
    have := ((isAnimal_iff H _).mp (X i).2).2 p hp q hq
    exact Relation.ReflTransGen.mono (fun a b hab => ⟨hmem i a hab.1, hmem i b hab.2.1, hab.2.2⟩)
      _ _ this
  rw [isAnimal_iff]
  refine ⟨⟨(X 0).2.1.choose, hmem 0 _ (X 0).2.1.choose_spec⟩, ?_⟩
  intro p hp q hq
  simp only [hU, unionOf, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp hq
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  have hr := hc.preconnected i j
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  have key : ∀ k, Relation.ReflTransGen (clusterGraph (overlap H) X).Adj i k →
      ∀ q ∈ (X k).1, Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro k hk
    induction hk with
    | refl => intro q hq; exact hin i p hi q hq
    | tail hab hbc ih =>
      rename_i b c
      intro q hq
      have hov : overlap H (X b) (X c) := by
        have := hbc.2
        exact (lnk_overlap H _ _).mp this
      obtain ⟨r, hrb, hrc⟩ := Finset.not_disjoint_iff.mp hov
      exact (ih r hrb).trans (hin c r hrc q hq)
  exact key j hr q hj

end Animal

section Vanishing

variable {B : Type*} {H : SimpleGraph B}

/-- The cluster terms with union `Y` vanish unless `Y` is a polymer. -/
theorem Pterm_eq_zero_of_not_isAnimal [Fintype (BlockPolymer H)] (K : BlockPolymer H → ℂ)
    (Y : Finset B) (hY : ¬ IsAnimal H Y) (n : ℕ) :
    Pterm (overlap H) (fun X => X.1) K Y n = 0 := by
  unfold Pterm
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero (fun X hX => ?_)
  rw [Finset.mem_filter] at hX
  have hnc : ¬ (clusterGraph (overlap H) X).Connected := fun hc => hY (hX.2 ▸ isAnimal_unionOf X hc)
  have h0 := aaw_eq_zero_of_not_connected (overlap H) X hnc
  have : ‖(clusterUrsell (overlap H) X Finset.univ : ℂ)‖ = 0 := by
    rw [norm_ursell_eq]; exact h0
  rw [norm_eq_zero.mp this, zero_mul]

theorem PY_eq_zero_of_not_isAnimal [Fintype (BlockPolymer H)] (K : BlockPolymer H → ℂ)
    (Y : Finset B) (hY : ¬ IsAnimal H Y) : PY (overlap H) (fun X => X.1) K Y = 0 := by
  unfold PY
  simp [Pterm_eq_zero_of_not_isAnimal K Y hY]

end Vanishing

end Balaban.Polymer
