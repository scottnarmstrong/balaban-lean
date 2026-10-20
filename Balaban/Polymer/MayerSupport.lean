/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Mayer
public import Balaban.Polymer.Support
public import Balaban.Polymer.MarkedCubesVanish
import Mathlib.Tactic.Positivity

/-!
# Vanishing of the Mayer gas on non-connected block sets

For terms `H t` supported on connected sets of blocks only, the Mayer activity of a non-connected
block set vanishes (`mayerK_eq_zero_of_not_isAnimal`: a connected family of connected supports has
a connected union, `isAnimal_unionCs_of_connSet`), and so do the local terms `P(Y)` of the gas on
nonempty block sets (`PY_shareBlock_eq_zero_of_not_isAnimal`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Support

variable {B : Type*} (H : SimpleGraph B)

/-- A connected family of connected supports has a connected union. -/
theorem isAnimal_unionCs_of_connSet {E : Type*} (cs : E → Finset B) {D : Finset E}
    (hconn : ConnSet cs D) (hS : ∀ t ∈ D, IsAnimal H (cs t)) : IsAnimal H (unionCs cs D) := by
  set U := unionCs cs D with hU
  have hmem : ∀ t ∈ D, ∀ p ∈ cs t, p ∈ U := fun t ht p hp => mem_unionCs.mpr ⟨t, ht, hp⟩
  have hin : ∀ t ∈ D, ∀ p ∈ cs t, ∀ q ∈ cs t,
      Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro t ht p hp q hq
    have := ((isAnimal_iff H _).mp (hS t ht)).2 p hp q hq
    exact Relation.ReflTransGen.mono
      (fun a b hab => ⟨hmem t ht a hab.1, hmem t ht b hab.2.1, hab.2.2⟩) _ _ this
  have hreach : ∀ t s, Reach cs D t s → t ∈ D →
      ∀ p ∈ cs t, ∀ q ∈ cs s, Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ H.Adj a b) p q := by
    intro t s h htD
    induction h with
    | refl => exact hin t htD
    | @tail b c _ hbc ih =>
      intro p hp q hq
      obtain ⟨_, hcD, hcont⟩ := hbc
      obtain ⟨r, hr1, hr2⟩ := Finset.not_disjoint_iff.mp hcont
      exact (ih p hp r hr1).trans (hin c hcD r hr2 q hq)
  rw [isAnimal_iff]
  obtain ⟨t0, ht0⟩ := hconn.1
  refine ⟨?_, fun p hp q hq => ?_⟩
  · obtain ⟨b, hb⟩ := ((isAnimal_iff H _).mp (hS t0 ht0)).1
    exact ⟨b, hmem t0 ht0 b hb⟩
  · obtain ⟨t, ht, hpt⟩ := mem_unionCs.mp hp
    obtain ⟨s, hs, hqs⟩ := mem_unionCs.mp hq
    exact hreach t s (hconn.2 t ht s hs) ht p hpt q hqs

variable [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) {T : Type*} [Fintype T] (sup : T → Finset B)
  (Hf : T → (∀ b, Ω b) → ℂ)

/-- **The Mayer activity of a non-connected block set vanishes, general weights**, when the weights
of the terms supported on non-connected sets vanish. -/
theorem mayerGenK_eq_zero_of_not_isAnimal (f : T → (∀ b, Ω b) → ℂ)
    (hf : ∀ t, ¬ IsAnimal H (sup t) → ∀ Φ, f t Φ = 0)
    (Z : NePoly B) (hZ : ¬ IsAnimal H Z.1) : mayerGenK μ sup f Z = 0 := by
  unfold mayerGenK
  refine (integral_congr_ae (g := fun _ => (0 : ℂ)) (Filter.Eventually.of_forall fun Φ => ?_)).trans
    (integral_zero _ _)
  unfold mayerGenAct polyAct
  refine Finset.sum_eq_zero fun C hC => ?_
  obtain ⟨hconn, -, hU⟩ := mem_Cfam.1 hC
  have : ∃ t ∈ C, ¬ IsAnimal H (sup t) := by
    by_contra hall
    push Not at hall
    exact hZ (hU ▸ isAnimal_unionCs_of_connSet H sup hconn hall)
  obtain ⟨t, htC, ht⟩ := this
  exact Finset.prod_eq_zero htC (hf t ht Φ)

/-- **The Mayer activity of a non-connected block set vanishes** when the terms supported on
non-connected sets vanish. -/
theorem mayerK_eq_zero_of_not_isAnimal (hH : ∀ t, ¬ IsAnimal H (sup t) → ∀ Φ, Hf t Φ = 0)
    (Z : NePoly B) (hZ : ¬ IsAnimal H Z.1) : mayerK μ sup Hf Z = 0 :=
  mayerGenK_eq_zero_of_not_isAnimal H μ sup (fun t Φ => Complex.exp (Hf t Φ) - 1)
    (fun t ht Φ => by simp [hH t ht Φ]) Z hZ

/-- **The local terms of a non-connected block set vanish** when the activities of the
non-connected sets vanish. -/
theorem PY_shareBlock_eq_zero_of_not_isAnimal (K : NePoly B → ℂ)
    (hK : ∀ Z : NePoly B, ¬ IsAnimal H Z.1 → K Z = 0) (Y : Finset B) (hY : ¬ IsAnimal H Y) :
    PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val K Y = 0 := by
  refine PY_eq_zero_of_forall _ _ K Y fun n X hXU hconn => ?_
  have : ∃ i, ¬ IsAnimal H (X i).1 := by
    by_contra hall
    push Not at hall
    let X' : Fin (n + 1) → BlockPolymer H := fun i => ⟨(X i).1, hall i⟩
    have hc : (clusterGraph (overlap H) X').Connected := by
      have : clusterGraph (overlap H) X' = clusterGraph (shareBlock (Subtype.val : NePoly B →
          Finset B)) X := by
        ext i j
        rw [clusterGraph_adj, clusterGraph_adj, lnk_overlap, lnk_shareBlock]
        rfl
      rw [this]; exact hconn
    exact hY (hXU ▸ isAnimal_unionOf X' hc)
  obtain ⟨i, hi⟩ := this
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hK _ hi)

end Support

end Balaban.Polymer
