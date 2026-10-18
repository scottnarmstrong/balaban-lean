/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.Polymer.GasLinkedEq

/-!
# Crossing terms at the last integral

P7, printed p. 532, following (4.11), retains a localized boundary term exactly when its
localization domain intersects a selected large-field component and its complement. A single
coverage-activated label cannot express this selected-set dependence. The exact elementary
identity uses an intersection trigger and an all-required trigger with opposite coefficients.
It is an identity of functions of the selected set before application of P7's operator
`T'_{k+1}`; it does not turn a field-dependent boundary term into a scalar gas coefficient.
-/

@[expose] public section

open scoped Classical
open Finset

namespace Balaban.Green

/-- For a nonempty localization domain, full coverage implies intersection. This gives the
exact two-trigger identity for the crossing part of P7 p. 532, after (4.11). -/
theorem finalCrossing_two_triggers {B : Type*} [DecidableEq B]
    {F Z : Finset B} (hF : F.Nonempty) (w : ℂ) :
    (if ¬ Disjoint F Z ∧ ¬ F ⊆ Z then w else 0) =
      (if ¬ Disjoint F Z then w else 0) - (if F ⊆ Z then w else 0) := by
  by_cases hs : F ⊆ Z
  · have hm : ¬ Disjoint F Z := by
      obtain ⟨b, hb⟩ := hF
      exact Finset.not_disjoint_iff.mpr ⟨b, hb, hs hb⟩
    simp [hs, hm]
  · by_cases hm : ¬ Disjoint F Z <;> simp [hs, hm]

/-- The two fixed triggers are literally the intersection and all-required modes of
`gasLinkedActive`. This only rewrites a field-dependent coefficient *before* the selected
operator is applied. -/
theorem finalCrossing_eq_linked_triggers {B : Type*} [Fintype B] [DecidableEq B]
    {F Z : Finset B} (hF : F.Nonempty) (w : ℂ) :
    (if ¬ Disjoint F Z ∧ ¬ F ⊆ Z then w else 0) =
      (if Balaban.Polymer.gasLinkedActive (fun y : Bool => y) (fun _ => F)
          (fun z : B => {z}) Z false then w else 0) -
        (if Balaban.Polymer.gasLinkedActive (fun y : Bool => y) (fun _ => F)
          (fun z : B => {z}) Z true then w else 0) := by
  rw [finalCrossing_two_triggers hF w]
  simp [Balaban.Polymer.gasLinkedActive, hF]

/-- The fixed-coefficient version, summed over nonempty elementary supports. The two terms on
the right can be represented by linked labels with `allRequired = false` and `true`,
respectively; this is still before integration over the bad variables. -/
theorem finalCrossing_sum_two_triggers {B : Type*} [DecidableEq B]
    (terms : Finset (Finset B)) (hne : ∀ F ∈ terms, F.Nonempty)
    (w : Finset B → ℂ) (Z : Finset B) :
    (∑ F ∈ terms, if ¬ Disjoint F Z ∧ ¬ F ⊆ Z then w F else 0) =
      (∑ F ∈ terms, if ¬ Disjoint F Z then w F else 0) -
        (∑ F ∈ terms, if F ⊆ Z then w F else 0) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro F hF
  exact finalCrossing_two_triggers (hne F hF) (w F)

/-- A one-label `gasLinkedActive` trigger cannot equal the crossing indicator on every
selected set. Already the two-site footprint `{a,b}` is a counterexample: it crosses `{a}`
but is wholly bad for `{a,b}`. This applies to either linked activation mode. -/
theorem no_single_linked_label_for_crossing
    {B Yt : Type*} [Fintype B] [Fintype Yt] [DecidableEq B]
    (a b : B) (hab : a ≠ b)
    (allRequired : Yt → Bool) (activation : Yt → Finset B) (y : Yt)
    (hact : ∀ Z : Finset B,
      Balaban.Polymer.gasLinkedActive allRequired activation (fun z : B => {z}) Z y ↔
        ¬ Disjoint ({a, b} : Finset B) Z ∧ ¬ ({a, b} : Finset B) ⊆ Z) :
    False := by
  have hcross : ¬ Disjoint ({a, b} : Finset B) ({a} : Finset B) ∧
      ¬ ({a, b} : Finset B) ⊆ ({a} : Finset B) := by
    constructor
    · exact Finset.not_disjoint_iff.mpr ⟨a, by simp, by simp⟩
    · intro hs
      have hb : b ∈ ({a} : Finset B) := hs (by simp)
      simp only [mem_singleton] at hb
      exact hab hb.symm
  have hsmall := (hact {a}).2 hcross
  have hlarge := Balaban.Polymer.gasLinkedActive_mono
    (allRequired := allRequired) (activation := activation)
    (cr := fun z : B => {z}) (by simp : ({a} : Finset B) ⊆ {a, b}) y hsmall
  have hfull : ({a, b} : Finset B) ⊆ ({a, b} : Finset B) := Subset.rfl
  exact ((hact {a, b}).1 hlarge).2 hfull

end Balaban.Green
