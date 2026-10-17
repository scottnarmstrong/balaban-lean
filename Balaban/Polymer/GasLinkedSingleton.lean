/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedCore
import Balaban.Green.FinalTailGas
import Mathlib.Tactic.Linarith

/-!
# Linked gas with one heavy object per bad block

The heavy support and core of a bad block are its singleton. Couplings can require several
bad blocks while carrying decay on a connected charged footprint. The numeric heavy threshold
is the singleton threshold of the landed final-integral gas.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Singleton

variable {B Yt : Type*} [Fintype B] [Fintype Yt]
  {allRequired : Yt → Bool} {activation footprint : Yt → Finset B}
  {β : Yt → ℂ} {τ : B → ℂ}

/-- A linked singleton gas has an exact polymer partition function. -/
theorem gasLinked_singleton_eq
    (hact : ∀ y, activation y ⊆ footprint y) :
    gasLinkedXi allRequired activation (fun z => {z}) (fun z => {z}) β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (gasLinkedK allRequired activation footprint
          (fun z => {z}) (fun z => {z}) β τ) := by
  exact gasLinked_eq allRequired activation footprint (fun z => {z})
    (fun z => {z}) β τ hact (fun z => by simp) (fun z => by simp)

/-- At most one singleton heavy label of each size contains a fixed block. -/
private theorem linked_singleton_heavy_count (b : B) (v : ℕ) :
    ((Finset.univ.filter (fun z : B => b ∈ ({z} : Finset B) ∧
      ({z} : Finset B).card = v)).card : ℝ) ≤ (1 : ℝ) ^ v := by
  have hc : (Finset.univ.filter (fun z : B => b ∈ ({z} : Finset B) ∧
      ({z} : Finset B).card = v)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro z hz z' hz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hz hz'
    exact hz.1.symm.trans hz'.1
  have hc' : ((Finset.univ.filter (fun z : B => b ∈ ({z} : Finset B) ∧
      ({z} : Finset B).card = v)).card : ℝ) ≤ 1 := by
    exact_mod_cast hc
  simpa using hc'

/-- Footprint decay and singleton heavy decay imply the linked activity estimate with the
same numeric threshold as the landed singleton last-integral gas. -/
theorem gasLinked_singleton_activity_bound
    (hact : ∀ y, activation y ⊆ footprint y)
    {B0 κ' κ'' P H : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκκ : κ' ≤ κ'') (hP : 0 ≤ P)
    (hent : ∀ b : B,
      ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint y),
        Real.exp (-(κ'' - κ') * ((footprint y).card : ℝ)) ≤ 1)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * ((footprint y).card : ℝ)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-P - H))
    (hH : B0 * Real.exp B0 + κ' + 4 ≤ H)
    (X : NePoly B) :
    ‖gasLinkedK allRequired activation footprint
      (fun z => {z}) (fun z => {z}) β τ X‖ ≤
      3 * Real.exp (-P) * Real.exp (-(κ' - 2) * (X.1.card : ℝ)) := by
  have hmain : ‖gasLinkedK allRequired activation footprint
      (fun z => {z}) (fun z => {z}) β τ X‖ ≤
      3 * 1 * Real.exp (-P) * Real.exp (-(κ' - 2) * (X.1.card : ℝ)) := by
    refine gasLinked_activity_bound (d := fun S : Finset B => (S.card : ℝ))
      (allRequired := allRequired) (activation := activation) (footprint := footprint)
      (zs := fun z : B => {z}) (cr := fun z : B => {z}) (β := β) (τ := τ)
      (c := 0) (c1 := 1) (c2 := 1) (B0 := B0) (κ' := κ') (κ'' := κ'')
      (p := P) (h := H)
      hact hB0 hκ' hκκ le_rfl zero_le_one hP
      (fun _ => Nat.cast_nonneg _) (fun z => by simp) (fun z => by simp)
      hB ?_ ?_ ?_ (K0' := 1) (K0'' := 1) zero_le_one ?_ le_rfl
      ?_ ?_ X ?_
    · intro z
      simpa using hτ z
    · intro z
      simp
    · intro C _ _
      simpa [gasCs] using
        card_unionCs_le (V := B)
          (gasCs footprint (fun z : B => ({z} : Finset B))) C
    · intro b
      exact hent b
    · intro b v
      exact linked_singleton_heavy_count b v
    · have := hH
      norm_num at this ⊢
      linarith
    · simp
  simpa only [one_mul, mul_one] using hmain

end Singleton

end Balaban.Polymer
