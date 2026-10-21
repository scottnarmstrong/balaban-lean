/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.NextBook

/-!
# The book of a component is invariant under a reindexing of its parts

`Setting.nextBook` reads its parts only through a finite set and a function on it
(card, sums, sup, unions, the unique element of a singleton), so it is unchanged when the parts are
replaced by their image under an embedding with the transported function
(`nextBook_map`; with `t4State_map`, `nextClock_map`, `nextState_map`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

theorem t4State_map {ι ι' : Type*} (S : Setting) (μ : ℕ) (parts : Finset ι) (e : ι ↪ ι')
    (f' : ι' → Book) (s' : ℕ) :
    S.t4State μ (parts.map e) f' s' = S.t4State μ parts (f' ∘ e) s' := by
  classical
  have h1 : Setting.t4Q (parts.map e) f' = Setting.t4Q parts (f' ∘ e) := by
    simp [Setting.t4Q, Finset.sup_map, Function.comp_def]
  have h2 : Setting.t4E μ (parts.map e) f' = Setting.t4E μ parts (f' ∘ e) := by
    ext x
    simp [Setting.t4E, Finset.mem_biUnion]
  have h3 : S.t4t0 (parts.map e) f' s' = S.t4t0 parts (f' ∘ e) s' := by
    simp [Setting.t4t0, h1]
  have h4 : S.t4T μ (parts.map e) f' s' = S.t4T μ parts (f' ∘ e) s' := by
    simp [Setting.t4T, h2, h3]
  have h5 : S.t4q μ (parts.map e) f' s' = S.t4q μ parts (f' ∘ e) s' := by
    simp [Setting.t4q, h4]
  simp [Setting.t4State, h5, h2, Finset.sum_map]

theorem nextClock_map {ι ι' : Type*} (S : Setting) (μ : ℕ) (parts : Finset ι) (e : ι ↪ ι')
    (f' : ι' → Book) (r : ℕ) (len : ℝ) :
    S.nextClock μ (parts.map e) f' r len = S.nextClock μ parts (f' ∘ e) r len := by
  classical
  simp [Setting.nextClock, Finset.sup_map, Function.comp_def]

theorem nextState_map {ι ι' : Type*} (S : Setting) (μ : ℕ) (parts : Finset ι) (e : ι ↪ ι')
    (f' : ι' → Book) (r : ℕ) (pt' : Prop) (s' : ℕ) :
    S.nextState μ (parts.map e) f' r pt' s' = S.nextState μ parts (f' ∘ e) r pt' s' := by
  classical
  unfold Setting.nextState
  by_cases h1 : 1 ≤ r
  · simp [h1]
  simp only [h1, ite_false]
  by_cases hc : parts.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    simp
  · have hc' : (parts.map e).card ≠ 1 := by simpa using hc
    simp only [hc, hc', dite_false]
    simp [Finset.sum_map, t4State_map, Function.comp_def]

theorem nextBook_map {ι ι' : Type*} (S : Setting) (μ : ℕ) (parts : Finset ι) (e : ι ↪ ι')
    (f' : ι' → Book) (r : ℕ) (Γ' : Spine S.d) :
    S.nextBook μ (parts.map e) f' r Γ' = S.nextBook μ parts (f' ∘ e) r Γ' := by
  simp only [Setting.nextBook, nextState_map, nextClock_map]

end Balaban.LargeField
