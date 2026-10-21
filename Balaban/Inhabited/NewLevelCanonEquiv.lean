/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Function

/-!
# The partial index bijection of two canonically indexed families

`partialEquiv_of_pairs`: let `p : ι → P` and `p' : ι' → P'` be injective index maps and `φ : P → P'`.
For predicates `Dom`, `Dom'` such that every `τ` with `Dom τ` has a partner `τ'` with `p' τ' = φ (p τ)`
(which then satisfies `Dom'`), every `τ'` with `Dom' τ'` is such a partner, and `φ ∘ p` is injective on
`Dom`, there is an equivalence `e` of the subtypes with `p' (e τ) = φ (p τ)`.
-/

@[expose] public section

namespace Balaban.Inhabited

/-- **A partial index bijection from the correspondence of the index pairs.** -/
theorem partialEquiv_of_pairs {ι ι' P P' : Type*} (p : ι → P) (p' : ι' → P') (φ : P → P')
    (Dom : ι → Prop) (Dom' : ι' → Prop) (hp' : Function.Injective p')
    (hex : ∀ τ, Dom τ → ∃ τ', p' τ' = φ (p τ))
    (hDom : ∀ τ τ', Dom τ → p' τ' = φ (p τ) → Dom' τ')
    (hback : ∀ τ', Dom' τ' → ∃ τ, Dom τ ∧ p' τ' = φ (p τ))
    (hinj : ∀ τ₁ τ₂, Dom τ₁ → Dom τ₂ → φ (p τ₁) = φ (p τ₂) → τ₁ = τ₂) :
    ∃ e : {τ // Dom τ} ≃ {τ' // Dom' τ'}, ∀ τ : {τ // Dom τ}, p' (e τ).1 = φ (p τ.1) := by
  classical
  let f : {τ // Dom τ} → {τ' // Dom' τ'} := fun τ =>
    ⟨(hex τ.1 τ.2).choose, hDom τ.1 _ τ.2 (hex τ.1 τ.2).choose_spec⟩
  have hf : ∀ τ : {τ // Dom τ}, p' (f τ).1 = φ (p τ.1) := fun τ => (hex τ.1 τ.2).choose_spec
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, fun b => ?_⟩, fun τ => hf τ⟩
  · refine Subtype.ext (hinj a.1 b.1 a.2 b.2 ?_)
    rw [← hf a, ← hf b, h]
  · obtain ⟨τ, hτ, hb⟩ := hback b.1 b.2
    refine ⟨⟨τ, hτ⟩, Subtype.ext (hp' ?_)⟩
    rw [hf, hb]

end Balaban.Inhabited
