/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Complex.Basic

/-!
# The sum over the old terms under a bijection of the index types

The explicit thick activity `H` of a new-level system is a sum over the old terms `τ` of the
conditional difference of two localized terms (`if Y ∈ polyDom τ then β (T₁ τ - T₀ τ) else 0`).
For two systems whose old terms correspond under a bijection `e` of the index types, with
`Y ∈ polyDom τ ↔ Y' ∈ polyDom' (e τ)` and corresponding values of the two localized terms
(`evDec_oldTerm_twoTorus`, at the marks `(u, 0)` and `(0, 0)`), the sums agree:

* `sum_ite_equiv`: the generic statement;
* `sum_ite_sub_equiv`: for the difference of two terms.
-/

@[expose] public section

namespace Balaban.Inhabited

/-- **A conditional sum under a bijection of the index types.** -/
theorem sum_ite_equiv {ι ι' : Type*} {_ : Fintype ι} {_ : Fintype ι'} (e : ι ≃ ι') (P : ι → Prop)
    (P' : ι' → Prop) {_ : DecidablePred P} {_ : DecidablePred P'} (f : ι → ℂ) (f' : ι' → ℂ)
    (hP : ∀ τ, P τ ↔ P' (e τ)) (hf : ∀ τ, P τ → f' (e τ) = f τ) :
    ∑ τ', (if P' τ' then f' τ' else 0) = ∑ τ, (if P τ then f τ else 0) := by
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases h : P τ
  · simp only [(hP τ).1 h, h, ite_true, hf τ h]
  · have h2 : ¬ P' (e τ) := fun h' => h ((hP τ).2 h')
    simp only [h, h2, ite_false]

/-- **A conditional sum of differences under a bijection**, from the agreement of each of the two
terms. -/
theorem sum_ite_sub_equiv {ι ι' : Type*} {_ : Fintype ι} {_ : Fintype ι'} (e : ι ≃ ι') (P : ι → Prop)
    (P' : ι' → Prop) {_ : DecidablePred P} {_ : DecidablePred P'} (c c' : ℂ) (hc : c' = c)
    (g h : ι → ℂ)
    (g' h' : ι' → ℂ) (hP : ∀ τ, P τ ↔ P' (e τ)) (hg : ∀ τ, P τ → g' (e τ) = g τ)
    (hh : ∀ τ, P τ → h' (e τ) = h τ) :
    ∑ τ', (if P' τ' then c' * (g' τ' - h' τ') else 0) =
      ∑ τ, (if P τ then c * (g τ - h τ) else 0) :=
  sum_ite_equiv e P P' (fun τ => c * (g τ - h τ)) (fun τ' => c' * (g' τ' - h' τ')) hP
    fun τ hτ => by rw [hg τ hτ, hh τ hτ, hc]

end Balaban.Inhabited
