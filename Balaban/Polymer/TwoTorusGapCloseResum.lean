/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapClose

/-!
# The gap-scale torus clause for the step with no inherited terms, and what the inherited terms add

`resum_gapScale_torus` (`TwoTorusGapAssembly`) needs the closeness `hFclose` of the terms on `ℓ` and
on the canonical torus `can X` for the compact supports `X` of the quarter box.

* `hFclose_of_exact`, `resum_gapScale_torus_exact`: for the step with no inherited terms the terms are
  equal on these supports (`evDec_boxMap_of_diameter` for the marked block-energy terms), so
  `hFclose` holds with `a = 0` and `resum_gapScale_torus` holds with the constant
  `B + 2 B e^{κ₂} + 2 B e^{κ₂ t₀}`.
* `hFclose_of_split`, `resum_gapScale_torus_inherited`: for the step with inherited terms
  `T = Tnew + Tinh`, the closeness holds with the constant of the inherited terms, which is the torus
  clause for them at the earlier scales (the induction hypothesis `hinh`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer

section Close

variable {d : ℕ}

/-- **What the inherited terms add (item 24, part 3).**  The terms of the step are the sum
`T = Tnew + Tinh` of the new terms (the step with no inherited terms) and the terms inherited from
the earlier scales.  The new terms satisfy the exact torus clause on the compact supports of the
quarter box (`hnew`; for the marked block-energy terms this is `evDec_boxMap_of_diameter`).  The
inherited terms satisfy the torus clause of the earlier scales, which is the induction hypothesis
(`hinh`): for such `X` the inherited terms on `ℓ` and on `can X` are close, with the constant `a`
and the decay `e^{-lam τ} e^{-κ₂ |X|}`.  Then the closeness `hFclose` of `resum_gapScale_torus` holds
with the constant `a` of the inherited terms: the new terms add nothing. -/
theorem hFclose_of_split {ι G : Type*} (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (T Tnew Tinh : ι → G → Finset (Fin d → ℤ) → ℂ) (Wd : ι → Finset (Fin d → ℤ) → Prop)
    {a lam κ₂ : ℝ} {t₀ : ℕ}
    (hsplit : ∀ ℓ g X, T ℓ g X = Tnew ℓ g X + Tinh ℓ g X)
    (hnew : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      Tnew ℓ g X = Tnew (can X) g X)
    (hinh : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖Tinh ℓ g X - Tinh (can X) g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by
  intro ℓ X hX hQ hW ht g hg
  have h : T ℓ g X - T (can X) g X = Tinh ℓ g X - Tinh (can X) g X := by
    rw [hsplit, hsplit, hnew ℓ X hX hQ hW ht g hg]; ring
  rw [h]
  exact hinh ℓ X hX hQ hW ht g hg

/-- **The closeness at the gap scale for the step with no inherited terms.**  If the terms on `ℓ`
and on `can X` are equal for the compact supports `X` of the quarter box with margin at least `t₀`,
then `hFclose` of `resum_gapScale_torus` holds with `a = 0`. -/
theorem hFclose_of_exact {ι G : Type*} (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (T : ι → G → Finset (Fin d → ℤ) → ℂ) (Wd : ι → Finset (Fin d → ℤ) → Prop)
    {lam κ₂ : ℝ} {t₀ : ℕ}
    (hexact : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      T ℓ g X = T (can X) g X) :
    ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤
        (0 : ℝ) * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by
  intro ℓ X hX hQ hW ht g hg
  rw [hexact ℓ X hX hQ hW ht g hg, sub_self, norm_zero, zero_mul, zero_mul]

/-- **The torus clause at a gap scale for the step with inherited terms** (item 24, part 3):
`resum_gapScale_torus` with the closeness `hFclose` replaced by its two inputs, the exact torus clause
of the new terms (`hnew`) and the torus clause of the inherited terms at the earlier scales
(`hinh`, with the constant `a`). -/
theorem resum_gapScale_torus_inherited {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (Wd : ι → Finset (Fin d → ℤ) → Prop)
    {B a κ κ₂ κ' lam : ℝ} {t₀ : ℕ}
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hWd : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Wd ℓ X → K ℓ ≤ 25 * X.card)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hκ₂ : κ + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (Tnew Tinh : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hsplit : ∀ ℓ g X, T ℓ g X = Tnew ℓ g X + Tinh ℓ g X)
    (hnew : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      Tnew ℓ g X = Tnew (can X) g X)
    (hinh : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖Tinh ℓ g X - Tinh (can X) g X‖ ≤
        a * Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ))) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (a + 2 * B) * Real.exp κ₂ + 2 * B * Real.exp (κ₂ * (t₀ : ℝ))) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  refine resum_gapScale_torus K hd hK P Q sz τ can D W R Ag T Wd hP hQ hsz hτ hR hAg hcanK hWd hB ha hκ
    hκ₂ hlam hκ' hsupp hloc han hbd ?_
  exact hFclose_of_split P Q sz τ can D T Tnew Tinh Wd hsplit hnew hinh

/-- **The torus clause at a gap scale for the step with no inherited terms** (item 24, part 2):
`resum_gapScale_torus` with `a = 0`, the closeness `hFclose` replaced by the equality of the terms on
`ℓ` and on `can X` for the compact supports `X` of the quarter box (`hexact`). -/
theorem resum_gapScale_torus_exact {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (Wd : ι → Finset (Fin d → ℤ) → Prop)
    {B κ κ₂ κ' lam : ℝ} {t₀ : ℕ}
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hWd : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Wd ℓ X → K ℓ ≤ 25 * X.card)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hκ₂ : κ + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hexact : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      T ℓ g X = T (can X) g X) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (2 * B) * Real.exp κ₂ + 2 * B * Real.exp (κ₂ * (t₀ : ℝ))) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  have h := resum_gapScale_torus K hd hK P Q sz τ can D W R Ag T Wd (a := 0) hP hQ hsz hτ hR hAg
    hcanK hWd hB le_rfl hκ hκ₂ hlam hκ' hsupp hloc han hbd
    (hFclose_of_exact P Q sz τ can D T Wd hexact)
  simpa only [zero_add] using h

end Close

end Balaban.Polymer
