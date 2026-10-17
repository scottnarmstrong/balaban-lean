/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsRecentreDet
public import Balaban.Polymer.TwoTorusGapCloseResum

/-!
# The gap-scale clause for the full step terms: composition (item 24, blocker 7)

The terms of the step at a gap scale are `T = Tnew + Tinh`, the new terms being the sum of the energy
terms `Te`, the determinant terms `Td` and the observable terms `To`.  If each of the three classes of
new terms is equal on `ℓ` and on `can X` for the compact supports of the quarter box, the clauses of
`resum_gapScale_torus` follow from the closeness `hinh` of the inherited terms alone
(`resum_gapScale_torus_threeTerms`).  The energy clause is `hnew_of_blockEnergy`; the determinant and
observable clauses are the recentred transports `sum_blockU_detActivityBg_recentred` and
`obsCoeffParam_recentred` once the terms are identified with their values at the cells of `X`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

section Full

variable {d : ℕ}

/-- **The torus clause at a gap scale for energy, determinant and observable terms.** -/
theorem resum_gapScale_torus_threeTerms {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
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
    (Te Td To Tinh : ι → G → Finset (Fin d → ℤ) → ℂ)
    (hsplit : ∀ ℓ g X, T ℓ g X = Te ℓ g X + Td ℓ g X + To ℓ g X + Tinh ℓ g X)
    (hen : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      Te ℓ g X = Te (can X) g X)
    (hdt : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      Td ℓ g X = Td (can X) g X)
    (hob : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      To ℓ g X = To (can X) g X)
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
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) :=
  resum_gapScale_torus_inherited K hd hK P Q sz τ can D W R Ag T Wd hP hQ hsz hτ hR hAg hcanK hWd
    hB ha hκ hκ₂ hlam hκ' hsupp hloc han hbd (fun ℓ g X => Te ℓ g X + Td ℓ g X + To ℓ g X) Tinh
    (fun ℓ g X => by rw [hsplit])
    (fun ℓ X hX hQX hW ht g hg => by
      simp only [hen ℓ X hX hQX hW ht g hg, hdt ℓ X hX hQX hW ht g hg, hob ℓ X hX hQX hW ht g hg])
    hinh

end Full

end Balaban.Polymer.TwoTorusStep
