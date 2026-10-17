/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapDataThr

/-!
# The gap scales with at most sixty cells per side (blocker 7)

At the top `⌈log_L 61⌉ - 1` gap scales of the smallest tori the side has `K ≤ 60` cells, and the
threshold of the wide supports of `resum_gapScale_torus_wide36` (`61 ≤ K`) is not available.  There
the closeness of the terms on two tori is not needed: for every support of the quarter box
`τ ≤ K / 4 ≤ 15`, so the bound `‖T‖ ≤ B e^{-κ'|X|}` alone gives
`‖T ℓ X - T (can X) X‖ ≤ 2 B e^{-κ'|X|} ≤ (2 B e^{15 lam}) e^{-lam τ} e^{-κ₂ |X|}`.

`resum_gapScale_torus_small`: `resum_gapScale_torus_of_wideMargin` with no wide supports and this
closeness, `a = 2 B e^{15 lam}`; no recentring and no comparison of the tori, a constant loss at
finitely many scales (uniform in the volume).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

section Small

variable {d : ℕ}

/-- **The resummation at a gap scale with at most sixty cells per side.**  The statement of
`resum_gapScale_torus_wide36` for `2 ≤ K ≤ 60`, with no wide supports and no closeness hypothesis:
the closeness follows from the bound `hbd` (`τ ≤ 15`), with the constant `a = 2 B e^{15 lam}`; the
supports of the quarter box of `ℓ` are supports of `can X` (`hcanP`). -/
theorem resum_gapScale_torus_small {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK2 : ∀ ℓ, 2 ≤ K ℓ) (hK60 : ∀ ℓ, K ℓ ≤ 60) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    {B κ κ₂ κ' lam : ℝ} {t₀ : ℕ}
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hcanP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ∈ P (can X))
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hκ₂ : κ + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ))) :
    ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
    ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
      (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
      (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then T (can X) g X else
        T ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
          (T ℓ g X₀ - T (can X₀) g X₀)) ∧
      (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, T ℓ g X) ∧
      (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖Tn ℓ g X‖ ≤
        (B + (2 * B * Real.exp (15 * lam) + 2 * B) * Real.exp κ₂ + 2 * B * Real.exp (κ₂ * (t₀ : ℝ))) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W)  := by
  have hκ₂0 : 0 ≤ κ₂ := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hlam0 : 0 ≤ lam := hκ₂0.trans hlam
  have hκ'κ₂ : κ₂ ≤ κ' := by linarith
  refine resum_gapScale_torus_of_wideMargin K hd hK2 P Q sz τ can D W R Ag T (fun _ _ => False)
    hP hQ hsz hτ hR hAg hcanK (fun _ _ _ _ h => h.elim) hB (by positivity) hκ hκ₂ hlam hκ' hsupp
    hloc han hbd (fun ℓ X hX hQX _ _ g hg => ?_)
  have hτ15 : (τ ℓ X : ℝ) ≤ 15 := by
    have : τ ℓ X ≤ 15 := by rw [hτ]; have := hK60 ℓ; omega
    exact_mod_cast this
  have h1 := hbd ℓ X hX g hg
  have h2 := hbd (can X) X (hcanP ℓ X hX hQX) g hg
  have hsz0 : (0 : ℝ) ≤ (sz X : ℝ) := Nat.cast_nonneg _
  have he : Real.exp (-κ' * (sz X : ℝ)) ≤ Real.exp (-κ₂ * (sz X : ℝ)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have he' : 1 ≤ Real.exp (15 * lam) * Real.exp (-lam * (τ ℓ X : ℝ)) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  calc ‖T ℓ g X - T (can X) g X‖ ≤ ‖T ℓ g X‖ + ‖T (can X) g X‖ := norm_sub_le _ _
    _ ≤ 2 * B * Real.exp (-κ₂ * (sz X : ℝ)) := by nlinarith [Real.exp_pos (-κ' * (sz X : ℝ))]
    _ = 2 * B * 1 * Real.exp (-κ₂ * (sz X : ℝ)) := by ring
    _ ≤ 2 * B * (Real.exp (15 * lam) * Real.exp (-lam * (τ ℓ X : ℝ))) *
        Real.exp (-κ₂ * (sz X : ℝ)) := by
      gcongr
    _ = 2 * B * Real.exp (15 * lam) * Real.exp (-lam * (τ ℓ X : ℝ)) *
        Real.exp (-κ₂ * (sz X : ℝ)) := by ring

end Small

end Balaban.Polymer.TwoTorusStep
