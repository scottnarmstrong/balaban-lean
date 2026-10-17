/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapAssembly
public import Balaban.Fluctuation.ParamActivityPhysical

/-!
# The gap-scale resummation on a family of tori of all sizes (blocker 7)

`resum_gapScale_torus_mixed`: the resummation `resum_gapScale_torus_of_wideMargin` on a family of
tori whose numbers of cells per side `K ℓ ≥ 2` are arbitrary.  Above a threshold `Kthr` the terms
of a support of the quarter box that is not wide are the same on `ℓ` and on `can X` (`hex`), and a
wide support pays the chain (`τ ≤ 7 |X|`, `hWm`); below `Kthr` no support is wide and the closeness
comes from the bound alone: `τ ≤ K / 4 ≤ Kthr / 4`, so
`‖T ℓ X - T (can X) X‖ ≤ 2 B e^{-κ'|X|} ≤ (2 B e^{(Kthr/4) lam}) e^{-lam τ} e^{-κ₂ |X|}`.
One family, one canonical torus map: the resummed terms agree on the common quarter boxes of all
tori, small and large.

`physRestrict_eq_of_subset`: equal restrictions to a set give equal restrictions to a subset.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

section Mixed

variable {d : ℕ}

/-- **The torus clause at a gap scale on a family of tori of all sizes.**  The conclusion of
`resum_gapScale_torus_of_wideMargin` with `a = 2 B e^{(Kthr/4) lam}` and `t₀ = 0`, for any family
with `2 ≤ K ℓ`: the wide supports `Wd` (with the chain margin `τ ≤ 7 |X|`) and the exact clause
`hex` are required only on the tori with `Kthr ≤ K ℓ`. -/
theorem resum_gapScale_torus_mixed {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (Kthr : ℕ) (hK2 : ∀ ℓ, 2 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
    (Q : ι → Finset (Fin d → ℤ) → Prop) (sz : Finset (Fin d → ℤ) → ℕ)
    (τ : ι → Finset (Fin d → ℤ) → ℕ) (can : Finset (Fin d → ℤ) → ι) (D : Set G)
    (W : Submodule ℂ (G → ℂ)) (R : Finset (Fin d → ℤ) → Prop)
    (Ag : Finset (Fin d → ℤ) → G → G → Prop) (T : ι → G → Finset (Fin d → ℤ) → ℂ)
    (Wd : ι → Finset (Fin d → ℤ) → Prop)
    {B κ κ₂ κ' lam : ℝ}
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hsz : ∀ X, sz X = X.card)
    (hτ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
    (hR : ∀ ℓ X, X ∈ P ℓ → R X)
    (hAg : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
    (hWm : ∀ ℓ X, Kthr ≤ K ℓ → X ∈ P ℓ → Q ℓ X → Wd ℓ X → τ ℓ X ≤ 7 * X.card)
    (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hκ₂ : κ + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hex : ∀ ℓ X, Kthr ≤ K ℓ → X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → ∀ g ∈ D,
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
        (B + (2 * B * Real.exp (((Kthr / 4 : ℕ) : ℝ) * lam) + 2 * B) * Real.exp κ₂ + 2 * B) *
          Real.exp (-κ * (sz X : ℝ))) ∧
      (∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, Tn ℓ g X = 0) ∧
      (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
      (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  have hκ₂0 : 0 ≤ κ₂ := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hlam0 : 0 ≤ lam := le_trans hκ₂0 hlam
  have hcanP : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ∈ P (can X) := by
    intro ℓ X hX hQX
    obtain ⟨Y, hY, rfl⟩ := (hP ℓ _).1 hX
    have hbox : ∀ b ∈ Y, ∀ μ, (b μ).valMinAbs.natAbs ≤ K ℓ / 4 := fun b hb μ =>
      (hQ ℓ _).1 hQX _ (Finset.mem_image_of_mem _ hb) μ
    obtain ⟨Y', hY', h⟩ := quarterBox_polymer_larger (hK2 ℓ) (hcanK ℓ _ hX hQX) hY hbox
    exact (hP _ _).2 ⟨Y', hY', h.symm⟩
  have hFclose : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ (Kthr ≤ K ℓ ∧ Wd ℓ X) → 0 ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤ 2 * B * Real.exp (((Kthr / 4 : ℕ) : ℝ) * lam) *
        Real.exp (-lam * (τ ℓ X : ℝ)) * Real.exp (-κ₂ * (sz X : ℝ)) := by
    intro ℓ X hX hQX hw _ g hg
    by_cases hK : Kthr ≤ K ℓ
    · rw [hex ℓ X hK hX hQX (fun h => hw ⟨hK, h⟩) g hg, sub_self, norm_zero]
      positivity
    · have hτK : τ ℓ X ≤ Kthr / 4 := by
        rw [hτ]
        have : K ℓ / 4 ≤ Kthr / 4 := Nat.div_le_div_right (by omega)
        omega
      have hτK' : (τ ℓ X : ℝ) ≤ ((Kthr / 4 : ℕ) : ℝ) := by exact_mod_cast hτK
      have h1 := hbd ℓ X hX g hg
      have h2 := hbd (can X) X (hcanP ℓ X hX hQX) g hg
      have hsz0 : (0 : ℝ) ≤ (sz X : ℝ) := Nat.cast_nonneg _
      have he : Real.exp (-κ' * (sz X : ℝ)) ≤ Real.exp (-κ₂ * (sz X : ℝ)) :=
        Real.exp_le_exp.2 (by nlinarith)
      have he' : 1 ≤ Real.exp (((Kthr / 4 : ℕ) : ℝ) * lam) * Real.exp (-lam * (τ ℓ X : ℝ)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      calc ‖T ℓ g X - T (can X) g X‖ ≤ ‖T ℓ g X‖ + ‖T (can X) g X‖ := norm_sub_le _ _
        _ ≤ 2 * B * Real.exp (-κ₂ * (sz X : ℝ)) := by
          nlinarith [Real.exp_pos (-κ' * (sz X : ℝ))]
        _ = 2 * B * 1 * Real.exp (-κ₂ * (sz X : ℝ)) := by ring
        _ ≤ 2 * B * (Real.exp (((Kthr / 4 : ℕ) : ℝ) * lam) * Real.exp (-lam * (τ ℓ X : ℝ))) *
            Real.exp (-κ₂ * (sz X : ℝ)) := by
          gcongr
        _ = 2 * B * Real.exp (((Kthr / 4 : ℕ) : ℝ) * lam) * Real.exp (-lam * (τ ℓ X : ℝ)) *
            Real.exp (-κ₂ * (sz X : ℝ)) := by ring
  obtain ⟨Φ, Tn, h1, h2, h3, h4, h5, h6, h7, h8⟩ := resum_gapScale_torus_of_wideMargin K hd hK2 P Q
    sz τ can D W R Ag T (fun ℓ X => Kthr ≤ K ℓ ∧ Wd ℓ X) (t₀ := 0) hP hQ hsz hτ hR hAg hcanK
    (fun ℓ X hX hQX hw => hWm ℓ X hw.1 hX hQX hw.2) hB (by positivity) hκ hκ₂ hlam hκ' hsupp hloc
    han hbd (fun ℓ X hX hQX hw ht g hg => hFclose ℓ X hX hQX hw (Nat.zero_le _) g hg)
  refine ⟨Φ, Tn, h1, h2, h3, h4, fun ℓ X hX g hg => ?_, h6, h7, h8⟩
  have := h5 ℓ X hX g hg
  simpa using this

end Mixed

section Restrict

open Balaban.Localization Balaban.Fluctuation Balaban.Background

variable {d L N₁ m₁ k N : ℕ}

/-- **Restriction to a subset.**  Data with equal restrictions to `R` have equal restrictions to every
`R' ⊆ R`. -/
theorem physRestrict_eq_of_subset {R R' : Set (CTorus d L N₁ m₁ (k + 1))} (h : R' ⊆ R)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hR : physRestrict (N := N) R Θ = physRestrict R Θ') :
    physRestrict (N := N) R' Θ = physRestrict R' Θ' := by
  funext x
  have := congrFun hR ⟨x.1, h x.2⟩
  simpa [physRestrict] using this

end Restrict

end Balaban.Polymer.TwoTorusStep
