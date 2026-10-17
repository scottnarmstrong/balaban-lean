/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapAssembly

/-!
# The wide/compact threshold `(K - 36) / 25` at the gap scale (item 24, blocker 7)

With the compact supports of cell spread at most `(K - 26) / 25` the determinant slack
`20 (Ds + (Ds + 1) / 4 + 2 L^(k+1)) + 20 < n` is not implied.  With the threshold `(K - 36) / 25`
(and `L^(k+1)` at most a quarter of the cell side) it is: `compact36_slack`.  A wide support
(spread above `(K - 36) / 25`) has `K ≤ 25 |X| + 10` cells (`wide_card36`), which pays the margin
for `61 ≤ K` (`margin_le_of_wide36`); the resummation core `resum_gapScale_torus_of_wideMargin` is
generic in the threshold, and the rate condition `7 lam + κ₂ ≤ κ'` is unchanged
(`resum_gapScale_torus_wide36`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

section Thr

/-- **The slack for the compact supports of threshold `(K - 36) / 25`.** -/
theorem compact36_slack {K K' aK Lk Dc Ds : ℕ} (hKK' : K ≤ K') (h4 : 4 * Lk ≤ aK) (hLk : 0 < Lk)
    (hK : 36 ≤ K) (hD : Dc ≤ (K - 36) / 25) (hDs : Ds + 1 ≤ aK * (Dc + 1)) :
    20 * (Ds + (Ds + 1) / 4 + 2 * Lk) + 20 < aK * K ∧
      20 * (Ds + (Ds + 1) / 4 + 2 * Lk) + 20 < aK * K' := by
  have h1 : 25 * Dc + 36 ≤ K := by omega
  have h2 : aK * (25 * Dc + 36) ≤ aK * K := Nat.mul_le_mul_left aK h1
  have h3 : aK * K ≤ aK * K' := Nat.mul_le_mul_left aK hKK'
  have h5 : aK * (25 * Dc + 36) = 25 * (aK * (Dc + 1)) + 11 * aK := by ring
  rw [h5] at h2
  constructor <;> omega

/-- **A wide support has many cells.**  A polymer with two cells at cyclic distance above
`(K - 36) / 25` in a coordinate has at least `(K - 10) / 25` cells. -/
theorem wide_card36 {d K : ℕ} [NeZero K] {Y : Finset (Balaban.Torus d K)}
    (hA : IsAnimal (blockGraph d K) Y)
    (hw : ∃ b0 ∈ Y, ∃ y ∈ Y, ∃ μ, (K - 36) / 25 < ((y μ - b0 μ).valMinAbs).natAbs) :
    K ≤ 25 * Y.card + 10 := by
  obtain ⟨b0, hb, y, hy, μ, hD⟩ := hw
  have := card_ge_of_spread Y hA hb hy μ
  omega

/-- **The chain is paid by a wide support** (`K ≤ 25 c + 10`, `61 ≤ K`). -/
theorem margin_le_of_wide36 {K c τ : ℕ} (hK : 61 ≤ K) (h : K ≤ 25 * c + 10) (hτ : τ ≤ K / 4) :
    τ ≤ 7 * c := by
  omega

variable {d : ℕ}

/-- **The torus clause at a gap scale with the wide supports of threshold `(K - 36) / 25`.**  As
`resum_gapScale_torus`, with the wide supports having `K ℓ ≤ 25 |X| + 10` cells (`hWd`,
`wide_card36`) and `61 ≤ K ℓ`; the rates are those of `resum_gapScale_torus`. -/
theorem resum_gapScale_torus_wide36 {ι G : Type*} (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (hd : 0 < d)
    (hK : ∀ ℓ, 61 ≤ K ℓ) (P : ι → Finset (Finset (Fin d → ℤ)))
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
    (hWd : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → Wd ℓ X → K ℓ ≤ 25 * X.card + 10)
    (hB : 0 ≤ B) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hκ₂ : κ + Real.log 2 ≤ κ₂) (hlam : κ₂ ≤ lam) (hκ' : 7 * lam + κ₂ ≤ κ')
    (hsupp : ∀ ℓ X, X ∈ P ℓ → ¬ R X → ∀ g, T ℓ g X = 0)
    (hloc : ∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → T ℓ g X = T ℓ g' X)
    (han : ∀ ℓ X, X ∈ P ℓ → (fun g => T ℓ g X) ∈ W)
    (hbd : ∀ ℓ X, X ∈ P ℓ → ∀ g ∈ D, ‖T ℓ g X‖ ≤ B * Real.exp (-κ' * (sz X : ℝ)))
    (hFclose : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → ¬ Wd ℓ X → t₀ ≤ τ ℓ X → ∀ g ∈ D,
      ‖T ℓ g X - T (can X) g X‖ ≤
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
  refine resum_gapScale_torus_of_wideMargin K hd (fun ℓ => by have := hK ℓ; omega) P Q sz τ can D W
    R Ag T Wd hP hQ hsz hτ hR hAg hcanK (fun ℓ X hX hQX hw => ?_) hB ha hκ hκ₂ hlam hκ' hsupp hloc
    han hbd hFclose
  have h2 := hWd ℓ X hX hQX hw
  rw [← hsz X]
  refine margin_le_of_wide36 (hK ℓ) (hsz X ▸ h2) ?_
  rw [hτ]; omega

end Thr

end Balaban.Polymer.TwoTorusStep
