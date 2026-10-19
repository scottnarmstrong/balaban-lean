/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusRoom
public import Balaban.LargeField.Background.StepGenSetsFlow

/-!
# The level torus and the history torus

The fine sets `fineK`, `fineK1` of the level-`(k+1)` torus `𝕋_{M₁ (c n_{k+1}) L^{k+1}}` are the
preimages, under the cast `torusCast` to the history torus `𝕋_{M n_K L^K}`, of the fine sets
`fineSet` of the history, and correspondences (`SetCorr`, `SetIff`) of sets of the history torus
give correspondences of their preimages.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField RegionHistory

section Preimage

variable {d : ℕ} {c : Fin d → ℤ}

theorem setCorr_preimage_cast {m₁ m₂ m₁' m₂' : ℕ} (e₁ : m₁' = m₁) (e₂ : m₂' = m₂)
    {A₁ : Set (Torus d m₁)} {A₂ : Set (Torus d m₂)} (h : SetCorr c A₁ A₂) :
    SetCorr c (torusCast e₁ ⁻¹' A₁) (torusCast e₂ ⁻¹' A₂) := by
  subst e₁ e₂; exact h

theorem setIff_preimage_cast {m₁ m₂ m₁' m₂' : ℕ} (e₁ : m₁' = m₁) (e₂ : m₂' = m₂)
    {A₁ : Set (Torus d m₁)} {A₂ : Set (Torus d m₂)} (h : SetIff c A₁ A₂) :
    SetIff c (torusCast e₁ ⁻¹' A₁) (torusCast e₂ ⁻¹' A₂) := by
  subst e₁ e₂; exact h

end Preimage

section Fine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M1 c K k : ℕ} [NeZero M1] [NeZero c]
  [NeZero S.L]

theorem coe_fineK1_eq_preimage (e : M1 * (c * n (k + 1)) * S.L ^ (k + 1) = c * M1 * n K * S.L ^ K)
    (A : Set (Torus S.d (n (k + 1)))) :
    ((fineK1 M1 c (n (k + 1)) S.L k A : Finset _) :
        Set (Torus S.d (M1 * (c * n (k + 1)) * S.L ^ (k + 1)))) =
      torusCast e ⁻¹' fineSet (S := S) (n := n) (c * M1) K (k + 1) A := by
  ext x
  simp only [Finset.mem_coe, mem_fineK1, Set.mem_preimage]
  show blockMap (S.L ^ (k + 1) * (c * M1)) (n (k + 1)) x ∈ A ↔
    blockMap (S.L ^ (k + 1) * (c * M1)) (n (k + 1)) (torusCast e x) ∈ A
  rw [blockMap_torusCast]

theorem coe_fineK_eq_preimage (e : M1 * (c * n (k + 1)) * S.L ^ (k + 1) = c * M1 * n K * S.L ^ K)
    (A : Set (Torus S.d (n k))) :
    ((fineK M1 c (n (k + 1)) S.L k (n k) A : Finset _) :
        Set (Torus S.d (M1 * (c * n (k + 1)) * S.L ^ (k + 1)))) =
      torusCast e ⁻¹' fineSet (S := S) (n := n) (c * M1) K k A := by
  ext x
  simp only [Finset.mem_coe, mem_fineK, Set.mem_preimage]
  show blockMap (S.L ^ k * (c * M1)) (n k) x ∈ A ↔
    blockMap (S.L ^ k * (c * M1)) (n k) (torusCast e x) ∈ A
  rw [blockMap_torusCast]

end Fine

end Balaban.RootFSpine
