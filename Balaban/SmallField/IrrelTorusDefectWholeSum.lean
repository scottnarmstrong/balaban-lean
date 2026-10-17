/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectMatrix

/-!
# Quantitative comparison after a common small-shape sum

This numerical lemma assembles exact agreement on common small shapes and two unmatched tails.
The anisotropic Cauchy and polymer-count estimates remain explicit premises for each tail.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

/-- The finite and infinite whole sums differ only by their unmatched tails. Each tail is
estimated by `norm_sum_winding_le`; the constants `24 e`, the decay threshold, and the
counting constants remain visible. -/
theorem norm_whole_sum_of_common_and_winding {ι : Type*} [DecidableEq ι]
    (C F I : Finset ι) (fFin fInf : ι → ℂ) (tFin tInf : ι → ℝ)
    (RFin RInf : ℂ) {E₀ κ κ₀ τFin τInf MFin MInf KFin KInf : ℝ}
    (hE₀ : 0 ≤ E₀) (hκ : κ₀ + 2 ≤ κ)
    (hMFin : 0 ≤ MFin) (hMInf : 0 ≤ MInf)
    (hFin0 : ∀ X ∈ F, 0 ≤ tFin X) (hInf0 : ∀ X ∈ I, 0 ≤ tInf X)
    (hFinτ : ∀ X ∈ F, τFin ≤ tFin X) (hInfτ : ∀ X ∈ I, τInf ≤ tInf X)
    (hFinCauchy : ∀ X ∈ F,
      ‖fFin X‖ ≤ MFin * E₀ * (1 + tFin X) ^ 4 * Real.exp (-κ * tFin X))
    (hInfCauchy : ∀ X ∈ I,
      ‖fInf X‖ ≤ MInf * E₀ * (1 + tInf X) ^ 4 * Real.exp (-κ * tInf X))
    (hFinCount : ∑ X ∈ F, Real.exp (-κ₀ * tFin X) ≤ KFin)
    (hInfCount : ∑ X ∈ I, Real.exp (-κ₀ * tInf X) ≤ KInf)
    (hCommon : ∀ X ∈ C, fFin X = fInf X)
    (hFinDecomp : RFin = ∑ X ∈ C, fFin X + ∑ X ∈ F, fFin X)
    (hInfDecomp : RInf = ∑ X ∈ C, fInf X + ∑ X ∈ I, fInf X) :
    ‖RFin - RInf‖ ≤
      24 * Real.exp 1 * MFin * E₀ * Real.exp (-τFin) * KFin +
      24 * Real.exp 1 * MInf * E₀ * Real.exp (-τInf) * KInf := by
  have hC : (∑ X ∈ C, fFin X) = ∑ X ∈ C, fInf X :=
    Finset.sum_congr rfl hCommon
  have hEq : RFin - RInf = (∑ X ∈ F, fFin X) - ∑ X ∈ I, fInf X := by
    rw [hFinDecomp, hInfDecomp, hC]
    abel
  rw [hEq]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_sum_winding_le F tFin fFin hMFin hE₀ hκ hFin0 hFinτ hFinCauchy hFinCount)
    (norm_sum_winding_le I tInf fInf hMInf hE₀ hκ hInf0 hInfτ hInfCauchy hInfCount))

end Balaban.SmallField.Def6
