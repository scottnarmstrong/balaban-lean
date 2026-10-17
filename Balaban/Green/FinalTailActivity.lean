/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailBlocks
public import Balaban.Green.FinalTailSplit
import Mathlib.Tactic.Positivity

/-!
# The absolute activity of a set of large blocks (W889)

Leaf T-4 of `notes/phase1/FINALPHYS3.md` section 6.  For pairwise disjoint blocks `blk z`
(`z ∈ Z`) and a function `F` bounded by `B` on the set
`{ψ | every block of Z is large, every other block is small}`, the integral of `F` over that set
against `pdGaussian ι W` has norm at most `B ∏_{z ∈ Z} (|blk z| 2^{dim W/2} e^{-ρ²/4})`.
No interpolation parameter acts on the large blocks: apply it to `F ψ = G (C ψ)` with the
covariance map evaluated at `s = 1`.  With `e^{-H_z} := |blk z| 2^{dim W/2} e^{-ρ²/4}` this is the
activity `B ∏_{z ∈ Z} e^{-H_z}` of P7 (4.12).
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Green

variable {ι β W E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Absolute activity of a large-block set** (leaf T-4).  If the blocks of `Z` are pairwise
disjoint and `‖F ψ‖ ≤ B` on `{ψ | every block of Z large, every other block small}`, then the
integral of `F` over that set against `pdGaussian ι W` has norm at most
`B ∏_{z ∈ Z} (|blk z| 2^{dim W/2} e^{-ρ²/4})`. -/
theorem norm_setIntegral_blocksSplit_le [Fintype β] (blk : β → Finset ι) (Z : Finset β)
    (hdisj : (Z : Set β).PairwiseDisjoint blk) {ρ : ℝ} (hρ : 0 ≤ ρ) {F : (ι → W) → E} {B : ℝ}
    (hB : 0 ≤ B)
    (hF : ∀ ψ ∈ {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ}, ‖F ψ‖ ≤ B) :
    ‖∫ ψ in {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
        ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ}, F ψ ∂(pdGaussian ι W)‖ ≤
      B * ∏ z ∈ Z, ((blk z).card *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := pdGaussian ι W)
    (s := {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ}) (C := B)
    ((measure_mono (Set.subset_univ _)).trans_lt
      (by rw [pdGaussian_univ]; exact ENNReal.one_lt_top)) hF
  refine h1.trans ?_
  rw [Measure.real]
  refine mul_le_mul_of_nonneg_left ?_ hB
  have hsub : {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ} ⊆ {ψ | ∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖} :=
    fun ψ h => h.1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((measure_mono hsub).trans (pdGaussian_tail_blocks_le (W := W) blk Z hdisj hρ))
  rwa [ENNReal.toReal_ofReal (Finset.prod_nonneg fun z _ => by positivity)] at this

end Balaban.Green
