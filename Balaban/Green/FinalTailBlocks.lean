/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailBound
import Mathlib.Tactic.Positivity

/-!
# The Gaussian weight of a set of large blocks (W889)

Leaf T-2 of `notes/phase1/FINALPHYS3.md` section 6.  For a family of pairwise disjoint blocks
`blk z ⊆ ι` (`z ∈ Z`), the event that every block `z ∈ Z` contains a site with `‖ψ x‖ > ρ` has
`pdGaussian` measure at most `∏_{z ∈ Z} (|blk z| · 2^{dim W/2} e^{-ρ²/4})`.  One site is selected
in each block, the selections are summed by the union bound, and the selected sites are distinct
because the blocks are disjoint, so `pdGaussian_tail_all_le` applies to each selection.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Green

variable {ι β W : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

/-- **Tail of a set of blocks** (leaf T-2).  If the blocks `blk z`, `z ∈ Z`, are pairwise disjoint,
`γ{ψ | ∀ z ∈ Z, ∃ x ∈ blk z, ‖ψ x‖ > ρ} ≤ ∏_{z ∈ Z} (|blk z| 2^{dim W/2} e^{-ρ²/4})`,
`γ = pdGaussian ι W`. -/
theorem pdGaussian_tail_blocks_le (blk : β → Finset ι) (Z : Finset β)
    (hdisj : (Z : Set β).PairwiseDisjoint blk) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    pdGaussian ι W {ψ | ∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖} ≤
      ENNReal.ofReal (∏ z ∈ Z, ((blk z).card *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)))) := by
  classical
  set t : ℝ := 2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4) with ht
  have ht0 : 0 ≤ t := by positivity
  have hset : {ψ : ι → W | ∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖} ⊆
      ⋃ s ∈ Fintype.piFinset (fun z : Z => blk z),
        {ψ : ι → W | ∀ x ∈ Finset.univ.image s, ρ < ‖ψ x‖} := by
    intro ψ hψ
    have hψ' : ∀ z : Z, ∃ x ∈ blk z, ρ < ‖ψ x‖ := fun z => hψ z z.2
    choose f hf using hψ'
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨f, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]; exact fun z => (hf z).1
    · intro x hx
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hx
      exact (hf z).2
  have hcard : ∀ s ∈ Fintype.piFinset (fun z : Z => blk z), (Finset.univ.image s).card = Z.card := by
    intro s hs
    rw [Fintype.mem_piFinset] at hs
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_coe]
    intro a b hab
    by_contra hne
    have hne' : (a : β) ≠ b := fun h => hne (Subtype.ext h)
    have hd := hdisj a.2 b.2 hne'
    exact Finset.disjoint_left.1 hd (hs a) (hab ▸ hs b)
  refine (measure_mono hset).trans ?_
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ s ∈ Fintype.piFinset (fun z : Z => blk z),
        pdGaussian ι W {ψ : ι → W | ∀ x ∈ Finset.univ.image s, ρ < ‖ψ x‖}
      ≤ ∑ s ∈ Fintype.piFinset (fun z : Z => blk z), ENNReal.ofReal (t ^ Z.card) :=
        Finset.sum_le_sum fun s hs => by
          have := pdGaussian_tail_all_le (ι := ι) (W := W) (Finset.univ.image s) hρ
          rwa [hcard s hs] at this
    _ = ENNReal.ofReal (((Fintype.piFinset (fun z : Z => blk z)).card : ℝ) * t ^ Z.card) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (∏ z ∈ Z, ((blk z).card * t)) := by
        congr 1
        rw [Fintype.card_piFinset, Finset.prod_mul_distrib, Finset.prod_const]
        push_cast
        rw [← Finset.prod_coe_sort Z (fun z => ((blk z).card : ℝ))]

end Balaban.Green
