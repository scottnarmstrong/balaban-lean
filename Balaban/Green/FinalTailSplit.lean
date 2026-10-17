/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Positivity

/-!
# Decomposition of an integral over the sets of large blocks (W889)

Leaf T-3 of `notes/phase1/FINALPHYS3.md` section 6.  For a family of blocks `blk z ⊆ ι`
(`z` in a finite index type `β`) and a radius `ρ`, call `z` large at `ψ` if some site of `blk z`
has `ρ < ‖ψ x‖`, and small otherwise.  The identity `1 = ∏_z (χ_z + (1 - χ_z))` is the exact
set-integral decomposition
`∫ F dμ = ∑_{Z ⊆ blocks} ∫_{blocks of Z large, the others small} F dμ`
for every measure `μ` and integrable `F`.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Green

variable {ι β W E : Type*} [Fintype β] [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype β] in
private theorem measurableSet_block_large (blk : β → Finset ι) (ρ : ℝ) (z : β) :
    MeasurableSet {ψ : ι → W | ∃ x ∈ blk z, ρ < ‖ψ x‖} := by
  have : {ψ : ι → W | ∃ x ∈ blk z, ρ < ‖ψ x‖} = ⋃ x ∈ blk z, {ψ : ι → W | ρ < ‖ψ x‖} := by
    ext ψ; simp
  rw [this]
  exact Finset.measurableSet_biUnion _ fun x _ =>
    measurableSet_lt measurable_const (measurable_norm.comp (measurable_pi_apply x))

/-- The set `{ψ | every block of Z is large, every other block is small}` is measurable. -/
theorem measurableSet_blocksSplit (blk : β → Finset ι) (ρ : ℝ) (Z : Finset β) :
    MeasurableSet {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ} := by
  classical
  have h1 : {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ} =
      (⋂ z ∈ Z, {ψ : ι → W | ∃ x ∈ blk z, ρ < ‖ψ x‖}) ∩
        ⋂ z ∈ (Finset.univ.filter (· ∉ Z) : Finset β), {ψ : ι → W | ∃ x ∈ blk z, ρ < ‖ψ x‖}ᶜ := by
    ext ψ; simp
  rw [h1]
  exact (Finset.measurableSet_biInter _ fun z _ => measurableSet_block_large blk ρ z).inter
    (Finset.measurableSet_biInter _ fun z _ => (measurableSet_block_large blk ρ z).compl)

/-- **Exact decomposition of the last integral** (leaf T-3).  For every measure `μ` and
integrable `F`,
`∫ F dμ = ∑_{Z ⊆ blocks} ∫_{blocks of Z large, the others small} F dμ`. -/
theorem integral_eq_sum_blocksSplit (blk : β → Finset ι) (ρ : ℝ) (μ : Measure (ι → W))
    {F : (ι → W) → E} (hF : Integrable F μ) :
    ∫ ψ, F ψ ∂μ = ∑ Z : Finset β, ∫ ψ in {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ}, F ψ ∂μ := by
  classical
  have hpt : ∀ ψ : ι → W, ∑ Z : Finset β, Set.indicator {ψ : ι → W |
      (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧ ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ} F ψ = F ψ := by
    intro ψ
    have key : ∀ Z : Finset β, ((∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
        ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ) ↔
        Z = Finset.univ.filter fun z => ∃ x ∈ blk z, ρ < ‖ψ x‖ := by
      intro Z
      constructor
      · rintro ⟨h1, h2⟩
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun hz => h1 z hz, fun hz => ?_⟩
        by_contra hn
        obtain ⟨x, hx, hlt⟩ := hz
        exact absurd (h2 z hn x hx) (not_le.2 hlt)
      · rintro rfl
        refine ⟨fun z hz => (Finset.mem_filter.1 hz).2, fun z hz x hx => ?_⟩
        by_contra hlt
        exact hz (Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, not_le.1 hlt⟩)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, key]
    simp
  have hfun : (fun ψ => F ψ) = fun ψ => ∑ Z : Finset β, Set.indicator {ψ : ι → W |
      (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧ ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ} F ψ :=
    funext fun ψ => (hpt ψ).symm
  conv_lhs => rw [hfun]
  rw [integral_finsetSum _ fun Z _ => hF.indicator (measurableSet_blocksSplit blk ρ Z)]
  exact Finset.sum_congr rfl fun Z _ => integral_indicator (measurableSet_blocksSplit blk ρ Z)

end Balaban.Green
