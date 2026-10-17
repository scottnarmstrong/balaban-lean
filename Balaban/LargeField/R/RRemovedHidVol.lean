/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedShell

/-!
# The volume of the shells of a family of variables (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  `pi_shell_le_one`: for any finite family
of non-spin variables, the product measure of the set of configurations with every variable in its shell
`{|u·u - 1| < t_i}` is at most `1` when the radii satisfy `0 < t_i ≤ 1/2`, `c_N t_i ≤ 1`.  The shell
indicators of the new′ variables of the Jv-coordinates and of the window coordinates in `T` are integrated
with it.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

section Vol

variable {N : ℕ}

/-- **The shells of a finite family of non-spin variables have measure at most `1`.** -/
theorem pi_shell_le_one (hN : 2 ≤ N) {ι : Type} [Fintype ι] (b : ι → Bool) (hb : ∀ i, b i = false)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1 / 2) (hct : ∀ i, cShell N * t i ≤ 1) :
    (Measure.pi fun i => varMeasure N (b i))
      {x | ∀ i, |‖VarVal.toEuc (x i)‖ ^ 2 - 1| < t i} ≤ 1 := by
  have hset : {x : ∀ i, VarVal N (b i) | ∀ i, |‖VarVal.toEuc (x i)‖ ^ 2 - 1| < t i} =
      Set.pi Set.univ (fun i => (VarVal.toEuc : VarVal N (b i) → EuclideanSpace ℝ (Fin N)) ⁻¹'
        shellSet N (t i)) := by
    ext x; simp [shellSet]
  rw [hset]
  refine pi_pi_le_one (fun i => varMeasure N (b i)) _ fun i => ?_
  rw [(measurePreserving_toEuc_false (N := N) _ (hb i)).measure_preimage
    (measurableSet_shellSet N (t i)).nullMeasurableSet]
  exact (volume_shellSet_le N hN (ht i) (ht1 i)).trans (ENNReal.ofReal_le_one.mpr (hct i))

/-- The integral of the indicator of a set of measure at most `1` is at most `1`. -/
theorem lintegral_ite_le_one {α : Type*} [MeasurableSpace α] (μ : Measure α) (P : α → Prop)
    [DecidablePred P] (h : μ {a | P a} ≤ 1) : ∫⁻ a, (if P a then (1 : ℝ≥0∞) else 0) ∂μ ≤ 1 := by
  have : (fun a => if P a then (1 : ℝ≥0∞) else 0) = Set.indicator {a | P a} 1 := by
    funext a; simp [Set.indicator]
  rw [this]
  exact (lintegral_indicator_one_le _).trans h

/-- **The product of the root densities is at most `e^{L_c}`**: each factor of the product over the
elements of `{a // V a}` is at least `1`, and at least `ρ₀` on those elements satisfying `g`. -/
theorem root_prod_le {α : Type} [Fintype α] (V g : α → Prop) [DecidablePred V] [DecidablePred g]
    [Fintype {a // V a}] (f : {a // V a} → ℝ) (ρ0 : ℝ) (hf1 : ∀ i, 1 ≤ f i)
    (hfg : ∀ i, g i.1 → ρ0 ≤ f i) :
    ENNReal.ofReal ρ0 ^ (Finset.univ.filter fun a => V a ∧ g a).card ≤
      ENNReal.ofReal (∏ i, f i) := by
  have hcard : (Finset.univ.filter fun a => V a ∧ g a).card =
      (Finset.univ.filter fun i : {a // V a} => g i.1).card := by
    rw [← Finset.card_map (Function.Embedding.subtype V)]
    congr 1
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨hV, hg'⟩
      exact ⟨⟨a, hV⟩, hg', rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.2, hi⟩
  rw [hcard, ← Finset.prod_const, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => (zero_le_one.trans (hf1 i)))]
  refine (Finset.prod_le_prod fun i hi => ENNReal.ofReal_le_ofReal
    (hfg i (Finset.mem_filter.mp hi).2)).trans ?_
  refine Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) fun i _ _ => ?_
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (hf1 i)

end Vol

end Balaban.LargeField
