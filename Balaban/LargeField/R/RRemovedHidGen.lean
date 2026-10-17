/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupPi
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The integral over the node and the shell variables, in general (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  `lintegral_nodes_shells_le`: a function
bounded by `K · G(nodes; shells) · I_O(outputs) · I_S(shells)` on the product of the node variables
`(A, Nd, W)` and the shell variables `(RO, Sh)` integrates to at most `K · P` when the integral of `G` over
the nodes is at most `P` for every value of the shells and the shell indicators integrate to at most `1`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

section Gen

variable {A RO Nd Sh W : Type*} [MeasurableSpace A] [MeasurableSpace RO] [MeasurableSpace Nd]
  [MeasurableSpace Sh] [MeasurableSpace W] (μA : Measure A) (μRO : Measure RO) (μNd : Measure Nd)
  (μSh : Measure Sh) (μW : Measure W) [SFinite μA] [SFinite μRO] [SFinite μNd] [SFinite μSh]
  [SFinite μW]

/-- The regrouping `((a, ro), ((nd, sh), w)) ↦ ((ro, sh), (a, (nd, w)))` of the integration variables into
the shell variables and the node variables, measure preserving. -/
theorem exists_nodes_shells_equiv :
    ∃ e : (A × RO) × ((Nd × Sh) × W) ≃ᵐ (RO × Sh) × (A × (Nd × W)),
      MeasurePreserving e ((μA.prod μRO).prod ((μNd.prod μSh).prod μW))
        ((μRO.prod μSh).prod (μA.prod (μNd.prod μW))) ∧
      ∀ p, e p = ((p.1.2, p.2.1.2), (p.1.1, (p.2.1.1, p.2.2))) := by
  let e : (A × RO) × ((Nd × Sh) × W) ≃ᵐ (RO × Sh) × (A × (Nd × W)) :=
    { toFun := fun p => ((p.1.2, p.2.1.2), (p.1.1, (p.2.1.1, p.2.2)))
      invFun := fun q => ((q.2.1, q.1.1), ((q.2.2.1, q.1.2), q.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      measurable_toFun := by
        show Measurable fun p : (A × RO) × ((Nd × Sh) × W) =>
          ((p.1.2, p.2.1.2), (p.1.1, (p.2.1.1, p.2.2)))
        fun_prop
      measurable_invFun := by
        show Measurable fun q : (RO × Sh) × (A × (Nd × W)) =>
          ((q.2.1, q.1.1), ((q.2.2.1, q.1.2), q.2.2.2))
        fun_prop }
  refine ⟨e, ?_, fun _ => rfl⟩
  -- `(A × RO) × ((Nd × Sh) × W)`
  have h1 := (Measure.measurePreserving_swap (μ := μA) (ν := μRO)).prod (MeasurePreserving.id
    ((μNd.prod μSh).prod μW))
  have h2 := measurePreserving_prodAssoc μRO μA ((μNd.prod μSh).prod μW)
  have h3 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μNd μSh μW)
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_swap12 μNd μSh μW)
  have h5 := measurePreserving_swap12 μA μSh (μNd.prod μW)
  have h6 := (MeasurePreserving.id μRO).prod (h5.comp (h4.comp h3))
  have h7 := (measurePreserving_prodAssoc μRO μSh (μA.prod (μNd.prod μW))).symm
  exact h7.comp (h6.comp (h2.comp h1))

/-- **The integral over the node variables and the shell variables.**  If `φ ≤ K G I_O I_S` pointwise, the
integral of `G` over the nodes `(a, nd, w)` is at most `P` for every value `sh` of the shells, and the
shell indicators `I_O`, `I_S` integrate to at most `1`, then `∫ φ ≤ K P`. -/
theorem lintegral_nodes_shells_le (φ : (A × RO) × ((Nd × Sh) × W) → ℝ≥0∞) (K P : ℝ≥0∞) (hK : K ≠ ∞)
    (G : A → RO → Nd → W → Sh → ℝ≥0∞) (IO : RO → ℝ≥0∞) (IS : Sh → ℝ≥0∞)
    (hIOf : ∀ ro, IO ro ≠ ∞) (hISf : ∀ sh, IS sh ≠ ∞)
    (hφ : ∀ a ro nd sh w, φ ((a, ro), ((nd, sh), w)) ≤ K * G a ro nd w sh * IO ro * IS sh)
    (hG : ∀ ro sh, ∫⁻ x : A × (Nd × W), G x.1 ro x.2.1 x.2.2 sh ∂(μA.prod (μNd.prod μW)) ≤ P)
    (hIO : ∫⁻ ro, IO ro ∂μRO ≤ 1) (hIS : ∫⁻ sh, IS sh ∂μSh ≤ 1) :
    ∫⁻ j, φ j ∂((μA.prod μRO).prod ((μNd.prod μSh).prod μW)) ≤ K * P := by
  obtain ⟨e, he, hep⟩ := exists_nodes_shells_equiv μA μRO μNd μSh μW
  have h1 : ∫⁻ j, φ j ∂((μA.prod μRO).prod ((μNd.prod μSh).prod μW)) =
      ∫⁻ q, φ (e.symm q) ∂((μRO.prod μSh).prod (μA.prod (μNd.prod μW))) := by
    rw [← he.lintegral_comp_emb e.measurableEmbedding]
    simp
  rw [h1]
  refine (lintegral_prod_le _).trans ?_
  have h2 : ∀ q : RO × Sh, ∫⁻ x : A × (Nd × W), φ (e.symm (q, x))
      ∂(μA.prod (μNd.prod μW)) ≤ K * P * IO q.1 * IS q.2 := by
    intro q
    calc ∫⁻ x : A × (Nd × W), φ (e.symm (q, x)) ∂(μA.prod (μNd.prod μW))
        ≤ ∫⁻ x : A × (Nd × W), (K * IO q.1 * IS q.2) * G x.1 q.1 x.2.1 x.2.2 q.2
            ∂(μA.prod (μNd.prod μW)) := by
          refine lintegral_mono fun x => ?_
          have : e.symm (q, x) = ((x.1, q.1), ((x.2.1, q.2), x.2.2)) :=
            e.symm_apply_eq.2 (by rw [hep])
          rw [this]
          refine (hφ x.1 q.1 x.2.1 q.2 x.2.2).trans (le_of_eq ?_)
          ring
      _ = (K * IO q.1 * IS q.2) * ∫⁻ x : A × (Nd × W), G x.1 q.1 x.2.1 x.2.2 q.2
            ∂(μA.prod (μNd.prod μW)) := by
          exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top hK (hIOf _))
            (hISf _))
      _ ≤ (K * IO q.1 * IS q.2) * P := by gcongr; exact hG q.1 q.2
      _ = K * P * IO q.1 * IS q.2 := by ring
  refine (lintegral_mono h2).trans ?_
  by_cases hc : K * P = ∞
  · rw [hc]; exact le_top
  refine (lintegral_prod_le _).trans ?_
  have h3 : ∀ ro : RO, ∫⁻ sh, K * P * IO ro * IS sh ∂μSh ≤ K * P * IO ro := by
    intro ro
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hc (hIOf ro))]
    calc K * P * IO ro * ∫⁻ sh, IS sh ∂μSh ≤ K * P * IO ro * 1 := by gcongr
      _ = K * P * IO ro := mul_one _
  refine (lintegral_mono h3).trans ?_
  rw [show (fun ro => K * P * IO ro) = fun ro => (K * P) * IO ro from rfl,
    lintegral_const_mul' _ _ hc]
  calc K * P * ∫⁻ ro, IO ro ∂μRO ≤ K * P * 1 := by gcongr
    _ = K * P := mul_one _

end Gen

end Balaban.LargeField
