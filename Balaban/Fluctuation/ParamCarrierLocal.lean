/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffAnalytic
public import Balaban.Fluctuation.HatLabelsTerms
public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Fluctuation.MeasureProduct
import Mathlib.Tactic.Linarith

/-!
# A compact carrier for the block measures of a step, and locality of `gsumCoeff` in a parameter

The single-site fluctuation measure `ν₁` has the sharp cutoff `‖ψ̂(u)‖ < p₁`, so the block measure
`ν_b = ⨂_{u ∈ b} ν₁` of `StepSetting.blockSplit` is carried by the product of closed balls
`{‖ψ̂(u)‖ ≤ p₁}`, which is compact.  Hence the compact carrier `Q` asked for by
`ParamMarkFamily` exists for the actual step measure.

* `physCarrier`: the set of block configurations all of whose site components have norm `≤ p₁`;
  it is compact, measurable and carries `Measure.pi BS.μ` almost everywhere
  (`isCompact_physCarrier`, `measurableSet_physCarrier`, `ae_mem_physCarrier`).  The block spaces
  `{u // cellOf u = b} → ℝ^N` carry the product topology, are second countable and have the Borel
  structure (instances below).
* `gsumCoeff_param_congr_of_local`: two parameters whose activities and marks agree on every label
  inside the enlarged region `Ŷ(sitesOf T)` give the same `gsumCoeff` at `T`.
* `paramMarked_analytic_local_bound`: for a `ParamMarkFamily` whose activities and marks on the
  enlarged region depend on `θ` only through `π θ`, the coefficient is analytic, factors through
  `π` and is bounded by the uniform bound of `norm_gsumCoeff_le`.

No physical family of marks is constructed here (that is `ParamMarksPhysical`), the determinant
term is not treated, and nothing depends on a choice of generating set for the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale

section Carrier

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)

instance instTopBlock (b) : TopologicalSpace ((S.blockSplit m₀ hp).Ωb b) :=
  inferInstanceAs (TopologicalSpace ({u : S.U // S.cellOf m₀ u = b} → Rn N))

instance instSecondCountableBlock (b) :
    SecondCountableTopology ((S.blockSplit m₀ hp).Ωb b) :=
  inferInstanceAs (SecondCountableTopology ({u : S.U // S.cellOf m₀ u = b} → Rn N))

instance instOpensMeasBlock (b) : OpensMeasurableSpace ((S.blockSplit m₀ hp).Ωb b) :=
  inferInstanceAs (OpensMeasurableSpace ({u : S.U // S.cellOf m₀ u = b} → Rn N))

/-- **The carrier of the step measure**: the block configurations all of whose site components
have norm at most `p₁`. -/
def physCarrier : Set (∀ b, (S.blockSplit m₀ hp).Ωb b) :=
  {Φ | ∀ b u, ‖Φ b u‖ ≤ S.p₁}

theorem physCarrier_eq_pi : physCarrier S m₀ hp =
    Set.pi Set.univ (fun b => Set.pi Set.univ
      (fun _ : {u : S.U // S.cellOf m₀ u = b} => Metric.closedBall (0 : Rn N) S.p₁)) := by
  ext Φ
  constructor
  · intro h b _ u _
    exact mem_closedBall_zero_iff.2 (h b u)
  · intro h b u
    exact mem_closedBall_zero_iff.1 (h b (Set.mem_univ _) u (Set.mem_univ _))

theorem isCompact_physCarrier : IsCompact (physCarrier S m₀ hp) := by
  rw [physCarrier_eq_pi]
  exact isCompact_univ_pi fun b => isCompact_univ_pi fun _ => isCompact_closedBall _ _

theorem measurableSet_physCarrier : MeasurableSet (physCarrier S m₀ hp) := by
  rw [physCarrier_eq_pi]
  exact MeasurableSet.univ_pi fun b => MeasurableSet.univ_pi fun _ => measurableSet_closedBall

theorem ae_mem_physCarrier :
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), Φ ∈ physCarrier S m₀ hp := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  have hb : ∀ b, ∀ᵐ Φ ∂((S.blockSplit m₀ hp).μ b), ∀ u, ‖Φ u‖ ≤ S.p₁ := fun b => by
    show ∀ᵐ Φ ∂(Measure.pi fun _ : {u : S.U // S.cellOf m₀ u = b} => fluctMeasure1 N S.p₁),
      ∀ u, ‖Φ u‖ ≤ S.p₁
    rw [ae_all_iff]
    intro u
    filter_upwards [(measurePreserving_eval
      (fun _ : {u : S.U // S.cellOf m₀ u = b} => fluctMeasure1 N S.p₁) u).quasiMeasurePreserving.ae
      (ae_norm_lt_fluctMeasure1 N S.p₁)] with x hx using hx.le
  rw [show (∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), Φ ∈ physCarrier S m₀ hp) ↔
    ∀ᵐ Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ), ∀ b, ∀ u, ‖Φ b u‖ ≤ S.p₁ from Iff.rfl,
    ae_all_iff]
  intro b
  exact (measurePreserving_eval (S.blockSplit m₀ hp).μ b).quasiMeasurePreserving.ae (hb b)

end Carrier

end Balaban.Fluctuation
