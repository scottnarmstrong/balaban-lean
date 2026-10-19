/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRRep
public import Balaban.LargeField.Operators.PiTools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRJac`: the chart Jacobians after a linear change of the site index (route FR, (E2))

`notes/phase1/KF0-FR.md` (E2); LF-BASE-KF0 Theorem G.1. The chart weight
`w(ξ) = (1-|ξ|²)^{-1/2} 1[|ξ|<1]` is unbounded but integrable on `h^⊥`: its integral is the area of
the open upper hemisphere (`lintegral_chartWeight_eq`). After the linear change `ξ = S ψ + b` of the
site index the product of the weights has the exact integral

`∫ ∏_x q((Sψ)_x + b_x) dψ = |det S|^{-(N-1)} (∫ q)^{|ι|}` (`lintegral_prod_matAct_add`),

for every measurable `q ≥ 0` and every shift `b`. This is the only control of the Jacobians used by
the route: it is uniform in the shift, so it applies with the exterior variables fixed.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)

/-- **The integral of the chart weight is the area of the open hemisphere.** -/
theorem lintegral_chartWeight_eq (hh : ‖h‖ = 1) :
    ∫⁻ ξ : perp h, ENNReal.ofReal (chartWeight h ξ) =
      (volume : Measure E).toSphere
        {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ h (φ : E)} := by
  have hm : MeasurableSet {φ : Metric.sphere (0 : E) 1 | 0 < inner ℝ h (φ : E)} :=
    measurableSet_lt measurable_const (measurable_const.inner measurable_subtype_coe)
  have h1 := congrArg (fun μ : Measure (Metric.sphere (0 : E) 1) => μ Set.univ)
    (toSphere_restrict_hemisphere_site h hh)
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h1
  rw [h1, Measure.map_apply (continuous_hemiPt h hh).measurable MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem lintegral_chartWeight_lt_top (hh : ‖h‖ = 1) :
    ∫⁻ ξ : perp h, ENNReal.ofReal (chartWeight h ξ) < ⊤ := by
  rw [lintegral_chartWeight_eq h hh]
  exact measure_lt_top _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The product of one-site functions after a linear change of the index and a shift**:
`∫ ∏_x q((Sψ)_x + b_x) dψ = |det S|^{-(N-1)} (∫ q)^{|ι|}`. -/
theorem lintegral_prod_matAct_add (hh : ‖h‖ = 1) (S : Matrix ι ι ℝ) (hS : IsUnit S.det)
    (b : ι → perp h) (q : perp h → ℝ≥0∞) (hq : Measurable q) :
    ∫⁻ ψ, ∏ x, q (matAct S ψ x + b x) ∂(Measure.pi fun _ : ι => (volume : Measure (perp h))) =
      (ENNReal.ofReal |S.det ^ (N - 1)|)⁻¹ * (∫⁻ v, q v) ^ Fintype.card ι := by
  set μ := Measure.pi fun _ : ι => (volume : Measure (perp h))
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  have hchange := lintegral_eq_ofReal_abs_det_mul μ (matActEquiv (W := perp h) S hS)
    (fun v => ∏ x, q (v x + b x))
  rw [det_matActEquiv, hr] at hchange
  have hprod : ∫⁻ v, ∏ x, q (v x + b x) ∂μ = (∫⁻ v, q v) ^ Fintype.card ι := by
    rw [PiTools.lintegral_fintype_prod_eq_prod ι (fun x v => q (v + b x))
      (fun x => hq.comp (measurable_add_const (b x)))]
    simp_rw [lintegral_add_right_eq_self (μ := (volume : Measure (perp h))) q]
    rw [Finset.prod_const, Finset.card_univ]
  rw [hprod] at hchange
  have hdet : S.det ^ (N - 1) ≠ 0 := pow_ne_zero _ hS.ne_zero
  have hpos : (ENNReal.ofReal |S.det ^ (N - 1)|) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.2 hdet
  rw [hchange, ← mul_assoc, ENNReal.inv_mul_cancel hpos ENNReal.ofReal_ne_top, one_mul]
  rfl

end

end Balaban.LargeField.KF0FR
