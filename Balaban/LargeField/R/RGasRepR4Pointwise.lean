/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RGasRepR4Operator
public import Balaban.LargeField.Operators.Kernel

/-!
# The front-free, output-pointwise heavy operator activity

P7 (3.10), printed p. 520, and the strengthened front-free bound (3.10″)
in `notes/phase1/LF-RECONSTRUCTION.md` §III.9 concern the internal integral
at a **fixed** output field.  The theorem below bounds the operator weight
at that same output.  It does not integrate the output and therefore needs
no output-volume factor.  It is the single-heavy input for the operator gas;
it is not the scalar `hτ` of `RRemovedFinal.lf4R_removed`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

variable {O X H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [Fintype ι]

/-- **Pointwise heavy activity from (3.10″).**  The output `o` is a parameter,
and only the internal variable `x` is integrated. -/
theorem r4HeavyActivity_bound (T : LFKernel O X H ι) (μ : Measure X)
    (h : H) (g : ι → ℂ) (F : O → X → ℂ) (hF : ∀ o x, ‖F o x‖ ≤ 1)
    (κ : ℝ) (hpoint : ∀ o, ∫⁻ x, T.absW o x h g ∂μ ≤ ENNReal.ofReal (Real.exp (-κ)))
    (o : O) : ‖T.op μ h g F o‖ ≤ Real.exp (-κ) := by
  have hnorm : ∀ x, ‖T.w o x h g * F o x‖ₑ ≤ T.absW o x h g := by
    intro x
    rw [enorm_mul]
    have hw : ‖T.w o x h g‖ₑ = T.absW o x h g := by
      unfold LFKernel.w LFKernel.absW
      rw [← ofReal_norm, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_of_nonneg (T.K_nonneg _ _ _)]
    rw [hw]
    calc T.absW o x h g * ‖F o x‖ₑ
        ≤ T.absW o x h g * 1 := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.2 (hF o x)
      _ = _ := mul_one _
  have h := (enorm_integral_le_lintegral_enorm (fun x => T.w o x h g * F o x)).trans
    ((lintegral_mono hnorm).trans (hpoint o))
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 h

section Family

variable {J : Type*} [DecidableEq J] {Xj : J → Type*}
  [∀ j, MeasurableSpace (Xj j)]

/-- The heavy operator activity at a fixed output: the finite sum over the
localized histories of one removed cluster, with their common output field
still free.  The internal carrier may depend on the history. -/
noncomputable def r4HeavyFamily (Hs : Finset J)
    (T : ∀ j, LFKernel O (Xj j) H ι)
    (μ : ∀ j, Measure (Xj j)) (h : H) (g : ι → ℂ)
    (F : ∀ j, O → Xj j → ℂ) (o : O) : ℂ :=
  ∑ j ∈ Hs, (T j).op (μ j) h g (F j) o

omit [DecidableEq J] in
/-- The family form of (3.10″): each history is bounded at the *same*
output `o`, and the result is still a function of that output. -/
theorem r4HeavyFamily_bound (Hs : Finset J)
    (T : ∀ j, LFKernel O (Xj j) H ι)
    (μ : ∀ j, Measure (Xj j)) (h : H) (g : ι → ℂ)
    (F : ∀ j, O → Xj j → ℂ)
    (hF : ∀ j o x, ‖F j o x‖ ≤ 1)
    (κ : J → ℝ)
    (hpoint : ∀ j ∈ Hs, ∀ o,
      ∫⁻ x, (T j).absW o x h g ∂(μ j) ≤ ENNReal.ofReal (Real.exp (-κ j)))
    (o : O) :
    ‖r4HeavyFamily Hs T μ h g F o‖ ≤ ∑ j ∈ Hs, Real.exp (-κ j) := by
  unfold r4HeavyFamily
  calc
    ‖∑ j ∈ Hs, (T j).op (μ j) h g (F j) o‖
        ≤ ∑ j ∈ Hs, ‖(T j).op (μ j) h g (F j) o‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Hs, Real.exp (-κ j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact r4HeavyActivity_bound (T j) (μ j) h g (F j) (hF j)
        (κ j) (hpoint j hj) o

end Family

end Balaban.LargeField
