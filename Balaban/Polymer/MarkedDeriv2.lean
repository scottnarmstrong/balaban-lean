/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Balaban.Polymer.CauchySum
public import Balaban.Polymer.MarkedDeriv

/-!
# First and second derivatives of `∫ exp (A + ∑ₖ wₖ Gₖ)` in the marks

For bounded measurable `A, Gₖ` and a probability measure `ν`, the function
`Ψ(w) = ∫ exp (A + ∑ₖ wₖ Gₖ) dν` has directional derivatives
`∂_i Ψ(w) = ∫ G_i exp (A + ∑ₖ wₖ Gₖ) dν`, and, when `Ψ` is analytic near `0`,
`D1 i Ψ = ∫ G_i exp A` and `D2 i j Ψ = ∫ G_i G_j exp A` (`D2_Psi`).
-/

@[expose] public section

namespace Balaban.Polymer

open MeasureTheory Metric Balaban.Analysis

theorem hasDerivAt_expMark_mul {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (A G B : X → ℂ) (hA : Measurable A) (hG : Measurable G)
    (hB : Measurable B) {CA CG CB : ℝ} (hCG : 0 ≤ CG) (hCB : 0 ≤ CB)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hGb : ∀ x, ‖G x‖ ≤ CG) (hBb : ∀ x, ‖B x‖ ≤ CB) :
    HasDerivAt (fun z : ℂ => ∫ x, B x * Complex.exp (A x + z * G x) ∂ν)
      (∫ x, B x * (G x * Complex.exp (A x)) ∂ν) 0 := by
  have hmeas : ∀ z : ℂ, Measurable (fun x => B x * Complex.exp (A x + z * G x)) := fun z =>
    hB.mul (Complex.measurable_exp.comp (hA.add (measurable_const.mul hG)))
  have hint : Integrable (fun x => B x * Complex.exp (A x + (0 : ℂ) * G x)) ν := by
    refine Integrable.of_bound (hmeas 0).aestronglyMeasurable (CB * Real.exp CA)
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [zero_mul, add_zero, norm_mul]
    exact mul_le_mul (hBb x) ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 (hAb x)))
      (norm_nonneg _) hCB
  have hF'm : Measurable (fun x => B x * (G x * Complex.exp (A x + (0 : ℂ) * G x))) :=
    hB.mul (hG.mul (Complex.measurable_exp.comp (hA.add (measurable_const.mul hG))))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℂ))
    (F := fun (z : ℂ) x => B x * Complex.exp (A x + z * G x))
    (F' := fun (z : ℂ) x => B x * (G x * Complex.exp (A x + z * G x))) (s := ball (0 : ℂ) 1)
    (bound := fun _ => CB * (CG * Real.exp (CA + CG))) (ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun z => (hmeas z).aestronglyMeasurable) hint
    hF'm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x z hz => by
      rw [norm_mul, norm_mul]
      refine mul_le_mul (hBb x) (mul_le_mul (hGb x)
        ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)) (norm_nonneg _) hCG)
        (by positivity) hCB
      calc ‖A x + z * G x‖ ≤ ‖A x‖ + ‖z * G x‖ := norm_add_le _ _
        _ ≤ CA + CG := by
          rw [norm_mul]
          refine add_le_add (hAb x) ?_
          have : ‖z‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hz).le
          calc ‖z‖ * ‖G x‖ ≤ 1 * CG := mul_le_mul this (hGb x) (norm_nonneg _) zero_le_one
            _ = CG := one_mul _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x z _ => by
      have h1 : HasDerivAt (fun z : ℂ => A x + z * G x) (G x) z := by
        simpa using ((hasDerivAt_id z).mul_const (G x)).const_add (A x)
      have := (HasDerivAt.cexp h1).const_mul (B x)
      simpa [mul_comm, mul_left_comm] using this)
  simpa using key.2

section Psi

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Ψ(w) = ∫ exp (A + ∑ₖ wₖ Gₖ) dν`. -/
noncomputable def Psi (A : X → ℂ) (G : ι → X → ℂ) (w : ι → ℂ) : ℂ :=
  ∫ x, Complex.exp (A x + ∑ k, w k * G k x) ∂ν

variable {ν}

theorem Psi_line_hasDerivAt [IsProbabilityMeasure ν] {A : X → ℂ} {G : ι → X → ℂ}
    (hA : Measurable A) (hG : ∀ k, Measurable (G k)) {CA CG : ℝ} (hCG : 0 ≤ CG)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hGb : ∀ k x, ‖G k x‖ ≤ CG) (w : ι → ℂ) (i : ι) :
    HasDerivAt (fun t : ℂ => Psi ν A G (w + t • Pi.single i 1))
      (∫ x, G i x * Complex.exp (A x + ∑ k, w k * G k x) ∂ν) 0 := by
  set A' : X → ℂ := fun x => A x + ∑ k, w k * G k x with hA'
  have hA'm : Measurable A' := hA.add (Finset.measurable_fun_sum _ (fun k _ =>
    measurable_const.mul (hG k)))
  have hA'b : ∀ x, ‖A' x‖ ≤ CA + ∑ k, ‖w k‖ * CG := fun x => by
    refine (norm_add_le _ _).trans (add_le_add (hAb x) ((norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun k _ => ?_))))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hGb k x) (norm_nonneg _)
  have := hasDerivAt_expMark ν A' (G i) hA'm (hG i) hCG hA'b (hGb i)
  have heq : (fun t : ℂ => Psi ν A G (w + t • Pi.single i 1)) =
      fun t : ℂ => ∫ x, Complex.exp (A' x + t * G i x) ∂ν := by
    funext t
    unfold Psi
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hA', Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    ring_nf
  rw [heq]
  exact this

theorem fderiv_single_eq_deriv_line {F : (ι → ℂ) → ℂ} {w : ι → ℂ} (hF : DifferentiableAt ℂ F w)
    (i : ι) : fderiv ℂ F w (Pi.single i 1) = deriv (fun t : ℂ => F (w + t • Pi.single i 1)) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => w + t • (Pi.single i 1 : ι → ℂ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single i 1 : ι → ℂ)).const_add w
  have h2 : HasFDerivAt F (fderiv ℂ F w) (w + (0 : ℂ) • (Pi.single i 1 : ι → ℂ)) := by
    simpa using hF.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℂ) h1).deriv.symm

variable [IsProbabilityMeasure ν] {A : X → ℂ} {G : ι → X → ℂ} {CA CG : ℝ}

theorem D1_Psi {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hana : AnalyticOnNhd ℂ (Psi ν A G) (polydisc 0 r))
    (hA : Measurable A) (hG : ∀ k, Measurable (G k)) (hCG : 0 ≤ CG)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hGb : ∀ k x, ‖G k x‖ ≤ CG) (i : ι) :
    D1 i (Psi ν A G) = ∫ x, G i x * Complex.exp (A x) ∂ν := by
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k
  unfold D1
  rw [fderiv_single_eq_deriv_line (hana 0 h0).differentiableAt i]
  have := (Psi_line_hasDerivAt (ν := ν) hA hG hCG hAb hGb 0 i).deriv
  simpa using this

theorem D2_Psi {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hana : AnalyticOnNhd ℂ (Psi ν A G) (polydisc 0 r))
    (hA : Measurable A) (hG : ∀ k, Measurable (G k)) (hCG : 0 ≤ CG)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hGb : ∀ k x, ‖G k x‖ ≤ CG) (i j : ι) :
    D2 i j (Psi ν A G) = ∫ x, G i x * (G j x * Complex.exp (A x)) ∂ν := by
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k
  have hopen := isOpen_polydisc (0 : ι → ℂ) r
  set Om : (ι → ℂ) → ℂ := fun w => ∫ x, G i x * Complex.exp (A x + ∑ k, w k * G k x) ∂ν with hOm
  have hev : (fun w => fderiv ℂ (Psi ν A G) w (Pi.single i 1)) =ᶠ[nhds (0 : ι → ℂ)] Om := by
    filter_upwards [hopen.mem_nhds h0] with w hw
    rw [fderiv_single_eq_deriv_line (hana w hw).differentiableAt i]
    exact (Psi_line_hasDerivAt (ν := ν) hA hG hCG hAb hGb w i).deriv
  have hd : DifferentiableAt ℂ (fun w => fderiv ℂ (Psi ν A G) w (Pi.single i 1)) 0 :=
    ((hana.fderiv 0 h0).differentiableAt).clm_apply (differentiableAt_const _)
  have hdOm : DifferentiableAt ℂ Om 0 := hd.congr_of_eventuallyEq hev.symm
  unfold D2
  rw [hev.fderiv_eq, fderiv_single_eq_deriv_line hdOm j]
  -- the line through `0` in direction `j`
  have hBm : Measurable (G i) := hG i
  have hGi : ∀ x, ‖G i x‖ ≤ CG := hGb i
  have := hasDerivAt_expMark_mul ν A (G j) (G i) hA (hG j) hBm hCG hCG hAb (hGb j) hGi
  have heq : (fun t : ℂ => Om (0 + t • Pi.single j 1)) =
      fun t : ℂ => ∫ x, G i x * Complex.exp (A x + t * G j x) ∂ν := by
    funext t
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.zero_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, zero_add,
      mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [heq]
  exact this.deriv

end Psi

end Balaban.Polymer
