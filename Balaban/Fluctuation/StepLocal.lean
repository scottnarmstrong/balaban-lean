/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepLocalReg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized energies add up (FLUCTUATION.md §2.5, P4 (2.56)-(2.60))

* `sum_E1loc`: `∑_z ℰ₁^{(k+1)}(z) = ℰ₁^{(k+1)}` (the blocks `B_{k+1}(z)` partition the unit lattice,
  the derivative of `Φ₁` is linear in the direction, the expectations are continuous on `[0,1]`);
* `sum_E0loc`: `∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}`, with the trace identity of Lemma 2.4 (c).

Inputs: `ClassRegularLoc` (the named input `ClassRegular` extended by the `C¹` regularity of
`Φ₁` near the segments) and `StepNonvanishing` (the denominators `Z_{s,0}`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

theorem partFun_Wone_eq (g : Fld d L N₁ m₁ (k + 1) N) (s : ℝ) :
    S.Zst C g s 0 = partFun S.nuFl (S.Wone C) s := by
  unfold Zst partFun₂ partFun
  simp [S.Wtwo_zero C g]

theorem ae_mem_closedBall (hp₁ : 0 < S.p₁) :
    ∀ᵐ x ∂S.nuFl, x ∈ Metric.closedBall (0 : S.E) S.p₁ := by
  filter_upwards [S.ae_ball hp₁] with x hx
  rw [mem_closedBall_zero_iff]
  exact ((chiFl_eq_one_iff hp₁ x).1 hx).le

/-- **`∑_z ℰ₁^{(k+1)}(z) = ℰ₁^{(k+1)}`** (P4 (2.56)-(2.60)). -/
theorem sum_E1loc (hp₁ : 0 < S.p₁) (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularLoc C g)
    (hnv : S.StepNonvanishing C g) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E1loc C z = S.E1 C := by
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  have : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  set B : Set S.E := Metric.closedBall (0 : S.E) S.p₁ with hBdef
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hB : ∀ᵐ x ∂S.nuFl, x ∈ B := S.ae_mem_closedBall hp₁
  -- the integrands
  set fz : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℝ → S.E → ℂ :=
    fun z s x => (fderiv ℝ (S.Phi1 C) (s • S.shiftU x)) (S.maskU z (S.shiftU x)) with hfz
  have hWc : ContinuousOn (fun q : ℝ × S.E => S.Wone C q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ B) :=
    S.continuousOn_Phi1_ray hcd hmem
  have hEc : ContinuousOn (fun q : ℝ × S.E => Complex.exp (S.Wone C q.1 q.2))
      (Icc (0 : ℝ) 1 ×ˢ B) := Complex.continuous_exp.comp_continuousOn hWc
  have hFc : ∀ z, ContinuousOn (fun q : ℝ × S.E => fz z q.1 q.2 * Complex.exp (S.Wone C q.1 q.2))
      (Icc (0 : ℝ) 1 ×ˢ B) := fun z =>
    (S.continuousOn_fderiv_ray hO hcd hmem z).mul hEc
  -- denominators
  have hZ : ∀ s ∈ Icc (0 : ℝ) 1, partFun S.nuFl (S.Wone C) s ≠ 0 := fun s hs => by
    rw [← S.partFun_Wone_eq C g]; exact hnv.seg1 s hs
  have hZc : ContinuousOn (partFun S.nuFl (S.Wone C)) (Icc (0 : ℝ) 1) :=
    continuousOn_integral_param hBc hBm hB (F := fun s x => Complex.exp (S.Wone C s x)) hEc
  -- the averages are continuous
  have havg : ∀ z, ContinuousOn (fun s => avgFun S.nuFl (S.Wone C) (fz z s) s) (Icc (0 : ℝ) 1) :=
    fun z => (continuousOn_integral_param hBc hBm hB (hFc z)).div hZc hZ
  -- sum identity at each `s`
  have hint : ∀ z, ∀ s ∈ Icc (0 : ℝ) 1,
      Integrable (fun x => fz z s x * Complex.exp (S.Wone C s x)) S.nuFl := fun z s hs =>
    integrable_of_continuousOn hBc hB
      ((hFc z).comp (f := fun x => (s, x)) (by fun_prop) (fun x hx => ⟨hs, hx⟩))
  have hsum : ∀ s ∈ Icc (0 : ℝ) 1,
      ∑ z, avgFun S.nuFl (S.Wone C) (fz z s) s =
        avgFun S.nuFl (S.Wone C) (fun x => deriv (fun r => S.Wone C r x) s) s := by
    intro s hs
    unfold avgFun
    rw [← Finset.sum_div, ← integral_finsetSum _ (fun z _ => hint z s hs)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hB] with x hx
    rw [← Finset.sum_mul]
    congr 1
    rw [(S.hasDerivAt_Wone_ray hO hcd hmem (mem_closedBall_zero_iff.1 hx) hs).deriv]
    simp only [hfz]
    rw [← map_sum, S.sum_maskU]
  unfold E1loc E1
  rw [← intervalIntegral.integral_finsetSum]
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact hsum s hs
  · intro z _
    exact (havg z).intervalIntegrable_of_Icc zero_le_one

section Trace

variable {δ' : ℝ} (H' : BgHyp d L (k + 1) ϱ S.a S.ν) (hδ'0 : 0 < δ')
  (hδ' : δ' ≤ thm73C3 d L N / 2) (hD'R : InDomainR S.G' S.ν δ' S.D')
  (hδ0 : 0 < S.δ)
  (hχ : ChiUBounds S.G' S.ν S.δ S.D' (bgField S.G' S.a S.ν S.D') (bgMult S.G' S.a S.ν S.D'))
  (hfam : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x (bgMult S.G' S.a S.ν S.D') 0 (fun _ => 1))
  (hsm : S.δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include S H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- The trace of the logarithm of Lemma 2.4 (c) is real. -/
theorem trace_logA_im :
    (∑ y : S.U, ∑ i : Fin N, S.logA (y, i) (y, i)).im = 0 :=
  (lemma24_c_logdet hfam (S.constraintField_bg H' hδ'0 hδ' hD'R hδ0 hχ) hδ0.le hsm
    (S.bgMult_real_S H' hδ'0 hδ' hD'R) (S.svec_bg_real H' hδ'0 hδ' hD'R)).2.2.1

include S C H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm in
/-- **`∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}`** (P4 (2.56)): the trace part is
`sum_blockU_trace` with `½ log det C^{(k)} = -½ ∑_y tr 𝕃(y,y)` (Lemma 2.4 (c)), the rest is
`sum_E1loc`. -/
theorem sum_E0loc (hp₁ : 0 < S.p₁) (g : Fld d L N₁ m₁ (k + 1) N)
    (hc : S.ClassRegularLoc C g) (hnv : S.StepNonvanishing C g) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E0loc C z = S.E0 C := by
  unfold E0loc E0
  rw [Finset.sum_add_distrib, S.sum_E1loc C hp₁ g hc hnv, ← Finset.mul_sum]
  have h1 : ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      ∑ y ∈ S.blockU z, ∑ i : Fin N, S.logA (y, i) (y, i) =
        ∑ y : S.U, ∑ i : Fin N, S.logA (y, i) (y, i) := S.sum_blockU_trace
  have h2 := S.halfLogDetC_eq_trace H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  have h3 := S.trace_logA_im H' hδ'0 hδ' hD'R hδ0 hχ hfam hsm
  rw [h1, h2]
  generalize (∑ y : S.U, ∑ i : Fin N, S.logA (y, i) (y, i)) = T at h3 ⊢
  have h4 : T = ((T.re : ℝ) : ℂ) := Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact h3)
  conv_lhs => rw [h4]
  push_cast
  ring

end Trace

end StepSetting

end Balaban.Fluctuation
