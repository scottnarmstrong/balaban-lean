/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepIdentityInhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Regularity of the class in the block directions, and parameter integrals (FLUCTUATION.md §2.5)

The localized energies `ℰ₁^{(k+1)}(z)` of P4 (2.56)-(2.60) differentiate the exponent
`Φ₁(y) = -β V^{(k)}(ψ^{(k)} + y) + δℰ_k(ψ^{(k)} + y)` in the directions `1_{B(z)} ψ'`, not only along
the ray `s ↦ s ψ'`.  The named input `ClassRegular` is the regularity along the ray; the identity
`∑_z ℰ₁(z) = ℰ₁` needs `Φ₁` to be `C¹` near the segments, so `ClassRegularLoc` extends `ClassRegular`
by this single field (the analytic terms `ℰ_k` and `V^{(k)}` are analytic on the domain, (H.2)).

* `ClassRegularLoc`: `ClassRegular` plus `Φ₁ ∈ C¹` on an open set containing `s ψ'(ψ̂)`,
  `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`;
* `continuousOn_integral_param`: continuity in a parameter of an integral over a compact support.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set

section Param

variable {Ω : Type*} [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
  {ν : Measure Ω} [IsFiniteMeasure ν]

omit [T2Space Ω] in
/-- Continuity on `[0,1]` of a parameter integral over a compact support `B` of `ν`. -/
theorem continuousOn_integral_param {B : Set Ω} (hBc : IsCompact B) (hBm : MeasurableSet B)
    (hB : ∀ᵐ ω ∂ν, ω ∈ B) {F : ℝ → Ω → ℂ}
    (hF : ContinuousOn (fun q : ℝ × Ω => F q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ B)) :
    ContinuousOn (fun s => ∫ ω, F s ω ∂ν) (Icc (0 : ℝ) 1) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hBc).exists_bound_of_continuousOn hF
  have hν : ν.restrict B = ν := Measure.restrict_eq_self_of_ae_mem hB
  refine continuousOn_of_dominated (bound := fun _ => M) (fun s hs => ?_) (fun s hs => ?_)
    (integrable_const M) ?_
  · have : ContinuousOn (F s) B := hF.comp (f := fun ω => (s, ω)) (by fun_prop) (fun ω hω => ⟨hs, hω⟩)
    have h := this.aestronglyMeasurable hBm (μ := ν)
    rwa [hν] at h
  · filter_upwards [hB] with ω hω
    exact hM (s, ω) ⟨hs, hω⟩
  · filter_upwards [hB] with ω hω
    exact hF.comp (f := fun s => (s, ω)) (by fun_prop) (fun s hs => ⟨hs, hω⟩)

/-- A function continuous on a compact support of a finite measure is integrable. -/
theorem integrable_of_continuousOn {B : Set Ω} (hBc : IsCompact B) (hB : ∀ᵐ ω ∂ν, ω ∈ B)
    {G : Ω → ℂ} (hG : ContinuousOn G B) : Integrable G ν := by
  have hν : ν.restrict B = ν := Measure.restrict_eq_self_of_ae_mem hB
  have := hG.integrableOn_compact hBc (μ := ν)
  rwa [IntegrableOn, hν] at this

end Param

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-- **Regularity of the class in the block directions** (extension of the named input
`ClassRegular`): the exponent `Φ₁(y) = -β V^{(k)}(ψ^{(k)} + y) + δℰ_k(ψ^{(k)} + y)` is `C¹` on an open
set containing the segments `s ψ'(ψ̂)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁` (analyticity of `ℰ_k` and of the
interaction, (H.2), on the domain of the composed data). -/
structure ClassRegularLoc (g : Fld d L N₁ m₁ (k + 1) N) : Prop extends S.ClassRegular C g where
  phi1 : ∃ O : Set S.E, IsOpen O ∧ ContDiffOn ℝ 1 (S.Phi1 C) O ∧
    ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ s ∈ Icc (0 : ℝ) 1, s • S.shiftU x ∈ O

theorem Wone_eq_Phi1 (s : ℝ) (x : S.E) : S.Wone C s x = S.Phi1 C (s • S.shiftU x) := rfl

theorem continuous_shiftU : Continuous S.shiftU := by
  unfold shiftU
  exact (LinearMap.continuous_of_finiteDimensional S.K).const_smul (S.betaU ^ (-(1 / 2 : ℝ)))

theorem continuous_maskU (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Continuous (S.maskU z) := by
  classical
  refine continuous_pi fun b => ?_
  by_cases h : b ∈ S.blockU z
  · simp only [maskU, h, ↓reduceIte]; exact continuous_apply b
  · simp only [maskU, h, ↓reduceIte]; exact continuous_const

theorem sum_maskU (x : S.E) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.maskU z x = x := by
  classical
  funext b
  rw [Finset.sum_apply]
  simp only [maskU, blockU, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_eq_single (unitBlock1 (b : UnitTorus d L N₁ m₁ k))]
  · simp
  · intro z _ hz
    have : ¬ (unitBlock1 (b : UnitTorus d L N₁ m₁ k) = z) := fun h => hz h.symm
    simp [this]
  · simp

section Local

variable {C} {O : Set S.E} (hO : IsOpen O) (hcd : ContDiffOn ℝ 1 (S.Phi1 C) O)
  (hmem : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ s ∈ Icc (0 : ℝ) 1, s • S.shiftU x ∈ O)

include hcd hmem in
theorem continuousOn_Phi1_ray :
    ContinuousOn (fun q : ℝ × S.E => S.Phi1 C (q.1 • S.shiftU q.2))
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
  refine hcd.continuousOn.comp (by have := S.continuous_shiftU; fun_prop) ?_
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  exact hmem x (by simpa using hx) s hs

include hO hcd hmem in
theorem continuousOn_fderiv_ray (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ContinuousOn (fun q : ℝ × S.E =>
      (fderiv ℝ (S.Phi1 C) (q.1 • S.shiftU q.2)) (S.maskU z (S.shiftU q.2)))
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
  have hf : ContinuousOn (fderiv ℝ (S.Phi1 C)) O :=
    hcd.continuousOn_fderiv_of_isOpen hO le_rfl
  have h1 : ContinuousOn (fun q : ℝ × S.E => fderiv ℝ (S.Phi1 C) (q.1 • S.shiftU q.2))
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
    refine hf.comp (by have := S.continuous_shiftU; fun_prop) ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact hmem x (by simpa using hx) s hs
  refine h1.clm_apply ?_
  have := S.continuous_shiftU
  have := S.continuous_maskU z
  fun_prop

include hO hcd hmem in
theorem hasDerivAt_Wone_ray {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => S.Wone C r x) ((fderiv ℝ (S.Phi1 C) (s • S.shiftU x)) (S.shiftU x)) s := by
  have hd : DifferentiableAt ℝ (S.Phi1 C) (s • S.shiftU x) :=
    (hcd.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds (hmem x hx s hs))
  have hp : HasDerivAt (fun r : ℝ => r • S.shiftU x) (S.shiftU x) s := by
    simpa using (hasDerivAt_id s).smul_const (S.shiftU x)
  exact hd.hasFDerivAt.comp_hasDerivAt s hp

end Local

end StepSetting

end Balaban.Fluctuation
