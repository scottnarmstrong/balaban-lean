/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation measure (FLUCTUATION.md §2.5) and the change of variables (2.7)

`ν₁ = fluctMeasure1 N p` on `ℝ^N = EuclideanSpace ℝ (Fin N)` has density
`Z₁⁻¹ 1[|ψ̂| < p] e^{-|ψ̂|²/2}`; `fluctMeasure T N p = ⨂_{x ∈ T} ν₁` is the product (2.5).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

/-- `ℝ^N` with the Euclidean norm. -/
abbrev Rn (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The unnormalized density `1[|ψ̂| < p] e^{-|ψ̂|²/2}` of `ν₁`. -/
noncomputable def fluctDensity (N : ℕ) (p : ℝ) (x : Rn N) : ℝ :=
  if ‖x‖ < p then Real.exp (-(‖x‖ ^ 2 / 2)) else 0

/-- The normalization `Z₁ = ∫ 1[|ψ̂| < p] e^{-|ψ̂|²/2} dψ̂`. -/
noncomputable def fluctNorm (N : ℕ) (p : ℝ) : ℝ := ∫ x : Rn N, fluctDensity N p x

/-- The single-site measure `ν₁(dψ̂) = Z₁⁻¹ 1[|ψ̂| < p] e^{-|ψ̂|²/2} dψ̂` on `ℝ^N`. -/
noncomputable def fluctMeasure1 (N : ℕ) (p : ℝ) : Measure (Rn N) :=
  ENNReal.ofReal (fluctNorm N p)⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (fluctDensity N p x))

/-- The product measure `ν_{p} = ⨂_{x ∈ T} ν₁` on `(ℝ^N)^T` (2.5). -/
noncomputable def fluctMeasure (T : Type*) [Fintype T] (N : ℕ) (p : ℝ) : Measure (T → Rn N) :=
  Measure.pi fun _ => fluctMeasure1 N p

/-- `e(N,p) = log ((2π)^{-N/2} Z₁)`. -/
noncomputable def fluctE (N : ℕ) (p : ℝ) : ℝ :=
  Real.log ((2 * π) ^ (-(N : ℝ) / 2) * fluctNorm N p)

private theorem integrable_gauss (N : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Rn N => Real.exp (-b * ‖x‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Rn N)
    (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [show (-(b : ℂ) * (‖x‖ : ℂ) ^ 2) = ((-b * ‖x‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

private theorem integral_gauss (N : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ x : Rn N, Real.exp (-b * ‖x‖ ^ 2) = (π / b) ^ ((N : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp

theorem fluctDensity_nonneg (N : ℕ) (p : ℝ) (x : Rn N) : 0 ≤ fluctDensity N p x := by
  unfold fluctDensity; split_ifs <;> positivity

theorem fluctDensity_le (N : ℕ) (p : ℝ) (x : Rn N) :
    fluctDensity N p x ≤ Real.exp (-(1 / 2) * ‖x‖ ^ 2) := by
  unfold fluctDensity
  split_ifs
  · exact le_of_eq (by congr 1; ring)
  · positivity

theorem measurable_fluctDensity (N : ℕ) (p : ℝ) : Measurable (fluctDensity N p) := by
  unfold fluctDensity
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
    measurable_const

theorem integrable_fluctDensity (N : ℕ) (p : ℝ) : Integrable (fluctDensity N p) :=
  (integrable_gauss N (by norm_num : (0 : ℝ) < 1 / 2)).mono'
    (measurable_fluctDensity N p).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fluctDensity_nonneg N p x)]
      exact fluctDensity_le N p x)

theorem fluctNorm_pos (N : ℕ) {p : ℝ} (hp : 0 < p) : 0 < fluctNorm N p := by
  unfold fluctNorm
  rw [integral_pos_iff_support_of_nonneg (fluctDensity_nonneg N p) (integrable_fluctDensity N p)]
  have : Function.support (fluctDensity N p) = Metric.ball (0 : Rn N) p := by
    ext x
    simp only [Function.mem_support, fluctDensity, mem_ball_zero_iff]
    split_ifs with h <;> simp [h]
  rw [this]
  exact Metric.measure_ball_pos _ _ hp

theorem lintegral_fluctDensity (N : ℕ) {p : ℝ} :
    ∫⁻ x, ENNReal.ofReal (fluctDensity N p x) = ENNReal.ofReal (fluctNorm N p) := by
  unfold fluctNorm
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_fluctDensity N p)
    (ae_of_all _ (fluctDensity_nonneg N p))]

/-- `ν₁` is a probability measure. -/
theorem isProbabilityMeasure_fluctMeasure1 (N : ℕ) {p : ℝ} (hp : 0 < p) :
    IsProbabilityMeasure (fluctMeasure1 N p) := by
  constructor
  have hZ := fluctNorm_pos N hp
  simp only [fluctMeasure1, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_fluctDensity, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hZ.le), inv_mul_cancel₀ hZ.ne', ENNReal.ofReal_one]

/-- The product measure (2.5) is a probability measure. -/
theorem isProbabilityMeasure_fluctMeasure (T : Type*) [Fintype T] (N : ℕ) {p : ℝ} (hp : 0 < p) :
    IsProbabilityMeasure (fluctMeasure T N p) := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  unfold fluctMeasure
  infer_instance

/-- Integrals against `ν₁` are `Z₁⁻¹ ∫ 1[|ψ̂| < p] e^{-|ψ̂|²/2} f`. -/
theorem integral_fluctMeasure1 (N : ℕ) (p : ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Rn N → E) :
    ∫ x, f x ∂fluctMeasure1 N p = (fluctNorm N p)⁻¹ • ∫ x, fluctDensity N p x • f x := by
  unfold fluctMeasure1
  rw [integral_smul_measure, ENNReal.toReal_ofReal]
  · rw [integral_withDensity_eq_integral_toReal_smul]
    · congr 2
      funext x
      rw [ENNReal.toReal_ofReal (fluctDensity_nonneg N p x)]
    · exact (measurable_fluctDensity N p).ennreal_ofReal
    · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top
  · by_cases hp : 0 < p
    · exact inv_nonneg.2 (fluctNorm_pos N hp).le
    · have : fluctNorm N p = 0 := by
        unfold fluctNorm
        have : fluctDensity N p = 0 := by
          funext x
          have h : ¬ ‖x‖ < p := not_lt.2 ((not_lt.1 hp).trans (norm_nonneg x))
          simp [fluctDensity, h]
        simp [this]
      simp [this]

/-- Gaussian tail bound: the mass of `e^{-|ψ̂|²/2}` outside the ball of radius `p` is at most
`e^{-p²/4} (4π)^{N/2}`. -/
theorem integral_gauss_sub_fluctNorm_le (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (2 * π) ^ ((N : ℝ) / 2) - fluctNorm N p ≤ Real.exp (-(p ^ 2 / 4)) * (4 * π) ^ ((N : ℝ) / 2) := by
  have hG := integral_gauss N (b := 1 / 2) (by norm_num)
  have hG4 := integral_gauss N (b := 1 / 4) (by norm_num)
  have e1 : π / (1 / 2) = 2 * π := by ring
  have e2 : π / (1 / 4) = 4 * π := by ring
  rw [e1] at hG
  rw [e2] at hG4
  have iG := integrable_gauss N (b := 1 / 2) (by norm_num)
  have iG4 := integrable_gauss N (b := 1 / 4) (by norm_num)
  unfold fluctNorm
  rw [← hG, ← integral_sub iG (integrable_fluctDensity N p), ← hG4, ← integral_const_mul]
  refine integral_mono (iG.sub (integrable_fluctDensity N p)) (iG4.const_mul _) fun x => ?_
  by_cases hx : ‖x‖ < p
  · have : fluctDensity N p x = Real.exp (-(‖x‖ ^ 2 / 2)) := by simp [fluctDensity, hx]
    rw [this, show -(1 / 2 : ℝ) * ‖x‖ ^ 2 = -(‖x‖ ^ 2 / 2) by ring, sub_self]
    positivity
  · have : fluctDensity N p x = 0 := by simp [fluctDensity, hx]
    rw [this, sub_zero, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : p ^ 2 ≤ ‖x‖ ^ 2 := by
      have := not_lt.1 hx
      nlinarith
    nlinarith

theorem fluctNorm_le (N : ℕ) (p : ℝ) : fluctNorm N p ≤ (2 * π) ^ ((N : ℝ) / 2) := by
  have hG := integral_gauss N (b := 1 / 2) (by norm_num)
  rw [show π / (1 / 2) = 2 * π by ring] at hG
  rw [← hG]
  exact integral_mono (integrable_fluctDensity N p) (integrable_gauss N (by norm_num))
    fun x => fluctDensity_le N p x

theorem fluctNorm_mono (N : ℕ) {p q : ℝ} (h : p ≤ q) : fluctNorm N p ≤ fluctNorm N q := by
  refine integral_mono (integrable_fluctDensity N p) (integrable_fluctDensity N q) fun x => ?_
  unfold fluctDensity
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_lt_of_le h1 h) h2
  · positivity
  · exact le_rfl

/-- The constant `C_N = (4π)^{N/2} / Z₁(1)` in the bound for `e(N,p)`. -/
noncomputable def fluctConst (N : ℕ) : ℝ := (4 * π) ^ ((N : ℝ) / 2) / fluctNorm N 1

/-- **(2.5), the vacuum constant.** For `p ≥ 1`, `|e(N,p)| ≤ C_N e^{-p²/4}`
where `e(N,p) = log ((2π)^{-N/2} Z₁)`. -/
theorem abs_fluctE_le (N : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    |fluctE N p| ≤ fluctConst N * Real.exp (-(p ^ 2 / 4)) := by
  set K : ℝ := (2 * π) ^ ((N : ℝ) / 2) with hK
  have hKpos : 0 < K := by positivity
  have hZ1 : 0 < fluctNorm N 1 := fluctNorm_pos N one_pos
  have hZ : fluctNorm N 1 ≤ fluctNorm N p := fluctNorm_mono N hp
  have hZpos : 0 < fluctNorm N p := hZ1.trans_le hZ
  have hZK := fluctNorm_le N p
  have htail := integral_gauss_sub_fluctNorm_le N (p := p) (by linarith)
  have hr : (2 * π) ^ (-(N : ℝ) / 2) = K⁻¹ := by
    rw [hK, ← Real.rpow_neg (by positivity)]
    congr 1; ring
  unfold fluctE
  rw [hr]
  have hle : K⁻¹ * fluctNorm N p ≤ 1 := by
    rw [inv_mul_le_iff₀ hKpos]; linarith
  have hrpos : 0 < K⁻¹ * fluctNorm N p := by positivity
  have hlog : Real.log (K⁻¹ * fluctNorm N p) ≤ 0 := Real.log_nonpos hrpos.le hle
  rw [abs_of_nonpos hlog]
  have h1 : -Real.log (K⁻¹ * fluctNorm N p) ≤ K / fluctNorm N p - 1 := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hrpos)
    rw [Real.log_inv] at this
    have e : (K⁻¹ * fluctNorm N p)⁻¹ = K / fluctNorm N p := by
      field_simp
    rw [e] at this
    exact this
  refine h1.trans ?_
  have h2 : K / fluctNorm N p - 1 = (K - fluctNorm N p) / fluctNorm N p := by
    field_simp
  rw [h2, fluctConst]
  calc (K - fluctNorm N p) / fluctNorm N p
      ≤ (Real.exp (-(p ^ 2 / 4)) * (4 * π) ^ ((N : ℝ) / 2)) / fluctNorm N 1 := by
        refine div_le_div₀ (by positivity) htail hZ1 hZ
    _ = _ := by ring

section ChangeOfVariables

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]

/-- **The linear change of variables (2.7).**  For an invertible linear `A` and `β > 0`, the
substitution `ψ' = β^{-1/2} A ψ̂` gives `dψ' = β^{-n/2} |det A| dψ̂` (`n = dim X`). -/
theorem integral_eq_smul_integral_comp_smul_linearMap (μ : Measure X) [μ.IsAddHaarMeasure]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : X →ₗ[ℝ] X)
    (hA : LinearMap.det A ≠ 0) {β : ℝ} (hβ : 0 < β) (f : X → F) :
    ∫ y, f y ∂μ = (β ^ (-(Module.finrank ℝ X : ℝ) / 2) * |LinearMap.det A|) •
      ∫ x, f ((β ^ (-(1 / 2 : ℝ))) • A x) ∂μ := by
  set c : ℝ := β ^ (-(1 / 2 : ℝ)) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos hβ _
  set M : X →ₗ[ℝ] X := c • A with hM
  have hdet : LinearMap.det M = c ^ Module.finrank ℝ X * LinearMap.det A := by
    rw [hM, LinearMap.det_smul]
  have hMne : LinearMap.det M ≠ 0 := by
    rw [hdet]; exact mul_ne_zero (pow_pos hcpos _).ne' hA
  let e : X ≃ₗ[ℝ] X := LinearMap.equivOfDetNeZero M hMne
  have hemb : MeasurableEmbedding e :=
    (e.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hMne
  have key : ∫ x, f (M x) ∂μ = |LinearMap.det M|⁻¹ • ∫ y, f y ∂μ := by
    have : ∫ x, f (e x) ∂μ = ∫ y, f y ∂(Measure.map e μ) := (hemb.integral_map f).symm
    have he : (e : X → X) = M := rfl
    rw [he] at this
    rw [this, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
    simp [abs_inv]
  have hcn : c ^ Module.finrank ℝ X = β ^ (-(Module.finrank ℝ X : ℝ) / 2) := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hβ.le]
    congr 1; ring
  have hpos : 0 < |LinearMap.det M| := abs_pos.2 hMne
  have hMx : ∀ x, f (M x) = f (c • A x) := fun x => rfl
  simp_rw [hMx] at key
  have hnz : β ^ (-(Module.finrank ℝ X : ℝ) / 2) * |LinearMap.det A| ≠ 0 :=
    mul_ne_zero (Real.rpow_pos_of_pos hβ _).ne' (abs_ne_zero.2 hA)
  rw [key, smul_smul, hdet, abs_mul, abs_of_pos (pow_pos hcpos _), hcn, mul_inv_cancel₀ hnz,
    one_smul]

end ChangeOfVariables

/-- The change of variables (2.7) on `(ℝ^N)^T` with Lebesgue measure: the Jacobian is
`β^{-N|T|/2} |det A|`. -/
theorem integral_eq_smul_integral_comp_smul_linearMap_pi (T : Type*) [Fintype T] (N : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (A : (T → Rn N) →ₗ[ℝ] (T → Rn N))
    (hA : LinearMap.det A ≠ 0) {β : ℝ} (hβ : 0 < β) (f : (T → Rn N) → F) :
    ∫ y, f y = (β ^ (-((N * Fintype.card T : ℕ) : ℝ) / 2) * |LinearMap.det A|) •
      ∫ x, f ((β ^ (-(1 / 2 : ℝ))) • A x) := by
  have := integral_eq_smul_integral_comp_smul_linearMap (volume : Measure (T → Rn N)) A hA hβ f
  simpa [Module.finrank_pi_fintype, mul_comm] using this

end Balaban.Fluctuation
