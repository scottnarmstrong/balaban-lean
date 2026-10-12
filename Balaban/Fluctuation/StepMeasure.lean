/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MeasureInterp
public import Balaban.Fluctuation.MeasureAbsorb
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The product measure as a density, and the abstract fluctuation integral (FLUCTUATION.md §2.6)

Abstract part of Proposition 2.6, on a finite product `(ℝ^N)^T` (the unit lattice `T = T^{(k)}_1`):

* `prod_fluctDensity`: `∏_t ν₁-density(ψ̂ t) = χ_fl(ψ̂) e^{-‖ψ̂‖²/2}`;
* `fluctMeasure_eq_withDensity`, `integral_fluctMeasure`: `ν_{p₁} = Z₁^{-|T|} χ_fl e^{-‖ψ̂‖²/2} dψ̂`;
* `interpZ`, `interpAvg`, `interpMeasure`: the partition functions `Z_{s,t}`, expectations
  `⟨f⟩_{s,t}` and interpolating measures `dμ_{s,t}` of (2.6) for real exponents `W₁(s,·)`, `W₂(t,·)`;
* `fluct_integral_eq`: the integral of `P χ_fl e^{-‖ψ̂‖²/2} e^{W₁(1) + W₂(1)}` against Lebesgue
  measure after the substitution (2.7) is `P β^{-N|T|/2} |det A| Z₁^{|T|} Z_{1,1}`, and
  `Z_{1,1} = exp (∫₀¹ ⟨∂_s W₁⟩_{s,0} ds + ∫₀¹ ⟨∂_t W₂⟩_{1,t} dt)` when `W₁(0) = W₂(0) = 0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

section ProductDensity

variable {T : Type*} [Fintype T] {N : ℕ}

/-- `e^{-‖ψ̂‖²/2}` for `ψ̂ ∈ (ℝ^N)^T`, with `‖ψ̂‖² = ∑_t |ψ̂(t)|²`. -/
noncomputable def gaussWeight (T : Type*) [Fintype T] (N : ℕ) (x : T → Rn N) : ℝ :=
  Real.exp (-(∑ t, ‖x t‖ ^ 2) / 2)

theorem gaussWeight_pos (x : T → Rn N) : 0 < gaussWeight T N x := Real.exp_pos _

theorem measurable_gaussWeight : Measurable (gaussWeight T N) := by
  unfold gaussWeight
  fun_prop

theorem prod_fluctDensity (p : ℝ) (x : T → Rn N) :
    ∏ t, fluctDensity N p (x t) = chiFl T N p x * gaussWeight T N x := by
  unfold chiFl gaussWeight
  have h : ∀ t, fluctDensity N p (x t) =
      (if ‖x t‖ < p then (1 : ℝ) else 0) * Real.exp (-(‖x t‖ ^ 2 / 2)) := fun t => by
    unfold fluctDensity; split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib, neg_div, Finset.sum_div]

theorem measurable_chiFl (p : ℝ) : Measurable (chiFl T N p) := by
  unfold chiFl
  refine Finset.measurable_prod _ fun t _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (by fun_prop) measurable_const

theorem measurable_prod_fluctDensity (p : ℝ) :
    Measurable (fun x : T → Rn N => ∏ t, fluctDensity N p (x t)) :=
  Finset.measurable_prod _ fun t _ => (measurable_fluctDensity N p).comp (measurable_pi_apply t)

theorem integrable_fluctDensity_indicator (p : ℝ) (s : Set (Rn N)) (hs : MeasurableSet s) :
    Integrable (s.indicator (fluctDensity N p)) :=
  (integrable_fluctDensity N p).indicator hs

instance isFiniteMeasure_fluctMeasure1 (N : ℕ) (p : ℝ) : IsFiniteMeasure (fluctMeasure1 N p) := by
  constructor
  simp only [fluctMeasure1, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_fluctDensity, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- **The product measure (2.5) is `Z₁^{-|T|} χ_fl e^{-‖ψ̂‖²/2} dψ̂`.** -/
theorem fluctMeasure_eq_withDensity (p : ℝ) :
    fluctMeasure T N p =
      ENNReal.ofReal ((fluctNorm N p)⁻¹ ^ Fintype.card T) •
        (volume : Measure (T → Rn N)).withDensity
          (fun x => ENNReal.ofReal (∏ t, fluctDensity N p (x t))) := by
  classical
  unfold fluctMeasure
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, withDensity_apply _ (MeasurableSet.univ_pi hs), smul_eq_mul]
  have hind : ∀ x : T → Rn N, (Set.pi univ s).indicator
      (fun x => ∏ t, fluctDensity N p (x t)) x = ∏ t, (s t).indicator (fluctDensity N p) (x t) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Set.indicator_of_mem (hx t (mem_univ t))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨t, ht⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [Set.indicator_of_notMem ht])
  have hnn : ∀ x : T → Rn N, 0 ≤ ∏ t, (s t).indicator (fluctDensity N p) (x t) := fun x =>
    Finset.prod_nonneg fun t _ =>
      Set.indicator_nonneg (fun y _ => fluctDensity_nonneg N p y) _
  have hint : Integrable (fun x : T → Rn N => ∏ t, (s t).indicator (fluctDensity N p) (x t)) := by
    have := Integrable.fintype_prod (𝕜 := ℝ) (μ := fun _ : T => (volume : Measure (Rn N)))
      (f := fun t => (s t).indicator (fluctDensity N p)) fun t =>
        integrable_fluctDensity_indicator p (s t) (hs t)
    simpa [volume_pi] using this
  have key : ∫⁻ x in Set.pi univ s, ENNReal.ofReal (∏ t, fluctDensity N p (x t)) =
      ENNReal.ofReal (∏ t, ∫ y in s t, fluctDensity N p y) := by
    rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
    have : ∀ x : T → Rn N, (Set.pi univ s).indicator
        (fun x => ENNReal.ofReal (∏ t, fluctDensity N p (x t))) x =
        ENNReal.ofReal (∏ t, (s t).indicator (fluctDensity N p) (x t)) := by
      intro x
      rw [← hind x]
      by_cases hx : x ∈ Set.pi univ s
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [this]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)]
    congr 1
    have := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ)
      (E := fun _ : T => Rn N) (fun t => (s t).indicator (fluctDensity N p))
    rw [this]
    refine Finset.prod_congr rfl fun t _ => ?_
    exact integral_indicator (hs t)
  rw [key]
  have hs' : ∀ t, fluctMeasure1 N p (s t) =
      ENNReal.ofReal ((fluctNorm N p)⁻¹ * ∫ y in s t, fluctDensity N p y) := by
    intro t
    unfold fluctMeasure1
    rw [Measure.smul_apply, withDensity_apply _ (hs t), smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal ((integrable_fluctDensity N p).integrableOn)
        (ae_of_all _ fun y => fluctDensity_nonneg N p y)]
    by_cases hp : 0 ≤ (fluctNorm N p)⁻¹
    · rw [ENNReal.ofReal_mul hp]
    · exfalso
      refine hp ?_
      unfold fluctNorm
      exact inv_nonneg.2 (integral_nonneg fun y => fluctDensity_nonneg N p y)
  simp only [hs']
  rw [← ENNReal.ofReal_prod_of_nonneg, ← ENNReal.ofReal_mul]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  · exact pow_nonneg (inv_nonneg.2 (integral_nonneg fun y => fluctDensity_nonneg N p y)) _
  · intro t _
    exact mul_nonneg (inv_nonneg.2 (integral_nonneg fun y => fluctDensity_nonneg N p y))
      (integral_nonneg fun y => fluctDensity_nonneg N p y)

/-- Integrals against the product measure (2.5):
`∫ g dν_{p} = Z₁^{-|T|} ∫ χ_fl e^{-‖ψ̂‖²/2} g dψ̂`. -/
theorem integral_fluctMeasure (p : ℝ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (T → Rn N) → F) :
    ∫ x, g x ∂fluctMeasure T N p =
      ((fluctNorm N p)⁻¹ ^ Fintype.card T) •
        ∫ x, (chiFl T N p x * gaussWeight T N x) • g x := by
  have hZ : 0 ≤ (fluctNorm N p)⁻¹ ^ Fintype.card T :=
    pow_nonneg (inv_nonneg.2 (integral_nonneg fun y => fluctDensity_nonneg N p y)) _
  rw [fluctMeasure_eq_withDensity, integral_smul_measure, ENNReal.toReal_ofReal hZ,
    integral_withDensity_eq_integral_toReal_smul]
  · congr 2
    funext x
    rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun t _ => fluctDensity_nonneg N p _),
      prod_fluctDensity]
  · exact (measurable_prod_fluctDensity p).ennreal_ofReal
  · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

end ProductDensity

section Interp

variable {X : Type*} [MeasurableSpace X]

/-- **The interpolating measures** `dμ_{s,t} = Z_{s,t}^{-1} e^{W₁(s,·) + W₂(t,·)} dν` of (2.6),
for real exponents (`Z_{s,t}` is `partFunR₂ ν W₁ W₂ s t`). -/
noncomputable def interpMeasure (ν : Measure X) (W₁ W₂ : ℝ → X → ℝ) (s t : ℝ) : Measure X :=
  ENNReal.ofReal (partFunR₂ ν W₁ W₂ s t)⁻¹ •
    ν.withDensity (fun x => ENNReal.ofReal (Real.exp (W₁ s x + W₂ t x)))

theorem integral_interpMeasure (ν : Measure X) (W₁ W₂ : ℝ → X → ℝ) {s t : ℝ}
    (hZ : 0 < partFunR₂ ν W₁ W₂ s t) (hm : Measurable fun x => W₁ s x + W₂ t x) (f : X → ℝ) :
    ∫ x, f x ∂interpMeasure ν W₁ W₂ s t = avgFunR₂ ν W₁ W₂ f s t := by
  unfold interpMeasure avgFunR₂
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hZ.le),
    integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [div_eq_inv_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  · exact (Real.measurable_exp.comp hm).ennreal_ofReal
  · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

end Interp

section Core

variable {T : Type*} [Fintype T] {N : ℕ}

/-- **The abstract fluctuation integral** (the integral of Proposition 2.6 after the substitution
(2.7)).  If `f(ψ₀ + β^{-1/2} A ψ̂) = P χ_fl(ψ̂) e^{-‖ψ̂‖²/2} e^{W₁(1,ψ̂) + W₂(1,ψ̂)}` for all `ψ̂`,
with `C¹` families `W₁, W₂` vanishing at `0`, then
`∫ f = P β^{-N|T|/2} |det A| Z₁^{|T|} exp (∫₀¹ ⟨∂_s W₁⟩_{s,0} ds + ∫₀¹ ⟨∂_t W₂⟩_{1,t} dt)`. -/
theorem fluct_integral_eq (A : (T → Rn N) →ₗ[ℝ] (T → Rn N)) (hA : LinearMap.det A ≠ 0)
    {β : ℝ} (hβ : 0 < β) {p : ℝ} (hp : 0 < p) (ψ₀ : T → Rn N) (P : ℝ)
    (f : (T → Rn N) → ℝ) {W₁ W₁' W₂ W₂' : ℝ → (T → Rn N) → ℝ} {U : Set ℝ}
    (hf : ∀ x, f (ψ₀ + (β ^ (-(1 / 2 : ℝ))) • A x) =
      P * (chiFl T N p x * gaussWeight T N x) * Real.exp (W₁ 1 x + W₂ 1 x))
    (h₁ : IsC1FamilyR U W₁ W₁') (h₂ : IsC1FamilyR U W₂ W₂')
    (h0₁ : ∀ x, W₁ 0 x = 0) (h0₂ : ∀ x, W₂ 0 x = 0) :
    ∫ ψ, f ψ = P * (β ^ (-((N * Fintype.card T : ℕ) : ℝ) / 2) * |LinearMap.det A|) *
      (fluctNorm N p ^ Fintype.card T) *
      Real.exp ((∫ s in (0 : ℝ)..1,
          avgFunR₂ (fluctMeasure T N p) W₁ W₂ (W₁' s) s 0) +
        ∫ t in (0 : ℝ)..1, avgFunR₂ (fluctMeasure T N p) W₁ W₂ (W₂' t) 1 t) := by
  have := isProbabilityMeasure_fluctMeasure T N hp
  have hZ : 0 < fluctNorm N p := fluctNorm_pos N hp
  have h1 : (1 : ℝ) ∈ U := h₁.Icc_subset ⟨zero_le_one, le_rfl⟩
  have h0 : (0 : ℝ) ∈ U := h₁.Icc_subset ⟨le_rfl, zero_le_one⟩
  have e1 : ∫ ψ, f ψ = ∫ y, f (ψ₀ + y) := by
    rw [integral_add_left_eq_self (μ := (volume : Measure (T → Rn N))) f ψ₀]
  rw [e1, integral_eq_smul_integral_comp_smul_linearMap_pi T N A hA hβ (fun y => f (ψ₀ + y))]
  simp only [hf]
  have e2 : ∫ x, P * (chiFl T N p x * gaussWeight T N x) * Real.exp (W₁ 1 x + W₂ 1 x) =
      P * (fluctNorm N p ^ Fintype.card T * partFunR₂ (fluctMeasure T N p) W₁ W₂ 1 1) := by
    have := integral_fluctMeasure (T := T) (N := N) p (fun x => Real.exp (W₁ 1 x + W₂ 1 x))
    simp only [smul_eq_mul] at this
    have hc : fluctNorm N p ^ Fintype.card T * (fluctNorm N p)⁻¹ ^ Fintype.card T = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hZ.ne', one_pow]
    unfold partFunR₂
    have hI : ∫ x, (chiFl T N p x * gaussWeight T N x) * Real.exp (W₁ 1 x + W₂ 1 x) =
        fluctNorm N p ^ Fintype.card T *
          ∫ x, Real.exp (W₁ 1 x + W₂ 1 x) ∂fluctMeasure T N p := by
      calc _ = fluctNorm N p ^ Fintype.card T * ((fluctNorm N p)⁻¹ ^ Fintype.card T *
            ∫ x, (chiFl T N p x * gaussWeight T N x) * Real.exp (W₁ 1 x + W₂ 1 x)) := by
              rw [← mul_assoc, hc, one_mul]
        _ = _ := by rw [this]
    have : ∀ x : T → Rn N, P * (chiFl T N p x * gaussWeight T N x) * Real.exp (W₁ 1 x + W₂ 1 x) =
        P * ((chiFl T N p x * gaussWeight T N x) * Real.exp (W₁ 1 x + W₂ 1 x)) := fun x => by ring
    simp only [this]
    rw [integral_const_mul, hI]
  have hZ00 : partFunR₂ (fluctMeasure T N p) W₁ W₂ 0 0 = 1 := by
    unfold partFunR₂
    simp [h0₁, h0₂]
  have hlog := log_partFunR₂_one_one_sub (ν := fluctMeasure T N p) h₁ h₂
  rw [hZ00, Real.log_one, sub_zero] at hlog
  have hpos := partFunR₂_pos (ν := fluctMeasure T N p) h₁ h₂ h1 h1
  have hexp : partFunR₂ (fluctMeasure T N p) W₁ W₂ 1 1 = Real.exp
      ((∫ s in (0 : ℝ)..1, avgFunR₂ (fluctMeasure T N p) W₁ W₂ (W₁' s) s 0) +
        ∫ t in (0 : ℝ)..1, avgFunR₂ (fluctMeasure T N p) W₁ W₂ (W₂' t) 1 t) := by
    rw [← hlog, Real.exp_log hpos]
  rw [e2, hexp, smul_eq_mul]
  ring

end Core

section CoreComplex

variable {T : Type*} [Fintype T] {N : ℕ}

/-- **The abstract fluctuation integral, complex form.**  Same as `fluct_integral_eq` for complex
exponents; `Z_{s,0} ≠ 0` and `Z_{1,t} ≠ 0` (`s, t ∈ [0,1]`) are premises. -/
theorem fluct_integral_eq_complex (A : (T → Rn N) →ₗ[ℝ] (T → Rn N)) (hA : LinearMap.det A ≠ 0)
    {β : ℝ} (hβ : 0 < β) {p : ℝ} (hp : 0 < p) (ψ₀ : T → Rn N) (P : ℂ)
    (f : (T → Rn N) → ℂ) {W₁ W₁' W₂ W₂' : ℝ → (T → Rn N) → ℂ} {U : Set ℝ}
    (hf : ∀ x, f (ψ₀ + (β ^ (-(1 / 2 : ℝ))) • A x) =
      P * ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) * Complex.exp (W₁ 1 x + W₂ 1 x))
    (h₁ : IsC1Family U W₁ W₁') (h₂ : IsC1Family U W₂ W₂')
    (h0₁ : ∀ x, W₁ 0 x = 0) (h0₂ : ∀ x, W₂ 0 x = 0)
    (hZ₁ : ∀ s ∈ Icc (0 : ℝ) 1, partFun₂ (fluctMeasure T N p) W₁ W₂ s 0 ≠ 0)
    (hZ₂ : ∀ t ∈ Icc (0 : ℝ) 1, partFun₂ (fluctMeasure T N p) W₁ W₂ 1 t ≠ 0) :
    ∫ ψ, f ψ = P * ((β ^ (-((N * Fintype.card T : ℕ) : ℝ) / 2) * |LinearMap.det A| *
        fluctNorm N p ^ Fintype.card T : ℝ) : ℂ) *
      Complex.exp ((∫ s in (0 : ℝ)..1,
          avgFun₂ (fluctMeasure T N p) W₁ W₂ (W₁' s) s 0) +
        ∫ t in (0 : ℝ)..1, avgFun₂ (fluctMeasure T N p) W₁ W₂ (W₂' t) 1 t) := by
  have hprob := isProbabilityMeasure_fluctMeasure T N hp
  have hZ : 0 < fluctNorm N p := fluctNorm_pos N hp
  have e1 : ∫ ψ, f ψ = ∫ y, f (ψ₀ + y) := by
    rw [integral_add_left_eq_self (μ := (volume : Measure (T → Rn N))) f ψ₀]
  rw [e1, integral_eq_smul_integral_comp_smul_linearMap_pi T N A hA hβ (fun y => f (ψ₀ + y))]
  simp only [hf]
  have e2 : ∫ x, P * ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) *
        Complex.exp (W₁ 1 x + W₂ 1 x) =
      P * ((fluctNorm N p ^ Fintype.card T : ℝ) : ℂ) * partFun₂ (fluctMeasure T N p) W₁ W₂ 1 1 := by
    have := integral_fluctMeasure (T := T) (N := N) p (fun x => Complex.exp (W₁ 1 x + W₂ 1 x))
    have hc : fluctNorm N p ^ Fintype.card T * (fluctNorm N p)⁻¹ ^ Fintype.card T = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hZ.ne', one_pow]
    unfold partFun₂
    have hI : ∫ x, ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) *
          Complex.exp (W₁ 1 x + W₂ 1 x) =
        ((fluctNorm N p ^ Fintype.card T : ℝ) : ℂ) *
          ∫ x, Complex.exp (W₁ 1 x + W₂ 1 x) ∂fluctMeasure T N p := by
      rw [this]
      simp only [Complex.real_smul]
      rw [← mul_assoc, ← Complex.ofReal_mul, hc, Complex.ofReal_one, one_mul]
    have : ∀ x : T → Rn N, P * ((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) *
        Complex.exp (W₁ 1 x + W₂ 1 x) =
        P * (((chiFl T N p x * gaussWeight T N x : ℝ) : ℂ) * Complex.exp (W₁ 1 x + W₂ 1 x)) :=
      fun x => by ring
    simp only [this]
    rw [integral_const_mul, hI]
    ring
  have hZ00 : partFun₂ (fluctMeasure T N p) W₁ W₂ 0 0 = 1 := by
    unfold partFun₂
    simp [h0₁, h0₂]
  have hexp := partFun₂_one_one_eq (ν := fluctMeasure T N p) h₁ h₂ hZ₁ hZ₂
  rw [hZ00, one_mul] at hexp
  rw [e2, hexp, Complex.real_smul]
  push_cast
  ring

end CoreComplex

end Balaban.Fluctuation
