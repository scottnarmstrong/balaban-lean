module

public import Balaban.Gaussian.Integral
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The normalized Gaussian measure on `ι → ℝ`

For a real symmetric positive definite `A`, `Balaban.gaussianMeasure A` is the probability measure
`Z⁻¹ exp(-½ φᵀAφ) dφ` with `Z = (2π)^{n/2} (det A)^{-1/2}` (covariance `A⁻¹`), defined by its
density. Results: it is a probability measure (`gaussianMeasure_univ`); its image under
`WithLp.toLp` is Mathlib's `multivariateGaussian 0 A⁻¹` (`map_gaussianMeasure_eq`, via the
characteristic function computed from `integral_cexp_quadratic_form`); its moments of order at
most two are `0`, `0` and `A⁻¹ i j` (`integral_coord_gaussianMeasure`,
`integral_coord_mul_gaussianMeasure`).
-/

@[expose] public section

namespace Balaban

open Matrix MeasureTheory ProbabilityTheory Complex
open scoped MatrixOrder Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- normalization -/
noncomputable def gaussianNormalization (A : Matrix ι ι ℝ) : ℝ :=
  (2 * π) ^ ((Fintype.card ι : ℝ) / 2) / Real.sqrt A.det

noncomputable def gaussianWeight (A : Matrix ι ι ℝ) (φ : ι → ℝ) : ℝ :=
  Real.exp (-(1 / 2) * (φ ⬝ᵥ A *ᵥ φ))

theorem integral_cexp_quadratic_form' (A : Matrix ι ι ℝ) (hA : A.PosDef) (J : ι → ℂ) :
    ∫ φ : ι → ℝ, cexp (-(1 / 2 : ℂ) * ((φ ⬝ᵥ A *ᵥ φ : ℝ) : ℂ) + ∑ i, J i * (φ i : ℂ))
      = (gaussianNormalization A : ℂ) * cexp ((1 / 2 : ℂ) * ∑ i, ∑ j, J i * ((A⁻¹ i j : ℝ) : ℂ) * J j) := by
  rw [integral_cexp_quadratic_form A hA J, gaussianNormalization]
  have hdpos : 0 < A.det := hA.det_pos
  have : ((2 * π : ℂ) ^ ((Fintype.card ι : ℂ) / 2)) = (((2 * π) ^ ((Fintype.card ι : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  rw [this]
  push_cast
  ring

theorem gaussianNormalization_pos (A : Matrix ι ι ℝ) (hA : A.PosDef) : 0 < gaussianNormalization A := by
  have := hA.det_pos
  unfold gaussianNormalization; positivity

theorem integrable_gaussianWeight (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Integrable (gaussianWeight A) := by
  have h := integral_cexp_quadratic_form' A hA 0
  have hne : (∫ φ : ι → ℝ, cexp (-(1 / 2 : ℂ) * ((φ ⬝ᵥ A *ᵥ φ : ℝ) : ℂ) + ∑ i, (0 : ι → ℂ) i * (φ i : ℂ))) ≠ 0 := by
    rw [h]; simp
    exact (gaussianNormalization_pos A hA).ne'
  have hint := Integrable.of_integral_ne_zero hne
  have : Integrable (fun φ : ι → ℝ => ((gaussianWeight A φ : ℝ) : ℂ)) := by
    refine hint.congr (Filter.Eventually.of_forall fun φ => ?_)
    simp [gaussianWeight, Complex.ofReal_exp]
  exact this.re.congr (by filter_upwards with φ; simp)

/-- The normalized Gaussian measure `Z⁻¹ exp(-½⟨φ, Aφ⟩) dφ` (covariance `A⁻¹`). -/
noncomputable def gaussianMeasure (A : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  ENNReal.ofReal (gaussianNormalization A)⁻¹ •
    volume.withDensity fun φ => ENNReal.ofReal (gaussianWeight A φ)

theorem integral_gaussianMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (F : (ι → ℝ) → E) :
    ∫ φ, F φ ∂(gaussianMeasure A) = (gaussianNormalization A)⁻¹ • ∫ φ, gaussianWeight A φ • F φ := by
  have hZ := gaussianNormalization_pos A hA
  have hm : Measurable (gaussianWeight A) := by
    unfold gaussianWeight; fun_prop
  unfold gaussianMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (inv_nonneg.mpr hZ.le)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, gaussianWeight]

theorem integral_gaussianWeight (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    ∫ φ, gaussianWeight A φ = gaussianNormalization A := by
  have h := integral_cexp_quadratic_form' A hA 0
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, mul_zero,
    Complex.exp_zero, mul_one] at h
  have h2 : (∫ φ : ι → ℝ, ((gaussianWeight A φ : ℝ) : ℂ)) = (gaussianNormalization A : ℂ) := by
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp [gaussianWeight, Complex.ofReal_exp]
  rw [integral_complex_ofReal] at h2
  exact_mod_cast h2

theorem gaussianMeasure_univ (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    gaussianMeasure A Set.univ = 1 := by
  have hZ := gaussianNormalization_pos A hA
  have h := integral_gaussianMeasure A hA (fun _ => (1 : ℝ))
  simp only [smul_eq_mul, mul_one, integral_gaussianWeight A hA, integral_const, inv_mul_cancel₀ hZ.ne'] at h
  have hfin : gaussianMeasure A Set.univ ≠ ⊤ := by
    intro ht
    simp [Measure.real, ht] at h
  have := (ENNReal.toReal_eq_one_iff _).mp (by simpa [Measure.real] using h)
  exact this

theorem isProbabilityMeasure_gaussianMeasure (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    IsProbabilityMeasure (gaussianMeasure A) := ⟨gaussianMeasure_univ A hA⟩

theorem charFun_map_gaussianMeasure (A : Matrix ι ι ℝ) (hA : A.PosDef) (t : EuclideanSpace ℝ ι) :
    charFun ((gaussianMeasure A).map (WithLp.toLp 2)) t =
      Complex.exp (-((t.ofLp ⬝ᵥ A⁻¹ *ᵥ t.ofLp : ℝ) : ℂ) / 2) := by
  have hZ := gaussianNormalization_pos A hA
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), integral_gaussianMeasure A hA]
  have hJ := integral_cexp_quadratic_form' A hA (fun i => Complex.I * (t i : ℂ))
  have e : ∀ φ : ι → ℝ, gaussianWeight A φ • Complex.exp ((inner ℝ (WithLp.toLp 2 φ) t : ℝ) * Complex.I)
      = Complex.exp (-(1 / 2 : ℂ) * ((φ ⬝ᵥ A *ᵥ φ : ℝ) : ℂ) + ∑ i, (Complex.I * (t i : ℂ)) * (φ i : ℂ)) := by
    intro φ
    rw [Complex.real_smul, gaussianWeight, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    push_cast
    rw [Finset.sum_mul]
    simp only [mul_comm, mul_left_comm]
  simp_rw [e]
  rw [hJ, Complex.real_smul]
  have hne : (gaussianNormalization A : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hZ.ne']
  simp only [Complex.ofReal_one, one_mul]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := Complex.I_mul_I
  linear_combination (1 / 2 * (t.ofLp i : ℂ) * (A⁻¹ i j : ℂ) * (t.ofLp j : ℂ)) * this

theorem map_gaussianMeasure_eq (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    (gaussianMeasure A).map (WithLp.toLp 2) = multivariateGaussian 0 A⁻¹ := by
  have := isProbabilityMeasure_gaussianMeasure A hA
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_gaussianMeasure A hA, charFun_multivariateGaussian hA.inv.posSemidef]
  simp [neg_div]

theorem integral_coord_gaussianMeasure (A : Matrix ι ι ℝ) (hA : A.PosDef) (i : ι) :
    ∫ φ, φ i ∂(gaussianMeasure A) = 0 := by
  have h := congrArg (fun ν : Measure (EuclideanSpace ℝ ι) => ∫ x, x i ∂ν) (map_gaussianMeasure_eq A hA)
  simp only at h
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  rw [show (∫ φ : ι → ℝ, φ i ∂gaussianMeasure A) = ∫ φ : ι → ℝ, (WithLp.toLp 2 φ : EuclideanSpace ℝ ι) i ∂gaussianMeasure A from rfl, h]
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_id_comm
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) A⁻¹) IsGaussian.integrable_id
  rw [integral_id_multivariateGaussian] at h0
  simpa using h0

theorem integral_coord_mul_gaussianMeasure (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) :
    ∫ φ, φ i * φ j ∂(gaussianMeasure A) = A⁻¹ i j := by
  have hS := hA.inv.posSemidef
  have hc := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ ι)) hS i j
  have hmem : ∀ k : ι, MemLp (fun x : EuclideanSpace ℝ ι => x k) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) A⁻¹) := fun k => by
    exact (EuclideanSpace.proj (𝕜 := ℝ) k).comp_memLp' (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) A⁻¹))
  rw [covariance_eq_sub (hmem i) (hmem j)] at hc
  have h1 : ∀ k, ∫ x : EuclideanSpace ℝ ι, x k ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) A⁻¹) = 0 := by
    intro k
    have h := integral_coord_gaussianMeasure A hA k
    rw [← map_gaussianMeasure_eq A hA]
    rw [integral_map (by fun_prop) (by fun_prop)]
    exact h
  have h2 := congrArg (fun ν : Measure (EuclideanSpace ℝ ι) => ∫ x, x i * x j ∂ν) (map_gaussianMeasure_eq A hA)
  simp only at h2
  rw [integral_map (by fun_prop) (by fun_prop)] at h2
  rw [show (∫ φ : ι → ℝ, φ i * φ j ∂gaussianMeasure A) = ∫ φ : ι → ℝ, (WithLp.toLp 2 φ : EuclideanSpace ℝ ι) i * (WithLp.toLp 2 φ : EuclideanSpace ℝ ι) j ∂gaussianMeasure A from rfl, h2]
  simp only [Pi.mul_apply, h1] at hc
  linarith
end Balaban
