/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0GoodGaussian
public import Balaban.Green.FinalHessian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Linarith

/-!
# The Gaussian change of variables for a general positive definite matrix (package W403)

This file is linear algebra and measure theory only.  For a finite index type `ι`, a real symmetric
positive definite matrix `K` on `ι` and a finite-dimensional real inner product space `W`, it
proves

* `pdSqrtInv K := CFC.sqrt K⁻¹` (Mathlib's square root; no choice), with
  `pdSqrtInv_mul_self` (`C * C = K⁻¹`), `pdSqrtInv_mul_mul` (`C * K * C = 1`),
  `pdSqrtInv_det_sq`, `pdSqrtInv_det_pos`, `pdSqrtInv_det_pow`, positive definiteness,
  symmetry and uniqueness (`pdSqrtInv_unique`);
* `lintegral_pd_gaussian_change` (T2): for every `F ≥ 0`,
  `∫ F(v) exp(-½ Q_K(v)) dv = Z_K ∫ F(C ψ) dγ(ψ)` where `Q_K(v) = ∑_{x,y} K(x,y) ⟨v_x, v_y⟩`,
  `C = pdSqrtInv K`, `γ` the standard Gaussian on `ι → W` and
  `Z_K = (2π)^{n/2} det(K)^{-dim W / 2}`, `n = |ι| dim W`;
* `lintegral_pd_gaussian_change_shifted` (T3): with a linear term `⟨J, v⟩ = ∑_x ⟨J_x, v_x⟩`,
  `∫ F(v) exp(-½ Q_K(v) - ⟨J, v⟩) dv = exp(½ Q_{K⁻¹}(J)) Z_K ∫ F(C ψ - K⁻¹ J) dγ(ψ)`,
  with the vector-valued completed square `pdQuad_add_inv` for a general `K`;
* instances: the good-region matrix `kwOpSub` (the landed `lintegral_good_gaussian_change` is
  recovered) and the stopped Hessian `finalHessian`, under the hypothesis that it is positive
  definite.

The last-integral bridges (identification of the stopped Hessian with the Hessian of the physical
final density, and the like) are NOT proved here.  Nothing in this file depends on the generator.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped MatrixOrder

namespace Balaban.Green

open Balaban.LargeField SphereChart

section Sqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The positive definite square root of `K⁻¹`, from the continuous functional calculus. -/
noncomputable def pdSqrtInv (K : Matrix ι ι ℝ) : Matrix ι ι ℝ := CFC.sqrt K⁻¹

variable {K : Matrix ι ι ℝ}

theorem pdSqrtInv_posSemidef (K : Matrix ι ι ℝ) : (pdSqrtInv K).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

theorem pdSqrtInv_mul_self (hK : K.PosDef) : pdSqrtInv K * pdSqrtInv K = K⁻¹ :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hK.inv.posSemidef)

theorem pdSqrtInv_transpose (K : Matrix ι ι ℝ) : (pdSqrtInv K)ᵀ = pdSqrtInv K := by
  have := (pdSqrtInv_posSemidef K).isHermitian
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact this

theorem pdSqrtInv_det_sq (hK : K.PosDef) : (pdSqrtInv K).det ^ 2 = K.det⁻¹ := by
  have := congrArg Matrix.det (pdSqrtInv_mul_self hK)
  rw [Matrix.det_mul, Matrix.det_nonsing_inv] at this
  rw [sq, this]
  exact Ring.inverse_eq_inv _

theorem pdSqrtInv_posDef (hK : K.PosDef) : (pdSqrtInv K).PosDef := by
  have hdet : 0 < K.det⁻¹ := inv_pos.2 hK.det_pos
  have hne : (pdSqrtInv K).det ≠ 0 := by
    intro h0
    have := pdSqrtInv_det_sq hK
    rw [h0] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    rw [← this] at hdet
    exact lt_irrefl _ hdet
  exact (pdSqrtInv_posSemidef K).posDef_iff_isUnit.2
    ((Matrix.isUnit_iff_isUnit_det _).2 hne.isUnit)

theorem pdSqrtInv_det_pos (hK : K.PosDef) : 0 < (pdSqrtInv K).det := (pdSqrtInv_posDef hK).det_pos

theorem pdSqrtInv_mul_mul (hK : K.PosDef) : pdSqrtInv K * K * pdSqrtInv K = 1 := by
  have hKu : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 hK.isUnit
  have h1 : pdSqrtInv K * (pdSqrtInv K * K) = 1 := by
    rw [← Matrix.mul_assoc, pdSqrtInv_mul_self hK]
    exact Matrix.nonsing_inv_mul K hKu
  exact mul_eq_one_comm.1 h1

theorem pdSqrtInv_det_pow (hK : K.PosDef) (k : ℕ) :
    (pdSqrtInv K).det ^ k = K.det ^ (-(k : ℝ) / 2) := by
  have hKpos : 0 < K.det := hK.det_pos
  have hsq := pdSqrtInv_det_sq hK
  have hSpos := pdSqrtInv_det_pos hK
  have h1 : (pdSqrtInv K).det = K.det ^ (-(1 / 2 : ℝ)) := by
    have h2 : (K.det ^ (-(1 / 2 : ℝ))) ^ 2 = K.det⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
      norm_num
      exact Real.rpow_neg_one _
    have h3 : 0 < K.det ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hKpos _
    nlinarith [sq_nonneg ((pdSqrtInv K).det - K.det ^ (-(1 / 2 : ℝ))),
      sq_nonneg ((pdSqrtInv K).det + K.det ^ (-(1 / 2 : ℝ)))]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
  congr 1
  ring

/-- Uniqueness: a positive semidefinite square root of `K⁻¹` is `pdSqrtInv K`. -/
theorem pdSqrtInv_unique {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (hCC : C * C = K⁻¹) : C = pdSqrtInv K := by
  unfold pdSqrtInv
  exact (CFC.sqrt_unique (a := K⁻¹) (b := C) hCC (Matrix.nonneg_iff_posSemidef.mpr hC)).symm

end Sqrt

section Forms

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The bilinear form `∑_{x,y} M(x,y) ⟨u_x, w_y⟩` on `ι → W`. -/
noncomputable def pdBil (M : Matrix ι ι ℝ) (u w : ι → W) : ℝ :=
  ∑ x, ∑ y, M x y * inner ℝ (u x) (w y)

/-- The quadratic form `Q_K(v) = ∑_{x,y} K(x,y) ⟨v_x, v_y⟩`. -/
noncomputable def pdQuad (K : Matrix ι ι ℝ) (v : ι → W) : ℝ := pdBil K v v

/-- The linear form `⟨J, v⟩ = ∑_x ⟨J_x, v_x⟩`. -/
noncomputable def pdLin (J v : ι → W) : ℝ := ∑ x, inner ℝ (J x) (v x)

omit [DecidableEq ι] in
theorem pdBil_add_left (M : Matrix ι ι ℝ) (u u' w : ι → W) :
    pdBil M (u + u') w = pdBil M u w + pdBil M u' w := by
  simp [pdBil, inner_add_left, mul_add, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem pdBil_add_right (M : Matrix ι ι ℝ) (u w w' : ι → W) :
    pdBil M u (w + w') = pdBil M u w + pdBil M u w' := by
  simp [pdBil, inner_add_right, mul_add, Finset.sum_add_distrib]

theorem pdBil_one (u w : ι → W) : pdBil (1 : Matrix ι ι ℝ) u w = ∑ x, inner ℝ (u x) (w x) := by
  simp [pdBil, Matrix.one_apply]

omit [DecidableEq ι] in
theorem pdBil_comm {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (u w : ι → W) :
    pdBil M u w = pdBil M w u := by
  unfold pdBil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have : M y x = M x y := by
    have h := congrFun (congrFun hM x) y
    simpa using h
  rw [this, real_inner_comm]

omit [DecidableEq ι] in
theorem pdBil_matAct_right (M A : Matrix ι ι ℝ) (u w : ι → W) :
    pdBil M u (matAct A w) = pdBil (M * A) u w := by
  unfold pdBil matAct
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [inner_sum, inner_smul_right, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ => ?_
  ring

omit [DecidableEq ι] in
theorem sum_comm₃ (f : ι → ι → ι → ℝ) :
    ∑ x, ∑ y, ∑ a, f x y a = ∑ a, ∑ y, ∑ x, f x y a := by
  calc ∑ x, ∑ y, ∑ a, f x y a = ∑ y, ∑ x, ∑ a, f x y a := Finset.sum_comm
    _ = ∑ y, ∑ a, ∑ x, f x y a := Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ a, ∑ y, ∑ x, f x y a := Finset.sum_comm

omit [DecidableEq ι] in
theorem pdBil_matAct_left (M A : Matrix ι ι ℝ) (u w : ι → W) :
    pdBil M (matAct A u) w = pdBil (Aᵀ * M) u w := by
  unfold pdBil matAct
  simp only [sum_inner, inner_smul_left, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    Matrix.transpose_apply, conj_trivial]
  rw [sum_comm₃]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl
    fun x _ => ?_
  ring

/-- `⟨Sψ, K Sψ⟩ = ∑ ‖ψ_x‖²` when `Sᵀ K S = 1`. -/
theorem pdQuad_matAct {K S : Matrix ι ι ℝ} (hKS : Sᵀ * K * S = 1) (ψ : ι → W) :
    pdQuad K (matAct S ψ) = ∑ x, ‖ψ x‖ ^ 2 := by
  unfold pdQuad
  rw [pdBil_matAct_right, pdBil_matAct_left, ← Matrix.mul_assoc, hKS, pdBil_one]
  exact Finset.sum_congr rfl fun x _ => real_inner_self_eq_norm_sq _

/-- **Vector-valued completed square.**  For symmetric invertible `K` and
`w = K⁻¹ J`: `Q_K(v + w) = Q_K(v) + 2⟨J, v⟩ + Q_{K⁻¹}(J)`. -/
theorem pdQuad_add_inv {K : Matrix ι ι ℝ} (hKt : Kᵀ = K) (hKu : IsUnit K.det) (J v : ι → W) :
    pdQuad K (v + matAct K⁻¹ J) = pdQuad K v + 2 * pdLin J v + pdQuad K⁻¹ J := by
  set w := matAct K⁻¹ J with hw
  have hKi : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hKu
  have hKit : K⁻¹ᵀ = K⁻¹ := by rw [Matrix.transpose_nonsing_inv, hKt]
  have h1 : pdBil K v w = pdLin J v := by
    rw [hw, pdBil_matAct_right, hKi, pdBil_one]
    exact Finset.sum_congr rfl fun x _ => real_inner_comm _ _
  have h2 : pdBil K w v = pdLin J v := by rw [pdBil_comm hKt, h1]
  have h3 : pdBil K w w = pdQuad K⁻¹ J := by
    rw [hw]
    conv_lhs => rw [pdBil_matAct_right, hKi, pdBil_one]
    have : ∑ x, inner ℝ (matAct K⁻¹ J x) (J x) = pdBil 1 (matAct K⁻¹ J) J := (pdBil_one _ _).symm
    rw [this, pdBil_matAct_left, hKit, Matrix.mul_one]
    rfl
  unfold pdQuad
  rw [pdBil_add_left, pdBil_add_right, pdBil_add_right, h1, h2, h3]
  unfold pdQuad
  ring

end Forms

section Change

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

/-- The Lebesgue measure on fields `ι → W`. -/
noncomputable abbrev pdVol (ι W : Type*) [Fintype ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] : Measure (ι → W) :=
  Measure.pi fun _ => (volume : Measure W)

/-- The dimension `n = |ι| dim W`. -/
noncomputable abbrev pdDim (ι W : Type*) [Fintype ι] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] : ℕ := Fintype.card ι * Module.finrank ℝ W

/-- The standard Gaussian probability measure `(2π)^{-n/2} exp(-½ ∑_x ‖ψ_x‖²) dψ` on `ι → W`. -/
noncomputable def pdGaussian (ι W : Type*) [Fintype ι] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] : Measure (ι → W) :=
  (pdVol ι W).withDensity fun ψ =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(pdDim ι W : ℝ) / 2) *
      Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2))

/-- The normalizer `Z_K = (2π)^{n/2} det(K)^{-dim W / 2}`. -/
noncomputable def pdGaussNorm (ι W : Type*) [Fintype ι] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [DecidableEq ι] (K : Matrix ι ι ℝ) : ℝ :=
  (2 * Real.pi) ^ ((pdDim ι W : ℝ) / 2) * K.det ^ (-(Module.finrank ℝ W : ℝ) / 2)

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
theorem pdGaussNorm_pos {K : Matrix ι ι ℝ} (hK : K.PosDef) : 0 < pdGaussNorm ι W K :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hK.det_pos _)

theorem lintegral_gauss_space :
    ∫⁻ u : W, ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((Module.finrank ℝ W : ℝ) / 2)) := by
  have hI := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := W) (b := (1 / 2 : ℝ))
    (by norm_num)
  have hpos : (Real.pi / (1 / 2 : ℝ)) ^ ((Module.finrank ℝ W : ℝ) / 2) =
      (2 * Real.pi) ^ ((Module.finrank ℝ W : ℝ) / 2) := by
    congr 1; ring
  rw [hpos] at hI
  have hint : Integrable (fun u : W => Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hI]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => (Real.exp_pos _).le), hI]

omit [DecidableEq ι] in
theorem lintegral_gauss_field :
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : ι, ‖ψ x‖ ^ 2)) ∂(pdVol ι W) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((pdDim ι W : ℝ) / 2)) := by
  have e1 : ∀ ψ : ι → W,
      ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : ι, ‖ψ x‖ ^ 2)) =
        ∏ x : ι, ENNReal.ofReal (Real.exp (-(1 / 2) * ‖ψ x‖ ^ 2)) := by
    intro ψ
    rw [Finset.mul_sum, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le)]
  simp_rw [e1]
  have hmeas : Measurable fun u : W => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
  rw [PiTools.lintegral_fintype_prod_eq_prod ι
    (fun _ u => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2))) (fun _ => hmeas)]
  rw [Finset.prod_const, lintegral_gauss_space, Finset.card_univ, ← ENNReal.ofReal_pow
    (Real.rpow_nonneg (by positivity) _), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

omit [DecidableEq ι] in
/-- The Gaussian `pdGaussian ι W` is a probability measure. -/
theorem pdGaussian_univ : pdGaussian ι W Set.univ = 1 := by
  unfold pdGaussian
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hc : ∀ ψ : ι → W,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(pdDim ι W : ℝ) / 2) *
        Real.exp (-(1 / 2) * ∑ x : ι, ‖ψ x‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(pdDim ι W : ℝ) / 2)) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : ι, ‖ψ x‖ ^ 2)) := fun ψ =>
    ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gauss_field,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), ← Real.rpow_add (by positivity)]
  have : -(pdDim ι W : ℝ) / 2 + (pdDim ι W : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, ENNReal.ofReal_one]

theorem lintegral_matAct_pd {S : Matrix ι ι ℝ} (hS : IsUnit S.det) (f : (ι → W) → ENNReal) :
    ∫⁻ v, f v ∂(pdVol ι W) =
      ENNReal.ofReal |S.det ^ Module.finrank ℝ W| * ∫⁻ ψ, f (matAct S ψ) ∂(pdVol ι W) := by
  have := lintegral_eq_ofReal_abs_det_mul (pdVol ι W) (matActEquiv S hS) f
  rw [det_matActEquiv] at this
  exact this

/-- **The Gaussian change of variables** `v = C ψ`, `C = pdSqrtInv K` (T2): for a real
symmetric positive definite `K` on a finite index type and every `F ≥ 0`,
`∫ F(v) exp(-½ Q_K(v)) dv = Z_K ∫ F(Cψ) dγ(ψ)`. -/
theorem lintegral_pd_gaussian_change {K : Matrix ι ι ℝ} (hK : K.PosDef)
    (F : (ι → W) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)) ∂(pdVol ι W) =
      ENNReal.ofReal (pdGaussNorm ι W K) *
        ∫⁻ ψ, F (matAct (pdSqrtInv K) ψ) ∂(pdGaussian ι W) := by
  set S := pdSqrtInv K with hS
  have hSpos : 0 < S.det := pdSqrtInv_det_pos hK
  have hSu : IsUnit S.det := hSpos.ne'.isUnit
  rw [lintegral_matAct_pd hSu]
  have hq : ∀ ψ : ι → W,
      F (matAct S ψ) * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K (matAct S ψ))) =
      F (matAct S ψ) * ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) := by
    intro ψ
    rw [pdQuad_matAct]
    rw [hS, pdSqrtInv_transpose]
    exact pdSqrtInv_mul_mul hK
  simp_rw [hq]
  set c₀ : ℝ := (2 * Real.pi) ^ (-(pdDim ι W : ℝ) / 2) with hc₀
  have hc₀pos : 0 < c₀ := Real.rpow_pos_of_pos (by positivity) _
  have hγ : ∫⁻ ψ, F (matAct S ψ) ∂(pdGaussian ι W) =
      ENNReal.ofReal c₀ * ∫⁻ ψ, F (matAct S ψ) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) ∂(pdVol ι W) := by
    unfold pdGaussian
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ψ => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul hc₀pos.le]
      ring
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact ae_of_all _ fun ψ => ENNReal.ofReal_lt_top
  rw [hγ, ← mul_assoc, ← ENNReal.ofReal_mul (pdGaussNorm_pos hK).le]
  congr 2
  have h2 : (2 * Real.pi) ^ ((pdDim ι W : ℝ) / 2) * c₀ = 1 := by
    rw [hc₀, ← Real.rpow_add (by positivity)]
    have : (pdDim ι W : ℝ) / 2 + -(pdDim ι W : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [abs_of_pos (pow_pos hSpos _), hS, pdSqrtInv_det_pow hK, pdGaussNorm, mul_right_comm, h2,
    one_mul]

/-- **The shifted form** (T3).  For `J : ι → W`,
`∫ F(v) exp(-½ Q_K(v) - ⟨J, v⟩) dv = exp(½ Q_{K⁻¹}(J)) Z_K ∫ F(Cψ - K⁻¹J) dγ(ψ)`. -/
theorem lintegral_pd_gaussian_change_shifted {K : Matrix ι ι ℝ} (hK : K.PosDef) (J : ι → W)
    (F : (ι → W) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v - pdLin J v)) ∂(pdVol ι W) =
      ENNReal.ofReal (Real.exp ((1 / 2) * pdQuad K⁻¹ J)) * ENNReal.ofReal (pdGaussNorm ι W K) *
        ∫⁻ ψ, F (matAct (pdSqrtInv K) ψ - matAct K⁻¹ J) ∂(pdGaussian ι W) := by
  have hKt : Kᵀ = K := by
    have := hK.isHermitian
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact this
  have hKu : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 hK.isUnit
  set w := matAct K⁻¹ J with hw
  set c : ℝ := (1 / 2) * pdQuad K⁻¹ J with hc
  have e1 : ∀ v : ι → W, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v - pdLin J v)) =
      ENNReal.ofReal (Real.exp c) *
        ((fun u => F (u - w) * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K u))) (v + w)) := by
    intro v
    simp only [add_sub_cancel_right]
    rw [hw, pdQuad_add_inv hKt hKu J v, mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    congr 3
    rw [hc]; ring
  simp_rw [e1]
  have : (pdVol ι W).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_add_right_eq_self
    (fun u => F (u - w) * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K u))) w]
  rw [lintegral_pd_gaussian_change hK (fun u => F (u - w)), mul_assoc]

end Change

/-! ### Instances -/

section GoodRegion

variable {d m N : ℕ} [NeZero m]

/-- The square roots agree: `pdSqrtInv (kwOpSub …) = kwSqrt …`. -/
theorem pdSqrtInv_kwOpSub (ν : ℝ) (D : Finset (Torus d m)) :
    pdSqrtInv (kwOpSub d m ν D) = kwSqrt ν D := rfl

theorem goodQuad_eq_pdQuad {h : EuclideanSpace ℝ (Fin N)} (ν : ℝ) (D : Finset (Torus d m))
    (v : Good D → perp h) : goodQuad D ν v = pdQuad (kwOpSub d m ν D) v := by
  unfold goodQuad pdQuad pdBil
  simp only [dotProduct, Matrix.mulVec, Submodule.coe_inner, PiLp.inner_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem goodGaussian_eq_pdGaussian {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    (D : Finset (Torus d m)) : goodGaussian D h = pdGaussian (Good D) (perp h) := by
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  unfold goodGaussian pdGaussian
  simp only [pdDim, hr, goodDim]

theorem kwGaussNorm_eq_pdGaussNorm {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (ν : ℝ)
    (D : Finset (Torus d m)) : kwGaussNorm d m N ν D = pdGaussNorm (Good D) (perp h) (kwOpSub d m ν D) := by
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  unfold kwGaussNorm pdGaussNorm
  simp only [pdDim, hr, goodDim]

/-- **Consistency check (T4a).**  The landed `lintegral_good_gaussian_change` is the instance
`K = kwOpSub d m ν D`, `W = h^⊥` of `lintegral_pd_gaussian_change`. -/
theorem lintegral_good_gaussian_change_of_general {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    (D : Finset (Torus d m)) {ν : ℝ} (hν : 0 < ν) (F : (Good D → perp h) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * goodQuad D ν v)) ∂(goodVol D h) =
      ENNReal.ofReal (kwGaussNorm d m N ν D) *
        ∫⁻ ψ, F (matAct (kwSqrt ν D) ψ) ∂(goodGaussian D h) := by
  have := lintegral_pd_gaussian_change (W := perp h) (kwOpSub_posDef ν D hν) F
  simp only [← goodQuad_eq_pdQuad] at this
  rw [goodGaussian_eq_pdGaussian hh, kwGaussNorm_eq_pdGaussNorm hh]
  exact this

end GoodRegion

section FinalHessianCase

variable {d ℓ Nb m N : ℕ} [NeZero ℓ] [NeZero m]

theorem spinLift_transpose {ι κ : Type*} (A : Matrix ι κ ℝ) :
    (spinLift N A)ᵀ = spinLift N Aᵀ := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j <;> simp [spinLift, hij, eq_comm]

theorem blockPullbackMatrix_eq (hN : 0 < Nb) :
    blockPullbackMatrix d ℓ Nb m = ((Nb : ℝ) ^ d) • (unitBlockAverageMatrix d ℓ Nb m)ᵀ := by
  have hc : ((Nb : ℝ) ^ d) ≠ 0 := by positivity
  ext x y
  by_cases hxy : blockMap Nb m x = y <;>
    simp [blockPullbackMatrix, unitBlockAverageMatrix, hxy, hc]

theorem unconstrainedUnitOperator_transpose (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d)
    {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a) :
    (unconstrainedUnitOperator d ℓ Nb m ν a)ᵀ = unconstrainedUnitOperator d ℓ Nb m ν a := by
  have hG := (fineHamiltonian_posDef hℓ hN hd hν ha).isHermitian
  have hGt : (fineHamiltonian d ℓ Nb m ν a)⁻¹ᵀ = (fineHamiltonian d ℓ Nb m ν a)⁻¹ := by
    have hGt' : (fineHamiltonian d ℓ Nb m ν a)ᵀ = fineHamiltonian d ℓ Nb m ν a := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hG
    rw [Matrix.transpose_nonsing_inv, hGt']
  have hc : ((Nb : ℝ) ^ d) ≠ 0 := by positivity
  unfold unconstrainedUnitOperator
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.transpose_mul, hGt, blockPullbackMatrix_eq hN,
    Matrix.transpose_smul, Matrix.transpose_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

theorem finalHessian_transpose (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (finalHessian d ℓ Nb m ν a h)ᵀ = finalHessian d ℓ Nb m ν a h := by
  have hc := (spinLift_commute_projH (N := N) (unconstrainedUnitOperator d ℓ Nb m ν a) h).eq
  rw [finalHessian_eq_split hℓ hN hd hν ha hh, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, projH_transpose,
    spinLift_transpose, unconstrainedUnitOperator_transpose hℓ hN hd hν ha]
  congr 1
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hc]

/-- **Positive definiteness of the stopped Hessian** under the running hypotheses of the stopped
flow (`kStop > 0`, `ℓ = L^{k_f} m`, `|h| = 1`): symmetry (`finalHessian_transpose`) and the
landed coercive bound `finalHessian_gap_of_running`. -/
theorem finalHessian_posDef_of_running {L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (hrun : LargeField.RunningHyp d L β ν a ε b n) (hpos : 0 < LargeField.StopIndex.kStop hrun)
    (hℓ : ℓ = L ^ LargeField.StopIndex.kStop hrun * m) (hd : 0 < d) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) :
    (finalHessian d ℓ (L ^ LargeField.StopIndex.kStop hrun) m (n (LargeField.StopIndex.kStop hrun))
      a h).PosDef := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hrun.hL)
  have hN : 0 < L ^ LargeField.StopIndex.kStop hrun := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hrun.hL
    positivity
  have hv0 := LargeField.StopIndex.kStop_spec hrun
  have hvpos : 0 ≤ n (LargeField.StopIndex.kStop hrun) := by
    have : 0 < 7 / 8 * ((L : ℝ) ^ 2)⁻¹ := by positivity
    linarith
  have hsym := finalHessian_transpose hℓ hN hd hvpos (by linarith [hrun.ha1] : 0 < a) hh
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun u hu => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hsym
  · have hgap := finalHessian_gap_of_running hrun hpos hℓ hd hh u
    have huu : 0 < u ⬝ᵥ u := by
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hu
      refine lt_of_lt_of_le (mul_self_pos.2 hx) ?_
      exact Finset.single_le_sum (f := fun x => u x * u x) (fun _ _ => mul_self_nonneg _)
        (Finset.mem_univ x)
    have hcpos : 0 < 7 / (8 * (L : ℝ) ^ 2 * (8 * (d : ℝ) + 3)) := by positivity
    simpa using lt_of_lt_of_le (mul_pos hcpos huu) hgap

/-- **The Gaussian change of variables for the stopped Hessian** (T4b), for every finite-dimensional
real inner product space `W` (the fields are `Torus d m × Fin N → W`). -/
theorem lintegral_finalHessian_gaussian_change {L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (hrun : LargeField.RunningHyp d L β ν a ε b n) (hpos : 0 < LargeField.StopIndex.kStop hrun)
    (hℓ : ℓ = L ^ LargeField.StopIndex.kStop hrun * m) (hd : 0 < d) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    (F : (Torus d m × Fin N → W) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad
      (finalHessian d ℓ (L ^ LargeField.StopIndex.kStop hrun) m
        (n (LargeField.StopIndex.kStop hrun)) a h) v)) ∂(pdVol (Torus d m × Fin N) W) =
      ENNReal.ofReal (pdGaussNorm (Torus d m × Fin N) W
        (finalHessian d ℓ (L ^ LargeField.StopIndex.kStop hrun) m
          (n (LargeField.StopIndex.kStop hrun)) a h)) *
        ∫⁻ ψ, F (matAct (pdSqrtInv (finalHessian d ℓ (L ^ LargeField.StopIndex.kStop hrun) m
          (n (LargeField.StopIndex.kStop hrun)) a h)) ψ) ∂(pdGaussian (Torus d m × Fin N) W) :=
  lintegral_pd_gaussian_change (finalHessian_posDef_of_running hrun hpos hℓ hd hh) F

end FinalHessianCase

end Balaban.Green
