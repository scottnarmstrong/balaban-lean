/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastIntegral
public import Balaban.Green.FinalSpinCurry

/-!
# The Gaussian reduction of the small-field factor over a cut, at a whitening

A6-3 (a), first step (`notes/phase1/SPINE-PLAN.md`; P7 (4.3)-(4.7), P4 (6.4)-(6.6), P5 (2.39)). The
last integral of the small-field factor `sfFactor2 C vc Y` on a cut `Y` is an integral over the
fields `ψ_k` of the `k`-blocks. For every invertible real linear map `A` of `blocks × Fin N` (the
whitening; in the source `A = β_k^{-1/2} L`, `L` the localized square root of the covariance, P5
(2.39)) and every centre `ψ₀`, the change of variables `ψ = ψ₀ + A w` is exact:

`∫ f dψ = |det A| (2π)^{n/2} ∫ f(ψ₀ + A w) e^{|w|²/2} dγ(w)` (`integral_spin_whiten`,
from `integral_eq_abs_det_mul`).

For every form `Kq`, `e^{|w|²/2} = exp(½ Q_{Kq}(A w)) · exp(-½⟨w, (Aᵀ Kq A - 1) w⟩)`
(`exp_half_sq_eq_mul_mismatchFactor`): the first factor cancels the Gaussian part of the exponent of
`sfFactor2` (`sfGaussIntegrandL`), the second is the mismatch of the whitening (`mismatchFactor`), a
defined factor of the integrand (`integral_mul_sfFactor2_whiten`). At the exact whitening
`A = Kq^{-1/2}` the mismatch vanishes and the normalizer is `Z_{Kq}` (`integral_spin_gaussian`,
`integral_mul_sfFactor2_gauss`, `integral_sfFactor2_gauss` are the instances). The cut `Y` enters
only through the integrand; `Y = univ` is `sfIntegral` (`sfIntegral_eq_gauss`).
-/

@[expose] public section

open MeasureTheory Matrix Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green

namespace Balaban.RootFSpine

section Linear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Linear change of variables for the Bochner integral**: `∫ f = |det R| ∫ f ∘ R` for a linear
automorphism `R` and an additive Haar measure (no integrability hypothesis). -/
theorem integral_eq_abs_det_mul (μ : Measure X) [μ.IsAddHaarMeasure] (R : X ≃ₗ[ℝ] X)
    (f : X → ℂ) :
    ∫ y, f y ∂μ = ((|LinearMap.det (R : X →ₗ[ℝ] X)| : ℝ) : ℂ) * ∫ x, f (R x) ∂μ := by
  have hdet : LinearMap.det (R : X →ₗ[ℝ] X) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hemb : MeasurableEmbedding R :=
    (R.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have h1 : ∫ y, f y ∂(Measure.map (R : X →ₗ[ℝ] X) μ) = ∫ x, f (R x) ∂μ :=
    hemb.integral_map f
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h1
  rw [← h1, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← abs_mul,
    mul_inv_cancel₀ hdet, abs_one, Complex.ofReal_one, one_mul]

end Linear

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [DecidableEq ι] in
/-- **The standard Gaussian against Lebesgue measure**:
`∫ G e^{|w|²/2} dγ = (2π)^{-n/2} ∫ G dw`. -/
theorem integral_mul_exp_pdGaussian (G : (ι × Fin N → ℝ) → ℂ) :
    ∫ w, G w * ((Real.exp ((1 / 2) * ∑ p, ‖w p‖ ^ 2) : ℝ) : ℂ) ∂(pdGaussian (ι × Fin N) ℝ) =
      (((2 * Real.pi) ^ (-(pdDim (ι × Fin N) ℝ : ℝ) / 2) : ℝ) : ℂ) *
        ∫ w, G w ∂(volume : Measure (ι × Fin N → ℝ)) := by
  unfold pdGaussian
  rw [integral_withDensity_eq_integral_toReal_smul (Measurable.ennreal_ofReal (by fun_prop))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.exp_pos _).le), Complex.real_smul]
  have e : Real.exp (-(1 / 2) * ∑ x, ‖w x‖ ^ 2) * Real.exp ((1 / 2) * ∑ p, ‖w p‖ ^ 2) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc (((2 * Real.pi) ^ (-(pdDim (ι × Fin N) ℝ : ℝ) / 2) *
          Real.exp (-(1 / 2) * ∑ x, ‖w x‖ ^ 2) : ℝ) : ℂ) *
        (G w * ((Real.exp ((1 / 2) * ∑ p, ‖w p‖ ^ 2) : ℝ) : ℂ))
      = (((2 * Real.pi) ^ (-(pdDim (ι × Fin N) ℝ : ℝ) / 2) : ℝ) : ℂ) * G w *
          ((Real.exp (-(1 / 2) * ∑ x, ‖w x‖ ^ 2) * Real.exp ((1 / 2) * ∑ p, ‖w p‖ ^ 2) : ℝ) : ℂ) := by
        push_cast; ring
    _ = _ := by rw [e]; push_cast; ring

/-- The normalizer of the exact whitening `K^{-1/2}` is `Z_K`. -/
theorem whitenNorm_pdSqrtInv {K : Matrix (ι × Fin N) (ι × Fin N) ℝ}
    (hK : K.PosDef) : whitenNorm (pdSqrtInv K) = pdGaussNorm (ι × Fin N) ℝ K := by
  have h1 := pdSqrtInv_det_pow hK 1
  rw [pow_one] at h1
  rw [whitenNorm, abs_of_pos (pdSqrtInv_det_pos hK), h1, pdGaussNorm, Module.finrank_self,
    mul_comm]

/-- **The linear change of variables for fields of `N`-vectors** (the whitening `ψ = ψ₀ + A w`):
for `A` invertible on `ι × Fin N`, a centre `ψ₀` and every `f`,
`∫ f = |det A| (2π)^{n/2} ∫ f(ψ₀ + A w) e^{|w|²/2} dγ(w)` (no integrability hypothesis). -/
theorem integral_spin_whiten {A : Matrix (ι × Fin N) (ι × Fin N) ℝ} (hA : IsUnit A.det)
    (ψ0 : ι → EuclideanSpace ℝ (Fin N)) (f : (ι → EuclideanSpace ℝ (Fin N)) → ℂ) :
    ∫ ψ, f ψ = (whitenNorm A : ℂ) *
      ∫ w, f ((spinField ι N).symm (spinField ι N ψ0 + matAct A w)) *
        ((Real.exp ((1 / 2) * ∑ p, ‖w p‖ ^ 2) : ℝ) : ℂ) ∂(pdGaussian (ι × Fin N) ℝ) := by
  have h1 : ∫ ψ, f ψ = ∫ v : ι × Fin N → ℝ, f ((spinField ι N).symm v) := by
    have := integral_spinField ι N (fun v => f ((spinField ι N).symm v))
    simpa using this
  have h2 : ∫ v : ι × Fin N → ℝ, f ((spinField ι N).symm v) =
      ∫ v : ι × Fin N → ℝ, f ((spinField ι N).symm (spinField ι N ψ0 + v)) :=
    (integral_add_left_eq_self (μ := (volume : Measure (ι × Fin N → ℝ))) _ _).symm
  have h3 := integral_eq_abs_det_mul (volume : Measure (ι × Fin N → ℝ))
    (matActEquiv (W := ℝ) A hA) (fun v => f ((spinField ι N).symm (spinField ι N ψ0 + v)))
  rw [det_matActEquiv, Module.finrank_self, pow_one] at h3
  rw [h1, h2, h3, integral_mul_exp_pdGaussian, whitenNorm]
  have h2π : (2 * Real.pi) ^ ((pdDim (ι × Fin N) ℝ : ℝ) / 2) *
      (2 * Real.pi) ^ (-(pdDim (ι × Fin N) ℝ : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by positivity)]
    have : (pdDim (ι × Fin N) ℝ : ℝ) / 2 + -(pdDim (ι × Fin N) ℝ : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  have e : ∀ v, (matActEquiv (W := ℝ) A hA) v = matAct A v := fun v => rfl
  simp only [e]
  calc ((|A.det| : ℝ) : ℂ) * ∫ x, f ((spinField ι N).symm (spinField ι N ψ0 + matAct A x))
      = ((|A.det| : ℝ) : ℂ) * ((((2 * Real.pi) ^ ((pdDim (ι × Fin N) ℝ : ℝ) / 2) *
          (2 * Real.pi) ^ (-(pdDim (ι × Fin N) ℝ : ℝ) / 2) : ℝ) : ℂ) *
          ∫ x, f ((spinField ι N).symm (spinField ι N ψ0 + matAct A x))) := by
        rw [h2π]; push_cast; ring
    _ = _ := by push_cast; ring

/-- **The Gaussian reduction for fields of `N`-vectors** (the instance `A = K^{-1/2}` of
`integral_spin_whiten`): for `K` positive definite on `ι × Fin N` and a centre `ψ₀`,
`∫ f = Z_K ∫ f(ψ₀ + K^{-1/2} w) exp(½ Q_K(K^{-1/2} w)) dγ(w)`. -/
theorem integral_spin_gaussian {K : Matrix (ι × Fin N) (ι × Fin N) ℝ} (hK : K.PosDef)
    (ψ0 : ι → EuclideanSpace ℝ (Fin N)) (f : (ι → EuclideanSpace ℝ (Fin N)) → ℂ) :
    ∫ ψ, f ψ = (pdGaussNorm (ι × Fin N) ℝ K : ℂ) *
      ∫ w, f ((spinField ι N).symm (spinField ι N ψ0 + matAct (pdSqrtInv K) w)) *
        ((Real.exp ((1 / 2) * pdQuad K (matAct (pdSqrtInv K) w)) : ℝ) : ℂ)
        ∂(pdGaussian (ι × Fin N) ℝ) := by
  rw [integral_spin_whiten (pdSqrtInv_det_pos hK).ne'.isUnit ψ0 f, whitenNorm_pdSqrtInv hK]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [pdQuad_matAct (by rw [pdSqrtInv_transpose]; exact pdSqrtInv_mul_mul hK)]

/-- The quadratic form of a difference of matrices. -/
theorem pdQuad_sub {κ : Type*} [Fintype κ] (M M' : Matrix κ κ ℝ) (w : κ → ℝ) :
    pdQuad (M - M') w = pdQuad M w - pdQuad M' w := by
  simp [pdQuad, pdBil, sub_mul, Finset.sum_sub_distrib]

/-- **The mismatch identity**: `e^{|w|²/2} = exp(½ Q_{Kq}(A w)) · exp(-½⟨w, (Aᵀ Kq A - 1) w⟩)`. -/
theorem exp_half_sq_eq_mul_mismatchFactor {κ : Type*} [Fintype κ] [DecidableEq κ]
    (Kq A : Matrix κ κ ℝ) (w : κ → ℝ) :
    Real.exp ((1 / 2) * ∑ p, ‖w p‖ ^ 2) =
      Real.exp ((1 / 2) * pdQuad Kq (matAct A w)) * mismatchFactor Kq A w := by
  unfold mismatchFactor whitenMismatch
  rw [← Real.exp_add, pdQuad_sub]
  congr 1
  have h1 : pdQuad Kq (matAct A w) = pdQuad (Aᵀ * Kq * A) w := by
    unfold pdQuad
    rw [pdBil_matAct_right, pdBil_matAct_left, Matrix.mul_assoc]
  have h2 : pdQuad (1 : Matrix κ κ ℝ) w = ∑ p, ‖w p‖ ^ 2 := by
    unfold pdQuad
    rw [pdBil_one]
    exact Finset.sum_congr rfl fun x _ => real_inner_self_eq_norm_sq _
  rw [h1, h2]
  ring

/-- **The mismatch of the exact whitening vanishes**: `mismatchFactor Kq Kq^{-1/2} = 1`. -/
theorem mismatchFactor_pdSqrtInv {κ : Type*} [Fintype κ] [DecidableEq κ] {Kq : Matrix κ κ ℝ}
    (hK : Kq.PosDef) (w : κ → ℝ) : mismatchFactor Kq (pdSqrtInv Kq) w = 1 := by
  unfold mismatchFactor whitenMismatch
  rw [pdSqrtInv_transpose, pdSqrtInv_mul_mul hK, sub_self]
  simp [pdQuad, pdBil]

end Core

section Sf

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The reduction of the last integral over a cut `Y` at a whitening, with a weight** (A6-3 (a),
P7 (4.3)-(4.7), P5 (2.39)): for every invertible `A`, form `Kq`, centre `ψ₀` and weight `χ`,
`∫ χ(ψ) sfFactor2 C vc Y ψ dψ_k = |det A| (2π)^{n/2} ∫ χ(ψ₀ + A w) sfGaussIntegrandL(w)
mismatch(w) dγ(w)`, with the mismatch factor `exp(-½⟨w, (Aᵀ Kq A - 1) w⟩)` in the integrand. -/
theorem integral_mul_sfFactor2_whiten (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} (hA : IsUnit A.det)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (χ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℂ) :
    ∫ ψ, χ ψ * sfFactor2 C vc Y ψ hv g =
      (whitenNorm A : ℂ) *
        ∫ w, χ ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct A w)) *
          sfGaussIntegrandL C vc Y hv g Kq A ψ0 w * (mismatchFactor Kq A w : ℂ)
          ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
  rw [integral_spin_whiten hA ψ0 (fun ψ => χ ψ * sfFactor2 C vc Y ψ hv g)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  simp only [sfGaussIntegrandL]
  rw [exp_half_sq_eq_mul_mismatchFactor Kq A w]
  push_cast
  ring

/-- **The Gaussian reduction of the last integral over a cut `Y`, with a weight** (A6-3 (a),
P7 (4.3)-(4.7); the instance `A = Kq^{-1/2}` of `integral_mul_sfFactor2_whiten`): for every weight
`χ` of the fields `ψ_k`,
`∫ χ(ψ) sfFactor2 C vc Y ψ dψ_k = Z_K ∫ χ(ψ₀ + Kq^{-1/2} w) sfGaussIntegrand(w) dγ(w)`, for every
positive definite form `Kq` and centre `ψ₀`. -/
theorem integral_mul_sfFactor2_gauss (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    {Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} (hK : Kq.PosDef)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (χ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℂ) :
    ∫ ψ, χ ψ * sfFactor2 C vc Y ψ hv g =
      (pdGaussNorm (BlockAt S n M K k × Fin N) ℝ Kq : ℂ) *
        ∫ w, χ ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) *
          sfGaussIntegrand C vc Y hv g Kq ψ0 w ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
  rw [integral_mul_sfFactor2_whiten C vc Y hv g Kq (pdSqrtInv_det_pos hK).ne'.isUnit ψ0 χ,
    whitenNorm_pdSqrtInv hK]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  rw [mismatchFactor_pdSqrtInv hK]
  simp [sfGaussIntegrand]

/-- **The Gaussian reduction of the last integral over a cut `Y`** (A6-3 (a), P7 (4.3)-(4.7)):
`∫ sfFactor2 C vc Y dψ_k = Z_K ∫ sfGaussIntegrand dγ`, for every positive definite form `Kq`
and centre `ψ₀` (the weight `χ = 1` of `integral_mul_sfFactor2_gauss`). -/
theorem integral_sfFactor2_gauss (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    {Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} (hK : Kq.PosDef)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    ∫ ψ, sfFactor2 C vc Y ψ hv g =
      (pdGaussNorm (BlockAt S n M K k × Fin N) ℝ Kq : ℂ) *
        ∫ w, sfGaussIntegrand C vc Y hv g Kq ψ0 w ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
  simpa using integral_mul_sfFactor2_gauss C vc Y hv g hK ψ0 (fun _ => 1)

/-- **`Ξ^sf` as a Gaussian average** (the empty cut `Y = univ`). -/
theorem sfIntegral_eq_gauss {P : BudgetConsts} {cs : OpConsts} {k0 : ℕ}
    {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M}
    {P6 : Balaban.SmallField.Def6.Consts} {C7 : Consts7}
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ) (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK]
    (g : GIdx S (sides S.L K nK) M K N → ℂ)
    {Kq : Matrix (BlockAt S (sides S.L K nK) M K k × Fin N)
      (BlockAt S (sides S.L K nK) M K k × Fin N) ℝ} (hK : Kq.PosDef)
    (ψ0 : BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) :
    sfIntegral F hM6 hkK vc hv nK g =
      (pdGaussNorm (BlockAt S (sides S.L K nK) M K k × Fin N) ℝ Kq : ℂ) *
        ∫ w, sfGaussIntegrand (F.ctx hM6 hkK nK) vc Set.univ hv g Kq ψ0 w
          ∂(pdGaussian (BlockAt S (sides S.L K nK) M K k × Fin N) ℝ) :=
  integral_sfFactor2_gauss _ vc Set.univ hv g hK ψ0

end Sf

end Balaban.RootFSpine
