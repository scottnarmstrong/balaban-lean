module

public import Balaban.LargeField.Base.BaseComponentDeterminant
public import Balaban.LargeField.Base.ChartIntegral
public import Balaban.Green.GaussianChangeGeneral

/-!
# Real Gaussian square roots for the first chart

The real inverse square root of a positive Gaussian matrix supplies the
linear change of variables in the chart formula of P4 (2.47)–(2.50).
-/

@[expose] public section

namespace Balaban.LargeField

open Matrix Balaban.Green MeasureTheory SphereChart
open scoped ENNReal

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For a real positive definite Gaussian matrix, the positive inverse square
root is a symmetric linear equivalence. Its double application is the inverse
of the Gaussian matrix, and its determinant is the positive Gaussian
normalization factor. -/
theorem gaussian_real_sqrt_equiv (A : Matrix κ κ ℝ) (hA : A.PosDef) :
    ∃ R : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ),
      (∀ w, A *ᵥ (R (R w)) = w) ∧
      (∀ u v, (R u) ⬝ᵥ v = u ⬝ᵥ (R v)) ∧
      LinearMap.det (R : (κ → ℝ) →ₗ[ℝ] (κ → ℝ)) =
        Real.sqrt A.det⁻¹ := by
  let S := pdSqrtInv A
  have hSpos : 0 < S.det := pdSqrtInv_det_pos hA
  have hSu : IsUnit S.det := hSpos.ne'.isUnit
  let R : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ) := matActEquiv S hSu
  refine ⟨R, ?_, ?_, ?_⟩
  · intro w
    have hAS : A * (S * S) = 1 := by
      rw [pdSqrtInv_mul_self hA, Matrix.mul_nonsing_inv A]
      exact (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
    change matAct A (matAct S (matAct S w)) = w
    rw [matAct_mul, matAct_mul]
    rw [Matrix.mul_assoc]
    rw [hAS, matAct_one]
  · intro u v
    change (S *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (S *ᵥ v)
    have hSymm : S.IsSymm := pdSqrtInv_transpose A
    calc
      (S *ᵥ u) ⬝ᵥ v = v ⬝ᵥ (S *ᵥ u) := dotProduct_comm _ _
      _ = u ⬝ᵥ (S *ᵥ v) := hSymm.dotProduct_mulVec_comm
  · rw [det_matActEquiv (W := ℝ) S hSu]
    simp only [Module.finrank_self, pow_one]
    have hsq := pdSqrtInv_det_sq hA
    change S.det ^ 2 = A.det⁻¹ at hsq
    have hdet : 0 ≤ A.det⁻¹ := inv_nonneg.mpr hA.det_pos.le
    have hsqrt : 0 ≤ Real.sqrt A.det⁻¹ := Real.sqrt_nonneg _
    nlinarith only [hsq, Real.sq_sqrt hdet, hSpos, hsqrt]

/-- The real Gaussian form of P4 (2.47) has the square-root change of
variables required by the sphere-chart identity whenever its coordinate
matrix is positive definite. -/
theorem gaussForm_sqrt_equiv_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hK : (LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm e H)).PosDef) :
    ∃ R : Config ι N ≃ₗ[ℝ] Config ι N,
      (∀ w, gaussForm e H (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N) =
        Real.sqrt (LinearMap.det (gaussForm e H))⁻¹ := by
  classical
  let B := Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  let K := LinearMap.toMatrix B B (gaussForm e H)
  let E := B.equivFun
  have hcoord (u v : Config ι N) : cinner u v = (E u) ⬝ᵥ (E v) := by
    simp [cinner, E, B, dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      Finset.sum_sigma', mul_comm]
  have hmap (u : Config ι N) : E (gaussForm e H u) = K *ᵥ E u := by
    simpa [E, K] using (LinearMap.toMatrix_mulVec_repr B B (gaussForm e H) u).symm
  obtain ⟨T, hTT, hTs, hTd⟩ := gaussian_real_sqrt_equiv K hK
  let R : Config ι N ≃ₗ[ℝ] Config ι N := (E.trans T).trans E.symm
  refine ⟨R, ?_, ?_, ?_⟩
  · intro w
    apply E.injective
    rw [hmap]
    change K *ᵥ (T (T (E w))) = E w
    exact hTT (E w)
  · intro u v
    rw [hcoord, hcoord]
    change (T (E u)) ⬝ᵥ E v = E u ⬝ᵥ T (E v)
    exact hTs (E u) (E v)
  · have hdetR : LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N) =
        LinearMap.det (T : ((Σ _ : ι, Fin N) → ℝ) →ₗ[ℝ] ((Σ _ : ι, Fin N) → ℝ)) := by
      change LinearMap.det
        ((E.symm : ((Σ _ : ι, Fin N) → ℝ) →ₗ[ℝ] Config ι N) ∘ₗ
          (T : ((Σ _ : ι, Fin N) → ℝ) →ₗ[ℝ] ((Σ _ : ι, Fin N) → ℝ)) ∘ₗ
          (E : Config ι N →ₗ[ℝ] ((Σ _ : ι, Fin N) → ℝ))) = _
      exact LinearMap.det_conj _ E.symm
    rw [hdetR, hTd]
    congr 1
    congr 1
    exact LinearMap.det_toMatrix B (gaussForm e H)

/-- Gaussian lifting and the real square-root change of variables on the
tangent chart of P4 (2.47)–(2.50). The nonnegative factor is arbitrary. -/
theorem lintegral_tangent_gaussian_real {ι : Type*} [Fintype ι] {N : ℕ}
    (e : Config ι N) (he : ∀ x, ‖e x‖ = 1)
    (H : Config ι N →ₗ[ℝ] Config ι N)
    (R : Config ι N ≃ₗ[ℝ] Config ι N)
    (hR : ∀ ψ, cinner (R ψ) (gaussForm e H (R ψ)) = cinner ψ ψ)
    (g : ((x : ι) → perp (e x)) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ v, g v * ENNReal.ofReal (Real.exp (-(1 / 2) *
        cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
          (H (fun x => (v x : EuclideanSpace ℝ (Fin N))))))
      ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) =
      ENNReal.ofReal ((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card ι / 2) *
        |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)|) *
        ∫⁻ ψ, g (tangentProj e he (R ψ)) ∂(stdGaussian ι N) := by
  classical
  let G : Config ι N → ℝ≥0∞ := fun u =>
    g (tangentProj e he u) * ENNReal.ofReal
      (Real.exp (-(1 / 2) * cinner (tangentOp e u) (H (tangentOp e u))))
  have hG : Measurable G := by
    have ht : Measurable (tangentProj e he) := measurable_tangentProj e he
    have hc : Continuous H := LinearMap.continuous_of_finiteDimensional H
    have hq : Measurable fun u : Config ι N =>
        Real.exp (-(1 / 2) * cinner (tangentOp e u) (H (tangentOp e u))) := by
      unfold cinner
      fun_prop
    exact (hg.comp ht).mul (ENNReal.measurable_ofReal.comp hq)
  have hv : Measurable fun v : (x : ι) → perp (e x) =>
      (fun x => (v x : EuclideanSpace ℝ (Fin N)) : Config ι N) :=
    measurable_pi_iff.2 fun x => measurable_subtype_coe.comp (measurable_pi_apply x)
  have hL := lintegral_tangent_eq e he
    (fun v => g v * ENNReal.ofReal (Real.exp (-(1 / 2) *
      cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))))))
    ((hg.mul (ENNReal.measurable_ofReal.comp (by
      have hc : Continuous H := LinearMap.continuous_of_finiteDimensional H
      unfold cinner
      fun_prop))))
  have hnormal (u : Config ι N) :
      G u * ENNReal.ofReal (normalWeight e u) =
        g (tangentProj e he u) * ENNReal.ofReal
          (Real.exp (-(1 / 2) * cinner u (gaussForm e H u))) := by
    unfold G normalWeight
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      cinner_gaussForm e H u]
    congr 3
    ring
  have hchange := lintegral_eq_ofReal_abs_det_mul
    (volume : Measure (Config ι N)) R
    (fun u => g (tangentProj e he u) * ENNReal.ofReal
      (Real.exp (-(1 / 2) * cinner u (gaussForm e H u))))
  have hq (ψ : Config ι N) :
      cinner (R ψ) (gaussForm e H (R ψ)) = cinner ψ ψ := hR ψ
  simp_rw [hq] at hchange
  have hstd : ∫⁻ ψ, g (tangentProj e he (R ψ)) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * cinner ψ ψ)) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((N * Fintype.card ι : ℕ) / (2 : ℝ))) *
        ∫⁻ ψ, g (tangentProj e he (R ψ)) ∂(stdGaussian ι N) := by
    unfold stdGaussian
    have hm : Measurable fun ψ : Config ι N => g (tangentProj e he (R ψ)) :=
      hg.comp ((measurable_tangentProj e he).comp
        (LinearMap.continuous_of_finiteDimensional (R : Config ι N →ₗ[ℝ] Config ι N)).measurable)
    have hd : Measurable fun ψ : Config ι N => ENNReal.ofReal
        ((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
          Real.exp (-(1 / 2) * cinner ψ ψ)) := by
      refine ENNReal.measurable_ofReal.comp ?_
      unfold cinner
      fun_prop
    rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable hm.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ψ => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have hp : 0 < 2 * Real.pi := by positivity
    have hpow : (2 * Real.pi) ^ ((N * Fintype.card ι : ℕ) / (2 : ℝ)) *
        ((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
          Real.exp (-(1 / 2) * cinner ψ ψ)) =
        Real.exp (-(1 / 2) * cinner ψ ψ) := by
      rw [← mul_assoc, ← Real.rpow_add hp]
      have : ((N * Fintype.card ι : ℕ) : ℝ) / 2 +
          -((N * Fintype.card ι : ℕ) : ℝ) / 2 = 0 := by ring
      rw [this, Real.rpow_zero, one_mul]
    rw [hpow]
  rw [hL]
  simp_rw [coe_tangentProj e he]
  simp_rw [hnormal]
  rw [hchange, hstd]
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hp : 0 < 2 * Real.pi := by positivity
  rw [← Real.rpow_add hp]
  congr 1
  push_cast
  ring

end Balaban.LargeField
