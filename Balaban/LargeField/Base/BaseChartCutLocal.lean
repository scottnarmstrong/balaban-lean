/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartGaussianNormalization
public import Balaban.LargeField.Base.BaseFRWhiteConfig
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The component square root as a Borel function of the form

The change of variables `ψ' ↦ R ψ'` of the first-step chart (P4 (2.47)-(2.54); LFR Definition II.7.6)
is `gaussSqrtMap e H`, the positive inverse square root `pdSqrtInv K` of the coordinate matrix `K`
of the Gaussian form `gaussForm e H`, acting on coordinates.  It is a total function; on the set
where `K` is positive definite it is the map `R` of `gaussForm_sqrt_equiv_of_posDef`
(`gaussForm_sqrt_equiv_of_posDef_apply`).  Here:

* `measurable_pdSqrtInv`: `K ↦ pdSqrtInv K` is Borel on all real matrices (the inverse is Borel as
  `det⁻¹ • adjugate`, and `CFC.sqrt` is Borel by `CFC.measurable_sqrt`);
* `measurable_sqrtApply`: `(K, ψ) ↦ R_K ψ` is Borel, where `R_K` is the coordinate action of
  `pdSqrtInv K`, so `gaussSqrtMap` is Borel in any measurable family of forms.
-/

@[expose] public section

namespace Balaban.LargeField

open Matrix Balaban.Green MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

section Meas

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The inverse of a real matrix is a Borel function of the matrix. -/
theorem measurable_matrix_inv : Measurable (fun K : Matrix κ κ ℝ => K⁻¹) := by
  have : (fun K : Matrix κ κ ℝ => K⁻¹) = fun K => (K.det)⁻¹ • K.adjugate := by
    funext K; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

/-- `K ↦ pdSqrtInv K` is Borel. -/
theorem measurable_pdSqrtInv : Measurable (fun K : Matrix κ κ ℝ => pdSqrtInv K) :=
  CFC.measurable_sqrt.comp measurable_matrix_inv

end Meas

section Sqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The coordinate action of the matrix `pdSqrtInv K` on `Config ι N`. -/
noncomputable def sqrtApply (K : Matrix (Σ _ : ι, Fin N) (Σ _ : ι, Fin N) ℝ) (u : Config ι N) :
    Config ι N :=
  (configBasis ι N).equivFun.symm (matAct (pdSqrtInv K) ((configBasis ι N).equivFun u))

/-- `gaussSqrtMap` is `sqrtApply` of the coordinate matrix of the form. -/
theorem gaussSqrtMap_eq_sqrtApply (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (u : Config ι N) :
    gaussSqrtMap e H u = sqrtApply (LinearMap.toMatrix (configBasis ι N) (configBasis ι N)
      (gaussForm e H)) u := rfl

theorem measurable_matAct {κ : Type*} [Fintype κ] :
    Measurable (fun p : Matrix κ κ ℝ × (κ → ℝ) => matAct p.1 p.2) := by
  refine measurable_pi_iff.2 fun x => ?_
  unfold matAct
  refine Finset.measurable_fun_sum _ fun y _ => ?_
  simp only [smul_eq_mul]
  exact ((measurable_pi_apply y).comp (measurable_pi_apply x |>.comp measurable_fst)).mul
    ((measurable_pi_apply y).comp measurable_snd)

/-- `(K, u) ↦ sqrtApply K u` is Borel. -/
theorem measurable_sqrtApply :
    Measurable (fun p : Matrix (Σ _ : ι, Fin N) (Σ _ : ι, Fin N) ℝ × Config ι N =>
      sqrtApply p.1 p.2) := by
  unfold sqrtApply
  have h1 : Measurable (fun p : Matrix (Σ _ : ι, Fin N) (Σ _ : ι, Fin N) ℝ × Config ι N =>
      ((pdSqrtInv p.1, (configBasis ι N).equivFun p.2) :
        Matrix (Σ _ : ι, Fin N) (Σ _ : ι, Fin N) ℝ × ((Σ _ : ι, Fin N) → ℝ))) :=
    (measurable_pdSqrtInv.comp measurable_fst).prodMk
      ((configBasis ι N).equivFun.toLinearMap.continuous_of_finiteDimensional.measurable.comp
        measurable_snd)
  exact ((configBasis ι N).equivFun.symm.toLinearMap.continuous_of_finiteDimensional.measurable).comp
    (measurable_matAct.comp h1)

end Sqrt

end Balaban.LargeField
