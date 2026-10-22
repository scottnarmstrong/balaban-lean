/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutEquiv
public import Balaban.LargeField.Base.BaseChartComponentNormalization

/-!
# The spins of a component from its fluctuation variables, and the chart Jacobian

LFR Definition II.7.6: on a component the spins are functions of the fluctuation variables `ψ'_0`
through the chart around the centre `e` and the substitution `u = β^{-1/2} R ψ'_0`, `R` the square
root of the component's Gaussian form (`gaussSqrtMap e H`).  With `v = tangentOp e (R ψ'_0)` the
tangent coordinate in the unit-`β` scale of the chart (`ChartIntegral`):

* `fluctSpinOf β e H ψ' = chartPoint β e v`, the spin configuration;
* `fluctJacOf β e H ψ' = chartJac β v = ∏_x 1[|v_x| < √β] (1 - |v_x|²/β)^{-1/2}`, the chart Jacobian
  of the kernel (the determinant of `R` and the normalization constants belong to `b₀`).

Both are total; `fluctJacOf` is nonnegative and Borel in `ψ'`, and both are `O(N)`-equivariant when
the centre is rotated and the Hamiltonian commutes with the rotation.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Matrix Balaban.Green MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The tangent coordinate `v = tangentOp e (R ψ')` of the fluctuation variable. -/
noncomputable def fluctTangent (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (ψ : Config ι N) : Config ι N :=
  tangentOp e (gaussSqrtMap e H ψ)

/-- The spins `e + β^{-1/2}(v + z(v))` of the component from its fluctuation variables. -/
noncomputable def fluctSpinOf (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (ψ : Config ι N) : Config ι N :=
  chartPoint β e (fluctTangent e H ψ)

/-- The chart Jacobian `∏_x 1[|v_x| < √β] (1 - |v_x|²/β)^{-1/2}` of the kernel. -/
noncomputable def fluctJacOf (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (ψ : Config ι N) : ℝ :=
  chartJac β (fluctTangent e H ψ)

theorem fluctJacOf_nonneg (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (ψ : Config ι N) : 0 ≤ fluctJacOf β e H ψ :=
  chartJac_nonneg β _

theorem measurable_fluctTangent (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N) :
    Measurable (fluctTangent e H) := by
  unfold fluctTangent gaussSqrtMap
  refine (tangentOp e).continuous_of_finiteDimensional.measurable.comp ?_
  exact ((configBasis ι N).equivFun.symm.toLinearMap.continuous_of_finiteDimensional.measurable).comp
    ((Measurable.comp (g := fun v => matAct _ v) (measurable_matAct.comp
      (measurable_const.prodMk measurable_id)) ((configBasis ι N).equivFun.toLinearMap.continuous_of_finiteDimensional.measurable)))

theorem measurable_fluctJacOf (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N) :
    Measurable (fluctJacOf β e H) :=
  (measurable_chartJac β).comp (measurable_fluctTangent e H)


/-- The componentwise rotation `(R u)_x = ρ u_x` of a configuration. -/
noncomputable def rotConfig (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    Config ι N →ₗ[ℝ] Config ι N :=
  LinearMap.pi fun x => ρ.toLinearEquiv.toLinearMap ∘ₗ LinearMap.proj x

@[simp] theorem rotConfig_apply (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (u : Config ι N) (x : ι) : rotConfig ρ u x = ρ (u x) := rfl

theorem cinner_rotConfig (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (u v : Config ι N) : cinner (rotConfig ρ u) (rotConfig ρ v) = cinner u v := by
  simp [cinner]

theorem tangentOp_rot (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e u : Config ι N) :
    tangentOp (rotConfig ρ e) (rotConfig ρ u) = rotConfig ρ (tangentOp e u) := by
  funext x
  simp [tangentOp_apply, map_sub, map_smul]

theorem normalProj_rot (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e u : Config ι N) :
    normalProj (rotConfig ρ e) (rotConfig ρ u) = rotConfig ρ (normalProj e u) := by
  funext x
  simp [normalProj_apply, map_smul]

/-- The form `gaussForm` is equivariant when the Hamiltonian commutes with the rotation. -/
theorem gaussForm_rot (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u, H (rotConfig ρ u) = rotConfig ρ (H u)) (u : Config ι N) :
    gaussForm (rotConfig ρ e) H (rotConfig ρ u) = rotConfig ρ (gaussForm e H u) := by
  unfold gaussForm
  simp only [LinearMap.add_apply, LinearMap.comp_apply, tangentOp_rot, hH, normalProj_rot, map_add]

/-- The square-root map is `O(N)`-equivariant (centre rotated, Hamiltonian commuting). -/
theorem gaussSqrtMap_rot (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u, H (rotConfig ρ u) = rotConfig ρ (H u))
    (hK : (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)).PosDef)
    (u : Config ι N) :
    gaussSqrtMap (rotConfig ρ e) H (rotConfig ρ u) = rotConfig ρ (gaussSqrtMap e H u) :=
  gaussSqrtMap_equivariant e (rotConfig ρ e) H H (rotConfig ρ) (cinner_rotConfig ρ)
    (gaussForm_rot ρ e H hH) hK u

theorem fluctTangent_rot (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u, H (rotConfig ρ u) = rotConfig ρ (H u))
    (hK : (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)).PosDef)
    (u : Config ι N) :
    fluctTangent (rotConfig ρ e) H (rotConfig ρ u) = rotConfig ρ (fluctTangent e H u) := by
  unfold fluctTangent
  rw [gaussSqrtMap_rot ρ e H hH hK, tangentOp_rot]

/-- The chart Jacobian is invariant under the rotation. -/
theorem fluctJacOf_rot (β : ℝ) (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u, H (rotConfig ρ u) = rotConfig ρ (H u))
    (hK : (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)).PosDef)
    (u : Config ι N) :
    fluctJacOf β (rotConfig ρ e) H (rotConfig ρ u) = fluctJacOf β e H u := by
  unfold fluctJacOf
  rw [fluctTangent_rot ρ e H hH hK]
  unfold chartJac
  refine Finset.prod_congr rfl fun x _ => ?_
  simp

/-- The spins are equivariant. -/
theorem fluctSpinOf_rot (β : ℝ) (ρ : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u, H (rotConfig ρ u) = rotConfig ρ (H u))
    (hK : (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)).PosDef)
    (u : Config ι N) :
    fluctSpinOf β (rotConfig ρ e) H (rotConfig ρ u) = rotConfig ρ (fluctSpinOf β e H u) := by
  unfold fluctSpinOf
  rw [fluctTangent_rot ρ e H hH hK]
  funext x
  simp [chartPoint, chartShift, map_add, map_smul]

/-- **The spins lie on the sphere** where the Jacobian is nonzero: for a unit centre and a tangent
coordinate of norm below `√β`, `‖e + β^{-1/2}(v + z(v))‖ = 1`. -/
theorem norm_chartPoint_eq_one {β : ℝ} (hβ : 0 < β) {e v : EuclideanSpace ℝ (Fin N)}
    (he : ‖e‖ = 1) (hv : inner ℝ e v = 0) (hlt : ‖v‖ < Real.sqrt β) :
    ‖e + (Real.sqrt β)⁻¹ • (v + (Real.sqrt β * (Real.sqrt (1 - ‖v‖ ^ 2 / β) - 1)) • e)‖ = 1 := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsq : Real.sqrt β ^ 2 = β := Real.sq_sqrt hβ.le
  have h1 : ‖v‖ ^ 2 / β < 1 := by
    rw [div_lt_one hβ, ← hsq]
    exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  have hr : 0 ≤ 1 - ‖v‖ ^ 2 / β := by linarith
  set t := Real.sqrt (1 - ‖v‖ ^ 2 / β) with ht
  have ht2 : t ^ 2 = 1 - ‖v‖ ^ 2 / β := Real.sq_sqrt hr
  have hcomb : e + (Real.sqrt β)⁻¹ • (v + (Real.sqrt β * (t - 1)) • e) =
      t • e + (Real.sqrt β)⁻¹ • v := by
    have : (Real.sqrt β)⁻¹ * (Real.sqrt β * (t - 1)) = t - 1 := by field_simp
    simp only [smul_add, smul_smul, this]
    module
  rw [hcomb]
  have hn : ‖t • e + (Real.sqrt β)⁻¹ • v‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, he, hv, real_inner_comm e v, RCLike.conj_to_real]
    have : (Real.sqrt β)⁻¹ ^ 2 * ‖v‖ ^ 2 = ‖v‖ ^ 2 / β := by
      rw [inv_pow, hsq]; ring
    nlinarith [this, ht2]
  have : 0 ≤ ‖t • e + (Real.sqrt β)⁻¹ • v‖ := norm_nonneg _
  nlinarith [hn]

end Balaban.LargeField
