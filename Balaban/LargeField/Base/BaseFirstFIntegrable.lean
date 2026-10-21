/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteConfig
public import Balaban.LargeField.Base.BaseChartComponentNormalization
public import Balaban.LargeField.Base.BaseChartIntegrability

/-!
# Integrability of the first-sector chart integrand against the tangent Gaussian

The first-sector chart integrand `F = baseSectorF` is the chart Jacobian `J_β(w)` (an integrable
singularity at the boundary of the tangent balls) times a function bounded on the balls
`|w_x| < √β`. Together with `e^{-½⟨w, Hw⟩} ≤ 1` on the tangent space, this gives integrability of
`e^{-½⟨w, Hw⟩} F(w)` for the product Lebesgue measure on the tangent hyperplanes
(`integrable_gaussian_mul_baseSectorF`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

section Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- On the tangent space the Hessian quadratic form of a positive definite chart form is
nonnegative. -/
theorem cinner_hessian_nonneg_of_perp (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N)
    (hK : (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)).PosDef)
    (v : (x : ι) → perp (e x)) :
    0 ≤ cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
      (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))) := by
  set w : Config ι N := fun x => (v x : EuclideanSpace ℝ (Fin N)) with hw
  have hperp : ∀ x, inner ℝ (e x) (w x) = 0 := fun x => inner_eq_of_mem_perp (e x) (v x).2
  have hQ : tangentOp e w = w := by
    funext x
    rw [tangentOp_apply, hperp x]
    simp
  have h1 := cinner_gaussForm e H w
  rw [hQ] at h1
  simp only [hperp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    add_zero] at h1
  rw [← h1, cinner_eq_repr_dot]
  have h2 : gaussForm e H = Matrix.toLin (configBasis ι N) (configBasis ι N)
      (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)) :=
    (Matrix.toLin_toMatrix _ _ _).symm
  rw [h2, repr_toLin]
  simpa using hK.posSemidef.dotProduct_mulVec_nonneg ((configBasis ι N).repr w)

end Gaussian

section Bound

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- **`F` is bounded by a constant times the chart Jacobian.** On the tangent balls
`|w_x| < √β` the exponent of the chart integrand is bounded (the shift `z` and `w` lie in the
compact ball of radius `√β`, and the mass term is bounded because the spins are unit vectors);
outside them the Jacobian vanishes. -/
theorem baseSectorF_norm_le {β : ℝ} (hβ : 0 < β) (a₀ ν : ℝ) (regimeB : Prop)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (e : Config (Torus d (L * n)) N)
    (he : ∀ x, ‖e x‖ = 1)
    (Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N)
    (χ : CfgT d N L n → ℝ) (hχ : ∀ φ, |χ φ| ≤ 1) (κ : ℂ) :
    ∃ C : ℝ, ∀ v : (x : Torus d (L * n)) → perp (e x),
      ‖baseSectorF β a₀ ν regimeB h g θ e he Hα χ κ v‖ ≤
        C * chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) := by
  classical
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  set K : Set (Config (Torus d (L * n)) N) := Metric.closedBall 0 (Real.sqrt β) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hHc : Continuous Hα := LinearMap.continuous_of_finiteDimensional Hα
  let Sf : Config (Torus d (L * n)) N × Config (Torus d (L * n)) N → ℂ := fun p =>
    ∑ x, ∑ i, g x i * (((p.1 x + p.2 x) i : ℝ) : ℂ)
  let Rf : Config (Torus d (L * n)) N × Config (Torus d (L * n)) N → ℝ := fun p =>
    cinner p.1 (Hα p.2) + (1 / 2) * cinner p.2 (Hα p.2)
  have hSf : Continuous Sf := by
    dsimp only [Sf]
    fun_prop
  have hRf : Continuous Rf := by
    dsimp only [Rf, cinner]
    fun_prop
  obtain ⟨CS, hCS⟩ := (hKc.prod hKc).exists_bound_of_continuousOn hSf.continuousOn
  obtain ⟨CR, hCR⟩ := (hKc.prod hKc).exists_bound_of_continuousOn hRf.continuousOn
  let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
  set T0 : ℂ := -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
      (∑ x : Torus d (L * n), ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) with hT0
  set M0 : ℝ := |β * (ν - (if regimeB then ν else 0)) / 2| *
    (Fintype.card (Torus d (L * n)) * (1 + ‖h‖) ^ 2) with hM0
  refine ⟨‖κ‖ * Real.exp (‖T0‖ + (Real.sqrt β)⁻¹ * CS + CR + M0), fun v => ?_⟩
  by_cases hv : ∀ x, ‖v x‖ < Real.sqrt β
  swap
  · obtain ⟨x, hx⟩ := not_forall.mp hv
    have hj : chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) = 0 :=
      chartJac_eq_zero (x₀ := x) hx
    simp [baseSectorF, hj]
  set w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N)) with hw
  set z := chartShift β e w with hz
  set φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v) with hφ
  have hJ : 0 ≤ chartJac β w :=
    Finset.prod_nonneg fun x _ => by
      split_ifs <;> positivity
  have hwK : w ∈ K := by
    rw [hK, mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hs.le).2 fun x => (hv x).le
  have hzK : z ∈ K := by
    rw [hK, mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hs.le).2 fun x => ?_
    simp only [hz, chartShift, norm_smul, he x, mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos hs]
    have h0 : 0 ≤ Real.sqrt (1 - ‖w x‖ ^ 2 / β) := Real.sqrt_nonneg _
    have h1 : Real.sqrt (1 - ‖w x‖ ^ 2 / β) ≤ 1 := by
      rw [Real.sqrt_le_one]
      have : 0 ≤ ‖w x‖ ^ 2 / β := by positivity
      linarith
    have h2 : |Real.sqrt (1 - ‖w x‖ ^ 2 / β) - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [mul_le_mul_of_nonneg_left h2 hs.le]
  set M : ℝ := β * (ν - (if regimeB then ν else 0)) / 2 *
    ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 with hMdef
  have hM : |M| ≤ M0 := by
    rw [hMdef, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    calc ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
        ≤ ∑ _x : Torus d (L * n), (1 + ‖h‖) ^ 2 := Finset.sum_le_sum fun x _ => by
          have h1 : ‖(φ x : EuclideanSpace ℝ (Fin N))‖ = 1 := mem_sphere_zero_iff_norm.1 (φ x).2
          have : ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ≤ 1 + ‖h‖ :=
            (norm_sub_le _ _).trans (by rw [h1])
          exact pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = Fintype.card (Torus d (L * n)) * (1 + ‖h‖) ^ 2 := by simp
  have hSb : ‖Sf (w, z)‖ ≤ CS := hCS _ (Set.mk_mem_prod hwK hzK)
  have hRb : ‖Rf (w, z)‖ ≤ CR := hCR _ (Set.mk_mem_prod hwK hzK)
  have hE : ‖T0 + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Sf (w, z) - ((Rf (w, z) + M : ℝ) : ℂ)‖ ≤
      ‖T0‖ + (Real.sqrt β)⁻¹ * CS + CR + M0 := by
    have h1 : ‖(((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Sf (w, z)‖ ≤ (Real.sqrt β)⁻¹ * CS := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
      exact mul_le_mul_of_nonneg_left hSb (inv_nonneg.2 hs.le)
    have h2 : ‖((Rf (w, z) + M : ℝ) : ℂ)‖ ≤ CR + M0 := by
      rw [Complex.norm_real]
      exact (norm_add_le _ _).trans (add_le_add hRb hM)
    calc _ ≤ ‖T0 + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Sf (w, z)‖ + ‖((Rf (w, z) + M : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ (‖T0‖ + (Real.sqrt β)⁻¹ * CS) + (CR + M0) :=
          add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl h1)) h2
      _ = _ := by ring
  have hF : baseSectorF β a₀ ν regimeB h g θ e he Hα χ κ v =
      ((chartJac β w : ℝ) : ℂ) * (((χ φ : ℝ) : ℂ) * κ *
        Complex.exp (T0 + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Sf (w, z) - ((Rf (w, z) + M : ℝ) : ℂ))) := by
    unfold baseSectorF
    simp only [T0, Sf, Rf, M]
    refine congrArg _ (congrArg _ (congrArg _ ?_))
    push_cast
    ring
  rw [hF, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hJ, Real.norm_eq_abs]
  have hexp : ‖Complex.exp (T0 + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Sf (w, z) -
      ((Rf (w, z) + M : ℝ) : ℂ))‖ ≤ Real.exp (‖T0‖ + (Real.sqrt β)⁻¹ * CS + CR + M0) :=
    (Complex.norm_exp _).trans_le (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans hE))
  have hk : 0 ≤ ‖κ‖ := norm_nonneg _
  calc chartJac β w * (|χ φ| * ‖κ‖ * ‖Complex.exp (T0 + (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Sf (w, z) -
        ((Rf (w, z) + M : ℝ) : ℂ))‖)
      ≤ chartJac β w * (1 * ‖κ‖ * Real.exp (‖T0‖ + (Real.sqrt β)⁻¹ * CS + CR + M0)) := by
        refine mul_le_mul_of_nonneg_left ?_ hJ
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hχ φ) hk) hexp (norm_nonneg _)
          (by positivity)
    _ = _ := by ring

omit [NeZero L] [NeZero n] in
theorem measurable_tangent_gaussian_weight {ι : Type*} [Fintype ι] {N : ℕ} (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N) :
    Measurable fun v : (x : ι) → perp (e x) => Real.exp (-(1 / 2) * cinner
      (fun x => (v x : EuclideanSpace ℝ (Fin N))) (H (fun x => (v x : EuclideanSpace ℝ (Fin N))))) := by
  have hc : Continuous H := LinearMap.continuous_of_finiteDimensional H
  have hv : Measurable fun v : (x : ι) → perp (e x) =>
      (fun x => (v x : EuclideanSpace ℝ (Fin N)) : Config ι N) :=
    measurable_pi_iff.2 fun x => measurable_subtype_coe.comp (measurable_pi_apply x)
  dsimp [cinner]
  fun_prop

open Classical in
/-- **Integrability of the Gaussian-weighted chart integrand**: the integrand
`e^{-½⟨w, Hα w⟩} F(w)` of `baseSectorChartIntegral_eq_tangent` is integrable on the tangent
hyperplanes (product Lebesgue measure). -/
theorem integrable_gaussian_mul_baseSectorF
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let κ : ℂ := ((∏ _y : Torus d n,
      ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
        ((N : ℝ) / 2) : ℝ) : ℂ)
    let F := baseSectorF β a₀ ν regimeB h g θ e he Hα χ κ
    Integrable (fun v : (x : Torus d (L * n)) → perp (e x) =>
      (((Real.exp (-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (Hα (fun x => (v x : EuclideanSpace ℝ (Fin N)))))) : ℝ) : ℂ) * F v)
      (Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  intro G α e he Hα χ κ F
  have hK := baseSector_gaussForm_posDef_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1
    θ φ₀ hp
  dsimp only at hK
  have hχ : ∀ φ, |χ φ| ≤ 1 := fun φ => by
    show |baseSectorCubeProduct regimeB ν δ₀ h θ φ| ≤ 1
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ]
    exact baseSectorCutoff_abs_le_one ϱ regimeB ν δ₀ h θ φ
  obtain ⟨C, hC⟩ := baseSectorF_norm_le hβ a₀ ν regimeB h g θ e he Hα χ hχ κ
  have hJac : Integrable (fun v : (x : Torus d (L * n)) → perp (e x) =>
      chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))))
      (Measure.pi fun x => (volume : Measure (perp (e x)))) := by
    have h1 := integrable_chartWeight_prod e he
    have h2 := (integrable_comp_smul_iff
      (Measure.pi fun x => (volume : Measure (perp (e x))))
      (fun ξ : (x : Torus d (L * n)) → perp (e x) => ∏ x, chartWeight (e x) (ξ x))
      (inv_ne_zero (Real.sqrt_pos.2 hβ).ne')).2 h1
    refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
    exact chartWeight_prod_inv_sqrt_eq_chartJac e hβ v
  have hq := measurable_tangent_gaussian_weight e Hα
  have hF : Measurable F := measurable_baseSectorF β a₀ ν regimeB h g θ e he Hα χ
    (measurable_baseSectorCubeProduct regimeB ν δ₀ h θ) κ
  refine (hJac.const_mul C).mono' ((Complex.measurable_ofReal.comp hq).mul hF).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have hq0 := cinner_hessian_nonneg_of_perp e Hα hK v
  have hG : Real.exp (-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
      (Hα (fun x => (v x : EuclideanSpace ℝ (Fin N))))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc _ ≤ 1 * ‖F v‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    _ ≤ C * chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) := by
      rw [one_mul]; exact hC v

end Bound

end Balaban.LargeField
