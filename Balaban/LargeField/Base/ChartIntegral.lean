/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.HemispherePi

/-!
# The exact real chart identity of the base step (LF-BASE-KF0 (A.3); Lemma II.7.4 (a), (b))

Let `ι` be a finite set of sites, `e_x ∈ S^{N-1}` unit vectors, `P = ⊕ e_x e_xᵀ`, `Q = I - P`,
`H` a symmetric operator on `(ℝ^N)^ι` and `A_e = Q H Q + P` (`gaussForm`).  For a measurable
`F ≥ 0` supported in the product of the open hemispheres `{⟨e_x, φ_x⟩ > 0}`
(`lintegral_sphere_pi_eq_gaussian`):

`∫ F(φ) e^{-(β/2)⟨φ-e, H(φ-e)⟩} ∏ dσ(φ_x)`
`  = β^{-m/2} (2π)^{m/2} |det R| ∫ J_β(v) e^{-⟨v,Hz(v)⟩ - ½⟨z(v),Hz(v)⟩} F(e + β^{-1/2}(v+z(v))) dγ(ψ)`,

`m = (N-1)|ι|`, `v = Q R ψ`, `γ` the standard Gaussian on `(ℝ^N)^ι`, `R` a square-root factor of
`C_e = A_e^{-1}`, so `|det R| = (det C_e)^{1/2}`.  The proof chains: the product chart
(`lintegral_sphere_pi_hemisphere`), the rescaling `v = √β ξ` of the tangent integral, the Gaussian lift
of the tangent integral (`lintegral_tangent_eq`, Lemma II.7.4 (b)), and the linear change of
variables `u = R ψ`.  The exponent of the Boltzmann weight is the exactly quadratic action of
Lemma II.7.3 (`action_sub_eq_chord_quadratic`).
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace Balaban.LargeField

open SphereChart

universe u

noncomputable section

variable {ι : Type u} [Fintype ι] {N : ℕ}

variable {ι : Type u} {N : ℕ}

/-- The configuration space `(ℝ^N)^ι`. -/
abbrev Config (ι : Type u) (N : ℕ) := ι → EuclideanSpace ℝ (Fin N)

/-- The projection `P u = (⟨e_x, u_x⟩ e_x)_x` onto the normal directions. -/
def normalProj (e : ι → EuclideanSpace ℝ (Fin N)) : Config ι N →ₗ[ℝ] Config ι N where
  toFun u := fun x => inner ℝ (e x) (u x) • e x
  map_add' u v := by funext x; simp [inner_add_right, add_smul]
  map_smul' c u := by funext x; simp [inner_smul_right, smul_smul]

/-- The projection `Q = I - P` onto the tangent directions `e_x^⊥`. -/
def tangentOp (e : ι → EuclideanSpace ℝ (Fin N)) : Config ι N →ₗ[ℝ] Config ι N :=
  LinearMap.id - normalProj e

/-- The operator `A_e = Q H Q + P` (LF-BASE-KF0 §A.1), whose inverse is the covariance `C_e`. -/
def gaussForm (e : ι → EuclideanSpace ℝ (Fin N)) (H : Config ι N →ₗ[ℝ] Config ι N) :
    Config ι N →ₗ[ℝ] Config ι N :=
  tangentOp e ∘ₗ H ∘ₗ tangentOp e + normalProj e

theorem normalProj_apply (e : ι → EuclideanSpace ℝ (Fin N)) (u : Config ι N) (x : ι) :
    normalProj e u x = inner ℝ (e x) (u x) • e x := rfl

theorem tangentOp_apply (e : ι → EuclideanSpace ℝ (Fin N)) (u : Config ι N) (x : ι) :
    tangentOp e u x = u x - inner ℝ (e x) (u x) • e x := rfl

variable [Fintype ι]

/-- The inner product `⟨u, v⟩ = ∑_x u_x · v_x` on `(ℝ^N)^ι`. -/
def cinner (u v : Config ι N) : ℝ := ∑ x, inner ℝ (u x) (v x)

theorem cinner_comm (u v : Config ι N) : cinner u v = cinner v u := by
  unfold cinner; exact Finset.sum_congr rfl fun x _ => real_inner_comm _ _

theorem cinner_add_left (u v w : Config ι N) : cinner (u + v) w = cinner u w + cinner v w := by
  unfold cinner; simp [inner_add_left, Finset.sum_add_distrib]

theorem cinner_add_right (u v w : Config ι N) : cinner u (v + w) = cinner u v + cinner u w := by
  rw [cinner_comm, cinner_add_left, cinner_comm v, cinner_comm w]

theorem cinner_sub_left (u v w : Config ι N) : cinner (u - v) w = cinner u w - cinner v w := by
  unfold cinner; simp [inner_sub_left, Finset.sum_sub_distrib]

theorem cinner_sub_right (u v w : Config ι N) : cinner u (v - w) = cinner u v - cinner u w := by
  rw [cinner_comm, cinner_sub_left, cinner_comm v, cinner_comm w]

theorem cinner_smul_left (c : ℝ) (u v : Config ι N) : cinner (c • u) v = c * cinner u v := by
  unfold cinner; simp [inner_smul_left, Finset.mul_sum]

theorem cinner_smul_right (c : ℝ) (u v : Config ι N) : cinner u (c • v) = c * cinner u v := by
  rw [cinner_comm, cinner_smul_left, cinner_comm]

theorem cinner_normalProj_right (e : ι → EuclideanSpace ℝ (Fin N))
    (u w : Config ι N) :
    cinner u (normalProj e w) = ∑ x, inner ℝ (e x) (w x) * inner ℝ (e x) (u x) := by
  unfold cinner
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [normalProj_apply, inner_smul_right, real_inner_comm (e x) (u x)]

theorem cinner_normalProj_comm (e : ι → EuclideanSpace ℝ (Fin N))
    (u w : Config ι N) : cinner u (normalProj e w) = cinner (normalProj e u) w := by
  rw [cinner_normalProj_right e, cinner_comm, cinner_normalProj_right e]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem cinner_normalProj_self (e : ι → EuclideanSpace ℝ (Fin N))
    (u : Config ι N) : cinner u (normalProj e u) = ∑ x, inner ℝ (e x) (u x) ^ 2 := by
  rw [cinner_normalProj_right e]
  exact Finset.sum_congr rfl fun x _ => (sq _).symm

theorem cinner_tangentOp_comm (e : ι → EuclideanSpace ℝ (Fin N))
    (u w : Config ι N) : cinner u (tangentOp e w) = cinner (tangentOp e u) w := by
  unfold tangentOp
  simp only [LinearMap.sub_apply, LinearMap.id_apply]
  rw [cinner_sub_right, cinner_sub_left, cinner_normalProj_comm e]

/-- `⟨u, A_e u⟩ = ⟨Qu, H Qu⟩ + ∑_x ⟨e_x, u_x⟩²`. -/
theorem cinner_gaussForm (e : ι → EuclideanSpace ℝ (Fin N))
    (H : Config ι N →ₗ[ℝ] Config ι N) (u : Config ι N) :
    cinner u (gaussForm e H u) =
      cinner (tangentOp e u) (H (tangentOp e u)) + ∑ x, inner ℝ (e x) (u x) ^ 2 := by
  unfold gaussForm
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [cinner_add_right, cinner_tangentOp_comm e, cinner_normalProj_self e]

/-- The quadratic form of a sum, for a symmetric `H`. -/
theorem cinner_quad_add (H : Config ι N →ₗ[ℝ] Config ι N)
    (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v) (v z : Config ι N) :
    cinner (v + z) (H (v + z)) =
      cinner v (H v) + 2 * cinner v (H z) + cinner z (H z) := by
  rw [map_add, cinner_add_left, cinner_add_right, cinner_add_right]
  have : cinner z (H v) = cinner v (H z) := by
    rw [hsymm z v, cinner_comm]
  rw [this]; ring

/-! ### The rescaled chart -/

/-- The nonlinear part `z(v)_x = √β (√(1 - |v_x|²/β) - 1) e_x` of the rescaled chart (A.2). -/
def chartShift (β : ℝ) (e : ι → EuclideanSpace ℝ (Fin N)) (v : Config ι N) : Config ι N :=
  fun x => (Real.sqrt β * (Real.sqrt (1 - ‖v x‖ ^ 2 / β) - 1)) • e x

/-- The chart point `e + β^{-1/2}(v + z(v))` (A.2). -/
def chartPoint (β : ℝ) (e : ι → EuclideanSpace ℝ (Fin N)) (v : Config ι N) : Config ι N :=
  fun x => e x + (Real.sqrt β)⁻¹ • (v x + chartShift β e v x)

/-- The chart Jacobian `1[|v_x| < √β ∀x] ∏_x (1 - |v_x|²/β)^{-1/2}` (A.2). -/
def chartJac (β : ℝ) (v : Config ι N) : ℝ :=
  ∏ x, if ‖v x‖ < Real.sqrt β then (Real.sqrt (1 - ‖v x‖ ^ 2 / β))⁻¹ else 0

theorem chartPoint_eq (β : ℝ) (hβ : 0 < β) (e : EuclideanSpace ℝ (Fin N)) (v : perp e) :
    hemiE e ((Real.sqrt β)⁻¹ • v) =
      e + (Real.sqrt β)⁻¹ • ((v : EuclideanSpace ℝ (Fin N)) +
        (Real.sqrt β * (Real.sqrt (1 - ‖(v : EuclideanSpace ℝ (Fin N))‖ ^ 2 / β) - 1)) • e) := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hn : ‖((Real.sqrt β)⁻¹ • v : perp e)‖ ^ 2 = ‖(v : EuclideanSpace ℝ (Fin N))‖ ^ 2 / β := by
    rw [norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg hs.le, inv_pow, Real.sq_sqrt hβ.le]
    rw [norm_coe_perp]; ring
  unfold hemiE
  rw [hn, Submodule.coe_smul]
  have h1 : (Real.sqrt β)⁻¹ * (Real.sqrt β * (Real.sqrt (1 - ‖(v : EuclideanSpace ℝ (Fin N))‖ ^ 2 / β) - 1))
      = Real.sqrt (1 - ‖(v : EuclideanSpace ℝ (Fin N))‖ ^ 2 / β) - 1 := by
    field_simp
  rw [smul_add, smul_smul, h1]
  module


theorem finrank_perp (e : EuclideanSpace ℝ (Fin N)) (he : ‖e‖ = 1) :
    Module.finrank ℝ (perp e) + 1 = N := by
  have h0 : e ≠ 0 := by rintro rfl; simp at he
  have h : 1 + Module.finrank ℝ (perp e) = N := by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
    rwa [finrank_span_singleton h0, finrank_euclideanSpace_fin] at this
  omega

theorem finrank_pi_perp (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) :
    Module.finrank ℝ ((x : ι) → perp (e x)) = Fintype.card ι * (N - 1) := by
  rw [Module.finrank_pi_fintype]
  have : ∀ x, Module.finrank ℝ (perp (e x)) = N - 1 := fun x => by
    have := finrank_perp (e x) (he x); omega
  simp [this]


/-- The standard Gaussian probability measure `(2π)^{-n/2} e^{-|ψ|²/2} dψ` on `(ℝ^N)^ι`,
`n = N |ι|`. -/
def stdGaussian (ι : Type u) [Fintype ι] (N : ℕ) : Measure (Config ι N) :=
  (volume : Measure (Config ι N)).withDensity fun ψ =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
      Real.exp (-(1 / 2) * cinner ψ ψ))

/-- The quadratic exponent `-(β/2) ⟨φ - e, H (φ - e)⟩` of the Boltzmann weight at the
background `e` (Lemma II.7.3, `A(φ) - A(e) = ½ ⟨φ - e, H (φ - e)⟩`). -/
def sphereExponent (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N) (u : Config ι N) :
    ℝ :=
  -(β / 2) * cinner (u - e) (H (u - e))

/-- The interaction exponent of (A.3): `-⟨v, H z(v)⟩ - ½⟨z(v), H z(v)⟩`. -/
def chartExponent (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N) (v : Config ι N) :
    ℝ :=
  -cinner v (H (chartShift β e v)) - (1 / 2) * cinner (chartShift β e v) (H (chartShift β e v))

/-- The integrand of (A.3) as a function of the tangent vector `v`. -/
def chartIntegrand (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (F : Config ι N → ℝ≥0∞) (v : Config ι N) : ℝ≥0∞ :=
  ENNReal.ofReal (chartJac β v) *
    (F (chartPoint β e v) * ENNReal.ofReal (Real.exp (chartExponent β e H v)))

theorem measurable_chartIntegrand (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (F : Config ι N → ℝ≥0∞) (hF : Measurable F) : Measurable (chartIntegrand β e H F) := by
  have hH : Continuous H := LinearMap.continuous_of_finiteDimensional H
  unfold chartIntegrand chartJac chartPoint chartExponent chartShift
  refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
  · refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun x _ => ?_)
    refine Measurable.ite (measurableSet_lt ?_ measurable_const) ?_ measurable_const
    · exact (measurable_pi_apply x).norm
    · fun_prop
  · refine hF.comp ?_
    refine measurable_pi_iff.2 fun x => ?_
    fun_prop
  · refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    unfold cinner
    fun_prop


theorem norm_sq_inv_sqrt_smul {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {β : ℝ}
    (hβ : 0 < β) (v : E') : ‖(Real.sqrt β)⁻¹ • v‖ ^ 2 = ‖v‖ ^ 2 / β := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  rw [norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg hs.le, inv_pow, Real.sq_sqrt hβ.le]
  ring

theorem norm_inv_sqrt_smul_lt_one_iff {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {β : ℝ} (hβ : 0 < β) (v : E') : ‖(Real.sqrt β)⁻¹ • v‖ < 1 ↔ ‖v‖ < Real.sqrt β := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hs.le, inv_mul_lt_iff₀ hs, mul_one]

theorem chartWeight_inv_sqrt_smul {β : ℝ} (hβ : 0 < β) (e : EuclideanSpace ℝ (Fin N)) (v : perp e) :
    chartWeight e ((Real.sqrt β)⁻¹ • v) =
      if ‖(v : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β then
        (Real.sqrt (1 - ‖(v : EuclideanSpace ℝ (Fin N))‖ ^ 2 / β))⁻¹ else 0 := by
  unfold chartWeight
  have h1 := norm_inv_sqrt_smul_lt_one_iff hβ v
  have h2 := norm_sq_inv_sqrt_smul hβ v
  by_cases h : ‖v‖ < Real.sqrt β
  · have h' : ‖(Real.sqrt β)⁻¹ • v‖ < 1 := h1.2 h
    have hv : ‖(v : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := h
    simp only [h', hv, ↓reduceIte]
    rw [h2, one_div]
    rfl
  · have h' : ¬ ‖(Real.sqrt β)⁻¹ • v‖ < 1 := fun hh => h (h1.1 hh)
    have hv : ¬ ‖(v : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := h
    simp only [h', hv, ↓reduceIte]


theorem chartJac_eq_zero {β : ℝ} {w : Config ι N} {x₀ : ι} (h : ¬ ‖w x₀‖ < Real.sqrt β) :
    chartJac β w = 0 := by
  unfold chartJac
  exact Finset.prod_eq_zero (Finset.mem_univ x₀) (by simp [h])

theorem chartJac_of_lt {β : ℝ} {w : Config ι N} (h : ∀ x, ‖w x‖ < Real.sqrt β) :
    chartJac β w = ∏ x, (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ := by
  unfold chartJac
  exact Finset.prod_congr rfl fun x _ => by simp [h x]

theorem chartJac_nonneg (β : ℝ) (w : Config ι N) : 0 ≤ chartJac β w := by
  unfold chartJac
  exact Finset.prod_nonneg fun x _ => by split_ifs <;> positivity

theorem sphereExponent_chartPoint {β : ℝ} (hβ : 0 < β) (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N) (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v)
    (w : Config ι N) :
    sphereExponent β e H (chartPoint β e w) =
      chartExponent β e H w - (1 / 2) * cinner w (H w) := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hd : chartPoint β e w - e = (Real.sqrt β)⁻¹ • (w + chartShift β e w) := by
    funext x; simp [chartPoint]
  unfold sphereExponent chartExponent
  rw [hd, map_smul, cinner_smul_left, cinner_smul_right, cinner_quad_add H hsymm]
  have : (β / 2) * ((Real.sqrt β)⁻¹ * ((Real.sqrt β)⁻¹ * (cinner w (H w) +
      2 * cinner w (H (chartShift β e w)) + cinner (chartShift β e w) (H (chartShift β e w)))))
      = (1 / 2) * (cinner w (H w) + 2 * cinner w (H (chartShift β e w)) +
        cinner (chartShift β e w) (H (chartShift β e w))) := by
    have : (Real.sqrt β)⁻¹ * (Real.sqrt β)⁻¹ = β⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hβ.le]
    rw [← mul_assoc ((Real.sqrt β)⁻¹), this]
    field_simp
  rw [neg_mul, this]; ring


/-- Pointwise form of the rescaling `ξ = β^{-1/2} v` of the chart integrand. -/
theorem chart_pointwise {β : ℝ} (hβ : 0 < β) (e : Config ι N) (he : ∀ x, ‖e x‖ = 1)
    (H : Config ι N →ₗ[ℝ] Config ι N) (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v)
    (F : Config ι N → ℝ≥0∞) (v : (x : ι) → perp (e x)) :
    (∏ x, ENNReal.ofReal (chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x))) *
        (F (fun x => (chartMapPi e he ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N))) *
          ENNReal.ofReal (Real.exp (sphereExponent β e H
            (fun x => (chartMapPi e he ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N)))))) =
      chartIntegrand β e H F (fun x => (v x : EuclideanSpace ℝ (Fin N))) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
          (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))))) := by
  set w : Config ι N := fun x => (v x : EuclideanSpace ℝ (Fin N)) with hw
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  by_cases hb : ∀ x, ‖w x‖ < Real.sqrt β
  · have hcw : ∀ x, chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x) =
        (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ := fun x => by
      rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]
      have hx := hb x
      simp only [hw] at hx
      simp only [hw, hx, ↓reduceIte]
    have hJ : ∏ x, ENNReal.ofReal (chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x)) =
        ENNReal.ofReal (chartJac β w) := by
      rw [chartJac_of_lt hb, ENNReal.ofReal_prod_of_nonneg (fun x _ => by positivity)]
      exact Finset.prod_congr rfl fun x _ => by rw [hcw x]
    have hpt : (fun x => (chartMapPi e he ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N))) =
        chartPoint β e w := by
      funext x
      have hlt : ‖((Real.sqrt β)⁻¹ • v) x‖ < 1 := by
        rw [Pi.smul_apply]; exact (norm_inv_sqrt_smul_lt_one_iff hβ (v x)).2 (hb x)
      unfold chartMapPi
      rw [coe_hemiPt_of_lt (e x) (he x) hlt, Pi.smul_apply, chartPoint_eq β hβ (e x) (v x)]
      rfl
    rw [hJ, hpt, sphereExponent_chartPoint hβ e H hsymm w]
    unfold chartIntegrand
    have h3 : chartExponent β e H w - 1 / 2 * cinner w (H w) =
        chartExponent β e H w + -(1 / 2) * cinner w (H w) := by ring
    rw [h3, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring
  · push Not at hb
    obtain ⟨x₀, hx₀⟩ := hb
    have h0 : chartJac β w = 0 := chartJac_eq_zero (x₀ := x₀) (not_lt.2 hx₀)
    have hp : ∏ x, ENNReal.ofReal (chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ x₀) ?_
      rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]
      have hx : ¬ ‖(x₀ |> fun x => ((v x : EuclideanSpace ℝ (Fin N))))‖ < Real.sqrt β := not_lt.2 hx₀
      simp only [hx, ↓reduceIte, ENNReal.ofReal_zero]
    rw [hp, zero_mul]
    unfold chartIntegrand
    rw [h0]; simp


theorem continuous_sphereExponent (β : ℝ) (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N) :
    Continuous (sphereExponent β e H) := by
  have hHc : Continuous H := LinearMap.continuous_of_finiteDimensional H
  unfold sphereExponent cinner
  fun_prop

omit [Fintype ι] in
theorem coe_tangentProj (e : Config ι N) (he : ∀ x, ‖e x‖ = 1) (u : Config ι N) :
    (fun x => (tangentProj e he u x : EuclideanSpace ℝ (Fin N))) = tangentOp e u := by
  funext x; rfl

/-- **The exact real chart identity (A.3) of LF-BASE-KF0** (with `R = C_e^{1/2}`): for the product
`Measure.pi (toSphere volume)` of the surface measures over a finite set `ι` of sites, a Boltzmann
weight `exp(-(β/2) ⟨φ - e, H (φ - e)⟩)` (`= exp(-β [A(φ) - A(e)])` by Lemma II.7.3, `H = H₀ + diag α`)
and a measurable `F ≥ 0` supported in the product of the open hemispheres around the unit vectors
`e_x`:
```
∫ F(φ) e^{-β[A(φ)-A(e)]} ∏ dσ(φ_x)
  = β^{-m/2} (2π)^{m/2} |det R| ∫ J_β(v) e^{-⟨v,Hz(v)⟩ - ½⟨z(v),Hz(v)⟩} F(e + β^{-1/2}(v + z(v))) dγ(ψ),
```
`m = (N-1)|ι|`, `v = Q R ψ`, `γ` the standard Gaussian on `(ℝ^N)^ι`, and `R` a factor of the covariance
`C_e = (Q H Q + P)^{-1}` of `A_e = Q H Q + P` (`⟨Rψ, A_e Rψ⟩ = |ψ|²`), so `|det R| = (det C_e)^{1/2}`. -/
theorem lintegral_sphere_pi_eq_gaussian (e : Config ι N) (he : ∀ x, ‖e x‖ = 1) (hN : 1 ≤ N)
    {β : ℝ} (hβ : 0 < β) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v) (R : Config ι N ≃ₗ[ℝ] Config ι N)
    (hR : ∀ ψ, cinner (R ψ) (gaussForm e H (R ψ)) = cinner ψ ψ)
    (F : Config ι N → ℝ≥0∞) (hF : Measurable F)
    (hFsupp : ∀ u : Config ι N, (∃ x, ¬ 0 < inner ℝ (e x) (u x)) → F u = 0) :
    ∫⁻ φ : ι → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
        F (fun x => (φ x : EuclideanSpace ℝ (Fin N))) *
          ENNReal.ofReal (Real.exp (sphereExponent β e H (fun x => (φ x : EuclideanSpace ℝ (Fin N)))))
        ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ENNReal.ofReal (β ^ (-(((N : ℝ) - 1) * Fintype.card ι) / 2) *
          (2 * Real.pi) ^ ((((N : ℝ) - 1) * Fintype.card ι) / 2) *
          |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)|) *
        ∫⁻ ψ, chartIntegrand β e H F (tangentOp e (R ψ)) ∂(stdGaussian ι N) := by
  classical
  set E := EuclideanSpace ℝ (Fin N) with hE
  set μT : Measure ((x : ι) → perp (e x)) := Measure.pi fun x => (volume : Measure (perp (e x)))
    with hμT
  set s : ℝ := (Real.sqrt β)⁻¹ with hs
  have hspos : 0 < s := inv_pos.2 (Real.sqrt_pos.2 hβ)
  have hHc : Continuous H := LinearMap.continuous_of_finiteDimensional H
  -- the Boltzmann integrand on the spin configurations
  set f : (ι → Metric.sphere (0 : E) 1) → ℝ≥0∞ := fun φ =>
    F (fun x => (φ x : E)) *
      ENNReal.ofReal (Real.exp (sphereExponent β e H (fun x => (φ x : E)))) with hf
  have hcoe : Measurable fun φ : ι → Metric.sphere (0 : E) 1 => fun x => (φ x : E) :=
    measurable_pi_iff.2 fun x => measurable_subtype_coe.comp (measurable_pi_apply x)
  have hfm : Measurable f := by
    exact (hF.comp hcoe).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((continuous_sphereExponent β e H).measurable.comp hcoe)))
  have hfsupp : ∀ φ : ι → Metric.sphere (0 : E) 1,
      (∃ x, ¬ 0 < inner ℝ (e x) (φ x : E)) → f φ = 0 := fun φ h => by
    simp only [hf]; rw [hFsupp _ h, zero_mul]
  -- Step A: the chart
  have hA := lintegral_sphere_pi_hemisphere e he f hfm hfsupp
  set Φ₁ : ((x : ι) → perp (e x)) → ℝ≥0∞ := fun ξ =>
    (∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))) * f (chartMapPi e he ξ) with hΦ₁
  have hΦm : Measurable Φ₁ :=
    (Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_chartWeight (e x)).comp (measurable_pi_apply x))).mul
      (hfm.comp (measurable_chartMapPi e he))
  -- Step B: the scaling `v = β^{1/2} ξ`
  have hB : ∫⁻ ξ, Φ₁ ξ ∂μT =
      ENNReal.ofReal (s ^ (Fintype.card ι * (N - 1))) * ∫⁻ v, Φ₁ (s • v) ∂μT := by
    have := lintegral_eq_pow_mul_lintegral_smul μT hspos hΦm
    rwa [finrank_pi_perp e he] at this
  -- Step C: the rescaled integrand
  set G' : Config ι N → ℝ≥0∞ := fun w =>
    chartIntegrand β e H F w * ENNReal.ofReal (Real.exp (-(1 / 2) * cinner w (H w))) with hG'
  have hC : ∫⁻ v, Φ₁ (s • v) ∂μT = ∫⁻ v, G' (fun x => (v x : E)) ∂μT :=
    lintegral_congr fun v => chart_pointwise hβ e he H hsymm F v
  -- Step D: the Gaussian lift
  have hcv : Measurable fun v : (x : ι) → perp (e x) => (fun x => (v x : E) : Config ι N) :=
    measurable_pi_iff.2 fun x => measurable_subtype_coe.comp (measurable_pi_apply x)
  have hexpm : Measurable fun w : Config ι N => Real.exp (-(1 / 2) * cinner w (H w)) := by
    refine Real.measurable_exp.comp ?_
    unfold cinner; fun_prop
  have hG'm : Measurable G' :=
    (measurable_chartIntegrand β e H F hF).mul (ENNReal.measurable_ofReal.comp hexpm)
  have hD := lintegral_tangent_eq e he (fun v => G' (fun x => (v x : E))) (hG'm.comp hcv)
  simp_rw [coe_tangentProj e he] at hD
  -- Step E: combine the Gaussian exponents
  set Ξ : Config ι N → ℝ≥0∞ := chartIntegrand β e H F with hΞ
  have hE : ∀ u : Config ι N, G' (tangentOp e u) * ENNReal.ofReal (normalWeight e u) =
      Ξ (tangentOp e u) * ENNReal.ofReal (Real.exp (-(1 / 2) * cinner u (gaussForm e H u))) := by
    intro u
    simp only [hG', hΞ]
    unfold normalWeight
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, cinner_gaussForm e H u]
    congr 3
    ring
  -- Step F: the linear change of variables `u = R ψ`
  have hF' := lintegral_eq_ofReal_abs_det_mul (volume : Measure (Config ι N)) R
    (fun u => Ξ (tangentOp e u) * ENNReal.ofReal (Real.exp (-(1 / 2) * cinner u (gaussForm e H u))))
  have hF'' : ∀ ψ : Config ι N,
      Ξ (tangentOp e (R ψ)) * ENNReal.ofReal (Real.exp (-(1 / 2) * cinner (R ψ) (gaussForm e H (R ψ)))) =
      Ξ (tangentOp e (R ψ)) * ENNReal.ofReal (Real.exp (-(1 / 2) * cinner ψ ψ)) := by
    intro ψ; rw [hR ψ]
  simp_rw [hF''] at hF'
  -- Step G: the standard Gaussian
  have hΞm : Measurable fun ψ : Config ι N => Ξ (tangentOp e (R ψ)) := by
    refine (measurable_chartIntegrand β e H F hF).comp ?_
    exact (LinearMap.continuous_of_finiteDimensional (tangentOp e ∘ₗ (R : Config ι N →ₗ[ℝ] Config ι N))).measurable
  have hdm : Measurable fun ψ : Config ι N => ENNReal.ofReal ((2 * Real.pi) ^
      (-((N * Fintype.card ι : ℕ) : ℝ) / 2) * Real.exp (-(1 / 2) * cinner ψ ψ)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul measurable_const (Real.measurable_exp.comp ?_))
    unfold cinner; fun_prop
  have hG : ∫⁻ ψ, Ξ (tangentOp e (R ψ)) * ENNReal.ofReal (Real.exp (-(1 / 2) * cinner ψ ψ)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (((N * Fintype.card ι : ℕ) : ℝ) / 2)) *
        ∫⁻ ψ, Ξ (tangentOp e (R ψ)) ∂(stdGaussian ι N) := by
    unfold stdGaussian
    rw [lintegral_withDensity_eq_lintegral_mul₀ hdm.aemeasurable hΞm.aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ψ => ?_
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    have : (2 * Real.pi) ^ (((N * Fintype.card ι : ℕ) : ℝ) / 2) *
        ((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) * Real.exp (-(1 / 2) * cinner ψ ψ)) =
        Real.exp (-(1 / 2) * cinner ψ ψ) := by
      rw [← mul_assoc, ← Real.rpow_add (by positivity)]
      rw [show ((N * Fintype.card ι : ℕ) : ℝ) / 2 + -((N * Fintype.card ι : ℕ) : ℝ) / 2 = 0 by ring]
      simp
    rw [this]; ring
  have hmcast : ((Fintype.card ι * (N - 1) : ℕ) : ℝ) = ((N : ℝ) - 1) * Fintype.card ι := by
    rw [Nat.cast_mul, Nat.cast_sub hN]; push_cast; ring
  have hncast : ((N * Fintype.card ι : ℕ) : ℝ) = (N : ℝ) * Fintype.card ι := by push_cast; ring
  have hpos2 : 0 < 2 * Real.pi := by positivity
  have ha : s ^ (Fintype.card ι * (N - 1)) = β ^ (-(((N : ℝ) - 1) * Fintype.card ι) / 2) := by
    have h1 : s = β ^ (-(1 / 2 : ℝ)) := by
      rw [hs, Real.sqrt_eq_rpow, Real.rpow_neg hβ.le]
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hβ.le, hmcast]
    congr 1; ring
  have hb : (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * (2 * Real.pi) ^
      (((N * Fintype.card ι : ℕ) : ℝ) / 2) = (2 * Real.pi) ^ ((((N : ℝ) - 1) * Fintype.card ι) / 2) := by
    rw [← Real.rpow_add hpos2, hncast]
    congr 1; ring
  calc _ = ∫⁻ ξ, Φ₁ ξ ∂μT := hA
    _ = ENNReal.ofReal (s ^ (Fintype.card ι * (N - 1))) * ∫⁻ v, G' (fun x => (v x : E)) ∂μT := by
        rw [hB, hC]
    _ = ENNReal.ofReal (s ^ (Fintype.card ι * (N - 1))) *
          (ENNReal.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) *
            ∫⁻ u, Ξ (tangentOp e u) *
              ENNReal.ofReal (Real.exp (-(1 / 2) * cinner u (gaussForm e H u)))) := by
        rw [hD]; congr 2; exact lintegral_congr fun u => hE u
    _ = ENNReal.ofReal (s ^ (Fintype.card ι * (N - 1))) *
          (ENNReal.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) *
            (ENNReal.ofReal |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)| *
              (ENNReal.ofReal ((2 * Real.pi) ^ (((N * Fintype.card ι : ℕ) : ℝ) / 2)) *
                ∫⁻ ψ, Ξ (tangentOp e (R ψ)) ∂(stdGaussian ι N)))) := by
        rw [hF', hG]
    _ = _ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ha]
        congr 2
        rw [← hb]; ring
