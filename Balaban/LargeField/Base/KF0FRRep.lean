/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRWhite
public import Balaban.LargeField.Base.KF0FRSheets
public import Balaban.LargeField.Base.KF0CutoffSplit
public import Balaban.LargeField.Base.PiLintegral
public import Balaban.Frozen.Model.PartitionFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRRep`: the partition function in whitened sheet coordinates (route FR, (R2)–(R3))

`notes/phase1/KF0-FR.md` (R2), (R3). On the sheet `σ_x` the spin is
`φ_x = ξ_x + s_x t_x h`, `ξ_x ∈ h^⊥`, `t_x = √(1-|ξ_x|²)`, `s_x = ±1` (`coe_sheetPt`). The energy is
exactly `H(φ) = ½⟨ξ, K ξ⟩ + V_σ(ξ)` (`energy_sheetCfg`) with the non-negative normal part

`V_σ(ξ) = ½ ∑_x ∑_μ (s_{x+e_μ} t_{x+e_μ} - s_x t_x)² + (ν/2) ∑_x (s_x t_x - 1)²` (`frV`).

The finite-range whitening `ξ = β^{-1/2} C_R ψ` (`frField`) then gives (`partitionFunction_eq_fr`)

`Z(g) = c ∑_σ ∫ exp(-½ ∑_{x,y} Q_R(x,y) ⟨ψ_x, ψ_y⟩) A_σ(β^{-1/2} C_R ψ; g) dγ(ψ)`,

with `γ` the product of standard Gaussians on `h^⊥`, `c = |det(β^{-1/2} C_R)|^{N-1} (2π)^{(N-1)|Λ|/2}`,
and `A_σ(ξ; g) = ∏_x w(ξ_x) · exp(-β V_σ(ξ) + ⟨g, φ⟩)` (`frA`): chart weights, normal energy and
source. Everything except the Gaussian weight is now a product of local factors.
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-- The sign of a sheet. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

/-- The normal coordinate `t = √(1 - |ξ|²)`. -/
def tN (ξ : perp h) : ℝ := Real.sqrt (1 - ‖ξ‖ ^ 2)

/-- **The sheet point in coordinates**: `φ = ξ + s t h`. -/
theorem coe_sheetPt (hh : ‖h‖ = 1) (b : Bool) {ξ : perp h} (hξ : ‖ξ‖ < 1) :
    ((sheetPt h hh b ξ : Sph) : E) = (ξ : E) + (sgn b * tN h ξ) • h := by
  cases b
  · simp only [sheetPt, Bool.false_eq_true, ↓reduceIte, coe_reflS, coe_hemiPt_of_lt h hh hξ,
      hemiE, sgn, tN]
    rw [map_add, map_smul, reflE_h, Submodule.reflection_mem_subspace_eq_self ξ.2]
    rw [smul_neg, add_comm, neg_one_mul, neg_smul]
  · simp only [sheetPt, ↓reduceIte, coe_hemiPt_of_lt h hh hξ, hemiE, sgn, tN, one_mul]
    rw [add_comm]

/-- Pythagoras for a tangent vector and a multiple of `h`. -/
theorem norm_sq_add_smul (hh : ‖h‖ = 1) (v : perp h) (c : ℝ) :
    ‖(v : E) + c • h‖ ^ 2 = ‖v‖ ^ 2 + c ^ 2 := by
  have h0 : inner ℝ (v : E) h = 0 := by
    rw [real_inner_comm]; exact inner_eq_of_mem_perp h v.2
  rw [norm_add_sq_real, inner_smul_right, h0, mul_zero, mul_zero, add_zero, norm_smul,
    hh, mul_one, Real.norm_eq_abs, sq_abs, norm_coe_perp]

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The sheet configuration above the tangent field `ξ`. -/
def sheetCfg (hh : ‖h‖ = 1) (σ : Torus d ℓ → Bool) (ξ : Torus d ℓ → perp h) :
    Torus d ℓ → Sph :=
  fun x => sheetPt h hh (σ x) (ξ x)

/-- The normal energy `V_σ(ξ)`. -/
def frV (ν : ℝ) (σ : Torus d ℓ → Bool) (ξ : Torus d ℓ → perp h) : ℝ :=
  (1 / 2) * ∑ x : Torus d ℓ, ∑ μ : Fin d,
      (sgn (σ (x + Pi.single μ 1)) * tN h (ξ (x + Pi.single μ 1)) - sgn (σ x) * tN h (ξ x)) ^ 2
    + (ν / 2) * ∑ x : Torus d ℓ, (sgn (σ x) * tN h (ξ x) - 1) ^ 2

/-- **The energy in sheet coordinates (R2)**: `H(φ) = ½ ⟨ξ, K ξ⟩ + V_σ(ξ)` when every
`|ξ_x| < 1`. -/
theorem energy_sheetCfg (hh : ‖h‖ = 1) (ν : ℝ) (σ : Torus d ℓ → Bool)
    {ξ : Torus d ℓ → perp h} (hξ : ∀ x, ‖ξ x‖ < 1) :
    energy d N ℓ ν h (sheetCfg h hh σ ξ) = (1 / 2) * tangentQuad ν ξ + frV h ν σ ξ := by
  have hc : ∀ x, ((sheetCfg h hh σ ξ x : Sph) : E) = (ξ x : E) + (sgn (σ x) * tN h (ξ x)) • h :=
    fun x => coe_sheetPt h hh (σ x) (hξ x)
  have hbond : ∀ x y, ‖((sheetCfg h hh σ ξ y : Sph) : E) - (sheetCfg h hh σ ξ x : Sph)‖ ^ 2 =
      ‖ξ y - ξ x‖ ^ 2 + (sgn (σ y) * tN h (ξ y) - sgn (σ x) * tN h (ξ x)) ^ 2 := by
    intro x y
    rw [hc, hc, ← norm_sq_add_smul h hh (ξ y - ξ x)]
    congr 1
    rw [Submodule.coe_sub, sub_smul]
    abel_nf
  have hsite : ∀ x, ‖((sheetCfg h hh σ ξ x : Sph) : E) - h‖ ^ 2 =
      ‖ξ x‖ ^ 2 + (sgn (σ x) * tN h (ξ x) - 1) ^ 2 := by
    intro x
    rw [hc, ← norm_sq_add_smul h hh (ξ x)]
    congr 1
    rw [sub_smul, one_smul]
    abel_nf
  unfold energy
  simp_rw [hbond, hsite]
  rw [tangentQuad_eq]
  unfold frV
  simp only [Finset.sum_add_distrib]
  ring

/-- The source pairing `⟨g, φ⟩`. -/
def srcPair (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → Sph) : ℂ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (((φ x : E) i : ℝ) : ℂ)

/-- **The non-Gaussian part of the chart integrand**: chart weights, normal energy, source. -/
def frA (hh : ‖h‖ = 1) (β ν : ℝ) (σ : Torus d ℓ → Bool) (g : Torus d ℓ → Fin N → ℂ)
    (ξ : Torus d ℓ → perp h) : ℂ :=
  (∏ x, ((chartWeight h (ξ x) : ℝ) : ℂ)) *
    Complex.exp (-((β * frV h ν σ ξ : ℝ) : ℂ) + srcPair g (sheetCfg h hh σ ξ))

theorem measurable_tN : Measurable (tN h) := by
  unfold tN; fun_prop

omit [NeZero ℓ] in
theorem measurable_sheetCfg (hh : ‖h‖ = 1) (σ : Torus d ℓ → Bool) :
    Measurable (sheetCfg h hh σ) := by
  refine measurable_pi_iff.2 fun x => ?_
  unfold sheetCfg sheetPt
  have hp : Measurable fun ξ : Torus d ℓ → perp h => hemiPt h hh (ξ x) :=
    (continuous_hemiPt h hh).measurable.comp (measurable_pi_apply x)
  split_ifs
  · exact hp
  · exact (measurable_reflS h).comp hp

theorem measurable_frV (ν : ℝ) (σ : Torus d ℓ → Bool) : Measurable (frV h ν σ) := by
  have ht : ∀ y, Measurable fun ξ : Torus d ℓ → perp h => tN h (ξ y) :=
    fun y => (measurable_tN h).comp (measurable_pi_apply y)
  unfold frV
  refine Measurable.add (measurable_const.mul (Finset.measurable_sum _ fun x _ =>
    Finset.measurable_sum _ fun μ _ => ?_)) (measurable_const.mul (Finset.measurable_sum _ fun x _ => ?_))
  · exact ((measurable_const.mul (ht _)).sub (measurable_const.mul (ht x))).pow_const 2
  · exact ((measurable_const.mul (ht x)).sub measurable_const).pow_const 2

theorem measurable_srcPair (g : Torus d ℓ → Fin N → ℂ) :
    Measurable (srcPair (d := d) (ℓ := ℓ) (N := N) g) := by
  unfold srcPair
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun i _ => ?_
  refine measurable_const.mul (Complex.measurable_ofReal.comp ?_)
  exact (by fun_prop : Continuous fun φ : Torus d ℓ → Sph => ((φ x : E) i)).measurable

theorem measurable_frA (hh : ‖h‖ = 1) (β ν : ℝ) (σ : Torus d ℓ → Bool)
    (g : Torus d ℓ → Fin N → ℂ) : Measurable (frA h hh β ν σ g) := by
  unfold frA
  refine Measurable.mul (Finset.measurable_prod _ fun x _ => Complex.measurable_ofReal.comp
    ((measurable_chartWeight h).comp (measurable_pi_apply x))) ?_
  refine Complex.measurable_exp.comp (Measurable.add ?_ ((measurable_srcPair g).comp
    (measurable_sheetCfg h hh σ)))
  exact (Complex.measurable_ofReal.comp (measurable_const.mul (measurable_frV h ν σ))).neg

/-! ### (R1) + (R2): the partition function as a sum over sheets -/

theorem energy_nonneg {ν : ℝ} (hν : 0 ≤ ν) (φ : Torus d ℓ → Sph) : 0 ≤ energy d N ℓ ν h φ := by
  unfold energy
  refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun μ _ => sq_nonneg _)) (mul_nonneg (by linarith) (Finset.sum_nonneg
      fun x _ => sq_nonneg _))

/-- **The partition function as a sum over the sheets**:
`Z(g) = ∑_σ ∫ exp(-(β/2)⟨ξ, K ξ⟩) A_σ(ξ; g) dξ`. -/
theorem partitionFunction_eq_sheets (hh : ‖h‖ = 1) {β : ℝ} (hβ : 0 ≤ β) {ν : ℝ} (hν : 0 ≤ ν)
    (g : Torus d ℓ → Fin N → ℂ) :
    partitionFunction d N ℓ β ν h g =
      ∑ σ : Torus d ℓ → Bool, ∫ ξ : Torus d ℓ → perp h,
        ((Real.exp (-(β / 2) * tangentQuad ν ξ) : ℝ) : ℂ) * frA h hh β ν σ g ξ
          ∂(Measure.pi fun _ => (volume : Measure (perp h))) := by
  set F : (Torus d ℓ → Sph) → ℂ := fun φ =>
    Complex.exp (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + srcPair g φ) with hF
  have hFm : Measurable F := by
    have he : Measurable (energy d N ℓ ν h) := by
      unfold energy; fun_prop
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul he)).neg.add (measurable_srcPair g))
  have hFi : Integrable F (Measure.pi fun _ : Torus d ℓ => (volume : Measure E).toSphere) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable
      (Real.exp (∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖)) (Filter.Eventually.of_forall fun φ => ?_)
    rw [hF, Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have hH : 0 ≤ energy d N ℓ ν h φ := energy_nonneg h hν φ
    have hre : (srcPair g φ).re ≤ ∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖ := by
      unfold srcPair
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hφi : |((φ x : E) i)| ≤ 1 := by
        have := PiLp.norm_apply_le (φ x : E) i
        rw [norm_eq_of_mem_sphere] at this
        simpa using this
      calc (g x i * (((φ x : E) i : ℝ) : ℂ)).re ≤ ‖g x i * (((φ x : E) i : ℝ) : ℂ)‖ :=
            Complex.re_le_norm _
        _ = ‖g x i‖ * |((φ x : E) i)| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖g x i‖ * 1 := mul_le_mul_of_nonneg_left hφi (norm_nonneg _)
        _ = ‖g x i‖ := mul_one _
    rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    have := mul_nonneg hβ hH
    linarith
  have hpart : partitionFunction d N ℓ β ν h g =
      ∫ φ, F φ ∂(Measure.pi fun _ : Torus d ℓ => (volume : Measure E).toSphere) := rfl
  rw [hpart, integral_sphere_pi_sheets h hh F hFm hFi]
  refine Finset.sum_congr rfl fun σ _ => integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  by_cases hall : ∀ x, ‖ξ x‖ < 1
  · have hE := energy_sheetCfg h hh ν σ hall
    simp only [hF, frA]
    change (∏ x, ((chartWeight h (ξ x) : ℝ) : ℂ)) *
        Complex.exp (-((β * energy d N ℓ ν h (sheetCfg h hh σ ξ) : ℝ) : ℂ) +
          srcPair g (sheetCfg h hh σ ξ)) = _
    rw [hE, Complex.ofReal_exp]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · push Not at hall
    obtain ⟨x, hx⟩ := hall
    have hw : chartWeight h (ξ x) = 0 := by unfold chartWeight; rw [ite_eq_right (not_lt.2 hx)]
    simp only [frA]
    rw [Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hw]), zero_mul, zero_mul, mul_zero]

/-! ### (R3): the finite-range Gaussian change of variables -/

/-- **Linear change of variables on the tangent fields** (Bochner form): for invertible `S`,
`∫ f dv = |det S|^{N-1} ∫ f(Sψ) dψ`. -/
theorem integral_tangentVol_matAct (hh : ‖h‖ = 1) (S : Matrix (Torus d ℓ) (Torus d ℓ) ℝ)
    (hS : IsUnit S.det) (f : (Torus d ℓ → perp h) → ℂ) :
    ∫ v, f v ∂(Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))) =
      ((|S.det ^ (N - 1)| : ℝ) : ℂ) *
        ∫ ψ, f (matAct S ψ) ∂(Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))) := by
  set μ := Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))
  set R := matActEquiv (W := perp h) S hS
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  have hdetR : LinearMap.det (R : (Torus d ℓ → perp h) →ₗ[ℝ] (Torus d ℓ → perp h)) =
      S.det ^ (N - 1) := by
    rw [det_matActEquiv, hr]
  have hdet : LinearMap.det (R : (Torus d ℓ → perp h) →ₗ[ℝ] (Torus d ℓ → perp h)) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hemb : MeasurableEmbedding R := (R.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have h1 : ∫ y, f y ∂(Measure.map (R : (Torus d ℓ → perp h) →ₗ[ℝ] (Torus d ℓ → perp h)) μ) =
      ∫ x, f (R x) ∂μ := hemb.integral_map f
  rw [hmap, integral_smul_measure] at h1
  have hpos : 0 < |LinearMap.det (R : (Torus d ℓ → perp h) →ₗ[ℝ] (Torus d ℓ → perp h))| :=
    abs_pos.2 hdet
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h1
  have h2 : ∫ x, f (R x) ∂μ = ∫ ψ, f (matAct S ψ) ∂μ := rfl
  rw [← h2, ← h1, ← hdetR, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, abs_inv,
    mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]

/-- The density of the product of standard Gaussians on the tangent fields. -/
theorem pi_oneSiteGaussian_eq (hh : ‖h‖ = 1) :
    (Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h)) =
      (Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))).withDensity
        (fun ψ => ENNReal.ofReal ((2 * Real.pi) ^ (-((N - 1 : ℕ) * Fintype.card (Torus d ℓ) : ℝ) / 2) *
          Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2))) := by
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  unfold oneSiteGaussian
  rw [pi_withDensity_eq (fun _ : Torus d ℓ => (volume : Measure (perp h)))
    (fun _ x => (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) *
      Real.exp (-(1 / 2) * ‖x‖ ^ 2)) (fun _ => by fun_prop)]
  congr 1
  funext ψ
  rw [← ENNReal.ofReal_prod_of_nonneg (fun x _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), hr, Finset.mul_sum]
  congr 3
  ring

/-- The constant of the finite-range Gaussian change of variables. -/
def frConst (d ℓ N : ℕ) [NeZero ℓ] (β ν : ℝ) (R : ℕ) : ℝ :=
  |((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R).det ^ (N - 1)| *
    (2 * Real.pi) ^ (((N - 1 : ℕ) * Fintype.card (Torus d ℓ) : ℝ) / 2)

theorem isUnit_det_frS {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (R : ℕ) :
    IsUnit ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R).det := by
  have hC : (kf0CR d ℓ ν R).det ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hCu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hq := kf0CR_form_ge (d := d) (m := ℓ) hν R u
    rw [hCu, dotProduct_zero] at hq
    have hc : 0 < (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ := by
      have h1 : 2 * (d : ℝ) / (2 * d + ν) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      have : 0 < Real.sqrt (2 * d + ν) := Real.sqrt_pos.2 (by positivity)
      have : 0 < 1 - 2 * (d : ℝ) / (2 * d + ν) := by linarith
      positivity
    have hu2 : 0 < u ⬝ᵥ u := by
      rw [← sum_sq_eq_dot]
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hu
      exact lt_of_lt_of_le (sq_pos_iff.2 hi)
        (Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i))
    have := mul_pos hc hu2
    linarith
  rw [Matrix.det_smul]
  exact (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Real.sqrt_pos.2 hβ).ne')) hC).isUnit

/-- **The finite-range Gaussian change of variables (R3)**: with `ξ = β^{-1/2} C_R ψ`,
`∫ e^{-(β/2)⟨ξ,Kξ⟩} G(ξ) dξ = c ∫ e^{-½ ∑ Q_R(x,y)⟨ψ_x,ψ_y⟩} G(β^{-1/2} C_R ψ) dγ(ψ)`. -/
theorem integral_gauss_fr (hh : ‖h‖ = 1) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (R : ℕ)
    (G : (Torus d ℓ → perp h) → ℂ) :
    ∫ ξ, ((Real.exp (-(β / 2) * tangentQuad ν ξ) : ℝ) : ℂ) * G ξ
        ∂(Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))) =
      ((frConst d ℓ N β ν R : ℝ) : ℂ) * ∫ ψ, ((Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
          inner ℝ (ψ x : E) (ψ y : E)) : ℝ) : ℂ) * G (frField d ℓ β ν R ψ)
        ∂(Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h)) := by
  rw [integral_tangentVol_matAct h hh _ (isUnit_det_frS hβ hν R)]
  set c : ℝ := (2 * Real.pi) ^ (-((N - 1 : ℕ) * Fintype.card (Torus d ℓ) : ℝ) / 2) with hc
  have hcpos : 0 < c := by positivity
  have hdm : Measurable fun ψ : Torus d ℓ → perp h =>
      ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun x _ =>
        (measurable_norm.comp (measurable_pi_apply x)).pow_const 2))))
  rw [pi_oneSiteGaussian_eq h hh, integral_withDensity_eq_integral_toReal_smul₀
    hdm.aemeasurable (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ ψ : Torus d ℓ → perp h,
      ((Real.exp (-(β / 2) * tangentQuad ν
          (matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) ψ)) : ℝ) : ℂ) *
        G (matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) ψ) =
      ((c⁻¹ : ℝ) : ℂ) * ((ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2))).toReal •
        (((Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
          inner ℝ (ψ x : E) (ψ y : E)) : ℝ) : ℂ) * G (frField d ℓ β ν R ψ))) := by
    intro ψ
    have hq := tangentQuad_frField (d := d) (m := ℓ) (h := h) hβ ν R ψ
    have he : -(β / 2) * tangentQuad ν (frField d ℓ β ν R ψ) =
        -(1 / 2) * ∑ x, ‖ψ x‖ ^ 2 + -(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y *
          inner ℝ (ψ x : E) (ψ y : E) := by
      have : -(β / 2) * tangentQuad ν (frField d ℓ β ν R ψ) =
          -(1 / 2) * (β * tangentQuad ν (frField d ℓ β ν R ψ)) := by ring
      rw [this, hq]; ring
    change ((Real.exp (-(β / 2) * tangentQuad ν (frField d ℓ β ν R ψ)) : ℝ) : ℂ) *
        G (frField d ℓ β ν R ψ) = _
    rw [he, Real.exp_add, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    push_cast
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hcpos.ne'
    field_simp
  simp_rw [hpt]
  rw [integral_const_mul, ← mul_assoc]
  congr 1
  unfold frConst
  rw [hc, Complex.ofReal_mul]
  congr 1
  rw [← Real.rpow_neg (by positivity)]
  congr 2
  ring

end

end Balaban.LargeField.KF0FR
