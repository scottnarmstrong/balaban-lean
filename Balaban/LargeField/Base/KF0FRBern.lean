/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRTerms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRBern`: the partition function as the expectation of the product of the terms (route FR,
(R4))

`notes/phase1/KF0-FR.md` (R4). The whitened chart integrand of each sheet configuration is
integrable for the product of standard Gaussians (`integrable_frG`: the defect form is dominated by
`½ θ |ψ|²` when the rows of `|Q_R|` sum to at most `θ ≤ 1`, and the chart weights are integrated by
`lintegral_prod_matAct_add`). The sum over the sheets is then the expectation for the Bernoulli
law `π_ε` with the compensating weights `b` (`sum_sheets_eq_integral`), and

`Z(g) = c (1+ε)^{|Λ|} e^{⟨g,h⟩} ∫ ∏_t F_t dμ` (`partitionFunction_eq_terms`).
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

local notation "E" => EuclideanSpace ℝ (Fin N)
local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

variable {d ℓ : ℕ} [NeZero ℓ]

/-! ### Bounds of the integrand -/

theorem frV_nonneg {ν : ℝ} (hν : 0 ≤ ν) (σ : Torus d ℓ → Bool) (ξ : Torus d ℓ → perp h) :
    0 ≤ frV h ν σ ξ := by
  unfold frV
  refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun μ _ => sq_nonneg _)) (mul_nonneg (by linarith) (Finset.sum_nonneg
      fun x _ => sq_nonneg _))

theorem re_srcPair_le (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → Sph) :
    (srcPair g φ).re ≤ ∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖ := by
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

/-- `|A_σ(ξ; g)| ≤ ∏_x w(ξ_x) · e^{‖g‖₁}`. -/
theorem norm_frA_le (hh : ‖h‖ = 1) {β ν : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν) (σ : Torus d ℓ → Bool)
    (g : Torus d ℓ → Fin N → ℂ) (ξ : Torus d ℓ → perp h) :
    ‖frA h hh β ν σ g ξ‖ ≤
      (∏ x, chartWeight h (ξ x)) * Real.exp (∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖) := by
  unfold frA
  rw [norm_mul, Complex.norm_exp, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.prod_congr rfl fun x _ => abs_of_nonneg (chartWeight_nonneg h (ξ x))]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
    (Finset.prod_nonneg fun x _ => chartWeight_nonneg h (ξ x))
  rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  have h1 := mul_nonneg hβ (frV_nonneg h hν σ ξ)
  have h2 := re_srcPair_le g (sheetCfg h hh σ ξ)
  linarith

/-- The defect form is dominated by `½ θ |ψ|²` when the rows of `|Q_R|` sum to at most `θ`. -/
theorem neg_frQ_form_le {ν : ℝ} (R : ℕ) {θ : ℝ} (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ)
    (ψ : Torus d ℓ → perp h) :
    -(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E) ≤
      (1 / 2) * θ * ∑ x, ‖ψ x‖ ^ 2 := by
  have hpt : ∀ x y, -(frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) ≤
      |frQ d ℓ ν R x y| * ((‖ψ x‖ ^ 2 + ‖ψ y‖ ^ 2) / 2) := by
    intro x y
    have hin : |inner ℝ (ψ x : E) (ψ y : E)| ≤ (‖ψ x‖ ^ 2 + ‖ψ y‖ ^ 2) / 2 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      simp only [norm_coe_perp]
      nlinarith [sq_nonneg (‖ψ x‖ - ‖ψ y‖)]
    calc -(frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E))
        ≤ |frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)| := neg_le_abs _
      _ = |frQ d ℓ ν R x y| * |inner ℝ (ψ x : E) (ψ y : E)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hin (abs_nonneg _)
  have hsum : -(∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) ≤
      ∑ x, ∑ y, |frQ d ℓ ν R x y| * ((‖ψ x‖ ^ 2 + ‖ψ y‖ ^ 2) / 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun x _ => by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_le_sum fun y _ => hpt x y
  have hsplit : ∑ x, ∑ y, |frQ d ℓ ν R x y| * ((‖ψ x‖ ^ 2 + ‖ψ y‖ ^ 2) / 2) =
      (1 / 2) * ∑ x, ‖ψ x‖ ^ 2 * ∑ y, |frQ d ℓ ν R x y| +
        (1 / 2) * ∑ y, ‖ψ y‖ ^ 2 * ∑ x, |frQ d ℓ ν R y x| := by
    have e1 : ∑ x, ∑ y, |frQ d ℓ ν R x y| * ((‖ψ x‖ ^ 2 + ‖ψ y‖ ^ 2) / 2) =
        (1 / 2) * ∑ x, ∑ y, |frQ d ℓ ν R x y| * ‖ψ x‖ ^ 2 +
          (1 / 2) * ∑ x, ∑ y, |frQ d ℓ ν R x y| * ‖ψ y‖ ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e1]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    · congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [frQ_symm ν R x y]; ring
  have hθ : ∀ x, ‖ψ x‖ ^ 2 * ∑ y, |frQ d ℓ ν R x y| ≤ ‖ψ x‖ ^ 2 * θ := fun x =>
    mul_le_mul_of_nonneg_left (hQ x) (sq_nonneg _)
  have h3 : ∑ x, ‖ψ x‖ ^ 2 * ∑ y, |frQ d ℓ ν R x y| ≤ θ * ∑ x, ‖ψ x‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => (hθ x).trans (le_of_eq (mul_comm _ _))
  rw [hsplit] at hsum
  linarith

/-! ### Integrability of the whitened chart integrand -/

/-- The whitened chart integrand of the sheet configuration `σ`. -/
def frG (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (σ : Torus d ℓ → Bool) (g : Torus d ℓ → Fin N → ℂ)
    (ψ : Torus d ℓ → perp h) : ℂ :=
  ((Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) : ℝ) : ℂ) *
    frA h hh β ν σ g (frField d ℓ β ν R ψ)

theorem measurable_frField (β ν : ℝ) (R : ℕ) :
    Measurable (frField (h := h) d ℓ β ν R) :=
  (LinearMap.continuous_of_finiteDimensional
    (matActL (W := perp h) ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R))).measurable

theorem measurable_frG (hh : ‖h‖ = 1) (β ν : ℝ) (R : ℕ) (σ : Torus d ℓ → Bool)
    (g : Torus d ℓ → Fin N → ℂ) : Measurable (frG h hh β ν R σ g) := by
  unfold frG
  refine Measurable.mul (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul ?_))) ((measurable_frA h hh β ν σ g).comp (measurable_frField h β ν R))
  refine Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_
  refine measurable_const.mul ?_
  exact (measurable_subtype_coe.comp (measurable_pi_apply x)).inner
    (measurable_subtype_coe.comp (measurable_pi_apply y))

/-- **Integrability of the whitened chart integrand** (rows of `|Q_R|` summing to at most `1`). -/
theorem integrable_frG (hh : ‖h‖ = 1) {β ν : ℝ} (hβ : 0 < β) (hν : 0 < ν) (R : ℕ)
    (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ 1) (σ : Torus d ℓ → Bool) (g : Torus d ℓ → Fin N → ℂ) :
    Integrable (frG h hh β ν R σ g) (Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h)) := by
  refine ⟨(measurable_frG h hh β ν R σ g).aestronglyMeasurable, ?_⟩
  set c : ℝ := (2 * Real.pi) ^ (-((N - 1 : ℕ) * Fintype.card (Torus d ℓ) : ℝ) / 2) with hc
  set Cg : ℝ := Real.exp (∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖) with hCg
  have hdm : Measurable fun ψ : Torus d ℓ → perp h =>
      ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun x _ =>
        (measurable_norm.comp (measurable_pi_apply x)).pow_const 2))))
  unfold HasFiniteIntegral
  rw [pi_oneSiteGaussian_eq h hh, lintegral_withDensity_eq_lintegral_mul₀ hdm.aemeasurable
    (measurable_frG h hh β ν R σ g).enorm.aemeasurable]
  have hpt : ∀ ψ : Torus d ℓ → perp h,
      (ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) *
        ‖frG h hh β ν R σ g ψ‖ₑ) ≤
      ENNReal.ofReal (c * Cg) * ∏ x, ENNReal.ofReal
        (chartWeight h (matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) ψ x + 0)) := by
    intro ψ
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_prod_of_nonneg (fun x _ => chartWeight_nonneg h _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [add_zero]
    have hA := norm_frA_le h hh hβ.le hν.le σ g (frField d ℓ β ν R ψ)
    have hQf := neg_frQ_form_le (h := h) (d := d) (ℓ := ℓ) (ν := ν) R hQ ψ
    unfold frG
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hW0 : 0 ≤ ∏ x, chartWeight h (frField d ℓ β ν R ψ x) :=
      Finset.prod_nonneg fun x _ => chartWeight_nonneg h _
    have he : Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2) *
        Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]
      linarith
    calc c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2) *
          (Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) *
            ‖frA h hh β ν σ g (frField d ℓ β ν R ψ)‖)
        ≤ c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2) *
          (Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E)) *
            ((∏ x, chartWeight h (frField d ℓ β ν R ψ x)) * Cg)) := by gcongr
      _ = c * (Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2) *
          Real.exp (-(1 / 2) * ∑ x, ∑ y, frQ d ℓ ν R x y * inner ℝ (ψ x : E) (ψ y : E))) *
            ((∏ x, chartWeight h (frField d ℓ β ν R ψ x)) * Cg) := by ring
      _ ≤ c * 1 * ((∏ x, chartWeight h (frField d ℓ β ν R ψ x)) * Cg) := by gcongr
      _ = c * Cg * ∏ x, chartWeight h (frField d ℓ β ν R ψ x) := by ring
  calc ∫⁻ ψ, ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) *
        ‖frG h hh β ν R σ g ψ‖ₑ ∂(Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h)))
      ≤ ∫⁻ ψ, ENNReal.ofReal (c * Cg) * ∏ x, ENNReal.ofReal
          (chartWeight h (matAct ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R) ψ x + 0))
          ∂(Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))) := lintegral_mono hpt
    _ = ENNReal.ofReal (c * Cg) * ((ENNReal.ofReal
          |((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R).det ^ (N - 1)|)⁻¹ *
          (∫⁻ v, ENNReal.ofReal (chartWeight h v)) ^ Fintype.card (Torus d ℓ)) := by
        rw [lintegral_const_mul _ (by
          refine Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
            ((measurable_chartWeight h).comp ?_)
          exact (measurable_add_const _).comp ((measurable_pi_apply x).comp
            (LinearMap.continuous_of_finiteDimensional
              (matActL (W := perp h) ((Real.sqrt β)⁻¹ • kf0CR d ℓ ν R))).measurable))]
        rw [lintegral_prod_matAct_add h hh _ (isUnit_det_frS hβ hν R) (fun _ => 0)
          (fun v => ENNReal.ofReal (chartWeight h v))
          (ENNReal.measurable_ofReal.comp (measurable_chartWeight h))]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ?_
          (ENNReal.pow_lt_top (lintegral_chartWeight_lt_top h hh)))
        rw [ENNReal.inv_lt_top, ENNReal.ofReal_pos]
        exact abs_pos.2 (pow_ne_zero _ (isUnit_det_frS hβ hν R).ne_zero)

/-! ### The sum over the sheets as an expectation -/

theorem frBern_real_mul_bW {ε : ℝ} (hε : 0 < ε) (b : Bool) :
    (frBern ε).real {b} * bW ε b = 1 / (1 + ε) := by
  cases b
  · rw [measureReal_def, frBern_false, ENNReal.toReal_ofReal (by positivity)]
    simp only [bW, Bool.false_eq_true, ↓reduceIte]
    field_simp
  · rw [measureReal_def, frBern_true, ENNReal.toReal_ofReal (by positivity)]
    simp [bW]

/-- **The sum over the sheets as an expectation (R4)**: for integrable `G σ`,
`∑_σ ∫ G_σ dγ = (1+ε)^{|Λ|} ∫ G_{σ(ω)}(ψ(ω)) ∏_x b(σ_x) dμ(ω)`. -/
theorem sum_sheets_eq_integral {ε : ℝ} (hε : 0 < ε)
    (G : (Torus d ℓ → Bool) → (Torus d ℓ → perp h) → ℂ) (hGm : ∀ σ, Measurable (G σ))
    (hG : ∀ σ, Integrable (G σ) (Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h))) :
    ∑ σ : Torus d ℓ → Bool, ∫ ψ, G σ ψ ∂(Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h)) =
      ((1 + ε) ^ Fintype.card (Torus d ℓ) : ℂ) *
        ∫ ω, G (frSig h ω) (frPsi h ω) * ((∏ x, bW ε (frSig h ω x) : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Torus d ℓ => frSiteMeasure h ε) := by
  have hπ : IsProbabilityMeasure (frBern ε) := isProbabilityMeasure_frBern hε.le
  set γ := Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h)
  set π := Measure.pi fun _ : Torus d ℓ => frBern ε
  set F' : (Torus d ℓ → perp h) × (Torus d ℓ → Bool) → ℂ := fun p =>
    G p.2 p.1 * ((∏ x, bW ε (p.2 x) : ℝ) : ℂ) with hF'
  have hmp := measurePreserving_arrowProdEquivProdArrow (perp h) Bool (Torus d ℓ)
    (fun _ => oneSiteGaussian (perp h)) (fun _ => frBern ε)
  have hcomp : ∫ ω, G (frSig h ω) (frPsi h ω) * ((∏ x, bW ε (frSig h ω x) : ℝ) : ℂ)
      ∂(Measure.pi fun _ : Torus d ℓ => frSiteMeasure h ε) = ∫ p, F' p ∂(γ.prod π) := by
    rw [← hmp.integral_comp' F']
    rfl
  have hF'm : Measurable F' := by
    have hm : ∀ σ, Measurable fun p : (Torus d ℓ → perp h) × (Torus d ℓ → Bool) =>
        (if p.2 = σ then G σ p.1 * ((∏ x, bW ε (σ x) : ℝ) : ℂ) else 0) := fun σ =>
      Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
        (((hGm σ).comp measurable_fst).mul measurable_const) measurable_const
    have : F' = fun p => ∑ σ : Torus d ℓ → Bool,
        (if p.2 = σ then G σ p.1 * ((∏ x, bW ε (σ x) : ℝ) : ℂ) else 0) := by
      funext p
      rw [Finset.sum_ite_eq]
      simp [hF']
    rw [this]
    exact Finset.measurable_sum _ fun σ _ => hm σ
  have hint : Integrable F' (γ.prod π) := by
    rw [integrable_prod_iff hF'm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun ψ => Integrable.of_finite, ?_⟩
    have : (fun ψ => ∫ σ, ‖F' (ψ, σ)‖ ∂π) = fun ψ => ∑ σ : Torus d ℓ → Bool,
        π.real {σ} • ‖F' (ψ, σ)‖ := by
      funext ψ; exact integral_fintype Integrable.of_finite
    rw [this]
    refine integrable_finsetSum _ fun σ _ => ?_
    simp only [smul_eq_mul, hF', norm_mul]
    exact ((hG σ).norm.mul_const _).const_mul _
  rw [hcomp, integral_prod F' hint]
  have hinner : ∀ ψ, ∫ σ, F' (ψ, σ) ∂π =
      ((1 + ε) ^ Fintype.card (Torus d ℓ) : ℂ)⁻¹ * ∑ σ : Torus d ℓ → Bool, G σ ψ := by
    intro ψ
    rw [integral_fintype Integrable.of_finite, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hπσ : π.real {σ} * ∏ x, bW ε (σ x) = ((1 + ε) ^ Fintype.card (Torus d ℓ))⁻¹ := by
      rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
      simp_rw [← measureReal_def, frBern_real_mul_bW hε]
      rw [Finset.prod_const, Finset.card_univ, div_pow, one_pow, one_div]
    simp only [hF', Complex.real_smul]
    have hc : (π.real {σ} : ℂ) * (G σ ψ * ((∏ x, bW ε (σ x) : ℝ) : ℂ)) =
        ((π.real {σ} * ∏ x, bW ε (σ x) : ℝ) : ℂ) * G σ ψ := by push_cast; ring
    rw [hc, hπσ]
    push_cast
    ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_finsetSum _ fun σ _ => hG σ, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact pow_ne_zero _ (by
    have : (1 : ℂ) + ε = ((1 + ε : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_ne_zero]; linarith)

/-! ### The partition function -/

/-- **The partition function as the expectation of the product of the terms**:
`Z(g) = c (1+ε)^{|Λ|} e^{⟨g,h⟩} ∫ ∏_t F_t dμ`, for every complex source, when the rows of the
defect `|Q_R|` sum to at most `1`. -/
theorem partitionFunction_eq_terms (hh : ‖h‖ = 1) {β ν ε : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    (hε : 0 < ε) (R : ℕ) (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ 1) (g : Torus d ℓ → Fin N → ℂ) :
    partitionFunction d N ℓ β ν h g =
      ((frConst d ℓ N β ν R * (1 + ε) ^ Fintype.card (Torus d ℓ) : ℝ) : ℂ) *
        Complex.exp (∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (h i : ℂ)) *
        ∫ ω, ∏ t : FRTerm d ℓ, frF h hh β ν ε R g t ω
          ∂(Measure.pi fun _ : Torus d ℓ => frSiteMeasure h ε) := by
  rw [partitionFunction_eq_sheets h hh hβ.le hν.le g]
  have hσ : ∀ σ : Torus d ℓ → Bool, ∫ ξ : Torus d ℓ → perp h,
      ((Real.exp (-(β / 2) * tangentQuad ν ξ) : ℝ) : ℂ) * frA h hh β ν σ g ξ
        ∂(Measure.pi fun _ => (volume : Measure (perp h))) =
      ((frConst d ℓ N β ν R : ℝ) : ℂ) *
        ∫ ψ, frG h hh β ν R σ g ψ ∂(Measure.pi fun _ : Torus d ℓ => oneSiteGaussian (perp h)) :=
    fun σ => integral_gauss_fr h hh hβ hν R (frA h hh β ν σ g)
  simp_rw [hσ]
  rw [← Finset.mul_sum, sum_sheets_eq_integral h hε (fun σ => frG h hh β ν R σ g)
    (fun σ => measurable_frG h hh β ν R σ g) (fun σ => integrable_frG h hh hβ hν R hQ σ g)]
  have hpt : ∀ ω : Torus d ℓ → perp h × Bool,
      frG h hh β ν R (frSig h ω) g (frPsi h ω) * ((∏ x, bW ε (frSig h ω x) : ℝ) : ℂ) =
        Complex.exp (∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (h i : ℂ)) *
          ∏ t : FRTerm d ℓ, frF h hh β ν ε R g t ω := fun ω => prod_frF_eq h hh β ν ε R g ω
  simp_rw [hpt]
  rw [integral_const_mul]
  push_cast
  ring

end

end Balaban.LargeField.KF0FR
