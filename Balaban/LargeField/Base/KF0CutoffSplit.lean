/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0HoleWalk
public import Balaban.LargeField.Base.KF0GoodGaussian
public import Balaban.LargeField.Base.KF0MeanShell
public import Balaban.LargeField.Base.KF0GoodChart
public import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation cutoff on a region with holes (package W398)

Fixed bad set `D ⊂ (ℤ/m)^d` and good sites `G = Dᶜ` (the subtype `Good D`).  The linked expansion
and the one-scale theorem are NOT proved here.

* (T1) `norm_matAct_kwSqrt_le`: from the nonnegative entries and the row sums of `kwSqrt`
  (`kwSqrt_nonneg_entry`, `kwSqrt_rowSum_le`), `sup ‖ψ_y‖ ≤ p` implies `‖(C_G ψ)_x‖ ≤ p/√ν`.
  `hemiPt_site_bound` is the one-site estimate of the chart; `kwSqrt_cutoff_chart_site`
  gives, for the chart variable `ξ = β^{-1/2} (n + C_G ψ)` (`n = √β · (mean)`, `‖n_x‖ ≤ μ`),
  `‖φ_x - h‖ ≤ √2 (μ + p/√ν)/√β`; `kwSqrt_cutoff_good_sites` is the margin form: with
  `L = log(βa)`, `p = b L`, `μ = 1/(2L)`, `r = A L/√(βν)` and `√ν < √2 (A - √2 b) L²` the site
  is good (`‖φ_x - h‖ < r`).  `norm_scaled_mean_le` links `mean_outside_collars` to `‖n_x‖ ≤ μ`.
* (T2) `oneSiteGaussian`: the standard Gaussian on a finite dimensional real inner product space
  (the one-site factor of `goodGaussian`); `oneSiteGaussian_univ`; `oneSiteGaussian_tail_le`:
  `γ(‖ψ‖ > p) ≤ 2^{n/2} exp(-p²/4)` (the crude exponential-Chebyshev bound).
* (T3) `largeSites`: the set of sites with `‖ψ_x‖ > p`.  `sum_indicator_largeSites` (exact
  pointwise partition), `integral_eq_sum_largeSites`, `measure_largeSites_eq`
  (`τ^{|P|} (1-τ)^{|ι|-|P|}`), `setIntegral_largeSites_le`.
* (T4) `integral_indicator_small_eq`: the conditioned product reference
  `Measure.pi (fun _ => cond γ {‖ψ‖ ≤ p})` and the normalization `(1-τ)^{|ι|}`.
* (T5) non-vacuity instance (`d = m = 3`, `ν = 1/8`, `D = {0}`).
-/

@[expose] public section

open Matrix MeasureTheory
open scoped MatrixOrder

namespace Balaban.LargeField

open SphereChart Balaban.Green

/-! ### T1: the cutoff implication on a region with holes -/

section T1

variable {d m : ℕ} [NeZero m] (D : Finset (Torus d m))

/-- Row-sum bound for the landed `kwSqrt`: `sup ‖ψ_y‖ ≤ p ⟹ ‖(C_G ψ)_x‖ ≤ p/√ν`. -/
theorem norm_matAct_kwSqrt_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {ν : ℝ}
    (hν : 0 < ν) {p : ℝ} (ψ : Good D → W) (hψ : ∀ y, ‖ψ y‖ ≤ p) (x : Good D) :
    ‖matAct (kwSqrt ν D) ψ x‖ ≤ p * (Real.sqrt ν)⁻¹ := by
  unfold matAct
  calc ‖∑ y, kwSqrt ν D x y • ψ y‖ ≤ ∑ y, ‖kwSqrt ν D x y • ψ y‖ := norm_sum_le _ _
    _ ≤ ∑ y, kwSqrt ν D x y * p := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (kwSqrt_nonneg_entry hν x y)]
        exact mul_le_mul_of_nonneg_left (hψ y) (kwSqrt_nonneg_entry hν x y)
    _ = (∑ y, kwSqrt ν D x y) * p := by rw [Finset.sum_mul]
    _ ≤ (Real.sqrt ν)⁻¹ * p :=
        mul_le_mul_of_nonneg_right (kwSqrt_rowSum_le hν x) (le_trans (norm_nonneg _) (hψ x))
    _ = p * (Real.sqrt ν)⁻¹ := mul_comm _ _

/-- The chart estimate at one site: for `‖u‖ < √β` the spin `hemiPt h (β^{-1/2} u)` lies in the
open hemisphere and `‖φ - h‖ ≤ √2 ‖u‖/√β`. -/
theorem hemiPt_site_bound {N : ℕ} {β : ℝ} (hβ : 0 < β) {h : EuclideanSpace ℝ (Fin N)}
    (hh : ‖h‖ = 1) (u : perp h) (hu : ‖u‖ < Real.sqrt β) :
    0 < inner ℝ h ((hemiPt h hh ((Real.sqrt β)⁻¹ • u) : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
        EuclideanSpace ℝ (Fin N)) ∧
      ‖((hemiPt h hh ((Real.sqrt β)⁻¹ • u) : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
        EuclideanSpace ℝ (Fin N)) - h‖ ≤ Real.sqrt 2 * ‖u‖ / Real.sqrt β := by
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hlt : ‖(Real.sqrt β)⁻¹ • u‖ < 1 := (norm_inv_sqrt_smul_lt_one_iff hβ u).2 hu
  refine ⟨inner_hemiPt_pos h hh hlt, ?_⟩
  rw [coe_hemiPt_of_lt h hh hlt]
  have h2 := (norm_sq_hemiE_sub_le hh ((Real.sqrt β)⁻¹ • u) hlt.le).2
  have hn : ‖(Real.sqrt β)⁻¹ • u‖ = ‖u‖ / Real.sqrt β := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hsβ.le]; ring
  rw [hn] at h2
  have hr : 0 ≤ Real.sqrt 2 * ‖u‖ / Real.sqrt β := by positivity
  refine le_of_sq_le_sq ?_ hr
  calc ‖hemiE h ((Real.sqrt β)⁻¹ • u) - h‖ ^ 2 ≤ 2 * (‖u‖ / Real.sqrt β) ^ 2 := h2
    _ = (Real.sqrt 2 * ‖u‖ / Real.sqrt β) ^ 2 := by
        rw [mul_div_assoc, mul_pow, Real.sq_sqrt (by norm_num)]

/-- **T1 (chart form).**  Let `ψ : Good D → h^⊥` with `sup ‖ψ_y‖ ≤ p`, `n : Good D → h^⊥` the scaled
mean `n_x = √β m_x` with `‖n_x‖ ≤ μ`, and `μ + p/√ν < √β`.  The chart variable is
`ξ = β^{-1/2} (n + C_G ψ) = m + β^{-1/2} C_G ψ`.  Then the spin at `x` lies in the open hemisphere
and `‖φ_x - h‖ ≤ √2 (μ + p/√ν)/√β`. -/
theorem kwSqrt_cutoff_chart_site {N : ℕ} {β ν p μ : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (hdom : μ + p * (Real.sqrt ν)⁻¹ < Real.sqrt β)
    (ψ n : Good D → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ p) (x : Good D) (hn : ‖n x‖ ≤ μ) :
    0 < inner ℝ h ((chartCfgOn h hh ((Real.sqrt β)⁻¹ • (n + matAct (kwSqrt ν D) ψ)) x :
        SpinSphere N) : EuclideanSpace ℝ (Fin N)) ∧
      ‖((chartCfgOn h hh ((Real.sqrt β)⁻¹ • (n + matAct (kwSqrt ν D) ψ)) x : SpinSphere N) :
        EuclideanSpace ℝ (Fin N)) - h‖ ≤
        Real.sqrt 2 * (μ + p * (Real.sqrt ν)⁻¹) / Real.sqrt β := by
  have hv : ‖(n + matAct (kwSqrt ν D) ψ) x‖ ≤ μ + p * (Real.sqrt ν)⁻¹ := by
    rw [Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add hn (norm_matAct_kwSqrt_le D hν ψ hψ x))
  have key := hemiPt_site_bound hβ hh ((n + matAct (kwSqrt ν D) ψ) x) (lt_of_le_of_lt hv hdom)
  have e : chartCfgOn h hh ((Real.sqrt β)⁻¹ • (n + matAct (kwSqrt ν D) ψ)) x =
      hemiPt h hh ((Real.sqrt β)⁻¹ • (n + matAct (kwSqrt ν D) ψ) x) := rfl
  rw [e]
  refine ⟨key.1, key.2.trans ?_⟩
  gcongr

/-- **T1 (margin form).**  With `L = log(βa) > 0`, `p = b L`, `‖n_x‖ ≤ μ ≤ 1/(2L)`, the domain
condition `μ + bL/√ν < √β` and the margin inequality `√ν < √2 (A - √2 b) L²`, the spin at `x`
satisfies `‖φ_x - h‖ < (A L/√β)/√ν`, the scaled good radius of `kf0_cutoff_good_sites`.  The
margin is the analogue of `A > √2 b/√ν` of the full-torus model with the extra term `1/(2L)`
of the mean; it holds for `log(βa) ≥ L₁` where `L₁² > √ν/(√2 (A - √2 b))`, i.e. for
`β ≥ exp(L₁)/a`. -/
theorem kwSqrt_cutoff_good_sites {N : ℕ} {β ν a b A μ : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (hβa : 1 < β * a)
    (hμ : μ ≤ 1 / (2 * Real.log (β * a)))
    (hdom : μ + b * Real.log (β * a) * (Real.sqrt ν)⁻¹ < Real.sqrt β)
    (hmargin : Real.sqrt ν < Real.sqrt 2 * (A - Real.sqrt 2 * b) * Real.log (β * a) ^ 2)
    (ψ n : Good D → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ b * Real.log (β * a)) (x : Good D)
    (hn : ‖n x‖ ≤ μ) :
    ‖((chartCfgOn h hh ((Real.sqrt β)⁻¹ • (n + matAct (kwSqrt ν D) ψ)) x : SpinSphere N) :
        EuclideanSpace ℝ (Fin N)) - h‖ <
      (A * Real.log (β * a) / Real.sqrt β) / Real.sqrt ν := by
  have hL : 0 < Real.log (β * a) := Real.log_pos hβa
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h1 := (kwSqrt_cutoff_chart_site D hβ hν hh hdom ψ n hψ x hn).2
  refine lt_of_le_of_lt h1 ?_
  set L := Real.log (β * a)
  set s := Real.sqrt ν
  have h2 : Real.sqrt 2 * (μ + b * L * s⁻¹) < A * L / s := by
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs20 : 0 < Real.sqrt 2 := by positivity
    -- multiply by `s * L > 0`
    have hμL : 2 * L * μ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ 2 * L)
      rwa [show 2 * L * (1 / (2 * L)) = 1 by field_simp] at this
    have hc : Real.sqrt 2 * s * (2 * L * μ) ≤ Real.sqrt 2 * s := by
      have : 0 ≤ Real.sqrt 2 * s := by positivity
      nlinarith
    have hm2 : Real.sqrt 2 * s < 2 * (A - Real.sqrt 2 * b) * L ^ 2 := by
      nlinarith
    have hfin : (Real.sqrt 2 * μ * s + Real.sqrt 2 * b * L) * L < A * L * L := by
      nlinarith [hm2, hc, hs2, mul_pos hL hL]
    have hfin' : Real.sqrt 2 * μ * s + Real.sqrt 2 * b * L < A * L :=
      lt_of_mul_lt_mul_right (by linarith) hL.le
    rw [lt_div_iff₀ hsν]
    calc Real.sqrt 2 * (μ + b * L * s⁻¹) * s
        = Real.sqrt 2 * μ * s + Real.sqrt 2 * b * L := by field_simp
      _ < A * L := hfin'
  rw [div_div, mul_comm (Real.sqrt β) s, ← div_div]
  rw [show Real.sqrt 2 * (μ + b * L * s⁻¹) / Real.sqrt β =
      (Real.sqrt 2 * (μ + b * L * s⁻¹)) / Real.sqrt β from rfl]
  rw [div_div, show A * L / (s * Real.sqrt β) = (A * L / s) / Real.sqrt β by
    rw [div_div]]
  exact div_lt_div_of_pos_right h2 hsβ

/-- The scaled mean is at most `1/(2 log(βa))` when `√β |c| ≤ 1/(2 log(βa))` (the conclusion of
`mean_outside_collars`, which is scalar valued) and the direction `e` has norm at most one. -/
theorem norm_scaled_mean_le {N : ℕ} {β L c : ℝ} {h : EuclideanSpace ℝ (Fin N)}
    (e : perp h) (he : ‖e‖ ≤ 1) (hc : Real.sqrt β * |c| ≤ 1 / (2 * L)) :
    ‖(Real.sqrt β * c) • e‖ ≤ 1 / (2 * L) := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg β)]
  calc Real.sqrt β * |c| * ‖e‖ ≤ Real.sqrt β * |c| * 1 :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ 1 / (2 * L) := by rwa [mul_one]

end T1

/-! ### T2: the Gaussian tail -/

section T2

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The standard Gaussian probability measure on a finite dimensional real inner product space
(the one-site factor of `goodGaussian`): density `(2π)^{-n/2} exp(-‖x‖²/2)` against the volume. -/
noncomputable def oneSiteGaussian : Measure E :=
  (volume : Measure E).withDensity fun x =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-(1 / 2) * ‖x‖ ^ 2))

variable {E}

theorem integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : E => Real.exp (-b * ‖v‖ ^ 2)) := by
  by_contra hni
  have h0 := integral_undef hni
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb] at h0
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne' h0

theorem lintegral_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ v : E, ENNReal.ofReal (c * Real.exp (-b * ‖v‖ ^ 2)) =
      ENNReal.ofReal (c * (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_sq_norm hb).const_mul c)
    (Filter.Eventually.of_forall fun v => by positivity),
    integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hb]

/-- The standard Gaussian has total mass one. -/
theorem oneSiteGaussian_univ : oneSiteGaussian E Set.univ = 1 := by
  unfold oneSiteGaussian
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    show (fun x : E => ENNReal.ofReal ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-(1 / 2) * ‖x‖ ^ 2))) = fun x : E => ENNReal.ofReal
        ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) from rfl,
    lintegral_exp_neg_mul_sq_norm (b := 1 / 2) (by norm_num) (by positivity)]
  rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring, ← Real.rpow_add (by positivity)]
  rw [show -(Module.finrank ℝ E : ℝ) / 2 + (Module.finrank ℝ E : ℝ) / 2 = 0 by ring]
  simp

instance : IsProbabilityMeasure (oneSiteGaussian E) := ⟨oneSiteGaussian_univ⟩

/-- **T2 (crude Gaussian tail; proved).**  `γ_n(‖ψ‖ > p) ≤ 2^{n/2} exp(-p²/4)`, `n = dim E`, by
exponential Chebyshev with `E exp(‖ψ‖²/4) = 2^{n/2}`.  Mathlib inputs: `withDensity_apply`,
`GaussianFourier.integral_rexp_neg_mul_sq_norm`, `ofReal_integral_eq_lintegral_ofReal`. -/
theorem oneSiteGaussian_tail_le {p : ℝ} (hp0 : 0 ≤ p) :
    oneSiteGaussian E {x | p < ‖x‖} ≤
      ENNReal.ofReal (2 ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.exp (-p ^ 2 / 4)) := by
  have hms : MeasurableSet {x : E | p < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  unfold oneSiteGaussian
  rw [withDensity_apply _ hms]
  set c : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpp : ∀ x ∈ {x : E | p < ‖x‖}, ENNReal.ofReal (c * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) ≤
      ENNReal.ofReal (c * Real.exp (-p ^ 2 / 4) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hx' : p ^ 2 ≤ ‖x‖ ^ 2 := by
      exact pow_le_pow_left₀ hp0 (le_of_lt hx) 2
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0
    nlinarith
  calc ∫⁻ x in {x : E | p < ‖x‖}, ENNReal.ofReal (c * Real.exp (-(1 / 2) * ‖x‖ ^ 2))
      ≤ ∫⁻ x in {x : E | p < ‖x‖},
          ENNReal.ofReal (c * Real.exp (-p ^ 2 / 4) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) :=
        setLIntegral_mono' hms hpp
    _ ≤ ∫⁻ x : E, ENNReal.ofReal (c * Real.exp (-p ^ 2 / 4) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (c * Real.exp (-p ^ 2 / 4) *
          (Real.pi / (1 / 4)) ^ ((Module.finrank ℝ E : ℝ) / 2)) :=
        lintegral_exp_neg_mul_sq_norm (b := 1 / 4) (by norm_num) (by positivity)
    _ = ENNReal.ofReal (2 ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.exp (-p ^ 2 / 4)) := by
        congr 1
        have : c * (Real.pi / (1 / 4)) ^ ((Module.finrank ℝ E : ℝ) / 2) =
            2 ^ ((Module.finrank ℝ E : ℝ) / 2) := by
          have h2π : 0 < 2 * Real.pi := by positivity
          have e1 : Real.pi / (1 / 4) = 2 * (2 * Real.pi) := by ring
          have e2 : -(Module.finrank ℝ E : ℝ) / 2 = -((Module.finrank ℝ E : ℝ) / 2) := by ring
          rw [hc, e1, e2, Real.rpow_neg h2π.le, Real.mul_rpow (by norm_num) h2π.le]
          have : 0 < (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos h2π _
          field_simp
        rw [mul_right_comm, this]

end T2

/-! ### T3 and T4: the exact partition by the large sites and the conditioned reference -/

section T3

open scoped Classical

variable {ι W : Type*} [Fintype ι] [NormedAddCommGroup W]

/-- The one-site event "fluctuation large": `‖w‖ > p`. -/
def largeSet (p : ℝ) : Set W := {w | p < ‖w‖}

/-- The one-site event "fluctuation small": `‖w‖ ≤ p`. -/
def smallSet (p : ℝ) : Set W := {w | ‖w‖ ≤ p}

theorem smallSet_eq_compl (p : ℝ) : smallSet p = (largeSet p : Set W)ᶜ := by
  ext w; simp [smallSet, largeSet]

theorem measurableSet_largeSet [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] (p : ℝ) : MeasurableSet (largeSet p : Set W) :=
  measurableSet_lt measurable_const measurable_norm

theorem measurableSet_smallSet [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] (p : ℝ) : MeasurableSet (smallSet p : Set W) := by
  rw [smallSet_eq_compl]; exact (measurableSet_largeSet p).compl

/-- The set of sites at which the fluctuation field is large. -/
noncomputable def largeSites (p : ℝ) (ψ : ι → W) : Finset ι :=
  Finset.univ.filter fun x => p < ‖ψ x‖

theorem largeSites_eq_iff (p : ℝ) (ψ : ι → W) (P : Finset ι) :
    largeSites p ψ = P ↔ ∀ x, x ∈ P ↔ p < ‖ψ x‖ := by
  constructor
  · rintro rfl x; simp [largeSites]
  · intro h; ext x; simp [largeSites, h x]

theorem setOf_largeSites_eq (p : ℝ) (P : Finset ι) :
    {ψ : ι → W | largeSites p ψ = P} =
      Set.pi Set.univ fun x => if x ∈ P then largeSet p else smallSet p := by
  ext ψ
  rw [Set.mem_ofPred_eq, largeSites_eq_iff, Set.mem_univ_pi]
  refine forall_congr' fun x => ?_
  by_cases hx : x ∈ P <;> simp [hx, largeSet, smallSet, not_lt]

theorem measurableSet_setOf_largeSites [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] (p : ℝ) (P : Finset ι) :
    MeasurableSet {ψ : ι → W | largeSites p ψ = P} := by
  rw [setOf_largeSites_eq]
  refine MeasurableSet.univ_pi fun x => ?_
  split_ifs
  · exact measurableSet_largeSet p
  · exact measurableSet_smallSet p

/-- **T3 (pointwise partition).**  `F ψ = ∑_P 1{large sites of ψ are exactly P} F ψ`. -/
theorem sum_indicator_largeSites (p : ℝ) (F : (ι → W) → ℝ) (ψ : ι → W) :
    ∑ P : Finset ι, Set.indicator {ψ : ι → W | largeSites p ψ = P} F ψ = F ψ := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_ite_eq]; simp

/-- **T3 (integral partition).** -/
theorem integral_eq_sum_largeSites [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] (μ : Measure (ι → W)) (p : ℝ) {F : (ι → W) → ℝ}
    (hF : Integrable F μ) :
    ∫ ψ, F ψ ∂μ = ∑ P : Finset ι, ∫ ψ in {ψ : ι → W | largeSites p ψ = P}, F ψ ∂μ := by
  have : (fun ψ => F ψ) = fun ψ => ∑ P : Finset ι,
      Set.indicator {ψ : ι → W | largeSites p ψ = P} F ψ :=
    funext fun ψ => (sum_indicator_largeSites p F ψ).symm
  conv_lhs => rw [this]
  rw [integral_finsetSum _ fun P _ => hF.indicator (measurableSet_setOf_largeSites p P)]
  exact Finset.sum_congr rfl fun P _ => integral_indicator (measurableSet_setOf_largeSites p P)

variable [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W] (γ : Measure W) [IsProbabilityMeasure γ]

/-- **T3 (weight of a given large set).**  For the product measure, with
`τ = γ(‖ψ‖ > p)`: `(⊗γ)(large sites exactly P) = τ^{|P|} (1-τ)^{|ι|-|P|}`. -/
theorem measure_setOf_largeSites (p : ℝ) (P : Finset ι) :
    (Measure.pi fun _ : ι => γ) {ψ : ι → W | largeSites p ψ = P} =
      (γ (largeSet p)) ^ P.card * (1 - γ (largeSet p)) ^ (Fintype.card ι - P.card) := by
  rw [setOf_largeSites_eq, Measure.pi_pi]
  have h1 : γ (smallSet p) = 1 - γ (largeSet p) := by
    rw [smallSet_eq_compl]; exact prob_compl_eq_one_sub (measurableSet_largeSet p)
  have : ∀ x : ι, γ (if x ∈ P then largeSet p else smallSet p) =
      if x ∈ P then γ (largeSet p) else 1 - γ (largeSet p) := fun x => by
    split_ifs <;> simp [h1]
  simp only [this]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ]

/-- **T3 (bounded integrand on a given large set).**  If `0 ≤ F ≤ M` then
`∫_{large sites exactly P} F d⊗γ ≤ M τ^{|P|}`, with `τ = γ(‖ψ‖ > p)` real. -/
theorem setIntegral_largeSites_le (p : ℝ) (P : Finset ι) {F : (ι → W) → ℝ} {M : ℝ}
    (hF : ∀ ψ, ‖F ψ‖ ≤ M) :
    ∫ ψ in {ψ : ι → W | largeSites p ψ = P}, F ψ ∂(Measure.pi fun _ : ι => γ) ≤
      M * (γ.real (largeSet p)) ^ P.card := by
  have hμ : (Measure.pi fun _ : ι => γ).real {ψ : ι → W | largeSites p ψ = P} ≤
      (γ.real (largeSet p)) ^ P.card := by
    unfold Measure.real
    rw [measure_setOf_largeSites γ p P]
    have hτ : γ (largeSet p) ≠ ⊤ := measure_ne_top _ _
    have hτ1 : 1 - γ (largeSet p) ≤ 1 := tsub_le_self
    have hle : (γ (largeSet p)) ^ P.card * (1 - γ (largeSet p)) ^ (Fintype.card ι - P.card) ≤
        (γ (largeSet p)) ^ P.card := by
      calc _ ≤ (γ (largeSet p)) ^ P.card * 1 := by
            gcongr
            exact pow_le_one' hτ1 _
        _ = _ := mul_one _
    calc _ ≤ ((γ (largeSet p)) ^ P.card).toReal := ENNReal.toReal_mono (ENNReal.pow_ne_top hτ) hle
      _ = _ := by rw [ENNReal.toReal_pow]
  refine ((Real.le_norm_self _).trans (norm_setIntegral_le_of_norm_le_const (C := M) ?_ ?_)).trans ?_
  · exact measure_lt_top _ _
  · intro ψ _; exact hF ψ
  · calc (M * (Measure.pi fun _ : ι => γ).real {ψ : ι → W | largeSites p ψ = P}) ≤
        M * (γ.real (largeSet p)) ^ P.card := by
          gcongr
          exact le_trans (norm_nonneg _) (hF (fun _ => 0))

end T3

end Balaban.LargeField
