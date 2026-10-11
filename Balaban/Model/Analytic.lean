/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.Derivatives
public import Balaban.Analysis.AnalyticLimit

/-!
# Analyticity of the partition function and of its logarithm (Lemma 0.1)

Mathlib has no several-variable "complex differentiable implies analytic".  We prove that
`g ↦ ∫ c(φ) exp(-β H(φ) + ⟨g, φ⟩) dμ` is analytic by a uniform limit of the polynomials obtained
from the partial sums of the exponential series (`Balaban.Analysis.analyticAt_of_tendstoUniformlyOn_ball`):
the `m`-th moment `y ↦ ∫ w ⟨y, φ⟩^m` is a finite sum of monomials in the coordinates of `y`.
-/

@[expose] public section

namespace Balaban

open MeasureTheory

variable {d N ℓ : ℕ} [NeZero ℓ]

theorem norm_sourcePairing_le (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) :
    ‖sourcePairing g φ‖ ≤ ∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖ := by
  unfold sourcePairing
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real]
  have : ‖(φ x : EuclideanSpace ℝ (Fin N)) i‖ ≤ 1 := by
    calc ‖(φ x : EuclideanSpace ℝ (Fin N)) i‖ ≤ ‖(φ x : EuclideanSpace ℝ (Fin N))‖ :=
          PiLp.norm_apply_le _ i
      _ = 1 := by simp
  nlinarith [norm_nonneg (g x i)]

theorem norm_sourcePairing_le_mul (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) :
    ‖sourcePairing g φ‖ ≤ (Fintype.card (Torus d ℓ) * N : ℝ) * ‖g‖ := by
  refine (norm_sourcePairing_le g φ).trans ?_
  calc ∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖ ≤ ∑ x : Torus d ℓ, ∑ _i : Fin N, ‖g‖ :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun i _ =>
          (norm_le_pi_norm (g x) i).trans (norm_le_pi_norm g x)
    _ = (Fintype.card (Torus d ℓ) * N : ℝ) * ‖g‖ := by simp; ring

/-- The coordinates of the spins, indexed by sites and components. -/
noncomputable def spinCoordC (a : Torus d ℓ × Fin N) (φ : Torus d ℓ → SpinSphere N) : ℂ :=
  (((φ a.1 : EuclideanSpace ℝ (Fin N)) a.2 : ℝ) : ℂ)

omit [NeZero ℓ] in
theorem continuous_spinCoordC (a : Torus d ℓ × Fin N) :
    Continuous (spinCoordC a : (Torus d ℓ → SpinSphere N) → ℂ) :=
  Complex.continuous_ofReal.comp (continuous_spin_coord a.1 a.2)

theorem sourcePairing_eq_sum (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) :
    sourcePairing g φ = ∑ a : Torus d ℓ × Fin N, g a.1 a.2 * spinCoordC a φ := by
  rw [Fintype.sum_prod_type]
  rfl

theorem sourcePairing_pow (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) (m : ℕ) :
    sourcePairing g φ ^ m =
      ∑ p ∈ Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Torus d ℓ × Fin N)),
        (∏ j, g (p j).1 (p j).2) * ∏ j, spinCoordC (p j) φ := by
  rw [sourcePairing_eq_sum, ← Fin.prod_const, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]

/-- The `m`-th moment `y ↦ ∫ w ⟨y, φ⟩^m` is analytic (a polynomial in the coordinates of `y`). -/
theorem analyticAt_moment {w : (Torus d ℓ → SpinSphere N) → ℂ} (hw : Continuous w) (m : ℕ)
    (y₀ : Torus d ℓ → Fin N → ℂ) :
    AnalyticAt ℂ (fun y : Torus d ℓ → Fin N → ℂ =>
      ∫ φ, w φ * sourcePairing y φ ^ m ∂aprioriMeasure d N ℓ) y₀ := by
  have hint : ∀ p : Fin m → Torus d ℓ × Fin N, Integrable
      (fun φ : Torus d ℓ → SpinSphere N => w φ * ∏ j, spinCoordC (p j) φ)
      (aprioriMeasure d N ℓ) := fun p =>
    integrable_of_continuous (hw.mul (continuous_finsetProd _ fun j _ => continuous_spinCoordC _))
  have heq : (fun y : Torus d ℓ → Fin N → ℂ =>
      ∫ φ, w φ * sourcePairing y φ ^ m ∂aprioriMeasure d N ℓ) = fun y =>
      ∑ p ∈ Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (Torus d ℓ × Fin N)),
        (∫ φ, w φ * ∏ j, spinCoordC (p j) φ ∂aprioriMeasure d N ℓ) *
          ∏ j, y (p j).1 (p j).2 := by
    funext y
    simp only [sourcePairing_pow, Finset.mul_sum]
    rw [integral_finsetSum _ fun p _ => ?_]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
      ring
    · have := (hint p).mul_const (∏ j, y (p j).1 (p j).2)
      refine this.congr (Filter.Eventually.of_forall fun φ => ?_)
      simp only
      ring
  rw [heq]
  refine Finset.analyticAt_fun_sum _ fun p _ => ?_
  refine analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun j _ => ?_)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) (p j).2).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d ℓ => Fin N → ℂ) (p j).1)).analyticAt y₀

theorem sourcePairing_add (g y : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) :
    sourcePairing (g + y) φ = sourcePairing g φ + sourcePairing y φ := by
  simp [sourcePairing, add_mul, Finset.sum_add_distrib]

/-- The exponential-moment integral `y ↦ ∫ w ⟨e^{⟨y,φ⟩}⟩` is analytic at `0`. -/
theorem analyticAt_exp_integral {w : (Torus d ℓ → SpinSphere N) → ℂ} (hw : Continuous w) :
    AnalyticAt ℂ (fun y : Torus d ℓ → Fin N → ℂ =>
      ∫ φ, w φ * Complex.exp (sourcePairing y φ) ∂aprioriMeasure d N ℓ) 0 := by
  set K : ℝ := (Fintype.card (Torus d ℓ) * N : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set R : ℝ := 1 / (K + 1) with hR
  have hRpos : 0 < R := by positivity
  -- on the ball the pairing has norm `≤ 1`
  have hpair : ∀ y ∈ Metric.ball (0 : Torus d ℓ → Fin N → ℂ) R, ∀ φ,
      ‖sourcePairing y φ‖ ≤ 1 := by
    intro y hy φ
    have hy' : ‖y‖ < R := by simpa using hy
    refine (norm_sourcePairing_le_mul y φ).trans ?_
    have : K * ‖y‖ ≤ K * R := mul_le_mul_of_nonneg_left hy'.le hK0
    have h2 : K * R ≤ 1 := by
      rw [hR, mul_one_div, div_le_one (by positivity)]
      linarith
    linarith
  obtain ⟨Bw, hBw⟩ := (isCompact_univ (X := Torus d ℓ → SpinSphere N)).exists_bound_of_continuousOn
    hw.continuousOn
  set B : ℝ := max Bw 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hwB : ∀ φ, ‖w φ‖ ≤ B := fun φ => (hBw φ (Set.mem_univ _)).trans (le_max_left _ _)
  set μR : ℝ := (aprioriMeasure d N ℓ).real Set.univ with hμR
  have hμR0 : 0 ≤ μR := measureReal_nonneg
  -- the partial sums
  set S : ℕ → ℂ → ℂ := fun n x => ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℂ) with hS
  set f : ℕ → (Torus d ℓ → Fin N → ℂ) → ℂ := fun k y =>
    ∫ φ, w φ * S (k + 1) (sourcePairing y φ) ∂aprioriMeasure d N ℓ with hf
  have hSint : ∀ (n : ℕ) (y : Torus d ℓ → Fin N → ℂ), Integrable
      (fun φ : Torus d ℓ → SpinSphere N => w φ * S n (sourcePairing y φ)) (aprioriMeasure d N ℓ) := by
    intro n y
    refine integrable_of_continuous (hw.mul ?_)
    have : Continuous fun φ : Torus d ℓ → SpinSphere N => sourcePairing y φ :=
      continuous_sourcePairing_prod.comp (Continuous.prodMk_right y)
    simp only [hS]
    fun_prop
  have hfan : ∀ k y₀, AnalyticAt ℂ (f k) y₀ := by
    intro k y₀
    have : f k = fun y => ∑ m ∈ Finset.range (k + 1), ((m.factorial : ℂ))⁻¹ *
        ∫ φ, w φ * sourcePairing y φ ^ m ∂aprioriMeasure d N ℓ := by
      funext y
      simp only [hf, hS, Finset.mul_sum]
      rw [integral_finsetSum _ fun m _ => ?_]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
        simp only [div_eq_inv_mul]
        ring
      · have hc : Continuous fun φ : Torus d ℓ → SpinSphere N => sourcePairing y φ :=
          continuous_sourcePairing_prod.comp (Continuous.prodMk_right y)
        exact integrable_of_continuous (by fun_prop)
    rw [this]
    exact Finset.analyticAt_fun_sum _ fun m _ => analyticAt_const.mul (analyticAt_moment hw m y₀)
  -- uniform bound on the partial sums
  have hfM : ∀ k, ∀ y ∈ Metric.ball (0 : Torus d ℓ → Fin N → ℂ) R,
      ‖f k y‖ ≤ B * Real.exp 1 * μR := by
    intro k y hy
    refine (norm_integral_le_of_norm_le_const (C := B * Real.exp 1)
      (Filter.Eventually.of_forall fun φ => ?_)).trans (le_of_eq (by rw [hμR]))
    rw [norm_mul]
    refine mul_le_mul (hwB φ) ?_ (norm_nonneg _) hB0
    refine (norm_sum_le _ _).trans ?_
    have hx := hpair y hy φ
    calc ∑ m ∈ Finset.range (k + 1), ‖sourcePairing y φ ^ m / (m.factorial : ℂ)‖
        = ∑ m ∈ Finset.range (k + 1), ‖sourcePairing y φ‖ ^ m / (m.factorial : ℝ) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [norm_div, norm_pow]
          simp
      _ ≤ Real.exp ‖sourcePairing y φ‖ := Real.sum_le_exp_of_nonneg (norm_nonneg _) _
      _ ≤ Real.exp 1 := Real.exp_le_exp.2 hx
  -- uniform convergence
  set b : ℕ → ℝ := fun k => B * (((k + 1 + 1 : ℕ) : ℝ) * (((k + 1).factorial * (k + 1) : ℕ) : ℝ)⁻¹)
    * μR with hb
  have hbt : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => 2 * B * μR * (1 / ((k : ℝ) + 1))) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * B * μR)
    refine squeeze_zero (fun k => ?_) (fun k => ?_) h1
    · simp only [hb]; positivity
    · simp only [hb]
      have hk : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1).factorial : ℝ) := by
        exact_mod_cast Nat.self_le_factorial (k + 1)
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have : ((k + 1 + 1 : ℕ) : ℝ) * (((k + 1).factorial * (k + 1) : ℕ) : ℝ)⁻¹ ≤
          2 * (1 / ((k : ℝ) + 1)) := by
        push_cast at hk ⊢
        have hF : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
        rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        have h5 : 2 * (1 / ((k : ℝ) + 1)) * (((k + 1).factorial : ℝ) * ((k : ℝ) + 1)) =
            2 * ((k + 1).factorial : ℝ) := by field_simp
        rw [h5]
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      calc B * (((k + 1 + 1 : ℕ) : ℝ) * (((k + 1).factorial * (k + 1) : ℕ) : ℝ)⁻¹) * μR
          ≤ B * (2 * (1 / ((k : ℝ) + 1))) * μR := by gcongr
        _ = 2 * B * μR * (1 / ((k : ℝ) + 1)) := by ring
  have hu : TendstoUniformlyOn f (fun y : Torus d ℓ → Fin N → ℂ =>
      ∫ φ, w φ * Complex.exp (sourcePairing y φ) ∂aprioriMeasure d N ℓ) Filter.atTop
      (Metric.ball (0 : Torus d ℓ → Fin N → ℂ) R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hbt.eventually (gt_mem_nhds hε)] with k hk y hy
    rw [dist_comm, dist_eq_norm]
    have hint1 : Integrable (fun φ : Torus d ℓ → SpinSphere N =>
        w φ * Complex.exp (sourcePairing y φ)) (aprioriMeasure d N ℓ) := by
      have : Continuous fun φ : Torus d ℓ → SpinSphere N => sourcePairing y φ :=
        continuous_sourcePairing_prod.comp (Continuous.prodMk_right y)
      exact integrable_of_continuous (by fun_prop)
    calc ‖f k y - ∫ φ, w φ * Complex.exp (sourcePairing y φ) ∂aprioriMeasure d N ℓ‖
        = ‖∫ φ, (w φ * S (k + 1) (sourcePairing y φ) -
            w φ * Complex.exp (sourcePairing y φ)) ∂aprioriMeasure d N ℓ‖ := by
          rw [integral_sub (hSint _ y) hint1]
      _ ≤ b k := by
          refine (norm_integral_le_of_norm_le_const (C := B * (((k + 1 + 1 : ℕ) : ℝ) *
            (((k + 1).factorial * (k + 1) : ℕ) : ℝ)⁻¹))
            (Filter.Eventually.of_forall fun φ => ?_)).trans (le_of_eq (by rw [hb]))
          rw [← mul_sub, norm_mul]
          refine mul_le_mul (hwB φ) ?_ (norm_nonneg _) hB0
          have hx := hpair y hy φ
          have := Complex.exp_bound hx (n := k + 1) (Nat.succ_pos k)
          rw [norm_sub_rev]
          refine this.trans ?_
          calc ‖sourcePairing y φ‖ ^ (k + 1) * (((k + 1).succ : ℝ) *
                (((k + 1).factorial : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹)
              ≤ 1 * (((k + 1).succ : ℝ) * (((k + 1).factorial : ℝ) * ((k + 1 : ℕ) : ℝ))⁻¹) := by
                gcongr
                exact pow_le_one₀ (norm_nonneg _) hx
            _ = _ := by push_cast; ring
      _ < ε := hk
  exact Balaban.Analysis.analyticAt_of_tendstoUniformlyOn_ball hRpos
    (fun k y _ => hfan k y) hfM hu

theorem analyticAt_sourceIntegral (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {c : (Torus d ℓ → SpinSphere N) → ℂ} (hc : Continuous c) (g₀ : Torus d ℓ → Fin N → ℂ) :
    AnalyticAt ℂ (sourceIntegral d N ℓ β ν h c) g₀ := by
  have hw : Continuous fun φ => sourceIntegrand d N ℓ β ν h c g₀ φ :=
    (continuous_sourceIntegrand_prod (d := d) (N := N) (ℓ := ℓ) β ν h hc).comp
      (Continuous.prodMk_right g₀)
  have heq : sourceIntegral d N ℓ β ν h c = (fun y : Torus d ℓ → Fin N → ℂ =>
      ∫ φ, sourceIntegrand d N ℓ β ν h c g₀ φ * Complex.exp (sourcePairing y φ)
        ∂aprioriMeasure d N ℓ) ∘ fun g => g - g₀ := by
    funext g
    unfold sourceIntegral
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    have : sourcePairing g φ = sourcePairing g₀ φ + sourcePairing (g - g₀) φ := by
      rw [← sourcePairing_add]; simp
    have e : ∀ a b c : ℂ, Complex.exp (a + (b + c)) = Complex.exp (a + b) * Complex.exp c :=
      fun a b c => by rw [← add_assoc, Complex.exp_add]
    simp only [sourceIntegrand, this]
    rw [e]
    ring
  rw [heq]
  exact (analyticAt_exp_integral hw).comp_of_eq (analyticAt_id.sub analyticAt_const)
    (sub_self g₀)

/-- Lemma 0.1: the partition function is analytic in the source (entire). -/
theorem analyticOnNhd_partitionFunction (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    AnalyticOnNhd ℂ (partitionFunction d N ℓ β ν h) Set.univ := by
  rw [partitionFunction_eq_sourceIntegral]
  exact fun g _ => analyticAt_sourceIntegral β ν h continuous_const g

/-- Lemma 0.1: `log (Z(g)/Z(0))` is analytic on `∑ |g| < 1`. -/
theorem analyticOnNhd_logPartition [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    AnalyticOnNhd ℂ (logPartition d N ℓ β ν h) (sourceBall d N ℓ) := by
  have hZ : AnalyticOnNhd ℂ (fun g => partitionFunction d N ℓ β ν h g /
      partitionFunction d N ℓ β ν h 0) Set.univ := fun g hg =>
    ((analyticOnNhd_partitionFunction β ν h g hg).div analyticAt_const
      (partitionFunction_zero_ne_zero β ν h))
  exact (hZ.mono (Set.subset_univ _)).clog fun g hg =>
    partitionFunction_div_mem_slitPlane β ν h hg

end Balaban
