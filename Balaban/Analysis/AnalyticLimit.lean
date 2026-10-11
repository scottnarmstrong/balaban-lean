/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.Cauchy
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic


/-!
# Uniform limits of analytic functions in several variables

Mathlib has no several-variable version of Weierstrass' theorem.  We prove it from the Cauchy
estimates of `Balaban.Analysis.Cauchy`: if `f` is analytic on `ball z₀ R` with `‖f‖ ≤ M` then
`‖D^n f (z₀)‖ ≤ M ((n+1)/R)^n` (iterate the first derivative bound on shrinking balls), hence the
Taylor series `taylorSeries f z₀` has operator norms `≤ 3 M (3/R)^n` and represents `f` on
`ball z₀ (R/3)` (`hasFPowerSeriesOnBall_taylorSeries`, via one-variable Taylor expansion along
lines).  For a uniformly convergent sequence the coefficient maps are Cauchy in operator norm,
their limit series is bounded the same way, and dominated convergence shows that it represents
the limit (`analyticAt_of_tendstoUniformlyOn_ball`, `analyticOnNhd_of_tendstoUniformlyOn`).
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem iteratedDeriv_line_eq [CompleteSpace F] {f : E → F} {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball x₀ R)) (y : E) (n : ℕ) :
    iteratedDeriv n (fun l : ℂ => f (x₀ + l • y)) 0 = iteratedFDeriv ℂ n f x₀ (fun _ => y) := by
  set f' : E → F := fun z => f (x₀ + z) with hf'
  set L : ℂ →L[ℂ] E := ContinuousLinearMap.toSpanSingleton ℂ y with hL
  have hs : ball (0 : E) R ⊆ (fun z => x₀ + z) ⁻¹' ball x₀ R := by
    intro z hz; simpa [mem_ball, dist_eq_norm] using hz
  have hcd : ContDiffOn ℂ n f' (ball (0 : E) R) := by
    refine ContDiffOn.comp (g := f) (f := fun z : E => x₀ + z) (t := ball x₀ R)
      (hf.contDiffOn_of_completeSpace) (contDiff_const.add contDiff_id).contDiffOn ?_
    intro z hz; simpa [mem_ball, dist_eq_norm] using hz
  have hg : (fun l : ℂ => f (x₀ + l • y)) = f' ∘ L := by
    funext l; simp [hf', hL]
  have h0 : L 0 ∈ ball (0 : E) R := by simp [hL, hR]
  have hopen : IsOpen (L ⁻¹' ball (0 : E) R) := (isOpen_ball (x := (0:E)) (ε := R)).preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hcd (isOpen_ball (x := (0:E)) (ε := R)).uniqueDiffOn
    hopen.uniqueDiffOn (x := 0) h0 (i := n) le_rfl
  rw [hg, iteratedDeriv_eq_iteratedFDeriv]
  rw [← iteratedFDerivWithin_of_isOpen n hopen (show (0:ℂ) ∈ L ⁻¹' ball (0 : E) R from h0), key,
    iteratedFDerivWithin_of_isOpen n (isOpen_ball (x := (0:E)) (ε := R)) h0]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have : L 0 = 0 := map_zero L
  rw [this, hf', iteratedFDeriv_comp_add_left]
  simp [hL]


/-- Iterated derivative bound: for `n * a < R`, on `ball z₀ (R - n a)`,
`‖D^n f‖ ≤ M / a^n`. -/
theorem norm_iteratedFDeriv_le_of_ball [CompleteSpace F] {f : E → F} {z₀ : E} {R M a : ℝ}
    (ha : 0 < a) (hf : AnalyticOnNhd ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M)
    (n : ℕ) (hn : (n : ℝ) * a < R) {w : E} (hw : w ∈ ball z₀ (R - n * a)) :
    ‖iteratedFDeriv ℂ n f w‖ ≤ M / a ^ n := by
  induction n generalizing w with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero] at hw
    simpa using hM w hw
  | succ n ih =>
    have hn' : (n : ℝ) * a < R := by push_cast at hn; nlinarith
    set Rn := R - n * a with hRn
    have hball : ball z₀ Rn ⊆ ball z₀ R := ball_subset_ball (by nlinarith)
    have hg : DifferentiableOn ℂ (iteratedFDeriv ℂ n f) (ball z₀ Rn) :=
      ((hf.iteratedFDeriv n).mono hball).differentiableOn
    have hw' : dist w z₀ < R - ((n : ℝ) + 1) * a := by
      rw [mem_ball] at hw; push_cast at hw; linarith
    have hwb : w ∈ ball z₀ Rn := by
      rw [mem_ball]; linarith
    have h1 := norm_fderiv_le_of_ball hg (fun z hz => ih hn' hz) hwb
    rw [norm_fderiv_iteratedFDeriv] at h1
    refine h1.trans ?_
    have hM0 : 0 ≤ M / a ^ n := by
      have := hM z₀ (mem_ball_self (by linarith [show (0:ℝ) ≤ n * a by positivity]))
      exact div_nonneg (le_trans (norm_nonneg _) this) (by positivity)
    rw [pow_succ, ← div_div]
    exact div_le_div_of_nonneg_left hM0 ha (by linarith)


/-- The Taylor series `∑ (n!)⁻¹ D^n f(x₀)`. -/
noncomputable def taylorSeries (f : E → F) (x₀ : E) : FormalMultilinearSeries ℂ E F :=
  fun n => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x₀

theorem norm_taylorSeries_le [CompleteSpace F] {f : E → F} {z₀ : E} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖taylorSeries f z₀ n‖ ≤ 3 * M * (3 / R) ^ n := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (mem_ball_self hR))
  set a := R / ((n : ℝ) + 1) with ha
  have hapos : 0 < a := by positivity
  have hna : (n : ℝ) * a < R := by
    rw [ha, mul_div_assoc']; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hw : z₀ ∈ ball z₀ (R - n * a) := by
    refine mem_ball_self ?_
    have : R - n * a = a := by rw [ha]; field_simp; ring
    rw [this]; exact hapos
  have h1 := norm_iteratedFDeriv_le_of_ball hapos hf hM n hna hw
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h2 : ‖taylorSeries f z₀ n‖ = ‖iteratedFDeriv ℂ n f z₀‖ / n.factorial := by
    simp only [taylorSeries, norm_smul, norm_inv, Complex.norm_natCast]; ring
  rw [h2, div_le_iff₀ hfac]
  have h3 : ((n : ℝ) + 1) ^ n / n.factorial ≤ 3 ^ (n + 1) := by
    have := Real.pow_div_factorial_le_exp ((n : ℝ) + 1) (by positivity) (n + 1)
    have h4 : ((n : ℝ) + 1) ^ (n + 1) / (n + 1).factorial = ((n : ℝ) + 1) ^ n / n.factorial := by
      rw [Nat.factorial_succ, pow_succ]; push_cast; field_simp
    rw [h4] at this
    refine this.trans ?_
    have h5 : Real.exp ((n : ℝ) + 1) = Real.exp 1 ^ (n + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [h5]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
  have h6 : M / a ^ n = M * (((n : ℝ) + 1) / R) ^ n := by
    rw [ha, div_pow, div_pow]; field_simp
  rw [h6] at h1
  calc ‖iteratedFDeriv ℂ n f z₀‖ ≤ M * (((n : ℝ) + 1) / R) ^ n := h1
    _ = M * (((n : ℝ) + 1) ^ n / n.factorial) * n.factorial / R ^ n := by
        rw [div_pow]; field_simp
    _ ≤ M * 3 ^ (n + 1) * n.factorial / R ^ n := by
        gcongr
    _ = 3 * M * (3 / R) ^ n * n.factorial := by rw [div_pow, pow_succ]; ring


/-- A bounded analytic function on a ball is given by its Taylor series on the ball of a third
of the radius. -/
theorem hasFPowerSeriesOnBall_taylorSeries [CompleteSpace F] {f : E → F} {z₀ : E} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (taylorSeries f z₀) z₀ (ENNReal.ofReal (R / 3)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (mem_ball_self hR))
  have hr3 : 0 < R / 3 := by positivity
  refine ⟨?_, by simpa using hr3, ?_⟩
  · have := FormalMultilinearSeries.le_radius_of_bound (taylorSeries f z₀) (3 * M)
      (r := (R / 3).toNNReal) (fun n => by
        have h := norm_taylorSeries_le hR hf hM n
        have : (((R / 3).toNNReal : NNReal) : ℝ) = R / 3 := Real.coe_toNNReal _ hr3.le
        rw [this]
        calc ‖taylorSeries f z₀ n‖ * (R / 3) ^ n ≤ 3 * M * (3 / R) ^ n * (R / 3) ^ n :=
              mul_le_mul_of_nonneg_right h (by positivity)
          _ = 3 * M := by rw [mul_assoc, ← mul_pow, show 3 / R * (R / 3) = 1 by field_simp, one_pow, mul_one])
    exact this
  · intro y hy
    have hy' : ‖y‖ < R / 3 := by
      rw [mem_eball_zero_iff, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hr3] at hy
      exact hy
    set g : ℂ → F := fun l => f (z₀ + l • y) with hg
    have hmem : ∀ l : ℂ, ‖l‖ < 3 → z₀ + l • y ∈ ball z₀ R := by
      intro l hl
      rw [mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul]
      calc ‖l‖ * ‖y‖ ≤ 3 * ‖y‖ := by gcongr
        _ < R := by linarith
    have hgd : DifferentiableOn ℂ g (ball 0 3) := by
      intro l hl
      have hl' : ‖l‖ < 3 := by simpa using hl
      have h1 : DifferentiableAt ℂ (fun l : ℂ => z₀ + l • y) l := by fun_prop
      exact (((hf.differentiableOn).differentiableAt (isOpen_ball.mem_nhds (hmem l hl'))).comp l h1).differentiableWithinAt
    have := Complex.hasSum_taylorSeries_on_ball hgd (z := 1) (by simp)
    simp only [sub_zero, one_pow, one_smul] at this
    convert this using 1
    · funext n
      simp only [taylorSeries, smul_apply]
      rw [hg, iteratedDeriv_line_eq hR hf]
    · simp [hg]


theorem taylorSeries_sub [CompleteSpace F] {f g : E → F} {s : Set E} (hs : IsOpen s)
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) {x : E} (hx : x ∈ s) (n : ℕ) :
    taylorSeries (f - g) x n = taylorSeries f x n - taylorSeries g x n := by
  have h := iteratedFDerivWithin_sub_apply (i := n)
    ((hf.contDiffOn_of_completeSpace) x hx) ((hg.contDiffOn_of_completeSpace) x hx)
    hs.uniqueDiffOn hx
  rw [iteratedFDerivWithin_of_isOpen n hs hx, iteratedFDerivWithin_of_isOpen n hs hx,
    iteratedFDerivWithin_of_isOpen n hs hx] at h
  simp only [taylorSeries, h, smul_sub]

/-- A uniform limit of bounded analytic functions on a ball is analytic at the centre. -/
theorem analyticAt_of_tendstoUniformlyOn_ball [CompleteSpace F] {f : ℕ → E → F} {g : E → F}
    {x₀ : E} {R M : ℝ} (hR : 0 < R) (hf : ∀ k, AnalyticOnNhd ℂ (f k) (ball x₀ R))
    (hM : ∀ k, ∀ z ∈ ball x₀ R, ‖f k z‖ ≤ M)
    (hu : TendstoUniformlyOn f g atTop (ball x₀ R)) : AnalyticAt ℂ g x₀ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 x₀ (mem_ball_self hR))
  have hr3 : 0 < R / 3 := by positivity
  have hx₀ : x₀ ∈ ball x₀ R := mem_ball_self hR
  -- Cauchy property of the coefficients
  have hcauchy : ∀ n, CauchySeq (fun k => taylorSeries (f k) x₀ n) := by
    intro n
    rw [Metric.cauchySeq_iff']
    intro ε hε
    set c : ℝ := 3 * (3 / R) ^ n with hc
    have hcpos : 0 < c := by positivity
    have hu' := Metric.tendstoUniformlyOn_iff.mp hu (ε / (4 * c)) (by positivity)
    obtain ⟨K, hK⟩ := eventually_atTop.mp hu'
    refine ⟨K, fun k hk => ?_⟩
    have hdiff : ∀ z ∈ ball x₀ R, ‖(f k - f K) z‖ ≤ ε / (2 * c) := by
      intro z hz
      have h1 := hK k hk z hz
      have h2 := hK K le_rfl z hz
      have h3 : ‖f k z - f K z‖ ≤ dist (g z) (f k z) + dist (g z) (f K z) := by
        rw [← dist_eq_norm]; exact dist_triangle_left _ _ _
      have h4 : ε / (4 * c) + ε / (4 * c) = ε / (2 * c) := by field_simp; ring
      simp only [Pi.sub_apply]
      linarith
    have hanal : AnalyticOnNhd ℂ (f k - f K) (ball x₀ R) := (hf k).sub (hf K)
    have h3 := norm_taylorSeries_le hR hanal hdiff n
    rw [taylorSeries_sub isOpen_ball (hf k) (hf K) hx₀] at h3
    rw [dist_eq_norm]
    calc ‖taylorSeries (f k) x₀ n - taylorSeries (f K) x₀ n‖ ≤ 3 * (ε / (2 * c)) * (3 / R) ^ n := h3
      _ = ε / 2 := by rw [hc]; field_simp
      _ < ε := by linarith
  choose Q hQ using fun n => cauchySeq_tendsto_of_complete (hcauchy n)
  have hQb : ∀ n, ‖Q n‖ ≤ 3 * M * (3 / R) ^ n := fun n =>
    le_of_tendsto (hQ n).norm (Eventually.of_forall fun k => norm_taylorSeries_le hR (hf k) (hM k) n)
  let Qs : FormalMultilinearSeries ℂ E F := Q
  have hrad : ENNReal.ofReal (R / 3) ≤ Qs.radius := by
    have := FormalMultilinearSeries.le_radius_of_bound Qs (3 * M)
      (r := (R / 3).toNNReal) (fun n => by
        have : (((R / 3).toNNReal : NNReal) : ℝ) = R / 3 := Real.coe_toNNReal _ hr3.le
        rw [this]
        calc ‖Qs n‖ * (R / 3) ^ n ≤ 3 * M * (3 / R) ^ n * (R / 3) ^ n :=
              mul_le_mul_of_nonneg_right (hQb n) (by positivity)
          _ = 3 * M := by
              rw [mul_assoc, ← mul_pow, show 3 / R * (R / 3) = 1 by field_simp, one_pow, mul_one])
    exact this
  have hps : ∀ k, HasFPowerSeriesOnBall (f k) (taylorSeries (f k) x₀) x₀ (ENNReal.ofReal (R / 3)) :=
    fun k => hasFPowerSeriesOnBall_taylorSeries hR (hf k) (hM k)
  suffices H : HasFPowerSeriesOnBall g Qs x₀ (ENNReal.ofReal (R / 3)) from H.analyticAt
  refine ⟨hrad, by simpa using hr3, ?_⟩
  intro y hy
  have hy' : ‖y‖ < R / 3 := by
    rw [mem_eball_zero_iff, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hr3] at hy
    exact hy
  have hxy : x₀ + y ∈ ball x₀ R := by
    rw [mem_ball, dist_eq_norm]; simp only [add_sub_cancel_left]; linarith
  set bd : ℕ → ℝ := fun n => 3 * M * (3 * ‖y‖ / R) ^ n with hbd
  have hq : 3 * ‖y‖ / R < 1 := by rw [div_lt_one hR]; linarith
  have hsum : Summable bd :=
    (summable_geometric_of_lt_one (by positivity) hq).mul_left (3 * M)
  have hbound : ∀ k n, ‖taylorSeries (f k) x₀ n (fun _ => y)‖ ≤ bd n := by
    intro k n
    calc ‖taylorSeries (f k) x₀ n (fun _ => y)‖
        ≤ ‖taylorSeries (f k) x₀ n‖ * ∏ _i : Fin n, ‖y‖ := (taylorSeries (f k) x₀ n).le_opNorm _
      _ ≤ 3 * M * (3 / R) ^ n * ‖y‖ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (norm_taylorSeries_le hR (hf k) (hM k) n) (by positivity)
      _ = bd n := by rw [hbd]; simp only; rw [mul_assoc, ← mul_pow]; ring_nf
  have hlim : ∀ n, Tendsto (fun k => taylorSeries (f k) x₀ n (fun _ => y)) atTop
      (𝓝 (Qs n (fun _ => y))) := by
    intro n
    have := (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => y)).continuous.tendsto (Qs n)
    exact this.comp (hQ n)
  have hT := tendsto_tsum_of_dominated_convergence hsum hlim
    (Eventually.of_forall fun k n => hbound k n)
  have hT2 : Tendsto (fun k => f k (x₀ + y)) atTop (𝓝 (g (x₀ + y))) := by
    have := hu.tendsto_at hxy
    exact this
  have heq : ∑' n, Qs n (fun _ => y) = g (x₀ + y) := by
    refine tendsto_nhds_unique hT ?_
    have : (fun k => ∑' n, taylorSeries (f k) x₀ n (fun _ => y)) = fun k => f k (x₀ + y) := by
      funext k; exact ((hps k).hasSum (by simpa using hy)).tsum_eq
    rw [this]; exact hT2
  have hs2 : Summable (fun n => Qs n (fun _ => y)) := by
    refine Summable.of_norm_bounded hsum (fun n => ?_)
    calc ‖Qs n (fun _ => y)‖ ≤ ‖Qs n‖ * ∏ _i : Fin n, ‖y‖ := (Qs n).le_opNorm _
      _ ≤ 3 * M * (3 / R) ^ n * ‖y‖ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (hQb n) (by positivity)
      _ = bd n := by rw [hbd]; simp only; rw [mul_assoc, ← mul_pow]; ring_nf
  rw [← heq]
  exact hs2.hasSum


/-- A uniform limit of uniformly bounded analytic functions on an open set is analytic. -/
theorem analyticOnNhd_of_tendstoUniformlyOn [CompleteSpace F] {f : ℕ → E → F} {g : E → F}
    {U : Set E} {M : ℝ} (hU : IsOpen U) (hf : ∀ k, AnalyticOnNhd ℂ (f k) U)
    (hM : ∀ k, ∀ z ∈ U, ‖f k z‖ ≤ M) (hu : TendstoUniformlyOn f g atTop U) :
    AnalyticOnNhd ℂ g U := by
  intro x hx
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hx
  exact analyticAt_of_tendstoUniformlyOn_ball hR (fun k => (hf k).mono hRU)
    (fun k z hz => hM k z (hRU hz)) (hu.mono hRU)

end Balaban.Analysis
