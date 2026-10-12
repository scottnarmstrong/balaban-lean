/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Balaban.Analysis.AnalyticLimit

/-!
# Analyticity of parametric integrals

Mathlib has no several-variable statement that a parametric integral of analytic functions is
analytic. For a finite-dimensional complex space `E` of parameters:

* `norm_integral_sub_riemann_mod`: Riemann sums of a function with a given modulus of continuity;
* `lipschitz_of_analytic_ball`, `continuousOn_uncurry_of_analytic`: a bounded analytic family is
  jointly continuous (Cauchy estimate);
* `analyticAt_intervalIntegral`, `analyticOnNhd_intervalIntegral`: the interval integral
  `∫_a^b G(x, e) dx` is analytic (uniform limit of Riemann sums,
  `Balaban.Analysis.analyticAt_of_tendstoUniformlyOn_ball`);
* `analyticAt_integral_Ioi`, `analyticOnNhd_integral_Ioi`: the improper integral `∫_0^∞ G(x, e) dx`
  is analytic when `‖G(x, e)‖ ≤ g(x)` with `g` continuous and integrable (the partial integrals on
  `[1/(n+1), n+1]` converge uniformly).
-/

@[expose] public section

namespace Balaban.Localization

open MeasureTheory intervalIntegral Set

/-- Riemann sums of a function with modulus of continuity `ε` at scale `(b-a)/n`. -/
theorem norm_integral_sub_riemann_mod {g : ℝ → ℂ} {a b ε : ℝ} (hab : a ≤ b) (hε : 0 ≤ ε)
    (hcont : ContinuousOn g (Icc a b)) {n : ℕ} (hn : 0 < n)
    (hmod : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| ≤ (b - a) / n → ‖g x - g y‖ ≤ ε) :
    ‖(∫ t in a..b, g t) - ((b - a) / (n : ℝ)) • ∑ k ∈ Finset.range n, g (a + k * ((b - a) / n))‖
      ≤ (b - a) * ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set h : ℝ := (b - a) / n with hh
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hn'.le
  set p : ℕ → ℝ := fun k => a + k * h with hp
  have hnh : (n : ℝ) * h = b - a := by rw [hh]; field_simp
  have hpmono : ∀ k : ℕ, k ≤ n → p k ∈ Icc a b := by
    intro k hk
    refine ⟨by simp only [hp]; nlinarith [mul_nonneg (Nat.cast_nonneg k) hh0], ?_⟩
    simp only [hp]
    have : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith
  have hint : ∀ k < n, IntervalIntegrable g volume (p k) (p (k + 1)) := by
    intro k hk
    refine (hcont.mono ?_).intervalIntegrable
    have hle : p k ≤ p (k + 1) := by simp only [hp]; push_cast; nlinarith
    rw [uIcc_of_le hle]
    exact Icc_subset_Icc (hpmono k hk.le).1 (hpmono (k + 1) hk).2
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (μ := volume) (a := p) (n := n) hint
  have hp0 : p 0 = a := by simp [hp]
  have hpn : p n = b := by simp only [hp]; linarith
  rw [hp0, hpn] at hsum
  rw [← hsum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hpiece : ∀ k ∈ Finset.range n,
      ‖(∫ t in (p k)..(p (k + 1)), g t) - h • g (a + k * h)‖ ≤ ε * h := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hlen : p (k + 1) - p k = h := by simp only [hp]; push_cast; ring
    have hc : (∫ _ in (p k)..(p (k + 1)), g (a + k * h)) = h • g (a + k * h) := by
      rw [intervalIntegral.integral_const, hlen]
    rw [← hc, ← intervalIntegral.integral_sub (hint k hk') intervalIntegrable_const]
    have hle : p k ≤ p (k + 1) := by rw [← sub_nonneg, hlen]; exact hh0
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := p k)
      (b := p (k + 1)) (C := ε) (f := fun t => g t - g (a + k * h)) (fun t ht => ?_)
    · rw [hlen] at this
      simpa [abs_of_nonneg hh0, mul_comm] using this
    · rw [uIoc_of_le hle] at ht
      have hx : t ∈ Icc a b := ⟨le_trans (hpmono k hk'.le).1 ht.1.le, le_trans ht.2 (hpmono (k + 1) hk').2⟩
      have hy : p k ∈ Icc a b := hpmono k hk'.le
      have := hmod t hx (p k) hy (by
        rw [abs_of_nonneg (by linarith [ht.1])]
        have := ht.2
        linarith)
      simpa [hp] using this
  refine (Finset.sum_le_sum hpiece).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  nlinarith

open Metric Filter Topology

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem lipschitz_of_analytic_ball {f : E → ℂ} {e0 : E} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball e0 (2 * R))) (hM : ∀ z ∈ ball e0 (2 * R), ‖f z‖ ≤ M)
    {e e' : E} (he : e ∈ closedBall e0 R) (he' : e' ∈ closedBall e0 R) :
    ‖f e - f e'‖ ≤ M / R * ‖e - e'‖ := by
  have hsub : closedBall e0 R ⊆ ball e0 (2 * R) := closedBall_subset_ball (by linarith)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM e0 (mem_ball_self (by linarith)))
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (s := closedBall e0 R)
    (C := M / R)
    (fun x hx => (hf x (hsub hx)).differentiableAt)
    (fun x hx => by
      refine (Balaban.Analysis.norm_fderiv_le_of_ball hf.differentiableOn hM (hsub hx)).trans ?_
      have hxt : dist x e0 ≤ R := mem_closedBall.mp hx
      exact div_le_div_of_nonneg_left hM0 hR (by linarith))
    (convex_closedBall _ _) (x := e') (y := e) he' he
  simpa using this

theorem continuousOn_uncurry_of_analytic {G : ℝ → E → ℂ} {e0 : E} {R M a b : ℝ} (hR : 0 < R)
    (hM0 : 0 ≤ M)
    (hG : ∀ x ∈ Icc a b, AnalyticOnNhd ℂ (G x) (ball e0 (2 * R)))
    (hbd : ∀ x ∈ Icc a b, ∀ e ∈ ball e0 (2 * R), ‖G x e‖ ≤ M)
    (hcont : ∀ e ∈ closedBall e0 R, ContinuousOn (fun x => G x e) (Icc a b)) :
    ContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc a b ×ˢ closedBall e0 R) := by
  rw [Metric.continuousOn_iff]
  rintro ⟨x0, e1⟩ ⟨hx0, he1⟩ ε hε
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousOn_iff.1 (hcont e1 he1) x0 hx0 (ε / 2) (by linarith)
  set δ2 : ℝ := ε / 2 / (M / R + 1) with hδ2
  have hMR : 0 ≤ M / R := div_nonneg hM0 hR.le
  have hδ2p : 0 < δ2 := by positivity
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2p, ?_⟩
  rintro ⟨x, e⟩ ⟨hx, he⟩ hd
  have hd' := hd
  rw [Prod.dist_eq, max_lt_iff] at hd'
  have hd1 : dist x x0 < δ1 := lt_of_lt_of_le hd'.1 (min_le_left _ _)
  have hd2 : dist e e1 < δ2 := lt_of_lt_of_le hd'.2 (min_le_right _ _)
  rw [dist_eq_norm] at hd1 hd2
  have hL := lipschitz_of_analytic_ball hR (hG x hx) (hbd x hx) he he1
  have hA : ‖G x e - G x e1‖ < ε / 2 := by
    refine lt_of_le_of_lt hL ?_
    calc M / R * ‖e - e1‖ ≤ (M / R + 1) * ‖e - e1‖ := by nlinarith [norm_nonneg (e - e1)]
      _ < (M / R + 1) * δ2 := by
        exact mul_lt_mul_of_pos_left hd2 (by positivity)
      _ = ε / 2 := by rw [hδ2]; field_simp
  have hB := h1 x hx (by rwa [dist_eq_norm])
  rw [dist_eq_norm] at hB
  show dist (G x e) (G x0 e1) < ε
  rw [dist_eq_norm]
  calc ‖G x e - G x0 e1‖ = ‖(G x e - G x e1) + (G x e1 - G x0 e1)‖ := by ring_nf
    _ ≤ ‖G x e - G x e1‖ + ‖G x e1 - G x0 e1‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hA hB
    _ = ε := by ring

theorem analyticAt_intervalIntegral [FiniteDimensional ℂ E] {G : ℝ → E → ℂ} {e0 : E}
    {R M a b : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M) (hab : a ≤ b)
    (hG : ∀ x ∈ Icc a b, AnalyticOnNhd ℂ (G x) (ball e0 (2 * R)))
    (hbd : ∀ x ∈ Icc a b, ∀ e ∈ ball e0 (2 * R), ‖G x e‖ ≤ M)
    (hcont : ∀ e ∈ ball e0 (2 * R), ContinuousOn (fun x => G x e) (Icc a b)) :
    AnalyticAt ℂ (fun e => ∫ x in a..b, G x e) e0 := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have hsub : closedBall e0 R ⊆ ball e0 (2 * R) := closedBall_subset_ball (by linarith)
  have hjc := continuousOn_uncurry_of_analytic hR hM0 hG hbd
    (fun e he => hcont e (hsub he))
  have hK : IsCompact (Icc a b ×ˢ closedBall e0 R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have huc := hK.uniformContinuousOn_of_continuous hjc
  set f : ℕ → E → ℂ := fun n e =>
    (((b - a) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (n + 1), G (a + k * ((b - a) / ((n + 1 : ℕ) : ℝ))) e with hf
  have hpt : ∀ n : ℕ, ∀ k ∈ Finset.range (n + 1),
      a + k * ((b - a) / ((n + 1 : ℕ) : ℝ)) ∈ Icc a b := by
    intro n k hk
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hh0 : 0 ≤ (b - a) / ((n + 1 : ℕ) : ℝ) := div_nonneg (by linarith) hn1.le
    refine ⟨by nlinarith [mul_nonneg (Nat.cast_nonneg k) hh0], ?_⟩
    have : (k : ℝ) * ((b - a) / ((n + 1 : ℕ) : ℝ)) ≤ b - a := by
      calc (k : ℝ) * ((b - a) / ((n + 1 : ℕ) : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) * ((b - a) / ((n + 1 : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ hh0; push_cast; linarith
        _ = b - a := by field_simp
    linarith
  refine Balaban.Analysis.analyticAt_of_tendstoUniformlyOn_ball (f := f) (M := (b - a) * M) hR ?_ ?_ ?_
  · intro n z hz
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun k hk => ?_)
    exact (hG _ (hpt n k hk) z (ball_subset_ball (by linarith) hz))
  · intro n z hz
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hh0 : 0 ≤ (b - a) / ((n + 1 : ℕ) : ℝ) := div_nonneg (by linarith) hn1.le
    simp only [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0]
    have hs : ‖∑ k ∈ Finset.range (n + 1), G (a + k * ((b - a) / ((n + 1 : ℕ) : ℝ))) z‖ ≤
        ((n + 1 : ℕ) : ℝ) * M := by
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ k ∈ Finset.range (n + 1), M := Finset.sum_le_sum fun k hk =>
            hbd _ (hpt n k hk) z (ball_subset_ball (by linarith) hz)
        _ = _ := by simp
    calc (b - a) / ((n + 1 : ℕ) : ℝ) * ‖∑ k ∈ Finset.range (n + 1), G _ z‖
        ≤ (b - a) / ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left hs hh0
      _ = (b - a) * M := by field_simp
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε' : 0 < ε / (2 * (b - a) + 1) := by
      have : 0 ≤ b - a := by linarith
      positivity
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc _ hε'
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    filter_upwards [eventually_ge_atTop N] with n hn
    intro z hz
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hlt : (b - a) / ((n + 1 : ℕ) : ℝ) < δ := by
      rw [div_lt_iff₀ hn1]
      rw [div_lt_iff₀ hδ] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      have : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      nlinarith
    have hzc : z ∈ closedBall e0 R := ball_subset_closedBall hz
    have hmod : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| ≤ (b - a) / ((n + 1 : ℕ) : ℝ) →
        ‖G x z - G y z‖ ≤ ε / (2 * (b - a) + 1) := by
      intro x hx y hy hxy
      have := hδ' (x, z) ⟨hx, hzc⟩ (y, z) ⟨hy, hzc⟩ (by
        rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq]
        exact max_lt (lt_of_le_of_lt hxy hlt) hδ)
      simpa [dist_eq_norm] using this.le
    have hr := norm_integral_sub_riemann_mod hab hε'.le
      ((hjc.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, hzc⟩)))
      (n := n + 1) (by omega) hmod
    rw [dist_eq_norm]
    simp only [hf]
    have e1 : (((b - a) / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (n + 1), G (a + k * ((b - a) / ((n + 1 : ℕ) : ℝ))) z =
        ((b - a) / ((n + 1 : ℕ) : ℝ)) • ∑ k ∈ Finset.range (n + 1),
          G (a + k * ((b - a) / ((n + 1 : ℕ) : ℝ))) z := by
      rw [Complex.real_smul]
    rw [e1]
    refine lt_of_le_of_lt hr ?_
    have : 0 ≤ b - a := by linarith
    calc (b - a) * (ε / (2 * (b - a) + 1)) = ε * ((b - a) / (2 * (b - a) + 1)) := by ring
      _ < ε * 1 := by
        apply mul_lt_mul_of_pos_left _ hε
        rw [div_lt_one (by linarith)]; linarith
      _ = ε := mul_one ε

theorem analyticOnNhd_intervalIntegral [FiniteDimensional ℂ E] {G : ℝ → E → ℂ} {e0 : E}
    {R M a b : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M) (hab : a ≤ b)
    (hG : ∀ x ∈ Icc a b, AnalyticOnNhd ℂ (G x) (ball e0 (2 * R)))
    (hbd : ∀ x ∈ Icc a b, ∀ e ∈ ball e0 (2 * R), ‖G x e‖ ≤ M)
    (hcont : ∀ e ∈ ball e0 (2 * R), ContinuousOn (fun x => G x e) (Icc a b)) :
    AnalyticOnNhd ℂ (fun e => ∫ x in a..b, G x e) (ball e0 R) := by
  intro z hz
  have hsub : ball z R ⊆ ball e0 (2 * R) := by
    intro y hy
    rw [mem_ball] at hy hz ⊢
    calc dist y e0 ≤ dist y z + dist z e0 := dist_triangle _ _ _
      _ < R + R := add_lt_add hy hz
      _ = 2 * R := by ring
  refine analyticAt_intervalIntegral (R := R / 2) (by positivity) hM0 hab ?_ ?_ ?_
  · intro x hx
    refine (hG x hx).mono ?_
    intro y hy; apply hsub; rwa [show 2 * (R / 2) = R by ring] at hy
  · intro x hx y hy
    refine hbd x hx y (hsub ?_)
    rwa [show 2 * (R / 2) = R by ring] at hy
  · intro y hy
    refine hcont y (hsub ?_)
    rwa [show 2 * (R / 2) = R by ring] at hy

theorem analyticAt_integral_Ioi [FiniteDimensional ℂ E] {G : ℝ → E → ℂ} {g : ℝ → ℝ} {e0 : E}
    {R : ℝ} (hR : 0 < R)
    (hG : ∀ x, 0 < x → AnalyticOnNhd ℂ (G x) (ball e0 (2 * R)))
    (hcont : ∀ e ∈ ball e0 (2 * R), ContinuousOn (fun x => G x e) (Ioi 0))
    (hgc : ContinuousOn g (Ioi 0)) (hgi : IntegrableOn g (Ioi 0))
    (hbd : ∀ x, 0 < x → ∀ e ∈ ball e0 (2 * R), ‖G x e‖ ≤ g x) :
    AnalyticAt ℂ (fun e => ∫ x in Ioi 0, G x e) e0 := by
  have hg0 : ∀ x, 0 < x → 0 ≤ g x := fun x hx =>
    le_trans (norm_nonneg _) (hbd x hx e0 (mem_ball_self (by linarith)))
  set lo : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hlo
  set hi : ℕ → ℝ := fun n => (n : ℝ) + 1 with hhi
  have hlo_pos : ∀ n, 0 < lo n := fun n => by simp only [hlo]; positivity
  have hlohi : ∀ n, lo n ≤ hi n := by
    intro n
    simp only [hlo, hhi]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hGint : ∀ z ∈ ball e0 (2 * R), IntegrableOn (fun x => G x z) (Ioi 0) := by
    intro z hz
    refine Integrable.mono' hgi ?_ ?_
    · exact (hcont z hz).aestronglyMeasurable measurableSet_Ioi
    · exact (ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun x hx => hbd x hx z hz)
  set f : ℕ → E → ℂ := fun n e => ∫ x in (lo n)..(hi n), G x e with hf
  refine Balaban.Analysis.analyticAt_of_tendstoUniformlyOn_ball (f := f) (M := ∫ x in Ioi 0, g x)
    hR ?_ ?_ ?_
  · intro n
    have hcg : IsCompact (Icc (lo n) (hi n)) := isCompact_Icc
    obtain ⟨M, hM⟩ := hcg.bddAbove_image (f := g) (hgc.mono (fun x hx => lt_of_lt_of_le (hlo_pos n) hx.1))
    refine analyticOnNhd_intervalIntegral (G := G) (M := max M 0) hR (le_max_right _ _) (hlohi n)
      ?_ ?_ ?_
    · intro x hx
      exact (hG x (lt_of_lt_of_le (hlo_pos n) hx.1)).mono
        (ball_subset_ball (by linarith))
    · intro x hx e he
      exact (hbd x (lt_of_lt_of_le (hlo_pos n) hx.1) e (ball_subset_ball (by linarith) he)).trans
        ((hM ⟨x, hx, rfl⟩).trans (le_max_left _ _))
    · intro e he
      exact (hcont e (ball_subset_ball (by linarith) he)).mono
        (fun x hx => lt_of_lt_of_le (hlo_pos n) hx.1)
  · intro n z hz
    have hz2 : z ∈ ball e0 (2 * R) := ball_subset_ball (by linarith) hz
    simp only [hf]
    rw [intervalIntegral.integral_of_le (hlohi n)]
    refine (MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict (Ioc (lo n) (hi n)))
      (g := g) ?_ ?_).trans ?_
    · exact hgi.mono_set (fun x hx => (hlo_pos n).trans hx.1)
    · exact (ae_restrict_iff' measurableSet_Ioc).2
        (Filter.Eventually.of_forall fun x hx => hbd x ((hlo_pos n).trans hx.1) z hz2)
    · exact setIntegral_mono_set hgi ((ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun x hx => hg0 x hx)) (Filter.Eventually.of_forall
          (fun x hx => (hlo_pos n).trans hx.1))
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hmono : Monotone (fun n : ℕ => Ioc (lo n) (hi n)) := by
      intro m n hmn
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      refine Ioc_subset_Ioc ?_ ?_
      · simp only [hlo]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      · simp only [hhi]; linarith
    have hunion : ⋃ n : ℕ, Ioc (lo n) (hi n) = Ioi 0 := by
      ext y
      simp only [mem_iUnion, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨n, h1, _⟩; exact (hlo_pos n).trans h1
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / y) y)
        refine ⟨n, ?_, ?_⟩
        · simp only [hlo]
          rw [div_lt_iff₀ (by positivity)]
          have h1 : 1 / y < n := lt_of_le_of_lt (le_max_left _ _) hn
          rw [div_lt_iff₀ hy] at h1
          nlinarith
        · simp only [hhi]
          have := lt_of_le_of_lt (le_max_right _ _) hn
          linarith
    have htend := MeasureTheory.tendsto_setIntegral_of_monotone (μ := volume)
      (s := fun n : ℕ => Ioc (lo n) (hi n)) (f := g) (fun n => measurableSet_Ioc) hmono
      (by rw [hunion]; exact hgi)
    rw [hunion] at htend
    have hev : ∀ᶠ n : ℕ in atTop, (∫ x in Ioi 0, g x) - ∫ x in Ioc (lo n) (hi n), g x < ε := by
      have := (tendsto_const_nhds (x := ∫ x in Ioi (0 : ℝ), g x)).sub htend
      rw [sub_self] at this
      exact (this.eventually (gt_mem_nhds hε))
    filter_upwards [hev] with n hn
    intro z hz
    have hz2 : z ∈ ball e0 (2 * R) := ball_subset_ball (by linarith) hz
    have hsubset : Ioc (lo n) (hi n) ⊆ Ioi 0 := fun x hx => (hlo_pos n).trans hx.1
    have hdiff := MeasureTheory.setIntegral_sdiff (μ := volume) (f := fun x => G x z)
      measurableSet_Ioc (hGint z hz2) hsubset
    have hdiffg := MeasureTheory.setIntegral_sdiff (μ := volume) (f := g)
      measurableSet_Ioc hgi hsubset
    rw [dist_eq_norm]
    simp only [hf]
    rw [intervalIntegral.integral_of_le (hlohi n), ← hdiff]
    refine lt_of_le_of_lt ?_ (hdiffg ▸ hn)
    refine MeasureTheory.norm_integral_le_of_norm_le (hgi.mono_set Set.sdiff_subset) ?_
    exact (ae_restrict_iff' (measurableSet_Ioi.diff measurableSet_Ioc)).2
      (Filter.Eventually.of_forall fun x hx => hbd x hx.1 z hz2)

theorem analyticOnNhd_integral_Ioi [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U)
    {G : ℝ → E → ℂ} {g : ℝ → ℝ}
    (hG : ∀ x, 0 < x → AnalyticOnNhd ℂ (G x) U)
    (hcont : ∀ e ∈ U, ContinuousOn (fun x => G x e) (Ioi 0))
    (hgc : ContinuousOn g (Ioi 0)) (hgi : IntegrableOn g (Ioi 0))
    (hbd : ∀ x, 0 < x → ∀ e ∈ U, ‖G x e‖ ≤ g x) :
    AnalyticOnNhd ℂ (fun e => ∫ x in Ioi 0, G x e) U := by
  intro e0 he0
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU e0 he0
  have hsub : ball e0 (2 * (r / 2)) ⊆ U := by
    rw [show 2 * (r / 2) = r by ring]; exact hrU
  exact analyticAt_integral_Ioi (R := r / 2) (by positivity)
    (fun x hx => (hG x hx).mono hsub) (fun e he => hcont e (hsub he)) hgc hgi
    (fun x hx e he => hbd x hx e (hsub he))

theorem continuousOn_inv_add_Ioi {ak : ℝ} (hak : 0 < ak) :
    ContinuousOn (fun y : ℝ => (ak + y)⁻¹) (Ioi 0) :=
  (continuousOn_const.add continuousOn_id).inv₀ fun y hy => by
    have := mem_Ioi.mp hy
    show ak + y ≠ 0
    exact (by linarith : 0 < ak + y).ne'

end Param

end Balaban.Localization
