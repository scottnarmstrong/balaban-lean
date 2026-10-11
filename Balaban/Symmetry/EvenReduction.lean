/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.AnalyticLimit
public import Balaban.Symmetry.TotallyReal
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# An even analytic function is an analytic function of the square

Let `g` be analytic near `z₀ ∈ ℂ³` with `z₀ 2 = 0`, and even in the third variable.  Then there
are `δ > 0` and `f`, analytic on the polydisc of radii `(δ, δ, δ²)` around `z₀`, with
`g z = f (z₀', z₁', z₂²)` for `|z₀ - z₀₀|, |z₁ - z₀₁|, |z₂| < δ` (`exists_sq_reduction`).
The proof expands in the third variable: the coefficients `a_k(u) = ∂₂^k g(u, 0)/k!` are analytic
in `u` and bounded by `M / R^k` (Cauchy), the odd ones vanish, and
`f(u, y) = ∑ a_{2m}(u) y^m` is a uniformly convergent series of analytic functions
(`Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn`).
-/

@[expose] public section

open Metric Set Filter Topology Balaban.Analysis

namespace Balaban.Symmetry

/-- Taylor coefficient in the third variable. -/
noncomputable def sliceCoeff (g : (Fin 3 → ℂ) → ℂ) (k : ℕ) (z : Fin 3 → ℂ) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedDeriv k (fun l : ℂ => g (Function.update z 2 l)) 0

theorem update_eq_add_smul (z : Fin 3 → ℂ) (l : ℂ) :
    Function.update z 2 l = Function.update z 2 0 + l • (Pi.single 2 1 : Fin 3 → ℂ) := by
  funext j
  by_cases hj : j = 2
  · subst hj; simp
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

theorem norm_update_zero_sub_lt {z₀ z : Fin 3 → ℂ} (hz₀ : z₀ 2 = 0) {ρ : ℝ} (hρ : 0 < ρ)
    (h0 : ‖z 0 - z₀ 0‖ < ρ) (h1 : ‖z 1 - z₀ 1‖ < ρ) :
    Function.update z 2 0 ∈ ball z₀ ρ := by
  rw [mem_ball, dist_pi_lt_iff hρ]
  intro j
  rw [dist_eq_norm]
  fin_cases j
  · simpa using h0
  · simpa using h1
  · simpa [hz₀] using hρ

theorem norm_sliceCoeff_le {g : (Fin 3 → ℂ) → ℂ} {z₀ z : Fin 3 → ℂ} (hz₀ : z₀ 2 = 0)
    {r M : ℝ} (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (ball z₀ r))
    (hM : ∀ w ∈ ball z₀ r, ‖g w‖ ≤ M)
    (h0 : ‖z 0 - z₀ 0‖ < r / 4) (h1 : ‖z 1 - z₀ 1‖ < r / 4) (k : ℕ) :
    ‖sliceCoeff g k z‖ ≤ M / (r / 2) ^ k := by
  have hc := norm_update_zero_sub_lt hz₀ (by positivity : 0 < r / 4) h0 h1
  have hsub : ball (Function.update z 2 0) (r / 2) ⊆ ball z₀ r := by
    intro w hw
    rw [mem_ball] at hw ⊢
    have := dist_triangle w (Function.update z 2 0) z₀
    rw [mem_ball] at hc
    linarith
  have key := norm_iteratedDeriv_line_le (f := g) (z₀ := Function.update z 2 0)
    (R := r / 2) (M := M) (by positivity) (hg.mono hsub).differentiableOn
    (fun w hw => hM w (hsub hw)) (Pi.single 2 1) k
  have hnorm : ‖(Pi.single 2 1 : Fin 3 → ℂ)‖ = 1 := by
    simp [Pi.norm_single]
  rw [hnorm, one_pow, mul_one] at key
  have heq : (fun l : ℂ => g (Function.update z 2 l)) =
      fun l : ℂ => g (Function.update z 2 0 + l • (Pi.single 2 1 : Fin 3 → ℂ)) := by
    funext l; rw [update_eq_add_smul z l]
  unfold sliceCoeff
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  calc (k.factorial : ℝ)⁻¹ * ‖iteratedDeriv k (fun l : ℂ =>
        g (Function.update z 2 0 + l • (Pi.single 2 1 : Fin 3 → ℂ))) 0‖
      ≤ (k.factorial : ℝ)⁻¹ * (k.factorial * M / (r / 2) ^ k) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = M / (r / 2) ^ k := by field_simp

theorem analyticAt_sliceCoeff {g : (Fin 3 → ℂ) → ℂ} {z₀ z : Fin 3 → ℂ} (hz₀ : z₀ 2 = 0)
    {r : ℝ} (hr : 0 < r) (hg : AnalyticOnNhd ℂ g (ball z₀ r))
    (h0 : ‖z 0 - z₀ 0‖ < r / 4) (h1 : ‖z 1 - z₀ 1‖ < r / 4) (k : ℕ) :
    AnalyticAt ℂ (sliceCoeff g k) z := by
  -- the open set where the coefficient is given by the iterated Fréchet derivative
  set V : Set (Fin 3 → ℂ) := {w | ‖w 0 - z₀ 0‖ < r / 4 ∧ ‖w 1 - z₀ 1‖ < r / 4} with hV
  have hVopen : IsOpen V := by
    have c0 : Continuous fun w : Fin 3 → ℂ => ‖w 0 - z₀ 0‖ := by fun_prop
    have c1 : Continuous fun w : Fin 3 → ℂ => ‖w 1 - z₀ 1‖ := by fun_prop
    exact (isOpen_lt c0 continuous_const).inter (isOpen_lt c1 continuous_const)
  have hzV : z ∈ V := ⟨h0, h1⟩
  have hcoef : ∀ w ∈ V, sliceCoeff g k w =
      (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k g (Function.update w 2 0) (fun _ => Pi.single 2 1) := by
    intro w hw
    have hc := norm_update_zero_sub_lt hz₀ (by positivity : 0 < r / 4) hw.1 hw.2
    have hsub : ball (Function.update w 2 0) (r / 2) ⊆ ball z₀ r := by
      intro x hx
      rw [mem_ball] at hx hc ⊢
      have := dist_triangle x (Function.update w 2 0) z₀
      linarith
    have := iteratedDeriv_line_eq (f := g) (x₀ := Function.update w 2 0) (R := r / 2)
      (by positivity) (hg.mono hsub) (Pi.single 2 1) k
    unfold sliceCoeff
    rw [← this]
    congr 2
    funext l; rw [update_eq_add_smul w l]
  have hupd : AnalyticAt ℂ (fun w : Fin 3 → ℂ => Function.update w 2 0) z := by
    rw [analyticAt_pi_iff]
    intro j
    by_cases hj : j = 2
    · subst hj; simpa using analyticAt_const
    · simp only [Function.update_of_ne hj]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j).analyticAt z)
  have hmemball : Function.update z 2 0 ∈ ball z₀ r := by
    have := norm_update_zero_sub_lt hz₀ (by positivity : 0 < r / 4) h0 h1
    exact ball_subset_ball (by linarith) this
  have hfd : AnalyticAt ℂ (fun w : Fin 3 → ℂ => iteratedFDeriv ℂ k g (Function.update w 2 0)) z :=
    AnalyticAt.comp (f := fun w : Fin 3 → ℂ => Function.update w 2 0) (x := z)
      ((hg.iteratedFDeriv k) _ hmemball) hupd
  have happ : AnalyticAt ℂ (fun w : Fin 3 → ℂ =>
      iteratedFDeriv ℂ k g (Function.update w 2 0) (fun _ => Pi.single 2 1)) z :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => Fin 3 → ℂ) ℂ
      (fun _ => Pi.single 2 1)).analyticAt _).comp hfd
  have hev : sliceCoeff g k =ᶠ[𝓝 z] fun w =>
      (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k g (Function.update w 2 0) (fun _ => Pi.single 2 1) :=
    Filter.eventually_of_mem (hVopen.mem_nhds hzV) hcoef
  exact (analyticAt_const.mul happ).congr hev.symm

theorem update_mem_ball {z₀ z : Fin 3 → ℂ} (hz₀ : z₀ 2 = 0) {r : ℝ} (hr : 0 < r)
    (h0 : ‖z 0 - z₀ 0‖ < r / 4) (h1 : ‖z 1 - z₀ 1‖ < r / 4) {l : ℂ} (hl : ‖l‖ < r / 2) :
    Function.update z 2 l ∈ ball z₀ r := by
  rw [mem_ball, dist_pi_lt_iff hr]
  intro j
  rw [dist_eq_norm]
  fin_cases j
  · simpa using lt_trans h0 (by linarith)
  · simpa using lt_trans h1 (by linarith)
  · simpa [hz₀] using lt_trans hl (by linarith)

/-- Odd Taylor coefficients of an even function vanish. -/
theorem sliceCoeff_odd_eq_zero {g : (Fin 3 → ℂ) → ℂ} {z₀ z : Fin 3 → ℂ} {r : ℝ} (hr : 0 < r)
    (hz₀ : z₀ 2 = 0) (heven : ∀ w ∈ ball z₀ r, g (Function.update w 2 (-w 2)) = g w)
    (h0 : ‖z 0 - z₀ 0‖ < r / 4) (h1 : ‖z 1 - z₀ 1‖ < r / 4) (m : ℕ) :
    sliceCoeff g (2 * m + 1) z = 0 := by
  set h : ℂ → ℂ := fun l => g (Function.update z 2 l) with hh
  have hmem : ∀ l : ℂ, ‖l‖ < r / 2 → Function.update z 2 l ∈ ball z₀ r :=
    fun l hl => update_mem_ball hz₀ hr h0 h1 hl
  have hev : (fun l => h (-l)) =ᶠ[𝓝 0] h := by
    have : ball (0 : ℂ) (r / 2) ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ (by positivity)
    filter_upwards [this] with l hl
    have hl' : ‖l‖ < r / 2 := by simpa using hl
    have := heven _ (hmem l hl')
    simp only [Function.update_self, Function.update_idem] at this
    simpa [hh] using this
  have h1' := hev.iteratedDeriv_eq (2 * m + 1)
  rw [iteratedDeriv_comp_neg] at h1'
  simp only [neg_zero, Odd.neg_one_pow (odd_two_mul_add_one m)] at h1'
  have : iteratedDeriv (2 * m + 1) h 0 = 0 := by
    have h2 : -iteratedDeriv (2 * m + 1) h 0 = iteratedDeriv (2 * m + 1) h 0 := by
      simpa using h1'
    linear_combination (-1/2 : ℂ) * h2
  unfold sliceCoeff
  rw [this]; simp

theorem exists_sq_reduction {g : (Fin 3 → ℂ) → ℂ} {z₀ : Fin 3 → ℂ} (hz₀ : z₀ 2 = 0)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hg : AnalyticOnNhd ℂ g (ball z₀ δ₀))
    (heven : ∀ z ∈ ball z₀ δ₀, g (Function.update z 2 (-z 2)) = g z) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : (Fin 3 → ℂ) → ℂ,
      AnalyticOnNhd ℂ f (polydisc z₀ ![δ, δ, δ ^ 2]) ∧
      ∀ z : Fin 3 → ℂ, ‖z 0 - z₀ 0‖ < δ → ‖z 1 - z₀ 1‖ < δ → ‖z 2‖ < δ →
        g z = f (Function.update z 2 (z 2 ^ 2)) := by
  -- a ball on which `g` is bounded
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hg.continuousOn.continuousAt (ball_mem_nhds z₀ hδ₀)).norm.eventually
      (gt_mem_nhds (lt_add_one ‖g z₀‖)))
  set r : ℝ := min ε δ₀ with hrdef
  have hr : 0 < r := lt_min hε hδ₀
  have hrδ : r ≤ δ₀ := min_le_right _ _
  have hrε : r ≤ ε := min_le_left _ _
  set M : ℝ := ‖g z₀‖ + 1 with hMdef
  have hgr : AnalyticOnNhd ℂ g (ball z₀ r) := hg.mono (ball_subset_ball hrδ)
  have hM : ∀ w ∈ ball z₀ r, ‖g w‖ ≤ M := fun w hw =>
    (hεb w (ball_subset_ball hrε hw)).le
  have hM0 : 0 ≤ M := by positivity
  have hevr : ∀ w ∈ ball z₀ r, g (Function.update w 2 (-w 2)) = g w := fun w hw =>
    heven w (ball_subset_ball hrδ hw)
  refine ⟨r / 4, by positivity, ?_⟩
  set δ : ℝ := r / 4 with hδ
  set U : Set (Fin 3 → ℂ) := polydisc z₀ ![δ, δ, δ ^ 2] with hU
  have hUopen : IsOpen U := isOpen_polydisc _ _
  have hUmem : ∀ w ∈ U, ‖w 0 - z₀ 0‖ < δ ∧ ‖w 1 - z₀ 1‖ < δ ∧ ‖w 2‖ < δ ^ 2 := by
    intro w hw
    refine ⟨by simpa using hw 0, by simpa using hw 1, ?_⟩
    simpa [hz₀] using hw 2
  -- the terms
  set T : ℕ → (Fin 3 → ℂ) → ℂ := fun m w => sliceCoeff g (2 * m) w * w 2 ^ m with hT
  set u : ℕ → ℝ := fun m => M * (1 / 4) ^ m with hu
  have husum : Summable u := (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M
  have hTb : ∀ m, ∀ w ∈ U, ‖T m w‖ ≤ u m := by
    intro m w hw
    obtain ⟨h0, h1, h2⟩ := hUmem w hw
    have hc := norm_sliceCoeff_le hz₀ hr hgr hM (z := w) (by simpa [hδ] using h0)
      (by simpa [hδ] using h1) (2 * m)
    calc ‖T m w‖ = ‖sliceCoeff g (2 * m) w‖ * ‖w 2‖ ^ m := by simp [hT, norm_pow]
      _ ≤ M / (r / 2) ^ (2 * m) * (δ ^ 2) ^ m := by
          gcongr
      _ = u m := by
          have e : (r / 4) ^ 2 / ((r / 2) ^ 2) = 1 / 4 := by field_simp; norm_num
          rw [hu, hδ]; simp only
          rw [pow_mul (r / 2) 2 m, div_mul_eq_mul_div, mul_div_assoc, ← div_pow, e]
  have hTan : ∀ m, AnalyticOnNhd ℂ (T m) U := by
    intro m w hw
    obtain ⟨h0, h1, _⟩ := hUmem w hw
    have h2 : AnalyticAt ℂ (fun v : Fin 3 → ℂ => v 2 ^ m) w :=
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) 2).analyticAt w)).pow m
    exact (analyticAt_sliceCoeff hz₀ hr hgr (by simpa [hδ] using h0) (by simpa [hδ] using h1)
      (2 * m)).mul h2
  have hfan : ∀ N, AnalyticOnNhd ℂ (fun w => ∑ m ∈ Finset.range N, T m w) U := by
    intro N w hw
    exact Finset.analyticAt_fun_sum _ (fun m _ => hTan m w hw)
  have hfb : ∀ N, ∀ w ∈ U, ‖∑ m ∈ Finset.range N, T m w‖ ≤ ∑' m, u m := by
    intro N w hw
    calc ‖∑ m ∈ Finset.range N, T m w‖ ≤ ∑ m ∈ Finset.range N, ‖T m w‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range N, u m := Finset.sum_le_sum fun m _ => hTb m w hw
      _ ≤ ∑' m, u m := husum.sum_le_tsum _ (fun m _ => by
          have := hTb m w hw
          exact le_trans (norm_nonneg _) this)
  have hFan : AnalyticOnNhd ℂ (fun w => ∑' m, T m w) U :=
    analyticOnNhd_of_tendstoUniformlyOn hUopen hfan hfb (tendstoUniformlyOn_tsum_nat husum hTb)
  refine ⟨fun w => ∑' m, T m w, hFan, ?_⟩
  intro z h0 h1 h2
  have h0' : ‖z 0 - z₀ 0‖ < r / 4 := by simpa [hδ] using h0
  have h1' : ‖z 1 - z₀ 1‖ < r / 4 := by simpa [hδ] using h1
  have h2' : ‖z 2‖ < r / 4 := by simpa [hδ] using h2
  have hwU : Function.update z 2 (z 2 ^ 2) ∈ U := by
    intro j
    fin_cases j
    · simpa using h0
    · simpa using h1
    · have : ‖z 2 ^ 2‖ < δ ^ 2 := by
        rw [norm_pow]; exact pow_lt_pow_left₀ h2 (norm_nonneg _) two_ne_zero
      simpa [hz₀] using this
  -- Taylor expansion in the third variable
  set h : ℂ → ℂ := fun l => g (Function.update z 2 l) with hh
  have hdiff : DifferentiableOn ℂ h (ball 0 (r / 2)) := by
    intro l hl
    have hl' : ‖l‖ < r / 2 := by simpa using hl
    exact ((analyticAt_update_line g z 2 l
      (hgr _ (update_mem_ball hz₀ hr h0' h1' hl'))).differentiableAt).differentiableWithinAt
  have hx : z 2 ∈ ball (0 : ℂ) (r / 2) := by
    rw [mem_ball_zero_iff]; linarith
  have hts := Complex.hasSum_taylorSeries_on_ball hdiff hx
  have hhz : h (z 2) = g z := by simp [hh]
  rw [hhz] at hts
  set term : ℕ → ℂ := fun n => sliceCoeff g n z * z 2 ^ n with hterm
  have hts' : HasSum term (g z) := by
    convert hts using 1
    funext n
    simp only [hterm, sliceCoeff, hh, smul_eq_mul, sub_zero]
    ring
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b hab => by
    simpa using hab
  have hzero : ∀ n, n ∉ Set.range (fun m : ℕ => 2 * m) → term n = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := by
      rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
      · exact absurd ⟨m, hm.symm⟩ hn
      · exact ⟨m, hm⟩
    simp [hterm, sliceCoeff_odd_eq_zero hr hz₀ hevr h0' h1' m]
  have hev := (hinj.hasSum_iff hzero).mpr hts'
  have hFeq : ∑' m, T m (Function.update z 2 (z 2 ^ 2)) = g z := by
    refine Eq.trans ?_ hev.tsum_eq
    refine tsum_congr fun m => ?_
    simp only [hT, hterm, Function.comp, sliceCoeff, Function.update_idem, Function.update_self]
    rw [pow_mul]
  exact hFeq.symm

end Balaban.Symmetry
