/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Analyticity of exponential moments in the marks

For an integrable weight `w` and bounded measurable functions `V_j`, the exponential moment
`λ ↦ ∫ w e^{∑_j λ_j V_j}` is analytic on `ℂ^ι` (`analyticOnNhd_integral_mul_exp`). Near `0` it is
the uniform limit of the integrals of the truncated exponential series, which are polynomials in
the marks (`LamPoly.analytic_integral_of_integrable`, Weierstrass); at a general point `x` the
weight `w e^{∑ x_j V_j}` is integrable and the moment is a translate of a moment near `0`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace Balaban.Polymer

noncomputable section

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) {ι : Type*} [Fintype ι]

omit [Fintype B] in
theorem lamPoly_one_add_truncExp (V : ι → (∀ b, Ω b) → ℂ) (hVm : ∀ j, Measurable (V j))
    (hVb : ∀ j, Bdd (V j)) (N : ℕ) :
    LamPoly ι Ω (fun l Φ => 1 + truncExp N (∑ j, l j * V j Φ)) := by
  refine LamPoly.add LamPoly.one ?_
  unfold truncExp
  refine LamPoly.sum _ (fun n _ => ?_)
  have hP := LamPoly.affine (ι := ι) (Ω := Ω) (fun _ => 0) measurable_const ⟨0, fun _ => by simp⟩
    V hVm hVb
  have := (hP.pow (n + 1)).smul (((n + 1).factorial : ℂ)⁻¹)
  exact this.congr (fun l Φ => by ring)

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] in
theorem norm_sum_mul_le {C : ℝ} (V : ι → (∀ b, Ω b) → ℂ) (hC : ∀ j Φ, ‖V j Φ‖ ≤ C)
    {r : ℝ} {l : ι → ℂ} (hl : ∀ j, ‖l j‖ ≤ r) (Φ : ∀ b, Ω b) :
    ‖∑ j, l j * V j Φ‖ ≤ Fintype.card ι * (r * C) := by
  have hr : ∀ j, 0 ≤ ‖l j‖ := fun j => norm_nonneg _
  calc ‖∑ j, l j * V j Φ‖ ≤ ∑ j, ‖l j‖ * ‖V j Φ‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    _ ≤ ∑ _j : ι, r * C := Finset.sum_le_sum fun j _ =>
        mul_le_mul (hl j) (hC j Φ) (norm_nonneg _) ((hr j).trans (hl j))
    _ = _ := by simp

/-- **Analyticity near `0`.** -/
theorem analyticOnNhd_integral_mul_exp_ball (w : (∀ b, Ω b) → ℂ)
    (hw : Integrable w (Measure.pi μ)) (V : ι → (∀ b, Ω b) → ℂ) (hVm : ∀ j, Measurable (V j))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j Φ, ‖V j Φ‖ ≤ C) {r : ℝ} (hr : 0 ≤ r)
    (hrC : Fintype.card ι * (r * C) < 1) :
    AnalyticOnNhd ℂ (fun l : ι → ℂ => ∫ Φ, w Φ * Complex.exp (∑ j, l j * V j Φ) ∂(Measure.pi μ))
      (Balaban.Analysis.polydisc 0 (fun _ => r)) := by
  set q := (Fintype.card ι : ℝ) * (r * C) with hq
  have hq0 : 0 ≤ q := by positivity
  have hVb : ∀ j, Bdd (V j) := fun j => ⟨C, hC j⟩
  have hbd : ∀ l : ι → ℂ, l ∈ Balaban.Analysis.polydisc (0 : ι → ℂ) (fun _ => r) → ∀ Φ,
      ‖∑ j, l j * V j Φ‖ ≤ q := by
    intro l hl Φ
    refine norm_sum_mul_le V hC (fun j => ?_) Φ
    have := hl j
    simp only [Pi.zero_apply, sub_zero] at this
    exact this.le
  set A : ℝ := ∫ Φ, ‖w Φ‖ ∂(Measure.pi μ) with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hmL : ∀ l : ι → ℂ, Measurable fun Φ => ∑ j, l j * V j Φ := fun l =>
    Finset.measurable_sum _ fun j _ => measurable_const.mul (hVm j)
  have hPoly := fun N => lamPoly_one_add_truncExp V hVm hVb N
  have hfN : ∀ N, AnalyticOnNhd ℂ
      (fun l : ι → ℂ => ∫ Φ, w Φ * (1 + truncExp N (∑ j, l j * V j Φ)) ∂(Measure.pi μ))
      (Balaban.Analysis.polydisc 0 (fun _ => r)) := fun N =>
    ((hPoly N).analytic_integral_of_integrable μ w hw).mono (Set.subset_univ _)
  refine Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn
    (M := A * (2 * Real.exp 1 + 2))
    (f := fun N (l : ι → ℂ) => ∫ Φ, w Φ * (1 + truncExp N (∑ j, l j * V j Φ)) ∂(Measure.pi μ))
    (Balaban.Analysis.isOpen_polydisc 0 _) hfN (fun N l hl => ?_) ?_
  · have hle : ∀ Φ, ‖w Φ * (1 + truncExp N (∑ j, l j * V j Φ))‖ ≤ ‖w Φ‖ * (2 * Real.exp 1 + 2) := by
      intro Φ
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_add_le _ _).trans ?_
      rw [norm_one]
      have := norm_truncExp_le (N := N) ((hbd l hl Φ).trans hrC.le)
      linarith
    refine (norm_integral_le_of_norm_le (hw.norm.mul_const _)
      (Eventually.of_forall hle)).trans (le_of_eq ?_)
    rw [integral_mul_const]
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun N : ℕ => A * (q ^ (N + 1) * Real.exp 1)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hrC).comp (tendsto_add_atTop_nat 1)
      simpa using (this.mul_const (Real.exp 1)).const_mul A
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
    intro l hl
    have hint1 : Integrable (fun Φ => w Φ * Complex.exp (∑ j, l j * V j Φ)) (Measure.pi μ) :=
      hw.mul_bdd (Complex.measurable_exp.comp (hmL l)).aestronglyMeasurable
        (Eventually.of_forall fun Φ => (Complex.norm_exp_le_exp_norm _).trans
          (Real.exp_le_exp.2 (hbd l hl Φ)))
    have hint2 : Integrable (fun Φ => w Φ * (1 + truncExp N (∑ j, l j * V j Φ)))
        (Measure.pi μ) := by
      refine hw.mul_bdd (c := 2 * Real.exp 1 + 1 + 1) ((hPoly N).measurable l).aestronglyMeasurable
        (Eventually.of_forall fun Φ => ?_)
      refine (norm_add_le _ _).trans ?_
      rw [norm_one]
      have := norm_truncExp_le (N := N) ((hbd l hl Φ).trans hrC.le)
      linarith
    rw [dist_eq_norm, ← integral_sub hint1 hint2]
    have hle : ∀ Φ, ‖w Φ * Complex.exp (∑ j, l j * V j Φ) -
        w Φ * (1 + truncExp N (∑ j, l j * V j Φ))‖ ≤ ‖w Φ‖ * (q ^ (N + 1) * Real.exp 1) := by
      intro Φ
      rw [← mul_sub, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := norm_sub_truncExp_le N (∑ j, l j * V j Φ)
      have h2 := hbd l hl Φ
      have h3 : ‖∑ j, l j * V j Φ‖ ^ (N + 1) ≤ q ^ (N + 1) :=
        pow_le_pow_left₀ (norm_nonneg _) h2 _
      have h4 : Real.exp ‖∑ j, l j * V j Φ‖ ≤ Real.exp 1 := Real.exp_le_exp.2 (h2.trans hrC.le)
      calc ‖Complex.exp (∑ j, l j * V j Φ) - (1 + truncExp N (∑ j, l j * V j Φ))‖ =
            ‖Complex.exp (∑ j, l j * V j Φ) - 1 - truncExp N (∑ j, l j * V j Φ)‖ := by
            congr 1; ring
        _ ≤ _ := h1.trans (mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity))
    calc _ ≤ ∫ Φ, ‖w Φ‖ * (q ^ (N + 1) * Real.exp 1) ∂(Measure.pi μ) :=
          norm_integral_le_of_norm_le (hw.norm.mul_const _) (Eventually.of_forall hle)
      _ = A * (q ^ (N + 1) * Real.exp 1) := integral_mul_const _ _
      _ < ε := hN

/-- **Exponential moments are analytic in the marks.** -/
theorem analyticOnNhd_integral_mul_exp [DecidableEq ι] (w : (∀ b, Ω b) → ℂ)
    (hw : Integrable w (Measure.pi μ)) (V : ι → (∀ b, Ω b) → ℂ) (hVm : ∀ j, Measurable (V j))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j Φ, ‖V j Φ‖ ≤ C) :
    AnalyticOnNhd ℂ (fun l : ι → ℂ => ∫ Φ, w Φ * Complex.exp (∑ j, l j * V j Φ) ∂(Measure.pi μ))
      Set.univ := by
  intro x _
  set r : ℝ := 1 / (Fintype.card ι * C + 1) with hr
  have hr0 : 0 < r := by positivity
  have hrC : Fintype.card ι * (r * C) < 1 := by
    rw [hr]
    have h1 : (0 : ℝ) < Fintype.card ι * C + 1 := by positivity
    rw [show (Fintype.card ι : ℝ) * (1 / (Fintype.card ι * C + 1) * C) =
      (Fintype.card ι * C) / (Fintype.card ι * C + 1) by ring, div_lt_one h1]
    linarith
  set Lx : (∀ b, Ω b) → ℂ := fun Φ => ∑ j, x j * V j Φ
  have hmLx : Measurable Lx := Finset.measurable_sum _ fun j _ => measurable_const.mul (hVm j)
  have hw' : Integrable (fun Φ => w Φ * Complex.exp (Lx Φ)) (Measure.pi μ) :=
    hw.mul_bdd (Complex.measurable_exp.comp hmLx).aestronglyMeasurable
      (Eventually.of_forall fun Φ => (Complex.norm_exp_le_exp_norm _).trans
        (Real.exp_le_exp.2 (norm_sum_mul_le V hC (fun j => le_of_eq (rfl : ‖x j‖ = ‖x j‖) |>.trans
          (norm_le_pi_norm x j)) Φ)))
  have hG := analyticOnNhd_integral_mul_exp_ball μ (fun Φ => w Φ * Complex.exp (Lx Φ)) hw' V hVm
    hC0 hC hr0.le hrC
  have hG0 : AnalyticAt ℂ (fun l : ι → ℂ => ∫ Φ, (w Φ * Complex.exp (Lx Φ)) *
      Complex.exp (∑ j, l j * V j Φ) ∂(Measure.pi μ)) 0 :=
    hG 0 (fun j => by simpa using hr0)
  have hshift : (fun l : ι → ℂ => ∫ Φ, w Φ * Complex.exp (∑ j, l j * V j Φ) ∂(Measure.pi μ)) =
      (fun l : ι → ℂ => ∫ Φ, (w Φ * Complex.exp (Lx Φ)) *
        Complex.exp (∑ j, l j * V j Φ) ∂(Measure.pi μ)) ∘ (fun l => l - x) := by
    funext l
    simp only [Function.comp]
    refine integral_congr_ae (Eventually.of_forall fun Φ => ?_)
    simp only [Lx]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring
  rw [hshift]
  have hsub : AnalyticAt ℂ (fun l : ι → ℂ => l - x) x := analyticAt_id.sub analyticAt_const
  have hx : x - x = 0 := sub_self x
  exact AnalyticAt.comp (g := fun l : ι → ℂ => ∫ Φ, (w Φ * Complex.exp (Lx Φ)) *
    Complex.exp (∑ j, l j * V j Φ) ∂(Measure.pi μ)) (f := fun l => l - x)
    (hx ▸ hG0 : AnalyticAt ℂ _ (x - x)) hsub

end

end Balaban.Polymer
