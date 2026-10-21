/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-!
# The source ray: the increment `F(g) = F(0) + ⟨g, ℳ(g)⟩₁`

For `F` analytic on the `ℓ¹` ball `{g : ∑ |g_{x,i}| < G}` of sources,
`F(g) - F(0) = ∑_{x,i} g_{x,i} ℳ_{x,i}(g)` with `ℳ_{x,i}(g) = ∫₀¹ ∂_{x,i} F (t g) dt`
(`sub_eq_sum_srcM`, from the fundamental theorem of calculus along the segment `t ↦ t g`).  If `F` is
bounded by `B` on the ball of radius `G > 1`, then `|ℳ_{x,i}(g)| ≤ B / (G - 1)` for `‖g‖₁ < 1`
(`norm_srcM_le`, the Cauchy estimate for the derivative in the direction of the unit source), and
`ℳ_{x,i} = 0` if `F` does not depend on the source at `x` (`srcM_eq_zero`).  `srcMVec` is the vector
`ℳ_x`; the covariance under linear maps is in `SourceRayLinear`.
-/

@[expose] public section

namespace Balaban.Analysis

open Metric Set MeasureTheory intervalIntegral

variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]

/-- The unit source at `(x, i)`. -/
def unitSrc (x : ι) (i : J) : ι → J → ℂ := Pi.single x (Pi.single i 1)

theorem eq_sum_unitSrc (g : ι → J → ℂ) : g = ∑ x, ∑ i, g x i • unitSrc x i := by
  funext y j
  simp only [Finset.sum_apply, Pi.smul_apply, unitSrc, smul_eq_mul]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq ι] [DecidableEq J] in
theorem l1_smul_lt {G : ℝ} {g : ι → J → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < G) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : ∑ x, ∑ i, ‖((t : ℂ) • g) x i‖ < G := by
  have : ∑ x, ∑ i, ‖((t : ℂ) • g) x i‖ = t * ∑ x, ∑ i, ‖g x i‖ := by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0,
      Finset.mul_sum]
  rw [this]
  have h0 : 0 ≤ ∑ x, ∑ i, ‖g x i‖ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  nlinarith

/-- **The source increment.**  For `F` analytic on the `ℓ¹` ball of radius `G` and `g` in it,
`F g - F 0 = ∑_{x,i} g_{x,i} ∫₀¹ ∂_{x,i} F (t g) dt`. -/
theorem sub_eq_sum_integral {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | ∑ x, ∑ i, ‖g x i‖ < G}) {g : ι → J → ℂ}
    (hg : ∑ x, ∑ i, ‖g x i‖ < G) :
    F g - F 0 = ∑ x, ∑ i, g x i * ∫ t in (0 : ℝ)..1, fderiv ℂ F ((t : ℂ) • g) (unitSrc x i) := by

  set U : Set (ι → J → ℂ) := {g | ∑ x, ∑ i, ‖g x i‖ < G} with hU
  have hmem : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ((t : ℂ) • g) ∈ U := fun t ht =>
    l1_smul_lt hg ht.1 ht.2
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ F ((t : ℂ) • g) := fun t ht =>
    (hF _ (hmem t ht)).differentiableAt
  have hder : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F ((t : ℂ) • g)) (fderiv ℂ F ((t : ℂ) • g) g) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) • g) g t := by
      have := (hasDerivAt_id t).ofReal_comp.smul_const g
      simpa using this
    have h2 : HasFDerivAt (𝕜 := ℝ) F ((fderiv ℂ F ((t : ℂ) • g)).restrictScalars ℝ) ((t : ℂ) • g) :=
      (hdiff t ht).hasFDerivAt.restrictScalars ℝ
    exact h2.comp_hasDerivAt t h1
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) g) (Icc (0 : ℝ) 1) := by
    have hA : AnalyticOnNhd ℂ (fderiv ℂ F) U := hF.fderiv
    have hc1 : ContinuousOn (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g)) (Icc (0 : ℝ) 1) := by
      refine hA.continuousOn.comp (g := fderiv ℂ F) ?_ (fun t ht => hmem t ht)
      exact (Complex.continuous_ofReal.smul continuous_const).continuousOn
    exact hc1.clm_apply continuousOn_const
  have hint := integral_eq_sub_of_hasDerivAt (fun t ht => hder t (by rwa [uIcc_of_le zero_le_one] at ht)) (hcont.intervalIntegrable_of_Icc zero_le_one)
  have hF0 : F (((0 : ℝ) : ℂ) • g) = F 0 := by simp
  have hF1 : F (((1 : ℝ) : ℂ) • g) = F g := by simp
  simp only [hF0, hF1] at hint
  rw [← hint]
  -- expand `g` in the unit sources
  have hexp : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → fderiv ℂ F ((t : ℂ) • g) g =
      ∑ x, ∑ i, g x i * fderiv ℂ F ((t : ℂ) • g) (unitSrc x i) := by
    intro t ht
    calc fderiv ℂ F ((t : ℂ) • g) g = fderiv ℂ F ((t : ℂ) • g) (∑ x, ∑ i, g x i • unitSrc x i) :=
          congrArg _ (eq_sum_unitSrc g)
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  have hcx : ∀ x i, ContinuousOn (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) (unitSrc x i)) (Icc (0 : ℝ) 1) := by
    intro x i
    have hA : AnalyticOnNhd ℂ (fderiv ℂ F) U := hF.fderiv
    have hc1 : ContinuousOn (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g)) (Icc (0 : ℝ) 1) := by
      refine hA.continuousOn.comp (g := fderiv ℂ F) ?_ (fun t ht => hmem t ht)
      exact (Complex.continuous_ofReal.smul continuous_const).continuousOn
    exact hc1.clm_apply continuousOn_const
  have hii : ∀ x i, IntervalIntegrable (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) (unitSrc x i)) volume 0 1 :=
    fun x i => (hcx x i).intervalIntegrable_of_Icc zero_le_one
  rw [integral_congr (fun t ht => hexp t (by rwa [uIcc_of_le zero_le_one] at ht))]
  have hI : ∀ x : ι, IntervalIntegrable (fun t : ℝ => ∑ i, g x i * fderiv ℂ F ((t : ℂ) • g) (unitSrc x i))
      volume 0 1 := fun x => by
    have := IntervalIntegrable.sum Finset.univ (fun i _ => (hii x i).const_mul (g x i))
    convert this using 1
    funext t; simp [Finset.sum_apply]
  rw [integral_finsetSum (fun x _ => hI x)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum (fun i _ => (hii x i).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul]

/-- The `ℓ¹` norm of a source. -/
noncomputable def l1src (g : ι → J → ℂ) : ℝ := ∑ x, ∑ i, ‖g x i‖

theorem l1src_unitSrc (x : ι) (i : J) : l1src (unitSrc x i) = 1 := by
  unfold l1src unitSrc
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · intro b _ hb; simp [hb]
  · simp

omit [DecidableEq ι] [DecidableEq J] in
theorem l1src_add_le (a b : ι → J → ℂ) : l1src (a + b) ≤ l1src a + l1src b := by
  unfold l1src
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => norm_add_le _ _

omit [DecidableEq ι] [DecidableEq J] in
theorem l1src_smul (c : ℂ) (a : ι → J → ℂ) : l1src (c • a) = ‖c‖ * l1src a := by
  unfold l1src
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Finset.mul_sum]

/-- **Cauchy estimate for the derivative in a unit source direction.**  `F` analytic on the `ℓ¹` ball of
radius `G > 1` and bounded by `B` there: `|∂_{x,i} F (h)| ≤ B / (G - 1)` for `‖h‖₁ < 1`. -/
theorem norm_fderiv_unitSrc_le {F : (ι → J → ℂ) → ℂ} {G B : ℝ} (hG : 1 < G)
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) (hB : ∀ g, l1src g < G → ‖F g‖ ≤ B)
    {h : ι → J → ℂ} (hh : l1src h < 1) (x : ι) (i : J) :
    ‖fderiv ℂ F h (unitSrc x i)‖ ≤ B / (G - 1) := by
  set e := unitSrc x i with he
  have hin : ∀ c : ℂ, ‖c‖ ≤ G - 1 → l1src (h + c • e) < G := by
    intro c hc
    have := l1src_add_le h (c • e)
    rw [l1src_smul, he, l1src_unitSrc] at this
    linarith
  have hd : DifferentiableOn ℂ (fun c : ℂ => F (h + c • e)) (closedBall 0 (G - 1)) := by
    intro c hc
    have hc' : ‖c‖ ≤ G - 1 := by simpa using hc
    have hA : AnalyticAt ℂ F (h + c • e) := hF _ (hin c hc')
    have hL : AnalyticAt ℂ (fun c : ℂ => h + c • e) c :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    exact (AnalyticAt.comp (f := fun c : ℂ => h + c • e) hA hL).differentiableAt.differentiableWithinAt
  have hpos : 0 < G - 1 := by linarith
  have hdc : DiffContOnCl ℂ (fun c : ℂ => F (h + c • e)) (ball 0 (G - 1)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hpos.ne']
    exact hd
  have hsph : ∀ c ∈ sphere (0 : ℂ) (G - 1), ‖F (h + c • e)‖ ≤ B := by
    intro c hc
    have hc' : ‖c‖ ≤ G - 1 := by simp at hc; exact hc.le
    exact hB _ (hin c hc')
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hpos hdc hsph
  have hderiv : deriv (fun c : ℂ => F (h + c • e)) 0 = fderiv ℂ F h e := by
    have hF1 : DifferentiableAt ℂ F h := (hF h (by show l1src h < G; linarith)).differentiableAt
    have h1 : HasDerivAt (fun c : ℂ => h + c • e) e 0 := by
      have := (hasDerivAt_id (0 : ℂ)).smul_const e
      simpa using this.const_add h
    have h2 := (show HasFDerivAt F (fderiv ℂ F h) ((fun c : ℂ => h + c • e) 0) by
      simpa using hF1.hasFDerivAt).comp_hasDerivAt (0 : ℂ) h1
    exact h2.deriv
  rw [hderiv] at hcau
  exact hcau

/-- **The coefficient `ℳ_{x,i}(g) = ∫₀¹ ∂_{x,i} F (t g) dt`** of the source increment. -/
noncomputable def srcM (F : (ι → J → ℂ) → ℂ) (g : ι → J → ℂ) (x : ι) (i : J) : ℂ :=
  ∫ t in (0 : ℝ)..1, fderiv ℂ F ((t : ℂ) • g) (unitSrc x i)

/-- **`F(g) = F(0) + ⟨g, ℳ(g)⟩₁`** for `F` analytic on the `ℓ¹` ball of radius `G > 0`. -/
theorem sub_eq_sum_srcM {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) {g : ι → J → ℂ} (hg : l1src g < G) :
    F g = F 0 + ∑ x, ∑ i, g x i * srcM F g x i := by
  have := sub_eq_sum_integral hF hg
  unfold srcM
  linear_combination this

/-- **The bound `|ℳ_{x,i}(g)| ≤ B / (G - 1)`** on the unit `ℓ¹` ball, `F` bounded by `B` on the
ball of radius `G > 1`. -/
theorem norm_srcM_le {F : (ι → J → ℂ) → ℂ} {G B : ℝ} (hG : 1 < G)
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) (hB : ∀ g, l1src g < G → ‖F g‖ ≤ B)
    {g : ι → J → ℂ} (hg : l1src g < 1) (x : ι) (i : J) : ‖srcM F g x i‖ ≤ B / (G - 1) := by
  unfold srcM
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := B / (G - 1)) (f := fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) (unitSrc x i)) (by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      refine norm_fderiv_unitSrc_le hG hF hB ?_ x i
      have := l1src_smul (t : ℂ) g
      rw [this, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
      have h0 : 0 ≤ l1src g := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith [ht.2])
  simpa using h

omit [DecidableEq ι] [DecidableEq J] in
theorem continuous_l1src : Continuous (l1src : (ι → J → ℂ) → ℝ) := by
  unfold l1src
  fun_prop

omit [Fintype ι] [Fintype J] in
theorem add_smul_unitSrc_eq_update (h : ι → J → ℂ) (x : ι) (i : J) (c : ℂ) :
    h + c • unitSrc x i = Function.update h x (h x + c • Pi.single i 1) := by
  funext y j
  by_cases hy : y = x
  · subst hy; simp [unitSrc]
  · simp [unitSrc, hy]

/-- The derivative in the direction `(x, i)` vanishes if `F` does not depend on the source at `x`
(near `h`). -/
theorem fderiv_unitSrc_eq_zero {F : (ι → J → ℂ) → ℂ} {h : ι → J → ℂ}
    (hd : DifferentiableAt ℂ F h) (x : ι) (i : J)
    (hx : ∀ᶠ c : ℂ in nhds 0, F (h + c • unitSrc x i) = F h) :
    fderiv ℂ F h (unitSrc x i) = 0 := by
  have h1 : HasDerivAt (fun c : ℂ => h + c • unitSrc x i) (unitSrc x i) 0 := by
    have := (hasDerivAt_id (0 : ℂ)).smul_const (unitSrc x i)
    simpa using this.const_add h
  have h2 := (show HasFDerivAt F (fderiv ℂ F h) ((fun c : ℂ => h + c • unitSrc x i) 0) by
      simpa using hd.hasFDerivAt).comp_hasDerivAt (0 : ℂ) h1
  have h3 : HasDerivAt (fun c : ℂ => F (h + c • unitSrc x i)) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (F h)).congr_of_eventuallyEq hx
  exact h2.unique h3

/-- **Locality**: if `F` does not depend on the source at the site `x` (inside the ball), then
`ℳ_{x,i} = 0`. -/
theorem srcM_eq_zero {F : (ι → J → ℂ) → ℂ} {G : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | l1src g < G}) (x : ι)
    (hx : ∀ h, l1src h < G → ∀ c, l1src (Function.update h x c) < G → F (Function.update h x c) = F h)
    {g : ι → J → ℂ} (hg : l1src g < G) (i : J) : srcM F g x i = 0 := by
  unfold srcM
  have : ∀ t ∈ Set.uIcc (0 : ℝ) 1, fderiv ℂ F ((t : ℂ) • g) (unitSrc x i) = 0 := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hh := l1_smul_lt hg ht.1 ht.2
    refine fderiv_unitSrc_eq_zero (hF _ hh).differentiableAt x i ?_
    have hc : Continuous fun c : ℂ => l1src ((t : ℂ) • g + c • unitSrc x i) :=
      continuous_l1src.comp (by fun_prop)
    have hev : ∀ᶠ c : ℂ in nhds 0, l1src ((t : ℂ) • g + c • unitSrc x i) < G := by
      have := hc.continuousAt (x := 0)
      refine this.eventually (gt_mem_nhds ?_)
      show l1src ((t : ℂ) • g + (0 : ℂ) • unitSrc x i) < G
      rw [zero_smul, add_zero]; exact hh
    filter_upwards [hev] with c hc'
    rw [add_smul_unitSrc_eq_update] at hc' ⊢
    exact hx _ hh _ hc'
  rw [intervalIntegral.integral_congr this]
  simp

/-- **The vector `ℳ_x(Y)`**: the components `ℳ_{x,i}(g)`, `i ∈ J`, of the source coefficient at the
site `x`. -/
noncomputable def srcMVec (F : (ι → J → ℂ) → ℂ) (g : ι → J → ℂ) (x : ι) : J → ℂ :=
  fun i => srcM F g x i

/-- The ray integral of the derivative in an arbitrary direction `v`. -/
noncomputable def srcMDir (F : (ι → J → ℂ) → ℂ) (g v : ι → J → ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, fderiv ℂ F ((t : ℂ) • g) v

omit [Fintype ι] [Fintype J] in
theorem srcM_eq_srcMDir (F : (ι → J → ℂ) → ℂ) (g : ι → J → ℂ) (x : ι) (i : J) :
    srcM F g x i = srcMDir F g (unitSrc x i) := rfl

end Balaban.Analysis

