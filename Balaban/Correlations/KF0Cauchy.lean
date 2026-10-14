/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.Cauchy
public import Balaban.Localization.DecoupledCovParam
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Cauchy / fundamental-theorem construction of the first-order terms

Model-independent lemmas.  Sources are functions `g : α → β → ℂ` on finite index sets (sites and
spin components); `l1 g = ∑ a, ∑ b, ‖g a b‖` and the source ball is `{l1 g < 1}`.  For a function
`F` on the source space put
`kf0Deriv F g a b = ∫₀¹ ∂_{g_b(a)} F(t g) dt`.  If `F` is analytic on the source ball then

* (a) `F g - F 0 = ∑_{a,b} g_b(a) kf0Deriv F g a b` on the ball;
* (b) if `‖F‖ ≤ B` on the ball then `‖kf0Deriv F g a b‖ ≤ 4 B` for `l1 g ≤ 1/2`
  (a Cauchy estimate on a disc of radius `1/4`);
* (c) if `F` depends only on the coordinates in `X` then so does `kf0Deriv F · a b`, and it
  vanishes for `a ∉ X`;
* (d) `g ↦ kf0Deriv F g a b` is analytic on the whole source ball.
-/

@[expose] public section

namespace Balaban.Correlations

open Metric Set intervalIntegral

section Defs

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The source `δ_{a,b}`: `1` at site `a` and component `b`, `0` elsewhere. -/
def unitSource (a : α) (b : β) : α → β → ℂ := Pi.single a (Pi.single b 1)

/-- `∫₀¹ ∂_{g_b(a)} F(t g) dt`, the derivative being the complex derivative of
`s ↦ F(t g + s δ_{a,b})` at `s = 0`. -/
noncomputable def kf0Deriv (F : (α → β → ℂ) → ℂ) (g : α → β → ℂ) (a : α) (b : β) : ℂ :=
  ∫ t in (0 : ℝ)..1, deriv (fun s : ℂ => F ((t : ℂ) • g + s • unitSource a b)) 0

end Defs

section L1

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The `ℓ¹` norm of a source. -/
noncomputable def l1 (g : α → β → ℂ) : ℝ := ∑ a, ∑ b, ‖g a b‖

/-- The source ball `{ℓ¹ norm < 1}`. -/
def ball1 (α β : Type*) [Fintype α] [Fintype β] : Set (α → β → ℂ) := {g | l1 g < 1}

theorem l1_nonneg (g : α → β → ℂ) : 0 ≤ l1 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem isOpen_ball1 : IsOpen (ball1 α β) :=
  isOpen_lt (by unfold l1; fun_prop) continuous_const

theorem zero_mem_ball1 : (0 : α → β → ℂ) ∈ ball1 α β := by
  simp [ball1, l1]

theorem l1_smul (c : ℂ) (g : α → β → ℂ) : l1 (c • g) = ‖c‖ * l1 g := by
  unfold l1
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Finset.mul_sum]

theorem l1_add_le (g g' : α → β → ℂ) : l1 (g + g') ≤ l1 g + l1 g' := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => norm_add_le _ _

theorem l1_le_add (e e₀ : α → β → ℂ) :
    l1 e ≤ l1 e₀ + (Fintype.card α * Fintype.card β : ℝ) * ‖e - e₀‖ := by
  have h1 : l1 e ≤ l1 e₀ + l1 (e - e₀) := by
    have := l1_add_le e₀ (e - e₀)
    simpa using this
  refine h1.trans (add_le_add_right ?_ _)
  unfold l1
  calc ∑ a, ∑ b, ‖(e - e₀) a b‖ ≤ ∑ _a : α, ∑ _b : β, ‖e - e₀‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          (norm_le_pi_norm ((e - e₀) a) b).trans (norm_le_pi_norm (e - e₀) a)
    _ = (Fintype.card α * Fintype.card β : ℝ) * ‖e - e₀‖ := by simp; ring

theorem convex_ball1 : Convex ℝ (ball1 α β) := by
  intro g hg g' hg' a b ha hb hab
  show l1 (a • g + b • g') < 1
  have e : ∀ (c : ℝ) (x : α → β → ℂ), c • x = (c : ℂ) • x := fun c x => by
    funext y j; simp [Complex.real_smul]
  rw [e, e]
  have h1 := l1_add_le ((a : ℂ) • g) ((b : ℂ) • g')
  rw [l1_smul, l1_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] at h1
  have hg1 : l1 g < 1 := hg
  have hg2 : l1 g' < 1 := hg'
  have hpos : 0 < a * (1 - l1 g) + b * (1 - l1 g') := by
    rcases ha.eq_or_lt with h0 | h0
    · have hb1 : b = 1 := by linarith
      rw [← h0, hb1]; linarith
    · exact add_pos_of_pos_of_nonneg (mul_pos h0 (by linarith)) (mul_nonneg hb (by linarith))
  nlinarith

variable [DecidableEq α] [DecidableEq β]

theorem l1_unitSource (a : α) (b : β) : l1 (unitSource a b) = 1 := by
  unfold l1 unitSource
  rw [Finset.sum_eq_single a (fun y _ hy => by simp [hy]) (by simp)]
  rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem sum_smul_unitSource (g : α → β → ℂ) :
    g = ∑ a, ∑ b, g a b • unitSource a b := by
  funext y j
  simp only [Finset.sum_apply, Pi.smul_apply, unitSource, smul_eq_mul]
  rw [Finset.sum_eq_single y (fun a _ ha => by simp [ha]) (by simp)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

omit [DecidableEq α] [DecidableEq β] in
theorem smul_mem_ball1 {g : α → β → ℂ} (hg : g ∈ ball1 α β) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ((t : ℂ) • g) ∈ ball1 α β := by
  show l1 ((t : ℂ) • g) < 1
  rw [l1_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have : l1 g < 1 := hg
  nlinarith [ht.2, l1_nonneg g]

/-- A line through a point of the ball: used for the Cauchy estimate. -/
theorem line_mem_ball1 {w : α → β → ℂ} {r : ℝ} (hw : l1 w ≤ r) (a : α) (b : β) {l : ℂ}
    (hl : ‖l‖ < 1 - r) : (w + l • unitSource a b) ∈ ball1 α β := by
  show l1 _ < 1
  have := l1_add_le w (l • unitSource a b)
  rw [l1_smul, l1_unitSource] at this
  linarith

variable {F : (α → β → ℂ) → ℂ}

omit [DecidableEq α] [DecidableEq β] in
theorem deriv_line (w v : α → β → ℂ) (hd : DifferentiableAt ℂ F w) :
    deriv (fun s : ℂ => F (w + s • v)) 0 = fderiv ℂ F w v := by
  have h1 : HasDerivAt (fun l : ℂ => w + l • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add w
  have h3 : HasFDerivAt F (fderiv ℂ F w) (w + (0 : ℂ) • v) := by simpa using hd.hasFDerivAt
  exact (h3.comp_hasDerivAt (0 : ℂ) h1).deriv

theorem kf0Deriv_eq_integral (hF : AnalyticOnNhd ℂ F (ball1 α β)) {g : α → β → ℂ}
    (hg : g ∈ ball1 α β) (a : α) (b : β) :
    kf0Deriv F g a b = ∫ t in (0 : ℝ)..1, fderiv ℂ F ((t : ℂ) • g) (unitSource a b) := by
  unfold kf0Deriv
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  have := (hF _ (smul_mem_ball1 hg ht)).differentiableAt
  simpa using deriv_line ((t : ℂ) • g) (unitSource a b) this

omit [DecidableEq α] [DecidableEq β] in
theorem continuousOn_fderiv_ray (hF : AnalyticOnNhd ℂ F (ball1 α β)) {g : α → β → ℂ}
    (hg : g ∈ ball1 α β) (v : α → β → ℂ) :
    ContinuousOn (fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) v) (Icc (0 : ℝ) 1) := by
  have h1 : ContinuousOn (fderiv ℂ F) (ball1 α β) := hF.fderiv.continuousOn
  have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) • g) (Icc (0 : ℝ) 1) := by fun_prop
  exact (h1.comp h2 fun t ht => smul_mem_ball1 hg ht).clm_apply continuousOn_const

/-- (a) The fundamental theorem of calculus along `t ↦ t g`. -/
theorem sub_zero_eq_sum_kf0Deriv (hF : AnalyticOnNhd ℂ F (ball1 α β)) {g : α → β → ℂ}
    (hg : g ∈ ball1 α β) :
    F g - F 0 = ∑ a, ∑ b, g a b * kf0Deriv F g a b := by
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => F ((t : ℂ) • g))
      (fderiv ℂ F ((t : ℂ) • g) g) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hd : HasFDerivAt F (fderiv ℂ F ((t : ℂ) • g))  ((t : ℂ) • g) :=
      (hF _ (smul_mem_ball1 hg ht)).differentiableAt.hasFDerivAt
    have h1 : HasDerivAt (fun s : ℂ => s • g) g (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).smul_const g
    have := (hd.comp_hasDerivAt (t : ℂ) h1)
    exact this.comp_ofReal
  have hint := continuousOn_fderiv_ray hF hg g
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hint.intervalIntegrable_of_Icc zero_le_one)
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul] at hFTC
  rw [← hFTC]
  have hdec : ∀ t : ℝ, fderiv ℂ F ((t : ℂ) • g) g =
      ∑ a, ∑ b, g a b * fderiv ℂ F ((t : ℂ) • g) (unitSource a b) := by
    intro t
    have h := congrArg (fun v => fderiv ℂ F ((t : ℂ) • g) v) (sum_smul_unitSource g)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    exact h
  simp_rw [hdec]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [kf0Deriv_eq_integral hF hg, intervalIntegral.integral_const_mul]
    · exact fun b _ => ((continuousOn_const.mul
        (continuousOn_fderiv_ray hF hg (unitSource a b)))).intervalIntegrable_of_Icc zero_le_one
  · intro a _
    exact (continuousOn_finsetSum _ fun b _ => continuousOn_const.mul
        (continuousOn_fderiv_ray hF hg (unitSource a b))).intervalIntegrable_of_Icc zero_le_one

/-- (b) The Cauchy estimate with a radius: `‖kf0Deriv F g a b‖ ≤ B / r` for `l1 g ≤ 1/2` and
`0 < r ≤ 1/2` (a disc of radius `r` around `t g`). -/
theorem norm_kf0Deriv_le_radius (hF : AnalyticOnNhd ℂ F (ball1 α β)) {B r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hB : ∀ g ∈ ball1 α β, ‖F g‖ ≤ B) {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (a : α) (b : β) :
    ‖kf0Deriv F g a b‖ ≤ B / r := by
  have hg1 : g ∈ ball1 α β := by show l1 g < 1; linarith
  rw [kf0Deriv_eq_integral hF hg1]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) (unitSource a b)) (C := B / r) ?_
  · simpa using this
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hw : l1 ((t : ℂ) • g) ≤ 1 / 2 := by
    rw [l1_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htI.1]
    nlinarith [ht.2, l1_nonneg g]
  have key := Balaban.Analysis.norm_fderiv_line_le (f := F) (w := (t : ℂ) • g)
    (v := unitSource a b) (ρ := r) (M := B) hr
    (fun l hl => (hF _ (line_mem_ball1 hw a b (by linarith))).differentiableAt)
    (fun l hl => hB _ (line_mem_ball1 hw a b (by linarith)))
  exact key

/-- (b) The Cauchy estimate: `‖kf0Deriv F g a b‖ ≤ 4 B` for `l1 g ≤ 1/2`. -/
theorem norm_kf0Deriv_le (hF : AnalyticOnNhd ℂ F (ball1 α β)) {B : ℝ}
    (hB : ∀ g ∈ ball1 α β, ‖F g‖ ≤ B) {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (a : α) (b : β) :
    ‖kf0Deriv F g a b‖ ≤ 4 * B := by
  have := norm_kf0Deriv_le_radius hF (r := 1 / 4) (by norm_num) (by norm_num) hB hg a b
  rwa [show B / (1 / 4) = 4 * B by ring] at this

omit [Fintype α] [Fintype β] in
/-- (c) Locality: if `F` depends only on the coordinates in `X`, so does `kf0Deriv F · a b`. -/
theorem kf0Deriv_congr {X : Finset α} (hloc : ∀ g g' : α → β → ℂ, (∀ y ∈ X, g y = g' y) →
    F g = F g') {g g' : α → β → ℂ} (hgg : ∀ y ∈ X, g y = g' y) (a : α) (b : β) :
    kf0Deriv F g a b = kf0Deriv F g' a b := by
  unfold kf0Deriv
  refine intervalIntegral.integral_congr fun t _ => ?_
  congr 1
  funext s
  refine hloc _ _ fun y hy => ?_
  simp [hgg y hy]

omit [Fintype α] [Fintype β] in
/-- (c) `kf0Deriv F · a b` vanishes for `a ∉ X`. -/
theorem kf0Deriv_eq_zero {X : Finset α} (hloc : ∀ g g' : α → β → ℂ, (∀ y ∈ X, g y = g' y) →
    F g = F g') (g : α → β → ℂ) {a : α} (ha : a ∉ X) (b : β) : kf0Deriv F g a b = 0 := by
  unfold kf0Deriv
  have : ∀ t : ℝ, deriv (fun s : ℂ => F ((t : ℂ) • g + s • unitSource a b)) 0 = 0 := by
    intro t
    have hc : (fun s : ℂ => F ((t : ℂ) • g + s • unitSource a b)) = fun _ => F ((t : ℂ) • g) := by
      funext s
      refine hloc _ _ fun y hy => ?_
      have hya : y ≠ a := fun h => ha (h ▸ hy)
      simp [unitSource, hya]
    rw [hc]
    exact deriv_const _ _
  exact (intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun t _ => this t).trans (by simp)

/-- (d) Analyticity of `g ↦ kf0Deriv F g a b` on the source ball, for `F` analytic and bounded on
the ball. -/
theorem analyticOnNhd_kf0Deriv (hF : AnalyticOnNhd ℂ F (ball1 α β)) {B : ℝ}
    (hB : ∀ g ∈ ball1 α β, ‖F g‖ ≤ B) (a : α) (b : β) :
    AnalyticOnNhd ℂ (fun g => kf0Deriv F g a b) (ball1 α β) := by
  intro e₀ he₀
  set r₀ := l1 e₀ with hr₀
  have hr₀1 : r₀ < 1 := he₀
  set K : ℝ := (Fintype.card α * Fintype.card β : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set ε := (1 - r₀) / 2 with hε
  have hε0 : 0 < ε := by linarith
  set R : ℝ := ε / (K + 1) / 2 with hR
  have hR0 : 0 < R := by positivity
  set r₁ := r₀ + ε with hr₁
  have hr₁1 : r₁ < 1 := by linarith
  set ρ := (1 - r₁) / 2 with hρ
  have hρ0 : 0 < ρ := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 zero_mem_ball1)
  -- points of the small ball have `l1 < r₁`
  have hsmall : ∀ e ∈ ball e₀ (2 * R), l1 e ≤ r₁ := by
    intro e he
    have hd : ‖e - e₀‖ < 2 * R := by rwa [mem_ball, dist_eq_norm] at he
    have h1 := l1_le_add e e₀
    have h2 : K * ‖e - e₀‖ ≤ ε := by
      calc K * ‖e - e₀‖ ≤ K * (2 * R) := mul_le_mul_of_nonneg_left hd.le hK0
        _ = K * (ε / (K + 1)) := by rw [hR]; ring
        _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by linarith)]
          nlinarith
    linarith
  have hray : ∀ e ∈ ball e₀ (2 * R), ∀ t ∈ Icc (0 : ℝ) 1, l1 ((t : ℂ) • e) ≤ r₁ := by
    intro e he t ht
    rw [l1_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have := hsmall e he
    nlinarith [ht.2, l1_nonneg e, ht.1]
  have hsubball : ∀ e ∈ ball e₀ (2 * R), e ∈ ball1 α β := fun e he => by
    show l1 e < 1
    linarith [hsmall e he]
  have hmain : AnalyticAt ℂ (fun e => ∫ t in (0 : ℝ)..1,
      fderiv ℂ F ((t : ℂ) • e) (unitSource a b)) e₀ := by
    refine Balaban.Localization.analyticAt_intervalIntegral (R := R) (M := B / ρ) hR0
      (div_nonneg hB0 hρ0.le) zero_le_one ?_ ?_ ?_
    · intro t ht e he
      have hlin : AnalyticAt ℂ (fun e : α → β → ℂ => (t : ℂ) • e) e :=
        (analyticAt_id.const_smul (c := (t : ℂ)))
      have hmem : ((t : ℂ) • e) ∈ ball1 α β := by
        show l1 _ < 1
        linarith [hray e he t ht]
      have h2 : AnalyticAt ℂ (fderiv ℂ F) ((t : ℂ) • e) := hF.fderiv _ hmem
      have h3 := h2.comp_of_eq hlin rfl
      exact ((ContinuousLinearMap.apply ℂ ℂ (unitSource a b)).analyticAt _).comp h3
    · intro t ht e he
      have hw := hray e he t ht
      have key := Balaban.Analysis.norm_fderiv_line_le (f := F) (w := (t : ℂ) • e)
        (v := unitSource a b) (ρ := ρ) (M := B) hρ0
        (fun l hl => (hF _ (line_mem_ball1 hw a b (by linarith))).differentiableAt)
        (fun l hl => hB _ (line_mem_ball1 hw a b (by linarith)))
      exact key
    · intro e he
      exact continuousOn_fderiv_ray hF (hsubball e he) (unitSource a b)
  refine hmain.congr ?_
  filter_upwards [isOpen_ball1.mem_nhds he₀] with e he
  exact (kf0Deriv_eq_integral hF he a b).symm

end L1

end Balaban.Correlations
