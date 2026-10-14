/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLogDet
public import Balaban.Green.FinalTaggedRow
public import Balaban.Green.FinalCfinInverse
public import Balaban.Green.FinalPathDefect

public import Balaban.Localization.DecoupledCovParam

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The interpolated final operator: invertibility on the full closed polydisc

The tagged parametrix `taggedGfin s = G_*(s) (1 - K(s))⁻¹` of `finalOp + t` vanishes at `s = 0`
(every tag set is nonempty), so it is not invertible on any polydisc centred at `0`
(`taggedGfin_not_isUnit_zero`).  The part of the interpolated operator that stays invertible on the
whole closed polydisc `‖s p‖ ≤ e^κ` is the defect factor `1 - K(s, t)`: its weighted row sums
satisfy `‖K(s, t)‖ ≤ B e^{H κ}/M ≤ 1/4`, so `1 - K(s, t)` is invertible with the weighted row sums
of the inverse at most `4/3` (`taggedDefect_isUnit_inv_weighted`).  At `s = 0` it is the identity
and at `s = 1` it is the product `(finalOp + t) · G_*(1, t)` of the shifted operator and the
partition-of-unity box resolvent (`det_one_sub_taggedK_one`).
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- At `s = 0` all tags vanish and the tagged defect is `0`. -/
theorem taggedK_zero (hM : 0 < M) (hd : 0 < d) (t : ℝ) :
    taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t (0 : MacIdx d N₀ M → ℂ) = 0 := by
  ext x y
  simp [taggedK, taggedMat, tagMon_macTags_zero hM hd]

/-- **Obstruction.**  The tagged parametrix of `finalOp + t` is `0` at `s = 0`, hence not
invertible there; no polydisc centred at `0` is a domain of invertibility of `taggedGfin`. -/
theorem taggedGfin_not_isUnit_zero (hM : 0 < M) (hd : 0 < d) (t : ℝ) (x : L1Torus d N₀) :
    ¬ IsUnit (taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t
      (0 : MacIdx d N₀ M → ℂ)) := by
  intro h
  rw [taggedGfin_zero hM hd, isUnit_zero_iff] at h
  have := congrFun (congrFun h x) x
  simp at this

/-- **Invertibility on the full closed polydisc.**  Under the hypotheses of `taggedGfin_final`,
for `0 ≤ r ≤ ε/8` and every `s` with `‖s p‖ ≤ e^κ`, the defect `1 - K(s, t)` of the interpolated
parametrix of `finalOp + t` is invertible, and the weighted row sums of its inverse are at most
`4/3`. -/
theorem taggedDefect_isUnit_inv_weighted (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) :
    IsUnit (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s) ∧
      ∀ x, ∑ y, Real.exp (r * dist x y) *
        ‖(1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s)⁻¹ x y‖ ≤ 4 / 3 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have hw1 : ∀ x y : L1Torus d N₀, 1 ≤ Real.exp (r * dist x y) := fun x y =>
    Real.one_le_exp (mul_nonneg hr0 dist_nonneg)
  have hww : ∀ x : L1Torus d N₀, Real.exp (r * dist x x) = 1 := fun x => by simp
  have hsub : ∀ x u y : L1Torus d N₀,
      Real.exp (r * dist x y) ≤ Real.exp (r * dist x u) * Real.exp (r * dist u y) := by
    intro x u y
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [dist_triangle x u y])
  have hinv := weightedRow_inv_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw1 hww hsub
    (taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t s) (q := 1 / 4) (by norm_num)
    (fun x => (taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x).trans hq)
  have h43 : 1 / (1 - (1 / 4 : ℝ)) = 4 / 3 := by norm_num
  rw [h43] at hinv
  exact hinv

/-- **The value at `s = 1`.**  `1 - K(1, t) = (finalOp + t) · G_*(1, t)`, so the determinant of the
interpolated defect at `s = 1` is the determinant of the shifted final operator times the
determinant of the partition-of-unity box resolvent `∑_z χ_z G_z`. -/
theorem det_one_sub_taggedK_one (t : ℝ) :
    (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det =
      (shiftMat (finalOp d L N₀ k v a) t).det *
        (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det := by
  rw [taggedK_one, taggedG_one, ← Matrix.det_mul,
    ← parametrix_identity Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (fun u => by
        exact_mod_cast macChi_sum (d := d) (m := N₀) (M := M) u) (finalOp d L N₀ k v a) t]

section LogDet

open MeasureTheory Set Filter Topology

variable {Pc : Type*} [Fintype Pc] [DecidableEq Pc]

theorem fderiv_apply_eq_sum (Δ : (Pc → ℂ) → ℂ) (z s : Pc → ℂ) :
    fderiv ℂ Δ z s = ∑ p, s p * fderiv ℂ Δ z (fun j => if p = j then 1 else 0) := by
  have := LinearMap.pi_apply_eq_sum_univ (fderiv ℂ Δ z).toLinearMap s
  simpa using this

theorem analyticAt_fderiv_apply {Δ : (Pc → ℂ) → ℂ} (hΔ : ∀ z, AnalyticAt ℂ Δ z)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f g : F → Pc → ℂ} {x : F}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) :
    AnalyticAt ℂ (fun y => fderiv ℂ Δ (f y) (g y)) x := by
  have hfun : (fun y => fderiv ℂ Δ (f y) (g y)) = fun y => ∑ p, g y p *
      fderiv ℂ Δ (f y) (fun j => if p = j then 1 else 0) := funext fun y => fderiv_apply_eq_sum Δ _ _
  rw [hfun]
  refine Finset.analyticAt_fun_sum _ fun p _ => ?_
  refine AnalyticAt.mul ?_ ?_
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Pc => ℂ) p).analyticAt _).comp hg
  · exact ((ContinuousLinearMap.apply ℂ ℂ (fun j => if p = j then (1 : ℂ) else 0)).analyticAt _).comp
      ((hΔ (f x)).fderiv.comp hf)

omit [DecidableEq Pc] in
theorem continuous_fderiv_apply {Δ : (Pc → ℂ) → ℂ} (hΔ : ∀ z, AnalyticAt ℂ Δ z)
    {X : Type*} [TopologicalSpace X] {f g : X → Pc → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => fderiv ℂ Δ (f y) (g y) :=
  ((continuous_iff_continuousAt.2 fun z => (hΔ z).fderiv.continuousAt).comp hf).clm_apply hg

/-- **Analytic logarithm on a polydisc.**  An everywhere analytic `Δ` on a finite product of
planes with `Δ 0 = 1`, nonvanishing on the sup-norm ball of radius `R`, has an analytic logarithm
on every smaller ball: `ell s = ∫₀¹ (d/dλ Δ (λ s)) / Δ (λ s) dλ` (written with the substitution
`λ = (2/π) arctan x`, `x ∈ (0, ∞)`). -/
theorem exists_analytic_log_of_ne_zero {Δ : (Pc → ℂ) → ℂ} (hΔ : ∀ z, AnalyticAt ℂ Δ z)
    (h0 : Δ 0 = 1) {R R' : ℝ} (hRR : R' < R)
    (hne : ∀ s : Pc → ℂ, ‖s‖ < R → Δ s ≠ 0) :
    ∃ ell : (Pc → ℂ) → ℂ, AnalyticOnNhd ℂ ell (Metric.ball 0 R') ∧
      (∀ s ∈ Metric.ball (0 : Pc → ℂ) R', Δ s = Complex.exp (ell s)) ∧ ell 0 = 0 := by
  set W : ℝ → ℝ := fun x => 2 / Real.pi * Real.arctan x with hW
  set W' : ℝ → ℝ := fun x => 2 / Real.pi * (1 + x ^ 2)⁻¹ with hW'
  have hpi : 0 < Real.pi := Real.pi_pos
  have hWd : ∀ x, HasDerivAt W (W' x) x := fun x => by
    simpa [hW, hW'] using ((Real.hasDerivAt_arctan' x).const_mul (2 / Real.pi))
  have hWc : Continuous W := continuous_const.mul Real.continuous_arctan
  have hW'c : Continuous W' := by
    refine continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x => by positivity)
  have hW'nn : ∀ x, 0 ≤ W' x := fun x => by simp only [hW']; positivity
  have hW'int : Integrable W' := integrable_inv_one_add_sq.const_mul _
  have hW1 : ∀ x, |W x| ≤ 1 := by
    intro x
    have h1 := Real.arctan_lt_pi_div_two x
    have h2 := Real.neg_pi_div_two_lt_arctan x
    rw [abs_le]
    constructor
    · simp only [hW]
      rw [show -1 = 2 / Real.pi * (-(Real.pi / 2)) by field_simp]
      exact mul_le_mul_of_nonneg_left h2.le (by positivity)
    · simp only [hW]
      rw [show (1 : ℝ) = 2 / Real.pi * (Real.pi / 2) by field_simp]
      exact mul_le_mul_of_nonneg_left h1.le (by positivity)
  have hWpos : ∀ x, 0 ≤ x → 0 ≤ W x := fun x hx => by
    simp only [hW]; have := Real.arctan_nonneg.2 hx; positivity
  have hnv : ∀ (s : Pc → ℂ), ‖s‖ ≤ R' → ∀ l : ℝ, |l| ≤ 1 → Δ ((l : ℂ) • s) ≠ 0 := by
    intro s hs l hl
    refine hne _ ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |l| * ‖s‖ ≤ 1 * ‖s‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ < R := by linarith
  set Q : ℝ → (Pc → ℂ) → ℂ := fun l s => fderiv ℂ Δ ((l : ℂ) • s) s / Δ ((l : ℂ) • s) with hQ
  set G : ℝ → (Pc → ℂ) → ℂ := fun x s => Q (W x) s * (W' x : ℂ) with hG
  have hψ : ∀ (s : Pc → ℂ) (x : ℝ), HasDerivAt (fun x : ℝ => Δ (((W x : ℝ) : ℂ) • s))
      (fderiv ℂ Δ (((W x : ℝ) : ℂ) • s) s * (W' x : ℂ)) x := by
    intro s x
    have h1 : HasDerivAt (fun x : ℝ => ((W x : ℝ) : ℂ)) ((W' x : ℝ) : ℂ) x := (hWd x).ofReal_comp
    have h2 : HasDerivAt (fun x : ℝ => ((W x : ℝ) : ℂ) • s) (((W' x : ℝ) : ℂ) • s) x :=
      h1.smul_const s
    have h3 := (((hΔ (((W x : ℝ) : ℂ) • s)).differentiableAt.hasFDerivAt).restrictScalars ℝ
      ).comp_hasDerivAt x h2
    simpa [map_smul, mul_comm, Function.comp_def] using h3
  have hGc : ∀ s : Pc → ℂ, ‖s‖ ≤ R' → Continuous fun x => G x s := by
    intro s hs
    have hc1 : Continuous fun x : ℝ => fderiv ℂ Δ (((W x : ℝ) : ℂ) • s) s :=
      continuous_fderiv_apply hΔ ((Complex.continuous_ofReal.comp hWc).smul continuous_const)
        continuous_const
    have hc2 : Continuous fun x : ℝ => Δ (((W x : ℝ) : ℂ) • s) :=
      (continuous_iff_continuousAt.2 fun z => (hΔ z).continuousAt).comp
        ((Complex.continuous_ofReal.comp hWc).smul continuous_const)
    exact (hc1.div hc2 fun x => hnv s hs _ (hW1 x)).mul (Complex.continuous_ofReal.comp hW'c)
  -- the compact bound
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ l : ℝ, 0 ≤ l → l ≤ 1 → ∀ s : Pc → ℂ, ‖s‖ ≤ R' → ‖Q l s‖ ≤ C := by
    have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Pc → ℂ) R') :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hc1 : Continuous fun p : ℝ × (Pc → ℂ) => fderiv ℂ Δ (((p.1 : ℝ) : ℂ) • p.2) p.2 :=
      continuous_fderiv_apply hΔ ((Complex.continuous_ofReal.comp continuous_fst).smul
        continuous_snd) continuous_snd
    have hc2 : Continuous fun p : ℝ × (Pc → ℂ) => Δ (((p.1 : ℝ) : ℂ) • p.2) :=
      (continuous_iff_continuousAt.2 fun z => (hΔ z).continuousAt).comp
        ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd)
    have hcQ : ContinuousOn (fun p : ℝ × (Pc → ℂ) => Q p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Pc → ℂ) R') := by
      refine hc1.continuousOn.div hc2.continuousOn fun p hp => ?_
      have hp1 : |p.1| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hp.1.1], hp.1.2⟩
      exact hnv p.2 (by simpa using hp.2) _ hp1
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcQ
    exact ⟨C, fun l hl0 hl1 s hs => hC (l, s) ⟨⟨hl0, hl1⟩, by simpa using hs⟩⟩
  have hGb : ∀ (x : ℝ), 0 ≤ x → ∀ s : Pc → ℂ, ‖s‖ ≤ R' → ‖G x s‖ ≤ C * W' x := by
    intro x hx s hs
    have hWx1 : W x ≤ 1 := (abs_le.1 (hW1 x)).2
    have := hC (W x) (hWpos x hx) hWx1 s hs
    rw [hG]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW'nn x)]
    exact mul_le_mul_of_nonneg_right this (hW'nn x)
  refine ⟨fun s => ∫ x in Ioi (0 : ℝ), G x s, ?_, ?_, ?_⟩
  · refine Balaban.Localization.analyticOnNhd_integral_Ioi (g := fun x => C * W' x)
      Metric.isOpen_ball ?_ ?_ ?_ ?_ ?_
    · intro x hx e he
      have hWx : |W x| ≤ 1 := hW1 x
      have hs : ‖e‖ ≤ R' := (mem_ball_zero_iff.1 he).le
      have ha1 : AnalyticAt ℂ (fun s : Pc → ℂ => ((W x : ℝ) : ℂ) • s) e :=
        (((W x : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (Pc → ℂ)).analyticAt e
      have ha2 : AnalyticAt ℂ (fun s : Pc → ℂ => Δ (((W x : ℝ) : ℂ) • s)) e :=
        (hΔ _).comp ha1
      have ha3 : AnalyticAt ℂ (fun s : Pc → ℂ => fderiv ℂ Δ (((W x : ℝ) : ℂ) • s) s) e :=
        analyticAt_fderiv_apply hΔ ha1 analyticAt_id
      exact (ha3.div ha2 (hnv e hs _ hWx)).mul analyticAt_const
    · intro e he
      exact (hGc e (mem_ball_zero_iff.1 he).le).continuousOn
    · exact (continuous_const.mul hW'c).continuousOn
    · exact (hW'int.const_mul C).integrableOn
    · intro x hx e he
      exact hGb x hx.le e (mem_ball_zero_iff.1 he).le
  · intro s hs
    have hs' : ‖s‖ ≤ R' := (mem_ball_zero_iff.1 hs).le
    -- primitive
    have hint : IntegrableOn (fun x => G x s) (Ioi (0 : ℝ)) := by
      refine Integrable.mono' (hW'int.const_mul C).integrableOn
        (hGc s hs').aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact ae_of_all _ fun x hx => hGb x (le_of_lt hx) s hs'
    set m : ℝ → ℂ := fun X => ∫ x in (0 : ℝ)..X, G x s with hm
    have hmd : ∀ X, HasDerivAt m (G X s) X := fun X =>
      intervalIntegral.integral_hasDerivAt_right
        ((hGc s hs').intervalIntegrable _ _)
        ((hGc s hs').stronglyMeasurableAtFilter _ _) (hGc s hs').continuousAt
    have hfd : ∀ X, HasDerivAt (fun X : ℝ => Δ (((W X : ℝ) : ℂ) • s) * Complex.exp (-m X)) 0 X := by
      intro X
      have h1 := hψ s X
      have h2 : HasDerivAt (fun X : ℝ => Complex.exp (-m X))
          (Complex.exp (-m X) * (-(G X s))) X := (hmd X).neg.cexp
      have h3 := h1.mul h2
      have hnz := hnv s hs' (W X) (hW1 X)
      convert h3 using 1
      simp only [hG, hQ]
      field_simp
      ring
    have hconst : ∀ X, Δ (((W X : ℝ) : ℂ) • s) * Complex.exp (-m X) = 1 := by
      intro X
      have hdiff : Differentiable ℝ fun X : ℝ => Δ (((W X : ℝ) : ℂ) • s) * Complex.exp (-m X) :=
        fun X => (hfd X).differentiableAt
      have := is_const_of_deriv_eq_zero hdiff (fun X => (hfd X).deriv) X 0
      rw [this]
      have hW0 : W 0 = 0 := by simp [hW]
      simp [hW0, hm, h0]
    have hexp : ∀ X, Δ (((W X : ℝ) : ℂ) • s) = Complex.exp (m X) := by
      intro X
      have := hconst X
      rw [Complex.exp_neg] at this
      have hne' := Complex.exp_ne_zero (m X)
      field_simp at this
      exact this
    have hlim1 : Tendsto m atTop (𝓝 (∫ x in Ioi (0 : ℝ), G x s)) :=
      intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    have hWlim : Tendsto W atTop (𝓝 1) := by
      have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul (2 / Real.pi)
      rw [show 2 / Real.pi * (Real.pi / 2) = 1 by field_simp] at this
      exact this
    have hlim2 : Tendsto (fun X => Δ (((W X : ℝ) : ℂ) • s)) atTop (𝓝 (Δ s)) := by
      have h1 : Tendsto (fun X => (((W X : ℝ) : ℂ)) • s) atTop (𝓝 (((1 : ℝ) : ℂ) • s)) :=
        ((Complex.continuous_ofReal.tendsto 1).comp hWlim).smul_const s
      rw [Complex.ofReal_one, one_smul] at h1
      exact (hΔ s).continuousAt.tendsto.comp h1
    have hlim3 : Tendsto (fun X => Δ (((W X : ℝ) : ℂ) • s)) atTop
        (𝓝 (Complex.exp (∫ x in Ioi (0 : ℝ), G x s))) := by
      simp_rw [hexp]
      exact ((Complex.continuous_exp.tendsto _).comp hlim1)
    exact tendsto_nhds_unique hlim2 hlim3
  · simp [hG, hQ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Analytic log-determinant of `1 - K(s)` past a closed polydisc.**  If the entries of `K` are
analytic, `K 0 = 0`, and `1 - K(s)` is invertible for `‖s p‖ ≤ ρ`, then there are `ρ' > ρ` and a
function `ell`, analytic on the polydisc `‖s p‖ < ρ'`, with `det (1 - K s) = exp (ell s)` there and
`ell 0 = 0`. -/
theorem exists_analytic_log_det_one_sub (K : (Pc → ℂ) → Matrix ι ι ℂ)
    (hK : ∀ x y s0, AnalyticAt ℂ (fun s => K s x y) s0) (h0 : K 0 = 0) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hunit : ∀ s : Pc → ℂ, ‖s‖ ≤ ρ → IsUnit (1 - K s)) :
    ∃ ρ' : ℝ, ρ < ρ' ∧ ∃ ell : (Pc → ℂ) → ℂ, AnalyticOnNhd ℂ ell (Metric.ball 0 ρ') ∧
      (∀ s ∈ Metric.ball (0 : Pc → ℂ) ρ', (1 - K s).det = Complex.exp (ell s)) ∧ ell 0 = 0 := by
  set Δ : (Pc → ℂ) → ℂ := fun s => (1 - K s).det with hΔdef
  have hΔ : ∀ z, AnalyticAt ℂ Δ z := fun z => by
    refine analyticAt_matrix_det fun x y => ?_
    simp only [Matrix.sub_apply]
    exact analyticAt_const.sub (hK x y z)
  have hΔ0 : Δ 0 = 1 := by simp [hΔdef, h0]
  have hopen : IsOpen {s : Pc → ℂ | Δ s ≠ 0} :=
    isOpen_ne_fun (continuous_iff_continuousAt.2 fun z => (hΔ z).continuousAt) continuous_const
  have hsub : Metric.closedBall (0 : Pc → ℂ) ρ ⊆ {s | Δ s ≠ 0} := by
    intro s hs
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hunit s (by simpa using hs))).ne_zero
  obtain ⟨ε, hε, hthick⟩ := (isCompact_closedBall (0 : Pc → ℂ) ρ).exists_thickening_subset_open
    hopen hsub
  rw [thickening_closedBall hε hρ] at hthick
  refine ⟨ρ + ε / 2, by linarith, ?_⟩
  obtain ⟨ell, h1, h2, h3⟩ := exists_analytic_log_of_ne_zero (R := ε + ρ) (R' := ρ + ε / 2) hΔ hΔ0
    (by linarith) fun s hs => hthick (mem_ball_zero_iff.2 hs)
  exact ⟨ell, h1, h2, h3⟩

end LogDet

section Instance

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **The localized log-determinant of the interpolated defect: existence.**  Under the hypotheses
of `taggedGfin_final` there are `ρ' > e^κ` and a function `ell` of the cut parameters, analytic on
the polydisc `‖s p‖ < ρ'` (which contains the closed polydisc `‖s p‖ ≤ e^κ`), with
`det (1 - K(s, t)) = exp (ell s)` there, `ell 0 = 0`, and
`exp (ell 1) = det (finalOp + t) · det (∑_z χ_z G_z)`. -/
theorem exists_analytic_log_det_taggedDefect (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    ∃ ρ' : ℝ, Real.exp κ < ρ' ∧ ∃ ell : (MacIdx d N₀ M → ℂ) → ℂ,
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ') ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s).det = Complex.exp (ell s)) ∧
      ell 0 = 0 ∧
      Complex.exp (ell (fun _ => 1)) = (shiftMat (finalOp d L N₀ k v a) t).det *
        (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det := by
  have hr0 : (0 : ℝ) ≤ 0 := le_rfl
  have hr : (0 : ℝ) ≤ pdEps d L / 8 := (div_nonneg (pdEps_pos hd).le (by norm_num))
  obtain ⟨ρ', hρ', ell, h1, h2, h3⟩ := exists_analytic_log_det_one_sub
    (fun s => taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t s)
    (fun x y s0 => taggedMat_analytic _ _ _ x y s0) (taggedK_zero hM hd t)
    (Real.exp_pos κ).le fun s hs =>
      (taggedDefect_isUnit_inv_weighted hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ le_rfl hr
        (s := s) (fun p => (norm_le_pi_norm s p).trans hs)).1
  have h1mem : (fun _ : MacIdx d N₀ M => (1 : ℂ)) ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ' := by
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt ?_ hρ'
    refine (pi_norm_le_iff_of_nonneg (Real.exp_pos κ).le).2 fun p => ?_
    simpa using Real.one_le_exp hκ
  refine ⟨ρ', hρ', ell, h1, h2, h3, ?_⟩
  rw [← h2 _ h1mem]
  exact det_one_sub_taggedK_one t

end Instance

end Balaban.Green
