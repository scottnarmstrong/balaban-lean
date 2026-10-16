/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalSecondOrder

/-!
# The cross term of the linear part with the source-independent exponent (W841)

Generic lemmas for leaf 3 of `notes/phase1/FINALAMP2.md`.

* `norm_odd_le_of_polydisc`: third-order Schwarz for the odd part.  If `G` is analytic on the
  polydisc of radius `T` around `0`, `‖G‖ ≤ B` there and `G'(0) = 0`, then
  `‖(G w - G (-w))/2‖ ≤ 2 B (R/T)^3` for `w` in the polydisc of radius `R < T`.
* `norm_setIntegral_box_mul_exp_le`: an odd function times `e^g`, `g = g_even + g_odd`,
  integrates over the symmetric box to `∫ f e^{g_even} (e^{g_odd} - 1)`, with the sup bound.
* `norm_log_ratio_sub_le`: the first-order bound for
  `log ∫ e^{G0 + J1 + J2} - log ∫ e^{G0}`.
-/

@[expose] public section

open Finset MeasureTheory Set Metric

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis

section Odd

/-- Reflection in the variable: derivative of `s ↦ f (-s)` at `0`. -/
theorem hasDerivAt_comp_neg_zero {f : ℂ → ℂ} {a : ℂ} (hf : HasDerivAt f a 0) :
    HasDerivAt (fun s => f (-s)) (-a) 0 := by
  have := HasDerivAt.comp_of_eq (0 : ℂ) (h₂ := f) (h := fun s : ℂ => -s) (by simpa using hf)
    (hasDerivAt_neg (0 : ℂ)) (by simp)
  convert this using 1 <;> first | rfl | simp

/-- Odd function of one variable, vanishing derivative at `0`: third-order bound. -/
theorem norm_odd_le_of_ball {h : ℂ → ℂ} {T B : ℝ} (hT : 0 < T)
    (hd : DifferentiableOn ℂ h (ball (0 : ℂ) T)) (hodd : ∀ t, h (-t) = - h t)
    (hB : ∀ t ∈ ball (0 : ℂ) T, ‖h t‖ ≤ B) (hd0 : deriv h 0 = 0) {t : ℂ} (ht : ‖t‖ < T) :
    ‖h t‖ ≤ 2 * B * (‖t‖ / T) ^ 3 := by
  have hball : ball (0 : ℂ) T ∈ nhds (0 : ℂ) := ball_mem_nhds _ hT
  have h0 : h 0 = 0 := by
    have := hodd 0
    simp only [neg_zero] at this
    linear_combination (1 / 2 : ℂ) * this
  set q : ℂ → ℂ := dslope h 0 with hq
  have hqd : DifferentiableOn ℂ q (ball (0 : ℂ) T) :=
    (Complex.differentiableOn_dslope hball).2 hd
  have hq0 : q 0 = 0 := by simp [hq, dslope_same, hd0]
  have hmaps : Set.MapsTo h (ball (0 : ℂ) T) (closedBall (h 0) B) := by
    intro τ hτ
    rw [mem_closedBall, h0, dist_zero_right]
    exact hB τ hτ
  have hqB : ∀ τ ∈ ball (0 : ℂ) T, ‖q τ‖ ≤ B / T := fun τ hτ =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps hτ
  have hqeven : ∀ τ, q (-τ) = q τ := by
    intro τ
    by_cases hτ : τ = 0
    · simp [hτ]
    · have hτ' : -τ ≠ 0 := neg_ne_zero.2 hτ
      simp only [hq, dslope_of_ne _ hτ, dslope_of_ne _ hτ', slope_def_field, sub_zero, hodd τ,
        h0]
      field_simp
  have hqd0 : deriv q 0 = 0 := by
    have hqa : DifferentiableAt ℂ q 0 := hqd.differentiableAt hball
    have h1 : HasDerivAt (fun τ => q (-τ)) (-(deriv q 0)) 0 := by
      exact hasDerivAt_comp_neg_zero hqa.hasDerivAt
    have h2 : (fun τ => q (-τ)) = q := funext hqeven
    rw [h2] at h1
    have h3 := hqa.hasDerivAt.unique h1
    linear_combination (1 / 2 : ℂ) * h3
  have key := norm_sub_linear_le_of_ball (h := q) hT hqd hq0
    (fun τ hτ => hqB τ hτ) ht
  rw [hqd0, mul_zero, sub_zero] at key
  have hht : h t = t * q t := by
    have := sub_smul_dslope h 0 t
    simpa [h0, smul_eq_mul] using this.symm
  have hqt : ‖q t‖ ≤ 2 * (B / T) * (‖t‖ / T) ^ 2 := key
  rw [hht, norm_mul]
  calc ‖t‖ * ‖q t‖ ≤ ‖t‖ * (2 * (B / T) * (‖t‖ / T) ^ 2) :=
        mul_le_mul_of_nonneg_left hqt (norm_nonneg _)
    _ = 2 * B * (‖t‖ / T) ^ 3 := by field_simp

variable {ι : Type*} [Fintype ι]

/-- **Third-order Schwarz for the odd part.**  `G` analytic on the polydisc of radius `T` around
`0` with `‖G‖ ≤ B` there and `G'(0) = 0`; then on the polydisc of radius `R`, `0 < R < T`,
the odd part satisfies `‖(G w - G (-w)) / 2‖ ≤ 2 B (R/T)^3`. -/
theorem norm_odd_le_of_polydisc {T R B : ℝ} (hR : 0 < R) (hRT : R < T)
    {G : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G (polydisc (0 : ι → ℂ) (fun _ => T)))
    (hB : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => T), ‖G w‖ ≤ B)
    (hG0 : fderiv ℂ G 0 = 0) {w : ι → ℂ} (hw : w ∈ polydisc (0 : ι → ℂ) (fun _ => R)) :
    ‖(G w - G (-w)) / 2‖ ≤ 2 * B * (R / T) ^ 3 := by
  have hT : 0 < T := hR.trans hRT
  set u : ι → ℂ := ((R : ℂ))⁻¹ • w with hu
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hu1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h := hw i
    simp only [hu, Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, Pi.zero_apply, sub_zero] at h ⊢
    rw [inv_mul_le_iff₀ hR]
    simpa using h.le
  have hmem : ∀ t : ℂ, ‖t‖ < T → t • u ∈ polydisc (0 : ι → ℂ) (fun _ => T) := by
    intro t ht i
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Pi.zero_apply, sub_zero]
    calc ‖t‖ * ‖u i‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (hu1 i) (norm_nonneg _)
      _ < T := by simpa using ht
  have hmem' : ∀ t : ℂ, ‖t‖ < T → G ∘ (fun t : ℂ => t • u) = G ∘ (fun t : ℂ => t • u) :=
    fun _ _ => rfl
  set g : ℂ → ℂ := fun t => G (t • u) with hg
  have hgd : ∀ t : ℂ, ‖t‖ < T → AnalyticAt ℂ g t := by
    intro t ht
    exact AnalyticAt.comp (g := G) (f := fun t : ℂ => t • u) (hG _ (hmem t ht))
      (analyticAt_id.smul analyticAt_const)
  have hGd0 : DifferentiableAt ℂ G 0 :=
    (hG 0 (fun i => by simpa using hT)).differentiableAt
  have hg0 : HasDerivAt g 0 0 := by
    have h1 : HasDerivAt (fun t : ℂ => t • u) u 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const u
    have h2 : HasFDerivAt G (fderiv ℂ G 0) ((0 : ℂ) • u) := by
      simpa using hGd0.hasFDerivAt
    have := h2.comp_hasDerivAt (0 : ℂ) h1
    simpa [hG0, hg, Function.comp_def] using this
  set h : ℂ → ℂ := fun t => (g t - g (-t)) / 2 with hh
  have hodd : ∀ t, h (-t) = - h t := by
    intro t; simp only [hh, neg_neg]; ring
  have hhd : DifferentiableOn ℂ h (ball (0 : ℂ) T) := by
    intro t ht
    have ht' : ‖t‖ < T := by simpa using ht
    have ht2 : ‖-t‖ < T := by simpa using ht'
    have a1 := hgd t ht'
    have a2 : AnalyticAt ℂ (fun s => g (-s)) t :=
      AnalyticAt.comp (g := g) (f := fun s : ℂ => -s) (hgd _ ht2) analyticAt_id.neg
    exact ((a1.sub a2).div_const).differentiableAt.differentiableWithinAt
  have hhB : ∀ t ∈ ball (0 : ℂ) T, ‖h t‖ ≤ B := by
    intro t ht
    have ht' : ‖t‖ < T := by simpa using ht
    have ht2 : ‖-t‖ < T := by simpa using ht'
    have b1 := hB _ (hmem t ht')
    have b2 := hB _ (hmem (-t) ht2)
    simp only [hh, hg]
    rw [norm_div]
    have : ‖G (t • u) - G ((-t) • u)‖ ≤ 2 * B := by
      calc _ ≤ ‖G (t • u)‖ + ‖G ((-t) • u)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add b1 b2
        _ = 2 * B := by ring
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hneg : (fun s => G (s • u)) (-t) = G ((-t) • u) := rfl
    rw [h2]
    have : ‖G (t • u) - G (-t • u)‖ ≤ 2 * B := this
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hhd0 : deriv h 0 = 0 := by
    have h1 : HasDerivAt (fun s => g (-s)) (-0) 0 := by
      simpa using hasDerivAt_comp_neg_zero hg0
    have h3 := (hg0.sub h1).div_const 2
    have : deriv h 0 = (0 - -0) / 2 := h3.deriv
    simpa using this
  have key := norm_odd_le_of_ball (h := h) hT hhd hodd hhB hhd0
    (t := (R : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]; exact hRT)
  have he : (R : ℂ) • u = w := by
    rw [hu, smul_smul, mul_inv_cancel₀ hRne, one_smul]
  have he2 : (-(R : ℂ)) • u = -w := by rw [neg_smul, he]
  simp only [hh, hg, he2, he] at key
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using key

end Odd

section Cancellation

variable {ι : Type*} [Fintype ι]

/-- The box integral of an odd function times `e^{g_even + g_odd}` equals the box integral of
`f e^{g_even} (e^{g_odd} - 1)`, for `γ` symmetric. -/
theorem setIntegral_box_odd_mul_exp_eq {γ : Measure (ι → ℝ)}
    (hsym : Measure.map Neg.neg γ = γ) {ρ : ℝ} (hγ : γ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {f ge go : (ι → ℝ) → ℂ} (hfc : Continuous f) (hgec : Continuous ge) (hgoc : Continuous go)
    (hf : ∀ ψ, f (-ψ) = - f ψ) (hge : ∀ ψ, ge (-ψ) = ge ψ) :
    ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, f ψ * Complex.exp (ge ψ + go ψ) ∂γ =
      ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ},
        f ψ * Complex.exp (ge ψ) * (Complex.exp (go ψ) - 1) ∂γ := by
  set S : Set (ι → ℝ) := {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} with hS
  have hSm : MeasurableSet S := (isCompact_box ρ).isClosed.measurableSet
  have hint : ∀ {u : (ι → ℝ) → ℂ}, Continuous u → IntegrableOn u S γ := fun hu =>
    hu.continuousOn.integrableOn_of_subset_isCompact (isCompact_box ρ) hSm subset_rfl hγ.ne
  have h1 : IntegrableOn (fun ψ => f ψ * Complex.exp (ge ψ) * (Complex.exp (go ψ) - 1)) S γ :=
    hint (by fun_prop)
  have h2 : IntegrableOn (fun ψ => f ψ * Complex.exp (ge ψ)) S γ := hint (by fun_prop)
  have h0 : ∫ ψ in S, f ψ * Complex.exp (ge ψ) ∂γ = 0 :=
    setIntegral_box_odd_eq_zero hsym (fun ψ => by simp [hf, hge])
  have : ∀ ψ, f ψ * Complex.exp (ge ψ + go ψ) =
      f ψ * Complex.exp (ge ψ) * (Complex.exp (go ψ) - 1) + f ψ * Complex.exp (ge ψ) := by
    intro ψ; rw [Complex.exp_add]; ring
  simp_rw [this]
  rw [integral_add h1 h2, h0, add_zero]

/-- **Odd cancellation with a weight.**  For `γ` symmetric, `f` odd, `g_even` even, `g_odd`
odd, with pointwise bounds on the box,
`‖∫_box f e^{g_even + g_odd} dγ‖ ≤ Cf Ce Co γ(box)`. -/
theorem norm_setIntegral_box_odd_mul_exp_le {γ : Measure (ι → ℝ)}
    (hsym : Measure.map Neg.neg γ = γ) {ρ : ℝ} (hγ : γ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {f ge go : (ι → ℝ) → ℂ} (hfc : Continuous f) (hgec : Continuous ge) (hgoc : Continuous go)
    (hf : ∀ ψ, f (-ψ) = - f ψ) (hge : ∀ ψ, ge (-ψ) = ge ψ) {Cf Ce Co : ℝ}
    (hCf : ∀ ψ ∈ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, ‖f ψ‖ ≤ Cf)
    (hCe : ∀ ψ ∈ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, ‖Complex.exp (ge ψ)‖ ≤ Ce)
    (hCo : ∀ ψ ∈ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, ‖Complex.exp (go ψ) - 1‖ ≤ Co) :
    ‖∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, f ψ * Complex.exp (ge ψ + go ψ) ∂γ‖ ≤
      Cf * Ce * Co * (γ {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal := by
  rw [setIntegral_box_odd_mul_exp_eq hsym hγ hfc hgec hgoc hf hge]
  refine (norm_setIntegral_le_of_norm_le_const hγ (C := Cf * Ce * Co) (fun ψ hψ => ?_)).trans
    ?_
  · rw [norm_mul, norm_mul]
    have a := hCf ψ hψ
    have b := hCe ψ hψ
    have c := hCo ψ hψ
    have a0 := (norm_nonneg _).trans a
    have b0 := (norm_nonneg _).trans b
    gcongr
  · rw [Measure.real]

end Cancellation

end Balaban.Green
