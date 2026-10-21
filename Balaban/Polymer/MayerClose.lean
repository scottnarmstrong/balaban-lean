/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.Mayer
public import Balaban.Polymer.PYClose

/-!
# Closeness of the Mayer activities

Two families of local terms `H, H₂` on the same product probability space, both bounded by
`H₀ e^{-(κ₀ + κ₁) d(t)}` (`H₀ ≤ log 2`), whose difference on the terms inside `Y` is at most `r` times
that bound (`0 ≤ r ≤ 1`), have Mayer activities `K(Y) = ∫ ∑_{C} ∏_{t ∈ C} (e^{H t} - 1)` with

`|K_H(Y) - K_{H₂}(Y)| ≤ 2 r · 2 q₂ c₁ e^{-(κ₁ - 3/2) d(Y)}`,  `q₂ = 2 (2 H₀) K₀ e^{κ₁ c}`

(`mayerK_sub_bound`): the bound of MY (iii) (`mayer_activity_bound`) at `2 H₀`, times `2 r`. The
products of `e^{H t} - 1` over a connected family are telescoped (`norm_prod_sub_prod_le_two`), with
`|e^x - e^y| ≤ 4 |x - y|` (`norm_exp_sub_exp_le`). Margin form (`mayerK_sub_bound_margin`): if the
difference of the terms is at most `H₀ e^{-(κ₀ + κ₁) d(t)} e^{-λ m(t)}` with `m ≥ 0` decreasing under
inclusion, then `r = e^{-λ m(Y)}`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

/-- `|e^x - e^y| ≤ 4 |x - y|` for `|y| ≤ log 2` and `|x - y| ≤ 1`. -/
theorem norm_exp_sub_exp_le {x y : ℂ} (hy : ‖y‖ ≤ Real.log 2) (hxy : ‖x - y‖ ≤ 1) :
    ‖Complex.exp x - Complex.exp y‖ ≤ 4 * ‖x - y‖ := by
  have e : Complex.exp x - Complex.exp y = Complex.exp y * (Complex.exp (x - y) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    ring
  rw [e, norm_mul]
  have h1 : ‖Complex.exp y‖ ≤ 2 := by
    refine (Complex.norm_exp_le_exp_norm y).trans ?_
    calc Real.exp ‖y‖ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hy
      _ = 2 := Real.exp_log (by norm_num)
  have h2 := Complex.norm_exp_sub_one_le hxy
  calc ‖Complex.exp y‖ * ‖Complex.exp (x - y) - 1‖ ≤ 2 * (2 * ‖x - y‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = 4 * ‖x - y‖ := by ring

section Close

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] {sup : T → Finset B} {H H₂ : T → (∀ b, Ω b) → ℂ}
  {d : Finset B → ℝ} {κ0 κ1 c H0 : ℝ}

omit [Fintype B] [∀ b, MeasurableSpace (Ω b)] in
/-- The pointwise closeness of the integrands of the Mayer activities. -/
theorem norm_mayerAct_sub_le (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0)
    (hκ1 : 0 ≤ κ1) (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hH₂ : ∀ t Φ, ‖H₂ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t))) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r ≤ 1) (Y : NePoly B)
    (hHH : ∀ t, sup t ⊆ Y.1 → ∀ Φ, ‖H t Φ - H₂ t Φ‖ ≤ r * (H0 * Real.exp (-(κ0 + κ1) * d (sup t))))
    (Φ : ∀ b, Ω b) :
    ‖mayerAct sup H Y Φ - mayerAct sup H₂ Y Φ‖ ≤
      2 * r * ∑ C ∈ Cfam sup (fun _ : Finset T => True) Y.1,
        ∏ t ∈ C, (mayerRho sup d κ0 (2 * H0) t * Real.exp (-κ1 * d (sup t))) := by
  unfold mayerAct polyAct
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun C hC => ?_)
  have hw : ∀ t, mayerRho sup d κ0 (2 * H0) t * Real.exp (-κ1 * d (sup t)) =
      2 * (mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t))) := fun t => by
    unfold mayerRho; ring
  simp_rw [hw]
  refine norm_prod_sub_prod_le_two C _ _ _ (by positivity)
    (fun t _ => norm_expm1_le_rho hH0 hH0' hκ0 hκ1 hd t Φ (hH t Φ))
    (fun t _ => norm_expm1_le_rho hH0 hH0' hκ0 hκ1 hd t Φ (hH₂ t Φ)) (fun t ht => ?_)
  have hsub := sub_of_mem_Cfam hC ht
  have hle : Real.exp (-(κ0 + κ1) * d (sup t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hd (sup t)])
  have hb := hHH t hsub Φ
  have hy : ‖H₂ t Φ‖ ≤ Real.log 2 := (hH₂ t Φ).trans (by nlinarith)
  have hxy : ‖H t Φ - H₂ t Φ‖ ≤ 1 := by
    refine hb.trans ?_
    have h2 : Real.log 2 ≤ 1 := (Real.log_two_lt_d9).le.trans (by norm_num)
    have : H0 * Real.exp (-(κ0 + κ1) * d (sup t)) ≤ H0 := by nlinarith
    nlinarith
  have he := norm_exp_sub_exp_le hy hxy
  have hρ : mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t)) =
      2 * (H0 * Real.exp (-(κ0 + κ1) * d (sup t))) := by
    unfold mayerRho
    rw [mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  show ‖(Complex.exp (H t Φ) - 1) - (Complex.exp (H₂ t Φ) - 1)‖ ≤
    2 * r * (mayerRho sup d κ0 H0 t * Real.exp (-κ1 * d (sup t)))
  rw [sub_sub_sub_cancel_right, hρ]
  nlinarith

/-- **Closeness of the Mayer activities.** With the hypotheses of `mayer_activity_bound` at `2 H₀`
(`q₂ c₁ ≤ 1/2`, `q₂ = 2 (2 H₀) K₀ e^{κ₁ c}`), two families of terms whose difference on the terms
inside `Y` is at most `r H₀ e^{-(κ₀ + κ₁) d(t)}` (`0 ≤ r ≤ 1`) have
`|K_H(Y) - K_{H₂}(Y)| ≤ 2 r · 2 q₂ c₁ e^{-(κ₁ - 3/2) d(Y)}`. -/
theorem mayerK_sub_bound (hmeas : ∀ t, Measurable (H t)) (hmeas₂ : ∀ t, Measurable (H₂ t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y) (hne : ∀ t, (sup t).Nonempty)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hH₂ : ∀ t Φ, ‖H₂ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t))) {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r ≤ 1) {K0 : ℝ} (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3 : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    {c1 : ℝ} (hc1 : 0 ≤ c1) (hq : 2 * (2 * H0) * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (Y : NePoly B) (hG1 : (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hHH : ∀ t, sup t ⊆ Y.1 → ∀ Φ, ‖H t Φ - H₂ t Φ‖ ≤ r * (H0 * Real.exp (-(κ0 + κ1) * d (sup t)))) :
    ‖mayerK μ sup H Y - mayerK μ sup H₂ Y‖ ≤
      2 * r * (2 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1 *
        Real.exp (-(κ1 - 3 / 2) * d Y.1)) := by
  obtain ⟨b0, hb0⟩ := Y.2
  have hK0 : 0 ≤ K0 := le_trans (Finset.sum_nonneg (fun t _ => (Real.exp_pos _).le)) (hG2 b0)
  set q := 2 * (2 * H0) * K0 * Real.exp (κ1 * c) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hH0₂ : 0 ≤ 2 * H0 := by positivity
  set M := Real.exp (-κ1 * d Y.1) * Real.exp (-κ1 * c) * (Real.exp (q * Y.1.card) - 1) with hM
  have hpt : ∀ Φ, ‖mayerAct sup H Y Φ - mayerAct sup H₂ Y Φ‖ ≤ 2 * r * M := fun Φ =>
    (norm_mayerAct_sub_le hH0 hH0' hκ0 hκ1 hd hH hH₂ hr hr1 Y hHH Φ).trans
      (mul_le_mul_of_nonneg_left (sum_cfam_rho_le hH0₂ hκ1 hne hG2 hG3 Y) (by positivity))
  have hint : ∀ H' : T → (∀ b, Ω b) → ℂ, (∀ t, Measurable (H' t)) →
      (∀ t Φ, ‖H' t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t))) →
      Integrable (mayerAct sup H' Y) (Measure.pi μ) := fun H' hm hb =>
    Integrable.of_bound (measurable_mayerAct hm Y).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun Φ => norm_mayerAct_le (d := d) (κ0 := κ0) (κ1 := κ1) hH0
        hH0' hκ0 hκ1 hd hb Y Φ)
  unfold mayerK
  rw [← integral_sub (hint H hmeas hH) (hint H₂ hmeas₂ hH₂)]
  have hb := norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
    (f := fun Φ => mayerAct sup H Y Φ - mayerAct sup H₂ Y Φ) (Filter.Eventually.of_forall hpt)
  have hreal : (Measure.pi μ).real Set.univ = 1 := by simp
  rw [hreal, mul_one] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact mayer_real_bound (q := q) (c1 := c1) (κ1 := κ1) (c := c) (D := d Y.1)
    (n := (Y.1.card : ℝ)) hq0 hc1 hκ1 hc (hd _) (Nat.cast_nonneg _) hq hG1

/-- **Closeness of the Mayer activities, margin form.** If the difference of the terms is at most
`H₀ e^{-(κ₀ + κ₁) d(t)} e^{-λ m(sup t)}` with `m ≥ 0` decreasing under inclusion and `λ ≥ 0`, then
`|K_H(Y) - K_{H₂}(Y)| ≤ 2 e^{-λ m(Y)} · 2 q₂ c₁ e^{-(κ₁ - 3/2) d(Y)}`. -/
theorem mayerK_sub_bound_margin (hmeas : ∀ t, Measurable (H t))
    (hmeas₂ : ∀ t, Measurable (H₂ t)) (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0)
    (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c) (hd : ∀ Y, 0 ≤ d Y) (hne : ∀ t, (sup t).Nonempty)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (hH₂ : ∀ t Φ, ‖H₂ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d (sup t)))
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam) {K0 : ℝ} (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ sup t),
      Real.exp (-κ0 * d (sup t)) ≤ K0)
    (hG3 : ∀ C : Finset T, ConnSet sup C →
      d (unionCs sup C) ≤ ∑ t ∈ C, d (sup t) + c * ((C.card : ℝ) - 1))
    {c1 : ℝ} (hc1 : 0 ≤ c1) (hq : 2 * (2 * H0) * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (Y : NePoly B) (hG1 : (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hHH : ∀ t, sup t ⊆ Y.1 → ∀ Φ, ‖H t Φ - H₂ t Φ‖ ≤
      H0 * Real.exp (-(κ0 + κ1) * d (sup t)) * Real.exp (-lam * m (sup t))) :
    ‖mayerK μ sup H Y - mayerK μ sup H₂ Y‖ ≤
      2 * Real.exp (-lam * m Y.1) * (2 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1 *
        Real.exp (-(κ1 - 3 / 2) * d Y.1)) := by
  refine mayerK_sub_bound μ hmeas hmeas₂ hH0 hH0' hκ0 hκ1 hc hd hne hH hH₂ (Real.exp_pos _).le
    (Real.exp_le_one_iff.2 (by nlinarith [hm Y.1])) hG2 hG3 hc1 hq Y hG1 fun t ht Φ => ?_
  refine (hHH t ht Φ).trans ?_
  rw [mul_comm (Real.exp (-lam * m Y.1))]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have := hmono _ _ ht
  nlinarith

end Close

end Balaban.Polymer
