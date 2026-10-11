/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-power arithmetic for the Hölder bound (Proposition 4.9)

Elementary inequalities with real exponents `θ ∈ (0, 1)` used to assemble the Hölder estimate for
the gradient: absorbing `r ≤ r^{1-θ} ℓ^θ` for `r ≤ ℓ`, and the comparison of the source and
potential contributions with `ℓ^θ r^{1-θ}`.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

theorem le_rpow_mul_of_le {r ℓ θ : ℝ} (hr : 0 < r) (hrℓ : r ≤ ℓ) (hθ : 0 < θ) :
    r ≤ r ^ (1 - θ) * ℓ ^ θ := by
  have h1 : r = r ^ (1 - θ) * r ^ θ := by
    rw [← Real.rpow_add hr]; simp
  have h2 : r ^ θ ≤ ℓ ^ θ := Real.rpow_le_rpow hr.le hrℓ hθ.le
  calc r = r ^ (1 - θ) * r ^ θ := h1
    _ ≤ r ^ (1 - θ) * ℓ ^ θ := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem mul_rpow_le_of_one_le {c ℓ θ : ℝ} (hc : 1 ≤ c) (hℓ : 0 ≤ ℓ) (hθ1 : θ ≤ 1) :
    (c * ℓ) ^ θ ≤ c * ℓ ^ θ := by
  rw [Real.mul_rpow (by linarith) hℓ]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc c ^ θ ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hθ1
    _ = c := Real.rpow_one c

theorem rpow_le_self_of_one_le {ℓ θ : ℝ} (hℓ : 1 ≤ ℓ) (hθ1 : θ ≤ 1) : ℓ ^ θ ≤ ℓ := by
  calc ℓ ^ θ ≤ ℓ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hℓ hθ1
    _ = ℓ := Real.rpow_one ℓ

/-- `ℓ² = ℓ^θ ℓ^{2-θ}`. -/
theorem sq_eq_rpow_mul {ℓ θ : ℝ} (hℓ : 0 < ℓ) : ℓ ^ 2 = ℓ ^ θ * ℓ ^ (2 - θ) := by
  rw [← Real.rpow_add hℓ]
  rw [show θ + (2 - θ) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- The source-term comparison: for `r ≤ ℓ ≤ Λ`, `R + 1 ≤ 2 Λ'` with `Λ' ≤ Λ`,
`ℓ² (r + r^{1-θ} (R+1)^θ) ≤ 3 Λ² ℓ^θ r^{1-θ}`. -/
theorem holder_source_arith {r ℓ Λ Λ' R θ : ℝ} (hr : 0 < r) (hrℓ : r ≤ ℓ) (hℓΛ : ℓ ≤ Λ)
    (hΛ' : Λ' ≤ Λ) (hΛ'0 : 0 ≤ Λ') (hR : R + 1 ≤ 2 * Λ') (hR0 : 0 ≤ R) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) :
    ℓ ^ 2 * (r + r ^ (1 - θ) * (R + 1) ^ θ) ≤ 3 * Λ ^ 2 * (ℓ ^ θ * r ^ (1 - θ)) := by
  have hℓ0 : 0 < ℓ := hr.trans_le hrℓ
  have hΛ0 : 0 < Λ := hℓ0.trans_le hℓΛ
  have h1 := le_rpow_mul_of_le hr hrℓ hθ0
  have hrpow0 : 0 < r ^ (1 - θ) := by positivity
  have hX : 0 < ℓ ^ θ * r ^ (1 - θ) := by positivity
  have h2 : ℓ ^ 2 * r ≤ Λ ^ 2 * (ℓ ^ θ * r ^ (1 - θ)) := by
    calc ℓ ^ 2 * r ≤ Λ ^ 2 * (r ^ (1 - θ) * ℓ ^ θ) := by
          apply mul_le_mul (pow_le_pow_left₀ hℓ0.le hℓΛ 2) h1 hr.le (by positivity)
      _ = _ := by ring
  have h3 : ℓ ^ 2 * (r ^ (1 - θ) * (R + 1) ^ θ) ≤ 2 * Λ ^ 2 * (ℓ ^ θ * r ^ (1 - θ)) := by
    have e1 : (R + 1) ^ θ ≤ 2 * Λ ^ θ := by
      calc (R + 1) ^ θ ≤ (2 * Λ') ^ θ := Real.rpow_le_rpow (by linarith) hR hθ0.le
        _ ≤ 2 * Λ' ^ θ := mul_rpow_le_of_one_le (by norm_num) hΛ'0 hθ1
        _ ≤ 2 * Λ ^ θ := by
            have := Real.rpow_le_rpow hΛ'0 hΛ' hθ0.le
            linarith
    have e2 : ℓ ^ (2 - θ) ≤ Λ ^ (2 - θ) := Real.rpow_le_rpow hℓ0.le hℓΛ (by linarith)
    have e3 : Λ ^ (2 - θ) * Λ ^ θ = Λ ^ 2 := by
      rw [← Real.rpow_add hΛ0]
      rw [show 2 - θ + θ = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [sq_eq_rpow_mul (θ := θ) hℓ0]
    have e4 : ℓ ^ (2 - θ) * (R + 1) ^ θ ≤ Λ ^ (2 - θ) * (2 * Λ ^ θ) :=
      mul_le_mul e2 e1 (by positivity) (by positivity)
    calc ℓ ^ θ * ℓ ^ (2 - θ) * (r ^ (1 - θ) * (R + 1) ^ θ)
        = (ℓ ^ θ * r ^ (1 - θ)) * (ℓ ^ (2 - θ) * (R + 1) ^ θ) := by ring
      _ ≤ (ℓ ^ θ * r ^ (1 - θ)) * (Λ ^ (2 - θ) * (2 * Λ ^ θ)) :=
          mul_le_mul_of_nonneg_left e4 hX.le
      _ = 2 * (Λ ^ (2 - θ) * Λ ^ θ) * (ℓ ^ θ * r ^ (1 - θ)) := by ring
      _ = _ := by rw [e3]
  calc ℓ ^ 2 * (r + r ^ (1 - θ) * (R + 1) ^ θ) = ℓ ^ 2 * r + ℓ ^ 2 * (r ^ (1 - θ) * (R + 1) ^ θ) := by
        ring
    _ ≤ _ := by linarith

theorem rpow_neg_two_sub_half {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ρ ^ (-2 - (d : ℝ) / 2) = (ρ ^ 2)⁻¹ * ρ ^ (-(d : ℝ) / 2) := by
  have e : (-2 - (d : ℝ) / 2) = -((2 : ℕ) : ℝ) + (-(d : ℝ) / 2) := by push_cast; ring
  rw [e, Real.rpow_add hρ, Real.rpow_neg hρ.le, Real.rpow_natCast]

/-- The `L²` term of the Hölder bound. -/
theorem holder_term_a {Cc κ ℓ ρ r Tv Y X : ℝ} (hCc : 0 ≤ Cc) (hκ : ℓ = κ * ρ) (hρ0 : 0 < ρ)
    (hr0 : 0 ≤ r) (hTv : Tv ≤ Y) (hrX : r ≤ X) (hY : 0 ≤ Y) :
    ℓ ^ 2 * (Cc * r * (ρ ^ 2)⁻¹ * Tv) ≤ Cc * κ ^ 2 * (X * Y) := by
  have h1 : ℓ ^ 2 * (ρ ^ 2)⁻¹ = κ ^ 2 := by rw [hκ]; field_simp
  have hC : 0 ≤ Cc * κ ^ 2 := by positivity
  calc ℓ ^ 2 * (Cc * r * (ρ ^ 2)⁻¹ * Tv) = Cc * κ ^ 2 * (r * Tv) := by rw [← h1]; ring
    _ ≤ Cc * κ ^ 2 * (X * Y) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have hTv0 : Tv ≤ Y := hTv
        by_cases hT0 : 0 ≤ Tv
        · exact mul_le_mul hrX hTv0 hT0 (hr0.trans hrX)
        · push Not at hT0
          have : r * Tv ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hT0.le
          have : 0 ≤ X * Y := mul_nonneg (hr0.trans hrX) hY
          linarith

/-- The source term of the Hölder bound. -/
theorem holder_term_b {Mf cH θ r ℓ L Λ' Rf X e E1 SA : ℝ} (hMf0 : 0 ≤ Mf) (hcH : 0 ≤ cH)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hr0 : 0 < r) (hrℓ : r ≤ ℓ) (hℓΛ : ℓ ≤ L * Λ') (hL1 : 1 ≤ L)
    (hΛ'1 : 1 ≤ Λ') (hRf : Rf + 1 ≤ 2 * Λ') (hRf0 : 0 ≤ Rf) (hE : 1 ≤ E1 * e)
    (hXdef : X = ℓ ^ θ * r ^ (1 - θ))
    (hSA : SA ≤ cH / θ * (r + r ^ (1 - θ) * (Rf + 1) ^ θ)) :
    ℓ ^ 2 * (Mf * SA) ≤ (3 * L ^ 2 * cH * E1 / θ) * (X * (e * (Λ' ^ 2 * Mf))) := by
  have hℓ0 : 0 < ℓ := hr0.trans_le hrℓ
  have harith := holder_source_arith (θ := θ) (R := Rf) (Λ := L * Λ') (Λ' := Λ') hr0 hrℓ hℓΛ
    (by nlinarith) (by linarith) hRf hRf0 hθ0 hθ1
  have hX0 : 0 < X := by rw [hXdef]; positivity
  have hcθ : 0 ≤ cH / θ := by positivity
  have hF0 : 0 ≤ Λ' ^ 2 * Mf := by positivity
  calc ℓ ^ 2 * (Mf * SA) ≤ ℓ ^ 2 * (Mf * (cH / θ * (r + r ^ (1 - θ) * (Rf + 1) ^ θ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSA hMf0) (by positivity)
    _ = (Mf * (cH / θ)) * (ℓ ^ 2 * (r + r ^ (1 - θ) * (Rf + 1) ^ θ)) := by ring
    _ ≤ (Mf * (cH / θ)) * (3 * (L * Λ') ^ 2 * (ℓ ^ θ * r ^ (1 - θ))) :=
        mul_le_mul_of_nonneg_left harith (by positivity)
    _ = (3 * L ^ 2 * cH / θ) * (X * (Λ' ^ 2 * Mf)) := by rw [hXdef]; ring
    _ ≤ (3 * L ^ 2 * cH / θ) * (X * (E1 * e * (Λ' ^ 2 * Mf))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hX0.le
        nlinarith [mul_le_mul_of_nonneg_right hE hF0]
    _ = _ := by ring

/-- The potential term of the Hölder bound. -/
theorem holder_term_c {ℓ ρ r L Lj M m cH θ Sb X : ℝ} (hcH : 0 ≤ cH) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hr0 : 0 < r) (hrℓ : r ≤ ℓ) (hρ1 : 1 ≤ ρ) (hρℓ : ρ ≤ ℓ) (hL0 : 0 < L) (hLj : 0 < Lj)
    (hℓ : ℓ = L * Lj) (hM0 : 0 ≤ M) (hm : m = 4 * (Lj ^ 2)⁻¹ * M)
    (hXdef : X = ℓ ^ θ * r ^ (1 - θ))
    (hSb : Sb ≤ cH / θ * (r + r ^ (1 - θ) * (2 * ρ + 1) ^ θ)) :
    ℓ ^ 2 * (m * Sb) ≤ (16 * L ^ 2 * cH / θ) * X * M := by
  have hℓ0 : 0 < ℓ := hr0.trans_le hrℓ
  have hρ0 : 0 < ρ := by linarith
  have hX0 : 0 < X := by rw [hXdef]; positivity
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have h1 : ℓ ^ 2 * m = 4 * L ^ 2 * M := by rw [hm, hℓ]; field_simp
  have h2 : r + r ^ (1 - θ) * (2 * ρ + 1) ^ θ ≤ 4 * X := by
    have e1 := le_rpow_mul_of_le hr0 hrℓ hθ0
    have e2 : (2 * ρ + 1) ^ θ ≤ 3 * ℓ ^ θ := by
      calc (2 * ρ + 1) ^ θ ≤ (3 * ρ) ^ θ :=
            Real.rpow_le_rpow (by positivity) (by linarith) hθ0.le
        _ ≤ 3 * ρ ^ θ := mul_rpow_le_of_one_le (by norm_num) hρ0.le hθ1
        _ ≤ 3 * ℓ ^ θ := by
            have := Real.rpow_le_rpow hρ0.le hρℓ hθ0.le
            linarith
    have e3 : r ^ (1 - θ) * (2 * ρ + 1) ^ θ ≤ 3 * X := by
      calc r ^ (1 - θ) * (2 * ρ + 1) ^ θ ≤ r ^ (1 - θ) * (3 * ℓ ^ θ) :=
            mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = 3 * X := by rw [hXdef]; ring
    have e4 : r ≤ X := by rw [hXdef]; linarith
    linarith
  have hcθ : 0 ≤ cH / θ := by positivity
  calc ℓ ^ 2 * (m * Sb) ≤ ℓ ^ 2 * (m * (cH / θ * (4 * X))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hm0
        exact hSb.trans (mul_le_mul_of_nonneg_left h2 hcθ)
    _ = (ℓ ^ 2 * m) * (cH / θ * (4 * X)) := by ring
    _ = _ := by rw [h1]; ring

/-- Assembly of the three terms of the Hölder bound. -/
theorem holder_assemble {Dn Cc cH θ r ρ ℓ κ Tv SA Sb Kl2 e F E1 L Lj Lj' Mf M m Rf : ℝ}
    (hCc : 0 ≤ Cc) (hcH : 0 ≤ cH) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hr0 : 0 < r) (hrρ : r ≤ ρ)
    (hρℓ : ρ ≤ ℓ) (hρ1 : 1 ≤ ρ) (hκ : ℓ = κ * ρ) (hℓ : ℓ = L * Lj) (hL0 : 0 < L) (hL1 : 1 ≤ L)
    (hLj : 0 < Lj) (hLj'1 : 1 ≤ Lj') (hMf0 : 0 ≤ Mf) (hM0 : 0 ≤ M) (hm : m = 4 * (Lj ^ 2)⁻¹ * M)
    (he0 : 0 < e) (hF : F = Lj' ^ 2 * Mf) (hKl2 : 0 ≤ Kl2) (hE1 : 0 ≤ E1)
    (hmain : Dn ≤ Cc * r * (ρ ^ 2)⁻¹ * Tv + (Mf * SA + m * Sb))
    (hTv : Tv ≤ Kl2 * e * F)
    (hSA : SA ≤ cH / θ * (r + r ^ (1 - θ) * (Rf + 1) ^ θ)) (hRf : Rf + 1 ≤ 2 * Lj')
    (hRf0 : 0 ≤ Rf)
    (hSb : Sb ≤ cH / θ * (r + r ^ (1 - θ) * (2 * ρ + 1) ^ θ))
    (hsrc : SA = 0 ∨ (ℓ ≤ L * Lj' ∧ 1 ≤ E1 * e)) :
    ℓ ^ 2 * Dn ≤ ((Cc * κ ^ 2 * Kl2 + 3 * L ^ 2 * cH * E1) / θ) * (ℓ ^ θ * r ^ (1 - θ)) * (e * F) +
      (16 * L ^ 2 * cH / θ) * (ℓ ^ θ * r ^ (1 - θ)) * M := by
  have hrℓ : r ≤ ℓ := hrρ.trans hρℓ
  have hℓ0 : 0 < ℓ := hr0.trans_le hrℓ
  have hρ0 : 0 < ρ := by linarith
  have hXdef : ℓ ^ θ * r ^ (1 - θ) = ℓ ^ θ * r ^ (1 - θ) := rfl
  have hX0 : 0 < ℓ ^ θ * r ^ (1 - θ) := by positivity
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  have hrX : r ≤ ℓ ^ θ * r ^ (1 - θ) := by
    have := le_rpow_mul_of_le hr0 hrℓ hθ0
    linarith
  have ha := holder_term_a (Y := Kl2 * e * F) (X := ℓ ^ θ * r ^ (1 - θ)) hCc hκ hρ0 hr0.le hTv hrX
    (by positivity)
  have hb : ℓ ^ 2 * (Mf * SA) ≤ (3 * L ^ 2 * cH * E1 / θ) * ((ℓ ^ θ * r ^ (1 - θ)) * (e * F)) := by
    rcases hsrc with h0 | ⟨hℓΛ, hexpo⟩
    · rw [h0]; simp only [mul_zero]; positivity
    · rw [hF]
      exact holder_term_b (X := ℓ ^ θ * r ^ (1 - θ)) (e := e) (E1 := E1) (SA := SA) hMf0 hcH hθ0 hθ1
        hr0 hrℓ hℓΛ hL1 hLj'1 hRf hRf0 hexpo rfl hSA
  have hc := holder_term_c (X := ℓ ^ θ * r ^ (1 - θ)) (Sb := Sb) (m := m) hcH hθ0 hθ1 hr0 hrℓ hρ1 hρℓ
    hL0 hLj hℓ hM0 hm rfl hSb
  have hℓ2 : 0 ≤ ℓ ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hmain hℓ2
  rw [mul_add, mul_add] at h1
  have hY : 0 ≤ (ℓ ^ θ * r ^ (1 - θ)) * (e * F) := by positivity
  have hCK : 0 ≤ Cc * κ ^ 2 * Kl2 := by
    have : 0 ≤ κ ^ 2 := sq_nonneg _
    positivity
  have h5 : Cc * κ ^ 2 * ((ℓ ^ θ * r ^ (1 - θ)) * (Kl2 * e * F)) ≤
      (Cc * κ ^ 2 * Kl2 / θ) * ((ℓ ^ θ * r ^ (1 - θ)) * (e * F)) := by
    have e7 : Cc * κ ^ 2 * ((ℓ ^ θ * r ^ (1 - θ)) * (Kl2 * e * F)) =
        (Cc * κ ^ 2 * Kl2) * ((ℓ ^ θ * r ^ (1 - θ)) * (e * F)) := by ring
    rw [e7]
    apply mul_le_mul_of_nonneg_right _ hY
    rw [le_div_iff₀ hθ0]
    nlinarith
  have e6 : (Cc * κ ^ 2 * Kl2 + 3 * L ^ 2 * cH * E1) / θ * (ℓ ^ θ * r ^ (1 - θ)) * (e * F) =
      (Cc * κ ^ 2 * Kl2 / θ) * ((ℓ ^ θ * r ^ (1 - θ)) * (e * F)) +
        (3 * L ^ 2 * cH * E1 / θ) * ((ℓ ^ θ * r ^ (1 - θ)) * (e * F)) := by ring
  rw [e6]
  linarith

end Balaban.Multiscale
