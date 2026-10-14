/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RootBoundsArith
public import Balaban.Green.FinalInteractionCutoff
public import Balaban.Green.FinalDetRatio

/-!
# From the coefficient bounds of the last integral to Root-F's term bound (W792)

Arithmetic of the last step, with the geometric and analytic inputs as hypotheses.

* `card_le_card_mul_of_subset_biUnion`: a polymer covered by `|C|` macro cells of at most `V`
  sites each has at most `|C| V` sites.
* `coefDecay_site`: the cell decay `A e^{-(κ-1)|C|}` of the cutoff interaction coefficients
  becomes the root decay `exp(-κ' |X| / (M L^j)^d)`, `κ' = (κ-1)/cov`.
* `detRatioCoef_decay`: the same for the determinant-ratio coefficients
  `2 |C| D/(e^κ-1)^{|C|}`, for `e^κ > 3`, with rate `log((e^κ-1)/2)`.
* `finalTerm_bound`: the activity of a polymer, bounded on the source ball by
  `K A e^{-(κ-1)n}` with `A` the interaction amplitude, `A ≤ C₀ β_{k_f}^{-2}`, gives for the first
  order term `∫₀¹ ∂_{g_b(x)} F(t g) dt`, `l1 g ≤ 1/2`, Root-F's bound
  `c₉ L^{-(k_f+1)((d-2)/2+δ)} exp(-κ' |X| / (M L^{k_f+1})^d)`
  once `L^{(d-2)/2+δ} K C₀ / r ≤ c₉ β₀²`.
-/

@[expose] public section

namespace Balaban.Green

open Balaban.Correlations Balaban.Inhabited.RootBoundsArith

/-- A set covered by `|C|` pieces of at most `V` elements has at most `|C| V` elements. -/
theorem card_le_card_mul_of_subset_biUnion {ι α : Type*} [DecidableEq α] (C : Finset ι)
    (S : ι → Finset α) (X : Finset α) (hX : X ⊆ C.biUnion S) {V : ℕ}
    (hS : ∀ p ∈ C, (S p).card ≤ V) : X.card ≤ C.card * V :=
  (Finset.card_le_card hX).trans (Finset.card_biUnion_le.trans
    ((Finset.sum_le_sum hS).trans (by simp)))

/-- **Polymer-to-site conversion.**  If `|X| ≤ n · cov · a` (`a = (M L^j)^d`, `cov > 0`), then
`A e^{-κ₁ n} ≤ A exp(-(κ₁/cov) |X| / a)`. -/
theorem coefDecay_site {A κ₁ cov a x : ℝ} {n : ℕ} (hA : 0 ≤ A) (hκ : 0 ≤ κ₁) (hcov : 0 < cov)
    (ha : 0 < a) (hx : x ≤ n * (cov * a)) :
    A * Real.exp (-κ₁ * n) ≤ A * Real.exp (-(κ₁ / cov) * x / a) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA
  have h1 : (κ₁ / cov) * x / a ≤ κ₁ * n := by
    rw [div_le_iff₀ ha, div_mul_eq_mul_div, div_le_iff₀ hcov]
    nlinarith [mul_le_mul_of_nonneg_left hx hκ]
  have : -(κ₁ / cov) * x / a = -((κ₁ / cov) * x / a) := by ring
  rw [this]; linarith

/-- `n ≤ 2^n`, so `n / r^n ≤ (2/r)^n`. -/
theorem nat_div_pow_le {r : ℝ} (hr : 0 < r) (n : ℕ) : (n : ℝ) / r ^ n ≤ (2 / r) ^ n := by
  rw [div_pow]
  exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le)
    (pow_pos hr n).le

/-- **The determinant-ratio coefficients.**  For `e^κ > 3`, `‖c‖ ≤ 2 n D / (e^κ-1)^n` gives
`‖c‖ ≤ 2 D exp(-log((e^κ-1)/2) n)`. -/
theorem detRatioCoef_decay {κ D c : ℝ} {n : ℕ} (hκ : 3 < Real.exp κ) (hD : 0 ≤ D)
    (hc : ‖c‖ ≤ 2 * n * D / (Real.exp κ - 1) ^ n) :
    ‖c‖ ≤ 2 * D * Real.exp (-Real.log ((Real.exp κ - 1) / 2) * n) := by
  have hr : 0 < Real.exp κ - 1 := by linarith
  refine hc.trans ?_
  have h := nat_div_pow_le hr n
  have e : Real.exp (-Real.log ((Real.exp κ - 1) / 2) * n) = (2 / (Real.exp κ - 1)) ^ n := by
    have hp : 0 < (Real.exp κ - 1) / 2 := by linarith
    rw [show -Real.log ((Real.exp κ - 1) / 2) * n = n * (-Real.log ((Real.exp κ - 1) / 2)) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log hp]
    congr 1
    field_simp
  rw [e]
  calc 2 * (n : ℝ) * D / (Real.exp κ - 1) ^ n = 2 * D * ((n : ℝ) / (Real.exp κ - 1) ^ n) := by ring
    _ ≤ 2 * D * (2 / (Real.exp κ - 1)) ^ n := by gcongr

/-- **Root-F's bound for the first-order final-scale term.**  Let `F` be analytic on the source
ball with `‖F g‖ ≤ K A e^{-κ₁ n}` there (`K` the number of macro families of the polymer, `A` the
interaction amplitude, `n` the number of macro cells), let the polymer have at most
`n · cov · a` sites (`a = (M L^{k_f+1})^d`), and let `A ≤ C₀ β_{k_f}^{-2}`.  Then for
`l1 g ≤ 1/2` and a Cauchy radius `0 < r ≤ 1/2`,
`‖∫₀¹ ∂_{g_b(x)} F(t g) dt‖ ≤ c₉ L^{-(k_f+1)((d-2)/2+δ)} exp(-(κ₁/cov) |X| / a)`,
provided `L^{(d-2)/2+δ} ≤ (c₉ r/(K C₀)) β₀²`. -/
theorem finalTerm_bound {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {d L kf : ℕ} {β0 c₉ δ A K C₀ κ₁ cov a x r : ℝ} {n : ℕ}
    (hd : 3 ≤ d) (hL : 2 ≤ L) (hc : 0 < c₉) (hβ0 : 0 < β0) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ ((d : ℝ) - 2) / 2) (hK : 0 < K) (hC₀ : 0 < C₀) (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hκ : 0 ≤ κ₁) (hcov : 0 < cov) (ha : 0 < a) (hx : x ≤ n * (cov * a))
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ (c₉ * r / (K * C₀)) * β0 ^ 2)
    (hA : A ≤ C₀ * ((Balaban.LargeField.ActionConv.betaK d L kf β0) ^ 2)⁻¹)
    {F : (α → β → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (ball1 α β))
    (hFB : ∀ g ∈ ball1 α β, ‖F g‖ ≤ K * A * Real.exp (-κ₁ * n))
    {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (u : α) (b : β) :
    ‖kf0Deriv F g u b‖ ≤ c₉ * (L : ℝ) ^ (-(((kf + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
      Real.exp (-(κ₁ / cov) * x / a) := by
  have h1 := norm_kf0Deriv_le_radius hF hr hr2 hFB hg u b
  have hKC : 0 < K * C₀ := mul_pos hK hC₀
  have hc' : 0 < c₉ * r / (K * C₀) := by positivity
  have h2 := betaK_inv_sq_le (k := kf) (c₉ := c₉ * r / (K * C₀)) (δ := δ) hd hL hc' hβ0 hδ0 hδ hβ
  have h4 := coefDecay_site (A := 1) (n := n) zero_le_one hκ hcov ha hx
  rw [one_mul, one_mul] at h4
  set P : ℝ := (L : ℝ) ^ (-(((kf + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
  have hE : 0 ≤ Real.exp (-κ₁ * n) := (Real.exp_pos _).le
  have hAn : A ≤ C₀ * (c₉ * r / (K * C₀) * P) := hA.trans (by gcongr)
  calc ‖kf0Deriv F g u b‖ ≤ (K * A * Real.exp (-κ₁ * n)) / r := h1
    _ ≤ (K * (C₀ * (c₉ * r / (K * C₀) * P)) * Real.exp (-κ₁ * n)) / r := by gcongr
    _ = c₉ * P * Real.exp (-κ₁ * n) := by field_simp
    _ ≤ c₉ * P * Real.exp (-(κ₁ / cov) * x / a) := by
        have hP : 0 ≤ c₉ * P := mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_left h4 hP

end Balaban.Green
