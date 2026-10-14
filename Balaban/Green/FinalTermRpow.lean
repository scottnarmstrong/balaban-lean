/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTermBound
public import Balaban.Green.FinalAmplitude

/-!
# The normalization at `g = 0` of the last-step term (W808)

The first-order term `kf0Deriv F g u b` does not see the constant `F 0`
(`kf0Deriv_sub_const`), so Root-F's bound needs the amplitude only for `F g - F 0`
(`finalTerm_bound_of_sub`).  If `F g - F 0` is bounded by `B` on the larger ball
`{l1 g < T}`, `T ≥ 1`, the Schwarz lemma gives `‖F g - F 0‖ ≤ B / T` on the unit ball
(`norm_sub_zero_le_of_ball`, `finalTerm_bound_of_sub_ball`).
-/

@[expose] public section

namespace Balaban.Green

open Balaban.Correlations Balaban.Inhabited.RootBoundsArith

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [Fintype α] [Fintype β] in
/-- `kf0Deriv` does not see an additive constant. -/
theorem kf0Deriv_sub_const (F : (α → β → ℂ) → ℂ) (c : ℂ) (g : α → β → ℂ) (a : α) (b : β) :
    kf0Deriv (fun h => F h - c) g a b = kf0Deriv F g a b := by
  unfold kf0Deriv
  congr 1
  funext t
  exact deriv_sub_const (f := fun s : ℂ => F ((t : ℂ) • g + s • unitSource a b)) c

/-- **Root-F's bound for the first-order term, amplitude on the `g`-dependent part only.**
As `finalTerm_bound_rpow`, with `‖F g‖ ≤ K A e^{-κ₁ n}` replaced by
`‖F g - F 0‖ ≤ K A e^{-κ₁ n}` on the source ball. -/
theorem finalTerm_bound_of_sub
    {d L kf : ℕ} {β0 c₉ δ p A K C₀ κ₁ cov a x r : ℝ} {n : ℕ}
    (hd : 3 ≤ d) (hL : 2 ≤ L) (hc : 0 < c₉) (hβ0 : 0 < β0)
    (hpδ : ((d : ℝ) - 2) / 2 + δ ≤ p * ((d : ℝ) - 2)) (hK : 0 < K) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hκ : 0 ≤ κ₁) (hcov : 0 < cov) (ha : 0 < a) (hx : x ≤ n * (cov * a))
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ (c₉ * r / (K * C₀)) * β0 ^ p)
    (hA : A ≤ C₀ * ((Balaban.LargeField.ActionConv.betaK d L kf β0) ^ p)⁻¹)
    {F : (α → β → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (ball1 α β))
    (hFB : ∀ g ∈ ball1 α β, ‖F g - F 0‖ ≤ K * A * Real.exp (-κ₁ * n))
    {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (u : α) (b : β) :
    ‖kf0Deriv F g u b‖ ≤ c₉ * (L : ℝ) ^ (-(((kf + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
      Real.exp (-(κ₁ / cov) * x / a) := by
  rw [← kf0Deriv_sub_const F (F 0) g u b]
  exact finalTerm_bound_rpow hd hL hc hβ0 hpδ hK hC₀ hr hr2 hκ hcov ha hx hβ hA
    (F := fun h => F h - F 0) (fun h hh => (hF h hh).sub analyticAt_const) hFB hg u b

omit [DecidableEq α] [DecidableEq β] in
/-- **Schwarz on the larger ball.**  If `F` is analytic on `{l1 g < T}` and `‖F g - F 0‖ ≤ B`
there, then `‖F g - F 0‖ ≤ B * (l1 g / T)` for `l1 g < T`. -/
theorem norm_sub_zero_le_of_ball {T B : ℝ} {F : (α → β → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F {g | l1 g < T})
    (hB : ∀ g, l1 g < T → ‖F g - F 0‖ ≤ B) {g : α → β → ℂ} (hg : l1 g < T) :
    ‖F g - F 0‖ ≤ B * (l1 g / T) := by
  have hT : 0 < T := lt_of_le_of_lt (l1_nonneg g) hg
  rcases (l1_nonneg g).eq_or_lt with h0 | hℓ
  · have : g = 0 := by
      funext a; funext b
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg
        (fun _ _ => norm_nonneg _))).1 h0.symm a (Finset.mem_univ a)
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => norm_nonneg _)).1 this b
        (Finset.mem_univ b)
      simpa using this
    subst this
    simp [← h0]
  · set g' : α → β → ℂ := ((l1 g : ℂ))⁻¹ • g with hg'
    have hl1 : l1 g' = 1 := by
      rw [hg', l1_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
      exact inv_mul_cancel₀ hℓ.ne'
    have hmem : ∀ t : ℂ, ‖t‖ < T → l1 (t • g') < T := by
      intro t ht; rw [l1_smul, hl1, mul_one]; exact ht
    have hG := Balaban.Localization.norm_le_of_vanishing_zero (ι := Unit) (R := 1) (T := T) (B := B)
      (fun t (_ : Unit → ℂ) => F (t • g') - F 0)
      (fun p hp => by
        have hFt : AnalyticAt ℂ F (p.1 • g') :=
          hF _ (hmem _ (by simpa using hp.1))
        have hc : AnalyticAt ℂ (fun q : ℂ × (Unit → ℂ) => q.1 • g') p :=
          analyticAt_fst.smul analyticAt_const
        exact (AnalyticAt.comp (g := F) (f := fun q : ℂ × (Unit → ℂ) => q.1 • g') hFt hc).sub
          analyticAt_const)
      (fun _ => by simp)
      (fun t ht _ _ => hB _ (hmem t (by simpa using ht)))
      (t := (l1 g : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]; exact hg)
      (s := fun _ => 0) (fun i => by simp)
    have he : (l1 g : ℂ) • g' = g := by
      rw [hg', smul_smul, mul_inv_cancel₀ (by exact_mod_cast hℓ.ne'), one_smul]
    simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ] using hG

/-- **Root-F's bound with the amplitude from the larger ball.**  Let `F` be analytic on
`{l1 g < T}`, `T ≥ 1`, with `‖F g - F 0‖ ≤ B` there and `B / T ≤ K A e^{-κ₁ n}`.  Then the
conclusion of `finalTerm_bound_of_sub` holds (the amplitude on the unit ball is `B / T`). -/
theorem finalTerm_bound_of_sub_ball
    {d L kf : ℕ} {β0 c₉ δ p A K C₀ κ₁ cov a x r T B : ℝ} {n : ℕ}
    (hd : 3 ≤ d) (hL : 2 ≤ L) (hc : 0 < c₉) (hβ0 : 0 < β0)
    (hpδ : ((d : ℝ) - 2) / 2 + δ ≤ p * ((d : ℝ) - 2)) (hK : 0 < K) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hκ : 0 ≤ κ₁) (hcov : 0 < cov) (ha : 0 < a) (hx : x ≤ n * (cov * a))
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ (c₉ * r / (K * C₀)) * β0 ^ p)
    (hA : A ≤ C₀ * ((Balaban.LargeField.ActionConv.betaK d L kf β0) ^ p)⁻¹)
    (hT : 1 ≤ T) {F : (α → β → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F {g | l1 g < T})
    (hB : ∀ g, l1 g < T → ‖F g - F 0‖ ≤ B)
    (hBA : B / T ≤ K * A * Real.exp (-κ₁ * n))
    {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (u : α) (b : β) :
    ‖kf0Deriv F g u b‖ ≤ c₉ * (L : ℝ) ^ (-(((kf + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
      Real.exp (-(κ₁ / cov) * x / a) := by
  have hT0 : 0 < T := by linarith
  refine finalTerm_bound_of_sub hd hL hc hβ0 hpδ hK hC₀ hr hr2 hκ hcov ha hx hβ hA
    (fun h hh => hF h (lt_of_lt_of_le hh hT)) ?_ hg u b
  intro h hh
  have h1 : l1 h < T := lt_of_lt_of_le hh hT
  have h2 := norm_sub_zero_le_of_ball hF hB h1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simpa [l1] using hT0))
  refine h2.trans (le_trans ?_ hBA)
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by nlinarith [show l1 h ≤ 1 from hh.le]) hT0.le

end Balaban.Green
