/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRBeta`: the conditions on large `β` (route FR, (P))

`notes/phase1/KF0-FR.md` (P). With the parameters `p, c_G, b_*, η_*` of the block side fixed, every
condition of the route that involves `β` holds for `β ≥ β₀`, uniformly in `ν_* ≤ ν ≤ 1`
(`frBeta_large`): powers of `√β` times `e^{-cβ}` and `β^{-1}` are small.
-/

@[expose] public section

open Filter Topology

namespace Balaban.LargeField.KF0FR

noncomputable section

/-- A power times a decaying exponential is eventually small. -/
theorem eventually_pow_mul_exp_le {c : ℝ} (hc : 0 < c) (K : ℕ) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, C * β ^ K * Real.exp (-(c * β)) ≤ ε := by
  have h1 : Tendsto (fun x : ℝ => x ^ K * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K
  have h2 : Tendsto (fun β : ℝ => c * β) atTop atTop := tendsto_id.const_mul_atTop hc
  have h3 : Tendsto (fun β : ℝ => C / c ^ K * ((c * β) ^ K * Real.exp (-(c * β)))) atTop (𝓝 0) := by
    simpa using (h1.comp h2).const_mul (C / c ^ K)
  filter_upwards [h3.eventually (gt_mem_nhds hε)] with β hβ
  have e : C * β ^ K * Real.exp (-(c * β)) = C / c ^ K * ((c * β) ^ K * Real.exp (-(c * β))) := by
    rw [mul_pow]; field_simp
  rw [e]; exact hβ.le

/-- `A / β` is eventually small. -/
theorem eventually_div_le (A : ℝ) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ β : ℝ in atTop, A / β ≤ ε := by
  have h := (tendsto_const_nhds (x := A)).div_atTop (tendsto_id (α := ℝ) (x := atTop))
  filter_upwards [h.eventually (gt_mem_nhds hε)] with β hβ using hβ.le

/-- `c √β` eventually exceeds any bound. -/
theorem eventually_lt_mul_sqrt {c : ℝ} (hc : 0 < c) (A : ℝ) : ∀ᶠ β : ℝ in atTop, A < c * Real.sqrt β := by
  have h : Tendsto (fun β : ℝ => c * Real.sqrt β) atTop atTop :=
    (Real.tendsto_sqrt_atTop).const_mul_atTop hc
  exact h.eventually_gt_atTop A

/-- `2 c √β ≤ c' β / 4` eventually. -/
theorem eventually_sqrt_le {c c' : ℝ} (hc' : 0 < c') :
    ∀ᶠ β : ℝ in atTop, 2 * c * Real.sqrt β ≤ c' * β / 4 := by
  filter_upwards [eventually_ge_atTop (max 1 ((8 * |c| / c') ^ 2))] with β hβ
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : (8 * |c| / c') ^ 2 ≤ β := (le_max_right _ _).trans hβ
  have hs : 8 * |c| / c' ≤ Real.sqrt β := Real.le_sqrt_of_sq_le hβ2
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt β := Real.sqrt_nonneg _
  have h8 : 8 * |c| ≤ c' * Real.sqrt β := by
    rw [div_le_iff₀ hc'] at hs; linarith
  have hc : c ≤ |c| := le_abs_self c
  nlinarith

/-- **The conditions on large `β`.** For fixed positive constants, all of the following hold for
`β ≥ β₀`. -/
theorem frBeta_large {p ns bs cG M0 η Γ Wc c0 α tgt : ℝ} (K : ℕ) (hns : 0 < ns) (hbs : 0 < bs)
    (hcG : 0 < cG) (hη : 0 < η) (htgt : 0 < tgt) :
    ∃ β₀ : ℝ, 1 ≤ β₀ ∧ ∀ β, β₀ ≤ β →
      p ^ 2 / (β * ns) ≤ 1 / 4 ∧ p ^ 2 / (β * ns) ≤ bs / 48 ∧
      p ^ 4 / (2 * β * ns) ≤ bs / 48 ∧ p ^ 4 / (2 * β * ns ^ 2) ≤ bs / 4 ∧
      2 * cG * Real.sqrt β ≤ ns * β / 4 ∧
      2 * M0 * Real.exp (-(ns / 4 * β)) ≤ η / 2 ∧
      M0 * Real.exp (-(ns * β)) ≤ η / 4 ∧
      Γ * 2 * Wc * c0 * β ^ K * Real.exp (-(ns / 128 * β)) ≤ η ∧
      Γ * Wc * c0 * β ^ K * Real.exp (-(ns / 128 * β)) ≤ 1 ∧
      1 < cG * Real.sqrt β ∧ 2 * α / (cG * Real.sqrt β) ≤ tgt := by
  have e1 := eventually_div_le (p ^ 2 / ns) (ε := 1 / 4) (by norm_num)
  have e2 := eventually_div_le (p ^ 2 / ns) (ε := bs / 48) (by positivity)
  have e3 := eventually_div_le (p ^ 4 / (2 * ns)) (ε := bs / 48) (by positivity)
  have e4 := eventually_div_le (p ^ 4 / (2 * ns ^ 2)) (ε := bs / 4) (by positivity)
  have e5 := eventually_sqrt_le (c := cG) (c' := ns) hns
  have e6 := eventually_pow_mul_exp_le (c := ns / 4) (by positivity) 0 (2 * M0) (ε := η / 2)
    (by positivity)
  have e7 := eventually_pow_mul_exp_le (c := ns) hns 0 M0 (ε := η / 4) (by positivity)
  have e8 := eventually_pow_mul_exp_le (c := ns / 128) (by positivity) K (Γ * 2 * Wc * c0) hη
  have e9 := eventually_pow_mul_exp_le (c := ns / 128) (by positivity) K (Γ * Wc * c0) one_pos
  have e10 := eventually_lt_mul_sqrt hcG 1
  have e11 := eventually_lt_mul_sqrt hcG (2 * α / tgt)
  have e12 : ∀ᶠ β : ℝ in atTop, 1 ≤ β := eventually_ge_atTop 1
  obtain ⟨β₀, hβ₀⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and
    (e7.and (e8.and (e9.and (e10.and (e11.and e12)))))))))))
  refine ⟨max β₀ 1, le_max_right _ _, fun β hβ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hβ₀ β ((le_max_left _ _).trans hβ)
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos h12
  have hs : 0 < cG * Real.sqrt β := lt_trans one_pos h10
  refine ⟨?_, ?_, ?_, ?_, h5, ?_, ?_, ?_, ?_, h10, ?_⟩
  · calc p ^ 2 / (β * ns) = p ^ 2 / ns / β := by rw [mul_comm, div_div]
      _ ≤ _ := h1
  · calc p ^ 2 / (β * ns) = p ^ 2 / ns / β := by rw [mul_comm, div_div]
      _ ≤ _ := h2
  · calc p ^ 4 / (2 * β * ns) = p ^ 4 / (2 * ns) / β := by rw [div_div]; ring_nf
      _ ≤ _ := h3
  · calc p ^ 4 / (2 * β * ns ^ 2) = p ^ 4 / (2 * ns ^ 2) / β := by rw [div_div]; ring_nf
      _ ≤ _ := h4
  · simpa using h6
  · simpa using h7
  · exact h8
  · exact h9
  · rw [div_le_iff₀ hs]
    have := h11
    rw [div_lt_iff₀ htgt] at this
    nlinarith

end

end Balaban.LargeField.KF0FR
