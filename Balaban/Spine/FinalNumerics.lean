/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Analytic.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The tolerance `δ_k` against the radii `ε_j`

A6-3 (a), item 1: `δ_k = (β_k a)^{-1/2} A₀ λ_k^{p₀}`, `λ_k = log (β_k a)`, with
`β_k = β L^{k(d-2)} γ_k`, `|log γ_k| ≤ 1/20`, is bounded by
`C₀ β^{-(1/2 - γ/(d-2))} (L^{-α})^k`, `α = (d-2)/2 - γ`, uniformly in the scale `k`
(`delta_le_geom`): the polynomial factor `λ^{p₀}` is absorbed into a small power of `β_k a`
(`pow_le_exp_mul`). The radius `ε_k ≥ α₀ (L^{-α})^k` of the class decays at the same rate, so
`Γ δ_k ≤ ε_k` for `β` large, uniformly in `k` (`exists_beta_delta_le`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Real

/-- `λ^p ≤ p! ε^{-p} e^{ελ}` for `λ ≥ 0`, `ε > 0`. -/
theorem pow_le_exp_mul (p : ℕ) {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) :
    x ^ p ≤ (p.factorial : ℝ) * (ε ^ p)⁻¹ * Real.exp (ε * x) := by
  have h := Real.pow_div_factorial_le_exp (ε * x) (by positivity) p
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  rw [div_le_iff₀ hf, mul_pow] at h
  have hp : (0 : ℝ) < ε ^ p := by positivity
  calc x ^ p = (ε ^ p)⁻¹ * (ε ^ p * x ^ p) := by field_simp
    _ ≤ (ε ^ p)⁻¹ * (Real.exp (ε * x) * p.factorial) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- **The tolerance `δ_k` decays like the radius `ε_k`**, uniformly in the scale: with
`β_k = β L^{k(d-2)} γ_k`, `|log γ_k| ≤ 1/20`, `β ≥ 2`, `a > 1`,
`|(β_k a)^{-1/2} A₀ λ_k^{p₀}| ≤ C₀ β^{-(1/2 - γ/(d-2))} (L^{-α})^k` with `α = (d-2)/2 - γ`. -/
theorem delta_le_geom {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {γP : ℝ} (hγ0 : 0 < γP)
    (hγ1 : γP < 1 / 2) {a : ℝ} (ha : 1 < a) (A0 : ℝ) (p0 : ℕ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ β : ℝ, 2 ≤ β → ∀ (bk : ℝ) (k : ℕ),
      (∃ g : ℝ, 0 < g ∧ |Real.log g| ≤ 1 / 20 ∧ bk = β * (L : ℝ) ^ (k * (d - 2)) * g) →
      |(bk * a) ^ (-(1 / 2 : ℝ)) * (A0 * Real.log (bk * a) ^ p0)| ≤
        C0 * β ^ (-(1 / 2 - γP / ((d : ℝ) - 2))) *
          ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := by
  have hd2 : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set ε : ℝ := γP / ((d : ℝ) - 2) with hε
  have hε0 : 0 < ε := div_pos hγ0 (by linarith)
  have hε1 : ε < 1 / 2 := by
    have : γP < 1 / 2 * ((d : ℝ) - 2) := by nlinarith
    rw [hε, div_lt_iff₀ (by linarith)]
    linarith
  set s : ℝ := 1 / 2 - ε with hs
  have hs0 : 0 < s := by linarith
  have hαs : ((d : ℝ) - 2) / 2 - γP = ((d : ℝ) - 2) * s := by
    rw [hs, hε]; field_simp
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  refine ⟨|A0| * p0.factorial * (ε ^ p0)⁻¹ * 3, by positivity, ?_⟩
  intro β hβ bk k ⟨g, hg0, hg, hbk⟩
  -- lower bound of x = bk * a
  have hexp : Real.exp (-(1 / 20)) ≤ g := by
    have := (abs_le.1 hg).1
    calc Real.exp (-(1 / 20)) ≤ Real.exp (Real.log g) := Real.exp_le_exp.2 this
      _ = g := Real.exp_log hg0
  have hexp2 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 20)) := by
    have := Real.add_one_le_exp (-(1 / 20 : ℝ))
    linarith
  set u : ℝ := β * (L : ℝ) ^ (k * (d - 2)) with hu
  have hLk : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hu2 : 2 ≤ u := by
    rw [hu]; nlinarith
  have hx : u * Real.exp (-(1 / 20)) ≤ bk * a := by
    rw [hbk]
    have h1 : u * Real.exp (-(1 / 20)) ≤ u * g := mul_le_mul_of_nonneg_left hexp (by linarith)
    have h2 : u * g ≤ u * g * a := le_mul_of_one_le_right (by positivity) ha.le
    linarith
  have hx1 : 1 ≤ bk * a := by
    have : (1 : ℝ) ≤ u * Real.exp (-(1 / 20)) := by nlinarith
    linarith
  set x : ℝ := bk * a with hxdef
  have hx0 : 0 < x := by linarith
  have hlam : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hpow := pow_le_exp_mul p0 hε0 hlam
  have hexpx : Real.exp (ε * Real.log x) = x ^ ε := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  rw [hexpx] at hpow
  have hxs : x ^ (-(1 / 2 : ℝ)) * x ^ ε = x ^ (-s) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [hs]; ring
  have h1 : |x ^ (-(1 / 2 : ℝ)) * (A0 * Real.log x ^ p0)| ≤
      |A0| * p0.factorial * (ε ^ p0)⁻¹ * x ^ (-s) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
      abs_of_nonneg (pow_nonneg hlam _)]
    calc x ^ (-(1 / 2 : ℝ)) * (|A0| * Real.log x ^ p0)
        ≤ x ^ (-(1 / 2 : ℝ)) * (|A0| * (p0.factorial * (ε ^ p0)⁻¹ * x ^ ε)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
            (Real.rpow_nonneg hx0.le _)
      _ = |A0| * p0.factorial * (ε ^ p0)⁻¹ * (x ^ (-(1 / 2 : ℝ)) * x ^ ε) := by ring
      _ = _ := by rw [hxs]
  have hu0 : 0 < u := by linarith
  have hexp0 : 0 < Real.exp (-(1 / 20)) := Real.exp_pos _
  have h2 : x ^ (-s) ≤ (u * Real.exp (-(1 / 20))) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)
  have h3 : (u * Real.exp (-(1 / 20))) ^ (-s) = u ^ (-s) * Real.exp (s / 20) := by
    rw [Real.mul_rpow hu0.le hexp0.le, ← Real.exp_mul]
    congr 2; ring
  have h4 : Real.exp (s / 20) ≤ 3 := by
    have : Real.exp (s / 20) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    exact this.trans (Real.exp_one_lt_d9.le.trans (by norm_num))
  have h5 : u ^ (-s) = β ^ (-s) * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := by
    rw [hu, Real.mul_rpow (by linarith) (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      hαs]
    congr 1
    have : ((k * (d - 2) : ℕ) : ℝ) = (k : ℝ) * ((d : ℝ) - 2) := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ d)]; ring
    rw [this]; ring
  calc |x ^ (-(1 / 2 : ℝ)) * (A0 * Real.log x ^ p0)|
      ≤ |A0| * p0.factorial * (ε ^ p0)⁻¹ * x ^ (-s) := h1
    _ ≤ |A0| * p0.factorial * (ε ^ p0)⁻¹ * (u ^ (-s) * 3) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc x ^ (-s) ≤ (u * Real.exp (-(1 / 20))) ^ (-s) := h2
          _ = u ^ (-s) * Real.exp (s / 20) := h3
          _ ≤ u ^ (-s) * 3 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hu0.le _)
    _ = |A0| * p0.factorial * (ε ^ p0)⁻¹ * 3 * β ^ (-s) *
          ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := by rw [h5]; ring

/-- **`Γ δ_k ≤ min (c, α₀ (L^{-α})^k)` for `β` large, uniformly in `k`.** -/
theorem exists_beta_delta_le {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {γP : ℝ} (hγ0 : 0 < γP)
    (hγ1 : γP < 1 / 2) {a : ℝ} (ha : 1 < a) (A0 : ℝ) (p0 : ℕ) (Γ c α₀ : ℝ) (hΓ : 0 ≤ Γ)
    (hc : 0 < c) (hα₀ : 0 < α₀) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ (bk : ℝ) (k : ℕ),
      (∃ g : ℝ, 0 < g ∧ |Real.log g| ≤ 1 / 20 ∧ bk = β * (L : ℝ) ^ (k * (d - 2)) * g) →
      Γ * |(bk * a) ^ (-(1 / 2 : ℝ)) * (A0 * Real.log (bk * a) ^ p0)| ≤
        min c (α₀ * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k) := by
  obtain ⟨C0, hC0, hC⟩ := delta_le_geom hd hL hγ0 hγ1 ha A0 p0
  have hd2 : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set s : ℝ := 1 / 2 - γP / ((d : ℝ) - 2) with hs
  have hs0 : 0 < s := by
    have : γP / ((d : ℝ) - 2) < 1 / 2 := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    rw [hs]; linarith
  set m : ℝ := min c α₀ with hm
  have hm0 : 0 < m := lt_min hc hα₀
  refine ⟨max 2 ((Γ * C0 / m + 1) ^ (1 / s)), le_max_left _ _, fun β hβ bk k hbk => ?_⟩
  have hβ2 : 2 ≤ β := (le_max_left _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hgeo := hC β hβ2 bk k hbk
  have hq0 : 0 ≤ ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := by
    have : 0 ≤ (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hq1 : ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k ≤ 1 := by
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have hα : 0 ≤ ((d : ℝ) - 2) / 2 - γP := by linarith
    exact pow_le_one₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  -- Γ C0 β^{-s} ≤ m
  have hbs : Γ * C0 * β ^ (-s) ≤ m := by
    have h1 : (Γ * C0 / m + 1) ≤ β ^ s := by
      have h2 : ((Γ * C0 / m + 1) ^ (1 / s)) ≤ β := (le_max_right _ _).trans hβ
      have h3 : 0 ≤ (Γ * C0 / m + 1) := by positivity
      calc Γ * C0 / m + 1 = ((Γ * C0 / m + 1) ^ (1 / s)) ^ s := by
            rw [← Real.rpow_mul h3, one_div_mul_cancel hs0.ne', Real.rpow_one]
        _ ≤ β ^ s := Real.rpow_le_rpow (Real.rpow_nonneg h3 _) h2 hs0.le
    rw [Real.rpow_neg hβ0.le]
    have hbp : 0 < β ^ s := Real.rpow_pos_of_pos hβ0 s
    rw [mul_inv_le_iff₀ hbp]
    have : Γ * C0 ≤ m * (Γ * C0 / m + 1) := by
      rw [mul_add, mul_div_cancel₀ _ hm0.ne']; linarith
    nlinarith
  have hmain : Γ * |(bk * a) ^ (-(1 / 2 : ℝ)) * (A0 * Real.log (bk * a) ^ p0)| ≤
      Γ * C0 * β ^ (-s) * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := by
    calc _ ≤ Γ * (C0 * β ^ (-s) * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k) :=
          mul_le_mul_of_nonneg_left hgeo hΓ
      _ = _ := by ring
  refine le_min ?_ ?_
  · calc _ ≤ Γ * C0 * β ^ (-s) * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := hmain
      _ ≤ Γ * C0 * β ^ (-s) * 1 := mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ ≤ m := by rw [mul_one]; exact hbs
      _ ≤ c := min_le_left _ _
  · calc _ ≤ Γ * C0 * β ^ (-s) * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k := hmain
      _ ≤ m * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k :=
          mul_le_mul_of_nonneg_right hbs hq0
      _ ≤ α₀ * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γP))) ^ k :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hq0

end Balaban.RootFSpine
