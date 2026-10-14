/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.KF0Cauchy
public import Balaban.LargeField.R.CancelIdentity

/-!
# The arithmetic of Root-F's term bounds

Three pieces that do not depend on the open blockers of the flow.

* Constant matching: a per-term bound of the form produced by the one-step theorems,
  `C (C' L^e β^{-q}) L^{-j e} e^{λ} E`, is at most `c₉ L^{-j e} E` once `β` is beyond an explicit
  threshold (`rootBound_of_perTerm`).
* The large-field polymer term: with `β_k = β₀ L^{k(d-2)}` and `δ ≤ (d-2)/2`, the bound
  `β_{k}^{-2} ≤ c₉ L^{-(k+1)((d-2)/2+δ)}` holds for every `k` as soon as `L^{(d-2)/2+δ} ≤ c₉ β₀²`
  (`betaK_inv_sq_le`); the stopping condition on `k_f` is not needed.
* The Cauchy step in one source variable: the radius is `1/2` inside the unit ball, and a bound
  `B` of the family on the ball gives `2B` for the first-order term (`norm_kf0Deriv_le_two`).
-/

@[expose] public section

namespace Balaban.Inhabited.RootBoundsArith

open Balaban.Correlations

/-- The amplitude `A β^{-q}` is at most `c` once `β ≥ (A/c)^{1/q}`. -/
theorem amplitude_le {A q β c : ℝ} (hA : 0 < A) (hq : 0 < q) (hc : 0 < c)
    (hβ : (A / c) ^ (1 / q) ≤ β) : A * β ^ (-q) ≤ c := by
  have h0 : 0 < (A / c) ^ (1 / q) := Real.rpow_pos_of_pos (div_pos hA hc) _
  have hβ0 : 0 < β := lt_of_lt_of_le h0 hβ
  have h1 : A / c ≤ β ^ q := by
    have := Real.rpow_le_rpow h0.le hβ hq.le
    rwa [← Real.rpow_mul (div_pos hA hc).le, one_div_mul_cancel hq.ne', Real.rpow_one] at this
  rw [Real.rpow_neg hβ0.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hβ0 _)]
  rw [div_le_iff₀ hc] at h1
  linarith

/-- **Constant matching.**  A per-term bound
`‖U‖ ≤ C (C' L^e β^{-q}) L^{-(j e)} e^{λ} E` (with `e = (d-2)/2 + δ`, `q = e/(d-2)`,
`E = exp (-κ |X| / (M L^j)^d)`) gives Root-F's bound `‖U‖ ≤ c₉ L^{-(j e)} E` as soon as
`β ≥ (C C' e^{λ} L^e / c₉)^{1/q}`. -/
theorem rootBound_of_perTerm {C C' lam e q β c₉ L E j : ℝ} {u : ℝ}
    (hC : 0 < C) (hC' : 0 < C') (hq : 0 < q) (hc : 0 < c₉) (hL : 0 < L) (hE : 0 ≤ E)
    (hβ : (C * C' * Real.exp lam * L ^ e / c₉) ^ (1 / q) ≤ β)
    (hu : u ≤ C * (C' * L ^ e * β ^ (-q)) * L ^ (-(j * e)) * Real.exp lam * E) :
    u ≤ c₉ * L ^ (-(j * e)) * E := by
  have hA : 0 < C * C' * Real.exp lam * L ^ e :=
    by have := Real.rpow_pos_of_pos hL e; have := Real.exp_pos lam; positivity
  have h := amplitude_le hA hq hc hβ
  have hP : 0 ≤ L ^ (-(j * e)) := (Real.rpow_pos_of_pos hL _).le
  refine hu.trans ?_
  calc C * (C' * L ^ e * β ^ (-q)) * L ^ (-(j * e)) * Real.exp lam * E
      = (C * C' * Real.exp lam * L ^ e * β ^ (-q)) * L ^ (-(j * e)) * E := by ring
    _ ≤ c₉ * L ^ (-(j * e)) * E := by gcongr

/-- **The `𝓟` arithmetic.**  For `β_k = β₀ L^{k(d-2)}` (`betaK`), `3 ≤ d`, `2 ≤ L`,
`0 ≤ δ ≤ (d-2)/2` and `L^{(d-2)/2+δ} ≤ c₉ β₀²`:
`β_k^{-2} ≤ c₉ L^{-(k+1)((d-2)/2+δ)}` for every `k`, in particular for `k = k_f`. -/
theorem betaK_inv_sq_le {d L k : ℕ} {β0 c₉ δ : ℝ} (hd : 3 ≤ d) (hL : 2 ≤ L) (hc : 0 < c₉)
    (hβ0 : 0 < β0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((d : ℝ) - 2) / 2)
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ c₉ * β0 ^ 2) :
    ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹ ≤
      c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  set e : ℝ := ((d : ℝ) - 2) / 2 + δ with he
  have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have he0 : 0 ≤ e := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    rw [he]; linarith
  have heb : e ≤ (d : ℝ) - 2 := by rw [he]; linarith
  have hsq : Balaban.LargeField.ActionConv.betaK d L k β0 ^ 2 = β0 ^ 2 * (L : ℝ) ^ (2 * (k * (d - 2))) := by
    unfold Balaban.LargeField.ActionConv.betaK; rw [mul_pow, ← pow_mul, mul_comm (k * (d - 2)) 2]
  have hexp : (k : ℝ) * e ≤ ((2 * (k * (d - 2)) : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_sub (by omega)]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    nlinarith
  have hkl : (L : ℝ) ^ ((k : ℝ) * e) ≤ (L : ℝ) ^ (2 * (k * (d - 2))) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 hexp
  have hsplit : (L : ℝ) ^ (((k + 1 : ℕ) : ℝ) * e) = (L : ℝ) ^ e * (L : ℝ) ^ ((k : ℝ) * e) := by
    rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
  rw [hsq, Real.rpow_neg hL0.le, ← div_eq_mul_inv, ← one_div]
  have hpos : 0 < (L : ℝ) ^ (((k + 1 : ℕ) : ℝ) * e) := Real.rpow_pos_of_pos hL0 _
  have hpos2 : 0 < β0 ^ 2 * (L : ℝ) ^ (2 * (k * (d - 2))) := by positivity
  rw [div_le_div_iff₀ hpos2 hpos, hsplit]
  have h3 : (L : ℝ) ^ e * (L : ℝ) ^ ((k : ℝ) * e) ≤
      c₉ * β0 ^ 2 * (L : ℝ) ^ (2 * (k * (d - 2))) :=
    mul_le_mul hβ hkl (Real.rpow_pos_of_pos hL0 _).le (by positivity)
  nlinarith

/-- **The Cauchy step in one source variable, radius `1/2`.**  If `F` is analytic on the source
ball `{∑|g| < 1}` and bounded by `B` there, then for `∑|g| ≤ 1/2` the first-order term
`∫₀¹ ∂_{g_b(a)} F(t g) dt` is bounded by `2 B` (the disc used has radius `1/2` around `t g`, which
stays inside the unit ball). -/
theorem norm_kf0Deriv_le_two {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] {F : (α → β → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (ball1 α β)) {B : ℝ}
    (hB : ∀ g ∈ ball1 α β, ‖F g‖ ≤ B) {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (a : α) (b : β) :
    ‖kf0Deriv F g a b‖ ≤ 2 * B := by
  have hg1 : g ∈ ball1 α β := by show l1 g < 1; linarith
  rw [kf0Deriv_eq_integral hF hg1]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t : ℝ => fderiv ℂ F ((t : ℂ) • g) (unitSource a b)) (C := 2 * B) ?_
  · simpa using this
  intro t ht
  rw [Set.uIoc_of_le zero_le_one] at ht
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hw : l1 ((t : ℂ) • g) ≤ 1 / 2 := by
    rw [l1_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htI.1]
    nlinarith [ht.2, l1_nonneg g]
  have key := Balaban.Analysis.norm_fderiv_line_le (f := F) (w := (t : ℂ) • g)
    (v := unitSource a b) (ρ := 1 / 2) (M := B) (by norm_num)
    (fun l hl => (hF _ (line_mem_ball1 hw a b (by linarith))).differentiableAt)
    (fun l hl => hB _ (line_mem_ball1 hw a b (by linarith)))
  calc ‖fderiv ℂ F ((t : ℂ) • g) (unitSource a b)‖ ≤ B / (1 / 2) := key
    _ = 2 * B := by ring

end Balaban.Inhabited.RootBoundsArith
