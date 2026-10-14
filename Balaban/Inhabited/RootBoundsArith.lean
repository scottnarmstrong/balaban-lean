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

/-- **The `𝓟` arithmetic with a real power.**  For `β_k = β₀ L^{k(d-2)}` (`betaK`), `3 ≤ d`,
`2 ≤ L`, a real `p` with `p (d-2) ≥ (d-2)/2 + δ` and
`L^{(d-2)/2+δ} ≤ c₉ β₀^p`: `β_k^{-p} ≤ c₉ L^{-(k+1)((d-2)/2+δ)}` for every `k`. -/
theorem betaK_inv_rpow_le {d L k : ℕ} {β0 c₉ δ p : ℝ} (hd : 3 ≤ d) (hL : 2 ≤ L)
    (hc : 0 < c₉) (hβ0 : 0 < β0)
    (hpδ : ((d : ℝ) - 2) / 2 + δ ≤ p * ((d : ℝ) - 2))
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ c₉ * β0 ^ p) :
    ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ p)⁻¹ ≤
      c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  set e : ℝ := ((d : ℝ) - 2) / 2 + δ with he
  have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hpow : Balaban.LargeField.ActionConv.betaK d L k β0 ^ p =
      β0 ^ p * (L : ℝ) ^ ((k : ℝ) * (p * ((d : ℝ) - 2))) := by
    unfold Balaban.LargeField.ActionConv.betaK
    rw [Real.mul_rpow hβ0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 2
    push_cast [hd2]; ring
  have hkl : (L : ℝ) ^ ((k : ℝ) * e) ≤ (L : ℝ) ^ ((k : ℝ) * (p * ((d : ℝ) - 2))) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (mul_le_mul_of_nonneg_left hpδ (Nat.cast_nonneg k))
  have hsplit : (L : ℝ) ^ (((k + 1 : ℕ) : ℝ) * e) = (L : ℝ) ^ e * (L : ℝ) ^ ((k : ℝ) * e) := by
    rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
  have hb0 : 0 < β0 ^ p := Real.rpow_pos_of_pos hβ0 _
  rw [hpow, Real.rpow_neg hL0.le, ← div_eq_mul_inv, ← one_div]
  have hpos : 0 < (L : ℝ) ^ (((k + 1 : ℕ) : ℝ) * e) := Real.rpow_pos_of_pos hL0 _
  have hpos2 : 0 < β0 ^ p * (L : ℝ) ^ ((k : ℝ) * (p * ((d : ℝ) - 2))) :=
    mul_pos hb0 (Real.rpow_pos_of_pos hL0 _)
  rw [div_le_div_iff₀ hpos2 hpos, hsplit]
  have h3 : (L : ℝ) ^ e * (L : ℝ) ^ ((k : ℝ) * e) ≤
      c₉ * β0 ^ p * (L : ℝ) ^ ((k : ℝ) * (p * ((d : ℝ) - 2))) :=
    mul_le_mul (by simpa [mul_comm] using hβ) hkl (Real.rpow_pos_of_pos hL0 _).le
      (by positivity)
  nlinarith

/-- **The `𝓟` arithmetic.**  For `β_k = β₀ L^{k(d-2)}` (`betaK`), `3 ≤ d`, `2 ≤ L`,
`0 ≤ δ ≤ (d-2)/2` and `L^{(d-2)/2+δ} ≤ c₉ β₀²`:
`β_k^{-2} ≤ c₉ L^{-(k+1)((d-2)/2+δ)}` for every `k`, in particular for `k = k_f`. -/
theorem betaK_inv_sq_le {d L k : ℕ} {β0 c₉ δ : ℝ} (hd : 3 ≤ d) (hL : 2 ≤ L) (hc : 0 < c₉)
    (hβ0 : 0 < β0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((d : ℝ) - 2) / 2)
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ c₉ * β0 ^ 2) :
    ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹ ≤
      c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have _ := hδ0
  have h := betaK_inv_rpow_le (k := k) (δ := δ) (p := 2) hd hL hc hβ0 (by linarith)
    (by simpa [Real.rpow_two] using hβ)
  simpa [Real.rpow_two] using h

/-- **The Cauchy step in one source variable, radius `1/2`.**  If `F` is analytic on the source
ball `{∑|g| < 1}` and bounded by `B` there, then for `∑|g| ≤ 1/2` the first-order term
`∫₀¹ ∂_{g_b(a)} F(t g) dt` is bounded by `2 B` (the disc used has radius `1/2` around `t g`, which
stays inside the unit ball). -/
theorem norm_kf0Deriv_le_two {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] {F : (α → β → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (ball1 α β)) {B : ℝ}
    (hB : ∀ g ∈ ball1 α β, ‖F g‖ ≤ B) {g : α → β → ℂ} (hg : l1 g ≤ 1 / 2) (a : α) (b : β) :
    ‖kf0Deriv F g a b‖ ≤ 2 * B := by
  have := norm_kf0Deriv_le_radius hF (r := 1 / 2) (by norm_num) le_rfl hB hg a b
  rwa [show B / (1 / 2) = 2 * B by ring] at this

end Balaban.Inhabited.RootBoundsArith
