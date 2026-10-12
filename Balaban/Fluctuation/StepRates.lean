/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsTerms
public import Balaban.Fluctuation.HatLabelsExpansion
public import Balaban.Fluctuation.StepNonvanishBound
public import Balaban.Fluctuation.Thm31b
public import Balaban.Fluctuation.Theorem42
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The arithmetic of the decay rates around one fluctuation step

Real arithmetic of `notes/phase1/RATES.md`, against the landed rate fields.

* `stepRates_no_closure` (T1): the abstract inequalities (4)-(5) of the note.
* `stepRates_no_closure_landed` (T2): the same at the landed label conversion
  `hatKappaH d L a = a / hatA d L - c1 d L` (`HatLabelsTerms.lean:50`, `hatA d L = 1 + 2^d c1 cG`,
  `HatLabelsTerms.lean:40`), with `a = 2 κ_dec - 1` the rate of the expansion terms of
  `interaction_expansion_hat_bound` (`InteractionHatAssemble.lean:95`: `exp (-(2 * κdec - 1) * ...)`).
  Thus `F = c1` and `A = hatA d L`.  The landed rate fields abstracted:
  - (i): old terms enter at `κdec - 1` (`InteractionHatAssemble.lean:189`,
    `exp (-(κdec - 1) * treeLenCovOne ...)`), against the class rate `κ_in` of `Def6`;
  - (iii): `StepActivityBound.hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH`
    (`StepNonvanishBound.lean:76`), the same field in `InterpMarks.hκ` (`Thm31cde.lean:114`) and
    `ObsMarks.hκ` (`Thm31b.lean:119`);
  - (iv): `thm31b_of_input`'s `hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1` (`Thm31b.lean:304`), with
    `κh ≥ κ'` as in the note.
* `stepRates_additive_closure_of_additive` (T3): the conditional positive result when the
  conversion is additive (NOT landed).
* `stepRates_trace_witness` (T4): the remaining numerical fields are jointly satisfiable.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban

/-- **T1 (RATES (4)-(5)).** -/
theorem stepRates_no_closure {A F κ0 c κin κdec κH κ' κout : ℝ} (hA : 2 < A) (hF : 0 ≤ F)
    (hκ0 : 0 ≤ κ0) (hc : 0 ≤ c) (hκin : 0 < κin)
    (h1 : κdec - 1 ≤ κin) (h2 : κH ≤ (2 * κdec - 1) / A - F)
    (h3 : κ' + (3 * κ0 + c + 3 / 2) ≤ κH) (h4 : κout ≤ κ' - κ0 - 1) :
    κout ≤ (2 * κin + 1) / A - (F + (3 * κ0 + c + 3 / 2) + κ0 + 1) ∧ κout < κin := by
  have hA0 : 0 < A := by linarith
  have h5 : (2 * κdec - 1) / A ≤ (2 * κin + 1) / A :=
    div_le_div_of_nonneg_right (by linarith) hA0.le
  have key : κout ≤ (2 * κin + 1) / A - (F + (3 * κ0 + c + 3 / 2) + κ0 + 1) := by linarith
  refine ⟨key, ?_⟩
  have hB : 5 / 2 ≤ F + (3 * κ0 + c + 3 / 2) + κ0 + 1 := by linarith
  have h6 : (2 * κin + 1) / A < κin + (F + (3 * κ0 + c + 3 / 2) + κ0 + 1) := by
    rw [div_lt_iff₀ hA0]; nlinarith
  linarith

/-- **T1, iterated form.** -/
theorem stepRates_iterate {A B : ℝ} (hA : 2 < A) (hAB : 1 < A * B) (κ : ℕ → ℝ)
    (h : ∀ n, κ (n + 1) ≤ 2 / A * κ n + 1 / A - B) : ∃ n, κ n ≤ 0 := by
  have hA0 : 0 < A := by linarith
  have he : 0 < B - 1 / A := by
    have : 1 / A < B := by rw [div_lt_iff₀ hA0]; linarith
    linarith
  by_contra hcon0
  have hcon : ∀ n, 0 < κ n := fun n => not_le.1 (fun h => hcon0 ⟨n, h⟩)
  have step : ∀ n, κ (n + 1) ≤ κ n - (B - 1 / A) := by
    intro n
    have hq : 2 / A < 1 := by rw [div_lt_iff₀ hA0]; linarith
    have := h n
    have := hcon n
    nlinarith
  have bound : ∀ n : ℕ, κ n ≤ κ 0 - n * (B - 1 / A) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => have := step n; push_cast; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (κ 0 / (B - 1 / A))
  have := bound n
  have h7 : κ 0 < n * (B - 1 / A) := (div_lt_iff₀ he).1 hn
  have := hcon n
  linarith

/-- **T3 (conditional, additive conversion not landed).**  The threshold
`κ_in = 2 (F + D + κ0 + 2)` works; (ii′) is `κH ≤ 2 κdec - 1 - F`. -/
theorem stepRates_additive_closure_of_additive (κ0 c F : ℝ) (hκ0 : 0 ≤ κ0) (hc : 0 ≤ c)
    (hF : 0 ≤ F) :
    ∃ κin κdec κ' κH κout : ℝ, 0 < κin ∧ κdec - 1 ≤ κin ∧ κH ≤ 2 * κdec - 1 - F ∧
      κ' + (3 * κ0 + c + 3 / 2) ≤ κH ∧ κout ≤ κ' - κ0 - 1 ∧ 3 * κ0 + 3 ≤ κdec ∧ κ0 ≤ κ' ∧
      κin ≤ κout := by
  refine ⟨2 * (F + (3 * κ0 + c + 3 / 2) + κ0 + 2), 2 * (F + (3 * κ0 + c + 3 / 2) + κ0 + 2),
    3 / 2 * (2 * (F + (3 * κ0 + c + 3 / 2) + κ0 + 2)) + κ0 + 1,
    3 / 2 * (2 * (F + (3 * κ0 + c + 3 / 2) + κ0 + 2)) + κ0 + 1 + (3 * κ0 + c + 3 / 2),
    3 / 2 * (2 * (F + (3 * κ0 + c + 3 / 2) + κ0 + 2)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith

/-- `hatA d L > 2` for `d ≥ 3`, `L ≥ 3`. -/
theorem two_lt_hatA {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) : 2 < hatA d L := by
  have : NeZero L := ⟨by omega⟩
  have h1 : 1 ≤ c1 d L := one_le_c1 d L
  have h2 : (8 : ℝ) ≤ 2 ^ d := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have h3 : (18 : ℝ) ≤ cG d L := by
    unfold cG
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  unfold hatA
  have : 8 * 1 * 18 ≤ 2 ^ d * c1 d L * cG d L := by
    apply mul_le_mul (mul_le_mul h2 h1 (by norm_num) (by positivity)) h3 (by norm_num)
      (by positivity)
  linarith

/-- **T2.**  At the landed conversion `κ_H = hatKappaH d L (2 κdec - 1) = (2 κdec - 1)/A - c1`
(`A = hatA d L`, `F = c1`), the landed fields (iii) `κ' + 3 κ0 + c1 + 3/2 ≤ κ_H`
(`StepActivityBound.hκ`), (iv) `κout ≤ min κh κ' - κ0 - 1` (`thm31b_of_input`, `κ' ≤ κh`) and
(i) `κdec - 1 ≤ κin` force `κout < κin` for every positive input rate. -/
theorem stepRates_no_closure_landed {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L)
    {κ0 κin κdec κ' κh κout : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hκin : 0 < κin)
    (hdec : κdec - 1 ≤ κin) (hκh : κ' ≤ κh)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ hatKappaH d L (2 * κdec - 1))
    (hκout : κout ≤ min κh κ' - κ0 - 1) : κout < κin := by
  have : NeZero L := ⟨by omega⟩
  have h0 : 0 ≤ κ0 := by linarith [aEnt_nonneg d L]
  have hmin : min κh κ' = κ' := min_eq_right hκh
  refine (stepRates_no_closure (A := hatA d L) (F := c1 d L) (c := c1 d L)
    (κH := hatKappaH d L (2 * κdec - 1)) (κ' := κ') (κout := κout)
    (two_lt_hatA hd hL) (by linarith [one_le_c1 d L]) h0 (by linarith [one_le_c1 d L]) hκin hdec
    (le_of_eq ?_) (by linarith) (by linarith)).2
  unfold hatKappaH; ring

/-- **T4.**  At `d = L = 3`, for every `m₀`, the numerical fields of `StepActivityBound`
(`hκ0 hKc hεpos hκ' hκ hε`), `ObsMarks`/`InterpMarks` (`hκ0' hκG hκh hκ`, output rate
`κb = min κh κ' - κ0 - 1`), `interaction_expansion_hat_bound` (`hκdec hκ h1 hlog`) and Theorem 4.2
(`theorem42_of_input`, `theorem42_late_of_input`: `3 ≤ κ`, `hκ₁`, `h1`, `hlog`, `0 ≤ κ'`, `hκm`,
`3κ/2 ≤ κ'`) hold jointly, with `κ_H` equal to the landed conversion
`hatKappaH 3 3 (2 κdec - 1)`; only the class-to-old-term field `κdec - 1 ≤ κin` fails
(`κin < κdec - 1`), as in T1/T2. -/
theorem stepRates_trace_witness (m₀ : ℕ) :
    ∃ κ0 Kc κ' κH κG κh κdet κin κdec κtr κtr' κAE εH : ℝ,
      aEnt 3 3 + 1 ≤ κ0 ∧ K0 3 3 κ0 + 1 ≤ Kc ∧ 0 < εH ∧ 0 ≤ κ' ∧ κ0 ≤ κ' ∧
      κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ κH ∧
      εH ≤ 1 / (8 * Kc ^ 3 * c1 3 3 *
        Real.exp ((κH - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) ∧
      κH ≤ κG ∧ κ0 ≤ κh ∧ κ' ≤ κh ∧ κ' ≤ κdet ∧ hatKappaH 3 3 (2 * κdec - 1) = κH ∧
      3 * κ0 + 3 ≤ κdec ∧ κin < κdec - 1 ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κAE ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κtr ≤ κAE ∧
      1 ≤ (κAE / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κAE / 2 - 1) / 2 ∧
      3 ≤ κtr ∧ 0 ≤ κtr' ∧ aMulti 3 3 + 2 ≤ 2 * κtr - κtr' ∧ 3 * κtr / 2 ≤ κtr' := by
  have hA2 : 2 < hatA 3 3 := two_lt_hatA le_rfl le_rfl
  have hA0 : 0 < hatA 3 3 := by linarith
  have hc1 : 1 ≤ c1 3 3 := one_le_c1 3 3
  have hent : 0 ≤ aEnt 3 3 := aEnt_nonneg 3 3
  obtain ⟨κ0, h0⟩ : ∃ x : ℝ, x = aEnt 3 3 + 1 + c1 3 3 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ x : ℝ, x = max (max (3 * κ0 + 3) (2 * aMulti 3 3 + 4))
    (7 + 8 * κ0 + 2 * c1 3 3) := ⟨_, rfl⟩
  have hM1 : 3 * κ0 + 3 ≤ M := hM ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : 2 * aMulti 3 3 + 4 ≤ M := hM ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  obtain ⟨κin, hin⟩ : ∃ x : ℝ, x = M + 10 := ⟨_, rfl⟩
  obtain ⟨κ', hk'⟩ : ∃ x : ℝ, x = 3 / 2 * κin + κ0 + 1 := ⟨_, rfl⟩
  obtain ⟨κH, hkH⟩ : ∃ x : ℝ, x = κ' + (3 * κ0 + c1 3 3 + 3 / 2) := ⟨_, rfl⟩
  obtain ⟨κdec, hdec⟩ : ∃ x : ℝ, x = 1 / 2 + hatA 3 3 / 2 * (κH + c1 3 3) := ⟨_, rfl⟩
  obtain ⟨κtr, htr⟩ : ∃ x : ℝ, x = max 3 (2 * aMulti 3 3 + 4) := ⟨_, rfl⟩
  have hκtr3 : 3 ≤ κtr := htr ▸ le_max_left _ _
  have hκtr2 : 2 * aMulti 3 3 + 4 ≤ κtr := htr ▸ le_max_right _ _
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨κAE, hAE⟩ : ∃ x : ℝ, x = 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) *
    (κdec + κtr) + 6 + 4 * |Real.log X| := ⟨_, rfl⟩
  have hκ0pos : 0 ≤ κ0 := by linarith
  have hκin0 : 1 < κin := by linarith
  have hκ'0 : 0 < κ' := by linarith
  have hκH0 : 0 < κH := by linarith
  have hκHc : 3 / 2 * κin ≤ κH + c1 3 3 := by linarith
  have hκdec1 : κH + c1 3 3 ≤ hatA 3 3 / 2 * (κH + c1 3 3) := by nlinarith
  have hκdec0 : 0 ≤ κdec := by linarith
  have hlogX := le_abs_self (Real.log X)
  have habs := abs_nonneg (Real.log X)
  have hcoef : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hcd := mul_le_mul_of_nonneg_left (show κdec ≤ κdec + κtr by linarith) hcoef
  have hct := mul_le_mul_of_nonneg_left (show κtr ≤ κdec + κtr by linarith) hcoef
  have hKc : 0 ≤ K0 3 3 κ0 + 1 := by
    have : 0 ≤ K0 3 3 κ0 := by
      unfold K0
      apply div_nonneg (Real.exp_pos _).le
      have : Real.exp (-1) < 1 := by simp
      linarith
    linarith
  have hpos : 0 < 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
      Real.exp ((κH - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) := by
    have : 0 < K0 3 3 κ0 + 1 := by
      have : 0 ≤ K0 3 3 κ0 := by
        unfold K0
        apply div_nonneg (Real.exp_pos _).le
        have : Real.exp (-1) < 1 := by simp
        linarith
      linarith
    have : 0 < c1 3 3 := by linarith
    positivity
  have hconv : hatKappaH 3 3 (2 * κdec - 1) = κH := by
    unfold hatKappaH
    have : (2 * κdec - 1) / hatA 3 3 = κH + c1 3 3 := by
      rw [div_eq_iff hA0.ne']; rw [hdec]; ring
    rw [this]; ring
  exact ⟨κ0, K0 3 3 κ0 + 1, κ', κH, κH, κ', κ', κin, κdec, κtr, 3 * κtr / 2, κAE,
    1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
      Real.exp ((κH - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)),
    by linarith, le_rfl, hpos, by linarith, by linarith, by linarith, le_rfl, le_rfl,
    by linarith, le_rfl, le_rfl, hconv, by linarith, by nlinarith, by linarith, by linarith,
    by linarith, by rw [← hX]; linarith, hκtr3, by linarith, by linarith, le_rfl⟩

end Balaban.Fluctuation
