/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRatesDirect
public import Balaban.Fluctuation.StepActivityDirectPhysical
public import Balaban.Fluctuation.StepObjects
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arithmetic of the smallness `(DA)` and of the rate relation of the direct activity bound

The direct activity bound `stepActivityBound_zeroClass_direct` needs
`R_σ ε_U ≤ [8 K_c'^3 c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G)]⁻¹` (`hDA`) and the rate
relation `κ' + 3κ₀ + c₁ + 3/2 ≤ 2κ_dec - 1` (`hκa`).  This file proves the arithmetic only.

**`C_*` is a parameter here.**  The estimate that the physical amplitude has the form
`ε_U = C_* (log β_k)^q / √β_k` with a constant `C_*` independent of the scale is NOT proved in this
file (see `notes/phase1/PHYSCUBIC.md`, `notes/phase1/DAPHYS.md`).

Contents.
* `H q = q! 4^q` and `t^q e^{-t/4} ≤ H q` for `t ≥ 0`; hence `(log β)^q/√β ≤ H q β^{-1/4}`
  for `β ≥ 1`.
* `daThreshold C T q = max e ((C H q / T)^4)`: for `β` at least this, `C (log β)^q/√β ≤ T`.
* `daT`: the largest `ε_U` allowed by `hDA` for a given `R_σ`; `hDA` is equivalent to `ε_U ≤ daT`.
* `da_numerics_witness`: at `d = L = 3` with the rates of `stepRates_direct_witness`, the threshold
  `daThreshold C (daT …) q` depends only on `C_*`, `q`, `R_σ` and the rate constants (which depend
  only on `d`, `L`); above it `hκa` and `hDA` hold.
* `da_numerics_betaU`: uniformity in the scale, `β_k ≥ β` for `d ≥ 2`.
* `c1_three`, `cG_three`: `c₁(3,3) = 3375`, `c_G(3,3) = 18`.
-/

@[expose] public section

namespace Balaban.Fluctuation

/-- The constant `H q = q! 4^q` bounding `t^q e^{-t/4}` for `t ≥ 0`. -/
noncomputable def H (q : ℕ) : ℝ := (q.factorial : ℝ) * 4 ^ q

theorem H_pos (q : ℕ) : 0 < H q := by unfold H; positivity

/-- For `t ≥ 0`, `t^q e^{-t/4} ≤ q! 4^q`. -/
theorem pow_mul_exp_neg_le (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ q * Real.exp (-t / 4) ≤ H q := by
  have h := Real.pow_div_factorial_le_exp (t / 4) (by positivity) q
  have hf : (0 : ℝ) < q.factorial := by positivity
  rw [div_le_iff₀ hf, div_pow] at h
  have h4 : (0 : ℝ) < 4 ^ q := by positivity
  have he : Real.exp (-t / 4) * Real.exp (t / 4) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hp : t ^ q ≤ Real.exp (t / 4) * q.factorial * 4 ^ q := by
    have := mul_le_mul_of_nonneg_right h h4.le
    rw [div_mul_cancel₀ _ h4.ne'] at this
    linarith
  calc t ^ q * Real.exp (-t / 4)
      ≤ (Real.exp (t / 4) * q.factorial * 4 ^ q) * Real.exp (-t / 4) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = H q := by unfold H; rw [← mul_one ((q.factorial : ℝ) * 4 ^ q), ← he]; ring

/-- For `β ≥ 1`, `(log β)^q / √β ≤ H q β^{-1/4}`. -/
theorem log_pow_div_sqrt_le {q : ℕ} {β : ℝ} (hβ : 1 ≤ β) :
    (Real.log β) ^ q / Real.sqrt β ≤ H q * β ^ (-(1 / 4 : ℝ)) := by
  have hβ0 : 0 < β := by linarith
  have ht : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hs : Real.sqrt β = Real.exp (Real.log β / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hβ0]; ring_nf
  have hr : β ^ (-(1 / 4 : ℝ)) = Real.exp (-Real.log β / 4) := by
    rw [Real.rpow_def_of_pos hβ0]; ring_nf
  rw [hs, hr, div_eq_mul_inv, ← Real.exp_neg]
  have h := pow_mul_exp_neg_le q ht
  have e : Real.exp (-(Real.log β / 2)) = Real.exp (-Real.log β / 4) * Real.exp (-Real.log β / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  calc _ ≤ H q * Real.exp (-Real.log β / 4) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := rfl

/-- The threshold `β₀ = max {e, (C H_q / T)^4}`. -/
noncomputable def daThreshold (Cstar T : ℝ) (q : ℕ) : ℝ :=
  max (Real.exp 1) ((Cstar * H q / T) ^ 4)

theorem one_le_daThreshold (Cstar T : ℝ) (q : ℕ) : 1 ≤ daThreshold Cstar T q := by
  unfold daThreshold
  exact le_trans (Real.one_le_exp (by norm_num)) (le_max_left _ _)

/-- **The amplitude bound.**  For `β ≥ daThreshold C T q`, `C (log β)^q / √β ≤ T`. -/
theorem amplitude_le {Cstar T : ℝ} (hC : 0 < Cstar) (hT : 0 < T) (q : ℕ) {β : ℝ}
    (hβ : daThreshold Cstar T q ≤ β) :
    Cstar * (Real.log β) ^ q / Real.sqrt β ≤ T := by
  have h1 : 1 ≤ β := le_trans (one_le_daThreshold Cstar T q) hβ
  have hβ0 : 0 < β := by linarith
  have hx : (Cstar * H q / T) ^ 4 ≤ β := le_trans (le_max_right _ _) hβ
  set x := Cstar * H q / T with hxdef
  have hx0 : 0 < x := by have := H_pos q; positivity
  set u := β ^ (1 / 4 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hβ0 _
  have hu4 : u ^ 4 = β := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]; norm_num
  have hxu : x ≤ u := by
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_pow_left₀ hlt hu0.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hu4] at this; linarith
  have hneg : β ^ (-(1 / 4 : ℝ)) = u⁻¹ := by rw [Real.rpow_neg hβ0.le]
  have h := log_pow_div_sqrt_le (q := q) h1
  rw [hneg] at h
  have hCx : Cstar * H q ≤ T * u := by
    have : x * T = Cstar * H q := by rw [hxdef]; field_simp
    nlinarith
  calc Cstar * (Real.log β) ^ q / Real.sqrt β
      = Cstar * ((Real.log β) ^ q / Real.sqrt β) := by ring
    _ ≤ Cstar * (H q * u⁻¹) := mul_le_mul_of_nonneg_left h hC.le
    _ = (Cstar * H q) * u⁻¹ := by ring
    _ ≤ (T * u) * u⁻¹ := mul_le_mul_of_nonneg_right hCx (inv_pos.2 hu0).le
    _ = T := by field_simp


/-- The largest amplitude allowed by `hDA` for the prefactor `R_σ`. -/
noncomputable def daT (d L : ℕ) (Rσ Kc' κdec κ0 κ' : ℝ) : ℝ :=
  (8 * Rσ * Kc' ^ 3 * c1 d L *
    Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))⁻¹

theorem daT_pos (d L : ℕ) [NeZero L] {Rσ Kc' : ℝ} (hR : 0 < Rσ) (hK : 0 < Kc')
    (κdec κ0 κ' : ℝ) : 0 < daT d L Rσ Kc' κdec κ0 κ' := by
  unfold daT
  have := one_le_c1 d L
  have : 0 < c1 d L := by linarith
  positivity

/-- `hDA` is equivalent to `ε_U ≤ daT`. -/
theorem hDA_iff (d L : ℕ) [NeZero L] {Rσ Kc' : ℝ} (hR : 0 < Rσ) (hK : 0 < Kc')
    (κdec κ0 κ' εU : ℝ) :
    Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) ↔
    εU ≤ daT d L Rσ Kc' κdec κ0 κ' := by
  have h1 := one_le_c1 d L
  have hc : 0 < c1 d L := by linarith
  have hD : 0 < 8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L) := by positivity
  have hD' : 0 < 8 * Rσ * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L) := by positivity
  unfold daT
  rw [le_div_iff₀ hD, ← one_div, le_div_iff₀ hD']
  constructor <;> intro h <;> nlinarith [h]

/-- **`hDA` from the threshold.**  For `β_k ≥ daThreshold C (daT …) q` and
`ε_U = C (log β_k)^q / √β_k`, the smallness `hDA` holds. -/
theorem hDA_of_threshold (d L : ℕ) [NeZero L] {Rσ Kc' Cstar : ℝ} (hR : 0 < Rσ) (hK : 0 < Kc')
    (hC : 0 < Cstar) (q : ℕ) (κdec κ0 κ' : ℝ) {βk : ℝ}
    (hβ : daThreshold Cstar (daT d L Rσ Kc' κdec κ0 κ') q ≤ βk) :
    Rσ * (Cstar * (Real.log βk) ^ q / Real.sqrt βk) ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) :=
  (hDA_iff d L hR hK κdec κ0 κ' _).2
    (amplitude_le hC (daT_pos d L hR hK κdec κ0 κ') q hβ)

theorem K0_pos (d L : ℕ) (κ : ℝ) : 0 < K0 d L κ := by
  unfold K0
  have : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have : 0 < 1 - Real.exp (-1) := by linarith
  positivity

/-- **The arithmetic of `(DA)` at `d = L = 3`.**  With the rates `κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1` and `K_c' = K₀ + 1` (all depending only
on `d = L = 3`), the rate relation `hκa` holds, the output rate `(3/2) κ_dec` is at least
`κ_dec`, and for every `β_k ≥ β₀ = daThreshold C (daT …) q` the smallness `hDA` holds with
`ε_U = C (log β_k)^q / √β_k`.  Here `C_*` is a free positive parameter. -/
theorem da_numerics_witness {Cstar Rσ : ℝ} (hC : 0 < Cstar) (hR : 0 < Rσ) (q : ℕ) :
    ∃ κ0 κdec κ' Kc' : ℝ, κ0 = aEnt 3 3 + 1 ∧ κdec = 100 * (κ0 + c1 3 3 + 10) ∧
      κ' = 3 / 2 * κdec + κ0 + 1 ∧ Kc' = K0 3 3 κ0 + 1 ∧ 0 < Kc' ∧ 0 ≤ κ0 ∧
      κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧ κdec ≤ 3 / 2 * κdec ∧
      ∀ βk : ℝ, daThreshold Cstar (daT 3 3 Rσ Kc' κdec κ0 κ') q ≤ βk →
        Rσ * (Cstar * (Real.log βk) ^ q / Real.sqrt βk) ≤ 1 / (8 * Kc' ^ 3 * c1 3 3 *
          Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) := by
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  have hK := K0_pos 3 3 (aEnt 3 3 + 1)
  refine ⟨aEnt 3 3 + 1, 100 * ((aEnt 3 3 + 1) + c1 3 3 + 10),
    3 / 2 * (100 * ((aEnt 3 3 + 1) + c1 3 3 + 10)) + (aEnt 3 3 + 1) + 1,
    K0 3 3 (aEnt 3 3 + 1) + 1, rfl, rfl, rfl, rfl, by linarith, by linarith, by linarith,
    by linarith, fun βk hβ => ?_⟩
  exact hDA_of_threshold 3 3 hR (by linarith) hC q _ _ _ hβ

/-- Uniformity in the scale: for `d ≥ 2` and `β > 0`, `β_k ≥ β`. -/
theorem le_betaU {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (hd : 2 ≤ d) (hβ : 0 < S.β) : S.β ≤ S.betaU := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hx : (1 : ℝ) ≤ (L : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hL)
  have hx0 : (0 : ℝ) < (L : ℝ) ^ k := by linarith
  unfold StepSetting.betaU
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  have h1 : 1 ≤ (((L : ℝ) ^ k) ^ e) := one_le_pow₀ hx
  have hx2 : 0 < ((L : ℝ) ^ k) ^ 2 := by positivity
  have : S.β * ((L : ℝ) ^ k) ^ (2 + e) / ((L : ℝ) ^ k) ^ 2 = S.β * ((L : ℝ) ^ k) ^ e := by
    rw [pow_add]; field_simp
  rw [this]
  nlinarith

/-- **Uniform in the scale.**  If `β ≥ daThreshold C (daT …) q` then `hDA` holds at every scale `k`
with `ε_U = C (log β_k)^q / √β_k`, `β_k = S.betaU`. -/
theorem hDA_of_betaU {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (hd : 2 ≤ d) (hβ : 0 < S.β)
    {Rσ Kc' Cstar : ℝ} (hR : 0 < Rσ) (hK : 0 < Kc') (hC : 0 < Cstar) (q : ℕ)
    (κdec κ0 κ' : ℝ)
    (hβ0 : daThreshold Cstar (daT d L Rσ Kc' κdec κ0 κ') q ≤ S.β) :
    Rσ * (Cstar * (Real.log S.betaU) ^ q / Real.sqrt S.betaU) ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) :=
  hDA_of_threshold d L hR hK hC q κdec κ0 κ' (le_trans hβ0 (le_betaU S hd hβ))

/-- `c₁(3,3) = 3375`. -/
theorem c1_three : c1 3 3 = 3375 := by unfold c1; norm_num

/-- `c_G(3,3) = 18`. -/
theorem cG_three : cG 3 3 = 18 := by unfold cG; norm_num

/-- The logarithm of the threshold: `log β₀ = max 1 (4 (log C + log H_q - log T))`. -/
theorem log_daThreshold {Cstar T : ℝ} (hC : 0 < Cstar) (hT : 0 < T) (q : ℕ) :
    Real.log (daThreshold Cstar T q) =
      max 1 (4 * (Real.log Cstar + Real.log (H q) - Real.log T)) := by
  have hH := H_pos q
  have hx : 0 < (Cstar * H q / T) ^ 4 := by positivity
  have hl : Real.log ((Cstar * H q / T) ^ 4) =
      4 * (Real.log Cstar + Real.log (H q) - Real.log T) := by
    rw [Real.log_pow, Real.log_div (by positivity) hT.ne', Real.log_mul hC.ne' hH.ne']
    push_cast; ring
  unfold daThreshold
  rcases le_total (Real.exp 1) ((Cstar * H q / T) ^ 4) with h | h
  · rw [max_eq_right h, hl]
    have := Real.log_le_log (Real.exp_pos 1) h
    rw [Real.log_exp, hl] at this
    rw [max_eq_right this]
  · rw [max_eq_left h, Real.log_exp]
    have := Real.log_le_log hx h
    rw [Real.log_exp, hl] at this
    rw [max_eq_left this]


/-- Crude size of the entropy exponent: `a_Ent(3,3) ≤ 300000`. -/
theorem aEnt_three_le : aEnt 3 3 ≤ 300000 := by
  have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl : ∀ x : ℝ, 0 < x → Real.log x ≤ x := fun x hx =>
    le_trans (Real.log_le_sub_one_of_pos hx) (by linarith)
  have e : entQ 3 3 = 125 * (1458 * 2 ^ 3500) ^ 54 := by
    unfold entQ; norm_num
  unfold aEnt
  rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have a := hl 125 (by norm_num)
  have b := hl 1458 (by norm_num)
  push_cast
  nlinarith

/-- Size of the exponent `E_D = (2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G` for the witness rates at
`d = L = 3`: `E_D ≤ 3 · 10^9`. -/
theorem E_D_three_le :
    (2 * (100 * ((aEnt 3 3 + 1) + c1 3 3 + 10)) - 1 - 2 * (aEnt 3 3 + 1)) * cG 3 3 + c1 3 3 +
      (3 / 2 * (100 * ((aEnt 3 3 + 1) + c1 3 3 + 10)) + (aEnt 3 3 + 1) + 1) * cG 3 3
      ≤ 3000000000 := by
  have := aEnt_three_le
  have := aEnt_nonneg 3 3
  rw [c1_three, cG_three]
  nlinarith

end Balaban.Fluctuation
