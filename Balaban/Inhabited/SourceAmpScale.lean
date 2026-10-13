/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTower
public import Balaban.Fluctuation.DARateNumerics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The amplitude of the step at a physical source, at every scale

For the zero class at the source `0` the landed amplitude is `β_k P / r³ + K/(β r)`
(`LevelStep.scale_amp_exists`): the source allowance `K/(β r)` comes from the auxiliary slice
`η = β⁻²` of the assembler.  At a physical source `g` with `∑ |g| < q ≤ 1` the assembler is used at
the source `g/β` on the slice `η = q/β` (`sourceSlice_mem_restricted`), and the source allowance is
`q K / r`, with no factor `1/β`.  This file bounds that amplitude with thresholds chosen before the
scale.  Write `b = β_k = β · 3^k`, `w = (log b)^p`, `κ₁ = lvKappa κ t`, `r = lvR κ t b p₁`.

* `LevelStep.sourceAmp_le`: the elementary estimate.  For `x = √b ≥ 1`, `w ≥ 1` and a radius `r`
  with `κ₁ x ≤ 4 A w r`: `x² (P / r³) + q K / r ≤ P (4A/κ₁)³ w³/x + q (4 A K/κ₁) w/x`.
* `LevelStep.sourceAmp_scale`: there is `β₁ ≥ e` (depending on `A₁, p, κ, t` only) such that for
  `b ≥ β₁`, every cutoff `0 < p₁ ≤ A₁ (log b)^p` and every `q ≥ 0`:
  `b (P / r³) + q K / r ≤ P (4A₁/κ₁)³ (log b)^{3p}/√b + q (4 A₁ K/κ₁) (log b)^p/√b`.
* `LevelStep.sourceAmp_scale_four`: the same for the prefactor `ε_H = 4 ε_U` of the source
  assembler (`R_σ = 2`, two expansions), with the constants
  `C_E = 4 (P (4A₁/κ₁)³ + 1)` (`srcCE`) and `C_F = 16 A₁ K/κ₁` (`srcCF`):
  `4 ε_U ≤ C_E (log b)^{3p}/√b + q C_F (log b)^p/√b`.
* `LevelStep.sourceAmp_doubled_hDA`: the smallness hypothesis of the source assembler
  (`stepActivityBound_zeroClass_source_of_directTerms`, with `R_σ = 2` and the entropy constant
  `2 K_c'`): for `q ≤ 1`, `log b ≥ 1` and
  `b ≥ daThreshold ((C_E + C_F)/4) (daT d L 4 (2 K_c') κ_dec κ₀ κ') (3p)`,
  `2 (2 ε_U) ≤ 1 / (8 (2K_c')³ c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G))`.

No constant depends on the scale `k`, the torus, the mass, `β`, the source or `q ≤ 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization

namespace LevelStep

/-- **The elementary estimate of the amplitude at a physical source.**  For `x = √β_k ≥ 1`,
`w = (log β_k)^p ≥ 1`, a radius `r` with `κ₁ x ≤ 4 A w r` and `q ≥ 0`:
`x² (P / r³) + q K / r ≤ P (4A/κ₁)³ w³ / x + q (4 A K / κ₁) w / x`. -/
theorem sourceAmp_le {x w r P K A κ₁ q : ℝ} (hx : 1 ≤ x) (hw : 1 ≤ w) (hA : 0 < A) (hκ : 0 < κ₁)
    (hP : 0 ≤ P) (hK : 0 ≤ K) (hq : 0 ≤ q) (hr : κ₁ * x ≤ 4 * A * w * r) :
    x ^ 2 * (P / r ^ 3) + q * K / r ≤
      P * (4 * A / κ₁) ^ 3 * w ^ 3 / x + q * (4 * A * K / κ₁) * w / x := by
  have hx0 : 0 < x := by linarith
  have hw0 : 0 < w := by linarith
  set ρ0 : ℝ := κ₁ * x / (4 * A * w) with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  have hrρ : ρ0 ≤ r := by
    rw [hρ0, div_le_iff₀ (by positivity)]; linarith
  have h1 : x ^ 2 * (P / r ^ 3) ≤ x ^ 2 * (P / ρ0 ^ 3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact div_le_div_of_nonneg_left hP (by positivity) (pow_le_pow_left₀ hρ0pos.le hrρ 3)
  have h2 : q * K / r ≤ q * K / ρ0 :=
    div_le_div_of_nonneg_left (mul_nonneg hq hK) hρ0pos hrρ
  have e1 : x ^ 2 * (P / ρ0 ^ 3) = P * (4 * A / κ₁) ^ 3 * w ^ 3 / x := by
    rw [hρ0]; field_simp
  have e2 : q * K / ρ0 = q * (4 * A * K / κ₁) * w / x := by
    rw [hρ0]; field_simp
  rw [← e1, ← e2]
  exact add_le_add h1 h2

/-- **The amplitude at a physical source, at every scale.**  For `A₁ > 0` there is `β₁ ≥ e`
(depending on `A₁, p, κ, t` only) such that for `b = β_k ≥ β₁`, every cutoff
`0 < p₁ ≤ A₁ (log b)^p` and every `q ≥ 0` the radius `r = lvR κ t b p₁` is positive and
`b (P / r³) + q K / r ≤ P (4A₁/κ₁)³ (log b)^{3p}/√b + q (4 A₁ K/κ₁) (log b)^p/√b`,
`κ₁ = lvKappa κ t`. -/
theorem sourceAmp_scale {A₁ κ t : ℝ} (hA : 0 < A₁) (p : ℕ) (ht : 0 < t) :
    ∃ β₁ : ℝ, Real.exp 1 ≤ β₁ ∧ ∀ b : ℝ, β₁ ≤ b → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p b →
      0 < lvR κ t b p₁ ∧ ∀ P K q : ℝ, 0 ≤ P → 0 ≤ K → 0 ≤ q →
        b * (P / (lvR κ t b p₁) ^ 3) + q * K / lvR κ t b p₁ ≤
          P * (4 * A₁ / lvKappa κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
          q * (4 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b := by
  set κ₁ : ℝ := lvKappa κ t with hκ₁def
  have hκ₁ : 0 < κ₁ := lvKappa_pos κ ht
  have hthr : 0 < κ₁ / 16 := by positivity
  refine ⟨max (Real.exp 1) (pLogThreshold A₁ p (κ₁ / 16)), le_max_left _ _, ?_⟩
  intro b hb p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ b := le_trans (le_max_left _ _) hb
  have hbp : pLogThreshold A₁ p (κ₁ / 16) ≤ b := le_trans (le_max_right _ _) hb
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hexp
  have hb0 : 0 < b := by linarith
  have hℓ : 1 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 hexp
  have hx1 : 1 ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  have hw1 : 1 ≤ (Real.log b) ^ p := one_le_pow₀ hℓ
  have hpL : pLog A₁ p b = A₁ * (Real.log b) ^ p := rfl
  have hp16 : pLog A₁ p b ≤ κ₁ / 16 * Real.sqrt b := pLog_le_mul_sqrt hA.le p hthr hb1 hbp
  have hcψeq : lvCpsi κ t b = κ₁ * Real.sqrt b := lvCpsi_eq κ t b
  have hc16 : 16 * p₁ ≤ lvCpsi κ t b := by rw [hcψeq]; linarith
  have e : 4 * p₁ * lvR κ t b p₁ = 2 * lvCpsi κ t b - 16 * p₁ := by
    unfold lvR; field_simp; ring
  have hcψ0 : 0 < lvCpsi κ t b := by rw [hcψeq]; positivity
  have hr0 : 0 < lvR κ t b p₁ := by
    by_contra h
    have h := not_lt.1 h
    have : 4 * p₁ * lvR κ t b p₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hrbound : κ₁ * Real.sqrt b ≤ 4 * A₁ * (Real.log b) ^ p * lvR κ t b p₁ := by
    calc κ₁ * Real.sqrt b = lvCpsi κ t b := hcψeq.symm
      _ ≤ 2 * lvCpsi κ t b - 16 * p₁ := by linarith
      _ = 4 * p₁ * lvR κ t b p₁ := e.symm
      _ ≤ 4 * pLog A₁ p b * lvR κ t b p₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
      _ = _ := by rw [hpL]; ring
  refine ⟨hr0, fun P K q hP hK hq => ?_⟩
  have hamp := sourceAmp_le (x := Real.sqrt b) (w := (Real.log b) ^ p)
    (r := lvR κ t b p₁) (P := P) (K := K) (A := A₁) (κ₁ := κ₁) (q := q) hx1 hw1 hA hκ₁
    hP hK hq hrbound
  rwa [Real.sq_sqrt hb0.le, ← pow_mul, show p * 3 = 3 * p by ring] at hamp

/-- The constant `C_E = 4 (P (4A₁/κ₁)³ + 1)` of the potential part of the prefactor
(`κ₁ = lvKappa κ t`). -/
noncomputable def srcCE (A₁ κ t P : ℝ) : ℝ := 4 * (P * (4 * A₁ / lvKappa κ t) ^ 3 + 1)

/-- The constant `C_F = 16 A₁ K / κ₁` of the source part of the prefactor (`κ₁ = lvKappa κ t`). -/
noncomputable def srcCF (A₁ κ t K : ℝ) : ℝ := 16 * A₁ * K / lvKappa κ t

theorem srcCE_pos {A₁ κ t P : ℝ} (hA : 0 < A₁) (ht : 0 < t) (hP : 0 ≤ P) : 0 < srcCE A₁ κ t P := by
  have := lvKappa_pos κ ht
  unfold srcCE
  positivity

theorem srcCF_nonneg {A₁ κ t K : ℝ} (hA : 0 < A₁) (ht : 0 < t) (hK : 0 ≤ K) :
    0 ≤ srcCF A₁ κ t K := by
  have := lvKappa_pos κ ht
  unfold srcCF
  positivity

theorem srcCF_pos {A₁ κ t K : ℝ} (hA : 0 < A₁) (ht : 0 < t) (hK : 0 < K) :
    0 < srcCF A₁ κ t K := by
  have := lvKappa_pos κ ht
  unfold srcCF
  positivity

/-- **The prefactor `4 ε_U` of the source assembler.**  If
`ε_U ≤ P (4A₁/κ₁)³ w³/√b + q (4 A₁ K/κ₁) w/√b` (`w³ = (log b)^{3p}`, `w = (log b)^p`,
`log b ≥ 0`, `b > 0`), then `4 ε_U ≤ C_E w³/√b + q C_F w/√b` with `C_E = srcCE`, `C_F = srcCF`. -/
theorem sourceAmp_scale_four {A₁ κ t P K q b ε : ℝ} (p : ℕ) (hb : 0 < b)
    (hℓ : 0 ≤ Real.log b)
    (hε : ε ≤ P * (4 * A₁ / lvKappa κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
      q * (4 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b) :
    4 * ε ≤ srcCE A₁ κ t P * (Real.log b) ^ (3 * p) / Real.sqrt b +
      q * srcCF A₁ κ t K * (Real.log b) ^ p / Real.sqrt b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have h0 : 0 ≤ (Real.log b) ^ (3 * p) / Real.sqrt b := by positivity
  unfold srcCE srcCF
  calc 4 * ε ≤ 4 * (P * (4 * A₁ / lvKappa κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
        q * (4 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b) := by linarith
    _ = 4 * (P * (4 * A₁ / lvKappa κ t) ^ 3) * ((Real.log b) ^ (3 * p) / Real.sqrt b) +
        q * (16 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b := by ring
    _ ≤ 4 * (P * (4 * A₁ / lvKappa κ t) ^ 3 + 1) * ((Real.log b) ^ (3 * p) / Real.sqrt b) +
        q * (16 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b := by nlinarith
    _ = _ := by ring

/-- **The smallness hypothesis of the source assembler at the physical amplitude.**  Let
`q ≤ 1`, `log b ≥ 1`, and
`ε_U ≤ P (4A₁/κ₁)³ (log b)^{3p}/√b + q (4 A₁ K/κ₁) (log b)^p/√b`.  If
`b ≥ daThreshold ((C_E + C_F)/4) (daT d L 4 (2K_c') κ_dec κ₀ κ') (3p)`, then
`2 (2 ε_U) ≤ 1 / (8 (2K_c')³ c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G))`: the hypothesis `hDA`
of `stepActivityBound_zeroClass_source_of_directTerms` with `R_σ = 2`. -/
theorem sourceAmp_doubled_hDA (d L : ℕ) [NeZero L] {A₁ κ t P K q b ε Kc' : ℝ} (p : ℕ)
    (hA : 0 < A₁) (ht : 0 < t) (hP : 0 ≤ P) (hK : 0 ≤ K) (hq1 : q ≤ 1)
    (hℓ : 1 ≤ Real.log b) (hb : 0 < b) (hKc : 0 < Kc') (κdec κ0 κ' : ℝ)
    (hthr : daThreshold ((srcCE A₁ κ t P + srcCF A₁ κ t K) / 4)
      (daT d L 4 (2 * Kc') κdec κ0 κ') (3 * p) ≤ b)
    (hε : ε ≤ P * (4 * A₁ / lvKappa κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
      q * (4 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b) :
    2 * (2 * ε) ≤ 1 / (8 * (2 * Kc') ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) := by
  have hκ₁ := lvKappa_pos κ ht
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hℓ0 : 0 ≤ Real.log b := by linarith
  have hCE := srcCE_pos (κ := κ) hA ht hP
  have hCF := srcCF_nonneg (κ := κ) hA ht hK
  have hw : (Real.log b) ^ p ≤ (Real.log b) ^ (3 * p) :=
    pow_le_pow_right₀ hℓ (by omega)
  have hw0 : 0 ≤ (Real.log b) ^ p := by positivity
  have h4 := sourceAmp_scale_four (A₁ := A₁) (κ := κ) (t := t) (P := P) (K := K) (q := q) p hb
    hℓ0 hε
  have hqw : q * srcCF A₁ κ t K * (Real.log b) ^ p / Real.sqrt b ≤
      srcCF A₁ κ t K * (Real.log b) ^ (3 * p) / Real.sqrt b := by
    refine div_le_div_of_nonneg_right ?_ hs.le
    calc q * srcCF A₁ κ t K * (Real.log b) ^ p ≤ 1 * srcCF A₁ κ t K * (Real.log b) ^ p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq1 hCF) hw0
      _ = srcCF A₁ κ t K * (Real.log b) ^ p := by ring
      _ ≤ srcCF A₁ κ t K * (Real.log b) ^ (3 * p) := mul_le_mul_of_nonneg_left hw hCF
  have hamp := amplitude_le (Cstar := (srcCE A₁ κ t P + srcCF A₁ κ t K) / 4)
    (by positivity) (daT_pos d L (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc')
      κdec κ0 κ') (3 * p) hthr
  have hε' : ε ≤ daT d L 4 (2 * Kc') κdec κ0 κ' := by
    refine le_trans ?_ hamp
    have e : (srcCE A₁ κ t P + srcCF A₁ κ t K) / 4 * (Real.log b) ^ (3 * p) / Real.sqrt b =
        (srcCE A₁ κ t P * (Real.log b) ^ (3 * p) / Real.sqrt b +
          srcCF A₁ κ t K * (Real.log b) ^ (3 * p) / Real.sqrt b) / 4 := by ring
    rw [e]
    linarith
  have h := (hDA_iff d L (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc') κdec κ0 κ'
    ε).2 hε'
  linarith

end LevelStep

end Balaban.Inhabited
