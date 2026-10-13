/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceAmpScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The amplitude threshold at a general source radius

`LevelStep.sourceAmp_doubled_hDA_rho` is `sourceAmp_doubled_hDA` for sources of size `q ≤ ρ`
(`ρ ≥ 0`): the threshold is `daThreshold ((C_E + ρ C_F)/4)`.  The landed statement
(`q ≤ 1`, threshold `(C_E + C_F)/4`) is the case `ρ = 1` (`sourceAmp_doubled_hDA_of_rho`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization

namespace LevelStep

/-- **The smallness hypothesis of the source assembler at radius `ρ`.**  As
`sourceAmp_doubled_hDA`, for `q ≤ ρ` and the threshold `((C_E + ρ C_F)/4)`. -/
theorem sourceAmp_doubled_hDA_rho (d L : ℕ) [NeZero L] {A₁ κ t P K q ρ b ε Kc' : ℝ} (p : ℕ)
    (hA : 0 < A₁) (ht : 0 < t) (hP : 0 ≤ P) (hK : 0 ≤ K) (hρ : 0 ≤ ρ) (hqρ : q ≤ ρ)
    (hℓ : 1 ≤ Real.log b) (hb : 0 < b) (hKc : 0 < Kc') (κdec κ0 κ' : ℝ)
    (hthr : daThreshold ((srcCE A₁ κ t P + ρ * srcCF A₁ κ t K) / 4)
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
      ρ * srcCF A₁ κ t K * (Real.log b) ^ (3 * p) / Real.sqrt b := by
    refine div_le_div_of_nonneg_right ?_ hs.le
    have hρC : 0 ≤ ρ * srcCF A₁ κ t K := mul_nonneg hρ hCF
    calc q * srcCF A₁ κ t K * (Real.log b) ^ p ≤ ρ * srcCF A₁ κ t K * (Real.log b) ^ p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqρ hCF) hw0
      _ ≤ ρ * srcCF A₁ κ t K * (Real.log b) ^ (3 * p) := mul_le_mul_of_nonneg_left hw hρC
  have hamp := amplitude_le (Cstar := (srcCE A₁ κ t P + ρ * srcCF A₁ κ t K) / 4)
    (by positivity) (daT_pos d L (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc')
      κdec κ0 κ') (3 * p) hthr
  have hε' : ε ≤ daT d L 4 (2 * Kc') κdec κ0 κ' := by
    refine le_trans ?_ hamp
    have e : (srcCE A₁ κ t P + ρ * srcCF A₁ κ t K) / 4 * (Real.log b) ^ (3 * p) / Real.sqrt b =
        (srcCE A₁ κ t P * (Real.log b) ^ (3 * p) / Real.sqrt b +
          ρ * srcCF A₁ κ t K * (Real.log b) ^ (3 * p) / Real.sqrt b) / 4 := by ring
    rw [e]
    linarith
  have h := (hDA_iff d L (by norm_num : (0 : ℝ) < 4) (by positivity : 0 < 2 * Kc') κdec κ0 κ'
    ε).2 hε'
  linarith

/-- The landed `sourceAmp_doubled_hDA` is the case `ρ = 1` of `sourceAmp_doubled_hDA_rho`. -/
theorem sourceAmp_doubled_hDA_of_rho (d L : ℕ) [NeZero L] {A₁ κ t P K q b ε Kc' : ℝ} (p : ℕ)
    (hA : 0 < A₁) (ht : 0 < t) (hP : 0 ≤ P) (hK : 0 ≤ K) (hq1 : q ≤ 1)
    (hℓ : 1 ≤ Real.log b) (hb : 0 < b) (hKc : 0 < Kc') (κdec κ0 κ' : ℝ)
    (hthr : daThreshold ((srcCE A₁ κ t P + srcCF A₁ κ t K) / 4)
      (daT d L 4 (2 * Kc') κdec κ0 κ') (3 * p) ≤ b)
    (hε : ε ≤ P * (4 * A₁ / lvKappa κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
      q * (4 * A₁ * K / lvKappa κ t) * (Real.log b) ^ p / Real.sqrt b) :
    2 * (2 * ε) ≤ 1 / (8 * (2 * Kc') ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)) :=
  sourceAmp_doubled_hDA_rho d L (ρ := 1) p hA ht hP hK zero_le_one hq1 hℓ hb hKc κdec κ0 κ'
    (by simpa using hthr) hε

end LevelStep

end Balaban.Inhabited
