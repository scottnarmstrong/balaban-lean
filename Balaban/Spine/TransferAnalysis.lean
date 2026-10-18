/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Analytic.Constants
public import Balaban.LargeField.Counter.LamStar
public import Balaban.LargeField.History.Scale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Numerical facts for the transfer at `k₀` (LFR Lemma IV.2.1, Lemma IV.3.3 (c))

Three facts about the a priori sequence `λ̂_j = log(β a) + 1 + j θ`, `θ = (d-2) log L`, used to
build the hypotheses of the transfer from the class at the switching scale:

* `exists_analyticConsts`: for `H₀ > 0` there are constants `𝖪` with the prescribed
  `d, L, p₀, H₀, c₂` such that (Λ15)–(Λ17′) hold at every `x` above a threshold;
* `setting_good_of_lamHat`: the setting with `λ_j = λ̂_j` satisfies `Setting.Good` once `λ̂_0` is
  above the threshold `λ_*` of the typing;
* `hLam_window`: the horizon conditions (H-λ) of LF-2 (ii) at `k₀ = kZero`, `k̂ = k̂_f`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

/-- The constants `𝖪` of (Λ15)–(Λ17′) of the transfer: `A₀ = 0` makes the three conditions on
`δ̄` trivial, so only `H₀ > 0` and the size of `x` enter. -/
def analyticK (d L p0 : ℕ) (H0 c2 : ℝ) : AnalyticConsts where
  d := d
  L := L
  N := 0
  p0 := p0
  A0 := 0
  H0 := H0
  c2 := c2
  c1BG := 1
  c11 := 1
  C3 := 1
  C4 := 1
  deltaSS := 1
  deltaS := 1

/-- (Λ15)–(Λ17′) for `analyticK` hold at every `x` above an explicit threshold. -/
theorem analyticK_at {d L p0 : ℕ} (hd : 1 ≤ d) (hL : 2 ≤ L) {H0 c2 : ℝ} (hH : 0 < H0) {x : ℝ}
    (hx : max (3 / (1 - (2 : ℝ) ^ (-(1 / (2 * (p0 : ℝ))))))
      (max (c2 + 2) (3 + 2 * (thetaOf d L + 1 + 1 / H0))) ≤ x) :
    AnalyticLamAt (analyticK d L p0 H0 c2) x := by
  have h1 := (le_max_left _ _).trans hx
  have h2 := ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
  have h3 := ((le_max_right _ _).trans ((le_max_right _ _).trans hx))
  have hL1 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hθ : 0 ≤ thetaOf d L := by
    unfold thetaOf
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have hLd : (2 : ℝ) ≤ (L : ℝ) ^ d :=
    calc (2 : ℝ) ≤ L := hL1
      _ = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
  have hd0 : ((L : ℝ) ^ d)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; simpa using hLd
  have hu0 : 0 < ((L : ℝ) ^ d)⁻¹ := by positivity
  set θ1 := thetaOf d L + 1 with hθ1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [analyticK] using h1
  · simp only [analyticK]
    set u := ((L : ℝ) ^ d)⁻¹ with hu
    have hHinv : H0 * (1 / H0) = 1 := by field_simp
    have hθ1p : 1 ≤ θ1 := by rw [hθ1]; linarith
    have hHp : 0 < 1 / H0 := by positivity
    have hx3 : 0 ≤ x - 3 := by linarith
    have hkey : 1 / H0 ≤ (1 - u) * (x - 3) - u * θ1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - u by linarith) hx3,
        mul_nonneg (show 0 ≤ 1 / 2 - u by linarith) (show 0 ≤ θ1 by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hH.le]
  · simp only [analyticK]; linarith
  · simp [analyticK, deltaBar]
  · simp [analyticK, deltaBar]
  · simp [analyticK, deltaBar]

/-- **`Setting.Good` from the typing** (LF-2, Part I §I.5.3): if the typing `T` is `Ok`, with
`θ₋ ≤ θ = (d-2) log L ≤ θ₊`, there is `x₀` such that the setting `λ_j = λ̂_j` is `Good` whenever
`λ̂_0 = log(β a) + 1 ≥ x₀`. -/
theorem exists_good_lamHat (T : Typing) (hT : T.Ok)
    (hθ : T.θm ≤ thetaOf T.d T.L ∧ thetaOf T.d T.L ≤ T.θp) :
    ∃ x₀ : ℝ, ∀ β a : ℝ, x₀ ≤ Real.log (β * a) + 1 →
      (Setting.mk T (lamHat T.d T.L β a)).Good := by
  obtain ⟨x₀, hx₀⟩ := exists_lamStar T hT
  refine ⟨x₀, fun β a hx => ?_⟩
  have hθp : 0 ≤ T.θp := hT.θm_pos.le.trans hT.θm_le_θp
  have hstar : 1 ≤ T.cStar := by
    unfold Typing.cStar
    have h1 : 0 < T.logL := by
      unfold Typing.logL
      exact Real.log_pos (by have := hT.two_le_L; exact_mod_cast this)
    have : 0 ≤ T.θp / (T.α * T.logL) := div_nonneg hθp (mul_pos hT.α_pos h1).le
    linarith
  have hl0 : T.θp ≤ x₀ := by
    have := hx₀.l0_a x₀ le_rfl
    nlinarith
  have hlam0 : (Setting.mk T (lamHat T.d T.L β a)).lam 0 = Real.log (β * a) + 1 := by
    show Real.log (β * a) + 1 + ((0 : ℕ) : ℝ) * thetaOf T.d T.L = _
    simp
  refine ⟨⟨hT, fun j => ?_, ?_, ?_⟩, ?_⟩
  · show T.θm ≤ lamHat T.d T.L β a (j + 1) - lamHat T.d T.L β a j ∧
      lamHat T.d T.L β a (j + 1) - lamHat T.d T.L β a j ≤ T.θp
    have : lamHat T.d T.L β a (j + 1) - lamHat T.d T.L β a j = thetaOf T.d T.L := by
      unfold lamHat; push_cast; ring
    rw [this]; exact hθ
  · rw [hlam0]; linarith [hx₀.one_le]
  · rw [hlam0]; linarith
  · show LamStarConditions T ((Setting.mk T (lamHat T.d T.L β a)).lam 0)
    rw [hlam0]; exact hx₀.mono hx

/-- **(H-λ)** (LFR Lemma IV.3.3 (c); the horizon conditions of LF-2 (ii)): if `log β ≥ 2d`,
`d ≥ 3`, `a > 1`, `d(d-2) log L / 2 ≤ c_H`, and `k̂` is a horizon of `ν` (`ν L^{2k+2} < 1` for
`k < k̂`), then with `k₀ = kZero d L β ν`: `k̂ - k₀ < λ̂_{k₀}` and `λ̂_{k̂} ≤ (d/2) λ̂_{k₀} + c_H`. -/
theorem hLam_window {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {β ν a cH : ℝ} (ha : 1 < a)
    (hβ0 : 0 < β) (hβ : 2 * (d : ℝ) ≤ Real.log β) (hν : 0 < ν)
    (hcH : (d : ℝ) * ((d : ℝ) - 2) / 2 * Real.log L ≤ cH) {kf : ℕ}
    (hh : ∀ k < kf, ν * (L : ℝ) ^ (2 * k + 2) < 1) :
    (kf : ℝ) - kZero d L β ν < lamHat d L β a (kZero d L β ν) ∧
      lamHat d L β a kf ≤ d / 2 * lamHat d L β a (kZero d L β ν) + cH := by
  set k0 := kZero d L β ν with hk0
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < L := by linarith
  have hℓ : 2 / 3 < Real.log L := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) hLR
    linarith
  set ℓ := Real.log L with hℓdef
  have hθ : thetaOf d L = ((d : ℝ) - 2) * ℓ := by
    unfold thetaOf
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  have hlogβa : Real.log (β * a) = Real.log β + Real.log a := Real.log_mul hβ0.ne' (by linarith)
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlam : ∀ j : ℕ, lamHat d L β a j = Real.log β + Real.log a + 1 + j * (((d : ℝ) - 2) * ℓ) := by
    intro j; unfold lamHat; rw [hlogβa, hθ]
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by linarith
  have hk0nn : (0 : ℝ) ≤ k0 := Nat.cast_nonneg _
  have hlam_pos : ∀ j : ℕ, 0 < lamHat d L β a j := by
    intro j; rw [hlam]
    have : 0 ≤ (j : ℝ) * (((d : ℝ) - 2) * ℓ) := by positivity
    linarith
  have hcH0 : 0 ≤ cH := by
    have : 0 ≤ (d : ℝ) * ((d : ℝ) - 2) / 2 * ℓ := by positivity
    linarith
  by_cases hcase : kf ≤ k0
  · have hkf : (kf : ℝ) ≤ k0 := by exact_mod_cast hcase
    refine ⟨by linarith [hlam_pos k0], ?_⟩
    have h1 : lamHat d L β a kf ≤ lamHat d L β a k0 := by
      rw [hlam, hlam]
      have : (kf : ℝ) * (((d : ℝ) - 2) * ℓ) ≤ (k0 : ℝ) * (((d : ℝ) - 2) * ℓ) :=
        mul_le_mul_of_nonneg_right hkf (by positivity)
      linarith
    have h2 := hlam_pos k0
    nlinarith
  · push Not at hcase
    have hkf1 : 1 ≤ kf := by omega
    have hν1 : ν * (L : ℝ) ^ (2 * kf) < 1 := by
      have := hh (kf - 1) (by omega)
      rwa [show 2 * (kf - 1) + 2 = 2 * kf by omega] at this
    have hlog1 : Real.log ν + 2 * kf * ℓ < 0 := by
      have h := Real.log_neg (mul_pos hν (pow_pos hLpos _)) hν1
      rw [Real.log_mul hν.ne' (pow_pos hLpos _).ne', Real.log_pow] at h
      push_cast at h
      linarith
    have hmax : 1 < β * ν * (L : ℝ) ^ ((k0 + 1) * d) := lt_kZero_succ (by omega) hL (mul_pos hβ0 hν)
    have hlog2 : 0 < Real.log β + Real.log ν + ((k0 : ℝ) + 1) * d * ℓ := by
      have h := Real.log_pos hmax
      rw [Real.log_mul (mul_pos hβ0 hν).ne' (pow_pos hLpos _).ne', Real.log_mul hβ0.ne' hν.ne',
        Real.log_pow] at h
      push_cast at h
      linarith
    have E1 : 2 * (kf : ℝ) * ℓ < Real.log β + ((k0 : ℝ) + 1) * d * ℓ := by linarith
    have hβpos : 0 < Real.log β := by linarith
    have hkfb : (kf : ℝ) < 3 / 4 * Real.log β + ((k0 : ℝ) + 1) * d / 2 := by
      by_contra hcon
      push Not at hcon
      have h1 := mul_le_mul_of_nonneg_left hcon (show 0 ≤ 2 * ℓ by linarith)
      nlinarith [mul_pos hβpos (show 0 < 3 * ℓ - 2 by linarith)]
    refine ⟨?_, ?_⟩
    · rw [hlam]
      nlinarith [mul_nonneg (mul_nonneg hk0nn hd2) (show 0 ≤ ℓ - 1 / 2 by linarith)]
    · rw [hlam, hlam]
      have E2 := mul_lt_mul_of_pos_left E1 (show 0 < (d : ℝ) - 2 by linarith)
      nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) / 2 - 1 by linarith) (show 0 ≤ Real.log a + 1 by linarith)]

/-- **`k₀ ≤ k̂_f`**: for `β ≥ 1`, `d ≥ 3` and a horizon `ν L^{2k̂+2} ≥ 1`, the regime index
`k₀ = kZero d L β ν` is at most `k̂` (from `L^{k₀ d} ≤ (β ν)⁻¹ ≤ ν⁻¹ ≤ L^{2k̂+2}`). -/
theorem kZero_le_horizon {d L : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) {β ν : ℝ} (hβ : 1 ≤ β)
    (hν : 0 < ν) {kf : ℕ} (h1 : 1 ≤ ν * (L : ℝ) ^ (2 * kf + 2)) : kZero d L β ν ≤ kf := by
  by_cases hk : kZero d L β ν = 0
  · omega
  · have hg : KZeroGenuine β ν := by
      by_contra hng
      exact hk (kZero_of_not_genuine hL hng)
    have hspec := kZero_spec (d := d) (L := L) (β := β) (ν := ν) (by omega) hL (mul_pos (by linarith) hν) hg
    have hLR : (1 : ℝ) < L := by exact_mod_cast hL
    have h2 : ν * (L : ℝ) ^ (kZero d L β ν * d) ≤ 1 := by
      have : ν * (L : ℝ) ^ (kZero d L β ν * d) ≤ β * ν * (L : ℝ) ^ (kZero d L β ν * d) := by
        have := pow_nonneg (show (0 : ℝ) ≤ L by linarith) (kZero d L β ν * d)
        nlinarith [mul_nonneg hν.le this]
      linarith
    have h3 : (L : ℝ) ^ (kZero d L β ν * d) ≤ (L : ℝ) ^ (2 * kf + 2) := by
      have hνp := hν
      have : ν * (L : ℝ) ^ (kZero d L β ν * d) ≤ ν * (L : ℝ) ^ (2 * kf + 2) := by linarith
      exact le_of_mul_le_mul_left this hνp
    have h4 : kZero d L β ν * d ≤ 2 * kf + 2 := (pow_le_pow_iff_right₀ hLR).1 h3
    have h5 : kZero d L β ν * 3 ≤ kZero d L β ν * d := Nat.mul_le_mul_left _ hd
    omega

end Balaban.RootFSpine
