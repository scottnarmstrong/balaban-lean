/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DARateNumerics
public import Balaban.Fluctuation.ObsScalarTilt
public import Balaban.Fluctuation.DetCauchyGraph
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# One chain of constants for the zero-class step output: the arithmetic witness

`notes/phase1/CONSTS.md`, leaf 1.  This file is numbers and arithmetic only.  It asserts no
`FlCore`, no physical mark, no analytic statement and no volume-uniform label system; those are the
physical layer `stepOutput_consts_physical`.

* `StepOutputConsts d L`: real numbers `κ₀, κ_dec, κ′, κ_out, κ_H`, the decoupling rate `κ`, the
  determinant rate `κ_det = (κ - log 2 - 2 log(detDeg + 1)) / (2 d L)`, the collar-hull constant
  `B_hull = c_G c₁` and rate `λ_hull = κ_det/(1 + B_hull) - c₁ log 2`, and the label constants
  `K_c = 2(K₀ + 1)`, `K_all = 2 K₀`, `K_tot = K_c + K_all`, together with the inequalities of the
  ledger.  The entropy requirement is the stronger `a_Ent + 2 ≤ κ₀` that `rootUnion_entropy`
  needs (the landed rate witness only has `a_Ent + 1`).
* `stepOutput_consts_witness`: `Nonempty (StepOutputConsts 3 3)`;
  `stepOutput_consts_exists_ge`: for every `κ_min` a record with `κ_min ≤ κ`.
* `exists_beta0_stepOutput`: a scale threshold `β₀` beyond which the scalar-tilt arithmetic
  (`R_g > 1`, `R_g ε ≤ Θ`) and the activity smallness `ε_H ≤ Θ(K_tot)` hold for `b = β 3^k`.
-/

@[expose] public section

namespace Balaban.Fluctuation

/-- The activity-smallness threshold `Θ(K) = 1 / (8 K³ c₁ exp((κ_H - 2κ₀) c_G + c₁ + κ′ c_G))`. -/
noncomputable def stepTheta (d L : ℕ) (K κH κ0 κ' : ℝ) : ℝ :=
  1 / (8 * K ^ 3 * c1 d L * Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))

/-- The numerical ledger of the zero-class step output (`CONSTS.md` §1), real numbers only. -/
structure StepOutputConsts (d L : ℕ) where
  /-- entropy rate -/
  k0 : ℝ
  /-- decoupling activity rate -/
  kdec : ℝ
  /-- label target rate `κ′` -/
  k' : ℝ
  /-- output class rate -/
  kout : ℝ
  /-- label-converted rate `κ_H` -/
  kH : ℝ
  /-- decoupling (interpolation) rate `κ` -/
  kapp : ℝ
  /-- determinant rate -/
  kdet : ℝ
  /-- collar-hull rate -/
  lhull : ℝ
  /-- collar-hull constant -/
  Bhull : ℝ
  /-- base label entropy constant -/
  Kc : ℝ
  /-- constant of the two label extensions -/
  Kall : ℝ
  /-- total label entropy constant -/
  Ktot : ℝ
  k0_ent : aEnt d L + 2 ≤ k0
  kdec_ge : 3 * k0 + 3 ≤ kdec
  kdec_ge' : 3 * k0 + c1 d L + 5 ≤ kdec
  k'_eq : k' = 3 / 2 * kdec + k0 + 1
  kout_eq : kout = 3 / 2 * kdec
  kH_eq : kH = 2 * kdec - 1
  kdec_le_kout : kdec ≤ kout
  kout_le : kout ≤ k' - k0 - 1
  kH_ge : k' + 3 * k0 + c1 d L + 3 / 2 ≤ kH
  kapp_ge : 4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * kdec ≤ kapp
  kdet_eq : kdet = (kapp - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L)
  kdet_ge : k' ≤ kdet
  z_lt : 2 * ((detDeg d L : ℝ) + 1) ^ 2 * Real.exp (-kapp) < 1
  Bhull_eq : Bhull = cG d L * c1 d L
  lhull_eq : lhull = kdet / (1 + Bhull) - c1 d L * Real.log 2
  lhull_ge : kout ≤ lhull
  Kc_eq : Kc = 2 * (K0 d L k0 + 1)
  Kall_eq : Kall = 2 * K0 d L k0
  Ktot_eq : Ktot = Kc + Kall

namespace StepOutputConsts

variable {d L : ℕ}

/-- The activity-smallness threshold at the total label constant of the record. -/
noncomputable def theta (C : StepOutputConsts d L) : ℝ :=
  stepTheta d L C.Ktot C.kH C.k0 C.k'

end StepOutputConsts

private theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem detDeg_three_succ' : (detDeg 3 3 : ℝ) + 1 = 214991878 := by
  have : detDeg 3 3 + 1 = 214991878 := by norm_num [detDeg, Localization.N0]
  exact_mod_cast this

/-- For every prescribed `κ_min` there is a record at `d = L = 3` with `κ_min ≤ κ`, with
`κ₀ = a_Ent + 2` and `κ_dec = 100 (κ₀ + c₁ + 10)`. -/
theorem stepOutput_consts_exists_ge (κmin : ℝ) :
    ∃ C : StepOutputConsts 3 3, κmin ≤ C.kapp ∧ C.k0 = aEnt 3 3 + 2 ∧
      C.kdec = 100 * (C.k0 + c1 3 3 + 10) := by
  have hc1 : c1 3 3 = 3375 := c1_three
  have hcG : cG 3 3 = 18 := cG_three
  have hent : 0 ≤ aEnt 3 3 := aEnt_nonneg 3 3
  have hl2 := log_two_pos'
  obtain ⟨k0, h0⟩ : ∃ x : ℝ, x = aEnt 3 3 + 2 := ⟨_, rfl⟩
  obtain ⟨kdec, hdec⟩ : ∃ x : ℝ, x = 100 * (k0 + c1 3 3 + 10) := ⟨_, rfl⟩
  obtain ⟨k', hk'⟩ : ∃ x : ℝ, x = 3 / 2 * kdec + k0 + 1 := ⟨_, rfl⟩
  obtain ⟨kout, hout⟩ : ∃ x : ℝ, x = 3 / 2 * kdec := ⟨_, rfl⟩
  obtain ⟨kH, hkH⟩ : ∃ x : ℝ, x = 2 * kdec - 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ x : ℝ, x = (detDeg 3 3 : ℝ) + 1 := ⟨_, rfl⟩
  have hD' : D = 214991878 := by rw [hD]; exact detDeg_three_succ'
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by rw [hD']; norm_num)
  obtain ⟨khull, hhull⟩ : ∃ x : ℝ, x = 18 * 60751 * (kout + 3375 * Real.log 2)
      + Real.log 2 + 2 * Real.log D := ⟨_, rfl⟩
  obtain ⟨kapp, hkapp⟩ : ∃ x : ℝ, x = max κmin (max (4116 * kdec) (khull + 1)) := ⟨_, rfl⟩
  have hk0 : 2 ≤ k0 := by linarith
  have hdec1 : 3 * k0 + c1 3 3 + 5 ≤ kdec := by rw [hdec]; linarith
  have hkdec0 : 0 ≤ kdec := by linarith
  have hkout0 : 0 ≤ kout := by linarith
  have hk1 : κmin ≤ kapp := by rw [hkapp]; exact le_max_left _ _
  have hk2 : 4116 * kdec ≤ kapp := by
    rw [hkapp]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hk3 : khull + 1 ≤ kapp := by
    rw [hkapp]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  set Lg := Real.log 2 with hLg
  have hkh : 18 * 60751 * (kout + 3375 * Lg) ≤ khull - Lg - 2 * Real.log D := by
    rw [hhull]; linarith
  have hdet : 60751 * (kout + 3375 * Lg) + 1 / 18 ≤ (kapp - Lg - 2 * Real.log D) / 18 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hz : 2 * D ^ 2 * Real.exp (-kapp) < 1 := by
    have hlog : Real.log (2 * D ^ 2) < kapp := by
      rw [Real.log_mul (by norm_num) (by rw [hD']; positivity), Real.log_pow]
      push_cast
      linarith
    have h2 : 2 * D ^ 2 < Real.exp kapp :=
      (Real.log_lt_iff_lt_exp (by rw [hD']; positivity)).1 hlog
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    exact h2
  have hKpos : 0 ≤ K0 3 3 k0 := (K0_pos 3 3 k0).le
  have e1 : aEnt 3 3 + 2 ≤ k0 := by linarith
  have e2 : 3 * k0 + 3 ≤ kdec := by linarith
  have e3 : 3 * k0 + c1 3 3 + 5 ≤ kdec := hdec1
  have e4 : kdec ≤ kout := by linarith
  have e5 : kout ≤ k' - k0 - 1 := by linarith
  have e6 : k' + 3 * k0 + c1 3 3 + 3 / 2 ≤ kH := by linarith
  refine ⟨StepOutputConsts.mk k0 kdec k' kout kH kapp ((kapp - Lg - 2 * Real.log D) / 18)
    ((kapp - Lg - 2 * Real.log D) / 18 / (1 + 60750) - 3375 * Lg) 60750 (2 * (K0 3 3 k0 + 1))
    (2 * K0 3 3 k0) (2 * (K0 3 3 k0 + 1) + 2 * K0 3 3 k0) e1 e2 e3 hk' hout hkH e4 e5 e6
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl, hk1, h0, hdec⟩
  · have : (4 : ℝ) * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
    rw [this]; exact hk2
  · rw [← hD, hLg]; norm_num
  · rw [hk']; linarith
  · rw [← hD]; exact hz
  · rw [hc1, hcG]; norm_num
  · rw [hc1]
  · have h : 60751 * (kout + 3375 * Lg) ≤ (kapp - Lg - 2 * Real.log D) / 18 := by linarith
    have : kout ≤ (kapp - Lg - 2 * Real.log D) / 18 / (1 + 60750) - 3375 * Lg := by
      rw [sub_eq_add_neg, ← sub_nonneg]
      have : 0 ≤ (kapp - Lg - 2 * Real.log D) / 18 / (1 + 60750) - 3375 * Lg - kout := by
        have h' : (kapp - Lg - 2 * Real.log D) / 18 / (1 + 60750) ≥ kout + 3375 * Lg := by
          rw [ge_iff_le, le_div_iff₀ (by norm_num)]; linarith
        linarith
      linarith
    exact this

/-- **T2.**  The record at `d = L = 3` is inhabited. -/
theorem stepOutput_consts_witness : Nonempty (StepOutputConsts 3 3) :=
  let ⟨C, _⟩ := stepOutput_consts_exists_ge 0
  ⟨C⟩

/-- The threshold `Θ(K_tot)` of a record is positive. -/
theorem StepOutputConsts.theta_pos {d L : ℕ} [NeZero L] (C : StepOutputConsts d L) :
    0 < C.theta := by
  have hK : 0 < C.Ktot := by
    rw [C.Ktot_eq, C.Kc_eq, C.Kall_eq]
    have := K0_pos d L C.k0
    linarith
  have hc : 0 < c1 d L := lt_of_lt_of_le one_pos (one_le_c1 d L)
  unfold StepOutputConsts.theta stepTheta
  positivity

/-- **T3.**  The scale threshold `β₀`: for `b = β 3^k` with `β ≥ β₀`, `k` arbitrary, the disc radius
`R_g = b^s/(C_R (log b)^{3p})` exceeds `1`, and every `ε_H` with
`0 ≤ ε_H ≤ C_U (log b)^{3p}/√b` satisfies `R_g ε_H ≤ Θ(K_tot)` and `ε_H ≤ Θ(K_tot)`, i.e. the
smallness `hε` of the mark records with the enlarged entropy constant. -/
theorem exists_beta0_stepOutput {d L : ℕ} [NeZero L] (C : StepOutputConsts d L)
    {CU CR s p : ℝ} (hCU : 0 ≤ CU) (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ (β : ℝ) (k : ℕ), β₀ ≤ β → ∀ ε : ℝ, 0 ≤ ε →
      ε ≤ CU * Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) →
      1 < obsRg CR s p (β * 3 ^ k) ∧ obsRg CR s p (β * 3 ^ k) * ε ≤ C.theta ∧ ε ≤ C.theta := by
  obtain ⟨b₁, hb₁, h1⟩ := exists_one_lt_obsRg (p := p) hCR hs0
  obtain ⟨b₂, hb₂, h2⟩ := exists_obsRg_mul_le (p := p) hCR hs hCU C.theta_pos
  refine ⟨max b₁ b₂, lt_of_lt_of_le hb₁ (le_max_left _ _), fun β k hβ ε hε0 hε => ?_⟩
  have hβ1 : 1 < β := lt_of_lt_of_le hb₁ (le_trans (le_max_left _ _) hβ)
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb : β ≤ β * 3 ^ k := by nlinarith
  have hb1 : 1 ≤ β * 3 ^ k := by linarith
  have hR := h1 _ (le_trans (le_trans (le_max_left _ _) hβ) hb)
  have hε' : ε ≤ CU * obsW p (β * 3 ^ k) ^ 3 / Real.sqrt (β * 3 ^ k) := by
    rwa [obsW_cube p _ hb1]
  have hR2 := h2 _ ε (le_trans (le_trans (le_max_right _ _) hβ) hb) hε'
  refine ⟨hR, hR2, ?_⟩
  nlinarith

end Balaban.Fluctuation
