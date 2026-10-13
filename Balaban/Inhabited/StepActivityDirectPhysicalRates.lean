/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityDirectScaledWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# The zero-class activity bound at the witness step, at the rates that preserve the decay rate

`stepActivityBound_zeroClass_direct_physical` (`StepActivityDirectScaledWitness`) holds at the
rates of the numerical tower: the Mayer rate is `κ' = 0` and `κ_dec = 3 κ₀ + c₁ + 5`.  One
fluctuation step preserves the decay rate only at the rates of `stepActivityBound_zeroClass_direct_rate`:
`κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`, output rate
`(3/2) κ_dec >= κ_dec`.  This file proves the physical corollary at those rates.

* `tower_core_rates`: the tower of `tower_core_fixed` with `κ₀` and `κ_dec` prescribed.  The
  landed construction was parametric: `κ_dec` and `κ₀` entered only through the decoupling rate
  `κ = 4 d (2L+1)^d κ_dec + 40000 + 1/thm73C3`, then `m₁` with `c_* e^{N₀ κ} <= 3^{m₁}`, then
  the radii `t`, `δ_c`; so the construction is re-run with `κ₀, κ_dec` as parameters, and nothing
  else changes.  The (C) items `tower_C_items` are stated for arbitrary tower data and are reused.
* `stepActivityBound_zeroClass_direct_physical_rate`: for all `β >= β₀` the zero class at
  `hatStep m₁ β (pLog A₁ p β) δ` has a step activity bound with `κ_H = 2 κ_dec - 1`, prefactor at
  most `C (log β)^{3p}/√β`, the rate relation `κ' + 3κ₀ + c₁ + 3/2 <= 2 κ_dec - 1`, and the output
  rate `(3/2) κ_dec >= κ_dec`, `κ_out <= κ' - κ₀ - 1`.  The smallness `(DA)` is taken at `κ'`.
  No amplitude or smallness hypothesis remains.

Sizes (all fixed before `β`): `κ₀ = a_Ent + 1` with `a_Ent <= 3*10^5` (`aEnt_three_le`);
`c₁ = 3375`; so `κ_dec = 100 (κ₀ + 3385) <= 3.1*10^7`; `κ' <= 4.7*10^7`; the decoupling rate
`κ >= 4 * 3 * 343 * κ_dec = 4116 κ_dec` (about `10^{11}`), and `m₁ >= N₀ κ / log 3` with
`N₀ = 41472` (about `10^{15}`); `L^{m₁}` is astronomically large, as expected.

What is proved: zero class, witness step `k = 1` (`d = L = 3`, `N = 2`): for all large `β` the
label-activity bound holds at rates for which one fluctuation step preserves the decay rate.  What
is not proved: other scales, other classes, and the output terms.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- **The fixed data of the tower with prescribed rates.**  The conclusions of `tower_core_fixed`,
for any `κ₀ >= a_Ent + 1` and `κ_dec >= 3 κ₀ + c₁ + 5` (the latter gives `3κ₀ + 3 <= κ_dec` and
the rate relation at `κ' = 0`). -/
theorem tower_core_rates (N : ℕ) {κ0 κdec : ℝ} (hκ0 : aEnt 3 3 + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 3 3 + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3)
        (Cchi 3 3) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 3 3 N BG κ ≤ thm73C3 3 3 N ∧
      cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin 3 3 N BG κ (xiC1 3 * t) < δc ∧
      K4 3 3 N BG κ * (xiC1 3 * t) < coerciveConst 3 / 2 ∧
      δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar 3 3 N ∧ cK2 3 3 N * (2 * t) < bgC0 3 3 N / 2 ∧
      cK2 3 3 N * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      cK2' 3 3 N (famConst 3 3 BG₂ κ) * t ≤ c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) ∧
      2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t) ≤ bgC1 3 3 N ∧
      aEnt 3 3 + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst 3 3 BG₂ κ := by
  obtain ⟨c, BG0, hS0⟩ := decSpecs_exists (d := 3) (L := 3) (by norm_num) (by norm_num)
  set BG := max BG0 1 with hBGdef
  have hS : DecSpecs 3 3 c BG := hS0.mono_BG (le_max_left _ _)
  have hBG1 : 1 ≤ BG := le_max_right _ _
  obtain ⟨c₂, BG₂, hS2⟩ := Dec2.decSpecs_exists (d := 3) (L := 3) (Kc := levelKc 3 3)
    (Cx := Cchi 3 3) (by norm_num) (by norm_num) (levelKc_nonneg 3 3) (Cchi_nonneg 3 3)
  have hT3 := thm73C3_pos (d := 3) (L := 3) (N := N) (by norm_num)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  have hκ00 : 0 ≤ κ0 := by linarith
  have hκdec0 : 0 ≤ κdec := by linarith
  set κ : ℝ := 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec + 40000 +
    1 / thm73C3 3 3 N with hκdef
  have hinv : 0 ≤ 1 / thm73C3 3 3 N := by positivity
  have hcoef : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hκ1 : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec + 40000 ≤ κ := by
    rw [hκdef]; linarith
  have hκ2 : 1 / thm73C3 3 3 N ≤ κ := by
    rw [hκdef]; nlinarith [mul_nonneg hcoef hκdec0]
  have hκ3 : 40000 ≤ κ := by nlinarith [mul_nonneg hcoef hκdec0]
  obtain ⟨m₁, h4, hm⟩ := exists_m₁ (max (max (c * Real.exp ((N0 3 3 : ℝ) * κ))
    (c₂ * Real.exp ((N0 3 3 : ℝ) * κ))) (cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ)))
  have hm1 : c * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_left _ _).trans ((le_max_left _ _).trans (by exact_mod_cast hm))
  have hm2 : c₂ * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (by exact_mod_cast hm))
  have hm3 : cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁ :=
    (le_max_right _ _).trans (by exact_mod_cast hm)
  have S := dgSettingNu h4
  have SH := opSettingNu h4
  have hev := flCore_level_eventually (N := N) S SH isLevel_Hm isLevel_Gp (bgHypNu m₁)
    hS (κ := κ) (by linarith) hm1 hS2 hm2
  have hB0 : 0 ≤ famConst 3 3 BG₂ κ := by
    have := famConst_ge_one (L := 3) hS2.fam.2.1 κ (d := 3) (by norm_num); linarith
  have hc6 : 0 < c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8) :=
    c6'_pos hB0 (by have := gamma1_pos (d := 3) (by norm_num); positivity)
  have hDs : 0 < deltaStar 3 3 N := deltaStar_pos (d := 3) (L := 3) (N := N) (by norm_num)
  have hC0 : 0 < bgC0 3 3 N := bgC0_pos 3 3 N (by norm_num)
  have hC1 : 0 < bgC1 3 3 N := bgC1_pos' (d := 3) (L := 3) (N := N) (by norm_num)
  have hSX := smallConstX_pos 3 3 κ
  set SX := smallConstX 3 3 κ with hSXdef
  set δc : ℝ := 1 / (2 * (SX + 1)) with hδcdef
  have hδc0 : 0 < δc := by positivity
  have hδc1 : δc * (2 * (SX + 1)) = 1 := by rw [hδcdef]; field_simp
  have hδcSX : δc ^ 2 * SX ≤ 1 / 4 := by
    have h1 : δc * SX ≤ 1 / 2 := by nlinarith
    have h2 : δc ≤ 1 / 2 := by nlinarith
    nlinarith
  have hK4 : 0 < K4 3 3 N BG κ := K4_pos (by linarith) (by norm_num)
  have hcoer : 0 < coerciveConst 3 := coerciveConst_pos (by norm_num)
  have wk : ∀ {p : ℝ → Prop}, (∀ᶠ t in 𝓝 (0 : ℝ), p t) → ∀ᶠ t in 𝓝[>] (0 : ℝ), p t :=
    fun h => eventually_nhdsWithin_of_eventually_nhds h
  have e1 := ev_lt (f := fun t : ℝ => 2 * t) (by fun_prop) (c := deltaStar 3 3 N) (by simpa using hDs)
  have e2 := ev_lt (f := fun t : ℝ => cK2 3 3 N * (2 * t)) (by fun_prop) (c := bgC0 3 3 N / 2)
    (by simp; positivity)
  have e3 := ev_lt (f := fun t : ℝ => cK2 3 3 N * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) (by simpa using hc6)
  have e4 := ev_lt (f := fun t : ℝ => cK2' 3 3 N (famConst 3 3 BG₂ κ) * t) (by fun_prop)
    (c := c6' 3 3 N (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) (by simpa using hc6)
  have e5 := ev_lt (f := fun t : ℝ => 2 * (compC4 3 * (bgK1 3 3 N * (xiC1 3 * t))) + 5 * (2 * t))
    (by fun_prop) (c := bgC1 3 3 N) (by simpa using hC1)
  have e6 := ev_lt (f := fun t : ℝ => decDomMargin 3 3 N BG κ (xiC1 3 * t))
    (by unfold decDomMargin; fun_prop) (c := δc) (by simp [decDomMargin]; exact hδc0)
  have e7 := ev_lt (f := fun t : ℝ => K4 3 3 N BG κ * (xiC1 3 * t)) (by fun_prop)
    (c := coerciveConst 3 / 2) (by simp; positivity)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hC, g1, g2, g3, g4, g5, g6, g7, ht0⟩ := (hev.and ((wk e1).and ((wk e2).and
    ((wk e3).and ((wk e4).and ((wk e5).and ((wk e6).and ((wk e7).and hpos)))))))).exists
  have h343 : Real.log (9261 : ℝ) ≤ 9261 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hlogκ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 := by
    norm_num at h343 ⊢
    linarith
  have hκdec3 : 3 * κ0 + 3 ≤ κdec := by linarith [one_le_c1 3 3]
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hC, hκ00, hκdec3,
    by linarith, by linarith, hlogκ, c7_le_thm73C3_of_large (by norm_num) hBG1 hκ2, hm3, g6, g7,
    hδcSX, g1.le, g2, g3.le, g4.le, g5.le, hκ0, by linarith [one_le_c1 3 3], hB0⟩


open Classical in
/-- **The zero-class activity bound at the witness step for all large `β`, at the rates that
preserve the decay rate.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C` (`β₀ >= 2`, `C > 0`) such that for every
`β >= β₀` the zero class at `hatStep m₁ β (pLog A₁ p β) δ` has a step activity bound with
`κ_H = 2 κ_dec - 1` and prefactor at most `C (log β)^{3p}/√β`; the rate relation
`κ' + 3κ₀ + c₁ + 3/2 <= 2 κ_dec - 1` holds, and the output rate `κ_out = (3/2) κ_dec` satisfies
`κ_dec <= κ_out <= min κ' κ' - κ₀ - 1`.  The definitions of `κ₀, κ_dec, κ'` are the equations. -/
theorem stepActivityBound_zeroClass_direct_physical_rate {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ∀ β : ℝ, β₀ ≤ β →
        ∃ B : StepActivityBound (hatStep m₁ β (pLog A₁ p β) δ)
            (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧ B.εH ≤ C * (Real.log β) ^ (3 * p) / Real.sqrt β ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1 := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ :=
    tower_core_rates 2 (κ0 := κ0) (κdec := κdec) (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have hκdec0 : 0 ≤ κdec := by linarith
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  set ECS : ℝ := energyConstScaled 3 3 2 (compWeight 3 (1 : ℝ)) 1
    (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t) t (rho4 3 3 2 BG κ) with hECS
  have hECS0 : 0 ≤ ECS := by
    have hd0 : 0 < 3 := by norm_num
    have hV : 0 ≤ cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t :=
      mul_nonneg (cK2'_pos' hB0).le ht0.le
    have hρ : 0 ≤ rho4 3 3 2 BG κ := by
      have hBG := hC.hS.fam.2.1
      have hB1 : 0 ≤ famConst 3 3 BG κ := by
        have := famConst_ge_one (L := 3) hBG κ hd0; linarith
      unfold rho4
      exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
    have ha : 0 ≤ compWeight 3 (1 : ℝ) 1 :=
      (hC.HBp.weights 1 le_rfl (by norm_num)).1.trans' (by norm_num)
    have h := energyBdScaled_nonneg (d := 3) (L := 3) (N := 2) ha hV ht0.le hρ
    rw [energyBdScaled_eq (by norm_num) _ _ _ _ _ (by norm_num)] at h
    exact nonneg_of_mul_nonneg_right h (by positivity)
  set P : ℝ := 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 * ECS with hPdef
  have hP0 : 0 ≤ P := by
    have := one_le_c1 3 3
    rw [hPdef]; positivity
  set K : ℝ := cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t with hKdef
  have hK0' : 0 ≤ K := mul_nonneg (cK2'_pos' hB0).le ht0.le
  obtain ⟨β₁, C0, hexpβ₁, hC0, hA'⟩ := tower_amp_exists (A₁ := A₁) (κ := κ) (t := t) hA p ht0
    hP0 hK0'
  set Kc'' : ℝ := K0 3 3 κ0 + 1 with hKc''
  have hKc''pos : 0 < Kc'' := by have := K0_pos 3 3 κ0; rw [hKc'']; linarith
  refine ⟨m₁, t, δ,
    max (max β₀t β₁) (daThreshold C0 (daT 3 3 2 Kc'' κdec κ0 κ') (3 * p)), 2 * C0,
    le_trans hβ₀t ((le_max_left _ _).trans (le_max_left _ _)), by positivity, ht0, hδ, ?_⟩
  intro β hβ
  have hβt : β₀t ≤ β := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hβ)
  have hβ₁ : β₁ ≤ β := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hβ)
  have hβd : daThreshold C0 (daT 3 3 2 Kc'' κdec κ0 κ') (3 * p) ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβt
  have hβ2 : 2 ≤ β := le_trans hβ₀t hβt
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := by linarith
  have hexp : Real.exp 1 ≤ β := le_trans hexpβ₁ hβ₁
  have hℓ : 1 ≤ Real.log β := (Real.le_log_iff_exp_le hβ0).2 hexp
  have hamp2 := hA' β hβ₁
  set εU : ℝ := C0 * (Real.log β) ^ (3 * p) / Real.sqrt β with hεU
  have hεpos : 0 < εU := by
    have : 0 < (Real.log β) ^ (3 * p) := by positivity
    rw [hεU]; positivity
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def]; linarith
  have hκa' : κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := by
    rw [hκ'def, hκdecdef]; linarith
  set S := hatStep m₁ β (pLog A₁ p β) δ with hS
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := 2) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData S.G' (compWeight 3 1) nuW (1 + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  have hDA0 : 2 * εU ≤ 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
          Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) :=
    (hDA_iff 3 3 (by norm_num) hKc''pos κdec κ0 κ' εU).2 (amplitude_le hC0 (daT_pos 3 3 (by norm_num) hKc''pos κdec κ0 κ') (3 * p) hβd)
  obtain ⟨B, hB1, hB2⟩ : ∃ B : StepActivityBound S (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
      B.κH = 2 * κdec - 1 ∧ B.εH = 2 * εU := by
    refine stepActivityBound_zeroClass_direct_scaled_beta S
      (ρ := pLog A₁ p β) (εU := εU) (κ0 := κ0) (κ' := κ') (Kc' := Kc'')
      (Rσ := 2) (R₁ := 2) (r := towerR κ t β (pLog A₁ p β)) (R := 2) (m₀ := 1) (κdec := κdec)
      (κ₀ := κ0) (ρE := 0)
      (ρM := 0) (Bh := 1 + 2 / nuW) (δc := δc) (cψ := towerCpsi κ t β)
      (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
      (X₁V := fun _ => Finset.univ) (jF := fun _ => 1) (XF := fun _ => Xr)
      (𝒦XF := fun _ => {0}) (X₁F := fun _ => Finset.univ)
      (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
      (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
      (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
      (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
      (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
      (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
      (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
      (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
      hC hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hκ0
      hκdec (by exact_mod_cast hκ) h1 (by norm_num) hr0 hβ1 le_rfl isLevel_Hm
      hcψ0.le hMX hdm hα hsmX hδ₁ one_pos (bgHypNu m₁) hc7 le_rfl g1 g2 g3 g4 g5
      (fun _ => covSetup)
      (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog)
      (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
      (∅ : Finset PEmpty.{1}) (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp))
      (fun _ => covSetup) (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog) (fun s => Finset.mem_univ _)
      (∅ : Finset PEmpty.{1}) (fun τ => PEmpty.elim τ) (fun τ => PEmpty.elim τ)
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ => PEmpty.elim τ) (fun τ hτ => absurd hτ (by simp)) le_rfl (fun x => by simp) le_rfl
      (fun p => by simp) (by unfold nuW; norm_num) hBh
      (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _)) (by norm_num) hc hD
      (by norm_num) hp le_rfl hεpos ?hεb hκE le_rfl hκ'0 hκa' hDA0 R0 hlt
      (StepSetting.baseDomain_of_rayData R0) (by norm_num) rfl rfl


    case hεb =>
      have e1 : S.betaU = 3 * β := hatStep_betaU m₁ β (pLog A₁ p β) δ
      rw [e1]
      simp only [hPdef, hKdef, hECS] at hamp2
      simp only [norm_zero, zero_mul, add_zero, zero_div, mul_zero]
      exact hamp2
  refine ⟨B, hB1, ?_, hκa', 3 / 2 * κdec, rfl, by linarith, by rw [hκ'def, min_self]; linarith⟩
  rw [hB2, hεU]
  have : 2 * (C0 * (Real.log β) ^ (3 * p) / Real.sqrt β) = 2 * C0 * (Real.log β) ^ (3 * p) / Real.sqrt β := by ring
  rw [this]


end Balaban.Inhabited
