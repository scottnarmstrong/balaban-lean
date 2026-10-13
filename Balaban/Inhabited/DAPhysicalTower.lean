/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DAPhysicalRadii

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The direct activity bound at the radius tower

`stepActivityBound_zeroClass_direct_at_tower`: for `β ≥ β₀`, with the cutoff `p₁ = pLog A₁ p β`
of the papers and the tower of `DAPhysicalRadii`, every hypothesis of
`stepActivityBound_zeroClass_direct` except the amplitude `hεb` and the smallness `hDA` holds.
The theorem takes exactly these two as hypotheses (stated at the tower's `r(β)`).

**The amplitude and smallness are NOT discharged.**  `tower_prop33_lower` proves that the landed
`hεb` forces `ε_U ≥ const · p₁ √β` at the tower, so `hεb` and `hDA` (whose right side is a fixed
constant) cannot both hold for large `β` (DAPHYS (B)).  The missing estimate is the scale-uniform
cubic bound of the potential remainder.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

theorem cK2'_pos' {B : ℝ} (hB : 0 ≤ B) : 0 < cK2' 3 3 2 B := by
  have h1 := cA_ge 3 3 2
  have h2 := cF_pos 3 3
  unfold cK2' cN'
  positivity

/-- **The landed amplitude is large at the tower** (T4, DAPHYS (B)).  If `0 < r` and
`r ≤ c_ψ/(2 p₁)` (as for `towerR`), the source allowance of `prop33Eps` gives
`β · prop33Eps ≥ (4 √N Q (|C|+1)/√3) · p₁ √β`, `Q = cK2'(famConst) > 0`. -/
theorem tower_prop33_lower {m₁ : ℕ} {BG BG₂ κ t β p₁ : ℝ} (ht : 0 < t)
    (hB : 0 ≤ famConst 3 3 BG₂ κ) (hβ : 0 < β) (hp : 0 < p₁)
    (hr : 0 < towerR κ t β p₁) :
    (4 * Real.sqrt ((2 : ℕ) : ℝ) * cK2' 3 3 2 (famConst 3 3 BG₂ κ) * (|towerC κ| + 1) /
        Real.sqrt 3) * p₁ * Real.sqrt β ≤
      prop33Eps 3 3 2 m₁ 1 1 1 nuW BG BG₂ κ t (towerR κ t β p₁) 0 0 * β := by
  set Q := cK2' 3 3 2 (famConst 3 3 BG₂ κ) with hQ
  have hQ0 : 0 < Q := cK2'_pos' hB
  set r := towerR κ t β p₁ with hrdef
  have hrle : r ≤ towerCpsi κ t β / (2 * p₁) := by rw [hrdef]; unfold towerR; linarith
  have hE : Q * t / r ≤ prop33Eps 3 3 2 m₁ 1 1 1 nuW BG BG₂ κ t r 0 0 := by
    unfold prop33Eps
    have : 0 ≤ 3 * c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
        ‖energyBd 3 3 2 (compWeight 3 1) nuW 1 (Q * t) t (rho4 3 3 2 BG κ)‖ / r ^ 3 := by
      have := one_le_c1 3 3
      positivity
    simp only [Nat.cast_ofNat, zero_mul, zero_div, add_zero] at this ⊢
    linarith
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hs2 : 0 < Real.sqrt ((2 : ℕ) : ℝ) := by positivity
  have hx : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hC1 := towerC_abs_pos κ
  have hr' : Q * t / (towerCpsi κ t β / (2 * p₁)) ≤ Q * t / r :=
    div_le_div_of_nonneg_left (by positivity) hr hrle
  have hid : (4 * Real.sqrt ((2 : ℕ) : ℝ) * Q * (|towerC κ| + 1) / Real.sqrt 3) * p₁ *
      Real.sqrt β = β * (Q * t / (towerCpsi κ t β / (2 * p₁))) := by
    rw [towerCpsi_eq]
    have h3 : Real.sqrt (3 * β) = Real.sqrt 3 * Real.sqrt β := Real.sqrt_mul (by norm_num) β
    have h4 : β = Real.sqrt β ^ 2 := (Real.sq_sqrt hβ.le).symm
    rw [h3]
    generalize Real.sqrt β = x at *
    subst h4
    have hx' : x ≠ 0 := hx.ne'
    have ht' : t ≠ 0 := ht.ne'
    have hs3' : Real.sqrt 3 ≠ 0 := hs3.ne'
    have hs2' : Real.sqrt ((2 : ℕ) : ℝ) ≠ 0 := hs2.ne'
    have hC1' : |towerC κ| + 1 ≠ 0 := hC1.ne'
    field_simp
    norm_num
  calc _ = β * (Q * t / (towerCpsi κ t β / (2 * p₁))) := hid
    _ ≤ β * (Q * t / r) := mul_le_mul_of_nonneg_left hr' hβ.le
    _ ≤ β * prop33Eps 3 3 2 m₁ 1 1 1 nuW BG BG₂ κ t r 0 0 := mul_le_mul_of_nonneg_left hE hβ.le
    _ = _ := by ring

/-- **The fixed data of the tower**: the numerics of `directWitness_core_amp` without the amplitude
inequality, so that `t = ε = δ₁` is chosen before `β` (it does not depend on `β`). -/
theorem tower_core_fixed (N : ℕ) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ κdec κ0 δc : ℝ),
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
  set κ0 : ℝ := aEnt 3 3 + 1 with hκ0def
  set κdec : ℝ := 3 * κ0 + c1 3 3 + 5 with hκdecdef
  have hκdec0 : 0 ≤ κdec := by rw [hκdecdef]; linarith
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
  have hκdec3 : 3 * κ0 + 3 ≤ κdec := by rw [hκdecdef]; linarith [one_le_c1 3 3]
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, hC, by linarith, hκdec3,
    by linarith, by linarith, hlogκ, c7_le_thm73C3_of_large (by norm_num) hBG1 hκ2, hm3, g6, g7,
    hδcSX, g1.le, g2, g3.le, g4.le, g5.le, le_rfl, ?_, hB0⟩
  rw [hκdecdef]; linarith [one_le_c1 3 3]



open Classical in
/-- **The direct activity bound at the tower** (T4).  There are fixed data `m₁, BG, BG₂, κ, t = δ₁,
δ, κ_dec, κ₀` and a threshold `β₀ ≥ 2` such that for every `β ≥ β₀`, at the step
`hatStep m₁ β (pLog A₁ p β) δ` with `ρ = p₁`, `pp = 2 p₁`, `c_ψ = towerCpsi κ t β`,
`r = towerR κ t β p₁`, `R_σ = R₁ = 2`, all hypotheses of `stepActivityBound_zeroClass_direct`
hold except the amplitude `hεb` and the smallness `hDA`; these two are the hypotheses below. -/
theorem stepActivityBound_zeroClass_direct_at_tower {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (m₁ : ℕ) (BG BG₂ κ t δ κdec κ0 β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      0 ≤ famConst 3 3 BG₂ κ ∧ aEnt 3 3 + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
      ∀ β : ℝ, β₀ ≤ β → 0 < pLog A₁ p β ∧ 0 < towerR κ t β (pLog A₁ p β) ∧
        (∀ εU : ℝ,
          prop33Eps 3 3 2 m₁ 1 1 1 nuW BG BG₂ κ t (towerR κ t β (pLog A₁ p β)) 0 0 * β ≤ εU →
          (4 * Real.sqrt ((2 : ℕ) : ℝ) * cK2' 3 3 2 (famConst 3 3 BG₂ κ) * (|towerC κ| + 1) /
            Real.sqrt 3) * pLog A₁ p β * Real.sqrt β ≤ εU) ∧
        ∀ εU : ℝ, 0 < εU →
        prop33Eps 3 3 2 m₁ 1 1 1 nuW BG BG₂ κ t (towerR κ t β (pLog A₁ p β)) 0 0 * β ≤ εU →
        2 * εU ≤ 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
          Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) →
        ∃ B : StepActivityBound (hatStep m₁ β (pLog A₁ p β) δ)
            (zeroClass 3 3 9 m₁ 1 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧ B.εH = 2 * εU := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hκdec0 : 0 ≤ κdec := by linarith
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀, hβ₀, hitems⟩ := tower_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  refine ⟨m₁, BG, BG₂, κ, t, δ, κdec, κ0, β₀, hβ₀, ht0, hδ, hB0, hκE, hκa, ?_⟩
  intro β hβ
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  have hβ0 : 0 < β := by linarith
  refine ⟨hp, hr0, fun εU hε => ?_, ?_⟩
  · exact (tower_prop33_lower (m₁ := m₁) (BG := BG) ht0 hB0 hβ0 hp hr0).trans hε
  intro εU hεpos hεb0 hDA0
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
  set Kc' : ℝ := K0 3 3 κ0 + 1 with hKc'
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  have hεb : prop33Eps 3 3 2 m₁ 1 1 S.a₁ S.ν BG BG₂ κ t (towerR κ t β (pLog A₁ p β)) 0 0 *
        ‖(S.β : ℂ)‖ + ‖(0 : ℂ)‖ * (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
        nuBd 3 3 2 1 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t)
          (K4 3 3 2 BG κ * (xiC1 3 * t) + (1 + 3 * (xiC1 3 * t)) + (1 + 2 / nuW)) /
          towerR κ t β (pLog A₁ p β))) ≤ εU := by
    rw [norm_zero, zero_mul, add_zero, Complex.norm_real,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ S.β from hβ0.le)]
    exact hεb0
  have hκa' : 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := hκa
  obtain ⟨B, hB1, hB2⟩ := stepActivityBound_zeroClass_direct S
      (ρ := pLog A₁ p β) (εU := εU) (κ0 := κ0) (κ' := 0) (Kc' := Kc')
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
      hκdec (by exact_mod_cast hκ) h1 (by norm_num) hr0 le_rfl isLevel_Hm
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
      (by norm_num) hp le_rfl hεpos hεb hκE le_rfl le_rfl hκa' hDA0 R0 hlt
      (StepSetting.baseDomain_of_rayData R0) (by norm_num) rfl rfl
  exact ⟨B, hB1, hB2⟩

/-- The forced lower bound `K · p₁ √β` of the landed amplitude is unbounded: for `K, a > 0` and
every `M` it exceeds `M` for `β ≥ (M/(K a))²`, `a ≤ p₁`. -/
theorem tower_lower_unbounded {K a p₁ β M : ℝ} (hK : 0 < K) (ha : 0 < a) (hap : a ≤ p₁)
    (hβ : (M / (K * a)) ^ 2 ≤ β) : M ≤ K * p₁ * Real.sqrt β := by
  have h0 : 0 ≤ M / (K * a) ∨ M / (K * a) < 0 := le_or_gt _ _
  have hs : M / (K * a) ≤ Real.sqrt β := by
    rcases h0 with h | h
    · exact Real.le_sqrt_of_sq_le hβ
    · exact h.le.trans (Real.sqrt_nonneg _)
  rw [div_le_iff₀ (by positivity)] at hs
  have : K * a * Real.sqrt β ≤ K * p₁ * Real.sqrt β :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hap hK.le) (Real.sqrt_nonneg _)
  linarith

/-- **Non-vacuity of the tower (T5).**  With `d = L = 3`, `N = 2`, `k = 1`, the fixed data of the
landed witness (`tower_core_fixed`), `A₁ = 1`, `p = 2` and one concrete `β ≥ β₀`, all (C) items hold
at `p₁ = (log β)^2`, `ρ = p₁`, `pp = 2 p₁`: the radius conditions are consistent.  (The amplitude
`hεb` can additionally be met at a single `β` by shrinking `t`, as in `directActivity_main`; it is
not met uniformly in `β`, by `tower_prop33_lower`.) -/
theorem tower_C_items_nonempty :
    ∃ (m₁ : ℕ) (κ t δ β : ℝ), 2 ≤ β ∧ 0 < t ∧ 0 < pLog 1 2 β ∧
      0 < towerR κ t β (pLog 1 2 β) ∧
      Real.sqrt ((2 : ℕ) : ℝ) * (‖(((hatStep m₁ β (pLog 1 2 β) δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ * towerCpsi κ t β)) < t ∧
      ((2 : ℝ) * 2 + towerR κ t β (pLog 1 2 β)) * pLog 1 2 β < towerCpsi κ t β ∧
      pLog 1 2 β < 2 * pLog 1 2 β ∧
      Nonempty ((hatStep m₁ β (pLog 1 2 β) δ).RayData (2 * pLog 1 2 β)) := by
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, -, hκ0, hκdec, hκ, -, -, -, hMX, -⟩ :=
    tower_core_fixed 2
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκdec0 : 0 ≤ κdec := by linarith
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀, hβ₀, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a
    hδ'b hδ'c
  obtain ⟨h1, -, h3, h4', h5, h6, h7⟩ := hitems β₀ le_rfl
  exact ⟨m₁, κ, t, δ, β₀, hβ₀, ht0, h1, h3, h4', h5, h6, h7⟩

end Balaban.Inhabited
