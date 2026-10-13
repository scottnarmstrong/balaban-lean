/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.TowerCoreRatesAtLeast
public import Balaban.Inhabited.DetOutputTermsWitness
public import Balaban.Fluctuation.StepRegWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared numerical tower for the witness step (`d = L = 3`, `N = 2`)

`StepTower κmin` bundles, once and for all, the output of `tower_core_rates_at_least` at the
physical rates `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`, the radii
`δ, δ'` of `exists_witness_params`, and the quantities derived from them that the per-scale
theorems use.  `exists_stepTower` shows that the record is inhabited for every `κmin`.

This file contains the tower only.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- The shared numerical tower at `N = 2`, with decoupling rate `κ ≥ κmin`. -/
structure StepTower (κmin : ℝ) where
  (κ0 κdec κ' : ℝ)
  κ0_eq : κ0 = aEnt 3 3 + 1
  κdec_eq : κdec = 100 * (κ0 + c1 3 3 + 10)
  κ'_eq : κ' = 3 / 2 * κdec + κ0 + 1
  m₁ : ℕ
  (c BG κ t c₂ BG₂ δc δ δ' : ℝ)
  m₁_four : 4 ≤ m₁
  t_pos : 0 < t
  core : Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁))
    1 nuW c BG κ t (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t)
  κ0_nonneg : 0 ≤ κ0
  κdec_lower : 3 * κ0 + 3 ≤ κdec
  κ_lower : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ
  κ_one : 1 ≤ (κ / 2 - 1) / 2
  κ_log : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) *
    (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2
  c7_cap : c7 3 3 2 BG κ ≤ thm73C3 3 3 2
  large_block : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁
  dom_margin : decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc
  coer_margin : K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2
  δc_small : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4
  t_cap : 2 * t ≤ deltaStar 3 3 2
  bg0_cap : cK2 3 3 2 * (2 * t) < bgC0 3 3 2 / 2
  cK2_cap : cK2 3 3 2 * t ≤
    c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)
  cK2'_cap : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t ≤
    c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)
  bg1_cap : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * t))) +
    5 * (2 * t) ≤ bgC1 3 3 2
  κ0_ent : aEnt 3 3 + 1 ≤ κ0
  rate_rel : 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1
  fam_nonneg : 0 ≤ famConst 3 3 BG₂ κ
  κmin_le : κmin ≤ κ
  δ_pos : 0 < δ
  δ_small : δ ^ 2 * smallConstX 3 3 0 ≤ 1 / 4
  δ'_pos : 0 < δ'
  δ'_cap : δ' ≤ thm73C3 3 3 2 / 2
  δ'_step : bgK1 3 3 2 * δ' ≤ δ / 4
  δ'_coer : bgK1 3 3 2 * δ' ≤ coerciveConst 3 / 4
  block_base : cstarX 3 3 ≤ (3 : ℝ) ^ m₁
  xi_small : xiC1 3 * t ≤ 1
  rho_nonneg : 0 ≤ rho4 3 3 2 BG κ
  det_z : ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1
  det_rate : κ' ≤ (κ - Real.log 2 -
    2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18

/-- **The tower record is inhabited** for every lower bound `κmin`. -/
theorem exists_stepTower (κmin : ℝ) : Nonempty (StepTower κmin) := by
  classical
  obtain ⟨-, δ, δ', -, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, -⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  set κ0 : ℝ := aEnt 3 3 + 1 with hκ0def
  set κdec : ℝ := 100 * (κ0 + c1 3 3 + 10) with hκdecdef
  set κ' : ℝ := 3 / 2 * κdec + κ0 + 1 with hκ'def
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hCn, hκ0n, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0, hmin⟩ :=
    tower_core_rates_at_least 2 κmin (κ0 := κ0) (κdec := κdec) le_rfl (by linarith)
  obtain ⟨hC⟩ := hCn
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  -- as in `stepActivityBound_zeroClass_direct_physical_rate`
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  -- as in `stepActivityBound_zeroClass_direct_physical_rate`
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  -- as in `stepActivityBound_zeroClass_direct_physical_rate`
  have hρ : 0 ≤ rho4 3 3 2 BG κ := by
    have hd0 : 0 < 3 := by norm_num
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst 3 3 BG κ := by
      have := famConst_ge_one (L := 3) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  -- as in `detExpansionLocC_scale`
  have e : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
  have hκ' := hκ
  rw [e] at hκ'
  have hκ57 : (57 : ℝ) ≤ κ := by linarith
  have hz := detDeg_three_rate hκ57
  have hlogd := log_detDeg_three_lt
  have hrate : κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  exact ⟨{
    κ0 := κ0, κdec := κdec, κ' := κ', κ0_eq := rfl, κdec_eq := rfl, κ'_eq := rfl
    m₁ := m₁, c := c, BG := BG, κ := κ, t := t, c₂ := c₂, BG₂ := BG₂, δc := δc, δ := δ, δ' := δ'
    m₁_four := h4, t_pos := ht0, core := ⟨hC⟩, κ0_nonneg := hκ0n, κdec_lower := hκdec
    κ_lower := hκ, κ_one := h1, κ_log := hlog, c7_cap := hc7, large_block := hMX
    dom_margin := hdm, coer_margin := hα, δc_small := hsmX, t_cap := g1, bg0_cap := g2
    cK2_cap := g3, cK2'_cap := g4, bg1_cap := g5, κ0_ent := hκE, rate_rel := hκa
    fam_nonneg := hB0, κmin_le := hmin, δ_pos := hδ, δ_small := hsm, δ'_pos := hδ'0
    δ'_cap := hδ'a, δ'_step := hδ'b, δ'_coer := hδ'c, block_base := hbig, xi_small := hxi1
    rho_nonneg := hρ, det_z := hz, det_rate := hrate }⟩

namespace StepTower

variable {κmin : ℝ} (T : StepTower κmin)

/-- The input `κ₀ ≥ a_Ent + 1` of the landed scale theorems. -/
theorem hκ0 : aEnt 3 3 + 1 ≤ T.κ0 := T.κ0_ent

/-- The input `κ_dec ≥ 3 κ₀ + c₁ + 5` of the landed scale theorems. -/
theorem hκdec : 3 * T.κ0 + c1 3 3 + 5 ≤ T.κdec := by
  have := one_le_c1 3 3
  have := T.κ0_nonneg
  rw [T.κdec_eq]; linarith

/-- The 21 conjuncts of `tower_core_rates 2` at the witnesses of `T`. -/
theorem tower_conj :
    4 ≤ T.m₁ ∧ 0 < T.t ∧
      Nonempty (FlCore 2 (Gp T.m₁ (rhoSep T.m₁)) (Hm T.m₁ (rhoSep T.m₁)) 1 nuW T.c T.BG T.κ T.t
        (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t) ∧
      0 ≤ T.κ0 ∧ 3 * T.κ0 + 3 ≤ T.κdec ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * T.κdec ≤ T.κ ∧
      1 ≤ (T.κ / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (T.κ / 2 - 1) / 2 ∧
      c7 3 3 2 T.BG T.κ ≤ thm73C3 3 3 2 ∧
      cstarX 3 3 * Real.exp (N0 3 3 * T.κ) ≤ ((3 : ℕ) : ℝ) ^ T.m₁ ∧
      decDomMargin 3 3 2 T.BG T.κ (xiC1 3 * T.t) < T.δc ∧
      K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t) < coerciveConst 3 / 2 ∧
      T.δc ^ 2 * smallConstX 3 3 T.κ ≤ 1 / 4 ∧
      2 * T.t ≤ deltaStar 3 3 2 ∧ cK2 3 3 2 * (2 * T.t) < bgC0 3 3 2 / 2 ∧
      cK2 3 3 2 * T.t ≤ c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8) ∧
      cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t ≤
        c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8) ∧
      2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (2 * T.t) ≤ bgC1 3 3 2 ∧
      aEnt 3 3 + 1 ≤ T.κ0 ∧
      0 + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ 2 * T.κdec - 1 ∧ 0 ≤ famConst 3 3 T.BG₂ T.κ :=
  ⟨T.m₁_four, T.t_pos, T.core, T.κ0_nonneg, T.κdec_lower, T.κ_lower, T.κ_one, T.κ_log,
    T.c7_cap, T.large_block, T.dom_margin, T.coer_margin, T.δc_small, T.t_cap, T.bg0_cap,
    T.cK2_cap, T.cK2'_cap, T.bg1_cap, T.κ0_ent, T.rate_rel, T.fam_nonneg⟩

end StepTower

end Balaban.Inhabited
