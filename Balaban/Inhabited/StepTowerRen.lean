/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.TowerCoreRatesRen
public import Balaban.Fluctuation.RenormStrictData
public import Balaban.Fluctuation.RenormDecAnalytic
public import Balaban.Inhabited.RenormLocC1ZeroWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower with the renormalization margins

`StepTowerRen κmin` extends `StepTower κmin` by the strict margin
`2 K₄ ξ₁ t < δ_*′(famConst BG κ, γ₁/8)` (which does not follow from `FlCore`) and one radius `r₀`
with the three margins `D₀ ≤ 1`, `D₀ ≤ δ_*′`, `D₁ ≤ δ_*′` in the forms taken by `renDec_analytic`
and `renDec_sharp` at `ε = t`.  `exists_stepTowerRen` shows that the record is inhabited for every
`κmin`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- The shared tower with the renormalization margins. -/
structure StepTowerRen (κmin : ℝ) extends StepTower κmin where
  ren_margin : 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) <
    deltaStar' 3 3 2 (famConst 3 3 BG κ) (gamma1 3 / 8)
  r₀ : ℝ
  r₀_pos : 0 < r₀
  r₀_le : r₀ ≤ 1 / 16
  D₀_le_one : 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) + 3 * r₀ ≤ 1
  D₀_le_star : 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) + 3 * r₀ ≤
    deltaStar' 3 3 2 (famConst 3 3 BG κ) (gamma1 3 / 8)
  D₁_le_star : (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 BG κ + bgK1 3 3 2) * xiC1 3)) * t * r₀ ≤
    deltaStar' 3 3 2 (famConst 3 3 BG κ) (gamma1 3 / 8)

/-- **The record with margins is inhabited** for every lower bound `κmin`. -/
theorem exists_stepTowerRen (κmin : ℝ) : Nonempty (StepTowerRen κmin) := by
  classical
  obtain ⟨-, δ, δ', -, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, -⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  set κ0 : ℝ := aEnt 3 3 + 2 with hκ0def
  set κdec : ℝ := 100 * (κ0 + c1 3 3 + 10) with hκdecdef
  set κ' : ℝ := 3 / 2 * κdec + κ0 + 1 with hκ'def
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hCn, hκ0n, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0, hmin, hmar⟩ :=
    tower_core_rates_at_least_ren 2 κmin (κ0 := κ0) (κdec := κdec) (by linarith) (by linarith)
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
  obtain ⟨r₀, hr0, hr1, hD0, hDs, hD1⟩ := renMargins_exists_r₀_of_flCore hC hmar
  exact ⟨StepTowerRen.mk {
    κ0 := κ0, κdec := κdec, κ' := κ', κ0_eq := rfl, κdec_eq := rfl, κ'_eq := rfl
    m₁ := m₁, c := c, BG := BG, κ := κ, t := t, c₂ := c₂, BG₂ := BG₂, δc := δc, δ := δ, δ' := δ'
    m₁_four := h4, t_pos := ht0, core := ⟨hC⟩, κ0_nonneg := hκ0n, κdec_lower := hκdec
    κ_lower := hκ, κ_one := h1, κ_log := hlog, c7_cap := hc7, large_block := hMX
    dom_margin := hdm, coer_margin := hα, δc_small := hsmX, t_cap := g1, bg0_cap := g2
    cK2_cap := g3, cK2'_cap := g4, bg1_cap := g5, κ0_ent := hκE, rate_rel := hκa
    fam_nonneg := hB0, κmin_le := hmin, δ_pos := hδ, δ_small := hsm, δ'_pos := hδ'0
    δ'_cap := hδ'a, δ'_step := hδ'b, δ'_coer := hδ'c, block_base := hbig, xi_small := hxi1
    rho_nonneg := hρ, det_z := hz, det_rate := hrate }
    hmar r₀ hr0 hr1 hD0 hDs hD1⟩


end Balaban.Inhabited
