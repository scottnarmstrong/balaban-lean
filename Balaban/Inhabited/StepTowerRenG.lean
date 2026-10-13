/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.StepTowerRen
public import Balaban.Inhabited.TowerCoreRatesGeneral
public import Balaban.Inhabited.TowerCoreRatesVariantsGeneral
public import Balaban.Fluctuation.DetRateGeneral
public import Balaban.Fluctuation.RenormStrictData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The general tower with the renormalization margins

`StepTowerRenG d L N κmin` extends `StepTowerG d L N κmin` by the strict margin
`2 K₄ ξ₁ t < δ_*′(famConst BG κ, γ₁/8)` and one radius `r₀` with the three margins
`D₀ ≤ 1`, `D₀ ≤ δ_*′`, `D₁ ≤ δ_*′`, for general dimension, block size and number of components.
`exists_stepTowerRenG` shows that the record is inhabited, and `StepTowerRen.toG` is the bridge
from the fixed `3, 3, 2` record.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep

/-- The general tower with the renormalization margins. -/
structure StepTowerRenG (d L N : ℕ) [NeZero L] (κmin : ℝ) extends StepTowerG d L N κmin where
  ren_margin : 2 * (K4 d L N BG κ * (xiC1 d * t)) <
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)
  r₀ : ℝ
  r₀_pos : 0 < r₀
  r₀_le : r₀ ≤ 1 / 16
  D₀_le_one : 2 * (K4 d L N BG κ * (xiC1 d * t)) + 3 * r₀ ≤ 1
  D₀_le_star : 2 * (K4 d L N BG κ * (xiC1 d * t)) + 3 * r₀ ≤
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)
  D₁_le_star : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * t * r₀ ≤
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)

/-- **The bridge**: the fixed `3, 3, 2` record with margins is a general one. -/
noncomputable def StepTowerRen.toG {κmin : ℝ} (T : StepTowerRen κmin) :
    StepTowerRenG 3 3 2 κmin :=
  { T.toStepTower.toG with
    ren_margin := T.ren_margin
    r₀ := T.r₀
    r₀_pos := T.r₀_pos
    r₀_le := T.r₀_le
    D₀_le_one := T.D₀_le_one
    D₀_le_star := T.D₀_le_star
    D₁_le_star := T.D₁_le_star }

namespace StepTowerRen

variable {κmin : ℝ} (T : StepTowerRen κmin)

@[simp] theorem toG_toStepTowerG : T.toG.toStepTowerG = T.toStepTower.toG := rfl
@[simp] theorem toG_r₀ : T.toG.r₀ = T.r₀ := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl

end StepTowerRen

/-- **The general record with margins is inhabited**, with cover index `m₀` and output-rate floor
`entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`. -/
theorem exists_stepTowerRenG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerRenG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec ∧
      (entropyLoss + c1 d L * κroot ≤ 150 * (aEnt d L + 2) → T.κ0 = aEnt d L + 2) := by
  classical
  obtain ⟨-, δ, δ', -, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, -⟩ :=
    exists_witness_params_general d L N (by omega) (by omega) (fun _ => 0)
  have hc1 := one_le_c1 d L
  have hent := aEnt_nonneg d L
  set κ0 : ℝ := max (aEnt d L + 2) ((entropyLoss + c1 d L * κroot) / 150) with hκ0def
  have hκ0a : aEnt d L + 2 ≤ κ0 := le_max_left _ _
  have hκ0b : (entropyLoss + c1 d L * κroot) / 150 ≤ κ0 := le_max_right _ _
  set κdec : ℝ := 100 * (κ0 + c1 d L + 10) with hκdecdef
  set κ' : ℝ := 3 / 2 * κdec + κ0 + 1 with hκ'def
  have hκ'0 : 0 ≤ κ' := by linarith
  set A : ℝ := (((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ) with hAdef
  set D : ℝ := Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) with hDdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set κm : ℝ := max κmin (max (4 * Real.log A + 2) (2 * d * L * κ' + D + 1)) with hκmdef
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hCn, hκ0n, hκdec, hκ, h1, -, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0, hmin, hmar⟩ :=
    tower_core_rates_ren_general (d := d) (L := L) N hd hL (ν := νref L)
      (by unfold νref; positivity)
      (by
        unfold νref
        rw [one_div, inv_mul_eq_div, div_le_one (by positivity)])
      κm (κ0 := κ0) (κdec := κdec) (by linarith) (by linarith)
  obtain ⟨hC⟩ := hCn
  have hm1 : κmin ≤ κ := le_trans (le_max_left _ _) hmin
  have hm2 : 4 * Real.log A + 2 ≤ κ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmin
  have hm3 : 2 * d * L * κ' + D + 1 ≤ κ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmin
  have hbig : cstarX d L ≤ (L : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos d L
    have h2 : cstarX d L ≤ cstarX d L * Real.exp ((N0 d L : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by
        have : 0 ≤ κ := by linarith
        positivity))
    have h3 : ((L : ℕ) : ℝ) ^ m₁ = (L : ℝ) ^ m₁ := rfl
    linarith
  have hκ_nn : 0 ≤ κ := by linarith
  have hxi1 : xiC1 d * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 d L N BG κ
    have h3 := bgC1_le_small d L N (by omega)
    linarith
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hd0' : 0 < d := by omega
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0'; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0'; positivity)).le
  have hpos : 0 ≤ 2 * (d : ℝ) * L * κ' := by positivity
  have hDk : D < κ := by linarith
  have hz := detDeg_rate_general d L hDk
  have hrate : κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
      (2 * (d : ℝ) * (L : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlog : Real.log A ≤ (κ / 2 - 1) / 2 := by linarith
  obtain ⟨r₀, hr0, hr1, hD0, hDs, hD1⟩ := renMargins_exists_r₀_of_flCore hC hmar
  refine ⟨{
    hd := hd, hL := hL, hN := hN
    κ0 := κ0, κdec := κdec, κ' := κ', κ0_ge := hκ0a, κdec_eq := rfl, κ'_eq := rfl
    m₁ := m₁, m₀ := m₀, m₀_pos := hm₀, c := c, BG := BG, κ := κ, t := t, c₂ := c₂, BG₂ := BG₂,
    δc := δc, δ := δ, δ' := δ'
    m₁_four := h4, t_pos := ht0, core := ⟨hC⟩, κ0_nonneg := hκ0n, κdec_lower := hκdec
    κ_lower := hκ, κ_one := h1, κ_log := hlog, c7_cap := hc7, large_block := hMX
    dom_margin := hdm, coer_margin := hα, δc_small := hsmX, t_cap := g1, bg0_cap := g2
    cK2_cap := g3, cK2'_cap := g4, bg1_cap := g5, κ0_ent := hκE, rate_rel := hκa
    fam_nonneg := hB0, κmin_le := hm1, δ_pos := hδ, δ_small := hsm, δ'_pos := hδ'0
    δ'_cap := hδ'a, δ'_step := hδ'b, δ'_coer := hδ'c, block_base := hbig, xi_small := hxi1
    rho_nonneg := hρ, det_z := hz, det_rate := hrate
    ren_margin := hmar, r₀ := r₀, r₀_pos := hr0, r₀_le := hr1, D₀_le_one := hD0
    D₀_le_star := hDs, D₁_le_star := hD1 }, rfl, ?_, ?_⟩
  · show entropyLoss + c1 d L * κroot ≤ 3 / 2 * κdec
    rw [hκdecdef]
    linarith
  · intro h
    show κ0 = aEnt d L + 2
    rw [hκ0def]
    exact max_eq_left (by linarith)

end Balaban.Inhabited
