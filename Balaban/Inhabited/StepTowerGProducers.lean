/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
public import Balaban.Inhabited.StepTowerThetaG
public import Balaban.Inhabited.StepTowerOfG
public import Balaban.Inhabited.StepTowerRenEndG
public import Balaban.Inhabited.StepTowerRenG
public import Balaban.Inhabited.TowerCoreRatesGeneral
public import Balaban.Inhabited.TowerCoreRatesVariantsGeneral
public import Balaban.Fluctuation.DetRateGeneral
public import Balaban.Fluctuation.RenormStrictData
public import Balaban.Fluctuation.RenormEndpointSharp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The producers of the general towers

One proof, `exists_stepTowerThetaG`, shows that `StepTowerThetaG d L N κmin` is inhabited for
every cover index `m₀ ≥ 1` and every requested output-rate floor: the rates are chosen first, then
the radius `r₀` is decreased (`StepTowerRenG.shrink`) until the endpoint, solution and chart-radius margins hold.
The producers of `StepTowerRenSolG`, `StepTowerRenEndG`, `StepTowerRenG` and the fixed `3, 3, 2` records
(`StepTower`, `StepTowerRen`, `StepTowerRenEnd`, `StepTowerRenSol`) are corollaries; so are the fixed
`StepTowerTheta` producers in `Balaban.Inhabited.StepTowerTheta`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep

/-- **The general record with the determinant data at the doubled radius is inhabited**, with
cover index `m₀` and output-rate floor `entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`.  This is the single
long producer of the chain. -/
theorem exists_stepTowerThetaG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerThetaG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec ∧
      (entropyLoss + c1 d L * κroot ≤ 150 * (aEnt d L + 2) → T.κ0 = aEnt d L + 2) := by
  classical
  obtain ⟨R, hm, hent, h0, hs, hC2, hdm2, hα2⟩ : ∃ R : StepTowerRenG d L N κmin, R.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * R.κdec ∧
      (entropyLoss + c1 d L * κroot ≤ 150 * (aEnt d L + 2) → R.κ0 = aEnt d L + 2) ∧
      bgK1 d L N * (xiC1 d * R.t) < deltaStar d L N ∧
      Nonempty (FlCore N (GpG d L 9 R.m₁ 1) (HmG d L 9 R.m₁ 1) 1 (νref L) R.c R.BG R.κ (2 * R.t)
        (levelKc d L) (Cchi d L) R.c₂ R.BG₂ (2 * R.t)) ∧
      decDomMargin d L N R.BG R.κ (xiC1 d * (2 * R.t)) < R.δc ∧
      K4 d L N R.BG R.κ * (xiC1 d * (2 * R.t)) < coerciveConst d / 2 := by
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
      hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0, hmin, hmar, hsol, hC2, hdm2, hα2⟩ :=
      tower_core_rates_two_general (d := d) (L := L) N hd hL (ν := νref L)
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
      D₀_le_star := hDs, D₁_le_star := hD1 }, rfl, ?_, ?_, hsol, hC2, hdm2, hα2⟩
    · show entropyLoss + c1 d L * κroot ≤ 3 / 2 * κdec
      rw [hκdecdef]
      linarith
    · intro h
      show κ0 = aEnt d L + 2
      rw [hκ0def]
      exact max_eq_left (by linarith)

  obtain ⟨hC₀⟩ := R.core
  have hd0 : 0 < d := by omega
  have hB1 := famConst_ge_one (L := L) hC₀.hS.fam.2.1 R.κ hd0
  have hK2 : 0 ≤ cK2' d L N (famConst d L R.BG R.κ) :=
    cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L R.BG R.κ) (by linarith)
  have hc6 : 0 < c6 d L N := c6_pos (d := d) (L := L) (N := N) hd0
  have hds : 0 < deltaStar d L N := deltaStar_pos (d := d) (L := L) (N := N) hd0
  have hsp : 0 < deltaStar d L N - bgK1 d L N * (xiC1 d * R.t) := by linarith
  have hK4 := K4_pos (d := d) (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1 hd0
  have hK1 := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have ht := R.t_pos
  have hcoef : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t := by
    positivity
  have hA : 0 ≤ cK2' d L N (famConst d L R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t) :=
    mul_nonneg hK2 hcoef
  set A := cK2' d L N (famConst d L R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t) with hAdef
  have hX : 0 < xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hP : 0 < min (c6 d L N) (min (deltaStar d L N - bgK1 d L N * (xiC1 d * R.t))
      (min (deltaStar d L N) 1)) := lt_min hc6 (lt_min hsp (lt_min hds one_pos))
  obtain ⟨r, hr0, hr1, -, hr2, -⟩ :=
    exists_radius_margins (A := A + 3 + 8 * R.t + xiK2 d L N * (3 / 2))
      (by positivity) hP hP R.r₀_pos R.r₀_pos
  have hm1 : (A + 3 + 8 * R.t + xiK2 d L N * (3 / 2)) * r ≤ c6 d L N :=
    hr2.trans (min_le_left _ _)
  have hm2 : (A + 3 + 8 * R.t + xiK2 d L N * (3 / 2)) * r ≤
      deltaStar d L N - bgK1 d L N * (xiC1 d * R.t) :=
    hr2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 : (A + 3 + 8 * R.t + xiK2 d L N * (3 / 2)) * r ≤ deltaStar d L N :=
    hr2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hm4 : (A + 3 + 8 * R.t + xiK2 d L N * (3 / 2)) * r ≤ 1 :=
    hr2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h1 : 0 ≤ A * r := mul_nonneg hA hr0.le
  have h2 : 0 ≤ R.t * r := mul_nonneg ht.le hr0.le
  have h3 : 0 ≤ xiK2 d L N * (3 / 2) * r := by positivity
  refine ⟨{ R.shrink r hr0 hr1 with
    end_margin := ?_
    sol_margin := hs
    sol_K := ?_
    sol_ζ := ?_
    core2 := hC2
    dom_margin2 := hdm2
    coer_margin2 := hα2
    r₀_xi := ?_ }, hm, hent, h0⟩
  · simp only [StepTowerRenG.shrink]
    have : A * r ≤ c6 d L N := by nlinarith
    calc _ = A * r := by rw [hAdef]; ring
      _ ≤ c6 d L N := this
  · simp only [StepTowerRenG.shrink]; nlinarith
  · simp only [StepTowerRenG.shrink]; nlinarith
  · simp only [StepTowerRenG.shrink]; nlinarith

/-- **The general record with the solution margins is inhabited**, with cover index `m₀` and
output-rate floor `entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`. -/
theorem exists_stepTowerRenSolG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerRenSolG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec ∧
      (entropyLoss + c1 d L * κroot ≤ 150 * (aEnt d L + 2) → T.κ0 = aEnt d L + 2) := by
  obtain ⟨T, hm, hent, h0⟩ :=
    exists_stepTowerThetaG d L N hd hL hN m₀ hm₀ κroot entropyLoss κmin
  exact ⟨T.toStepTowerRenSolG, hm, hent, h0⟩

/-- **The general record with the endpoint margin is inhabited**, with cover index `m₀` and
output-rate floor `entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`. -/
theorem exists_stepTowerRenEndG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerRenEndG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec ∧
      (entropyLoss + c1 d L * κroot ≤ 150 * (aEnt d L + 2) → T.κ0 = aEnt d L + 2) := by
  obtain ⟨T, hm, hent, h0⟩ :=
    exists_stepTowerRenSolG d L N hd hL hN m₀ hm₀ κroot entropyLoss κmin
  exact ⟨T.toStepTowerRenEndG, hm, hent, h0⟩

/-- **The general record with margins is inhabited**, with cover index `m₀` and output-rate floor
`entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`. -/
theorem exists_stepTowerRenG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerRenG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec ∧
      (entropyLoss + c1 d L * κroot ≤ 150 * (aEnt d L + 2) → T.κ0 = aEnt d L + 2) := by
  obtain ⟨T, hm, hent, h0⟩ :=
    exists_stepTowerRenEndG d L N hd hL hN m₀ hm₀ κroot entropyLoss κmin
  exact ⟨T.toStepTowerRenG, hm, hent, h0⟩

/-- **The record with the solution margins is inhabited** for every `κmin`. -/
theorem exists_stepTowerRenSol (κmin : ℝ) : Nonempty (StepTowerRenSol κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerRenSolG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerRenSolG.nonempty_fixed_of_three T (h0 (by simp; linarith)) hm

/-- The tower with the renormalization margins and `K₁ ξ₁ t < δ_*`. -/
theorem exists_stepTowerRen_sol (κmin : ℝ) :
    ∃ R : StepTowerRen κmin, bgK1 3 3 2 * (xiC1 3 * R.t) < deltaStar 3 3 2 := by
  obtain ⟨T⟩ := exists_stepTowerRenSol κmin
  exact ⟨T.toStepTowerRen, T.sol_margin⟩

/-- **The record with the endpoint margin is inhabited** for every `κmin`. -/
theorem exists_stepTowerRenEnd (κmin : ℝ) : Nonempty (StepTowerRenEnd κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerRenEndG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerRenEndG.nonempty_fixed_of_three T (h0 (by simp; linarith)) hm

/-- **The tower record is inhabited** for every lower bound `κmin`. -/
theorem exists_stepTower (κmin : ℝ) : Nonempty (StepTower κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerRenG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerG.nonempty_fixed_of_three T.toStepTowerG (h0 (by simp; linarith)) hm

/-- **The general tower record is inhabited** at `d = L = 3`, `N = 2` for every `κmin`. -/
theorem exists_stepTowerG_three (κmin : ℝ) : Nonempty (StepTowerG 3 3 2 κmin) :=
  (exists_stepTower κmin).map StepTower.toG

/-- **The record with margins is inhabited** for every lower bound `κmin`. -/
theorem exists_stepTowerRen (κmin : ℝ) : Nonempty (StepTowerRen κmin) := by
  obtain ⟨T, hm, -, h0⟩ := exists_stepTowerRenG 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin
  have := aEnt_nonneg 3 3
  exact StepTowerRenG.nonempty_fixed_of_three T (h0 (by simp; linarith)) hm

end Balaban.Inhabited
