/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenEnd
public import Balaban.Inhabited.TowerCoreRatesRenSol
public import Balaban.Fluctuation.RenormExpLemma35
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower with the renormalized solution

`StepTowerRenSol κmin` extends `StepTowerRenEnd κmin` by the margin `K₁ ξ₁ t < δ_*` and the two
radius margins `K₁ ξ₁ t + 3 r₀ ≤ δ_*`, `8 t r₀ ≤ δ_*` of `exists_isRenSol` at `r_F = r₀`.
`exists_stepTowerRenSol` shows that the record is inhabited for every `κmin`.  At every scale,
`exists_isRenSol_scale_of_tower` gives the renormalized solution `F` and
`renEndpoint_scale_of_tower` the endpoint `s = 1` with no hypothesis besides the tower and the
scale conditions.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- The shared tower with the endpoint margin and the margins of the renormalized solution. -/
structure StepTowerRenSol (κmin : ℝ) extends StepTowerRenEnd κmin where
  sol_margin : bgK1 3 3 2 * (xiC1 3 * t) < deltaStar 3 3 2
  sol_K : bgK1 3 3 2 * (xiC1 3 * t) + 3 * r₀ ≤ deltaStar 3 3 2
  sol_ζ : 8 * t * r₀ ≤ deltaStar 3 3 2

/-- The tower with the renormalization margins and `K₁ ξ₁ t < δ_*`. -/
theorem exists_stepTowerRen_sol (κmin : ℝ) :
    ∃ R : StepTowerRen κmin, bgK1 3 3 2 * (xiC1 3 * R.t) < deltaStar 3 3 2 := by
  classical
  obtain ⟨-, δ, δ', -, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, -⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  set κ0 : ℝ := aEnt 3 3 + 2 with hκ0def
  set κdec : ℝ := 100 * (κ0 + c1 3 3 + 10) with hκdecdef
  set κ' : ℝ := 3 / 2 * κdec + κ0 + 1 with hκ'def
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hCn, hκ0n, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0, hmin, hmar, hsol⟩ :=
    tower_core_rates_at_least_renSol 2 κmin (κ0 := κ0) (κdec := κdec) (by linarith) (by linarith)
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
  refine ⟨StepTowerRen.mk {
    κ0 := κ0, κdec := κdec, κ' := κ', κ0_eq := rfl, κdec_eq := rfl, κ'_eq := rfl
    m₁ := m₁, c := c, BG := BG, κ := κ, t := t, c₂ := c₂, BG₂ := BG₂, δc := δc, δ := δ, δ' := δ'
    m₁_four := h4, t_pos := ht0, core := ⟨hC⟩, κ0_nonneg := hκ0n, κdec_lower := hκdec
    κ_lower := hκ, κ_one := h1, κ_log := hlog, c7_cap := hc7, large_block := hMX
    dom_margin := hdm, coer_margin := hα, δc_small := hsmX, t_cap := g1, bg0_cap := g2
    cK2_cap := g3, cK2'_cap := g4, bg1_cap := g5, κ0_ent := hκE, rate_rel := hκa
    fam_nonneg := hB0, κmin_le := hmin, δ_pos := hδ, δ_small := hsm, δ'_pos := hδ'0
    δ'_cap := hδ'a, δ'_step := hδ'b, δ'_coer := hδ'c, block_base := hbig, xi_small := hxi1
    rho_nonneg := hρ, det_z := hz, det_rate := hrate }
    hmar r₀ hr0 hr1 hD0 hDs hD1, hsol⟩

/-- **The record with the solution margins is inhabited** for every `κmin`. -/
theorem exists_stepTowerRenSol (κmin : ℝ) : Nonempty (StepTowerRenSol κmin) := by
  obtain ⟨R, hs⟩ := exists_stepTowerRen_sol κmin
  have hd : 0 < 3 := by norm_num
  obtain ⟨hC₀⟩ := R.core
  have hB1 := famConst_ge_one (L := 3) hC₀.hS.fam.2.1 R.κ hd
  have hK2 : 0 ≤ cK2' 3 3 2 (famConst 3 3 R.BG R.κ) :=
    cK2'_nonneg (d := 3) (L := 3) (N := 2) (B := famConst 3 3 R.BG R.κ) (by linarith)
  have hc6 : 0 < c6 3 3 2 := c6_pos (d := 3) (L := 3) (N := 2) hd
  have hds : 0 < deltaStar 3 3 2 := deltaStar_pos (d := 3) (L := 3) (N := 2) hd
  have hsp : 0 < deltaStar 3 3 2 - bgK1 3 3 2 * (xiC1 3 * R.t) := by linarith
  have hA : 0 ≤ cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) :=
    mul_nonneg hK2 R.coef_nonneg
  have ht := R.t_pos
  set A := cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t) with hAdef
  have hP : 0 < min (c6 3 3 2) (min (deltaStar 3 3 2 - bgK1 3 3 2 * (xiC1 3 * R.t))
      (deltaStar 3 3 2)) := lt_min hc6 (lt_min hsp hds)
  obtain ⟨r, hr0, hr1, -, hr2, -⟩ := exists_radius_margins (A := A + 3 + 8 * R.t)
    (by positivity) hP hP R.r₀_pos R.r₀_pos
  have hm1 := (min_le_left _ _).trans' hr2
  have hm2 : (A + 3 + 8 * R.t) * r ≤ deltaStar 3 3 2 - bgK1 3 3 2 * (xiC1 3 * R.t) :=
    hr2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 : (A + 3 + 8 * R.t) * r ≤ deltaStar 3 3 2 :=
    hr2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1 : 0 ≤ A * r := mul_nonneg hA hr0.le
  have h2 : 0 ≤ R.t * r := mul_nonneg ht.le hr0.le
  refine ⟨{ R.shrink r hr0 hr1 with end_margin := ?_, sol_margin := hs, sol_K := ?_, sol_ζ := ?_ }⟩
  · simp only [StepTowerRen.shrink]
    have : A * r ≤ c6 3 3 2 := by nlinarith
    calc _ = A * r := by rw [hAdef]; ring
      _ ≤ c6 3 3 2 := this
  · simp only [StepTowerRen.shrink]; nlinarith
  · simp only [StepTowerRen.shrink]; nlinarith

/-- **`IsRenSol` at every scale of the tower**: the renormalized solution at radius `r₀` and
bound `B = 8 t`. -/
theorem exists_isRenSol_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
      ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F := by
  have hC := R.flCore_scale k hk N₁ hN hν0 hν
  have hHB := bgHyp_lv (k := k) R.m₁ hν0 hν
  exact exists_isRenSol hHB R.t_pos (R.r₀_le) hC.small1 (hC.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) R.sol_K R.sol_ζ

/-- **The endpoint at every scale of the tower with the solution margins**: no hypothesis besides
the tower and the scale conditions. -/
theorem renEndpoint_scale_of_tower {κmin : ℝ} (R : StepTowerRenSol κmin) (k : ℕ)
    (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (X₁ : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ (F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ))
      (Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) × ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ)),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t R.t R.r₀
        (8 * R.t) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) X₁ → ℂ) (fun _ => Real.exp R.κ)) ∧
      ∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν R.t D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ) := by
  obtain ⟨F, hF⟩ := exists_isRenSol_scale_of_tower R k hk N₁ hN hν0 hν
  obtain ⟨Fcut, h1, h2⟩ := renDec_one_unique_sharp_scale_of_tower R.toStepTowerRenEnd k hk N₁ hN
    hν0 hν X₁ hF le_rfl
  exact ⟨F, Fcut, hF, h1, h2⟩

end Balaban.Inhabited
