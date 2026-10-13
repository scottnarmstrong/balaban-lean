/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.TowerCoreRatesRen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# The numerical tower with the renormalized-solution margin

`tower_core_rates_at_least_renSol` is `tower_core_rates_at_least_ren` with one more
eventual-at-zero inequality in the choice of `t`: `K₁ ξ₁ t < δ_*` (the margin `exists_isRenSol`
needs for the radius; `deltaStar_pos` gives the positive right-hand side).
`tower_core_rates_at_least_ren_of_renSol` recovers the landed theorem.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology

/-- `tower_core_rates_at_least_ren` with one more conjunct: the strict margin
`K₁ ξ₁ t < δ_*`. -/
theorem tower_core_rates_at_least_renSol (N : ℕ) {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt 3 3 + 1 ≤ κ0)
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
      0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst 3 3 BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 3 3 N BG κ * (xiC1 3 * t)) <
        deltaStar' 3 3 N (famConst 3 3 BG κ) (gamma1 3 / 8) ∧
      bgK1 3 3 N * (xiC1 3 * t) < deltaStar 3 3 N := by
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
  set κ0' : ℝ := 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec + 40000 +
    1 / thm73C3 3 3 N with hκ0'def
  set κ : ℝ := max κ0' κmin with hκdef
  have hinv : 0 ≤ 1 / thm73C3 3 3 N := by positivity
  have hcoef : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hκ1 : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec + 40000 ≤ κ := by
    refine le_trans ?_ (le_max_left _ _); rw [hκ0'def]; linarith
  have hκ2 : 1 / thm73C3 3 3 N ≤ κ := by
    refine le_trans ?_ (le_max_left _ _); rw [hκ0'def]; nlinarith [mul_nonneg hcoef hκdec0]
  have hκ3 : 40000 ≤ κ := by
    refine le_trans ?_ (le_max_left _ _); rw [hκ0'def]; nlinarith [mul_nonneg hcoef hκdec0]
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
  have hB1 : 0 ≤ famConst 3 3 BG κ := by
    have := famConst_ge_one (L := 3) hS.fam.2.1 κ (d := 3) (by norm_num); linarith
  have hDs' : 0 < deltaStar' 3 3 N (famConst 3 3 BG κ) (gamma1 3 / 8) :=
    deltaStar'_pos hB1 (by have := gamma1_pos (d := 3) (by norm_num); positivity)
  have e8 := ev_lt (f := fun t : ℝ => 2 * (K4 3 3 N BG κ * (xiC1 3 * t))) (by fun_prop)
    (c := deltaStar' 3 3 N (famConst 3 3 BG κ) (gamma1 3 / 8)) (by simpa using hDs')
  have e9 := ev_lt (f := fun t : ℝ => bgK1 3 3 N * (xiC1 3 * t)) (by fun_prop)
    (c := deltaStar 3 3 N) (by simpa using hDs)
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, hC, g1, g2, g3, g4, g5, g6, g7, g8, g9, ht0⟩ := (hev.and ((wk e1).and ((wk e2).and
    ((wk e3).and ((wk e4).and ((wk e5).and ((wk e6).and ((wk e7).and ((wk e8).and ((wk e9).and hpos)))))))))).exists
  have h343 : Real.log (9261 : ℝ) ≤ 9261 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have hlogκ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ 1) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 := by
    norm_num at h343 ⊢
    linarith
  have hκdec3 : 3 * κ0 + 3 ≤ κdec := by linarith [one_le_c1 3 3]
  refine ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, hC, hκ00, hκdec3,
    by linarith, by linarith, hlogκ, c7_le_thm73C3_of_large (by norm_num) hBG1 hκ2, hm3, g6, g7,
    hδcSX, g1.le, g2, g3.le, g4.le, g5.le, hκ0, by linarith [one_le_c1 3 3], hB0, le_max_right _ _, g8, g9⟩

/-- `tower_core_rates_at_least_ren` follows from `tower_core_rates_at_least_renSol`. -/
theorem tower_core_rates_at_least_ren_of_renSol (N : ℕ) {κ0 κdec : ℝ} (κmin : ℝ)
    (hκ0 : aEnt 3 3 + 1 ≤ κ0) (hκdec : 3 * κ0 + c1 3 3 + 5 ≤ κdec) :
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
      0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst 3 3 BG₂ κ ∧ κmin ≤ κ ∧
      2 * (K4 3 3 N BG κ * (xiC1 3 * t)) <
        deltaStar' 3 3 N (famConst 3 3 BG κ) (gamma1 3 / 8) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, -⟩ :=
    tower_core_rates_at_least_renSol N κmin hκ0 hκdec
  exact ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht, hC, h1, h2, h3, h4', h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

end Balaban.Inhabited
