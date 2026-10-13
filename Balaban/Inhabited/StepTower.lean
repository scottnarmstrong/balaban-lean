/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.TowerCoreRatesAtLeast
public import Balaban.Inhabited.DetOutputTermsWitness
public import Balaban.Fluctuation.StepRegWitness
public import Balaban.Inhabited.StepTowerG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared numerical tower for the witness step (`d = L = 3`, `N = 2`)

`StepTower κmin` bundles, once and for all, the output of `tower_core_rates_at_least` at the
physical rates `κ₀ = a_Ent + 2`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`, the radii
`δ, δ'` of `exists_witness_params`, and the quantities derived from them that the per-scale
theorems use.  `exists_stepTower` shows that the record is inhabited for every `κmin`.

This file contains the tower only.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology LevelStep

/-- The shared numerical tower at `N = 2`, with decoupling rate `κ ≥ κmin`. -/
structure StepTower (κmin : ℝ) where
  (κ0 κdec κ' : ℝ)
  κ0_eq : κ0 = aEnt 3 3 + 2
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

/-- **The bridge**: the fixed `3, 3, 2` tower is a general tower. -/
noncomputable def StepTower.toG {κmin : ℝ} (T : StepTower κmin) : StepTowerG 3 3 2 κmin where
  hd := le_rfl
  hL := le_rfl
  hN := le_rfl
  κ0 := T.κ0
  κdec := T.κdec
  κ' := T.κ'
  κ0_ge := le_of_eq T.κ0_eq.symm
  κdec_eq := T.κdec_eq
  κ'_eq := T.κ'_eq
  m₁ := T.m₁
  m₀ := 1
  m₀_pos := le_rfl
  c := T.c
  BG := T.BG
  κ := T.κ
  t := T.t
  c₂ := T.c₂
  BG₂ := T.BG₂
  δc := T.δc
  δ := T.δ
  δ' := T.δ'
  m₁_four := T.m₁_four
  t_pos := T.t_pos
  core := flCore_three_transport T.core
  κ0_nonneg := T.κ0_nonneg
  κdec_lower := T.κdec_lower
  κ_lower := T.κ_lower
  κ_one := T.κ_one
  κ_log := by simpa using T.κ_log
  c7_cap := T.c7_cap
  large_block := T.large_block
  dom_margin := T.dom_margin
  coer_margin := T.coer_margin
  δc_small := T.δc_small
  t_cap := T.t_cap
  bg0_cap := T.bg0_cap
  cK2_cap := T.cK2_cap
  cK2'_cap := T.cK2'_cap
  bg1_cap := T.bg1_cap
  κ0_ent := T.κ0_ent
  rate_rel := T.rate_rel
  fam_nonneg := T.fam_nonneg
  κmin_le := T.κmin_le
  δ_pos := T.δ_pos
  δ_small := T.δ_small
  δ'_pos := T.δ'_pos
  δ'_cap := T.δ'_cap
  δ'_step := T.δ'_step
  δ'_coer := T.δ'_coer
  block_base := T.block_base
  xi_small := T.xi_small
  rho_nonneg := T.rho_nonneg
  det_z := T.det_z
  det_rate := by
    have e : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
    rw [e]; exact T.det_rate

namespace StepTower

variable {κmin : ℝ} (T : StepTower κmin)

@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_c : T.toG.c = T.c := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_c₂ : T.toG.c₂ = T.c₂ := rfl
@[simp] theorem toG_BG₂ : T.toG.BG₂ = T.BG₂ := rfl
@[simp] theorem toG_δc : T.toG.δc = T.δc := rfl
@[simp] theorem toG_δ : T.toG.δ = T.δ := rfl
@[simp] theorem toG_δ' : T.toG.δ' = T.δ' := rfl

end StepTower

namespace StepTower

variable {κmin : ℝ} (T : StepTower κmin)

/-- The input `κ₀ ≥ a_Ent + 1` of the landed scale theorems. -/
theorem hκ0 : aEnt 3 3 + 1 ≤ T.κ0 := T.toG.hκ0

/-- The input `a_Ent + 2 ≤ κ₀` of `rootUnion_entropy` (`notes/phase1/TOWERJOIN.md` §1). -/
theorem κ0_two : aEnt 3 3 + 2 ≤ T.κ0 := T.toG.κ0_two

/-- The input `κ_dec ≥ 3 κ₀ + c₁ + 5` of the landed scale theorems. -/
theorem hκdec : 3 * T.κ0 + c1 3 3 + 5 ≤ T.κdec := T.toG.hκdec

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
