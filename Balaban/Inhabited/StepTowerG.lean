/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelPairGeneral
public import Balaban.Fluctuation.StepRegWitnessGeneral
public import Balaban.Fluctuation.DetCauchyGraph

/-!
# The general numerical tower for one witness step

`StepTowerG d L N κmin` has the fields of the fixed `StepTower κmin` for general dimension `d`,
block size `L` and number of components `N`, with one amendment: the equality `κ0 = a_Ent + 2`
is replaced by the lower bound `a_Ent d L + 2 ≤ κ0`.  An inhabitant certifies the numerical and
core package of one step, nothing about the root.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

/-- The reference mass `L⁻⁴` of the general core (equal to `1/81` at `L = 3`). -/
noncomputable def νref (L : ℕ) : ℝ := 1 / (L : ℝ) ^ 4

/-- The general numerical tower of one witness step at dimension `d`, block size `L`, `N`
components, decoupling rate `κ ≥ κmin`.  An inhabitant certifies the numerical and core package
of one step, nothing about the root. -/
structure StepTowerG (d L N : ℕ) [NeZero L] (κmin : ℝ) where
  hd : 3 ≤ d
  hL : 3 ≤ L
  hN : 2 ≤ N
  (κ0 κdec κ' : ℝ)
  κ0_ge : aEnt d L + 2 ≤ κ0
  κdec_eq : κdec = 100 * (κ0 + c1 d L + 10)
  κ'_eq : κ' = 3 / 2 * κdec + κ0 + 1
  m₁ : ℕ
  m₀ : ℕ
  m₀_pos : 1 ≤ m₀
  (c BG κ t c₂ BG₂ δc δ δ' : ℝ)
  m₁_four : 4 ≤ m₁
  t_pos : 0 < t
  core : Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1)
    1 (νref L) c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t)
  κ0_nonneg : 0 ≤ κ0
  κdec_lower : 3 * κ0 + 3 ≤ κdec
  κ_lower : 4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ
  κ_one : 1 ≤ (κ / 2 - 1) / 2
  κ_log : Real.log (((((2 * L + 1) ^ d : ℕ) : ℝ)) *
    ((((L ^ m₀) ^ d : ℕ) : ℝ))) ≤ (κ / 2 - 1) / 2
  c7_cap : c7 d L N BG κ ≤ thm73C3 d L N
  large_block : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  dom_margin : decDomMargin d L N BG κ (xiC1 d * t) < δc
  coer_margin : K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2
  δc_small : δc ^ 2 * smallConstX d L κ ≤ 1 / 4
  t_cap : 2 * t ≤ deltaStar d L N
  bg0_cap : cK2 d L N * (2 * t) < bgC0 d L N / 2
  cK2_cap : cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  cK2'_cap : cK2' d L N (famConst d L BG₂ κ) * t ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  bg1_cap : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N
  κ0_ent : aEnt d L + 1 ≤ κ0
  rate_rel : 0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1
  fam_nonneg : 0 ≤ famConst d L BG₂ κ
  κmin_le : κmin ≤ κ
  δ_pos : 0 < δ
  δ_small : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4
  δ'_pos : 0 < δ'
  δ'_cap : δ' ≤ thm73C3 d L N / 2
  δ'_step : bgK1 d L N * δ' ≤ δ / 4
  δ'_coer : bgK1 d L N * δ' ≤ coerciveConst d / 4
  block_base : cstarX d L ≤ (L : ℝ) ^ m₁
  xi_small : xiC1 d * t ≤ 1
  rho_nonneg : 0 ≤ rho4 d L N BG κ
  det_z : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1
  det_rate : κ' ≤ (κ - Real.log 2 -
    2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * (d : ℝ) * (L : ℝ))

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- The input `κ₀ ≥ a_Ent + 1` of the landed scale theorems. -/
theorem hκ0 : aEnt d L + 1 ≤ T.κ0 := T.κ0_ent

/-- The input `a_Ent + 2 ≤ κ₀`. -/
theorem κ0_two : aEnt d L + 2 ≤ T.κ0 := T.κ0_ge

/-- The input `κ_dec ≥ 3 κ₀ + c₁ + 5` of the landed scale theorems. -/
theorem hκdec : 3 * T.κ0 + c1 d L + 5 ≤ T.κdec := by
  have := one_le_c1 d L
  have := T.κ0_nonneg
  rw [T.κdec_eq]; linarith

/-- The rate arithmetic: `min (2 κ_dec) κ' - κ₀ - 1 = (3/2) κ_dec`. -/
theorem outRate_eq : min (2 * T.κdec) T.κ' - T.κ0 - 1 = 3 / 2 * T.κdec := by
  have h1 := T.κ'_eq
  have h2 := T.κdec_lower
  have h3 := T.κ0_nonneg
  have : T.κ' ≤ 2 * T.κdec := by linarith
  rw [min_eq_right this]; linarith

/-- The rate of the bound of the observable coefficient family is `(3/2) κ_dec`. -/
theorem obsFamilyRate_eq :
    min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ' = 3 / 2 * T.κdec := by
  rw [T.outRate_eq]
  have h1 := T.κ'_eq
  have h2 := T.κdec_lower
  have h3 := T.κ0_nonneg
  exact min_eq_left (by linarith)

end StepTowerG

end Balaban.Inhabited
