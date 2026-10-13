/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelStepSettingGeneral
public import Balaban.Inhabited.TowerCoreRatesGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A consecutive level pair for general dimension `d` and block size `L`

The separation parameter `rhoSepG d L m₁` is
`bgR0 d L + 4 d L · L^{m₁} + 4 d L³ · L^{m₁} + 1 + 2 d log L / (agmonRate d / 16)`.
It satisfies the separation inequalities of the decoupled setting and the operator setting for
all `d ≥ 3`, `L ≥ 3`, and equals the landed `rhoSep m₁` at `d = L = 3`.  With it the pair
`GpG`, `HmG` (the generating sets of levels `k + 1` and `k` on the torus of side `N₁ L^{m₁}`)
carries `DGSetting` and `Dec2.OpSetting` (`dgSetting_lvG`, `opSetting_lvG`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Finset

namespace LevelStep

/-- The separation parameter for dimension `d`, block size `L` and scale `m₁`. -/
noncomputable def rhoSepG (d L m₁ : ℕ) : ℝ :=
  bgR0 d L + 4 * d * L * (L : ℝ) ^ m₁ + 4 * d * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ + 1 +
    2 * d * Real.log L / (agmonRate d / 16)

section Ineq

variable {d L : ℕ} (m₁ : ℕ)

theorem bgR0_nonneg_G : 0 ≤ bgR0 d L := by
  unfold bgR0; exact le_trans (by positivity) (le_max_left _ _)

theorem rhoSepG_tail_nonneg (hd : 3 ≤ d) (hL : 3 ≤ L) :
    0 ≤ 2 * (d : ℝ) * Real.log L / (agmonRate d / 16) := by
  have := agmonRate_pos (d := d) (by omega)
  have : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
  positivity

theorem rhoSepG_terms_nonneg (hd : 3 ≤ d) (hL : 3 ≤ L) :
    0 ≤ 4 * (d : ℝ) * L * (L : ℝ) ^ m₁ ∧ 0 ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ := by
  constructor <;> positivity

theorem bgR0_le_rhoSepG (hd : 3 ≤ d) (hL : 3 ≤ L) : bgR0 d L ≤ rhoSepG d L m₁ := by
  have := rhoSepG_tail_nonneg (d := d) hd hL
  have := rhoSepG_terms_nonneg (d := d) (L := L) m₁ hd hL
  unfold rhoSepG; linarith

theorem cover_le_rhoSepG (hd : 3 ≤ d) (hL : 3 ≤ L) :
    4 * (d : ℝ) * L * (L : ℝ) ^ m₁ ≤ rhoSepG d L m₁ := by
  have := rhoSepG_tail_nonneg (d := d) hd hL
  have := rhoSepG_terms_nonneg (d := d) (L := L) m₁ hd hL
  have := bgR0_nonneg_G (d := d) (L := L)
  unfold rhoSepG; linarith

theorem sep_le_rhoSepG (hd : 3 ≤ d) (hL : 3 ≤ L) :
    2 * (d : ℝ) * Real.log L ≤ agmonRate d / 16 * (rhoSepG d L m₁ - 1) := by
  have ha := agmonRate_pos (d := d) (by omega)
  have hq : 2 * (d : ℝ) * Real.log L / (agmonRate d / 16) ≤ rhoSepG d L m₁ - 1 := by
    have := rhoSepG_terms_nonneg (d := d) (L := L) m₁ hd hL
    have := bgR0_nonneg_G (d := d) (L := L)
    unfold rhoSepG; linarith
  rw [div_le_iff₀ (by positivity)] at hq
  linarith

theorem radius_le_rhoSepG (hd : 3 ≤ d) (hL : 3 ≤ L) :
    4 * (d : ℝ) * (L : ℝ) ^ 3 * (L : ℝ) ^ m₁ ≤ rhoSepG d L m₁ - 1 := by
  have := rhoSepG_tail_nonneg (d := d) hd hL
  have := rhoSepG_terms_nonneg (d := d) (L := L) m₁ hd hL
  have := bgR0_nonneg_G (d := d) (L := L)
  unfold rhoSepG; linarith

/-- At `d = L = 3` the general separation is the landed one. -/
theorem rhoSepG_three : rhoSepG 3 3 m₁ = rhoSep m₁ := by
  unfold rhoSepG rhoSep
  push_cast
  ring

end Ineq

section Pair

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ν : ℝ}

/-- The top generating set `𝔹_{k+1}` at the separation `rhoSepG d L m₁`. -/
noncomputable abbrev GpG (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (rhoSepG d L m₁) :=
  lvTopG d L N₁ m₁ k (rhoSepG d L m₁)

/-- The lower generating set `𝔹_k` at the separation `rhoSepG d L m₁`. -/
noncomputable abbrev HmG (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (rhoSepG d L m₁) :=
  lvLowG d L N₁ m₁ k (rhoSepG d L m₁)

/-- **`DGSetting` of the full level `𝔹_{k+1}`**, general `d`, `L`. -/
theorem dgSetting_lvG (hd : 3 ≤ d) (hL : 3 ≤ L) (hm : 4 ≤ m₁) (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    DGSetting (GpG d L N₁ m₁ k) (compWeight L 1) ν where
  hd := hd
  hL := hL
  aligned :=
    { two_le := by omega
      dvd := dvd_mul_left _ _
      union := fun j _ hj x x' _ => by simp [lvTopG_Ω, hj] }
  hM := by
    calc 4 * L ^ 2 ≤ L ^ 2 * L ^ 2 := by
          have : 4 ≤ L ^ 2 := by nlinarith
          exact Nat.mul_le_mul_right _ this
      _ = L ^ 4 := by ring
      _ ≤ L ^ m₁ := Nat.pow_le_pow_right (by omega) hm
  cover_sep := cover_le_rhoSepG m₁ hd hL
  sep := sep_le_rhoSepG m₁ hd hL
  weights := isAdmissibleWeights_compWeight hL (by norm_num) (by norm_num) _
  mass := hν0
  massLe := massLe_lvG hν
  big := hN₁

/-- **`OpSetting` of the lower level `𝔹_k`**, general `d`, `L`. -/
theorem opSetting_lvG (hd : 3 ≤ d) (hL : 3 ≤ L) (hm : 4 ≤ m₁) (hN₁ : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    Dec2.OpSetting (HmG d L N₁ m₁ k) (compWeight L 1) ν :=
  { hd := hd, hL := hL, mass := hν0, massLe := massLe_lvG hν,
    weights := (dgSetting_lvG (k := k) (N₁ := N₁) hd hL hm hN₁ hν0 hν).weights,
    sep := sep_le_rhoSepG m₁ hd hL }

/-- **The pair hypothesis of `tower_core_rates_general_of_pair`**, discharged at `N₁ = 9`,
level `k = 1`, `n = 1`, for general `d ≥ 3`, `L ≥ 3` and every mass `0 ≤ ν ≤ L^{-4}`. -/
theorem hpair_lvG (hd : 3 ≤ d) (hL : 3 ≤ L) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1) :
    ∀ m₁ : ℕ, 4 ≤ m₁ → ∃ n : ℕ,
      Nonempty (DGSetting (GpG d L 9 m₁ 1) (compWeight L 1) ν) ∧
      Nonempty (Dec2.OpSetting (HmG d L 9 m₁ 1) (compWeight L 1) ν) ∧
      IsLevel (HmG d L 9 m₁ 1) n ∧ IsLevel (GpG d L 9 m₁ 1) (n + 1) ∧
      BgHyp d L (1 + 1) (rhoSepG d L m₁) (compWeight L 1) ν :=
  fun m₁ hm => ⟨1, ⟨dgSetting_lvG hd hL hm (by norm_num) hν0 hν⟩,
    ⟨opSetting_lvG hd hL hm (by norm_num) hν0 hν⟩, isLevel_lvLowG le_rfl, isLevel_lvTopG,
    bgHyp_lvG hd hL (bgR0_le_rhoSepG m₁ hd hL) hν0 hν⟩

end Pair

end LevelStep

open LevelStep in
/-- **The core rates of the tower at general `(d, L, N)`**, unconditional: the level pair of
`tower_core_rates_general_of_pair` is `GpG d L 9 m₁ 1`, `HmG d L 9 m₁ 1`, with mass
`0 ≤ ν ≤ L^{-4}` and weights `compWeight L 1`. -/
theorem tower_core_rates_general {d L : ℕ} [NeZero L] (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L)
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (1 + 1)) ≤ 1)
    {κ0 κdec : ℝ} (κmin : ℝ) (hκ0 : aEnt d L + 1 ≤ κ0)
    (hκdec : 3 * κ0 + c1 d L + 5 ≤ κdec) :
    ∃ (m₁ : ℕ) (c BG κ t c₂ BG₂ δc : ℝ),
      4 ≤ m₁ ∧ 0 < t ∧
      Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 ν c BG κ t (levelKc d L)
        (Cchi d L) c₂ BG₂ t) ∧
      0 ≤ κ0 ∧ 3 * κ0 + 3 ≤ κdec ∧
      4 * ((d : ℕ) : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ ∧ 1 ≤ (κ / 2 - 1) / 2 ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 ∧
      c7 d L N BG κ ≤ thm73C3 d L N ∧
      cstarX d L * Real.exp (N0 d L * κ) ≤ ((L : ℕ) : ℝ) ^ m₁ ∧
      decDomMargin d L N BG κ (xiC1 d * t) < δc ∧
      K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2 ∧
      δc ^ 2 * smallConstX d L κ ≤ 1 / 4 ∧
      2 * t ≤ deltaStar d L N ∧ cK2 d L N * (2 * t) < bgC0 d L N / 2 ∧
      cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8) ∧
      2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N ∧
      aEnt d L + 1 ≤ κ0 ∧
      0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧ 0 ≤ famConst d L BG₂ κ ∧ κmin ≤ κ :=
  tower_core_rates_general_of_pair (N₁ := 9) (K := 1 + 1) N hd hL
    (fun m₁ => GpG d L 9 m₁ 1) (fun m₁ => HmG d L 9 m₁ 1) (a₁ := 1) (ν := ν)
    (hpair_lvG hd hL hν0 hν) κmin hκ0 hκdec

end Balaban.Inhabited
