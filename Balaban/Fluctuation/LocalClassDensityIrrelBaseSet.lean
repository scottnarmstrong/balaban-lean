/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.LocalClassDensityIrrelAux
public import Balaban.Inhabited.LevelCoversDef
public import Balaban.Inhabited.StepTowerCollarBgSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The base settings of the step from the tower (`LocalClassDensityIrrelBaseSet`)

For the step `T.step k hk N₁ ν β p₁` of a tower `T`, with the scale record `StepScaleData`
(whose `FlCore` carries the `DecSpecs`, `DGSetting`, `BgHyp`, the block-size and the
`Dec2` data of the step), the numerical conditions `ChainNum` and `FlNum` of the base radius
`ε' = T.t`, `r₀ = 324`, and the generating set `Gk₀ = Gj₀ = 𝔹_k` (the whole-lattice set of level
`k`), the base settings of the class chain hold with `X₁f' = X₀' =` the whole torus:

* `step_bgSetting_base`: `BgSetting` for the step;
* `step_flSetting_base`: `FlSetting` for the step;
* `rhoSep_le_minSep_of_four`: `rhoSep m₁ ≤ minSep 3 (3^(m₁+4))` for `m₁ ≥ 4`;
* `rhoSep_numeric_of_four`: the inequality `bgR0 3 3 + 1 + tail ≤ 855 · 3^{m₁}` behind it.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Finset

/-- The numerical constants `bgR0 3 3`, `agmonRate 3`: `bgR0 3 3 + 1 + 6 log 3 / (agmonRate 3 / 16)
≤ 855 · 3^{m₁}` for `m₁ ≥ 4`. -/
theorem rhoSep_numeric_of_four {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    bgR0 3 3 + 1 + 6 * Real.log 3 / (agmonRate 3 / 16) ≤ 855 * (3 : ℝ) ^ m₁ := by
  have hlog : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
    linarith
  have hlog0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hag : agmonRate 3 = 1 / 144 := by
    unfold agmonRate poincareConst
    norm_num [min_def]
  have hR0 : bgR0 3 3 ≤ 6913 := by
    unfold bgR0
    rw [hag]
    refine max_le (by norm_num) ?_
    push_cast
    norm_num
    nlinarith
  have htail : 6 * Real.log 3 / (agmonRate 3 / 16) ≤ 27648 := by
    rw [hag]
    norm_num
    nlinarith
  have h81 : (81 : ℝ) ≤ 3 ^ m₁ := by
    have : (3 : ℝ) ^ 4 ≤ 3 ^ m₁ := pow_le_pow_right₀ (by norm_num) h4
    norm_num at this
    exact this
  linarith

/-- `rhoSep m₁ ≤ minSep 3 (3^(m₁+4))` for `m₁ ≥ 4`. -/
theorem rhoSep_le_minSep_of_four {m₁ : ℕ} (h4 : 4 ≤ m₁) :
    Localization.I5Inhabited.rhoSep m₁ ≤ Balaban.LargeField.minSep 3 (3 ^ (m₁ + 4)) :=
  rhoSep_le_minSep_three (rhoSep_numeric_of_four h4)

section Rate

/-- **The rate condition of the labels gives the lower bounds the chain needs, general `d`, `L`.**
For a class block index `m₀ ≥ max 1 d`, a tower decoupling rate `κT ≥ 3` and a label rate `κdec` with
`(2 κT - 1) A + 1 ≤ 2 κdec`, `A = L^{m₀-1} + 2 d L^{m₀} (L^{m₀-1})^d c₁`, `c₁ ≥ 1`: `κT ≤ κdec`, and
if also `4 d (2L+1)^d κdec ≤ κ` then `log ((2L+1)^d (L^{m₀})^d) ≤ (κ/2 - 1)/2`. -/
theorem rate_consequencesG {d L m₀ : ℕ} (hd : 3 ≤ d) (hL : 2 ≤ L) (hm1 : 1 ≤ m₀) (hmd : d ≤ m₀)
    {κ κT κdec c₁ : ℝ} (hT : 3 ≤ κT) (hc : 1 ≤ c₁)
    (h4 : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ)
    (hr : (2 * κT - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) * (L : ℝ) ^ m₀ *
          ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c₁) + 1 ≤ 2 * κdec) :
    κT ≤ κdec ∧
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hd1 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set w : ℝ := (L : ℝ) ^ (m₀ - 1) with hw
  have hw1 : 1 ≤ w := one_le_pow₀ hL1
  have hLm : (L : ℝ) ^ m₀ = L * w := by
    rw [hw, ← pow_succ']
    congr 1
    omega
  have hwd : (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) = w ^ d := by
    rw [hw]; push_cast; rfl
  rw [hLm, hwd] at hr
  have hwpos : 0 < w := by linarith
  have hwd1 : 1 ≤ w ^ d := one_le_pow₀ hw1
  set A : ℝ := w + 2 * (d : ℝ) * (L * w) * w ^ d * c₁ with hA
  have hA1 : 1 ≤ A := by
    have : 0 ≤ 2 * (d : ℝ) * (L * w) * w ^ d * c₁ := by positivity
    linarith
  have hT5 : 5 ≤ 2 * κT - 1 := by linarith
  have hkd : (2 * κT - 1) * A + 1 ≤ 2 * κdec := hr
  refine ⟨by nlinarith, ?_⟩
  -- the logarithm
  have hX0 : 0 < (((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ) := by positivity
  refine (Real.log_le_sub_one_of_pos hX0).trans ?_
  have hkdec : 5 / 2 * A ≤ κdec := by nlinarith
  have hP : (1 : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hAlow : 2 * (d : ℝ) * (L * w) * w ^ d ≤ A := by
    have : 2 * (d : ℝ) * (L * w) * w ^ d ≤ 2 * (d : ℝ) * (L * w) * w ^ d * c₁ := by
      have h0 : 0 ≤ 2 * (d : ℝ) * (L * w) * w ^ d := by positivity
      nlinarith
    linarith
  have hLd : (L : ℝ) ^ d ≤ w * L := by
    have : (L : ℝ) ^ d ≤ (L : ℝ) ^ (m₀ - 1 + 1) := pow_le_pow_right₀ hL1 (by omega)
    rw [pow_succ] at this
    exact this
  have hLmd : (((L ^ m₀) ^ d : ℕ) : ℝ) = (L : ℝ) ^ d * w ^ d := by
    push_cast
    rw [hLm, mul_pow]
  set P : ℝ := (((2 * L + 1) ^ d : ℕ) : ℝ) with hPdef
  rw [hLmd]
  have hPpos : 0 < P := by linarith
  have hLdw : (L : ℝ) ^ d * w ^ d ≤ (w * L) * w ^ d :=
    mul_le_mul_of_nonneg_right hLd (by positivity)
  have hdd : (0 : ℝ) < d := by linarith
  have hq : 0 < P * (L * w * w ^ d) := by positivity
  have hk1 : 4 * d * P * κdec ≤ κ := h4
  have hk2 : 4 * d * P * (5 / 2 * A) ≤ 4 * d * P * κdec := by
    have : 0 ≤ 4 * (d : ℝ) * P := by positivity
    exact mul_le_mul_of_nonneg_left hkdec this
  have hk3 : 4 * d * P * (5 / 2 * (2 * (d : ℝ) * (L * w) * w ^ d)) ≤ 4 * d * P * (5 / 2 * A) := by
    have : 0 ≤ 4 * (d : ℝ) * P := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) this
  have hk4 : 20 * (d : ℝ) ^ 2 * (P * (L * w * w ^ d)) ≤ κ := by nlinarith
  have hX1 : P * ((L : ℝ) ^ d * w ^ d) ≤ P * (L * w * w ^ d) := by
    have := mul_le_mul_of_nonneg_left hLdw hPpos.le
    calc P * ((L : ℝ) ^ d * w ^ d) ≤ P * ((w * L) * w ^ d) := this
      _ = P * (L * w * w ^ d) := by ring
  have hdd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hdd2 hq.le]

/-- **The rate condition of the labels gives the lower bounds the chain needs.**  For a class
block index `m₀ ≥ 7`, a tower decoupling rate `κT ≥ 3` and a label rate `κdec` with
`(2 κT - 1) A + 1 ≤ 2 κdec`, `A = 3^{m₀-1} + 2·3·3^{m₀}·(3^{m₀-1})^3 c₁`, `c₁ ≥ 1`: `κT ≤ κdec`, and
if also `4·3·7^3 κdec ≤ κ` then `log (7^3 (3^{m₀})^3) ≤ (κ/2 - 1)/2`. -/
theorem rate_consequences {m₀ : ℕ} (hm : 7 ≤ m₀) {κ κT κdec c₁ : ℝ} (hT : 3 ≤ κT) (hc : 1 ≤ c₁)
    (h4 : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ)
    (hr : (2 * κT - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
          ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c₁) + 1 ≤ 2 * κdec) :
    κT ≤ κdec ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2 :=
  rate_consequencesG (d := 3) (L := 3) (by norm_num) (by norm_num) (by omega) (by omega) hT hc h4 hr

end Rate

section Base

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **`BgSetting` of the step from the tower.**  `Gp = 𝔹_{k+1}` of the step, `Gk₀ = Gj₀ = 𝔹_k`,
`X₀' = dataSites 𝔹_k`, `X₁f' =` the whole torus, `ε' = T.t`, `r₀ = 324`, `j₁ = 1`; the fields come
from `FlCore` of the scale record and `ChainNum`. -/
theorem step_bgSetting_base (Dt : StepScaleData T k hk N₁ ν β p₁) {δ₃ : ℝ}
    (hnum : ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃) :
    BgSetting 2 (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν
      T.c T.BG T.κ 324 T.t δ₃ (dataSites (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))) Finset.univ 1 :=
  step_bgSetting_base_collar T Dt hnum le_rfl (by norm_num)

/-- **`FlSetting` of the step from the tower** (`Gk₀ = 𝔹_k`, `Hm = 𝔹_k`, `δ₁ = T.t`, `X₁f'' =` the
whole torus), from `FlCore` of the scale record and `FlNum`. -/
theorem step_flSetting_base (Dt : StepScaleData T k hk N₁ ν β p₁) {δ₃ δfl : ℝ}
    (hnum : FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl) :
    FlSetting 2 (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν
      T.κ T.BG T.t δ₃ (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t δfl Finset.univ := by
  have hC := Dt.core
  exact {
    hS2 := hC.hS2
    SM := hC.SM
    hM2 := hC.hM2
    hPm := precedes_refl _
    hPmp := hC.hPmp
    depm := fun _ _ y _ => Finset.mem_univ y
    num := hnum }

end Base

end Balaban.Inhabited
