/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.LocalClassDensityIrrelAux
public import Balaban.Inhabited.LevelCoversDef
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

section Base

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **`BgSetting` of the step from the tower.**  `Gp = 𝔹_{k+1}` of the step, `Gk₀ = Gj₀ = 𝔹_k`,
`X₀' = dataSites 𝔹_k`, `X₁f' =` the whole torus, `ε' = T.t`, `r₀ = 324`, `j₁ = 1`; the fields come
from `FlCore` of the scale record and `ChainNum`. -/
theorem step_bgSetting_base (Dt : StepScaleData T k hk N₁ ν β p₁) {δ₃ : ℝ}
    (hnum : ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃) :
    BgSetting 2 (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν
      T.c T.BG T.κ 324 T.t δ₃ (dataSites (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))) Finset.univ 1 := by
  have hC := Dt.core
  exact {
    hS := hC.hS
    Sp := hC.Sp
    ha₁ := one_pos
    HBp := hC.HBp
    HBk := hC.HBp
    HBj := hC.HBp
    hP := hC.hPmp
    hq := precedes_refl _
    colk := fun z _ => by
      show z ∈ (lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1
      rw [(isLevel_lvTop (N₁ := N₁) (m₁ := T.m₁) (k := k) (ϱ := rhoSep T.m₁)).Ω_one]
      exact Finset.mem_univ _
    colj := fun z hz => classOldDec_collar hk z hz
    hκ := hC.hκ
    hM := hC.hM
    num := hnum
    dsX₀ := fun x hx => hx
    hN := fun _ _ _ y _ => Finset.mem_univ y
    hr := by
      have h1 : (0 : ℝ) ≤ 36 * 3 ^ T.m₁ := by positivity
      have h2 := rhoSep_tail_nonneg
      have h3 := rhoSep_ge T.m₁
      push_cast
      nlinarith
    hr₀ := by norm_num
    dep := fun _ _ y _ => Finset.mem_univ y
    hj := by omega }

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
