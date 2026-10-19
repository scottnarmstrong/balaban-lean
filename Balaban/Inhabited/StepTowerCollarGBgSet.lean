/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.LocalClassDensityIrrelAux
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The base settings of the general step at a general collar (`StepTowerCollarGBgSet`)

For `T : StepTowerG d L N κmin` and its scale record `StepScaleDataG`:

* `StepTowerG.bgSetting_base_collar`: `BgSetting` of `T.step k hk N₁ ν β p₁` (`Gp = 𝔹_{k+1}`,
  `Gk₀ = Gj₀ = 𝔹_k`, `X₀' = dataSites 𝔹_k`, `X₁f' =` the whole torus, `ε' = T.t`, `j₁ = 1`) at every
  collar `r₀ ∈ [4 d L³, 4 d L³ + 4 d L]`, from `ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃`.  The
  source collar `4 d L³ + L` lies in this range, since `L ≤ 4 d L`.  At `d = L = 3` the range is
  `[324, 360]`.
* `StepTowerG.flSetting_base_dec`: `FlSetting` of the step at a fluctuation radius `δ₁`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep Finset

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} {hk : 1 ≤ k}
  {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **`BgSetting` of the general step at a collar `r₀ ∈ [4 d L³, 4 d L³ + 4 d L]`.** -/
theorem bgSetting_base_collar (Dt : StepScaleDataG T k hk N₁ ν β p₁) {r₀ δ₃ : ℝ}
    (hnum : ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃) (hr₁ : 4 * (d : ℝ) * (L : ℝ) ^ 3 ≤ r₀)
    (hr₂ : r₀ ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 + 4 * d * L) :
    BgSetting N (T.step k hk N₁ ν β p₁).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (T.step k hk N₁ ν β p₁).a₁
      (T.step k hk N₁ ν β p₁).ν T.c T.BG T.κ r₀ T.t δ₃
      (dataSites (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))) Finset.univ 1 := by
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
      show z ∈ (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1
      rw [(isLevel_lvTopG (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k)
        (ϱ := rhoSepG d L T.m₁)).Ω_one]
      exact Finset.mem_univ _
    colj := fun z hz => classOldDec_collar hk z hz
    hκ := hC.hκ
    hM := hC.hM
    num := hnum
    dsX₀ := fun x hx => hx
    hN := fun _ _ _ y _ => Finset.mem_univ y
    hr := by
      have h0 : (0 : ℝ) ≤ (L : ℝ) ^ T.m₁ := by positivity
      have h1 : r₀ * (L : ℝ) ^ T.m₁ ≤ (4 * (d : ℝ) * (L : ℝ) ^ 3 + 4 * d * L) * (L : ℝ) ^ T.m₁ :=
        mul_le_mul_of_nonneg_right hr₂ h0
      have h2 := rhoSepG_tail_nonneg (d := d) T.hd T.hL
      have h3 := bgR0_nonneg_G (d := d) (L := L)
      have h4 : (0 : ℝ) ≤ 4 * d * L * (L : ℝ) ^ T.m₁ := by positivity
      unfold rhoSepG
      nlinarith
    hr₀ := hr₁
    dep := fun _ _ y _ => Finset.mem_univ y
    hj := by omega }

/-- **`FlSetting` of the general step at a fluctuation radius `δ₁`**: the fields come from `FlCore`
of the scale record, the numerics from `FlNum … T.t δ₃ δ₁ δfl`. -/
theorem flSetting_base_dec (Dt : StepScaleDataG T k hk N₁ ν β p₁) {δ₃ δ₁ δfl : ℝ}
    (hnum : FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl) :
    FlSetting N (T.step k hk N₁ ν β p₁).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (T.step k hk N₁ ν β p₁).a₁
      (T.step k hk N₁ ν β p₁).ν T.κ T.BG T.t δ₃ (levelKc d L) (Cchi d L) T.c₂ T.BG₂ δ₁ δfl
      Finset.univ := by
  have hC := Dt.core
  exact {
    hS2 := hC.hS2
    SM := hC.SM
    hM2 := hC.hM2
    hPm := precedes_refl _
    hPmp := hC.hPmp
    depm := fun _ _ y _ => Finset.mem_univ y
    num := hnum }

end StepTowerG

end Balaban.Inhabited
