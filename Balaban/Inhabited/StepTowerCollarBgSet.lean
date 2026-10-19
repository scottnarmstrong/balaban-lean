/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldDecInputE
public import Balaban.Fluctuation.LocalClassDensityIrrelAux
public import Balaban.Inhabited.LevelCoversDef
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Inhabited.StepTowerCollarGBgSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The base background setting of the step at a general collar (`StepTowerCollarBgSet`)

`step_bgSetting_base_collar`: `BgSetting` of the step `T.step k hk N₁ ν β p₁` from the tower
(`Gp = 𝔹_{k+1}`, `Gk₀ = Gj₀ = 𝔹_k`, `X₀' = dataSites 𝔹_k`, `X₁f' =` the whole torus, `ε' = T.t`,
`j₁ = 1`) at every collar `r₀ ∈ [4 d L³, 360] = [324, 360]`: the collar condition
`r₀ L^{m₁} ≤ ϱ - 1` holds for the separation `ϱ = rhoSep m₁ ≥ 360 · 3^{m₁} + 1`
(`rhoSep_ge`).  The numerics are `ChainNum` at the collar `r₀`.  The source's collar is
`r₀ = 4 d L³ + L = 327` (FLUCTUATION §1.4); `step_bgSetting_base` is the case `r₀ = 324`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Finset

section Base

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **`BgSetting` of the step from the tower at a collar `r₀ ∈ [324, 360]`.**  `Gp = 𝔹_{k+1}` of
the step, `Gk₀ = Gj₀ = 𝔹_k`, `X₀' = dataSites 𝔹_k`, `X₁f' =` the whole torus, `ε' = T.t`,
`j₁ = 1`; the fields come from `FlCore` of the scale record and `ChainNum` at `r₀`. -/
theorem step_bgSetting_base_collar (Dt : StepScaleData T k hk N₁ ν β p₁) {r₀ δ₃ : ℝ}
    (hnum : ChainNum 3 3 2 T.m₁ T.BG T.κ r₀ T.t δ₃) (hr₁ : 324 ≤ r₀) (hr₂ : r₀ ≤ 360) :
    BgSetting 2 (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν
      T.c T.BG T.κ r₀ T.t δ₃ (dataSites (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))) Finset.univ 1 := by
  have h := T.toG.step_bgSetting_base_collar (StepTower.scaleDataG_of_fixed T Dt) hnum
    (by norm_num; exact hr₁) (by norm_num; linarith)
  have key : ∀ ϱ : ℝ, ϱ = rhoSep T.m₁ →
      BgSetting 2 (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁
          T.δ).G' (stepG 3 3 N₁ T.m₁ k ϱ) (stepG 3 3 N₁ T.m₁ k ϱ)
        (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁ T.δ).a₁
        (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁ T.δ).ν
        T.c T.BG T.κ r₀ T.t δ₃ (dataSites (stepG 3 3 N₁ T.m₁ k ϱ)) Finset.univ 1 →
      BgSetting 2 (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁
        (T.step k hk N₁ ν β p₁).ν T.c T.BG T.κ r₀ T.t δ₃
        (dataSites (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))) Finset.univ 1 := by
    intro ϱ hϱ; subst hϱ; exact id
  exact key _ (rhoSepG_three _) h

end Base

end Balaban.Inhabited
