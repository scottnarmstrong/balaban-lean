/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrCount
public import Balaban.Inhabited.MarkCorrBudget
public import Balaban.Inhabited.DecMarkCorrCountFromTowerG
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Inhabited.MarkedRootAssemblyFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rooted count of the corrected marks at every scale of the shared tower

`corrected_markedOutDec_count` at the step `T.step k hk N₁ ν β p₁` of a scale of a shared tower
with `StepScaleData`, with the radius `R = corrR`, the disc radius `U = corrU = 17/16`, the
constant `F₀ = corrF0 T k β p₁`, and one decoupling pair for every block (from
`markedEv_joint_physV`), the hypotheses discharged as in `markedRootAssembly_zero_fromTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

open Classical in
/-- **The rooted count of the corrected marks at the tower.**  For `β ≥ 0`-scale data
`D : StepScaleData T k hk N₁ ν β p₁` with `2 · corrU ≤ corrR` (true for `β` beyond the threshold of
`exists_beta0_corrR`) and a root `zr`, there is one decoupling pair `(F₁ b, Sol b)` for every block
`b` (mask `blockU zr`, covers of `D.covers`, `m₀ = 1`, `j = k`), such that for every datum
`Θ` of the chart, every block configuration `Φ` and every first mark `‖u‖ ≤ 17/16`, the rooted
outputs of the terms `t ↦ t · (−β · decMarkCorr … u Φ)` satisfy the bound
`corrF0 T k β p₁ · e^{−(2κ_dec−1) d(Y′)}`, the weighted sum over the bridge family is at most
`corrF0 T k β p₁ · K₀(2κ_dec−1−a'')`, a nonzero output has the root cube among its cubes, and
the sum of the outputs is the sum of `−β · decMarkCorr` over the blocks and the labels. -/
theorem corrected_markedOutDec_count_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁)
    (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁)
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁)
    (hSp : 0 < S.p₁)
    (zr : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
      (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
        (S.blockU zr) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b)) ∧
      ∀ Θ ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ, ‖um‖ ≤ corrU →
        ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
      (∀ Y', ‖markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
            (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
              (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU zr) p₁ hSp (S.β : ℂ) Θ um Φ)
            Y'‖ ≤ corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y')) ∧
      (∀ {a'' : ℝ}, aEnt 3 3 + 1 ≤ 2 * T.κdec - 1 - a'' →
        ∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) zr},
          ‖markedOutDec 1 (fun _ => Set.univ)
              (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
              (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
                (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU zr) p₁ hSp (S.β : ℂ) Θ um
                Φ) Y'.1‖ * Real.exp (a'' * treeLenCovOne 1 (k + 1) Y'.1) ≤
          corrF0 T k β p₁ * K0 3 3 (2 * T.κdec - 1 - a'')) ∧
      (∀ Y', markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
            (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
              (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU zr) p₁ hSp (S.β : ℂ) Θ um Φ)
            Y' ≠ 0 →
          IsDj 1 (k + 1) Y' ∧ rootCube (m₀ := 1) zr ∈ blocksOf 1 (k + 1) Set.univ Y') ∧
      ∑ Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
          (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b))) zr,
        markedOutDec 1 (fun _ => Set.univ)
          (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
          (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
            (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU zr) p₁ hSp (S.β : ℂ) Θ um Φ)
          Y' =
        ∑ b, ∑ Y ∈ polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b)),
          -(S.β : ℂ) * decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
            (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b)
            (S.blockU zr) Y p₁ hSp Θ um Φ := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  have h := corrected_markedOutDec_count_fromTowerG T.toG rfl (T.scaleDataG_of_fixed D) hN hν0
    (by simpa using hν) hβ hp hRU' (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm hS hSp zr
  simp only [corrF0_toG, corrU]
  exact h

end Balaban.Inhabited
