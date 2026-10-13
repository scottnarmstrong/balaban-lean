/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrCount
public import Balaban.Inhabited.DecMarkCorrCountFromTowerG

/-!
# One family of decoupling pairs for the corrected marks at the general tower

General version of `markCorrFamily_fromTower`: one application of `decMarkPair_family` over all
pairs `(zr, b)` of a root and a block gives a family `(F₁, Sol)` of decoupling pairs, with the
four conclusions of the rooted count with the constant `corrF0G T k β p₁` and the field
conclusions of every corrected mark.  The cover index of the marks is `1` (`T.m₀ = 1`); the step
setting is stated over an arbitrary `ϱ = rhoSepG d L T.m₁`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

open Classical in
/-- **One family of pairs for the corrected marks at the tower.** -/
theorem markCorrFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁)
    (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (hSp : 0 < S.p₁) :
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
      ∀ zr : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
      (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
        (S.blockU zr) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (zr, b)) (Sol (zr, b))) ∧
      (∀ b, ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t})) ∧
      (∀ b, ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
        ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad d L N k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) p.2 t Y ((p.1.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), ψh)) 0)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Θ ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ, ‖um‖ ≤ (17 / 16 : ℝ) →
        ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
      (∀ Y', ‖markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
            (decMarkCorrTerm S (fun b => (LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
              (fun _ => k) (fun b => (LocalCover.fam 1 (LocalCover.blockSite k b))) 1 S.a₁ S.ν
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (fun b => F₁ (zr, b)) (fun b => Sol (zr, b)) (S.blockU zr) p₁ hSp (S.β : ℂ)
              Θ um Φ) Y'‖ ≤
          corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y')) ∧
      (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * T.κdec - 1 - a'' →
        ∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr},
          ‖markedOutDec 1 (fun _ => Set.univ)
              (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
              (decMarkCorrTerm S (fun b => (LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
                (fun _ => k) (fun b => (LocalCover.fam 1 (LocalCover.blockSite k b))) 1 S.a₁ S.ν
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (fun b => F₁ (zr, b)) (fun b => Sol (zr, b)) (S.blockU zr) p₁ hSp
                (S.β : ℂ) Θ um Φ) Y'.1‖ * Real.exp (a'' * treeLenCovOne 1 (k + 1) Y'.1) ≤
          corrF0G T k β p₁ * K0 d L (2 * T.κdec - 1 - a'')) ∧
      (∀ Y', markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
            (decMarkCorrTerm S (fun b => (LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
              (fun _ => k) (fun b => (LocalCover.fam 1 (LocalCover.blockSite k b))) 1 S.a₁ S.ν
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (fun b => F₁ (zr, b)) (fun b => Sol (zr, b)) (S.blockU zr) p₁ hSp (S.β : ℂ)
              Θ um Φ) Y' ≠ 0 →
          IsDj 1 (k + 1) Y' ∧ rootCube (m₀ := 1) zr ∈ blocksOf 1 (k + 1) Set.univ Y') ∧
      ∑ Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
          (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr,
        markedOutDec 1 (fun _ => Set.univ)
          (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
          (decMarkCorrTerm S (fun b => (LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
            (fun _ => k) (fun b => (LocalCover.fam 1 (LocalCover.blockSite k b))) 1 S.a₁ S.ν
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (fun b => F₁ (zr, b)) (fun b => Sol (zr, b)) (S.blockU zr) p₁ hSp (S.β : ℂ)
            Θ um Φ) Y' =
        ∑ b, ∑ Y ∈ polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)),
          -(S.β : ℂ) * decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um Φ) ∧
      ∀ b,
      (∀ (Y Y' : Set (CTorus d L N₁ T.m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L 1 T.m₁ (k + 1)) y) (cellSide L 1 T.m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        DepOn (blocksOf 1 (k + 1) Set.univ Y') (decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        Continuous (decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um) ∧ Measurable (decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ, ‖um‖ ≤ (17 / 16 : ℝ) →
        ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
        ‖decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um Φ‖ ≤
          4 * (energyBdScaled d L N (compWeight L S.a₁) k
            (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) T.t (rho4 d L N T.BG T.κ) *
            Real.exp (-2 * T.κdec * treeLenCov S.G' 1 Y) / corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) *
          ((17 / 16 : ℝ) / corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) ^ 2) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b), ∀ a b' : ℝ, 0 < a → 0 < b' →
        (a + b') * markedRad d L N k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp (p.1.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) p.2 Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp (p.1.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) p.2 Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁))) ∧
      -- the defining properties of the pair
      ((∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
        InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D →
        ∀ (φ : S.G'.Ω 1 × Fin N → ℂ) (α : S.G'.Ω 1 → ℂ),
          IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
          (F₁ (zr, b)) (s, rawOf D) = (φ, α)) ∧
      (∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
        StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
          ((Sol (zr, b)) p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (zr, b)) p).2 ∧
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (zr, b)) p).2 ∧
          Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (zr, b)) p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
          Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (zr, b)) p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          SupBounds (stepG d L N₁ T.m₁ k ϱ) ((Sol (zr, b)) p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol (zr, b)) p).2))) := by
  classical
  subst hϱ
  subst hS
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  have hd := T.hd
  have hL := T.hL
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ by linarith)
      hp.le
    linarith [D.ray_margin]
  have hmem := compWeightG_mem T hk
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have := scalePosG T k
    positivity
  have hR := corrRG_pos T hk hb0 hp
  have hbU : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN (by omega) k T.m₁ _ hk ν β p₁ T.δ
  have hRR : (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ +
      corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) *
      markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).a₁ T.κ p₁
        (((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).betaU) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
    rw [hbU]
    have := markedRadG_eq T k hb0.le p₁
    have h2 := two_corrRG_mul_decMRG_lt T hk hb0 hp
    show (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ +
      corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) *
      markedRad d L N k 1 T.κ p₁ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t
    rw [this]
    linarith
  have hcov : ∀ b, CovSetup (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).G' 1 k
      (LocalCover.cube 1 k (LocalCover.blockSite k b))
      (LocalCover.fam 1 (LocalCover.blockSite k b)) := fun b => (hV b).1
  have hX : ∀ b, (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)) : Set (CTorus d L N₁ T.m₁ (k + 1))) =
      X1 (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) := fun b => (hV b).2.1
  have hopt : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube 1 k (LocalCover.blockSite k b)) ∧
        MeetsOne 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) W₀ ∧
        bondCost (scaleW L 1 T.m₁ k) E₀ =
          treeLenCovOne 1 k (LocalCover.cube 1 k (LocalCover.blockSite k b)) :=
    fun b => (hV b).2.2.1
  have hΔ : ∀ b, treeLenCovOne 1 k (LocalCover.cube 1 k (LocalCover.blockSite k b)) = 0 :=
    fun b => (hV b).2.2.2.1
  have hZ : ∀ b, readSites (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) k b ⊆
      ↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)) := fun b => (hV b).2.2.2.2.1
  have hmar : ∀ b, BlockMargin (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b))
      (↑(blockSites d L N₁ T.m₁ (k + 1) k b) : Set (CTorus d L N₁ T.m₁ (k + 1))) :=
    fun b => (hV b).2.2.2.2.2.1
  have hM : ∀ r : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
      Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
      MarkedEvJointPhysV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ) (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
      ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).blockU r.1) (LocalCover.nbhdF 1 (LocalCover.blockSite k r.2)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k r.2)) r.2 := fun r =>
    markedEv_joint_physV (S := (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)) (cc := _) (Zm := _) (hC := D.core)
      (hG := StepSetting.hG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)) (hcψ := hp.le) (hMX := T.large_block)
      (hdm := T.dom_margin) (hα := T.coer_margin) (hsm := T.δc_small) (hcov := hcov r.2)
      (hX₁ := hX r.2) (hconn := hatConn_lvTopG hL)
      (hrow := rowInHat_lvG hk (dgSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν))
      (hopt := hopt r.2) (hΔ := hΔ r.2) (hκ₀ := T.κ0_nonneg)
      (hκdec := T.κdec_lower) (hκ := by exact_mod_cast T.κ_lower) (h1 := T.κ_one)
      (hlog := by simpa [hm₀] using T.κ_log) (z := r.2) (hZ := hZ r.2)
      (hmar := hmar r.2)
  obtain ⟨F₁, Sol, hF⟩ := decMarkPair_family (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ) hM
  have hκ1 : 1 ≤ 2 * T.κdec := by
    have := T.κ0_nonneg
    have := T.κdec_lower
    linarith
  have hβS : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).β = β := rfl
  have hF0 : ‖(((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).β : ℝ) : ℂ)‖ * 4 *
      ‖energyBdScaled d L N (compWeight L (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).a₁) k
        (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) T.t (rho4 d L N T.BG T.κ)‖ *
      (17 / 16 : ℝ) ^ 2 / corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ^ 3 *
      (c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d) *
      ((nFibre d L : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)) = corrF0G T k β p₁ := by
    rw [hβS, Complex.norm_real, Real.norm_eq_abs]
    unfold corrF0G EstarG VstarG KmarkG
    show _ = _
    have ha : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).a₁ = 1 := rfl
    rw [ha]
    ring
  refine ⟨F₁, Sol, fun zr => ⟨fun b => (hF (zr, b)).1, fun b => (hF (zr, b)).2.1,
    fun b => (hF (zr, b)).2.2.2.1, fun Θ hΘ um hum Φ => ?_, fun b => ?_⟩⟩
  · obtain ⟨c1', c2', c3', c4'⟩ := corrected_markedOutDec_count (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).hG' hd (by omega)
      (fun b => (hV b).1) (fun b => (hV b).2.1) (fun b => (hV b).2.2.1)
      (fun b => (hV b).2.2.2.2.1) hκ1 zr
      (fun p hp' y hy => (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).blockU_supported zr hp' y hy)
      (fun b => F₁ (zr, b)) (fun b => Sol (zr, b))
      (fun b => (hF (zr, b)).1) (fun b => (hF (zr, b)).2.1) (fun b => (hF (zr, b)).2.2.2.1)
      (ρ := p₁) hp le_rfl hSp T.t_pos
      (β := ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).β : ℂ)) hΘ
      (R := corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) (U := 17 / 16) hR hRR hRU hum Φ
    refine ⟨fun Y' => ?_, fun {a''} ha => ?_, c3', c4'⟩
    · have := c1' Y'
      simpa only [hF0] using this
    · have := c2' ha
      simpa only [hF0] using this
  · obtain ⟨f1, f2, f3, f4⟩ := decMarkCorr_fields_of_pair (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)
      (F₁ (zr, b)) (Sol (zr, b)) (hF (zr, b)).1 (hF (zr, b)).2.1 (hF (zr, b)).2.2.2.1
      (ρ := p₁) hp le_rfl hSp T.t_pos
    exact ⟨f1, f2, fun Y Θ hΘ um hum Φ => f3 Y Θ hΘ _ _ hR hRR hRU um hum Φ, f4,
      fun Y Φ => f4 Y Φ _ _ hR hR hRR, (hF (zr, b)).2.2.2.2.2⟩

end Balaban.Inhabited
