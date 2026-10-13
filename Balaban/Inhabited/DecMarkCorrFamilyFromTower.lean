/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrCount
public import Balaban.Inhabited.DecMarkCorrCountFromTower

/-!
# One family of decoupling pairs for the corrected marks at the tower

`corrected_markedOutDec_count_fromTower` and the field theorems each choose their own pairs.  Here
one application of `decMarkPair_family`, over all pairs `(zr, b)` of a root and a block, gives a
family `(F₁, Sol)`; for every root `zr` the family `b ↦ (F₁ (zr, b), Sol (zr, b))` has the
properties of a decoupling pair, the four conclusions of the rooted count with the constant
`corrF0 T k β p₁`, and the field conclusions of every corrected mark.  The mask of the pair of the
block `b` is `S.blockU zr`, so the family depends on the root `zr` through the mask only, and it
is indexed by `(zr, b)`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

open Classical in
/-- **One family of pairs for the corrected marks at the tower.** -/
theorem markCorrFamily_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁)
    (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁)
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁)
    (hSp : 0 < S.p₁) :
    ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
      ∀ zr : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
      (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
        (S.blockU zr) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (zr, b)) (Sol (zr, b))) ∧
      (∀ b, ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ)) × (ℂ × ℂ) =>
          evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad 3 3 2 k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t})) ∧
      (∀ b, ∀ Y, ∀ ψh : unitPts S.G' × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
        ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad 3 3 2 k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        AnalyticOnNhd ℂ (fun p : physParam 2 S × ℂ => deriv (fun t : ℂ =>
          evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) p.2 t Y ((p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), ψh)) 0)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Θ ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ, ‖um‖ ≤ corrU →
        ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
      (∀ Y', ‖markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
            (decMarkCorrTerm S (fun b => (LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
              (fun _ => k) (fun b => (LocalCover.fam 1 (LocalCover.blockSite k b))) 1 S.a₁ S.ν
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (fun b => F₁ (zr, b)) (fun b => Sol (zr, b)) (S.blockU zr) p₁ hSp (S.β : ℂ)
              Θ um Φ) Y'‖ ≤
          corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y')) ∧
      (∀ {a'' : ℝ}, aEnt 3 3 + 1 ≤ 2 * T.κdec - 1 - a'' →
        ∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr},
          ‖markedOutDec 1 (fun _ => Set.univ)
              (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
              (decMarkCorrTerm S (fun b => (LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
                (fun _ => k) (fun b => (LocalCover.fam 1 (LocalCover.blockSite k b))) 1 S.a₁ S.ν
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (fun b => F₁ (zr, b)) (fun b => Sol (zr, b)) (S.blockU zr) p₁ hSp
                (S.β : ℂ) Θ um Φ) Y'.1‖ * Real.exp (a'' * treeLenCovOne 1 (k + 1) Y'.1) ≤
          corrF0 T k β p₁ * K0 3 3 (2 * T.κdec - 1 - a'')) ∧
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
          -(S.β : ℂ) * decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um Φ) ∧
      ∀ b,
      (∀ (Y Y' : Set (CTorus 3 3 N₁ T.m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide 3 1 T.m₁ (k + 1)) y) (cellSide 3 1 T.m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad 3 3 2 k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        DepOn (blocksOf 1 (k + 1) Set.univ Y') (decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad 3 3 2 k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        Continuous (decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um) ∧ Measurable (decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ, ‖um‖ ≤ corrU →
        ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
        ‖decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp Θ um Φ‖ ≤
          4 * (energyBdScaled 3 3 2 (compWeight 3 S.a₁) k
            (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ) *
            Real.exp (-2 * T.κdec * treeLenCov S.G' 1 Y) / corrR T k (β * 3 ^ k) p₁) *
          (corrU / corrR T k (β * 3 ^ k) p₁) ^ 2) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b), ∀ a b' : ℝ, 0 < a → 0 < b' →
        (a + b') * markedRad 3 3 2 k S.a₁ T.κ p₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t →
        AnalyticOnNhd ℂ (fun p : physParam 2 S × ℂ =>
          decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp (p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) p.2 Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
        AnalyticOnNhd ℂ (fun p : physParam 2 S × ℂ =>
          decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ (zr, b)) (Sol (zr, b)) (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b) (S.blockU zr) Y p₁ hSp (p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) p.2 Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) (corrR T k (β * 3 ^ k) p₁))) := by
  classical
  subst hS
  obtain ⟨hV, -⟩ := D.covers
  have hr0 := D.r_pos
  have hlt : p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
    have h := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 2 * 2 + lvR T.κ T.t (β * 3 ^ k) p₁ by linarith) hp.le
    linarith [D.ray_margin]
  have hmem := compWeight_three_mem hk
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hR := corrR_pos T hk hb0 hp
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * 3 ^ k := by
    have hβS : (T.step k hk N₁ ν β p₁).β = β := rfl
    unfold StepSetting.betaU
    rw [hβS]
    push_cast
    field_simp
  have hRR : (corrR T k (β * 3 ^ k) p₁ + corrR T k (β * 3 ^ k) p₁) *
      markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
    rw [hbU]
    have := markedRad_eq T k hb0.le p₁
    have h2 := two_corrR_mul_decMR_lt T hk hb0 hp
    show (corrR T k (β * 3 ^ k) p₁ + corrR T k (β * 3 ^ k) p₁) *
      markedRad 3 3 2 k 1 T.κ p₁ (((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t
    rw [this]
    linarith
  have hM : ∀ r : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
      Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
      MarkedEvJointPhysV (T.step k hk N₁ ν β p₁)
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
      ((T.step k hk N₁ ν β p₁).blockU r.1) (LocalCover.nbhdF 1 (LocalCover.blockSite k r.2)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k r.2)) r.2 := fun r =>
    markedEv_joint_physV (T.step k hk N₁ ν β p₁) D.core (T.step k hk N₁ ν β p₁).hG _ hp.le
      _ T.large_block T.dom_margin T.coer_margin T.δc_small (hV r.2).1 (hV r.2).2.1 hatConn_lvTop
      (rowInHat_lv hk T.m₁_four hN hν0 hν) (hV r.2).2.2.1 (hV r.2).2.2.2.1 T.κ0_nonneg
      T.κdec_lower (by exact_mod_cast T.κ_lower) T.κ_one T.κ_log r.2 (hV r.2).2.2.2.2.1
      (hV r.2).2.2.2.2.2.1
  obtain ⟨F₁, Sol, hF⟩ := decMarkPair_family (T.step k hk N₁ ν β p₁) hM
  have hκ1 : 1 ≤ 2 * T.κdec := by
    have := T.κ0_nonneg
    have := T.κdec_lower
    linarith
  have hβS : (T.step k hk N₁ ν β p₁).β = β := rfl
  have hF0 : ‖(((T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)‖ * 4 *
      ‖energyBdScaled 3 3 2 (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) k
        (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) T.t (rho4 3 3 2 T.BG T.κ)‖ *
      corrU ^ 2 / corrR T k (β * 3 ^ k) p₁ ^ 3 *
      (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + T.m₁)) ^ 3) *
      ((nFibre 3 3 : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)) = corrF0 T k β p₁ := by
    rw [hβS, Complex.norm_real, Real.norm_eq_abs]
    unfold corrF0 Kmark Estar Vstar
    show _ = _
    have ha : (T.step k hk N₁ ν β p₁).a₁ = 1 := rfl
    rw [ha]
    ring
  refine ⟨F₁, Sol, fun zr => ⟨fun b => (hF (zr, b)).1, fun b => (hF (zr, b)).2.1,
    fun b => (hF (zr, b)).2.2.2.1, fun Θ hΘ um hum Φ => ?_, fun b => ?_⟩⟩
  · obtain ⟨c1', c2', c3', c4'⟩ := corrected_markedOutDec_count (T.step k hk N₁ ν β p₁)
      (T.step k hk N₁ ν β p₁).hG' (by norm_num) (by norm_num)
      (fun b => (hV b).1) (fun b => (hV b).2.1) (fun b => (hV b).2.2.1)
      (fun b => (hV b).2.2.2.2.1) hκ1 zr
      (fun p hp' y hy => (T.step k hk N₁ ν β p₁).blockU_supported zr hp' y hy)
      (fun b => F₁ (zr, b)) (fun b => Sol (zr, b))
      (fun b => (hF (zr, b)).1) (fun b => (hF (zr, b)).2.1) (fun b => (hF (zr, b)).2.2.2.1)
      (ρ := p₁) hp le_rfl hSp T.t_pos
      (β := ((T.step k hk N₁ ν β p₁).β : ℂ)) hΘ
      (R := corrR T k (β * 3 ^ k) p₁) (U := corrU) hR hRR hRU hum Φ
    refine ⟨fun Y' => ?_, fun {a''} ha => ?_, c3', c4'⟩
    · have := c1' Y'
      simpa only [hF0] using this
    · have := c2' ha
      simpa only [hF0] using this
  · obtain ⟨f1, f2, f3, f4⟩ := decMarkCorr_fields_of_pair (T.step k hk N₁ ν β p₁)
      (F₁ (zr, b)) (Sol (zr, b)) (hF (zr, b)).1 (hF (zr, b)).2.1 (hF (zr, b)).2.2.2.1
      (ρ := p₁) hp le_rfl hSp T.t_pos
    exact ⟨f1, f2, fun Y Θ hΘ um hum Φ => f3 Y Θ hΘ _ _ hR hRR hRU um hum Φ, f4,
      fun Y Φ => f4 Y Φ _ _ hR hR hRR⟩

section Rooted

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- The rooted output of the corrected marks is the sum of `−β · decMarkCorr` over the pairs
`(b, Y)` of the root whose bridge is `Y′`. -/
theorem markedOutDec_decMarkCorrTerm_eq
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) (zr : RootIdx d L N₁ m₁ (k + 1))
    (Y' : Set (CTorus d L N₁ m₁ (k + 1))) :
    markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y' =
      ∑ q ∈ (markedIdx (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b))
          zr).filter (fun q => bridge m₀ zr q.2 = Y'),
        -β * decMarkCorr S (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) a₁ ν cc (F₁ q.1) (Sol q.1)
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k q.1) Zm q.2 ρ hp Θ um Φ := by
  unfold markedOutDec
  exact Finset.sum_congr rfl fun q _ => deriv_decMarkCorrTerm S F₁ Sol ρ hp β Θ um Φ q.1 q.2

open Classical in
/-- **Fields of the rooted output of the corrected marks.**  For a family of pairs `(F₁ b, Sol b)`
with the eight clauses and the analyticity statements `hJ2`, `hJ4` for every block, the rooted
output `Φ ↦ markedOutDec … (decMarkCorrTerm …) Y′` is measurable and depends only on the blocks
of `Y′` for a bridge label `Y′`, and `(e, um) ↦ markedOutDec …` is analytic on `physV × ball 0 a`. -/
theorem markedOutDecCorr_fields
    (hG' : IsLevel S.G' (k + 1)) (hd : 3 ≤ d) (hN : L ^ m₀ ∣ N₁)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (zr : RootIdx d L N₁ m₁ (k + 1))
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm (X₁V b)
      m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (hJ2 : ∀ b, ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν S.hG' cc (F₁ b) (Sol b)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    (hJ4 : ∀ b, ∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν S.hG' cc (F₁ b) (Sol b)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) (β : ℂ) :
    (∀ Y', ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      Measurable (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y')) ∧
    (∀ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr,
      ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      DepOn (blocksOf m₀ (k + 1) Set.univ Y')
        (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y')) ∧
    (∀ Y', ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b' : ℝ, 0 < a → 0 < b' →
      (a + b') * markedRad d L N k a₁ κ cψ cc < δ₁ →
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β
            (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ) Y')
        (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  have hfl := fun b => decMarkCorr_fields_of_pair S (F₁ b) (Sol b) (hP b) (hJ2 b) (hJ4 b)
    hρ hρc hp hδ
  refine ⟨fun Y' Θ hΘ um hum => ?_, fun Y' hY' Θ hΘ um hum => ?_, fun Y' Φ a b' ha hb' hab => ?_⟩
  · have e : (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y') =
        fun Φ => ∑ q ∈ (markedIdx (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr).filter
            (fun q => bridge m₀ zr q.2 = Y'),
          -β * decMarkCorr S (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) a₁ ν cc (F₁ q.1) (Sol q.1)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k q.1) Zm q.2 ρ hp Θ um Φ :=
      funext fun Φ => markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ um Φ zr Y'
    rw [e]
    refine Finset.measurable_sum _ fun (q : _ × _) _ => measurable_const.mul ?_
    exact ((hfl q.1).2.1 q.2 Θ hΘ um hum).2
  · have e : (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y') =
        fun Φ => ∑ q ∈ (markedIdx (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr).filter
            (fun q => bridge m₀ zr q.2 = Y'),
          -β * decMarkCorr S (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) a₁ ν cc (F₁ q.1) (Sol q.1)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k q.1) Zm q.2 ρ hp Θ um Φ :=
      funext fun Φ => markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ um Φ zr Y'
    rw [e]
    intro Φ Φ' hΦ
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    have hmem := mem_markedIdx.1 hq1
    have hDj : IsDj m₀ (k + 1) q.2 :=
      isDj_of_polyDom hG' (hcovV q.1) hd (hoptV q.1) hmem.1
    have hDj' : IsDj m₀ (k + 1) Y' := hq2 ▸ bridge_isDj hN zr hDj
    have hsub : q.2 ⊆ Y' := hq2 ▸ subset_bridge zr q.2
    have := (hfl q.1).1 q.2 Y' hsub (cell_subset_of_isDj hN hDj') Θ hΘ um hum Φ Φ' hΦ
    rw [this]
  · have e : (fun p : physParam N S × ℂ =>
        markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β
            (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ) Y') =
        fun p => ∑ q ∈ (markedIdx (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr).filter
            (fun q => bridge m₀ zr q.2 = Y'),
          -β * decMarkCorr S (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) a₁ ν cc (F₁ q.1) (Sol q.1)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k q.1) Zm q.2 ρ hp
            (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ :=
      funext fun p => markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β _ _ Φ zr Y'
    rw [e]
    exact Finset.analyticOnNhd_fun_sum _ fun (q : _ × _) _ =>
      analyticOnNhd_const.mul ((hfl q.1).2.2.2 q.2 Φ a b' ha hb' hab)

end Rooted

end Balaban.Inhabited
