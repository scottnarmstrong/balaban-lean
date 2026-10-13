/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrRooted
public import Balaban.Inhabited.DecMarkCorrTotalFromTower
public import Balaban.Inhabited.DecMarkCorrSumFromTowerG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The physical sum identity for the corrected marks at every scale of the shared tower

At the step `(T.step k hk N₁ ν β p₁).withDatum D' hDh` of a scale of a shared tower with
`StepScaleData`, for a family of decoupling pairs given with its clauses (one pair for every
block, the constants `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁` of the tower, any
covers), a root `z`, a hat field `‖x‖ ≤ p₁` and real `s ∈ [0,1]`:

* `markedRad_slice_lt_fromTower`: every first mark `‖u‖ ≤ 17/16` lies in the slice
  `(‖u‖ + 0) · markedRad(p₁) < T.t` of the bidisc of the pairs;
* `sum_decMarkCorr_physical_fromTower`: the sum over the blocks and the labels of
  `−β · decMarkCorr` at the first mark `s` is `DΦ₁(s ψ')[M_z ψ']`;
* `sum_markedOutDec_decMarkCorr_physical_fromTower`: the sum over the bridge family of the rooted
  outputs of the terms `decMarkCorrTerm` is `DΦ₁(s ψ')[M_z ψ']`;
* `ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTower`: the same identity for almost every
  hat field of the fluctuation measure.

The total-mark identity and the corrected mark of the total are the landed
`mark_eq_deriv_blockEnergy_fromTower` and `fderiv_mask_corrected_total_fromTower`.  The base step
is the case `D' = (T.step k hk N₁ ν β p₁).D'` (in the chart by `StepScaleData.xi`).  The pairs are
arguments: the statements apply to the pairs of `corrected_markedOutDec_count_fromTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set Filter
  Topology MeasureTheory

/-- **The first marks of the disc `‖u‖ ≤ 17/16` lie in the slice of the bidisc of the pairs.**
At a scale of the tower, `(‖u‖ + 0) · markedRad(p₁) < T.t` for every `‖u‖ ≤ 17/16`
(`StepScaleData.marked_radius_lt`). -/
theorem markedRad_slice_lt_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁)
    {u : ℂ} (hu : ‖u‖ ≤ 17 / 16) :
    (‖u‖ + ‖(0 : ℂ)‖) * markedRad 3 3 2 k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have h := markedRad_slice_lt_fromTowerG T.toG (T.scaleDataG_of_fixed D) hp hu
  rw [StepTower.toG_step_betaU] at h
  exact h

/-- **The physical sum identity for the corrected marks at every scale of the tower** (zero
class).  Let `(F₁ b, Sol b)` be a pair with the eight clauses for every block `b`, at the step
`S = (T.step k hk N₁ ν β p₁).withDatum D' hDh` with the constants of the tower
(`cc = β_k^{-1/2}`, mask `blockU z`, `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁`).  For
a hat field `‖x‖ ≤ p₁`, the clamp radius `p₁` and real `s ∈ [0,1]`,
`∑_b ∑_{Y ∈ 𝒟_b} −β · decMarkCorr_b … Y … s (restr x) = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_decMarkCorr_physical_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1))}
    {X₁V : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (CTorus 3 3 N₁ T.m₁ (k + 1))}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (x : S.E) (hx : ‖x‖ ≤ p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
        -(S.β : ℂ) * decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k b)
          (S.blockU z) Y p₁ hSp (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hSp).restr x) =
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  exact sum_decMarkCorr_physical_fromTowerG T.toG (T.scaleDataG_of_fixed D) hβ hp
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS hSp z F₁ Sol hP x hx hs

/-- **The rooted physical identity for the corrected marks at every scale of the tower** (zero
class).  Under the hypotheses of `sum_decMarkCorr_physical_fromTower`, with the terms
`decMarkCorrTerm`, `T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`, of the pairs
`(F₁ b, Sol b)`:
`∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′ = DΦ₁(s ψ')[M_z ψ']`. -/
theorem sum_markedOutDec_decMarkCorr_physical_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1))}
    {X₁V : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (CTorus 3 3 N₁ T.m₁ (k + 1))}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    (x : S.E) (hx : ‖x‖ ≤ p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
      markedOutDec m₀ (fun _ => Set.univ)
        (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
          (S.blockU z) p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ) ((S.blockSplit m₀ hSp).restr x)) Y' =
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
        (S.maskUC z (S.shiftUC x)) := by
  exact sum_markedOutDec_decMarkCorr_physical_fromTowerG T.toG (T.scaleDataG_of_fixed D) hβ hp
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS hSp z F₁ Sol hP x hx hs

/-- **The rooted physical identity for the corrected marks at every scale of the tower, almost
everywhere** (zero class).  Under the hypotheses of `sum_decMarkCorr_physical_fromTower` on the
pairs, for real `s ∈ [0,1]` and almost every hat field `x` of the fluctuation measure `ν_{p₁}`,
`DΦ₁(s ψ')[M_z ψ'] = ∑_{Y′ ∈ 𝒴_z} markedOutDec … T Y′`, with the terms `decMarkCorrTerm`,
`T_{b,Y}(t) = t · (−β · decMarkCorr_b … Y … s (restr x))`. -/
theorem ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTower {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleData T k hk N₁ ν β p₁) (hβ : 0 < β) (hp : 0 < p₁)
    (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D')
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)}
    (hS : S = (T.step k hk N₁ ν β p₁).withDatum D' hDh) (hSp : 0 < S.p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {BG κdec : ℝ} {m₀ : ℕ}
    {jV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → ℕ}
    {𝒦XV : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ T.m₁ (k + 1))}
    {X₁V : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Finset (CTorus 3 3 N₁ T.m₁ (k + 1))}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (X₁V b) m₀ (jV b) (𝒦XV b) b (F₁ b) (Sol b))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        ∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
          markedOutDec m₀ (fun _ => Set.univ)
            (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
            (decMarkCorrTerm S X₁V jV 𝒦XV m₀ S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              Sol (S.blockU z) p₁ hSp (S.β : ℂ) (rawOf S.D') (s : ℂ)
              ((S.blockSplit m₀ hSp).restr x)) Y' := by
  exact ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTowerG T.toG (T.scaleDataG_of_fixed D) hβ hp
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD hS hSp z F₁ Sol hP hs

end Balaban.Inhabited
