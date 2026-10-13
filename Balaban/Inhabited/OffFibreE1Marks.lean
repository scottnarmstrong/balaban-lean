/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarkParamCommon
public import Balaban.Inhabited.DecMarkCorrSumFromTower
public import Balaban.Inhabited.OffFibreCoeffFirst
import Mathlib.Tactic.Linarith

/-!
# First-energy parameter marks at a free chart datum

The cutoffs in the parameter marks are inactive at every datum of the chart. The rooted
outputs then sum to the corrected marks of the decoupled block energies, including when the
incoming external field varies across sites.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

open Classical in
/-- At any chart datum, the parameter marks sum to the corrected marks of the decoupled
block energies. The external field of the datum may vary across sites. -/
theorem e1_param_marks_sum_decMarkCorr_raw {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁)
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
      (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : S.E) :
    ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
      e1MarkGParam S F₁ Sol p₁ hp z T.t
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
        ((S.blockSplit 1 hp).restr x) =
    ∑ b, ∑ Y ∈ e1Dom S b,
      -(S.β : ℂ) * decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
        (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
          (compWeight 3 S.a₁) S.ν k b) (S.blockU z) Y p₁ hp
        (rawOf D) (s : ℂ) ((S.blockSplit 1 hp).restr x) := by
  classical
  have hsU : ‖(s : ℂ)‖ < corrU := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]
    unfold corrU
    linarith [hs.2]
  have hΘ : rawOf D ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t :=
    ⟨D, hX, rfl⟩
  have hp0 : 0 < p₁ := by subst hS; exact hp
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact hs.2
  have hrad : (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad 3 3 2 k S.a₁ T.κ p₁
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t := by
    subst hS
    exact markedRad_slice_lt_fromTower T Dt hp0 (u := (s : ℂ)) (by linarith)
  calc
    _ = ∑ Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z,
          markedOutDec 1 (fun _ => Set.univ) (e1Dom S) z
            (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
              (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1
              S.a₁ S.ν ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
              (S.blockU z) p₁ hp (S.β : ℂ) (rawOf D) (s : ℂ)
              ((S.blockSplit 1 hp).restr x)) Y' := by
        refine (Eq.trans (Finset.sum_subtype _ (fun _ => Iff.rfl) _)
          (Finset.sum_congr rfl fun i _ => ?_)).symm
        exact (e1MarkGParam_of_mem S F₁ Sol p₁ hp z T.t
            ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
            i (s : ℂ) ((S.blockSplit 1 hp).restr x) hΘ hsU).symm
    _ = _ := by
      exact S.sum_markedOutDec_eq_sum_decMarkCorr z F₁ Sol hP hp0
        le_rfl hp Dt.core.δ₁_pos hΘ hrad ((S.blockSplit 1 hp).restr x)
        (-(S.β : ℂ)) _
        (fun b Y => deriv_decMarkCorrTerm S F₁ Sol p₁ hp (S.β : ℂ)
          (rawOf D) (s : ℂ) _ b Y)

open Classical in
/-- The same free-datum parameter marks are the first Taylor remainder of the
decoupled block-energy mark. -/
theorem e1_param_marks_taylor_raw {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁)
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
      (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : S.E) :
    let G : ℂ → ℂ := fun u => ∑ b, ∑ Y ∈ e1Dom S b,
      decMarkG S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
        (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
          (compWeight 3 S.a₁) S.ν k b) (S.blockU z) Y p₁ hp
        (rawOf D) u ((S.blockSplit 1 hp).restr x)
    ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
      e1MarkGParam S F₁ Sol p₁ hp z T.t
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
        ((S.blockSplit 1 hp).restr x) =
      -(S.β : ℂ) * (G (s : ℂ) - G 0 - (s : ℂ) * deriv G 0) := by
  dsimp only
  rw [e1_param_marks_sum_decMarkCorr_raw T Dt hS hp F₁ Sol z hP D hX s hs x]
  have hp0 : 0 < p₁ := by subst hS; exact hp
  have hΘ : rawOf D ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t :=
    ⟨D, hX, rfl⟩
  have hT := sum_decMarkCorr_eq_taylor1 S F₁ Sol hP hp0 le_rfl hp
    Dt.core.δ₁_pos hΘ (s : ℂ) ((S.blockSplit 1 hp).restr x)
  calc
    _ = -(S.β : ℂ) * (∑ b, ∑ Y ∈ e1Dom S b,
        decMarkCorr S (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ b) (Sol b)
          (blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
            (compWeight 3 S.a₁) S.ν k b) (S.blockU z) Y p₁ hp
          (rawOf D) (s : ℂ) ((S.blockSplit 1 hp).restr x)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
    _ = _ := congrArg (fun v : ℂ => -(S.β : ℂ) * v) hT

end Balaban.Inhabited
