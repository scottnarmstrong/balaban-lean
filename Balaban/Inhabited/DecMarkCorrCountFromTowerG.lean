/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrCount
public import Balaban.Inhabited.MarkCorrBudgetG
public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Fluctuation.DecMarkOfPair
public import Balaban.Fluctuation.MarkedEvJoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rooted count of the corrected marks at every scale of the general tower

`corrected_markedOutDec_count` at the step of a scale of a general tower
`T : StepTowerG d L N κmin` with `StepScaleDataG`, with the radius `R = corrRG`, the disc radius
`U = 17/16`, the constant `F₀ = corrF0G T k β p₁`, and one decoupling pair for every block (from
`markedEv_joint_physV`).  The cover index of the marks is `1`, so the tower carries `T.m₀ = 1`
(the constant `KmarkG` has the factor `(L^{1+m₁})^d`).  The step setting `S` is stated over an
arbitrary separation parameter `ϱ` equal to `rhoSepG d L T.m₁`, so that the fixed
`d = L = 3`, `N = 2` statement (over `rhoSep T.m₁`) is the instance.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

open Classical in
/-- **The rooted count of the corrected marks at the general tower.**  General version of
`corrected_markedOutDec_count_fromTower`. -/
theorem corrected_markedOutDec_count_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁)
    (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (hSp : 0 < S.p₁)
    (zr : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
      (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
        (S.blockU zr) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b)) ∧
      ∀ Θ ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t, ∀ um : ℂ, ‖um‖ ≤ 17 / 16 →
        ∀ Φ : (∀ b, (S.blockSplit 1 hSp).Ωb b),
      (∀ Y', ‖markedOutDec 1 (fun _ => Set.univ)
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) zr
            (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b))
              (fun _ => k) (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU zr) p₁ hSp (S.β : ℂ) Θ um Φ)
            Y'‖ ≤ corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y')) ∧
      (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * T.κdec - 1 - a'' →
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
          corrF0G T k β p₁ * K0 d L (2 * T.κdec - 1 - a'')) ∧
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
            (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b)
            (S.blockU zr) Y p₁ hSp Θ um Φ := by
  classical
  subst hϱ
  subst hS
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  have hd := T.hd
  have hL := T.hL
  have hN0 : 0 < N := Nat.lt_of_lt_of_le two_pos T.hN
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
  have hbU : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁
      T.δ).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN (by omega) k T.m₁ _ hk ν β p₁ T.δ
  have hRR : (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ +
      corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) *
      markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁)
        hk ν β p₁ T.δ).a₁ T.κ p₁
        ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁)
          hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
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
  have hM : ∀ b, MarkedEvJointPhysV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁
      (rhoSepG d L T.m₁) hk ν β p₁ T.δ) (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
      ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁)
        hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
      (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁)
        hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁)
        hk ν β p₁ T.δ).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
      ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁)
        hk ν β p₁ T.δ).blockU zr) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b := fun b =>
    markedEv_joint_physV (S := (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)) (cc := _) (Zm := _) (hC := D.core)
      (hG := StepSetting.hG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)) (hcψ := hp.le) (hMX := T.large_block)
      (hdm := T.dom_margin) (hα := T.coer_margin) (hsm := T.δc_small) (hcov := hcov b)
      (hX₁ := hX b) (hconn := hatConn_lvTopG hL)
      (hrow := rowInHat_lvG hk (dgSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν))
      (hopt := hopt b) (hΔ := hΔ b) (hκ₀ := T.κ0_nonneg)
      (hκdec := T.κdec_lower) (hκ := by exact_mod_cast T.κ_lower) (h1 := T.κ_one)
      (hlog := by simpa [hm₀] using T.κ_log) (z := b) (hZ := hZ b)
      (hmar := hmar b)
  obtain ⟨F₁, Sol, hF⟩ := decMarkPair_family (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ) hM
  have hκ1 : 1 ≤ 2 * T.κdec := by
    have := T.κ0_nonneg
    have := T.κdec_lower
    linarith
  refine ⟨F₁, Sol, fun b => (hF b).1, fun Θ hΘ um hum Φ => ?_⟩
  obtain ⟨c1', c2', c3', c4'⟩ := corrected_markedOutDec_count (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ)
    (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).hG' hd (by omega)
    (fun b => (hV b).1) (fun b => (hV b).2.1) (fun b => (hV b).2.2.1)
    (fun b => (hV b).2.2.2.2.1) hκ1 zr
    (fun p hp' y hy => (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).blockU_supported zr hp' y hy) F₁ Sol
    (fun b => (hF b).1) (fun b => (hF b).2.1) (fun b => (hF b).2.2.2.1) (ρ := p₁) hp le_rfl hSp T.t_pos
    (β := ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).β : ℂ)) hΘ
    (R := corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) (U := 17 / 16) hR hRR hRU hum Φ
  have hF0 : ‖(((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).β : ℝ) : ℂ)‖ * 4 *
      ‖energyBdScaled d L N (compWeight L (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).a₁) k
        (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) T.t (rho4 d L N T.BG T.κ)‖ *
      (17 / 16 : ℝ) ^ 2 / corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ ^ 3 *
      (c1 d L * (((L : ℕ) : ℝ) ^ (1 + T.m₁)) ^ d) *
      ((nFibre d L : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)) = corrF0G T k β p₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold corrF0G EstarG VstarG KmarkG
    show _ = _
    have ha : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).a₁ = 1 := rfl
    have hβS : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).β = β := rfl
    rw [ha, hβS]
    ring
  refine ⟨fun Y' => ?_, fun {a''} ha => ?_, c3', ?_⟩
  · have := c1' Y'
    simpa only [hF0] using this
  · have := c2' ha
    simpa only [hF0] using this
  · exact c4'

end Balaban.Inhabited
