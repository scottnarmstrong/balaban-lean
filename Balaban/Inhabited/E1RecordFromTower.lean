/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkCorrSumFromTower
public import Balaban.Inhabited.E1RecordOfSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The energy marks record of the renormalization step at the shared tower

`e1MarksC_zeroClass_of_sum` assembles the record `E1MarksC` of the interpolation integral
`ℰ₁^{(k+1)}(z)` (zero class, whole torus) for a family of decoupling pairs, with the physical sum
identity `hF` as its only hypothesis.  This file proves that identity for every family of pairs
with the eight clauses, and removes the hypothesis.

* `e1_hF_of_pairs_fromTower`: for a family of pairs `(F₁ (z, b), Sol (z, b))` with the eight
  clauses at the base step of a scale of the tower, every root `z`, real `s ∈ [0,1]` and almost
  every hat field `x`: the masked derivative `DΦ₁(s ψ')[M_z ψ']` is the sum over the bridge family
  of `z` of the marks `e1MarkG` of the pairs of `z` at the first mark `s` and the block
  configuration of `x` (the cutoff `‖u‖ < corrU` of `e1MarkG` is inactive at real `s ∈ [0,1]`).
* `e1MarksC_zeroClass_fromTower`: the record `E1MarksC` at every scale beyond one threshold in `β`,
  for every root, with its disc, rates, constants and budget.
* `e1loc_expansion_zeroClass_fromTower`: the expansion of the local energy term `ℰ₁^{(k+1)}(z)`
  into terms bounded by `K₀ e^{-κ' d_Ext(T)}`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **The physical sum identity for the marks of the energy record, general tower.**  At the step
`S = hatStepKG … ϱ …` of a scale of `T : StepTowerG d L N κmin` over any `ϱ = rhoSepG d L T.m₁`, let
`(F₁ (z, b), Sol (z, b))` be a pair with the eight clauses for every root `z` and block `b` (mask
`blockU z`, covers of the scale, `m₀ = 1`, `j = k`, the constants `BG₂ = T.BG₂`, `κ = T.κ`,
`eps = δ₁ = T.t`, `cψ = p₁`).  Then for every root `z`, real `s ∈ [0,1]` and almost every hat field
`x` of the fluctuation measure, `DΦ₁(s ψ')[M_z ψ'] = ∑_{Y′ ∈ 𝒴_z} e1MarkGGen … z Y′ s (restr x)`
(the cutoff `‖u‖ < 17/16` of `e1MarkGGen` is inactive at real `s ∈ [0,1]`).  The fixed
`e1_hF_of_pairs_fromTower` is its corollary. -/
theorem e1_hF_of_pairs_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) (hβ : 0 < β) {ϱ : ℝ}
    (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁) {BG κdec : ℝ}
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
        Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
        Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
    (hP : ∀ z : RootIdx d L N₁ T.m₁ (k + 1), ∀ b,
      MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
        (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
        (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)))
    (z : RootIdx d L N₁ T.m₁ (k + 1)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
          (S.maskUC z (S.shiftUC x)) =
        ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
          e1MarkGGen S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i (s : ℂ)
            ((S.blockSplit 1 hp).restr x) := by
  intro s hs
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  have hp0 : 0 < p₁ := hp
  have hsU : ‖(s : ℂ)‖ < (17 / 16 : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; linarith [hs.2]
  filter_upwards [ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTowerG T D hβ hp0 rfl
    (S₀ := T.step k hk N₁ ν β p₁) rfl (T.step k hk N₁ ν β p₁).D' (T.step k hk N₁ ν β p₁).hh₀ D.xi
    (S := T.step k hk N₁ ν β p₁) rfl hp z (fun b => F₁ (z, b)) (fun b => Sol (z, b)) (hP z) hs]
    with x hx
  refine hx.trans (Eq.trans (Finset.sum_subtype _ (fun _ => Iff.rfl) _)
    (Finset.sum_congr rfl fun i _ => ?_))
  exact (e1MarkGGen_of_lt (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
    z i hsU _).symm

open Classical in
/-- **The physical sum identity for the marks of the energy record.**  At the base step
`S = T.step k hk N₁ ν β p₁` of a scale of the tower, let `(F₁ (z, b), Sol (z, b))` be a pair with
the eight clauses for every root `z` and block `b` (mask `blockU z`, covers of the scale,
`m₀ = 1`, `j = k`, the constants `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁`).  Then
for every root `z`, real `s ∈ [0,1]` and almost every hat field `x` of the fluctuation measure,
`DΦ₁(s ψ')[M_z ψ'] = ∑_{Y′ ∈ 𝒴_z} e1MarkG … z Y′ s (restr x)`, the field `hF` of the record of
`e1MarksC_zeroClass_of_sum` (clamp radius `p₁`, datum `rawOf S.D'`). -/
theorem e1_hF_of_pairs_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hβ : 0 < β)
    (hp : 0 < p₁) {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
        Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
        Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') ×
          Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (hP : ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1), ∀ b,
      MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (T.step k hk N₁ ν β p₁).hG'
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν BG T.BG₂ T.κ T.t T.t κdec p₁
        ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
      (fderiv ℂ ((T.step k hk N₁ ν β p₁).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
          ((s : ℂ) • (T.step k hk N₁ ν β p₁).shiftUC x))
          ((T.step k hk N₁ ν β p₁).maskUC z ((T.step k hk N₁ ν β p₁).shiftUC x)) =
        ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (e1Dom (T.step k hk N₁ ν β p₁)) z},
          e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i
            (s : ℂ) (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x) := by
  exact fun s hs => e1_hF_of_pairs_fromTowerG T.toG (StepTower.scaleDataG_of_fixed T D) hβ
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S := T.step k hk N₁ ν β p₁) rfl hp F₁ Sol hP z
    s hs

open Classical in
/-- **The marks record of the energy term at the general tower.**  The statement of
`e1MarksC_zeroClass_fromTower_anchor` at `T : StepTowerG d L N κmin` with `T.m₀ = 1`, a constants
record `C` with the rates and label constants of `T` (`StepTowerG.exists_outputConsts`) and the step
`S = hatStepKG … ϱ …` over any `ϱ = rhoSepG d L T.m₁`: beyond a threshold `β₀`, at every scale
datum and every root `z`, a record `E1MarksC` of the interpolation integral `ℰ₁^{(k+1)}(z)` (zero
class) with disc `ball 0 (17 / 16)`, `κ_G = 2 κ_dec − 1`, `κ' = T.κ'`, `F₀ = corrF0G`, the budget
`C_PE ∑ F₀ e^{-κ₀ d} ≤ K₀`, and the root clause.  The record of `e1MarksC_zeroClass_of_sum_anchorG`,
whose hypothesis `hF` is `e1_hF_of_pairs_fromTowerG`. -/
theorem e1MarksC_zeroClass_fromTowerG_anchor {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ (S : StepSetting d L N₁ T.m₁ k N ϱ),
        S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ → ∀ (hp : 0 < S.p₁),
      ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∃ I : E1MarksC S (zeroClass d L N₁ T.m₁ k N ϱ) (S.blockSplit 1 hp) z,
          I.𝒰 = Metric.ball (0 : ℂ) (17 / 16 : ℝ) ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
          I.F0 = (fun _ => corrF0G T k β p₁) ∧
          CPE d L I.Kc I.κH I.κ0 I.κ' *
            (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0 d L T.κ0 ∧
            ∀ i, rootCube (m₀ := 1) (K := k + 1) z ∈
              blocksOf 1 (k + 1) Set.univ (I.Lab.ysite (I.y0 i)) := by
  obtain ⟨β₀, h3, h⟩ := e1MarksC_zeroClass_of_sum_anchorG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp z => ?_⟩
  obtain ⟨F₁, Sol, hpairs, h'⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  exact h' z (e1_hF_of_pairs_fromTowerG T D (by linarith) hϱ hS hp F₁ Sol
    (fun z b => (hpairs z b).1) z)

open Classical in
/-- **The marks record of the energy term at the tower.**  Beyond a threshold `β₀`, at every scale
datum and every root `z`, there is a record `E1MarksC` of the interpolation integral
`ℰ₁^{(k+1)}(z)` (zero class) with disc `ball 0 corrU`, `κ_G = 2 κ_dec − 1`, `κ' = T.κ'`,
`F₀ = corrF0`, and the budget `C_PE ∑ F₀ e^{-κ₀ d} ≤ K₀`: the record of
`e1MarksC_zeroClass_of_sum`, whose hypothesis `hF` is `e1_hF_of_pairs_fromTower`.  The version `_anchor` also returns the root clause: the root cube of
`z` lies in the blocks of the site set of every label of the marks. -/
theorem e1MarksC_zeroClass_fromTower_anchor {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        ∃ I : E1MarksC (T.step k hk N₁ ν β p₁) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) z,
          I.𝒰 = Metric.ball (0 : ℂ) corrU ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
          I.F0 = (fun _ => corrF0 T k β p₁) ∧
          CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
            (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0 3 3 T.κ0 ∧
            ∀ i, rootCube (m₀ := 1) (K := k + 1) z ∈
              blocksOf 1 (k + 1) Set.univ (I.Lab.ysite (I.y0 i)) := by
  obtain ⟨β₀, h3, H⟩ := e1MarksC_zeroClass_fromTowerG_anchor T.toG rfl
    (stepOutputPhysical T hHull) rfl rfl rfl rfl rfl hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z => ?_⟩
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hν0 (by simpa using hν) β hβ p₁
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T D) (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm (T.step k hk N₁ ν β p₁) rfl hp z
  simp only [corrF0_toG]
  exact G

open Classical in
/-- **The marks record of the energy term at the tower.**  The record of
`e1MarksC_zeroClass_fromTower_anchor` without its root clause. -/
theorem e1MarksC_zeroClass_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        ∃ I : E1MarksC (T.step k hk N₁ ν β p₁) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) z,
          I.𝒰 = Metric.ball (0 : ℂ) corrU ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
          I.F0 = (fun _ => corrF0 T k β p₁) ∧
          CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
            (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0 3 3 T.κ0 := by
  obtain ⟨β₀, h3, h⟩ := e1MarksC_zeroClass_fromTower_anchor T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z => ?_⟩
  obtain ⟨I, h1, h2, h3', h4, h5, -⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z
  exact ⟨I, h1, h2, h3', h4, h5⟩

open Classical in
/-- **The expansion of the local energy term at the tower.**  Beyond a threshold `β₀`, at every
scale datum and every root `z`, the local energy term `ℰ₁^{(k+1)}(z)` of the zero class is a sum
over finite sets `T` of level-one blocks of terms bounded by `K₀ e^{-κ' d_Ext(T)}`
(`e1loc_expansion_zeroClass_of_sum` with its hypothesis `hF` given by
`e1_hF_of_pairs_fromTower`).  This expands the zero-class local `ℰ₁(z)` of P4 (2.57) at the base
datum; the local `ℰ₀(z)` of Theorem 3.1 (a) also contains the determinant trace
(`thm31a_zeroClass_supp_fromTower`). -/
theorem e1loc_expansion_zeroClass_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ _ : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ,
          (T.step k hk N₁ ν β p₁).E1locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
            ∑ T', E T' ∧
          ∀ T', ‖E T'‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt T') := by
  obtain ⟨β₀, h3, h⟩ := e1loc_expansion_zeroClass_of_sum T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D z => ?_⟩
  obtain ⟨F₁, Sol, hpairs, h'⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  exact h' z (e1_hF_of_pairs_fromTower T D (by linarith) hp F₁ Sol
    (fun z b => (hpairs z b).1) z)

end Balaban.Inhabited
