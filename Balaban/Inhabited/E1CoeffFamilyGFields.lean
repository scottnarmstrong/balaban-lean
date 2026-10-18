/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarkParamCommonG
public import Balaban.Inhabited.E1ParamRawLocal
public import Balaban.Fluctuation.GsumActiveParam
public import Balaban.Inhabited.E1ParamFibreValueG
public import Balaban.Inhabited.ZeroSourceActivityCommon
public import Balaban.Inhabited.OffFibreE1ActivityG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The mark fields of the energy coefficient family at the general tower

`e1DomG_isDj_of_eq`, `e1MarkParam_pairs_fromTowerG` and `e1Mark_hG_rawY_fromTowerG`, moved here from
`E1CoeffFamilyG.lean` (names and statements unchanged); they are used by
`e1CoeffFamily_value_fromTowerG_core` (`E1CoeffFamilyGCore.lean`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

/-- The label domains of a step equal to the step of the tower are domains of the level `k + 1`
(`e1DomG_isDj`, stated for an arbitrary step `S` equal to `hatStepKG … ϱ …`). -/
theorem e1DomG_isDj_of_eq {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    {S : StepSetting d L N₁ T.m₁ k N ϱ} (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) :
    ∀ b, ∀ Y ∈ e1DomG S b, IsDj 1 (k + 1) Y := by
  subst hS
  exact e1DomG_isDj T hm₀ D hϱ

section Fields

open Classical in
/-- **The mark fields of the parameter family, with the pairs.**  One family of pairs
`(F₁, Sol)`, chosen before every parameter and every root, such that for every root `z`: the pairs
satisfy `MarkedBlockExpansionDecPair`; the bridge family is nonempty; the marks `e1MarkGParam` are
measurable in `Φ`; for every label system on which the common labels are built, for every
parameter `θ` (not only on `physV`), they depend only on the blocks of the common label of their
anchor and are bounded by `corrF0 · exp (−(2 κ_dec − 1) d_l)`; they are analytic in `(θ, u)` on
`physV × ball 0 (17 / 16 : ℝ)` and continuous in the configuration on the carrier. -/
theorem e1MarkParam_pairs_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (h3N : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) :
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
    ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
      (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ)
        S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
        (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z} ∧
      (∀ (θ : physParam N S)
        (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
        (u : ℂ), Measurable (e1MarkGParamG S (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG S) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)))
            (e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
              z T.t θ i u)) ∧
        (∀ (θ : physParam N S)
            (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG S) z}) (u : ℂ) Φ,
          ‖e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              T.t θ i u Φ‖ ≤
            corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
        (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
            T.t p.1 i p.2 Φ)
          (physV S S.a₁ S.ν T.t
            ×ˢ Metric.ball (0 : ℂ) (17 / 16 : ℝ))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}),
        ∀ θ ∈ physV S S.a₁
            S.ν T.t,
        ∀ u ∈ Metric.ball (0 : ℂ) (17 / 16 : ℝ),
          ContinuousOn (e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u) (physCarrier S 1 hp)) ∧
      -- the defining properties of the pair of every block
      (∀ b, (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
        InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D →
        ∀ (φ : S.G'.Ω 1 × Fin N → ℂ) (α : S.G'.Ω 1 → ℂ),
          IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
          (F₁ (z, b)) (s, rawOf D) = (φ, α)) ∧
      (∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
        StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
          ((Sol (z, b)) p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
          Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          SupBounds (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol (z, b)) p).2))) := by
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  classical
  have hp' : 0 < (T.step k hk N₁ ν β p₁).p₁ := hp
  have hp0 : 0 < p₁ := hp
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  obtain ⟨F₁, Sol, hF⟩ := markCorrFamily_fromTowerG T hm₀ D hN hν0 hν hβ hp0 hRU rfl rfl hp
  refine ⟨F₁, Sol, fun z => ?_⟩
  obtain ⟨hP, hJ2, hJ4, hcnt, hblk⟩ := hF z
  have hout := markedOutDecCorr_fields (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).hG'
    T.hd (by rwa [hm₀] at h3N) (fun b => (hV b).1) (fun b => (hV b).2.2.1) z
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) hP hJ2 hJ4 (ρ := p₁) hp le_rfl hp' T.t_pos
    (((T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)
  obtain ⟨hmeas, hdep, hhol⟩ := hout
  have hF0 := corrF0G_pos T hk hβ hp0
  have hR := corrRG_pos T hk (by have := scalePosG T k; positivity : 0 < β * (L : ℝ) ^ (k * (d - 2))) hp0
  have hdepG : ∀ (θ : physParam N (T.step k hk N₁ ν β p₁))
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1DomG (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
          z T.t θ i u) := by
    intro θ i u
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
        XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight L (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < (17 / 16 : ℝ)
    · have e : e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
        funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2
      rw [e]
      exact hdep i.1 i.2 _ hc.1 u (e1_rad_ltG T hk hβ hp0 hRU hc.2.le)
    · intro Φ Φ' _
      rw [e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ hc,
        e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ' hc]
  have hbdG : ∀ (θ : physParam N (T.step k hk N₁ ν β p₁))
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1DomG (T.step k hk N₁ ν β p₁)) z}) (u : ℂ) Φ,
      ‖e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
        T.t θ i u Φ‖ ≤
        corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) i.1) := by
    intro θ i u Φ
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
        XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight L (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < (17 / 16 : ℝ)
    · rw [e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2]
      exact (hcnt _ hc.1 u hc.2.le Φ).1 i.1
    · rw [e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ hc, norm_zero]
      positivity
  have hmeasG : ∀ (θ : physParam N (T.step k hk N₁ ν β p₁))
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1DomG (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      Measurable (e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u) := by
    intro θ i u
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
        XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight L (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < (17 / 16 : ℝ)
    · have e : e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
        funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2
      rw [e]
      exact hmeas i.1 _ hc.1 u (e1_rad_ltG T hk hβ hp0 hRU hc.2.le)
    · have e : e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = fun _ => 0 :=
        funext fun Φ => e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ hc
      rw [e]
      exact measurable_const
  have hopen : IsOpen (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
      (T.step k hk N₁ ν β p₁).ν T.t) :=
    isOpen_physV _ _ _ _ (bgHyp_lvG T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν)
  refine ⟨hP, ?_, hmeasG, fun Lb _ Lab => ⟨fun θ i u => ?_, fun θ i u Φ => ?_⟩, ?_, ?_,
    fun b => (hblk b).2.2.2.2.2⟩
  · obtain ⟨Y, hY⟩ := e1DomG_bridgeFamily_nonempty T hm₀ D rfl z
    exact ⟨⟨Y, hY⟩⟩
  · exact (commonAnchor_marks_fields (Lab := Lab)
      (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega) (fun _ => Set.univ)
      (e1DomG (T.step k hk N₁ ν β p₁)) ((e1DomG_isDj T hm₀ D rfl)) z (ι := {Y' // Y' ∈ bridgeFamily 1
        (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z}) id (fun _ => corrF0G T k β p₁)
      (2 * T.κdec - 1)
      (fun i u => e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z T.t θ i u) (hdepG θ) (hbdG θ)).1 i u
  · exact hbdG θ i u Φ
  · intro i Φ
    have han := hhol i.1 Φ (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) hR hR
      (e1_rad_RR_ltG T hk hβ hp0)
    have hmono := han.mono (Set.prod_mono (subset_refl _)
      (Metric.ball_subset_ball (by linarith : (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)))
    refine hmono.congr (hopen.prod Metric.isOpen_ball) fun p hp'' => ?_
    exact (e1MarkGParamG_of_mem _ _ _ _ hp z T.t p.1 i p.2 Φ hp''.1.1
      (mem_ball_zero_iff.1 hp''.2)).symm
  · intro i θ hθ u hu
    have hu' : ‖u‖ < (17 / 16 : ℝ) := mem_ball_zero_iff.1 hu
    have e : e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
      funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hθ.1 hu'
    rw [e]
    refine (continuous_markedOutDec_decMarkCorrTerm (T.step k hk N₁ ν β p₁) _ _ p₁ hp _ _ _ z
      i.1 fun b Y => ?_).continuousOn
    exact ((hblk b).2.1 Y _ hθ.1 u (e1_rad_ltG T hk hβ hp0 hRU hu'.le)).1

open Classical in
/-- **The sharp premise `hG` of `paramMarked_analytic_local_bound` at the tower.**  For pairs
`(F₁ (z, b), Sol (z, b))` with the defining properties `hspec` (the last clause of
`e1MarkParam_pairs_fromTower`), the marks `e1MarkGParam` of the root `z` at two parameters of
`physV` with equal restrictions of `(raw datum, source)` to `sitesOf C` coincide (for every real
`s ∈ [0, 1]`), at every bridge label whose anchor's site set lies in `Ŷ(sitesOf C)`.  This is
the conclusion of `markedOutDec_decMarkCorrTerm_hG_rawY` for `π θ = physRestrict (sitesOf C)
(physIncl N S θ)`, with the cover, margin and rate hypotheses discharged from the data `D` of the
tower. -/
theorem e1Mark_hG_rawY_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    {S : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
    (z : RootIdx d L N₁ T.m₁ (k + 1))
    (hspec : ∀ b, (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
        InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D →
        ∀ (φ : S.G'.Ω 1 × Fin N → ℂ) (α : S.G'.Ω 1 → ℂ),
          IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
          (F₁ (z, b)) (s, rawOf D) = (φ, α)) ∧
      (∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
        StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
          ((Sol (z, b)) p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
          Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          SupBounds (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
          (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol (z, b)) p).2)))
    {Lb : Type} (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb) (hN1 : L ^ 1 ∣ N₁)
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    ∀ θ ∈ physV S S.a₁ S.ν T.t,
    ∀ θ' ∈ physV S S.a₁ S.ν T.t,
      physRestrict (N := N) (sitesOf C) (physIncl N S θ) =
        physRestrict (sitesOf C) (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
        (commonLabels Lab hN1 (by have := T.hL; omega) (fun _ => Set.univ)
          (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).ysite
          (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i) ⊆
          Yhat Set.univ (sitesOf C) →
        (fun Φ => e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i (s : ℂ) Φ) =
        (fun Φ => e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ' i (s : ℂ) Φ) := by
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  classical
  have hp0 : 0 < p₁ := hp
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  intro θ hθ θ' hθ' h s hs i hi
  have hu : ‖(s : ℂ)‖ < (17 / 16 : ℝ) := norm_ofReal_lt_of_mem hs (by norm_num)
  have hagT := ((physRestrict_physIncl_eq_iff (T.step k hk N₁ ν β p₁) (sitesOf C) θ θ').1 h).1
  rw [Yhat_univ] at hi
  funext Φ
  rw [e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i (s : ℂ) Φ hθ.1 hu,
    e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ' i (s : ℂ) Φ hθ'.1 hu]
  exact markedOutDec_decMarkCorrTerm_rawY_congr (T.step k hk N₁ ν β p₁) D.core
    hk (T.step k hk N₁ ν β p₁).hG hp0.le T.large_block T.dom_margin T.coer_margin T.δc_small
    (hatConn_lvTopG T.hL) (rowInHat_lvG hk (dgSetting_lvG T.hd T.hL T.m₁_four hN hν0 hν)) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
    (fun b => (hV b).1) (fun b => (hV b).2.1) (fun b => (hspec b).1) (fun b => (hspec b).2)
    (fun b => (hV b).2.2.2.2.1) (fun b => (hV b).2.2.2.2.2.1) hp0 le_rfl hp T.t_pos ((T.step k hk N₁ ν β p₁).β : ℂ) hθ.1 hθ'.1
    (e1_rad_ltG T hk hβ hp0 hRU hu.le) z Φ (agreeOn_mono hi hagT)

end Fields

end Balaban.Inhabited
