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
# One energy coefficient family at the general tower

At a scale of the general tower `T : StepTowerG d L N κmin` with `T.m₀ = 1` (zero class), the
coefficients of the local energy term are assembled as one family
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (G z θ) C` in the datum `θ` of the physical
parameter space, from the landed pieces: the activity `A₀` of
`zeroSourceActivity_common_fromTowerG` (zero-source activity on the common labels, with a records
`C` of the output constants), the marks `e1MarkGParamG` of one family of decoupling pairs chosen
before every parameter, the locality premises of `E1ParamRawLocal.lean`, and
`paramMarked_analytic_local_bound` with the support lemmas of `GsumActiveParam.lean`.

* `e1MarkParam_pairs_fromTowerG`: the field theorem with the defining clauses of the pairs and the
  block dependence for every parameter exposed.
* `e1Mark_hG_rawY_fromTowerG`: the sharp locality premise `hG` of
  `paramMarked_analytic_local_bound`.
* `e1CoeffFamily_value_fromTowerG`: analyticity, locality, bound and support of the coefficient
  family, with the identity of the coefficient sum at `(rawOf D′, 0)` and the local energy term of
  the step with the datum `D′` of the chart with constant field `h₀`.
* `e1CoeffFamily_fromTowerG`: the corollary without the value clause.

The steps are stated over any `ϱ = rhoSepG d L T.m₁` with `S = hatStepKG … ϱ …`.
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

section Main

open Classical in
/-- **One energy coefficient family at the tower, with its value on the fibre `h ≡ h₀`.**  Beyond
a threshold `β₀`, at every scale datum there are one family of decoupling pairs `(F₁, Sol)`, a
label system `Lab₀` and an activity `A₀` on the common labels (with its identity for the
interpolation integral at every chart datum), chosen before every root and before every datum, such
that for every root `z` the pairs have the eight clauses, the activity and the marks carry a
`ParamMarkFamily` over `physV`, `ball 0 (17 / 16 : ℝ)` and `physCarrier`, and the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParamG … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 d L T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`;
and, for every datum `D′` of the chart with constant field `h₀`,
(v) the local energy term of the step with the datum `D′` is
`ℰ₁^{(k+1)}(z) = ∑_C c z (rawOf D′, 0) C`. -/
theorem e1CoeffFamily_value_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS))
            (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)),
      (∀ (D' : BgData S.G' N)
          (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν
          (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          (S.withDatum D' hDh).WoneC
              (zeroClass d L N₁ T.m₁ k N ϱ) s x =
            ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub N S.G'), g) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ)
          S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
        Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
          (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) A₀
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG S) z} =>
            commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
          (fun θ i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0G T k β p₁)
          (physV S S.a₁
            S.ν T.t)
          (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) (physCarrier S 1 hp)) ∧
        ∃ c : physParam N S →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff (S.blockSplit 1 hp).μ
            (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1DomG S) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
            (fun i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c θ C)
              (physV S S.a₁
                S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ∀ θ' ∈ physV S S.a₁
                S.ν T.t,
              physRestrict (N := N) (thickSet S.G'
                  (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C)))
                  (physIncl N S θ') → c θ C = c θ' C) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ∀ θ' ∈ physV S S.a₁
                S.ν T.t,
              physRestrict (N := N) (sitesOf C) (physIncl N S θ) =
                physRestrict (sitesOf C) (physIncl N S θ') →
                c θ C = c θ' C) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ‖c θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          ∀ (D' : BgData S.G' N)
              (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a
              S.ν (k + 1) 1 T.t D' →
            (S.withDatum D' hDh).E1locC
                (zeroClass d L N₁ T.m₁ k N ϱ) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
      0 < εH ∧
      εH ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' ∧
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
        DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) (Metric.ball (0 : ℂ) 2)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) Φ,
          AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
            e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t
              r.1 i r.2 Φ)
            (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16 : ℝ))) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ),
        DepOn (blocksOf 1 (k + 1) Set.univ
          ((commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁)
            (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
            (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).ysite
            (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)))
          (e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ),
          Measurable (e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ) Φ,
          ‖e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u Φ‖ ≤
            corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁)
                (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
                (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i))) ∧
      ∃ Jr : S.JointRep T.t (2 * p₁),
        ∀ (D' : BgData S.G' N),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
              (rawOf D', (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                ((S.blockSplit 1 hp).restr x) := by
  classical
  obtain ⟨βa, CE, CF, hβa3, -, -, hact⟩ := zeroSourceActivity_common_fromTowerG T C hKc hKall hH h0 h' hA p
  rw [hm₀] at hact
  obtain ⟨β₀, hmax, hR, hbud⟩ := exists_beta0_e1G T hm₀ hA p βa
  have hKc1 : K0 d L T.κ0 + 1 ≤ 2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0 := by
    have := T.marks_hKc; rwa [hm₀] at this
  refine ⟨β₀, (le_max_left _ _).trans hmax, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  have hβ3 : 3 ≤ β := ((le_max_left _ _).trans hmax).trans hβ
  have hβpos : 0 < β := by linarith
  have hβa : βa ≤ β := ((le_max_right _ _).trans hmax).trans hβ
  have hRU := hR k hk β hβ p₁ (show 0 < p₁ from hp) hp₁
  obtain ⟨F₁, Sol, hF⟩ := e1MarkParam_pairs_fromTowerG T hm₀ D h3N hN hν0.le hν hβpos rfl rfl hp hRU
  obtain ⟨Jr, val, I0, hFd, hεU, hval, hεpos, hamp, hθ, hstep, A, hAeq, hW1, hW2, hcom⟩ :=
    hact k hk N₁ (by rwa [hm₀] at h3N) hN ν hν0 hν β hβa p₁ (show 0 < p₁ from hp) hp₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨A0, hA0eq, hana, hdiffA, hcont, hsum, hdat, hWstep, hfam0, -⟩ :=
    hcom (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)
  have hU2 : (17 / 16 : ℝ) ≤ 2 := by norm_num
  have hF0 := corrF0G_pos T hk hβpos (show 0 < p₁ from hp)
  have hθ' := hstep
  refine ⟨F₁, Sol, {Y // Y ∈ I0.𝒴}, inferInstance, thickLabels I0.𝒴 I0.dom, _, A0,
    hdat, ?_, hεpos, hstep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  swap
  · exact hdiffA
  swap
  · intro z i Φ
    exact (hF z).2.2.2.2.1 i Φ
  swap
  · intro z θ i u
    exact ((hF z).2.2.2.1 {Y // Y ∈ I0.𝒴} (thickLabels I0.𝒴 I0.dom)).1 θ i u
  swap
  · intro z θ i u
    exact (hF z).2.2.1 θ i u
  swap
  · intro z θ i u Φ
    exact ((hF z).2.2.2.1 {Y // Y ∈ I0.𝒴} (thickLabels I0.𝒴 I0.dom)).2 θ i u Φ
  swap
  · refine ⟨Jr, fun D' hX => ?_⟩
    have hN1 : L ^ 1 ∣ N₁ := by rwa [hm₀] at h3N
    exact e1_common_activity_freeDatum_of_directTermsG T k hk N₁ hN1 ν hν0 hν β
      p₁ (show 0 < p₁ from hp) D _ rfl hp Jr val hval I0 hFd hεU A hAeq
      A0 hsum D' hX
  intro z
  obtain ⟨hP, hne, hmeas, hdb, hholG, hcontG, hspec⟩ := hF z
  obtain ⟨hdep, hbnd⟩ := hdb {Y // Y ∈ I0.𝒴} (thickLabels I0.𝒴 I0.dom)
  have hfam : ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
          (commonLabels (thickLabels I0.𝒴 I0.dom) (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)) A0
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (T.step k hk N₁ ν β p₁)) z} =>
            commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z i)
          (fun θ i u Φ => e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0G T k β p₁)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)
          (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp) := by
    obtain ⟨hA'⟩ := hfam0
    exact { isOpenV := hA'.isOpenV
            isOpenU := Metric.isOpen_ball
            seg := fun s hs => by
              rw [mem_ball_zero_iff]
              refine norm_ofReal_lt_of_mem hs ?_
              norm_num
            compact := hA'.compact
            measQ := hA'.measQ
            carried := hA'.carried
            meas := hmeas
            bound := hbnd
            holA := fun y Φ hΦ => (hA'.holA y Φ hΦ).mono
              (Set.prod_mono (subset_refl _) (Metric.ball_subset_ball hU2))
            holG := fun i Φ _ => hholG i Φ
            contA := fun y θ hθ u hu => hA'.contA y θ hθ u (Metric.ball_subset_ball hU2 hu)
            contG := fun i θ hθ u hu => hcontG i θ hθ u hu }
  refine ⟨hP, ⟨hfam⟩, _, fun _ _ => rfl, fun C => ?_, fun D' hDh hD => ?_⟩
  swap
  · exact e1Param_fibre_value_of_fields_fromTowerG T hm₀ D (by rwa [hm₀] at h3N) (by have := T.hL; omega) hβpos
      rfl (S := T.step k hk N₁ ν β p₁) rfl hp (e1DomG_isDj T hm₀ D rfl) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) z hP (thickLabels I0.𝒴 I0.dom) A0 hεpos hstep hdiffA hdat hmeas
      (fun θ _ => hdep θ) hbnd hholG D' hDh hD
  have hp0 : 0 < p₁ := hp
  have hprob := isProbabilityMeasure_fluctMeasure1 N hp
  have hN1 : L ^ 1 ∣ N₁ := by rwa [hm₀] at h3N
  have hlab : ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1DomG (T.step k hk N₁ ν β p₁)) z},
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
        ((commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by have := T.hL; omega) (fun _ => Set.univ)
          (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)).ysite
          (commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z
            i)) :=
    fun i => (bridgeFamily_spec hN1 (by have := T.hL; omega) (e1DomG_isDj T hm₀ D rfl) z i.2).2.1
  have hAloc : ∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := N) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl N (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
          (physIncl N (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, (commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by have := T.hL; omega) (fun _ => Set.univ)
          (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)).ysite y ⊆
          Yhat Set.univ (sitesOf C) → (A0 θ (s : ℂ)).H y = (A0 θ' (s : ℂ)).H y := by
    intro C
    subst hA0eq
    subst hAeq
    exact commonAct_zeroSourceAct_hA (T.step k hk N₁ ν β p₁) 1 _ hFd hN1 hp0 zero_le_two hεU
      T.κ0_ent T.marks_K0_le (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)
      (by have := T.hL; omega) (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two one_pos
      (fun θ => physRestrict (N := N) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl N (T.step k hk N₁ ν β p₁) θ)) C
      (fun θ _ θ' _ h Y hY => physRestrict_thickSet_agree _ _ h hY)
  have hGloc : ∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := N) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl N (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
          (physIncl N (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z},
        (commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by have := T.hL; omega) (fun _ => Set.univ)
          (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)).ysite
          (commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z
            i) ⊆ Yhat Set.univ (sitesOf C) →
        (fun Φ => e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i (s : ℂ) Φ) =
        (fun Φ => e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ' i (s : ℂ) Φ) := by
    intro C θ hθ θ' hθ' h s hs i hi
    have hu : ‖(s : ℂ)‖ < (17 / 16 : ℝ) := norm_ofReal_lt_of_mem hs (by norm_num)
    funext Φ
    rw [e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i (s : ℂ) Φ hθ.1 hu,
      e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ' i (s : ℂ) Φ hθ'.1 hu]
    exact markedOutDec_decMarkCorrTerm_raw_congr (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) hP (ρ := p₁) hp0 le_rfl hp T.t_pos _ hθ.1 hθ'.1
      (e1_rad_ltG T hk hβpos hp0 hRU hu.le) z Φ (physRestrict_thickSet_agree _ _ h hi)
  have hmain := fun C => paramMarked_analytic_local_bound (m₀ := 1) (j := k + 1) (Ω := Set.univ)
    ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ hN1 le_rfl isPiUnion_univ_K hfam
    (fun θ i s => hdep θ i s) T.marks_hκ0 hKc1 hεpos hne (fun _ => hF0) T.marks_hκ'
    T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') C
    (fun θ => physRestrict (N := N) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl N (T.step k hk N₁ ν β p₁) θ))
    (hAloc C) (hGloc C)
  have hmainY := fun C => paramMarked_analytic_local_bound (m₀ := 1) (j := k + 1)
    (Ω := Set.univ) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ hN1 le_rfl
    isPiUnion_univ_K hfam (fun θ i s => hdep θ i s) T.marks_hκ0 hKc1 hεpos hne
    (fun _ => hF0) T.marks_hκ' T.marks_hκG T.marks_hκ
    (by unfold stepTheta at hθ'; exact hθ') C
    (fun θ => physRestrict (N := N) (sitesOf C) (physIncl N (T.step k hk N₁ ν β p₁) θ))
    (by
      subst hA0eq
      subst hAeq
      exact commonAct_zeroSourceAct_hA_rawY (T.step k hk N₁ ν β p₁) 1 _ hFd hN1 hp0
        zero_le_two hεU T.κ0_ent T.marks_K0_le (fun _ => Set.univ)
        (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl) (by have := T.hL; omega)
        (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two one_pos C)
    (by
      exact e1Mark_hG_rawY_fromTowerG T hm₀ D hN hν0.le hν hβpos rfl rfl hp hRU F₁ Sol z hspec
        (thickLabels I0.𝒴 I0.dom) hN1 C)
  have hgm : ∀ (θ : physParam N (T.step k hk N₁ ν β p₁)), ∀ (i : {Y' // Y' ∈ bridgeFamily 1
      (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      Measurable (fun Φ => e1MarkGParamG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) := hmeas
  refine ⟨(hmain C).1, (hmain C).2.1, (hmainY C).2.1,
    fun θ hθ => ?_, fun θ hne0 => ?_⟩
  · exact ((hmain C).2.2 θ hθ).trans (mul_le_mul_of_nonneg_right
      (by have h := hbud k hk N₁ h3N ν β hβ p₁ (show 0 < p₁ from hp) hp₁ D rfl z; rw [hm₀] at h; exact h) (Real.exp_pos _).le)
  · exact ⟨mem_of_gsumCoeff_ne_zero_of_labels hN1 ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (A0 θ) _ _ (hgm θ) (hdep θ) (hbnd θ) T.marks_hκ0 hKc1 hεpos (fun _ => hF0)
      T.marks_hκ' T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') hlab hne0,
      (gsumCoeff_ne_zero_active hN1 ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (A0 θ) _ _ (hgm θ) (hdep θ) (hbnd θ) T.marks_hκ0 hKc1 hεpos (fun _ => hF0)
      T.marks_hκ' T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') hne0).2⟩

open Classical in
/-- **One energy coefficient family at the tower.**  Beyond a threshold `β₀`, at every scale datum
there are one family of decoupling pairs `(F₁, Sol)`, a label system `Lab₀` and an activity `A₀` on
the common labels (the zero-source activity of `zeroSourceActivity_common_fromTower`, with its
identity for the interpolation integral at every chart datum), chosen before every root, such that
for every root `z` the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParamG … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 d L T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`.
The family `A₀`, `c` and the marks carry a `ParamMarkFamily` over `physV`, `ball 0 (17 / 16 : ℝ)` and
`physCarrier`. -/
theorem e1CoeffFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS))
            (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)),
      (∀ (D' : BgData S.G' N)
          (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν
          (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          (S.withDatum D' hDh).WoneC
              (zeroClass d L N₁ T.m₁ k N ϱ) s x =
            ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub N S.G'), g) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) ∧
      ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ)
          S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
        Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
          (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) A₀
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG S) z} =>
            commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
          (fun θ i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0G T k β p₁)
          (physV S S.a₁
            S.ν T.t)
          (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) (physCarrier S 1 hp)) ∧
        ∃ c : physParam N S →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff (S.blockSplit 1 hp).μ
            (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1DomG S) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
            (fun i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          ∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c θ C)
              (physV S S.a₁
                S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ∀ θ' ∈ physV S S.a₁
                S.ν T.t,
              physRestrict (N := N) (thickSet S.G'
                  (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C)))
                  (physIncl N S θ') → c θ C = c θ' C) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ‖c θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C)) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp₁ D ϱ hϱ S hS hp => ?_⟩
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ := H k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, -⟩ := hz.1 z
  exact ⟨h1, h2, c, hc, fun C =>
    ⟨(hcl C).1, (hcl C).2.1, (hcl C).2.2.2.1, (hcl C).2.2.2.2⟩⟩

end Main

end Balaban.Inhabited
