/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkCorrSumFromTowerG
public import Balaban.Inhabited.E1MarkParamCommonG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The energy record at every chart datum of the fibre `h ≡ h₀`, for the parameter marks, at the general tower

General versions of `e1_hF_param_of_pairs_fromTower`, `e1MarksC_withDatum_of_fields_fromTower` and
`e1Param_fibre_value_of_fields_fromTower`.  The step `S` is stated over any
`ϱ = rhoSepG d L T.m₁` (`hϱ`) with `hS : S = hatStepKG … ϱ …`; the cover index is `1`
(`hm₀ : T.m₀ = 1`).

* `e1_hF_param_of_pairs_fromTowerG`: for pairs with the eight clauses, real `s ∈ [0,1]` and almost
  every hat field `x`, the masked derivative `DΦ₁(s ψ′)[M_z ψ′]` of the step with the datum `D′`
  is the sum over the bridge family of `z` of the parameter marks `e1MarkGParamG` at `θ′`.
* `e1MarksC_withDatum_of_fields_fromTowerG`: the record `E1MarksC (S.withDatum D′)` whose activity,
  anchors and marks are the values at `θ′` of the family `(A₀, commonAnchor, e1MarkGParamG)`.
* `e1Param_fibre_value_of_fields_fromTowerG`: the local energy term of the step with the datum
  `D′` is the sum of the parameter coefficients at `θ′`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **The physical sum identity for the parameter marks, at every chart datum of the fibre.**
At the step `S = T.step k hk N₁ ν β p₁` of a scale of the tower, let `(F₁ b, Sol b)` be a pair
with the eight clauses for every block `b` (mask `blockU z`, covers of the scale, `m₀ = 1`,
`j = k`, the constants `BG₂ = T.BG₂`, `κ = T.κ`, `eps = δ₁ = T.t`, `cψ = p₁`), and let `D′` be a
datum of the chart with `D′.h ≡ h₀`.  Then for real `s ∈ [0,1]` and almost every hat field `x` of
the fluctuation measure,
`DΦ₁(s ψ′)[M_z ψ′] = ∑_{Y′ ∈ 𝒴_z} e1MarkGParamG … z (rawOf D′, 0) Y′ s (restr x)`,
where `Φ₁`, `ψ′` and the mask are those of the step with the datum `D′`.  This is the field `hF`
of `InterpMarks` for the marks of the parameter family at the point `(rawOf D′, 0)`. -/
theorem e1_hF_param_of_pairs_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁) (hβ : 0 < β)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
  (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (hp : 0 < S.p₁) {BG κdec : ℝ}
    (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
    (z : RootIdx d L N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 T.t D') :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ ((S.withDatum D' hDh).Phi1C (zeroClass d L N₁ T.m₁ k N ϱ))
          ((s : ℂ) • (S.withDatum D' hDh).shiftUC x))
          ((S.withDatum D' hDh).maskUC z ((S.withDatum D' hDh).shiftUC x)) =
        ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
          e1MarkGParamG S F₁ Sol p₁ hp z T.t
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
              (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) i (s : ℂ)
            ((S.blockSplit 1 hp).restr x) := by
  intro s hs
  have hsU : ‖(s : ℂ)‖ < (17 / 16 : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; linarith [hs.2]
  have hΘ : rawOf D' ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t := ⟨D', hD, rfl⟩
  -- the tower identity, for pairs typed over the step with the datum `D'`
  have key : ∀ (G₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams (S.withDatum D' hDh).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((S.withDatum D' hDh).G'.Ω 1 × Fin N → ℂ) × ((S.withDatum D' hDh).G'.Ω 1 → ℂ))
      (Sl : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (S.withDatum D' hDh).G') ×
            Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
      (hq : 0 < (S.withDatum D' hDh).p₁),
      (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ)
        (S.withDatum D' hDh).hG' (((S.withDatum D' hDh).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (S.withDatum D' hDh).a₁ (S.withDatum D' hDh).ν BG T.BG₂ T.κ T.t T.t κdec p₁
        ((S.withDatum D' hDh).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (G₁ b) (Sl b)) →
      ∀ᵐ x ∂(S.withDatum D' hDh).nuFl,
        (fderiv ℂ ((S.withDatum D' hDh).Phi1C (zeroClass d L N₁ T.m₁ k N ϱ))
            ((s : ℂ) • (S.withDatum D' hDh).shiftUC x))
            ((S.withDatum D' hDh).maskUC z ((S.withDatum D' hDh).shiftUC x)) =
          ∑ Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (fun b => polyDom (S.withDatum D' hDh).G'
                (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k b))) z,
            markedOutDec 1 (fun _ => Set.univ)
              (fun b => polyDom (S.withDatum D' hDh).G'
                (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k b))) z
              (decMarkCorrTerm (S.withDatum D' hDh)
                (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
                (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1
                (S.withDatum D' hDh).a₁ (S.withDatum D' hDh).ν
                (((S.withDatum D' hDh).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) G₁ Sl
                ((S.withDatum D' hDh).blockU z) p₁ hq ((S.withDatum D' hDh).β : ℂ)
                (rawOf (S.withDatum D' hDh).D') (s : ℂ)
                (((S.withDatum D' hDh).blockSplit 1 hq).restr x)) Y' := by
    subst hS
    subst hϱ
    intro G₁ Sl hq hQ
    exact ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTowerG T D hβ hq rfl
      (S₀ := T.step k hk N₁ ν β p₁) rfl D' hDh hD
      (S := (T.step k hk N₁ ν β p₁).withDatum D' hDh) rfl hq z G₁ Sl hQ hs
  refine (key F₁ Sol hp hP).mono fun x hx => hx.trans ?_
  refine Eq.trans (Finset.sum_subtype _ (fun _ => Iff.rfl) _)
    (Finset.sum_congr rfl fun i _ => ?_)
  exact (e1MarkGParamG_of_mem S F₁ Sol p₁ hp z T.t
    ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) i (s : ℂ)
    ((S.blockSplit 1 hp).restr x) hΘ hsU).symm

section Record

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
  (D : StepScaleDataG T k hk N₁ ν β p₁) (hN3 : L ^ 1 ∣ N₁) (hL : 2 ≤ L) (hβ : 0 < β)
  {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) {S : StepSetting d L N₁ T.m₁ k N ϱ}
  (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
  (hp : 0 < S.p₁) (hdj : ∀ b, ∀ Y ∈ e1DomG S b, IsDj 1 (k + 1) Y) {BG κdec : ℝ}
  (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
    DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
  (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
      ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
  (z : RootIdx d L N₁ T.m₁ (k + 1))
  (hP : ∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG'
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
    (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
    (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
  {Lb : Type} [Fintype Lb]
  (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
    Set.univ Lb) {εH : ℝ}
  (A₀ : physParam N S → ℂ →
    LabelAct (commonLabels Lab₀ hN3 hL (fun _ => Set.univ) (e1DomG S) hdj)
      (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0))
  (hεpos : 0 < εH) (hε : εH ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ')
  (hdiffA : ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
    DifferentiableOn ℂ (fun u => (A₀ e u).H y Φ) (Metric.ball (0 : ℂ) 2))
  (hdat : ∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
    XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N ϱ) s x =
        ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (s : ℂ)).H y
          ((S.blockSplit 1 hp).restr x))
  (hmeas : ∀ (θ : physParam N S)
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ),
    Measurable (e1MarkGParamG S F₁ Sol p₁ hp z T.t θ i u))
  (hdep : ∀ θ ∈ physV S S.a₁ S.ν T.t,
    ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ),
    DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab₀ hN3 hL (fun _ => Set.univ) (e1DomG S) hdj).ysite
        (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)))
      (e1MarkGParamG S F₁ Sol p₁ hp z T.t θ i u))
  (hbnd : ∀ (θ : physParam N S)
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ) Φ,
    ‖e1MarkGParamG S F₁ Sol p₁ hp z T.t θ i u Φ‖ ≤
      corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
        (commonLabels Lab₀ hN3 hL (fun _ => Set.univ) (e1DomG S) hdj).dl
          (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)))
  (hholG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
    AnalyticOnNhd ℂ (fun q : physParam N S × ℂ => e1MarkGParamG S F₁ Sol p₁ hp z T.t q.1 i q.2 Φ)
      (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16 : ℝ)))
  (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ))
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 T.t D')

include hm₀ D hβ hϱ hS hP hεpos hε hdiffA hdat hmeas hdep hbnd hholG hD in
open Classical in
/-- **The energy marks record at a chart datum of the fibre, with the data of the parameter
family.**  At the step `S` of a scale of the tower let the pairs `(F₁ b, Sol b)` have the eight
clauses for the root `z`, let `A₀` be an activity family on the common labels with a positive
amplitude below `stepTheta`, holomorphic in the interpolation parameter on `ball 0 2` for every
parameter of `physV`, and summing to `W₁` of the step with the datum `D″` at `(rawOf D″, g)` for
every datum `D″` of the chart with constant field `h₀`; let the parameter marks `e1MarkGParam` of
the pairs be measurable, block local on `physV`, bounded by `corrF0 · exp (−(2 κ_dec − 1) d_l)`
and analytic on `physV × ball 0 (17 / 16 : ℝ)`.  Then for every datum `D′` of the chart with constant
field `h₀` there is a record `E1MarksC (S.withDatum D′)` of the interpolation integral
`ℰ₁^{(k+1)}(z)` of the step with the datum `D′`, with disc `ball 0 (17 / 16 : ℝ)`, `κ_G = 2 κ_dec − 1`,
`κ' = T.κ'`, `F₀ = corrF0`, whose interpolation coefficient at every `C` is the parameter
coefficient `gsumCoeff … (A₀ θ′) (commonAnchor …) (e1MarkGParamG … θ′) C` at `θ′ = (rawOf D′, 0)`,
and whose budget is `C_PE ∑_{Y′} corrF0 e^{-κ₀ d(Y′)}`. -/
theorem e1MarksC_withDatum_of_fields_fromTowerG :
    ∃ I : E1MarksC (S.withDatum D' hDh) (zeroClass d L N₁ T.m₁ k N ϱ)
        ((S.withDatum D' hDh).blockSplit 1 hp) z,
      I.𝒰 = Metric.ball (0 : ℂ) (17 / 16 : ℝ) ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.F0 = (fun _ => corrF0G T k β p₁) ∧
      (∀ C, interpCoeff I C = gsumCoeff (S.blockSplit 1 hp).μ
        (commonLabels Lab₀ hN3 hL (fun _ => Set.univ) (e1DomG S) hdj)
        (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)))
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z} =>
          commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
        (fun i u Φ => e1MarkGParamG S F₁ Sol p₁ hp z T.t
          ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) i u Φ) C) ∧
      CPE d L I.Kc I.κH I.κ0 I.κ' * (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) =
        CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          ∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
            corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1) := by
  classical
  have hp0 : 0 < p₁ := by subst hS; exact hp
  have hne : Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z} := by
    subst hS
    obtain ⟨Y, hY⟩ := e1DomG_bridgeFamily_nonempty T hm₀ D hϱ z
    exact ⟨⟨Y, hY⟩⟩
  have hθ' : ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈ physV S S.a₁ S.ν T.t :=
    (mk_mem_physFibre S hDh hD (g := 0) (by simp)).1
  have hU2 : (17 / 16 : ℝ) ≤ 2 := by norm_num
  refine ⟨{
      Lb := Lb ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1DomG S)
      εH := εH
      κH := 2 * T.κdec - 1
      κ0 := T.κ0
      Kc := (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)
      Lab := commonLabels Lab₀ hN3 hL (fun _ => Set.univ) (e1DomG S) hdj
      ι := {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}
      nonempty := hne
      κG := 2 * T.κdec - 1
      κ' := T.κ'
      F0 := fun _ => corrF0G T k β p₁
      hN := hN3
      𝒰 := Metric.ball (0 : ℂ) (17 / 16 : ℝ)
      isOpen := Metric.isOpen_ball
      seg := fun s hs => by
        rw [mem_ball_zero_iff]
        refine norm_ofReal_lt_of_mem hs ?_
        norm_num
      A := fun u => A₀ (⟨rawOf D', rawOf_mem_rawSub _⟩,
        (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) u
      y0 := fun i => commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i
      G := fun i u Φ => e1MarkGParamG S F₁ Sol p₁ hp z T.t
        (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) i u Φ
      meas := fun i u => hmeas _ i u
      dep := fun i u => hdep _ hθ' i u
      bound := fun i u Φ => hbnd _ i u Φ
      holA := fun y Φ => (hdiffA _ hθ' y Φ).mono (ball_subset_ball hU2)
      holG := fun i Φ => ((hholG i Φ).differentiableOn).comp
        (f := fun u : ℂ => ((((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) : physParam N S), u))
        (s := Metric.ball (0 : ℂ) (17 / 16 : ℝ))
        ((differentiableOn_const _).prodMk differentiableOn_id) (fun u hu => ⟨hθ', hu⟩)
      hκ0 := T.marks_hκ0
      hKc := by have := T.marks_hKc; rwa [hm₀] at this
      hεpos := hεpos
      hF0 := fun _ => corrF0G_pos T hk hβ hp0
      hκ' := T.marks_hκ'
      hκG := T.marks_hκG
      hκ := T.marks_hκ
      hε := by unfold stepTheta at hε; exact hε
      hW := fun s hs => hdat D' hDh hD 0 s hs
      hF := e1_hF_param_of_pairs_fromTowerG T D hβ hϱ hS hp F₁ Sol z hP D' hDh hD },
    rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

include hm₀ D hβ hϱ hS hP hεpos hε hdiffA hdat hmeas hdep hbnd hholG hD in
open Classical in
/-- **The value of the parameter coefficients on the fibre `h ≡ h₀`.**  Under the hypotheses of
`e1MarksC_withDatum_of_fields_fromTower`, for every datum `D′` of the chart with constant field
`h₀`, the local energy term `ℰ₁^{(k+1)}(z)` of the step with the datum `D′` is the sum over the
finite sets `C` of level-one blocks of the parameter coefficients
`gsumCoeff … (A₀ θ′) (commonAnchor …) (e1MarkGParamG … θ′) C` at `θ′ = (rawOf D′, 0)`. -/
theorem e1Param_fibre_value_of_fields_fromTowerG :
    (S.withDatum D' hDh).E1locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
      ∑ C, gsumCoeff (S.blockSplit 1 hp).μ
        (commonLabels Lab₀ hN3 hL (fun _ => Set.univ) (e1DomG S) hdj)
        (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)))
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z} =>
          commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
        (fun i u Φ => e1MarkGParamG S F₁ Sol p₁ hp z T.t
          ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) i u Φ) C := by
  obtain ⟨I, -, -, -, -, hc, -⟩ := e1MarksC_withDatum_of_fields_fromTowerG T hm₀ D hN3 hL hβ hϱ hS hp hdj
    F₁ Sol z hP Lab₀ A₀ hεpos hε hdiffA hdat hmeas hdep hbnd hholG D' hDh hD
  exact ((interpCoeff_spec I).1).trans (Finset.sum_congr rfl fun C _ => hc C)

end Record

end Balaban.Inhabited
