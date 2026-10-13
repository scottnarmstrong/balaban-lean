/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkCorrSumFromTower
public import Balaban.Inhabited.E1MarkParamCommon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The energy record at every chart datum of the fibre `h ≡ h₀`, for the parameter marks

At a scale of the shared tower (`d = L = 3`, `N = 2`, zero class), let `S` be the step, `D′` a
datum of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with the constant field `h₀`, and
`θ′ = (rawOf D′, 0)` the corresponding point of the physical parameter space.  The step with the
datum `D′` is `S.withDatum D′`; its fluctuation measure, block split, masks and label domains are
those of `S`, and only the covariance square root (hence the shift `ψ′`, `W₁` and `Φ₁`) depends on
`D′`.

Everything here is stated for a family of decoupling pairs `(F₁ b, Sol b)` and an activity family
`A₀` given as arguments, with the clauses that the landed theorems return for them, so that one
choice of the pairs and of the activity serves every root and every datum.

* `e1_hF_param_of_pairs_fromTower`: for pairs with the eight clauses, real `s ∈ [0,1]` and almost
  every hat field `x`, the masked derivative `DΦ₁(s ψ′)[M_z ψ′]` of the step with the datum `D′` is
  the sum over the bridge family of `z` of the parameter marks `e1MarkGParam` at `θ′` (the field
  `hF` of `InterpMarks`; both cutoffs of `e1MarkGParam` are inactive at `θ′` and real `s ∈ [0,1]`).
* `e1MarksC_withDatum_of_fields_fromTower`: the record `E1MarksC (S.withDatum D′)` whose activity,
  anchors and marks are the values at `θ′` of the family `(A₀, commonAnchor, e1MarkGParam)`; its
  interpolation coefficient is the parameter coefficient `gsumCoeff` at `θ′`.
* `e1Param_fibre_value_of_fields_fromTower`: the local energy term of the step with the datum `D′`
  is the sum of the parameter coefficients at `θ′`.
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
`DΦ₁(s ψ′)[M_z ψ′] = ∑_{Y′ ∈ 𝒴_z} e1MarkGParam … z (rawOf D′, 0) Y′ s (restr x)`,
where `Φ₁`, `ψ′` and the mask are those of the step with the datum `D′`.  This is the field `hF`
of `InterpMarks` for the marks of the parameter family at the point `(rawOf D′, 0)`. -/
theorem e1_hF_param_of_pairs_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) (hβ : 0 < β)
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
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
      (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 T.t D') :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (fderiv ℂ ((S.withDatum D' hDh).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
          ((s : ℂ) • (S.withDatum D' hDh).shiftUC x))
          ((S.withDatum D' hDh).maskUC z ((S.withDatum D' hDh).shiftUC x)) =
        ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
          e1MarkGParam S F₁ Sol p₁ hp z T.t
            ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
            ((S.blockSplit 1 hp).restr x) := by
  intro s hs
  have hsU : ‖(s : ℂ)‖ < corrU := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; unfold corrU; linarith [hs.2]
  have hΘ : rawOf D' ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t := ⟨D', hD, rfl⟩
  -- the tower identity, for pairs typed over the step with the datum `D'`
  have key : ∀ (G₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams (S.withDatum D' hDh).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((S.withDatum D' hDh).G'.Ω 1 × Fin 2 → ℂ) × ((S.withDatum D' hDh).G'.Ω 1 → ℂ))
      (Sl : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (S.withDatum D' hDh).G') ×
            Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
      (hq : 0 < (S.withDatum D' hDh).p₁),
      (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (S.withDatum D' hDh).hG' (((S.withDatum D' hDh).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (S.withDatum D' hDh).a₁ (S.withDatum D' hDh).ν BG T.BG₂ T.κ T.t T.t κdec p₁
        ((S.withDatum D' hDh).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (G₁ b) (Sl b)) →
      ∀ᵐ x ∂(S.withDatum D' hDh).nuFl,
        (fderiv ℂ ((S.withDatum D' hDh).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
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
    intro G₁ Sl hq hQ
    exact ae_fderiv_mask_eq_sum_markedOutDec_decMarkCorr_fromTower T D hβ hq D' hDh hD
      (S := (T.step k hk N₁ ν β p₁).withDatum D' hDh) rfl hq z G₁ Sl hQ hs
  refine (key F₁ Sol hp hP).mono fun x hx => hx.trans ?_
  refine Eq.trans (Finset.sum_subtype _ (fun _ => Iff.rfl) _)
    (Finset.sum_congr rfl fun i _ => ?_)
  exact (e1MarkGParam_of_mem S F₁ Sol p₁ hp z T.t
    ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
    ((S.blockSplit 1 hp).restr x) hΘ hsU).symm

section Record

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
  (D : StepScaleData T k hk N₁ ν β p₁) (hN3 : 3 ^ 1 ∣ N₁) (hβ : 0 < β)
  {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁)
  (hp : 0 < S.p₁) (hdj : ∀ b, ∀ Y ∈ e1Dom S b, IsDj 1 (k + 1) Y) {BG κdec : ℝ}
  (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
    DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
      (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
  (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
      ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
  (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
  (hP : ∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁ (S.blockU z)
    (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
    (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
  {Lb : Type} [Fintype Lb]
  (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
    Set.univ Lb) {εH : ℝ}
  (A₀ : physParam 2 S → ℂ →
    LabelAct (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
      (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 T.marksKc')
  (hεpos : 0 < εH) (hε : εH ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ')
  (hdiffA : ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
    DifferentiableOn ℂ (fun u => (A₀ e u).H y Φ) (Metric.ball (0 : ℂ) 2))
  (hdat : ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
    XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
        ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
          ((S.blockSplit 1 hp).restr x))
  (hmeas : ∀ (θ : physParam 2 S)
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ),
    Measurable (e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u))
  (hdep : ∀ θ ∈ physV S S.a₁ S.ν T.t,
    ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ),
    DepOn (blocksOf 1 (k + 1) Set.univ
      ((commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj).ysite
        (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)))
      (e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u))
  (hbnd : ∀ (θ : physParam 2 S)
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ) Φ,
    ‖e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ‖ ≤
      corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
        (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj).dl
          (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)))
  (hholG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
    AnalyticOnNhd ℂ (fun q : physParam 2 S × ℂ => e1MarkGParam S F₁ Sol p₁ hp z T.t q.1 i q.2 Φ)
      (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU))
  (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ))
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 T.t D')

include D hβ hS hP hεpos hε hdiffA hdat hmeas hdep hbnd hholG hD in
open Classical in
/-- **The energy marks record at a chart datum of the fibre, with the data of the parameter
family.**  At the step `S` of a scale of the tower let the pairs `(F₁ b, Sol b)` have the eight
clauses for the root `z`, let `A₀` be an activity family on the common labels with a positive
amplitude below `stepTheta`, holomorphic in the interpolation parameter on `ball 0 2` for every
parameter of `physV`, and summing to `W₁` of the step with the datum `D″` at `(rawOf D″, g)` for
every datum `D″` of the chart with constant field `h₀`; let the parameter marks `e1MarkGParam` of
the pairs be measurable, block local on `physV`, bounded by `corrF0 · exp (−(2 κ_dec − 1) d_l)`
and analytic on `physV × ball 0 corrU`.  Then for every datum `D′` of the chart with constant
field `h₀` there is a record `E1MarksC (S.withDatum D′)` of the interpolation integral
`ℰ₁^{(k+1)}(z)` of the step with the datum `D′`, with disc `ball 0 corrU`, `κ_G = 2 κ_dec − 1`,
`κ' = T.κ'`, `F₀ = corrF0`, whose interpolation coefficient at every `C` is the parameter
coefficient `gsumCoeff … (A₀ θ′) (commonAnchor …) (e1MarkGParam … θ′) C` at `θ′ = (rawOf D′, 0)`,
and whose budget is `C_PE ∑_{Y′} corrF0 e^{-κ₀ d(Y′)}`. -/
theorem e1MarksC_withDatum_of_fields_fromTower :
    ∃ I : E1MarksC (S.withDatum D' hDh) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        ((S.withDatum D' hDh).blockSplit 1 hp) z,
      I.𝒰 = Metric.ball (0 : ℂ) corrU ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.F0 = (fun _ => corrF0 T k β p₁) ∧
      (∀ C, interpCoeff I C = gsumCoeff (S.blockSplit 1 hp).μ
        (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
        (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)))
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z} =>
          commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)
        (fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t
          ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i u Φ) C) ∧
      CPE 3 3 I.Kc I.κH I.κ0 I.κ' * (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) =
        CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
          ∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
            corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1) := by
  classical
  have hp0 : 0 < p₁ := by subst hS; exact hp
  have hne : Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z} := by
    subst hS
    obtain ⟨Y, hY⟩ := e1Dom_bridgeFamily_nonempty T D z
    exact ⟨⟨Y, hY⟩⟩
  have hθ' : ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈ physV S S.a₁ S.ν T.t :=
    (mk_mem_physFibre S hDh hD (g := 0) (by simp)).1
  have hU2 : corrU ≤ 2 := by unfold corrU; norm_num
  refine ⟨{
      Lb := Lb ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1Dom S)
      εH := εH
      κH := 2 * T.κdec - 1
      κ0 := T.κ0
      Kc := T.marksKc'
      Lab := commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj
      ι := {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}
      nonempty := hne
      κG := 2 * T.κdec - 1
      κ' := T.κ'
      F0 := fun _ => corrF0 T k β p₁
      hN := hN3
      𝒰 := Metric.ball (0 : ℂ) corrU
      isOpen := Metric.isOpen_ball
      seg := fun s hs => by
        rw [mem_ball_zero_iff]
        refine norm_ofReal_lt_of_mem hs ?_
        unfold corrU
        norm_num
      A := fun u => A₀ (⟨rawOf D', rawOf_mem_rawSub _⟩,
        (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) u
      y0 := fun i => commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i
      G := fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t
        (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i u Φ
      meas := fun i u => hmeas _ i u
      dep := fun i u => hdep _ hθ' i u
      bound := fun i u Φ => hbnd _ i u Φ
      holA := fun y Φ => (hdiffA _ hθ' y Φ).mono (ball_subset_ball hU2)
      holG := fun i Φ => ((hholG i Φ).differentiableOn).comp
        (f := fun u : ℂ => ((((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) : physParam 2 S), u))
        (s := Metric.ball (0 : ℂ) corrU)
        ((differentiableOn_const _).prodMk differentiableOn_id) (fun u hu => ⟨hθ', hu⟩)
      hκ0 := T.marks_hκ0
      hKc := T.marks_hKc
      hεpos := hεpos
      hF0 := fun _ => corrF0_pos T hk hβ hp0
      hκ' := T.marks_hκ'
      hκG := T.marks_hκG
      hκ := T.marks_hκ
      hε := by unfold stepTheta at hε; exact hε
      hW := fun s hs => hdat D' hDh hD 0 s hs
      hF := e1_hF_param_of_pairs_fromTower T D hβ hS hp F₁ Sol z hP D' hDh hD },
    rfl, rfl, rfl, rfl, fun _ => rfl, rfl⟩

include D hβ hS hP hεpos hε hdiffA hdat hmeas hdep hbnd hholG hD in
open Classical in
/-- **The value of the parameter coefficients on the fibre `h ≡ h₀`.**  Under the hypotheses of
`e1MarksC_withDatum_of_fields_fromTower`, for every datum `D′` of the chart with constant field
`h₀`, the local energy term `ℰ₁^{(k+1)}(z)` of the step with the datum `D′` is the sum over the
finite sets `C` of level-one blocks of the parameter coefficients
`gsumCoeff … (A₀ θ′) (commonAnchor …) (e1MarkGParam … θ′) C` at `θ′ = (rawOf D′, 0)`. -/
theorem e1Param_fibre_value_of_fields_fromTower :
    (S.withDatum D' hDh).E1locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
      ∑ C, gsumCoeff (S.blockSplit 1 hp).μ
        (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
        (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)))
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z} =>
          commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)
        (fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t
          ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i u Φ) C := by
  obtain ⟨I, -, -, -, -, hc, -⟩ := e1MarksC_withDatum_of_fields_fromTower T D hN3 hβ hS hp hdj
    F₁ Sol z hP Lab₀ A₀ hεpos hε hdiffA hdat hmeas hdep hbnd hholG D' hDh hD
  exact ((interpCoeff_spec I).1).trans (Finset.sum_congr rfl fun C _ => hc C)

end Record

end Balaban.Inhabited
