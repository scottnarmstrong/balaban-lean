/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarkParamCommon
public import Balaban.Inhabited.E1ParamRawLocal
public import Balaban.Fluctuation.GsumActiveParam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# One energy coefficient family at the tower

At a scale of the shared tower (`d = L = 3`, `N = 2`, zero class), the coefficients of the local
energy term are assembled as one family
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (G z θ) C` in the datum `θ` of the physical
parameter space, from the landed pieces:

* the activity `A₀` of `zeroSourceActivity_common_fromTower` (zero-source activity on the common
  labels);
* the marks `e1MarkGParam` of one family of decoupling pairs, chosen before every parameter;
* the locality premises of `E1ParamRawLocal.lean`;
* `paramMarked_analytic_local_bound` and the support lemmas of `GsumActiveParam.lean`.

`e1MarkParam_pairs_fromTower` is the field theorem of `e1MarkParam_fields_fromTower` with the
defining clauses of the pairs and the block dependence for every parameter exposed.
`e1CoeffFamily_fromTower` states, for every root `z` and every finite set `C` of level-one blocks,
analyticity of `θ ↦ c z θ C` on `physV`, locality in the raw datum, the bound
`K₀ e^{-κ' d_Ext(C)}`, and the support on rooted polymer sets.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section Fields

open Classical in
/-- **The mark fields of the parameter family, with the pairs.**  One family of pairs
`(F₁, Sol)`, chosen before every parameter and every root, such that for every root `z`: the pairs
satisfy `MarkedBlockExpansionDecPair`; the bridge family is nonempty; the marks `e1MarkGParam` are
measurable in `Φ`; for every label system on which the common labels are built, for every
parameter `θ` (not only on `physV`), they depend only on the blocks of the common label of their
anchor and are bounded by `corrF0 · exp (−(2 κ_dec − 1) d_l)`; they are analytic in `(θ, u)` on
`physV × ball 0 corrU` and continuous in the configuration on the carrier. -/
theorem e1MarkParam_pairs_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < (T.step k hk N₁ ν β p₁).p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁) :
    ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
      (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
    ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
      (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
        (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
        ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
        (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z} ∧
      (∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
        (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        (u : ℂ), Measurable (e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
              (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)))
            (e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
              z T.t θ i u)) ∧
        (∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
            (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ) Φ,
          ‖e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              T.t θ i u Φ‖ ≤
            corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        (Φ : ∀ b, ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb b),
        AnalyticOnNhd ℂ (fun p : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ =>
          e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
            T.t p.1 i p.2 Φ)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t
            ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}),
        ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t,
        ∀ u ∈ Metric.ball (0 : ℂ) corrU,
          ContinuousOn (e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) := by
  classical
  have hp' : 0 < (T.step k hk N₁ ν β p₁).p₁ := hp
  have hp0 : 0 < p₁ := hp
  obtain ⟨hV, -⟩ := D.covers
  obtain ⟨F₁, Sol, hF⟩ := markCorrFamily_fromTower T D hN hν0 hν hβ hp0 hRU
    (S := T.step k hk N₁ ν β p₁) rfl hp
  refine ⟨F₁, Sol, fun z => ?_⟩
  obtain ⟨hP, hJ2, hJ4, hcnt, hblk⟩ := hF z
  have hout := markedOutDecCorr_fields (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).hG'
    (by norm_num) (by simpa using h3N) (fun b => (hV b).1) (fun b => (hV b).2.2.1) z
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) hP hJ2 hJ4 (ρ := p₁) hp le_rfl hp' T.t_pos
    (((T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)
  obtain ⟨hmeas, hdep, hhol⟩ := hout
  have hF0 := corrF0_pos T hk hβ hp0
  have hR := corrR_pos T hk (by positivity : 0 < β * 3 ^ k) hp0
  have hdepG : ∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
          z T.t θ i u) := by
    intro θ i u
    by_cases hc : (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
        XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < corrU
    · have e : e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
        funext fun Φ => e1MarkGParam_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2
      rw [e]
      exact hdep i.1 i.2 _ hc.1 u (e1_rad_lt T hk hβ hp0 hRU hc.2.le)
    · intro Φ Φ' _
      rw [e1MarkGParam_of_not _ _ _ _ hp z T.t θ i u Φ hc,
        e1MarkGParam_of_not _ _ _ _ hp z T.t θ i u Φ' hc]
  have hbdG : ∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ) Φ,
      ‖e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
        T.t θ i u Φ‖ ≤
        corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) i.1) := by
    intro θ i u Φ
    by_cases hc : (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
        XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < corrU
    · rw [e1MarkGParam_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2]
      exact (hcnt _ hc.1 u hc.2.le Φ).1 i.1
    · rw [e1MarkGParam_of_not _ _ _ _ hp z T.t θ i u Φ hc, norm_zero]
      positivity
  have hmeasG : ∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      Measurable (e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u) := by
    intro θ i u
    by_cases hc : (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
        XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ∧ ‖u‖ < corrU
    · have e : e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
        funext fun Φ => e1MarkGParam_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2
      rw [e]
      exact hmeas i.1 _ hc.1 u (e1_rad_lt T hk hβ hp0 hRU hc.2.le)
    · have e : e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = fun _ => 0 :=
        funext fun Φ => e1MarkGParam_of_not _ _ _ _ hp z T.t θ i u Φ hc
      rw [e]
      exact measurable_const
  have hopen : IsOpen (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
      (T.step k hk N₁ ν β p₁).ν T.t) :=
    isOpen_physV _ _ _ _ (bgHyp_lv (k := k) T.m₁ hν0 hν)
  refine ⟨hP, ?_, hmeasG, fun Lb _ Lab => ⟨fun θ i u => ?_, fun θ i u Φ => ?_⟩, ?_, ?_⟩
  · obtain ⟨Y, hY⟩ := e1Dom_bridgeFamily_nonempty T D z
    exact ⟨⟨Y, hY⟩⟩
  · exact (commonAnchor_marks_fields (Lab := Lab)
      (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num) (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) ((e1Dom_isDj T D)) z (ι := {Y' // Y' ∈ bridgeFamily 1
        (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}) id (fun _ => corrF0 T k β p₁)
      (2 * T.κdec - 1)
      (fun i u => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z T.t θ i u) (hdepG θ) (hbdG θ)).1 i u
  · exact hbdG θ i u Φ
  · intro i Φ
    have han := hhol i.1 Φ (corrR T k (β * 3 ^ k) p₁) (corrR T k (β * 3 ^ k) p₁) hR hR
      (e1_rad_RR_lt T hk hβ hp0)
    have hmono := han.mono (Set.prod_mono (subset_refl _)
      (Metric.ball_subset_ball (by linarith : corrU ≤ corrR T k (β * 3 ^ k) p₁)))
    refine hmono.congr (hopen.prod Metric.isOpen_ball) fun p hp'' => ?_
    exact (e1MarkGParam_of_mem _ _ _ _ hp z T.t p.1 i p.2 Φ hp''.1.1
      (mem_ball_zero_iff.1 hp''.2)).symm
  · intro i θ hθ u hu
    have hu' : ‖u‖ < corrU := mem_ball_zero_iff.1 hu
    have e : e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
      funext fun Φ => e1MarkGParam_of_mem _ _ _ _ hp z T.t θ i u Φ hθ.1 hu'
    rw [e]
    refine (continuous_markedOutDec_decMarkCorrTerm (T.step k hk N₁ ν β p₁) _ _ p₁ hp _ _ _ z
      i.1 fun b Y => ?_).continuousOn
    exact ((hblk b).2.1 Y _ hθ.1 u (e1_rad_lt T hk hβ hp0 hRU hu'.le)).1

end Fields

section Main

open Classical in
/-- **One energy coefficient family at the tower.**  Beyond a threshold `β₀`, at every scale datum
there are one family of decoupling pairs `(F₁, Sol)`, a label system `Lab₀` and an activity `A₀` on
the common labels (the zero-source activity of `zeroSourceActivity_common_fromTower`, with its
identity for the interpolation integral at every chart datum), chosen before every root, such that
for every root `z` the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParam … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 3 3 T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`.
The family `A₀`, `c` and the marks carry a `ParamMarkFamily` over `physV`, `ball 0 corrU` and
`physCarrier`. -/
theorem e1CoeffFamily_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < (T.step k hk N₁ ν β p₁).p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ D : StepScaleData T k hk N₁ ν β p₁,
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ →
          LabelAct (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 T.marksKc'),
      (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
          (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
        XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
          (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).WoneC
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
            ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub 2 (T.step k hk N₁ ν β p₁).G'), g) (s : ℂ)).H y
              (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) ∧
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
          (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
        Nonempty (ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
          (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A₀
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
            commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
          (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0 T k β p₁)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)
          (Metric.ball (0 : ℂ) corrU) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) ∧
        ∃ c : physParam 2 (T.step k hk N₁ ν β p₁) →
            Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
            (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
              (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
            (fun i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          ∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c θ C)
              (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → c θ C = c θ' C) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ‖c θ C‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C)) := by
  classical
  obtain ⟨βa, CE, CF, hβa3, -, -, hact⟩ := zeroSourceActivity_common_fromTower T hHull hA p
  obtain ⟨β₀, hmax, hR, hbud⟩ := exists_beta0_e1 T hA p βa
  refine ⟨β₀, (le_max_left _ _).trans hmax, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  have hβ3 : 3 ≤ β := ((le_max_left _ _).trans hmax).trans hβ
  have hβpos : 0 < β := by linarith
  have hβa : βa ≤ β := ((le_max_right _ _).trans hmax).trans hβ
  have hRU := hR k hk β hβ p₁ hp hp₁
  obtain ⟨F₁, Sol, hF⟩ := e1MarkParam_pairs_fromTower T D h3N hN hν0.le hν hβpos hp hRU
  obtain ⟨Jr, val, I0, hFd, hεU, hval, hεpos, hamp, hθ, hstep, A, hAeq, hW1, hW2, hcom⟩ :=
    hact k hk N₁ h3N hN ν hν0 hν β hβa p₁ hp hp₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨A0, hA0eq, hana, hdiffA, hcont, hsum, hdat, hWstep, hfam0, -⟩ :=
    hcom (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)
  have hU2 : corrU ≤ 2 := by unfold corrU; norm_num
  have hF0 := corrF0_pos T hk hβpos (show 0 < p₁ from hp)
  have hθ' := hstep
  refine ⟨F₁, Sol, {Y // Y ∈ I0.𝒴}, inferInstance, thickLabels I0.𝒴 I0.dom, _, A0, hdat, ?_⟩
  intro z
  obtain ⟨hP, hne, hmeas, hdb, hholG, hcontG⟩ := hF z
  obtain ⟨hdep, hbnd⟩ := hdb {Y // Y ∈ I0.𝒴} (thickLabels I0.𝒴 I0.dom)
  have hfam : ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
          (commonLabels (thickLabels I0.𝒴 I0.dom) (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A0
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
            commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
          (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0 T k β p₁)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)
          (Metric.ball (0 : ℂ) corrU) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp) := by
    obtain ⟨hA'⟩ := hfam0
    exact { isOpenV := hA'.isOpenV
            isOpenU := Metric.isOpen_ball
            seg := fun s hs => by
              rw [mem_ball_zero_iff]
              refine norm_ofReal_lt_of_mem hs ?_
              unfold corrU
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
  refine ⟨hP, ⟨hfam⟩, _, fun _ _ => rfl, fun C => ?_⟩
  have hp0 : 0 < p₁ := hp
  have hprob := isProbabilityMeasure_fluctMeasure1 2 hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hlab : ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) z},
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
        ((commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
          (commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z
            i)) :=
    fun i => (bridgeFamily_spec hN1 (by norm_num) (e1Dom_isDj T D) z i.2).2.1
  have hAloc : ∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
          (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y, (commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite y ⊆
          Yhat Set.univ (sitesOf C) → (A0 θ (s : ℂ)).H y = (A0 θ' (s : ℂ)).H y := by
    intro C
    subst hA0eq
    subst hAeq
    exact commonAct_zeroSourceAct_hA (T.step k hk N₁ ν β p₁) 1 _ hFd hN1 hp0 zero_le_two hεU
      T.κ0_ent T.marks_K0_le (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)
      (by norm_num) (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two one_pos
      (fun θ => physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ)) C
      (fun θ _ θ' _ h Y hY => physRestrict_thickSet_agree _ _ h hY)
  have hGloc : ∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
          (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z},
        (commonLabels (thickLabels I0.𝒴 I0.dom) hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
          (commonAnchor {Y // Y ∈ I0.𝒴} (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z
            i) ⊆ Yhat Set.univ (sitesOf C) →
        (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i (s : ℂ) Φ) =
        (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ' i (s : ℂ) Φ) := by
    intro C θ hθ θ' hθ' h s hs i hi
    have hu : ‖(s : ℂ)‖ < corrU := norm_ofReal_lt_of_mem hs (by unfold corrU; norm_num)
    funext Φ
    rw [e1MarkGParam_of_mem _ _ _ _ hp z T.t θ i (s : ℂ) Φ hθ.1 hu,
      e1MarkGParam_of_mem _ _ _ _ hp z T.t θ' i (s : ℂ) Φ hθ'.1 hu]
    exact markedOutDec_decMarkCorrTerm_raw_congr (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) hP (ρ := p₁) hp0 le_rfl hp T.t_pos _ hθ.1 hθ'.1
      (e1_rad_lt T hk hβpos hp0 hRU hu.le) z Φ (physRestrict_thickSet_agree _ _ h hi)
  have hmain := fun C => paramMarked_analytic_local_bound (m₀ := 1) (j := k + 1) (Ω := Set.univ)
    ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ hN1 le_rfl isPiUnion_univ_K hfam
    (fun θ i s => hdep θ i s) T.marks_hκ0 T.marks_hKc hεpos hne (fun _ => hF0) T.marks_hκ'
    T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') C
    (fun θ => physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ))
    (hAloc C) (hGloc C)
  have hgm : ∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁)), ∀ (i : {Y' // Y' ∈ bridgeFamily 1
      (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      Measurable (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) := hmeas
  refine ⟨(hmain C).1, (hmain C).2.1, fun θ hθ => ?_, fun θ hne0 => ?_⟩
  · exact ((hmain C).2.2 θ hθ).trans (mul_le_mul_of_nonneg_right
      (hbud k hk N₁ h3N ν β hβ p₁ hp hp₁ D z) (Real.exp_pos _).le)
  · exact ⟨mem_of_gsumCoeff_ne_zero_of_labels hN1 ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (A0 θ) _ _ (hgm θ) (hdep θ) (hbnd θ) T.marks_hκ0 T.marks_hKc hεpos (fun _ => hF0)
      T.marks_hκ' T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') hlab hne0,
      (gsumCoeff_ne_zero_active hN1 ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (A0 θ) _ _ (hgm θ) (hdep θ) (hbnd θ) T.marks_hκ0 T.marks_hKc hεpos (fun _ => hF0)
      T.marks_hκ' T.marks_hκG T.marks_hκ (by unfold stepTheta at hθ'; exact hθ') hne0).2⟩

end Main
end Balaban.Inhabited
