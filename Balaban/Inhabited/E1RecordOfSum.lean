/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarksCommon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The energy marks record of the renormalization step, conditional on the sum identity

At a scale of the shared tower, beyond one threshold in `β`, the record `E1MarksC` of the
interpolation integral `ℰ₁^{(k+1)}(z)` (zero class, whole torus) is assembled from landed pieces,
with the physical sum identity as its only hypothesis:

* `hF`: for `s ∈ [0,1]` and `ν`-almost every `x`, the masked derivative of `Φ₁` at `s · ψ'` equals the
  sum over the bridge family of `z` of the marks `e1MarkG` of the family of pairs `(F₁, Sol)` returned
  by the same theorem, evaluated at the restriction of `x`.

The labels and the activity are those of the common zero-source family (`zeroSourceActivity_common_fromTower`)
at the label domains `e1Dom`; the marks, the disc and the constant `corrF0` are those of
`e1Marks_common_fromTower_pairs`; the budget is `exists_beta0_e1`.  The family of pairs is returned
together with its defining clauses (`MarkedBlockExpansionDecPair` and the two analyticity clauses),
so that the sum identity can be proved for it.  The consequence for the local energy term is
`e1loc_expansion_zeroClass_of_sum`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **The marks record of the energy term at the general tower, conditional on the sum identity.**
The statement of `e1MarksC_zeroClass_of_sum_anchor` at `T : StepTowerG d L N κmin` with `T.m₀ = 1`,
a constants record `C` with the rates and label constants of `T`
(`StepTowerG.exists_outputConsts`), the step `S = hatStepKG … ϱ …` over any
`ϱ = rhoSepG d L T.m₁`, and the marks `e1MarkGGen` on the disc `ball 0 (17 / 16)`.  The fixed
theorem is its corollary. -/
theorem e1MarksC_zeroClass_of_sum_anchorG {d L N : ℕ} [NeZero L] {κmin : ℝ}
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
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
        (∀ z : RootIdx d L N₁ T.m₁ (k + 1), ∀ b,
        MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁ (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)) ∧
        (∀ Y, AnalyticOnNhd ℂ
          (fun p : (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z) p.2.1 p.2.2 Y p.1)
          ((XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
            {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k S.a₁ T.κ p₁ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t})) ∧
        (∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
          ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad d L N k S.a₁ T.κ p₁ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t →
          AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) S.a₁ S.ν S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k b) (S.blockU z) p.2 t Y ((p.1.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), ψh)) 0)
            (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) a))) ∧
        ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            (fderiv ℂ (S.Phi1C (zeroClass d L N₁ T.m₁ k N ϱ)) ((s : ℂ) • S.shiftUC x))
                (S.maskUC z (S.shiftUC x)) =
              ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}, e1MarkGGen S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i
                (s : ℂ) ((S.blockSplit 1 hp).restr x)) →
          ∃ I : E1MarksC S (zeroClass d L N₁ T.m₁ k N ϱ) (S.blockSplit 1 hp) z,
            I.𝒰 = Metric.ball (0 : ℂ) (17 / 16 : ℝ) ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
            I.F0 = (fun _ => corrF0G T k β p₁) ∧
            CPE d L I.Kc I.κH I.κ0 I.κ' *
              (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0 d L T.κ0 ∧
            ∀ i, rootCube (m₀ := 1) (K := k + 1) z ∈
              blocksOf 1 (k + 1) Set.univ (I.Lab.ysite (I.y0 i)) := by
  classical
  obtain ⟨βa, CE, CF, hβa3, -, -, hact⟩ :=
    zeroSourceActivity_common_fromTowerG T C hKc hKall hH h0 h' hA p
  rw [hm₀] at hact
  obtain ⟨β₀, hmax, hR, hbud⟩ := exists_beta0_e1G T hm₀ hA p βa
  rw [hm₀] at hbud
  have hKc1 : K0 d L T.κ0 + 1 ≤ 2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0 := by
    have := T.marks_hKc; rwa [hm₀] at this
  refine ⟨β₀, (le_max_left _ _).trans hmax, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  have hp0 : 0 < p₁ := hp
  have hN1 : L ^ 1 ∣ N₁ := by rwa [hm₀] at h3N
  have hβ3 : 3 ≤ β := ((le_max_left _ _).trans hmax).trans hβ
  have hβpos : 0 < β := by linarith
  have hβa : βa ≤ β := ((le_max_right _ _).trans hmax).trans hβ
  have hRU := hR k hk β hβ p₁ hp0 hp₁
  obtain ⟨hFpos, hopen, hseg, F₁, Sol, hpairs, hmk⟩ :=
    e1Marks_common_fromTower_pairsG T hm₀ D h3N hN hν0.le hν hβpos hp0 hRU rfl
  refine ⟨F₁, Sol, hpairs, fun z hF => ?_⟩
  obtain ⟨hne, hmeas, hdb, hdiff⟩ := hmk z
  obtain ⟨Jr, val, I0, hFd, hεU, hval, hεpos, hamp, hθ, hstep, A, hAeq, hW1, hW2, hcom⟩ :=
    hact k hk N₁ hN1 hN ν hν0 hν β hβa p₁ hp0 hp₁ 1 one_pos le_rfl D (T.step k hk N₁ ν β p₁)
      rfl hp
  obtain ⟨A0, hA0eq, hana, hdiffA, hcont, hsum, hdat, hWstep, -, -⟩ :=
    hcom (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl)
  have hXi := D.xi
  have he₀ : ((⟨rawOf (T.step k hk N₁ ν β p₁).D', rawOf_mem_rawSub _⟩ :
      rawSub N (T.step k hk N₁ ν β p₁).G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
      physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t :=
    (mk_mem_physFibre (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).hh₀ hXi (g := 0)
      (by simp)).1
  have hU2 : (17 / 16 : ℝ) ≤ 2 := by norm_num
  have hθ' := hstep
  obtain ⟨hdep, hbnd⟩ := hdb _ (commonLabels (thickLabels I0.𝒴 I0.dom)
    hN1 (by have := T.hL; omega) (fun _ => Set.univ)
    (e1DomG (T.step k hk N₁ ν β p₁)) (e1DomG_isDj T hm₀ D rfl))
  refine ⟨{
      Lb := {Y // Y ∈ I0.𝒴} ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁))
      εH := 2 ^ 2 * (2 * ((T.step k hk N₁ ν β p₁).β * prop33EpsEtaScaled d L N T.m₁ k 1
        (T.step k hk N₁ ν β p₁).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0
        (1 / (T.step k hk N₁ ν β p₁).β)))
      κH := 2 * T.κdec - 1
      κ0 := T.κ0
      Kc := 2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0
      Lab := commonLabels (thickLabels I0.𝒴 I0.dom) hN1
        (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁))
        (e1DomG_isDj T hm₀ D rfl)
      ι := {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z}
      nonempty := hne
      κG := 2 * T.κdec - 1
      κ' := T.κ'
      F0 := fun _ => corrF0G T k β p₁
      hN := hN1
      𝒰 := Metric.ball (0 : ℂ) (17 / 16 : ℝ)
      isOpen := hopen
      seg := hseg
      A := fun u => A0 (⟨rawOf (T.step k hk N₁ ν β p₁).D', rawOf_mem_rawSub _⟩,
        (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) u
      y0 := fun i => commonAnchor _ (fun _ => Set.univ) (e1DomG (T.step k hk N₁ ν β p₁)) z i
      G := fun i u Φ => e1MarkGGen (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z i u Φ
      meas := hmeas
      dep := fun i u => hdep i u
      bound := fun i u Φ => hbnd i u Φ
      holA := fun y Φ => (hdiffA _ he₀ y Φ).mono (ball_subset_ball hU2)
      holG := hdiff
      hκ0 := T.marks_hκ0
      hKc := hKc1
      hεpos := hεpos
      hF0 := fun _ => hFpos
      hκ' := T.marks_hκ'
      hκG := T.marks_hκG
      hκ := T.marks_hκ
      hε := by unfold stepTheta at hθ'; exact hθ'
      hW := hWstep
      hF := hF }, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨hbud k hk N₁ hN1 ν β hβ p₁ hp0 hp₁ D rfl z, fun i => ?_⟩
  exact (bridgeFamily_spec hN1 (by have := T.hL; omega) (e1DomG_isDj T hm₀ D rfl) z i.2).2.1

open Classical in
/-- **The marks record of the energy term, conditional on the sum identity.**  Beyond a threshold
`β₀`, at every scale datum, there is a family of pairs `(F₁, Sol)` with the defining clauses of
`markCorrFamily_fromTower`, such that for every root `z`: if the masked derivative of `Φ₁` equals the
sum of the marks `e1MarkG` of this family almost everywhere (the field `hF` of `InterpMarks`), then
there is a record `E1MarksC` with disc `ball 0 corrU`, `κ_G = 2 κ_dec - 1`, `κ' = T.κ'`,
`F₀ = corrF0`, and the budget `C_PE ∑ F₀ e^{-κ₀ d} ≤ K₀`.  The version `_anchor` also returns the root clause: the
root cube of `z` lies in the blocks of the site set of every label of the marks (the labels are the
anchors of the bridge family of `z`). -/
theorem e1MarksC_zeroClass_of_sum_anchor {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
        (∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1), ∀ b,
        MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁ ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)) ∧
        (∀ Y, AnalyticOnNhd ℂ
          (fun p : (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ)) × (ℂ × ℂ) =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2.1 p.2.2 Y p.1)
          ((XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
            {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t})) ∧
        (∀ Y, ∀ ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
          ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t →
          AnalyticOnNhd ℂ (fun p : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ => deriv (fun t : ℂ =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2 t Y ((p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), ψh)) 0)
            (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) a))) ∧
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            (fderiv ℂ ((T.step k hk N₁ ν β p₁).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • (T.step k hk N₁ ν β p₁).shiftUC x))
                ((T.step k hk N₁ ν β p₁).maskUC z ((T.step k hk N₁ ν β p₁).shiftUC x)) =
              ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}, e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i
                (s : ℂ) (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) →
          ∃ I : E1MarksC (T.step k hk N₁ ν β p₁) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) z,
            I.𝒰 = Metric.ball (0 : ℂ) corrU ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
            I.F0 = (fun _ => corrF0 T k β p₁) ∧
            CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
              (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0 3 3 T.κ0 ∧
            ∀ i, rootCube (m₀ := 1) (K := k + 1) z ∈
              blocksOf 1 (k + 1) Set.univ (I.Lab.ysite (I.y0 i)) := by
  obtain ⟨β₀, h3, H⟩ := e1MarksC_zeroClass_of_sum_anchorG T.toG rfl (stepOutputPhysical T hHull)
    rfl rfl rfl rfl rfl hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D => ?_⟩
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hν0 (by simpa using hν) β hβ p₁
    (by rw [e]; exact hp₁) (StepTower.scaleDataG_of_fixed T D) (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm (T.step k hk N₁ ν β p₁) rfl hp
  simp only [corrF0_toG]
  exact G

open Classical in
/-- **The marks record of the energy term, conditional on the sum identity.**  The record of
`e1MarksC_zeroClass_of_sum_anchor` without its root clause. -/
theorem e1MarksC_zeroClass_of_sum {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
        (∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1), ∀ b,
        MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁ ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)) ∧
        (∀ Y, AnalyticOnNhd ℂ
          (fun p : (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ)) × (ℂ × ℂ) =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2.1 p.2.2 Y p.1)
          ((XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
            {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t})) ∧
        (∀ Y, ∀ ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
          ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t →
          AnalyticOnNhd ℂ (fun p : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ => deriv (fun t : ℂ =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2 t Y ((p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), ψh)) 0)
            (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) a))) ∧
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            (fderiv ℂ ((T.step k hk N₁ ν β p₁).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • (T.step k hk N₁ ν β p₁).shiftUC x))
                ((T.step k hk N₁ ν β p₁).maskUC z ((T.step k hk N₁ ν β p₁).shiftUC x)) =
              ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}, e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i
                (s : ℂ) (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) →
          ∃ I : E1MarksC (T.step k hk N₁ ν β p₁) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) z,
            I.𝒰 = Metric.ball (0 : ℂ) corrU ∧ I.κG = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
            I.F0 = (fun _ => corrF0 T k β p₁) ∧
            CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
              (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) ≤ K0 3 3 T.κ0 := by
  obtain ⟨β₀, h3, h⟩ := e1MarksC_zeroClass_of_sum_anchor T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D => ?_⟩
  obtain ⟨F₁, Sol, hpairs, h'⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  refine ⟨F₁, Sol, hpairs, fun z hF => ?_⟩
  obtain ⟨I, h1, h2, h3', h4, h5, -⟩ := h' z hF
  exact ⟨I, h1, h2, h3', h4, h5⟩

/-- **The expansion of the local energy term, conditional on the sum identity.**  The consumer
`e1locC_expansion_of_input` applied to the record of `e1MarksC_zeroClass_of_sum`: the local energy
term `ℰ₁^{(k+1)}(z)` is a sum over finite sets `T` of level-one blocks of terms bounded by
`K₀ e^{-κ' d_Ext(T)}`. -/
theorem e1loc_expansion_zeroClass_of_sum {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
        (∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1), ∀ b,
        MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁ ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)) ∧
        (∀ Y, AnalyticOnNhd ℂ
          (fun p : (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ)) × (ℂ × ℂ) =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2.1 p.2.2 Y p.1)
          ((XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
            {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t})) ∧
        (∀ Y, ∀ ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
          ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t →
          AnalyticOnNhd ℂ (fun p : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ => deriv (fun t : ℂ =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2 t Y ((p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), ψh)) 0)
            (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) a))) ∧
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
            (fderiv ℂ ((T.step k hk N₁ ν β p₁).Phi1C (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) ((s : ℂ) • (T.step k hk N₁ ν β p₁).shiftUC x))
                ((T.step k hk N₁ ν β p₁).maskUC z ((T.step k hk N₁ ν β p₁).shiftUC x)) =
              ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}, e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i
                (s : ℂ) (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) →
          ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (T.step k hk N₁ ν β p₁).E1locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z = ∑ T', E T' ∧
            ∀ T', ‖E T'‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt T') := by
  obtain ⟨β₀, h3, h⟩ := e1MarksC_zeroClass_of_sum T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D => ?_⟩
  obtain ⟨F₁, Sol, hpairs, h'⟩ := h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  refine ⟨F₁, Sol, hpairs, fun z hF => ?_⟩
  obtain ⟨I, -, -, hκ', -, hbud⟩ := h' z hF
  obtain ⟨E, h1, h2⟩ := e1locC_expansion_of_input I
  refine ⟨E, h1, fun T' => (h2 T').trans ?_⟩
  rw [← hκ']
  exact mul_le_mul_of_nonneg_right hbud (Real.exp_pos _).le

end Balaban.Inhabited
