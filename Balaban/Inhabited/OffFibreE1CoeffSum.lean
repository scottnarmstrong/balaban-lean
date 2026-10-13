/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.OffFibreE1Value
public import Balaban.Fluctuation.Thm31CoeffA

/-!
# The first-energy coefficient sum at a free chart datum

The activity identity and the analytic marked-expansion bounds are supplied by an
`InterpMarks` record. Its `hW` field is the free-datum activity identity. The marked integrand
is identified with the localized derivative of the raw first exponent using the pointwise
comparison, for every incoming field in the chart.
-/

@[expose] public section
namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit

open Classical in
/-- The parameter coefficient sum is the localized raw first-energy derivative integral.
The `InterpMarks` witness contains the free-datum activity identity in its `hW` field. -/
theorem e1_param_coeff_sum_eq_raw_deriv_of_interpMarks {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ pp : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (Jr : S.JointRep T.t pp)
    (hp : 0 < S.p₁) (hlt : S.p₁ < pp)
    {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
      (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (I : InterpMarks S.nuFl (S.blockSplit 1 hp)
      (fun s x => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • yhat x))
      (fun s x => ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
        e1MarkGParam S F₁ Sol p₁ hp z T.t
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
          ((S.blockSplit 1 hp).restr x)))
    (e : I.ι ≃ {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
    (hG : ∀ i u Φ, I.G i u Φ =
      e1MarkGParam S F₁ Sol p₁ hp z T.t
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (e i) u Φ) :
    (∑ C, gsumCoeff (S.blockSplit 1 hp).μ I.Lab I.A I.y0
      (fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (e i) u Φ) C) =
    ∫ s in (0 : ℝ)..1, avgFun S.nuFl
      (fun s x => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • yhat x))
      (fun x => (fderiv ℂ (fun w : S.EC =>
        Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, w))
        ((s : ℂ) • yhat x))
        ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) s := by
  have hsum := (interpCoeff_spec I).1
  change _ = ∑ C, gsumCoeff (S.blockSplit 1 hp).μ I.Lab I.A I.y0 I.G C at hsum
  have hGeq : I.G = (fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
        (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (e i) u Φ) := by
    funext i u Φ
    exact hG i u Φ
  rw [hGeq] at hsum
  rw [← hsum]
  unfold interpAvg
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  apply avgFun_congr_ae (ν := S.nuFl) (W := fun s x =>
    Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
      (rawOf D, (s : ℂ) • yhat x)) (Filter.Eventually.of_forall fun _ => rfl)
  filter_upwards [S.ae_ball hp] with x hx
  have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp x).1 hx
  have hpS : S.p₁ = p₁ := by subst hS; rfl
  exact (e1_param_marks_eq_raw_deriv T Dt S hS Jr hp hlt F₁ Sol z hP D hX s hs x
    (hpS ▸ hxn.le))

open Classical in
/-- With a free-datum activity identity and the fixed-parameter mark bounds, the sum of the
actual E1 parameter coefficients equals the localized raw derivative integral. -/
theorem e1_param_coeff_sum_eq_raw_deriv_of_activity {κmin : ℝ} (T : StepTower κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ pp : ℝ}
    (Dt : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (Jr : S.JointRep T.t pp)
    (hp : 0 < S.p₁) (hlt : S.p₁ < pp) (hβpos : 0 < β)
    {BG κdec : ℝ}
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
        ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hP : ∀ b, MarkedBlockExpansionDecPair 2
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.a₁ S.ν BG T.BG₂ T.κ T.t T.t κdec p₁
      (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ b) (Sol b))
    (D : BgData S.G' 2) (hX : XiCData S.G' S.a S.ν (k + 1) 1 T.t D)
    (hN3 : 3 ^ 1 ∣ N₁) (hdj : ∀ b, ∀ Y ∈ e1Dom S b, IsDj 1 (k + 1) Y)
    {Lb : Type} [Fintype Lb]
    (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) 1 (k + 1) Set.univ Lb)
    {εH : ℝ}
    (A₀ : physParam 2 S → ℂ →
      LabelAct (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
        (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 T.marksKc')
    (θ : physParam 2 S)
    (hθ : θ = ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)))
    (hact : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ (x : S.E) ∂S.nuFl,
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • yhat x) =
        ∑ y, (A₀ θ (s : ℂ)).H y ((S.blockSplit 1 hp).restr x))
    (hεpos : 0 < εH)
    (hε : εH ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ')
    (hAhol : ∀ y Φ, DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ)
      (Metric.ball (0 : ℂ) corrU))
    (hmeas : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
      (u : ℂ), Measurable (e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u))
    (hdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
      (u : ℂ), DepOn (blocksOf 1 (k + 1) Set.univ
        ((commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj).ysite
          (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)))
        (e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u))
    (hbnd : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z})
      (u : ℂ) Φ, ‖e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ‖ ≤
        corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
          (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj).dl
            (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)))
    (hGhol : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) Φ,
      DifferentiableOn ℂ (fun u => e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ)
        (Metric.ball (0 : ℂ) corrU)) :
    (∑ C, gsumCoeff (S.blockSplit 1 hp).μ
      (commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj)
      (A₀ θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z} =>
        commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i)
      (fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t θ i u Φ) C) =
    ∫ s in (0 : ℝ)..1, avgFun S.nuFl
      (fun s x => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • yhat x))
      (fun x => (fderiv ℂ (fun w : S.EC =>
        Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, w))
        ((s : ℂ) • yhat x))
        ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) s := by
  subst hθ
  have hne : Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z} := by
    subst hS
    obtain ⟨Y, hY⟩ := e1Dom_bridgeFamily_nonempty T Dt z
    exact ⟨⟨Y, hY⟩⟩
  let I : InterpMarks S.nuFl (S.blockSplit 1 hp)
      (fun s x => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (rawOf D, (s : ℂ) • yhat x))
      (fun s x => ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
        e1MarkGParam S F₁ Sol p₁ hp z T.t
          ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i (s : ℂ)
          ((S.blockSplit 1 hp).restr x)) := {
    Lb := Lb ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1Dom S)
    Lab := commonLabels Lab₀ hN3 (by norm_num) (fun _ => Set.univ) (e1Dom S) hdj
    ι := {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}
    nonempty := hne
    εH := εH
    κH := 2 * T.κdec - 1
    κG := 2 * T.κdec - 1
    κ0 := T.κ0
    κ' := T.κ'
    Kc := T.marksKc'
    F0 := fun _ => corrF0 T k β p₁
    hN := hN3
    𝒰 := Metric.ball (0 : ℂ) corrU
    isOpen := Metric.isOpen_ball
    seg := fun s hs => by
      rw [mem_ball_zero_iff]
      refine norm_ofReal_lt_of_mem hs ?_
      unfold corrU
      norm_num
    A := A₀ (⟨rawOf D, rawOf_mem_rawSub _⟩,
      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
    y0 := fun i => commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z i
    G := fun i u Φ => e1MarkGParam S F₁ Sol p₁ hp z T.t
      (⟨rawOf D, rawOf_mem_rawSub _⟩,
        (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) i u Φ
    meas := hmeas
    dep := hdep
    bound := hbnd
    holA := hAhol
    holG := hGhol
    hκ0 := T.marks_hκ0
    hKc := T.marks_hKc
    hεpos := hεpos
    hF0 := fun _ => corrF0_pos T hk hβpos (by
      have hpS : S.p₁ = p₁ := by subst hS; rfl
      exact hpS ▸ hp)
    hκ' := T.marks_hκ'
    hκG := T.marks_hκG
    hκ := T.marks_hκ
    hε := by unfold stepTheta at hε; exact hε
    hW := hact
    hF := fun _ _ => Filter.Eventually.of_forall fun _ => rfl }
  exact e1_param_coeff_sum_eq_raw_deriv_of_interpMarks T Dt S hS Jr hp hlt F₁ Sol z hP D hX
    I (Equiv.refl _) (fun _ _ _ => rfl)

end Balaban.Inhabited
