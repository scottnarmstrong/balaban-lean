/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1CoeffFamilyG
public import Balaban.Inhabited.OffFibreE1CoeffSum

/-!
# The first-energy coefficient family at every chart datum

The common activity and the parameter marks are chosen once at each scale. Their coefficient
family is analytic, local and bounded, and its sum is the localized derivative of the raw
first exponent at every datum in the chart.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit

open Classical in
/-- One first-energy coefficient family has the raw localized value at every chart datum. -/
theorem e1CoeffFamily_raw_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1)
    (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ Dt : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' ×
            RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) ×
              (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') ×
            Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁)
            (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
            (e1DomG_isDj_of_eq T hm₀ Dt hϱ hS))
            (S.blockSplit 1 hp).Ωb εH
            (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0))
        (Jr : S.JointRep T.t (2 * p₁)),
        0 < εH ∧
        εH ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' ∧
        (∀ (D : BgData S.G' N),
          XiCData S.G' S.a
            S.ν (k + 1) 1 T.t D →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
            ∀ᵐ x ∂S.nuFl,
              Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
                rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                ((S.blockSplit 1 hp).restr x)) ∧
        ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
          ∃ c : physParam N S →
              Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
                (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
            (∀ θ C, c θ C = gsumCoeff (S.blockSplit 1 hp).μ
              (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ Dt hϱ hS))
              (A₀ θ)
              (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                  (e1DomG S) z} =>
                commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
              (fun i u Φ => e1MarkGParamG S
                (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
            (∀ C, AnalyticOnNhd ℂ (fun θ => c θ C)
                (physV S S.a₁
                  S.ν T.t) ∧
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
              (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧
                IsPolyDom 1 (k + 1) (sitesOf C) ∧
                dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
            ∀ (D : BgData S.G' N),
              XiCData S.G' S.a
                S.ν (k + 1) 1 T.t D →
              ∑ C, c ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
                rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C =
              ∫ s in (0 : ℝ)..1, avgFun S.nuFl
                (fun s x => Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
                  (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))
                (fun x => (fderiv ℂ (fun w : S.EC =>
                  Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ) (rawOf D, w))
                  ((s : ℂ) • Balaban.Fluctuation.yhat x))
                  ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z
                    (Jr.Mx (rawOf D) *ᵥ Balaban.Fluctuation.yhat x))) s 
 := by
  classical
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ Dt ϱ hϱ S hS hp
  have G := H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ Dt hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, -, hz, hεpos, hε, hAhol, hGhol, hdep,
    hmeas, hbnd, Jr, hraw⟩ := G
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, Jr, hεpos, hε, hraw.1, fun z => ?_⟩
  obtain ⟨hP, -, c, hc, hC, -⟩ := hz z
  refine ⟨c, hc, fun C => ⟨(hC C).1, (hC C).2.2.1, (hC C).2.2.2.1,
    (hC C).2.2.2.2⟩, ?_⟩
  intro D hX
  let θ : physParam N S :=
    ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
  have hθ : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈ physV S S.a₁ S.ν T.t := by
    exact ⟨⟨D, hX, rfl⟩, by
      change (∑ x : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N, ‖(0 : ℂ)‖) < 1
      simp⟩
  have hAhol : ∀ y Φ, DifferentiableOn ℂ
      (fun u => (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) u).H y Φ)
      (Metric.ball (0 : ℂ) corrU) := by
    intro y Φ
    exact (hAhol _ hθ y Φ).mono (by unfold corrU; exact Metric.ball_subset_ball (by norm_num))
  have hGhol : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) Φ,
      DifferentiableOn ℂ (fun u => e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z T.t ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) i u Φ)
        (Metric.ball (0 : ℂ) corrU) := by
    intro i Φ u hu
    have hu' : u ∈ Metric.ball (0 : ℂ) (17 / 16 : ℝ) := by simpa [corrU] using hu
    have ha := (hGhol z i Φ (θ, u) ⟨hθ, hu'⟩).differentiableAt
    have hp' : DifferentiableAt ℂ (fun v : ℂ => (θ, v)) u :=
      DifferentiableAt.prodMk (differentiableAt_const θ) differentiableAt_id
    have hcomp := ha.comp u hp'
    exact hcomp.differentiableWithinAt
  have hβpos : 0 < β := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (h3.trans hβ)
  have hlt : S.p₁ < 2 * p₁ := by
    have hp₁ : 0 < p₁ := by subst hS; exact hp
    have hpS : S.p₁ = p₁ := by subst hS; rfl
    rw [hpS]
    linarith
  have hsum := T.e1_param_coeff_sum_eq_raw_deriv_of_activity Dt hm₀ hϱ S hS Jr hp hlt hβpos
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) z hP D hX
    (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (e1DomG_isDj_of_eq T hm₀ Dt hϱ hS) Lab₀ A₀ _ rfl
    (hraw.1 D hX) hεpos hε hAhol
    (fun i u => hmeas z _ i u)
    (fun i u => hdep z _ i u)
    (fun i u Φ => hbnd z θ i u Φ)
    hGhol
  calc
    ∑ C, c θ C = _ := Finset.sum_congr rfl (fun C _ => hc θ C)
    _ = _ := hsum

open Classical in
/-- One first-energy coefficient family has the raw localized value at every chart datum. -/
theorem e1CoeffFamily_raw_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < (T.step k hk N₁ ν β p₁).p₁,
        p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ Dt : StepScaleData T k hk N₁ ν β p₁,
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
          Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' ×
            RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) ×
              ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
          Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') ×
            Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ Lb) (εH : ℝ)
        (A₀ : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ →
          LabelAct (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁)
            (by norm_num) (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁))
            (e1Dom_isDj T Dt))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εH
            (2 * T.κdec - 1) T.κ0 T.marksKc')
        (Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁)),
        0 < εH ∧
        εH ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
        (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
            (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
            ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
                rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) ∧
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          ∃ c : physParam 2 (T.step k hk N₁ ν β p₁) →
              Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
                (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
            (∀ θ C, c θ C = gsumCoeff ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
              (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T Dt))
              (A₀ θ)
              (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                  (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
                commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
              (fun i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁)
                (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
            (∀ C, AnalyticOnNhd ℂ (fun θ => c θ C)
                (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                  (T.step k hk N₁ ν β p₁).ν T.t) ∧
              (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                  (T.step k hk N₁ ν β p₁).ν T.t,
                ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                  (T.step k hk N₁ ν β p₁).ν T.t,
                physRestrict (N := 2) (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                  physRestrict (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
                  c θ C = c θ' C) ∧
              (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                  (T.step k hk N₁ ν β p₁).ν T.t,
                ‖c θ C‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
              (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧
                IsPolyDom 1 (k + 1) (sitesOf C) ∧
                dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
            ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
              XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
                (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D →
              ∑ C, c ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
                rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C =
              ∫ s in (0 : ℝ)..1, avgFun (T.step k hk N₁ ν β p₁).nuFl
                (fun s x => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                  (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))
                (fun x => (fderiv ℂ (fun w : (T.step k hk N₁ ν β p₁).EC =>
                  Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, w))
                  ((s : ℂ) • Balaban.Fluctuation.yhat x))
                  ((Jr.Mx (rawOf D))⁻¹ *ᵥ (T.step k hk N₁ ν β p₁).maskUC z
                    (Jr.Mx (rawOf D) *ᵥ Balaban.Fluctuation.yhat x))) s := by
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_raw_fromTowerG T.toG rfl (stepOutputPhysical T hHull) rfl rfl
    rfl rfl rfl hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ Dt
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  exact H k hk N₁ (by simpa using h3N) hN ν hν0 (by simpa using hν) β hβ p₁ (by rw [e]; exact hp₁)
    (T.scaleDataG_of_fixed Dt) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (T.step k hk N₁ ν β p₁)
    rfl hp


end Balaban.Inhabited
