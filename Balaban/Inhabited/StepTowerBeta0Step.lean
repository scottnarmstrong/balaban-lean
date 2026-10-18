/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerChainStep
public import Balaban.Inhabited.StepTowerBeta0Struct
public import Balaban.Inhabited.StepTowerScaleTRoom
public import Balaban.Inhabited.StepTowerCollarStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The class chain with the per-label premises at the composed step data, at every tower radius, and at the towers `T_k`

`e0CoeffFamily_class_exists_tower_struct_step_agree`: the statement of
`e0CoeffFamily_class_exists_tower_struct_step` for all towers `T` that agree with a reference
tower `T₀` on `m₁, BG, BG₂, κ, δ` and every radius `t ≥ c 3^{-α(k+1)}` (`2 α < 1`), beyond one
threshold `β₀`: the instance `r₀ = 324`, `δ₁ = T.t` of
`e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- The class chain at a tower, structural premises discharged, with the per-label premises at the
composed step data, at every tower radius `t ≥ c 3^{-α(k+1)}`, beyond one threshold. -/
theorem e0CoeffFamily_class_exists_tower_struct_step_agree (m₀ : ℕ) {κmin : ℝ}
    (hlo : stepHullMin ≤ κmin) (T₀ : StepTower κmin) {κdec : ℝ}
    (hκ₀ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T₀.κ)
    (hr₀ : (2 * T₀.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
      ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ → ∀ δ₃ δfl : ℝ, ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃ →
      FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ T.m₁ (k + 1) × Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ T.m₁ (k + 1) 2 (rhoSep T.m₁)}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1)
            (rhoSep T.m₁), (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld 3 3 N₁ T.m₁ (k + 1) 2, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock 3 3 (N₁ * 3 ^ T.m₁) (k + 1) j x = jBlock 3 3 (N₁ * 3 ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide 3 C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => 3 / 2 * cellSide 3 C.m₀ T.m₁ τ.1.1) (3 * cellSide 3 C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ 324 T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t δfl (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ T.t,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ T.t,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / (T.t / (2 * markedRad 3 3 2 k S.a₁ T.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 T.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤
          1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
            rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
            Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3))) →
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := 2) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl 2 S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl 2 S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
            27 * covBLogMax 3 3 T.κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) *
                Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                  dExt T') +
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, HC⟩ :=
    e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar m₀ hlo T₀ hκ₀ hr₀ hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₁ hBG hBG₂ hκT hδ δ₃ δfl hnB hnF => ?_⟩
  exact HC T hm₁ hBG hBG₂ hκT hδ 324 δ₃ T.t δfl le_rfl (by norm_num) hnB hnF le_rfl

open Classical in
/-- **The class chain at the towers `T_k` of `exists_stepTower_room`, one `β₀` for every scale.** -/
theorem e0CoeffFamily_class_exists_tower_struct_step_uniform (m₀ : ℕ) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {c₁ α : ℝ} (hc₁ : 0 < c₁) (hα₀ : 0 ≤ α) (hα : 2 * α < 1) :
    ∃ (κmin : ℝ) (_ : stepHullMin ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ), ∃ β₀ : ℝ,
      3 ≤ β₀ ∧ ∀ ε : ℕ → ℝ, Antitone ε → (∀ j : ℕ, c₁ * (3 : ℝ) ^ (-(α * (j : ℝ))) ≤ ε j) →
      ∀ (k : ℕ) (hk : 1 ≤ k),
      ∃ (Tk : StepTower κmin) (l : ℝ), 0 < l ∧ l ≤ 1 ∧
        l = min 1 (ε (k + 1) / (T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl)) ∧
        Tk.t = l * T.t ∧ Tk.t ≤ ε (k + 1) ∧ Tk.m₁ = T.m₁ ∧ Tk.c = T.c ∧ Tk.BG = T.BG ∧
        Tk.κ = T.κ ∧ Tk.c₂ = T.c₂ ∧ Tk.BG₂ = T.BG₂ ∧ Tk.δc = T.δc ∧ Tk.δ = T.δ ∧ Tk.δ' = T.δ' ∧
        ChainNum 3 3 2 Tk.m₁ Tk.BG Tk.κ 324 Tk.t (l * δ₃) ∧
        FlNum 3 3 2 Tk.BG Tk.BG₂ Tk.κ Tk.t (l * δ₃) Tk.t (l * δfl) ∧
        (∀ j ≤ k + 1, Tk.t + xiK2 3 3 2 * (l * δ₃) + xiK2 3 3 2 * (l * δfl) ≤ ε j) ∧
        ∀ (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
              ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
              ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
              ∀ (S : StepSetting 3 3 N₁ Tk.m₁ k 2 (rhoSep Tk.m₁))
                (_ : S = Tk.step k hk N₁ ν β p₁),
              ∃ Jr : S.JointRep Tk.t (2 * p₁),
              ∀ (C : StepClass 3 3 N₁ Tk.m₁ k 2 (rhoSep Tk.m₁)) (z : RootIdx 3 3 N₁ Tk.m₁ (k + 1))
                (𝒯E : Finset (ℕ × CTorus 3 3 N₁ Tk.m₁ (k + 1) × Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))))
                (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1) ×
                    Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))))).filter
                  (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
                {P : Consts} {Dom : FieldDom 3 3 N₁ Tk.m₁ (k + 1) 2 (rhoSep Tk.m₁)}
                (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
                (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
                (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1)
                    (rhoSep Tk.m₁), (∀ i, j < i → G.Ω i = ∅) →
                  ∀ Ψ : Fld 3 3 N₁ Tk.m₁ (k + 1) 2, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
                  (∀ x x', jBlock 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) j x = jBlock 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) j x' →
                    Ψ x = Ψ x') →
                  Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
                (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus 3 3 N₁ Tk.m₁ (k + 1)))
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide 3 C.m₀ Tk.m₁ τ.1.1) τ.1.2.1 -
                  natT fun _ => 3 / 2 * cellSide 3 C.m₀ Tk.m₁ τ.1.1) (3 * cellSide 3 C.m₀ Tk.m₁ τ.1.1))
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1)))
                  (E₀ : Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1) × CTorus 3 3 N₁ Tk.m₁ (k + 1))),
                  ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
                    bondCost (scaleW 3 C.m₀ Tk.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
                (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : C.m₀ = m₀),
              ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) (rhoSep Tk.m₁))
                (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) (rhoSep Tk.m₁))
                (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ Tk.m₁ (k + 1))),
                (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ Tk.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
                (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν Tk.c Tk.BG Tk.κ 324 Tk.t (l * δ₃) (X₀ τ) (X₁f τ) τ.1.1) ∧
                (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.κ Tk.BG Tk.t (l * δ₃)
                  (levelKc 3 3) (Cchi 3 3) Tk.c₂ Tk.BG₂ Tk.t (l * δfl) (X₁f τ)) ∧
                ∀
                -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2 →
                    ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
                  (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
                    Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
                      bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
                  ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.BG Tk.κ Tk.t
                    (X₁f τ) Tk.BG₂ Tk.t,
                  ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
                    (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) (compWeight 3 S.a₁) t.1.1
                      t.2.1 t.2.2) →
                  Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
                    dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
                -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
                -- (P1 (3.128), open)
                (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ Tk.m₁) (k + 1) 2 →
                    ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
                  (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
                    Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
                      bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
                  ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) S.a₁ S.ν Tk.BG Tk.κ Tk.t
                    (X₁f τ) Tk.BG₂ Tk.t,
                  ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) Fk
                    (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ Tk.m₁ k (rhoSep Tk.m₁)) (compWeight 3 S.a₁) t.1.1
                      t.2.1 t.2.2) →
                  ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
                    Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
                {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
                  Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
                (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
              -- the old densities are analytic along the path
              (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
                ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
                AnalyticAt ℂ
                  (fun q : Fld 3 3 N₁ Tk.m₁ (k + 1) 2 × Fld 3 3 N₁ Tk.m₁ (k + 1) 2 =>
                    Edens C.m₀ C.Tm j q.1 q.2)
                  (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
              -- the smallness of the class constants against the marked radius
              (corrU / (Tk.t / (2 * markedRad 3 3 2 k S.a₁ Tk.κ p₁
                      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
                  (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + Tk.m₁)) ^ 3 * P.E₀ *
                  (2 * K0 3 3 Tk.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
                    n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
                  Real.exp ((2 * Tk.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
                    ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤
                  1 / (8 * (2 * (K0 3 3 Tk.κ0 + 1) + (K0 3 3 Tk.κ0 + rootUnionK 3 3 1 Tk.m₁ Tk.κ0) +
                    rootUnionK 3 3 1 Tk.m₁ Tk.κ0) ^ 3 * c1 3 3 *
                    Real.exp (((2 * Tk.κdec - 1) - 2 * Tk.κ0) * cG 3 3 + c1 3 3 + Tk.κ' * cG 3 3))) →
              ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁)
                  (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
                (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tk.m₁) (K := k + 1) 1 (k + 1)
                    Set.univ),
                  AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν Tk.t) ∧
                  (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ∀ θ' ∈ physV S S.a₁ S.ν Tk.t,
                    physRestrict (N := 2) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                        (physIncl 2 S θ) =
                      physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl 2 S θ') →
                    e θ T' = e θ' T') ∧
                  (∀ θ ∈ physV S S.a₁ S.ν Tk.t, ‖e θ T'‖ ≤
                    27 * covBLogMax 3 3 Tk.κ /
                        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp Tk.κ)) *
                        Real.exp (-((Tk.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                          dExt T') +
                      B * Real.exp (-Tk.κ' * dExt T')) ∧
                  (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
                (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 Tk.t D →
                  Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ Tk.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
                  (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
                    rawSub 2 S.G'), (0 : CTorus 3 3 N₁ Tk.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
                ∀ ε : ℝ, ε ≤ Tk.t → ∀ q : Fld 3 3 N₁ Tk.m₁ (k + 1) 2 × Fld 3 3 N₁ Tk.m₁ (k + 1) 2,
                  XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
                  Jr.densE0 C (rootSite z) q = ∑ T',
                    (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
                      e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0)   := by
  classical
  obtain ⟨κmin, hlo, T₀, δ₃, δfl, κdec, hκ₀, hr₀, hnB₀, hnF₀, Hroom⟩ :=
    exists_stepTower_room m₀ stepHullMin
  have ht0 := T₀.t_pos
  have hx : 0 ≤ xiK2 3 3 2 := by
    have := cK2_pos 3 3 2
    unfold xiK2; positivity
  have hd := hnB₀.δ₃_nn
  have hf := hnF₀.δfl_nn
  have hR0 : 0 < T₀.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl := by
    have := mul_nonneg hx hd
    have := mul_nonneg hx hf
    linarith
  set R : ℝ := T₀.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl with hR
  set m : ℝ := min 1 (c₁ / R) with hm
  have hm0 : 0 < m := lt_min one_pos (div_pos hc₁ hR0)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmR : m ≤ c₁ / R := min_le_right _ _
  have hcR : 0 < m * T₀.t := mul_pos hm0 ht0
  have hαR : 2 * α < 1 := hα
  obtain ⟨β₀, hβ₀, H⟩ := e0CoeffFamily_class_exists_tower_struct_step_agree m₀ hlo T₀ hκ₀ hr₀ hA
    p hcR hα
  refine ⟨κmin, hlo, T₀, δ₃, δfl, κdec, β₀, hβ₀, fun ε hε hεc k hk => ?_⟩
  have hεk : 0 < ε (k + 1) := lt_of_lt_of_le (by positivity) (hεc (k + 1))
  obtain ⟨Tk, l, hl0, hl1, hl, hTt, hTε, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hC, hF,
    hroom⟩ := Hroom ε hε k hεk
  have hw0 : 0 < (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) := by positivity
  have hw1 : (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : 0 ≤ α * ((k : ℝ) + 1) := by positivity
    linarith
  set w : ℝ := (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) with hw
  have hεw : c₁ * w ≤ ε (k + 1) := by
    have := hεc (k + 1)
    push_cast at this
    exact this
  have hlw : w * m ≤ l := by
    rw [hl]
    refine le_min ?_ ?_
    · nlinarith
    · rw [le_div_iff₀ hR0]
      have h1 : w * m * R ≤ w * (c₁ / R) * R := by gcongr
      have h2 : w * (c₁ / R) * R = c₁ * w := by field_simp
      linarith
  have hct : (m * T₀.t) * w ≤ Tk.t := by
    rw [hTt]
    nlinarith
  refine ⟨Tk, l, hl0, hl1, hl, hTt, hTε, hTm, hTc, hTB, hTκ, hTc₂, hTB₂, hTδc, hTδ, hTδ', hC, hF,
    hroom, ?_⟩
  intro N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  exact H Tk hTm hTB hTB₂ hTκ hTδ (l * δ₃) (l * δfl) hC hF k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁
    hp0 hp₁ S hS


end Balaban.Inhabited
