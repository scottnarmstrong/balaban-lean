/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralClassPathAnalytic
public import Balaban.Inhabited.StepTowerChainStruct

/-!
# Analyticity of the old densities from the membership of the pair in the class domain

For a class with the clauses `SFTermClauses P Dom Tm`, the density `ℰ^{(j)}` is analytic at every
pair `(ψ, h)` that lies in `Dom.dom j (Tm.gs j X)` for all the polymers `X` of scale `j`
(`analyticAt_Edens_of_dom`).  Hence the analyticity of `Edens` along the path of the composed pairs
`Jr.PJ j (rawOf D, s • ŷ(x))` is a consequence of the membership of those pairs in the class
domain (`analyticAt_Edens_path_of_dom`); the membership is the chart condition of the composed
pairs at the levels `j ≤ k` (for `levelGS j`), the same kind of condition as `hchart`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation Finset Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **`ℰ^{(j)}` is analytic at a pair lying in the class domain of every polymer of scale `j`.** -/
theorem analyticAt_Edens_of_dom {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P Dom Tm) {m₀ : ℕ} (hm : P.m₀ = m₀)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {p₀ : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : ∀ X, IsPolyDom m₀ j X → Dom.dom j (Tm.gs j X) p₀.1 p₀.2) :
    AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens m₀ Tm j p.1 p.2) p₀ := by
  unfold Edens
  refine Finset.analyticAt_fun_sum _ fun y _ => ?_
  unfold Eloc
  refine analyticAt_finsum_polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j y
    (fun X (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) => Tm.E j y X p.1 p.2)
    fun X hX hy => ?_
  have hX' : IsPolyDom P.m₀ j X := hm ▸ hX
  exact hcl.analyticE j hj1 (hjk.trans (Nat.le_succ k)) y X hX' hy _ (hp X hX)

/-- **Path analyticity of `Edens` from the membership of the composed pairs in the class domain**:
the premise of `e0CoeffFamily_class_exists_tower_struct` on the analyticity of `Edens` at the
composed pairs `Jr.PJ j (rawOf D, s • ŷ(x))`, from the membership of those pairs in
`Dom.dom j (Tm.gs j X)` for every polymer `X` of scale `j`. -/
theorem analyticAt_Edens_path_of_dom {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (hcl : SFTermClauses P Dom C.Tm) (hm : P.m₀ = C.m₀) {eps pp : ℝ}
    (Jr : S.JointRep eps pp)
    (hpair : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        ∀ X, IsPolyDom C.m₀ j X →
          Dom.dom j (C.Tm.gs j X) (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)).1
            (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)).2) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)) := by
  intro D hD s hs x hx j hj
  have hj' := Finset.mem_Icc.1 hj
  exact analyticAt_Edens_of_dom hcl hm hj'.1 hj'.2 (hpair D hD s hs x hx j hj)


open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The class chain at a tower with the path analyticity reduced to the chart of the composed
pairs**: `e0CoeffFamily_class_exists_tower_struct` with the analyticity of `Edens` along the path
replaced by the membership of the composed pairs `Jr.PJ j (rawOf D, s • ŷ(x))` in the class domain
(`analyticAt_Edens_path_of_dom`). -/
theorem e0CoeffFamily_class_exists_tower_struct_pair (m₀ : ℕ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (κmin : ℝ) (_ : stepHullMin ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ), ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
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
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
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
        -- the chart of the label generators lies in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the composed pairs of the path lie in the class domain of every polymer
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        ∀ X, IsPolyDom C.m₀ j X →
          Dom.dom j (C.Tm.gs j X) (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x)).1
            (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x)).2) →
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

  obtain ⟨κmin, hlo, T, δ₃, δfl, κdec, β₀, hβ₀, H⟩ :=
    e0CoeffFamily_class_exists_tower_struct m₀ hA p
  refine ⟨κmin, hlo, T, δ₃, δfl, κdec, β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  obtain ⟨Jr, HJ⟩ := H k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom bL hb₁ hbC hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hCm
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, HG⟩ := @HJ C z 𝒯E h𝒯 P Dom bL hb₁ hbC hm hcl hE₀ i₀ i₁
    hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hpair hnum
  exact @HG hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL
    (analyticAt_Edens_path_of_dom hcl hm Jr hpair) hnum

end Balaban.Inhabited
