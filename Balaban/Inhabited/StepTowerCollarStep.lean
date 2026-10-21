/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCollarStruct

/-!
# The class chain with the per-label premises at the composed step data: fluctuation radius
free, general collar, every tower radius (`StepTowerCollarStep`)

`e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar`: the instance of
`e0CoeffFamily_class_exists_tower_struct_onSet_dec_agree_collar` at the sets of composed step data
(`hchart`, `hEbd` at the composed data of the realizable triples `t ∈ FlRealLC … T.t (X₁f τ) T.BG₂ δ₁`,
for every background map of `Gk τ`), as `e0CoeffFamily_class_exists_tower_struct_step_decoupled`
is the instance of `e0CoeffFamily_class_exists_tower_struct_onSet_dec`.  One threshold `β₀` serves
every tower agreeing with `T₀`, every collar `r₀ ∈ [324, 360]`, every fluctuation radius `δ₁ ≤ T.t`
and every scale `k` with `δ₁ ≥ c 3^{-α(k+1)}`; the step chart (`JointRep`, `physV`, `XiCData`,
`XiDom`) has the step radius `T.t`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The class chain at a general tower, per-label premises at the composed step data, with the
formula of its family.**  The statement of
`StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi` with one more premise of
`hΦ`: the family `e` is the coefficient of a system of the new level of `C` (`NewLevelFormula`). -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi_formula {d L N : ℕ} [NeZero L] (m₀ : ℕ) {κmin : ℝ}
    (T₀ : StepTowerG d L N κmin) (hm₀ : T₀.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ) {κdec : ℝ}
    (hκ₀ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T₀.κ)
    (hrate₀ : (2 * T₀.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
      (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ → ∀ r₀ δ₃ δ₁ δfl : ℝ, 4 * (d : ℝ) * (L : ℝ) ^ 3 ≤ r₀ → r₀ ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 + 4 * d * L →
      ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃ → FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl →
      δ₁ ≤ T.t →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ δ₁ →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ {ϱ : ℝ} (_ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (_ : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass d L N₁ T.m₁ k N ϱ) (z : RootIdx d L N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus d L N₁ T.m₁ (k + 1) × Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ T.m₁ (k + 1) ×
            Set (CTorus d L N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom d L N₁ T.m₁ (k + 1) N ϱ}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ T.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => L / 2 * cellSide L C.m₀ T.m₁ τ.1.1) (L * cellSide L C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW L C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : L ^ C.m₀ ∣ N₁) (_ : d ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
        (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + r₀ * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
        (_ : rhoSepG d L T.m₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s))) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc d L) (Cchi d L) T.c₂ T.BG₂ δ₁ δfl (X₁f τ)) ∧
        (ClassHatCond C s r₀ → ∀ τ : {τ // τ ∈ 𝒯E}, Gj τ = C.Tm.gs τ.1.1 τ.1.2.2) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃))))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / (δ₁ / (2 * markedRad d L N k S.a₁ T.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L T.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
          1 / (8 * (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
            rootUnionK d L 1 T.m₁ T.κ0) ^ 3 * c1 d L *
            Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L))) →
      (Φ : (physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') →
        (NewLevelFormulaW S C z Jr
          ⟨T.κ, T.BG, T.BG₂, p₁, T.κ0, T.κ, T.BG, T.BG₂, δ₁, p₁, C.m₀, T.c, r₀, δ₃, levelKc d L,
            Cchi d L, T.c₂, δfl⟩ e ∧
          (ClassHatCond C s r₀ → NewLevelFormula S C z Jr
          ⟨T.κ, T.BG, T.BG₂, p₁, T.κ0, T.κ, T.BG, T.BG₂, δ₁, p₁, C.m₀, T.c, r₀, δ₃, levelKc d L,
            Cchi d L, T.c₂, δfl⟩ e)) →
        B ≤ CPE d L (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
          rootUnionK d L 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          (corrF0G T k β p₁ * K0 d L T.κ0 +
            (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L T.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) / (2 * (δ₁ / (4 * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁))) *
              (((nFibre d L : ℕ) : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)) * K0 d L T.κ0 +
            ((nFibre d L : ℕ) : ℝ) * Real.exp (T.κ0 * cBr d L) * K0 d L T.κ0) → Φ e B) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl N S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
            (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) *
                Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  dExt T') +
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, HC⟩ :=
    StepTowerG.e0CoeffFamily_class_exists_tower_struct_onSet_dec_agree_collar_phi_formula m₀ T₀ hm₀ hhull hκ₀ hrate₀ hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₀T hm₁ hBG hBG₂ hκT hk0 hk' hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, HC'⟩ := HC T hm₀T hm₁ hBG hBG₂ hκT hk0 hk' hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T k hk
    N₁ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hGjC, HG⟩ := @HC' C z 𝒯E h𝒯 P Dom 1 le_rfl
    (one_le_scaledC0 d) hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hGjC, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL
  exact @HG
    (fun τ => {r | ∃ Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ),
      (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
        Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
          bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) ∧
      ∃ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k (ϱ)) S.a₁ S.ν T.BG T.κ T.t (X₁f τ) T.BG₂
        δ₁, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
          (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k (ϱ)) (compWeight L S.a₁) t.1.1
            t.2.1 t.2.2)})
    (fun τ r hr => by
      obtain ⟨Fk, hFk, t, ht, rfl⟩ := hr
      exact hchart τ Fk hFk t ht _ rfl) Bτ hBτ
    (fun τ r hr => by
      obtain ⟨Fk, hFk, t, ht, rfl⟩ := hr
      exact hEbd τ Fk hFk t ht _ rfl) CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL
    (fun τ Fk hFk t ht => ⟨Fk, hFk, t, ht, rfl⟩)

open Classical in
/-- The class chain at the composed step data of a general tower, at a general collar, with `B` bounded by an explicit constant. -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi {d L N : ℕ} [NeZero L] (m₀ : ℕ) {κmin : ℝ}
    (T₀ : StepTowerG d L N κmin) (hm₀ : T₀.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ) {κdec : ℝ}
    (hκ₀ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T₀.κ)
    (hrate₀ : (2 * T₀.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
      (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ → ∀ r₀ δ₃ δ₁ δfl : ℝ, 4 * (d : ℝ) * (L : ℝ) ^ 3 ≤ r₀ → r₀ ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 + 4 * d * L →
      ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃ → FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl →
      δ₁ ≤ T.t →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ δ₁ →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ {ϱ : ℝ} (_ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (_ : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass d L N₁ T.m₁ k N ϱ) (z : RootIdx d L N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus d L N₁ T.m₁ (k + 1) × Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ T.m₁ (k + 1) ×
            Set (CTorus d L N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom d L N₁ T.m₁ (k + 1) N ϱ}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ T.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => L / 2 * cellSide L C.m₀ T.m₁ τ.1.1) (L * cellSide L C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW L C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : L ^ C.m₀ ∣ N₁) (_ : d ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
        (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + r₀ * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
        (_ : rhoSepG d L T.m₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s))) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc d L) (Cchi d L) T.c₂ T.BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃))))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / (δ₁ / (2 * markedRad d L N k S.a₁ T.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L T.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
          1 / (8 * (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
            rootUnionK d L 1 T.m₁ T.κ0) ^ 3 * c1 d L *
            Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L))) →
      (Φ : (physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') →
        B ≤ CPE d L (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
          rootUnionK d L 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          (corrF0G T k β p₁ * K0 d L T.κ0 +
            (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L T.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) / (2 * (δ₁ / (4 * decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁))) *
              (((nFibre d L : ℕ) : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)) * K0 d L T.κ0 +
            ((nFibre d L : ℕ) : ℝ) * Real.exp (T.κ0 * cBr d L) * K0 d L T.κ0) → Φ e B) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl N S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
            (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) *
                Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  dExt T') +
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)  := by
  obtain ⟨β₀, hβ₀, H⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi_formula m₀ T₀ hm₀ hhull hκ₀ hrate₀ hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₀T hm₁ hBG hBG₂ hκT hk0 hk' hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, H'⟩ := H T hm₀T hm₁ hBG hBG₂ hκT hk0 hk' hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T k hk
    N₁ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, -, HG⟩ := @H' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X
    hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum Φ hΦ
  exact @HG hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum Φ
    (fun e B hc _ hb => hΦ e B hc hb)

open Classical in
/-- The class chain at the composed step data, at a general collar, with `B` bounded by an explicit constant. -/
theorem e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi (m₀ : ℕ) {κmin : ℝ}
    (hlo : stepHullMin ≤ κmin) (T₀ : StepTower κmin) {κdec : ℝ}
    (hκ₀ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T₀.κ)
    (hrate₀ : (2 * T₀.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
      ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ → ∀ r₀ δ₃ δ₁ δfl : ℝ, 324 ≤ r₀ → r₀ ≤ 360 →
      ChainNum 3 3 2 T.m₁ T.BG T.κ r₀ T.t δ₃ → FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl →
      δ₁ ≤ T.t →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ δ₁ →
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
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
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
            (X₁f τ) T.BG₂ δ₁,
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
      (corrU / (δ₁ / (2 * markedRad 3 3 2 k S.a₁ T.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 T.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤
          1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
            rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
            Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3))) →
      (Φ : (physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
          ∀ T', e θ' T' = e θ T') →
        B ≤ CPE 3 3 (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          (corrF0 T k β p₁ * K0 3 3 T.κ0 +
            (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 T.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) / (2 * (δ₁ / (4 * decMR T k (β * 3 ^ k) p₁))) *
              (((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)) * K0 3 3 T.κ0 +
            ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T.κ0 * cBr 3 3) * K0 3 3 T.κ0) → Φ e B) →
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
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
  classical
  obtain ⟨β₀, h3, H⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi
    m₀ T₀.toG rfl (T₀.hhull_toG_of_stepHullMin hlo) (by exact_mod_cast hκ₀) hrate₀ hA p hcR
    (alpha_three_cast hαR)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  have hr₁G : 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 ≤ r₀ := by norm_num; linarith
  have hr₂G : r₀ ≤ 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) := by
    norm_num; linarith
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ S hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hδ r₀ δ₃ δ₁ δfl hr₁G hr₂G hnB hnF hδ₁T k hk N₁
    (by simpa using h3N) hN₁ ν hν0 (by simpa using hν) β hβ
    (by rw [radius_three_cast]; exact hcδ) p₁ hp0 (by rw [e]; exact hp₁)
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm S hS
  obtain ⟨Jr, G'⟩ := G
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ hm7 hCm
  have hidxG : (((5 * 3 + 13) * 3 ^ 4 : ℕ) : ℝ) + r₀ * ((3 : ℕ) : ℝ) ≤
      (((3 - 2 : ℕ)) : ℝ) * ((3 : ℕ) : ℝ) ^ (C.m₀ + 1) := by
    have h := index_condition_shift_collar hm7 (show r₀ ≤ 1431 by linarith)
    norm_num at h ⊢
    linarith
  have hminG : rhoSepG 3 3 T.m₁ ≤ Balaban.LargeField.minSep 3 (3 ^ (T.m₁ + 4)) := by
    rw [rhoSepG_three]; exact rhoSep_le_minSep_of_four T.m₁_four
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, G''⟩ := @G' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ (by omega) 4 (by omega) hidxG hminG hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [e, h27, h18, ← corrF0_toG, ← decMR_toG] at G''
  exact @G'' hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL

open Classical in
/-- The class chain of a general tower with the per-label premises at the composed step data, at a general collar. -/
theorem StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar {d L N : ℕ} [NeZero L] (m₀ : ℕ) {κmin : ℝ}
    (T₀ : StepTowerG d L N κmin) (hm₀ : T₀.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ) {κdec : ℝ}
    (hκ₀ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T₀.κ)
    (hrate₀ : (2 * T₀.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
      (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ → ∀ r₀ δ₃ δ₁ δfl : ℝ, 4 * (d : ℝ) * (L : ℝ) ^ 3 ≤ r₀ → r₀ ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 + 4 * d * L →
      ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃ → FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl →
      δ₁ ≤ T.t →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ δ₁ →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ {ϱ : ℝ} (_ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (_ : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass d L N₁ T.m₁ k N ϱ) (z : RootIdx d L N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus d L N₁ T.m₁ (k + 1) × Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ T.m₁ (k + 1) ×
            Set (CTorus d L N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom d L N₁ T.m₁ (k + 1) N ϱ}
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ T.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => L / 2 * cellSide L C.m₀ T.m₁ τ.1.1) (L * cellSide L C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW L C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : L ^ C.m₀ ∣ N₁) (_ : d ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
        (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + r₀ * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
        (_ : rhoSepG d L T.m₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s))) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc d L) (Cchi d L) T.c₂ T.BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
              bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) Fk
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃))))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / (δ₁ / (2 * markedRad d L N k S.a₁ T.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L T.κ0 * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * ((((L : ℝ) ^ (n₁ - 1)) ^ d))))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤
          1 / (8 * (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
            rootUnionK d L 1 T.m₁ T.κ0) ^ 3 * c1 d L *
            Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L))) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl N S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
            (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) *
                Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                  dExt T') +
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, Hφ⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_phi m₀ T₀ hm₀ hhull hκ₀ hrate₀ hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₀T hm₁ hBG hBG₂ hκT hk0 hk' hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ ϱ hϱ S hS
  obtain ⟨Jr, Hφ'⟩ := Hφ T hm₀T hm₁ hBG hBG₂ hκT hk0 hk' hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T k hk
    N₁ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ hϱ S hS
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, HG⟩ := @Hφ' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 s hs hidx hmin hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
  obtain ⟨e, B, -, h⟩ := @HG hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
    (fun _ _ => True) (fun _ _ _ _ => trivial)
  exact ⟨e, B, h⟩

open Classical in
/-- **The class chain, structural premises discharged, per-label premises at the composed step
data, at a fluctuation radius `δ₁ ≤ T.t` and a collar `r₀ ∈ [324, 360]`, for every tower agreeing
with `T₀` and every scale with `δ₁ ≥ c 3^{-α(k+1)}`, beyond one threshold.** -/
theorem e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar (m₀ : ℕ) {κmin : ℝ}
    (hlo : stepHullMin ≤ κmin) (T₀ : StepTower κmin) {κdec : ℝ}
    (hκ₀ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T₀.κ)
    (hrate₀ : (2 * T₀.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
      ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ → ∀ r₀ δ₃ δ₁ δfl : ℝ, 324 ≤ r₀ → r₀ ≤ 360 →
      ChainNum 3 3 2 T.m₁ T.BG T.κ r₀ T.t δ₃ → FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl →
      δ₁ ≤ T.t →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ δ₁ →
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
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (Fk : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ)),
          (∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
            Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
              bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D)) →
          ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
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
            (X₁f τ) T.BG₂ δ₁,
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
      (corrU / (δ₁ / (2 * markedRad 3 3 2 k S.a₁ T.κ p₁
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
  classical
  obtain ⟨β₀, h3, H⟩ := StepTowerG.e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar
    m₀ T₀.toG rfl (T₀.hhull_toG_of_stepHullMin hlo) (by exact_mod_cast hκ₀) hrate₀ hA p hcR
    (alpha_three_cast hαR)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ hδ r₀ δ₃ δ₁ δfl hr₁ hr₂ hnB hnF hδ₁T => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  have hr₁G : 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 ≤ r₀ := by norm_num; linarith
  have hr₂G : r₀ ≤ 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ 3 + 4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) := by
    norm_num; linarith
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hcδ p₁ hp0 hp₁ S hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hδ r₀ δ₃ δ₁ δfl hr₁G hr₂G hnB hnF hδ₁T k hk N₁
    (by simpa using h3N) hN₁ ν hν0 (by simpa using hν) β hβ
    (by rw [radius_three_cast]; exact hcδ) p₁ hp0 (by rw [e]; exact hp₁)
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm S hS
  obtain ⟨Jr, G'⟩ := G
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ hm7 hCm
  have hidxG : (((5 * 3 + 13) * 3 ^ 4 : ℕ) : ℝ) + r₀ * ((3 : ℕ) : ℝ) ≤
      (((3 - 2 : ℕ)) : ℝ) * ((3 : ℕ) : ℝ) ^ (C.m₀ + 1) := by
    have h := index_condition_shift_collar hm7 (show r₀ ≤ 1431 by linarith)
    norm_num at h ⊢
    linarith
  have hminG : rhoSepG 3 3 T.m₁ ≤ Balaban.LargeField.minSep 3 (3 ^ (T.m₁ + 4)) := by
    rw [rhoSepG_three]; exact rhoSep_le_minSep_of_four T.m₁_four
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, G''⟩ := @G' C z 𝒯E h𝒯 P Dom hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN₃ (by omega) 4 (by omega) hidxG hminG hCm
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [h27, h18] at G''
  exact @G'' hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum

end Balaban.Inhabited
