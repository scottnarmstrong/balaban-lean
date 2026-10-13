/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1CoeffFamilyG
public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Inhabited.DetPackageFromTowerG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The determinant term in parameter form, and the energy coefficient family, general tower

`detParamFamily` (moved from `E0CoeffFamily.lean`, name and statement unchanged; it is generic in
`d`, `L`, `N`): for a record `E : DetExpansionLocC S m₀ z eps κ'' cdet` of the determinant
expansion, the term `E.term D` is a function `dz` of the parameter `θ = (raw datum, source)`,
analytic on `physV`, local in the raw datum on the thickening of `Ŷ(sitesOf T)`, bounded by
`cdet · exp(-κ'' d_Ext T)` on `physV`, and supported on rooted polymer sets.

* `StepTowerG.detConst_le_mul`: the determinant constant of `T` is at most `2 · const · K₀`.
* `e0CoeffFamily_value_fromTowerG`: for the general tower with `T.m₀ = 1`, the mark coefficient
  family of `e1CoeffFamily_value_fromTowerG` together with the determinant function `dz` (with the
  determinant half of the value at every datum of the chart: `-½ ∑_{y ∈ B(z)} tr 𝕃(y,y) = ∑_T dz`
  and `ℰ₀ = ∑_T dz + ℰ₁`) and the sum `e0 = dz + c`, which has the four properties (analyticity,
  locality, the bound `(2 · cdet + 1) K₀ e^{-κ' d_Ext}`, polymer support) and
  `ℰ₀ = ∑_T e0 (rawOf D′, 0) T` at every datum `D′` of the chart with constant field `h₀`.
* `e0CoeffFamily_fromTowerG`: the corollary without the value clauses.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section Det

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **The determinant term as a function of the parameter.**  For a record of the determinant
expansion at a step whose chart is open in the subspace of data, there is a function `dz` of the
parameter `θ = (raw datum, source)` which equals `E.term D` at `θ = (rawOf D, g)` for every datum `D`
of the chart, and which is analytic on `physV`, local (equal at two parameters of `physV` whose raw
data and sources agree on the thickening of `Ŷ(sitesOf T)`), bounded by `cdet e^{-κ'' d_Ext T}` on
`physV`, and non-zero only at rooted polymer sets.  No locality on `sitesOf T` itself is asserted
for an individual `dz`: the determinant's locality on its own domain is supplied by the
collar-grouped record on the `renYs` domains (`renE0_fibre_det_at`). -/
theorem detParamFamily {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}
    (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν) :
    ∃ dz : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        m₀ (k + 1) Set.univ) → ℂ,
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ∀ (g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) T,
          dz (⟨rawOf D, rawOf_mem_rawSub D⟩, g) T = E.term D T) ∧
      ∀ T, AnalyticOnNhd ℂ (fun θ => dz θ T) (physV S S.a₁ S.ν eps) ∧
        (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
          physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T))) (physIncl N S θ) =
            physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T))) (physIncl N S θ') →
          dz θ T = dz θ' T) ∧
        (∀ θ ∈ physV S S.a₁ S.ν eps, ‖dz θ T‖ ≤ cdet * Real.exp (-κ'' * dExt T)) ∧
        (∀ θ, dz θ T ≠ 0 → rootCube (m₀ := m₀) (K := k + 1) z ∈ T ∧
          IsPolyDom m₀ (k + 1) (sitesOf T)) := by
  choose A hA1 hA2 using E.analyticAt_raw
  let dz : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        m₀ (k + 1) Set.univ) → ℂ := fun θ T =>
    if h : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps then E.term (Classical.choose h) T
      else 0
  have hdz : ∀ (θ : physParam N S) T (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D → dz θ T = E.term D T := by
    intro θ T D hD hθD
    have hmem : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps := ⟨D, hD, hθD⟩
    have hdef : dz θ T = E.term (Classical.choose hmem) T := by
      simp only [dz, hmem, ↓reduceDIte]
    obtain ⟨hD₀, hr₀⟩ := Classical.choose_spec hmem
    have : Classical.choose hmem = D := BgData.eq_of_raw (hr₀.symm.trans hθD)
    rw [hdef, this]
  have hchart : ∀ θ ∈ physV S S.a₁ S.ν eps, ∃ D : BgData S.G' N,
      XiCData S.G' S.a S.ν (k + 1) 1 eps D ∧
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D := fun θ hθ => hθ.1
  refine ⟨dz, fun D hD g T => hdz _ T D hD rfl, fun T => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ hθ
    obtain ⟨D, hD, hθD⟩ := hchart θ hθ
    let f : physParam N S →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N :=
      (rawSub N S.G').subtypeL.comp (ContinuousLinearMap.fst ℂ _ _)
    have hf : f θ = rawOf D := hθD
    have han : AnalyticAt ℂ (A T) (f θ) := by
      rw [hf]; exact hA1 T D hD
    have hcomp : AnalyticAt ℂ (fun θ' => A T (f θ')) θ := han.comp (f.analyticAt θ)
    have hU : IsOpen {θ' : physParam N S | (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps} :=
      (isOpen_preimage_xiCRaw (N := N) (G := S.G') (σ := 1) (ε := eps) (n := k + 1) H).preimage
        continuous_fst
    refine hcomp.congr ?_
    filter_upwards [hU.mem_nhds ⟨D, hD, hθD⟩] with θ' hθ'
    obtain ⟨D', hD', hθ'D⟩ := hθ'
    rw [hdz θ' T D' hD' hθ'D, ← hA2 T D' hD']
    show A T (f θ') = A T (rawOf D')
    rw [show f θ' = rawOf D' from hθ'D]
  · intro θ hθ θ' hθ' h
    obtain ⟨D, hD, hθD⟩ := hchart θ hθ
    obtain ⟨D', hD', hθ'D⟩ := hchart θ' hθ'
    rw [hdz θ T D hD hθD, hdz θ' T D' hD' hθ'D]
    refine E.local_resDep D D' hD hD' T (fun x hx w hw => ?_)
    have hwmem : w ∈ thickSet S.G' (Yhat Set.univ (sitesOf T)) :=
      Or.inr ⟨x, Or.inl hx, x.2, hw⟩
    have := congrFun h ⟨w, hwmem⟩
    simp only [physRestrict, physIncl_apply, Prod.mk.injEq] at this
    obtain ⟨e1, e2, -⟩ := this
    have hΨ : D.Ψ w = D'.Ψ w := by
      have a1 : D.Ψ w = (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 w := by rw [hθD]; rfl
      have a2 : D'.Ψ w = (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 w := by rw [hθ'D]; rfl
      rw [a1, a2, e1]
    refine ⟨hΨ, fun _ => ?_⟩
    have a1 : D.h w = (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 w := by rw [hθD]; rfl
    have a2 : D'.h w = (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 w := by rw [hθ'D]; rfl
    rw [a1, a2, e2]
  · intro θ hθ
    obtain ⟨D, hD, hθD⟩ := hchart θ hθ
    rw [hdz θ T D hD hθD]
    exact E.bound D hD T
  · intro θ hθ
    by_cases hmem : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps
    · obtain ⟨D, hD, hθD⟩ := hmem
      rw [hdz θ T D hD hθD] at hθ
      exact E.anchor D hD T hθ
    · exact absurd (by simp only [dz, hmem, ↓reduceDIte]) hθ

end Det
section Main

/-- `K₀ ≥ 1`. -/
theorem one_le_K0_aux (d L : ℕ) [NeZero L] (κ0 : ℝ) : 1 ≤ K0 d L κ0 := by
  unfold K0
  have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have h2 : 0 < 1 - Real.exp (-1) := by linarith
  rw [le_div_iff₀ h2]
  have := Real.one_le_exp (aEnt_nonneg d L)
  have := Real.exp_pos (-1)
  linarith

/-- The determinant constant of the general tower is at most `2 · const · K₀`. -/
theorem StepTowerG.detConst_le_mul {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) :
    (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) ≤
    2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * K0 d L T.κ0 := by
  have h0 := T.detConst_nonneg
  have h1 := one_le_K0_aux d L T.κ0
  nlinarith

open Classical in
/-- **The energy coefficient family at the general tower with its value on the fibre `h ≡ h₀`.**
See the module doc-string. -/
theorem e0CoeffFamily_value_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
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
          (∀ (D' : BgData S.G' N)
              (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a
              S.ν (k + 1) 1 T.t D' →
            (S.withDatum D' hDh).E1locC
                (zeroClass d L N₁ T.m₁ k N ϱ) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
          ∃ dz : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
              -(1 / 2 : ℂ) * ∑ y ∈ (S.withDatum D' hDh).blockU z, ∑ i,
                  (S.withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  (S.withDatum D' hDh).E1locC (zeroClass d L N₁ T.m₁ k N ϱ) z) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                dz θ C = dz θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖dz θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
          ∃ e0 : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ θ C, e0 θ C = dz θ C + c θ C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                e0 θ C = e0 θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖e0 θ C‖ ≤ (2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) + 1) * K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
            (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
              (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, e0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                  (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hβ'⟩ :=
    H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨hP, hfam, c, hc, hC, hcv⟩ := hβ'.1 z
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  have hLN : L ∣ N₁ := by rw [hm₀] at h3N; simpa using h3N
  have hE : ∃ E : DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
      ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
      ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))), True :=
    ((detExpansionLocC_scale_of_towerG T.hd T.hL T.hN T.m₁_four T.t_pos (Classical.choice T.core)
      T.large_block T.dom_margin T.coer_margin T.δc_small T.det_z k hk N₁ hLN hN hν0.le hν β
      p₁ T.δ).2 z).imp fun _ _ => trivial
  obtain ⟨E, -⟩ := hE
  obtain ⟨dz, hdz1, hdz2⟩ := detParamFamily (N := N) E
    (bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0.le hν)
  have hc0 := T.detConst_nonneg
  have hdet := T.detConst_le_mul
  have hrate := T.det_rate
  have hdz1' : ∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' N)
      (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
        (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
      -(1 / 2 : ℂ) * ∑ y ∈ ((T.step k hk N₁ ν β p₁).withDatum D' hDh).blockU z, ∑ i,
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).logAC (y, i) (y, i) =
        ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
      ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
          (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) z =
        ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
            (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) z := by
    intro D' hDh hX g
    have hs : -(1 / 2 : ℂ) * ∑ y ∈ ((T.step k hk N₁ ν β p₁).withDatum D' hDh).blockU z, ∑ i,
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).logAC (y, i) (y, i) =
        ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C := by
      rw [(E.atDatum D' hDh hX).sum_eq]
      exact Finset.sum_congr rfl fun C _ => (hdz1 D' hX g C).symm
    refine ⟨hs, ?_⟩
    unfold StepSetting.E0locC
    rw [hs]
  have hdzB : ∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
      (k + 1) Set.univ), ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
        (T.step k hk N₁ ν β p₁).ν T.t,
      ‖dz θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
          Real.exp (-T.κ' * dExt C) := by
    intro C θ hθ
    refine ((hdz2 C).2.2.1 θ hθ).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0)
    nlinarith [dExt_nonneg (m₀ := 1) (j := k + 1) (Ω := Set.univ) C]
  refine ⟨hP, hfam, c, hc, hC, hcv, dz, hdz1', ?_, ?_⟩
  · intro C
    obtain ⟨a1, a2, a3, a4⟩ := hdz2 C
    exact ⟨a1, a2, hdzB C, a4⟩
  · refine ⟨fun θ C => dz θ C + c θ C, fun _ _ => rfl, fun C => ?_, fun D' hDh hX => ?_⟩
    swap
    · obtain ⟨-, hsum⟩ := hdz1' D' hDh hX 0
      rw [hsum, hcv D' hDh hX, ← Finset.sum_add_distrib]
    obtain ⟨a1, a2, a3, a4⟩ := hdz2 C
    obtain ⟨b1, b2, -, b3, b4⟩ := hC C
    refine ⟨a1.add b1, fun θ hθ θ' hθ' h => ?_, fun θ hθ => ?_, fun θ hθ => ?_⟩
    · show dz θ C + c θ C = dz θ' C + c θ' C
      rw [a2 θ hθ θ' hθ' h, b2 θ hθ θ' hθ' h]
    · refine (norm_add_le _ _).trans ?_
      have h1 : ‖dz θ C‖ ≤ 2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * K0 d L T.κ0 *
          Real.exp (-T.κ' * dExt C) :=
        (hdzB C θ hθ).trans (mul_le_mul_of_nonneg_right hdet (Real.exp_pos _).le)
      have h2 := b3 θ hθ
      nlinarith
    · have hne : dz θ C + c θ C ≠ 0 := hθ
      by_cases h0 : dz θ C = 0
      · rw [h0, zero_add] at hne
        exact ⟨(b4 θ hne).1, (b4 θ hne).2.1⟩
      · exact a4 θ h0

open Classical in
/-- **The energy coefficient family at the general tower: determinant, marks and their sum.**
See the module doc-string.  The first part is `e1CoeffFamily_fromTowerG`; then the determinant
function `dz` (with the determinant half of the value at every datum of the chart) and the sum
`e0 = dz + c`. -/
theorem e0CoeffFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
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
              ‖c θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          ∃ dz : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
              -(1 / 2 : ℂ) * ∑ y ∈ (S.withDatum D' hDh).blockU z, ∑ i,
                  (S.withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  (S.withDatum D' hDh).E1locC (zeroClass d L N₁ T.m₁ k N ϱ) z) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                dz θ C = dz θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖dz θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
          ∃ e0 : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ θ C, e0 θ C = dz θ C + c θ C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                e0 θ C = e0 θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖e0 θ C‖ ≤ (2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) + 1) * K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp₁ D ϱ hϱ S hS hp => ?_⟩
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ :=
    H k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, -, dz, hdz, hdzl, e0, he, hel, -⟩ := hz z
  exact ⟨h1, h2, c, hc,
    (fun C => ⟨(hcl C).1, (hcl C).2.1, (hcl C).2.2.2.1, (hcl C).2.2.2.2⟩),
    dz, hdz, hdzl, e0, he, hel⟩

end Main

end Balaban.Inhabited
