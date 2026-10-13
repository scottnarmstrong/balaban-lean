/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1CoeffFamily
public import Balaban.Inhabited.Thm31aFromTower
public import Balaban.Inhabited.StepTowerScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The determinant term in parameter form, and the energy coefficient family

For a record `E : DetExpansionLocC S m₀ z eps κ'' cdet` of the determinant expansion, the term
`E.term D T` is a function of the datum `D` of the chart.  Writing the datum through its raw part
`rawOf D` (a point of the subspace `rawSub`), `detParamFamily` produces a function
`dz : physParam N S → (sets of cubes) → ℂ` of the parameter `θ = (raw datum, source)` with
`dz (⟨rawOf D, _⟩, g) T = E.term D T` at every datum of the chart and every source `g`, analytic on
`physV`, local in the raw datum on the thickening of `Ŷ(sitesOf T)`, bounded by
`cdet · exp(-κ'' d_Ext T)` on `physV`, and supported on rooted polymer sets.

`e0CoeffFamily_fromTower` adds this to the mark coefficient of `e1CoeffFamily_fromTower`: at a scale
of the tower, for every root `z`, the determinant term and the sum `e0 = dz + c` carry the same four
properties (analyticity, locality, the bound `(2 · 27 · BL + 1) K₀ e^{-κ' d_Ext}`, polymer support),
and the determinant half of the value at every datum of the chart is proved:
`-½ ∑_{y ∈ B(z)} tr 𝕃(y,y) = ∑_T dz(θ') T` and `ℰ₀ = ∑_T dz(θ') T + ℰ₁`.
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
`physV`, and non-zero only at rooted polymer sets. -/
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

/-- The numerical facts about the determinant constant of the tower used in the sum:
`27 BL ≥ 0`, and `27 BL ≤ 2 · 27 · BL · K₀`. -/
theorem towerDetConst_le_mul {κmin : ℝ} (T : StepTower κmin) :
    0 ≤ 27 * covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) ∧
      27 * covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) ≤
      2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) * K0 3 3 T.κ0 := by
  have hz := T.det_z
  have hzpos : 0 < 1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ) := by linarith
  have hκ : 0 ≤ T.κ := by
    have h1 := T.κ_lower
    have h0 := T.κ0_nonneg
    have h2 := T.κdec_lower
    have : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * T.κdec := by
      have : (0 : ℝ) ≤ T.κdec := by linarith
      positivity
    linarith
  have hBL : 0 ≤ covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) := by
    have h1 := one_le_covBLog 3 (L := 3) (by norm_num) (a := 2) (by norm_num)
      (2 / (3 : ℝ) ^ 2) hκ
    unfold covBLogMax
    exact div_nonneg (by linarith) hzpos.le
  have hK1 : 1 ≤ K0 3 3 T.κ0 := by
    unfold K0
    have h1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
    have h2 : 0 < 1 - Real.exp (-1) := by linarith
    rw [le_div_iff₀ h2]
    have := Real.one_le_exp (aEnt_nonneg 3 3)
    have := Real.exp_pos (-1)
    linarith
  rw [mul_div_assoc]
  exact ⟨by positivity, by nlinarith [mul_nonneg hBL (sub_nonneg.2 hK1)]⟩

open Classical in
/-- **The energy coefficient family at the tower: determinant, marks and their sum.**  See the
module doc-string.  The first part is `e1CoeffFamily_fromTower`; then the determinant function
`dz` (with the determinant half of the value at every datum of the chart) and the sum
`e0 = dz + c`. -/
theorem e0CoeffFamily_fromTower {κmin : ℝ} (T : StepTower κmin)
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
          (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
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
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          ∃ dz : physParam 2 (T.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
                (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
              XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
              ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
              -(1 / 2 : ℂ) * ∑ y ∈ ((T.step k hk N₁ ν β p₁).withDatum D' hDh).blockU z, ∑ i,
                  ((T.step k hk N₁ ν β p₁).withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z) ∧
            (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ∀ θ' ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → dz θ C = dz θ' C) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ‖dz θ C‖ ≤ (27 * (covBLogMax 3 3 T.κ / (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
            ∃ e0 : physParam 2 (T.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
              (∀ θ C, e0 θ C = dz θ C + c θ C) ∧
              (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 θ C) (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ∀ θ' ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → e0 θ C = e0 θ' C) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ‖e0 θ C‖ ≤ ((2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ / (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) + 1) * K0 3 3 T.κ0) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) := by
  obtain ⟨β₀, h3, h⟩ := e1CoeffFamily_fromTower T hHull hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hβ'⟩ :=
    h k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨hP, hfam, c, hc, hC⟩ := hβ' z
  obtain ⟨hE, hrate⟩ := detExpansionLocC_scale_fromTower T k hk N₁ h3N hN hν0.le hν β p₁
  obtain ⟨E, -⟩ := hE z
  obtain ⟨dz, hdz1, hdz2⟩ := detParamFamily (N := 2) E (bgHyp_lv (k := k) T.m₁ hν0.le hν)
  obtain ⟨hc0, hdet⟩ := towerDetConst_le_mul T
  refine ⟨hP, hfam, c, hc, hC, dz, ?_, ?_, ?_⟩
  · intro D' hDh hX g
    have hs : -(1 / 2 : ℂ) * ∑ y ∈ ((T.step k hk N₁ ν β p₁).withDatum D' hDh).blockU z, ∑ i,
        ((T.step k hk N₁ ν β p₁).withDatum D' hDh).logAC (y, i) (y, i) =
        ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C := by
      rw [(E.atDatum D' hDh hX).sum_eq]
      exact Finset.sum_congr rfl fun C _ => (hdz1 D' hX g C).symm
    refine ⟨hs, ?_⟩
    unfold StepSetting.E0locC
    rw [hs]
  · intro C
    obtain ⟨a1, a2, a3, a4⟩ := hdz2 C
    refine ⟨a1, a2, fun θ hθ => (a3 θ hθ).trans ?_, a4⟩
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by rw [← mul_div_assoc]; exact hc0)
    nlinarith [dExt_nonneg (m₀ := 1) (j := k + 1) (Ω := Set.univ) C]
  · refine ⟨fun θ C => dz θ C + c θ C, fun _ _ => rfl, fun C => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := hdz2 C
    obtain ⟨b1, b2, b3, b4⟩ := hC C
    refine ⟨a1.add b1, fun θ hθ θ' hθ' h => ?_, fun θ hθ => ?_, fun θ hθ => ?_⟩
    · show dz θ C + c θ C = dz θ' C + c θ' C
      rw [a2 θ hθ θ' hθ' h, b2 θ hθ θ' hθ' h]
    · refine (norm_add_le _ _).trans ?_
      have h1 : ‖dz θ C‖ ≤ (2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
          (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * K0 3 3 T.κ0 *
          Real.exp (-T.κ' * dExt C) := by
        refine (a3 θ hθ).trans ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0).trans
          (mul_le_mul_of_nonneg_right hdet (Real.exp_pos _).le))
        nlinarith [dExt_nonneg (m₀ := 1) (j := k + 1) (Ω := Set.univ) C]
      have h2 := b3 θ hθ
      nlinarith
    · have hne : dz θ C + c θ C ≠ 0 := hθ
      by_cases h0 : dz θ C = 0
      · rw [h0, zero_add] at hne
        exact ⟨(b4 θ hne).1, (b4 θ hne).2.1⟩
      · exact a4 θ h0

end Balaban.Inhabited
