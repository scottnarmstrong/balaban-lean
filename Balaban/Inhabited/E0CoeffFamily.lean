/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1CoeffFamily
public import Balaban.Inhabited.E0CoeffFamilyG
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

`e0CoeffFamily_value_fromTower` adds this to the mark coefficient of
`e1CoeffFamily_value_fromTower` (`e0CoeffFamily_fromTower` is its corollary): at a scale
of the tower, for every root `z`, the determinant term and the sum `e0 = dz + c` carry the same four
properties (analyticity, locality, the bound `(2 · 27 · BL + 1) K₀ e^{-κ' d_Ext}`, polymer support),
and the determinant half of the value at every datum of the chart is proved:
`-½ ∑_{y ∈ B(z)} tr 𝕃(y,y) = ∑_T dz(θ') T` and `ℰ₀ = ∑_T dz(θ') T + ℰ₁`. The value
clause is `ℰ₀ = ∑_T e0 (rawOf D′, 0) T` at every datum `D′` of the chart with constant field `h₀`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

/-- The numerical facts about the determinant constant of the tower used in the sum:
`27 BL ≥ 0`, and `27 BL ≤ 2 · 27 · BL · K₀`. -/
theorem towerDetConst_le_mul {κmin : ℝ} (T : StepTower κmin) :
    0 ≤ 27 * covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) ∧
      27 * covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) ≤
      2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) * K0 3 3 T.κ0 := by
  have h0 := T.toG.detConst_nonneg
  have h1 := T.toG.detConst_le_mul
  have e : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) =
      27 * covBLogMax 3 3 T.κ / (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) := by
    push_cast; ring
  have e2 : (27 : ℝ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) =
      27 * (covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) := by ring
  simp only [StepTower.toG_κ, StepTower.toG_κ0] at h0 h1
  rw [e] at h0 h1
  refine ⟨h0, ?_⟩
  rw [e2] at h1 ⊢
  refine h1.trans (le_of_eq ?_)
  push_cast; ring

open Classical in
/-- **The energy coefficient family at the tower with its value on the fibre `h ≡ h₀`.**  See the
module doc-string.  The first part is `e1CoeffFamily_value_fromTower`; then the determinant
function `dz` (with the determinant half of the value at every datum of the chart) and the sum
`e0 = dz + c`, whose coefficient sum at `(rawOf D′, 0)` is the local energy term `ℰ₀^{(k+1)}(z)`
of the step with the datum `D′`, for every datum `D′` of the chart with constant field `h₀`. -/
theorem e0CoeffFamily_value_fromTower {κmin : ℝ} (T : StepTower κmin)
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
              ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              physRestrict (N := 2) (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
                c θ C = c θ' C) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ‖c θ C‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
              (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
            XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
              (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
            ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
                (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C) ∧
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
            (∀ θ, e0 θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
              ∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
                (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
              XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
                (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
              ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
                  (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
                ∑ C, e0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                  (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C := by
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTowerG T.toG rfl (stepOutputPhysical T hHull)
    rfl rfl rfl rfl rfl hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  have e : (((3 : ℕ)) : ℝ) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have e27 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) =
      27 * (covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) := by
    push_cast; ring
  have G := H k hk N₁ (by simpa using h3N) hN ν hν0 (by simpa using hν) β hβ p₁
    (by rw [e]; exact hp₁) (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm
    (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ := G
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, hcv, dz, hdz, hdzl, e0, he, hel, hev⟩ := hz z
  refine ⟨h1, by simp only [corrF0_toG]; exact h2, c, hc, hcl, hcv, dz, hdz, fun C => ?_, e0, he, fun C => ?_, hev⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hdzl C
    refine ⟨a1, a2, fun θ hθ => ?_, a4⟩
    have := a3 θ hθ
    simp only [StepTower.toG_κ, StepTower.toG_κ'] at this
    rw [e27] at this
    convert this using 3
    all_goals rfl
  · obtain ⟨a1, a2, a3, a4⟩ := hel C
    refine ⟨a1, a2, fun θ hθ => ?_, a4⟩
    have := a3 θ hθ
    simp only [StepTower.toG_κ, StepTower.toG_κ'] at this
    rw [e27] at this
    convert this using 3
    all_goals first | rfl | ring

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
  classical
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTower T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp hp₁ D => ?_⟩
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ := H k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp hp₁ D
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, -, dz, hdz, hdzl, e0, he, hel, -⟩ := hz z
  exact ⟨h1, h2, c, hc,
    (fun C => ⟨(hcl C).1, (hcl C).2.1, (hcl C).2.2.2.1, (hcl C).2.2.2.2⟩),
    dz, hdz, hdzl, e0, he, hel⟩

end Balaban.Inhabited
