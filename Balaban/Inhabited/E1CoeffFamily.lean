/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarkParamCommon
public import Balaban.Inhabited.E1ParamRawLocal
public import Balaban.Fluctuation.GsumActiveParam
public import Balaban.Inhabited.E1ParamFibreValue
public import Balaban.Inhabited.E1CoeffFamilyG
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
analyticity of `θ ↦ c z θ C` on `physV`, locality (equal values at parameters whose raw datum
and source agree on the thickening of `Ŷ(sitesOf C)`), the bound `K₀ e^{-κ' d_Ext(C)}`, and the
support on rooted polymer sets.  `e1CoeffFamily_value_fromTower` carries one more clause, the
identity of the coefficient sum at `(rawOf D′, 0)` with the local energy term `ℰ₁(z)` of the step
with the datum `D′` of the chart with constant field `h₀`; `e1CoeffFamily_fromTower` is its
corollary.
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
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) ∧
      -- the defining properties of the pair of every block
      (∀ b, (∀ (s : DecParams (T.step k hk N₁ ν β p₁).G') (D : BgData (T.step k hk N₁ ν β p₁).G' 2), (∀ P, ‖s P‖ < Real.exp T.κ) →
        InUnionDomainC (T.step k hk N₁ ν β p₁).G' (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) (T.step k hk N₁ ν β p₁).ν D →
        ∀ (φ : (T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) (α : (T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ),
          IsDecBg (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (rho4 3 3 2 T.BG T.κ) s D φ α →
          (F₁ (z, b)) (s, rawOf D) = (φ, α)) ∧
      (∀ p : Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
        StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t))) T.t p.2 →
          ((Sol (z, b)) p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (Dec2.decG (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν p.1) p.2.2.1 p.2.1
            (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Dec2.DecFixed (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) ((Sol (z, b)) p).2 (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) ∧
          Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) ((Sol (z, b)) p).2 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) ∧
          SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) ((Sol (z, b)) p).1 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) ∧
          (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ, Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) →
            Dec2.DecFixed (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol (z, b)) p).2))) := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  have h := e1MarkParam_pairs_fromTowerG T.toG rfl (T.scaleDataG_of_fixed D)
    (by simpa using h3N) hN hν0 (by simpa using hν) hβ (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm (S := T.step k hk N₁ ν β p₁) rfl hp hRU'
  simp only [corrF0_toG]
  exact h

open Classical in
/-- **The sharp premise `hG` of `paramMarked_analytic_local_bound` at the tower.**  For pairs
`(F₁ (z, b), Sol (z, b))` with the defining properties `hspec` (the last clause of
`e1MarkParam_pairs_fromTower`), the marks `e1MarkGParam` of the root `z` at two parameters of
`physV` with equal restrictions of `(raw datum, source)` to `sitesOf C` coincide (for every real
`s ∈ [0, 1]`), at every bridge label whose anchor's site set lies in `Ŷ(sitesOf C)`.  This is
the conclusion of `markedOutDec_decMarkCorrTerm_hG_rawY` for `π θ = physRestrict (sitesOf C)
(physIncl 2 S θ)`, with the cover, margin and rate hypotheses discharged from the data `D` of the
tower. -/
theorem e1Mark_hG_rawY_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < (T.step k hk N₁ ν β p₁).p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁)
    (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
    (hspec : ∀ b, (∀ (s : DecParams (T.step k hk N₁ ν β p₁).G') (D : BgData (T.step k hk N₁ ν β p₁).G' 2), (∀ P, ‖s P‖ < Real.exp T.κ) →
        InUnionDomainC (T.step k hk N₁ ν β p₁).G' (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) (T.step k hk N₁ ν β p₁).ν D →
        ∀ (φ : (T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) (α : (T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ),
          IsDecBg (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (rho4 3 3 2 T.BG T.κ) s D φ α →
          (F₁ (z, b)) (s, rawOf D) = (φ, α)) ∧
      (∀ p : Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
        StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t))) T.t p.2 →
          ((Sol (z, b)) p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (Dec2.decG (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν p.1) p.2.2.1 p.2.1
            (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Dec2.DecFixed (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
          Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) ((Sol (z, b)) p).2 (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) ∧
          Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) ((Sol (z, b)) p).2 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) ∧
          SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) ((Sol (z, b)) p).1 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) ∧
          (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ, Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) →
            Dec2.DecFixed (coverOf (T.step k hk N₁ ν β p₁).G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol (z, b)) p).2)))
    {Lb : Type} (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb) (hN1 : 3 ^ 1 ∣ N₁)
    (C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t,
    ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t,
      physRestrict (N := 2) (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
        physRestrict (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z},
        (commonLabels Lab hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
          (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i) ⊆
          Yhat Set.univ (sitesOf C) →
        (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i (s : ℂ) Φ) =
        (fun Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ' i (s : ℂ) Φ) := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  exact e1Mark_hG_rawY_fromTowerG T.toG rfl (T.scaleDataG_of_fixed D) hN hν0 (by simpa using hν)
    hβ (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm (S := T.step k hk N₁ ν β p₁) rfl hp hRU' F₁ Sol
    z hspec Lab hN1 C

end Fields

section Main

open Classical in
/-- **One energy coefficient family at the tower, with its value on the fibre `h ≡ h₀`.**  Beyond
a threshold `β₀`, at every scale datum there are one family of decoupling pairs `(F₁, Sol)`, a
label system `Lab₀` and an activity `A₀` on the common labels (with its identity for the
interpolation integral at every chart datum), chosen before every root and before every datum, such
that for every root `z` the pairs have the eight clauses, the activity and the marks carry a
`ParamMarkFamily` over `physV`, `ball 0 corrU` and `physCarrier`, and the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParam … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 3 3 T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`;
and, for every datum `D′` of the chart with constant field `h₀`,
(v) the local energy term of the step with the datum `D′` is
`ℰ₁^{(k+1)}(z) = ∑_C c z (rawOf D′, 0) C`. -/
theorem e1CoeffFamily_value_fromTower {κmin : ℝ} (T : StepTower κmin)
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
          ∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
              (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
            XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
              (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
            ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
                (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C := by
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_value_fromTowerG T.toG rfl (stepOutputPhysical T hHull)
    rfl rfl rfl rfl rfl hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  have e : (((3 : ℕ)) : ℝ) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hν0 (by simpa using hν) β hβ p₁
    (by rw [e]; exact hp₁) (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm
    (T.step k hk N₁ ν β p₁) rfl hp
  simp only [corrF0_toG]
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hdat, hz, -⟩ := G
  exact ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hdat, hz⟩

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
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_value_fromTower T hHull hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp hp₁ D => ?_⟩
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ := H k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp hp₁ D
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, -⟩ := hz z
  exact ⟨h1, h2, c, hc, fun C =>
    ⟨(hcl C).1, (hcl C).2.1, (hcl C).2.2.2.1, (hcl C).2.2.2.2⟩⟩

end Main
end Balaban.Inhabited
