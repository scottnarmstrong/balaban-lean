/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarksCommon
public import Balaban.Fluctuation.ParamCarrierLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The marks of the energy record as the marks of a parameter family, general tower

General versions of the definitions and theorems of `E1MarkParamCommon`: `e1MarkGParamG` (the mark
of the root `z` at the bridge label `Y′` as a function of the parameter `θ`, with the body of
`e1MarkGParam` at general `d`, `L`, `N`), `e1MarkParam_fields_fromTowerG` and
`e1MarkParamFamily_fromTowerG`.  The cover index is `1` (`T.m₀ = 1`); the step setting is
`hatStepKG … ϱ …` with `ϱ = rhoSepG d L T.m₁`.  The continuity of the rooted output in the
configuration (`continuous_markedOutDec_decMarkCorrTerm`) lives here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

section Def

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

open Classical in
/-- **The mark of the root `z` at the bridge label `Y′` as a function of the parameter `θ`**: the
rooted corrected output of the pairs `(F₁, Sol)` at the raw datum of `θ`, when this datum lies in
the chart `XiCRaw … eps` and `‖u‖ < (17 / 16 : ℝ)`, and `0` otherwise. -/
noncomputable def e1MarkGParamG (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1)) (eps : ℝ) (θ : physParam N S)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) : ℂ :=
  if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < (17 / 16 : ℝ) then
    markedOutDec 1 (fun _ => Set.univ) (e1DomG S) z
      (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) u Φ) Y'.1
  else 0

variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
  (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
  (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1)) (eps : ℝ) (θ : physParam N S)
  (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
  (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b)

theorem e1MarkGParamG_of_mem
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps) (hu : ‖u‖ < (17 / 16 : ℝ)) :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ Y' u Φ =
      markedOutDec 1 (fun _ => Set.univ) (e1DomG S) z
        (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
          (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) u Φ) Y'.1 := by
  simp [e1MarkGParamG, hθ, hu]

theorem e1MarkGParamG_of_not (h : ¬ ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < (17 / 16 : ℝ))) :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ Y' u Φ = 0 := by
  simp [e1MarkGParamG, h]

/-- **At the raw datum of the step** the mark of the parameter family is the landed `e1MarkG`. -/
theorem e1MarkGParamG_eq_e1MarkG
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf S.D')
    (hΘ : rawOf S.D' ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps) :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ Y' u Φ = e1MarkGGen S F₁ Sol ρ hp z Y' u Φ := by
  unfold e1MarkGParamG e1MarkGGen
  rw [hθ]
  simp only [hΘ, true_and]

end Def

section Rooted

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν cψ : ℝ} {m₀ : ℕ} {cc : ℂ} {Zm : Finset (unitPts S.G')}
variable {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- The rooted output of the corrected marks is continuous in the configuration when each block
term is. -/
theorem continuous_markedOutDec_decMarkCorrTerm
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (β : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (um : ℂ)
    (zr : RootIdx d L N₁ m₁ (k + 1)) (Y' : Set (CTorus d L N₁ m₁ (k + 1)))
    (hc : ∀ b, ∀ Y, Continuous (decMarkCorr S (X₁V b) m₀ (jV b) (𝒦XV b) a₁ ν cc (F₁ b) (Sol b)
      (blockEnergyFun S.G' Hm (compWeight L a₁) ν k b) Zm Y ρ hp Θ um)) :
    Continuous (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
        (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y') := by
  have e : (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        markedOutDec m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr
          (decMarkCorrTerm S X₁V jV 𝒦XV m₀ a₁ ν cc F₁ Sol Zm ρ hp β Θ um Φ) Y') =
        fun Φ => ∑ q ∈ (markedIdx (fun _ => Set.univ)
          (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) zr).filter
            (fun q => bridge m₀ zr q.2 = Y'),
          -β * decMarkCorr S (X₁V q.1) m₀ (jV q.1) (𝒦XV q.1) a₁ ν cc (F₁ q.1) (Sol q.1)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k q.1) Zm q.2 ρ hp Θ um Φ :=
    funext fun Φ => markedOutDec_decMarkCorrTerm_eq S F₁ Sol ρ hp β Θ um Φ zr Y'
  rw [e]
  exact continuous_finsetSum _ fun q _ => continuous_const.mul (hc q.1 q.2)

end Rooted

section Main

open Classical in
/-- **The mark hypotheses of the parameter family, for every root.**  One family of pairs
`(F₁, Sol)` (indexed by root and block, chosen before every parameter) such that for every root
`z`, with the marks `e1MarkGParamG` of the step `hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ` at the chart radius `T.t`
and the clamp radius `p₁`: the bridge family is nonempty, the marks are measurable in `Φ` and, for
every label system `Lab` on which the common labels are built, bounded by
`corrF0 · exp (−(2 κ_dec − 1) d_l)` at the anchor, for all parameters, `u` and `Φ`; they are jointly
analytic in `(θ, u)` on `physV × ball 0 (17 / 16 : ℝ)` for every `Φ`; continuous in `Φ` on the carrier for
`θ ∈ physV`, `u ∈ ball 0 (17 / 16 : ℝ)`; and, for `θ ∈ physV`, depend only on the blocks of the common label
of their anchor. -/
theorem e1MarkParam_fields_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ}
    {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (h3N : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    (hp : 0 < (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) :
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 × Fin N → ℂ) × ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
    ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z} ∧
      (∀ (θ : physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
        (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z})
        (u : ℂ), Measurable (e1MarkGParamG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ θ ∈ physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
            (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t,
          ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)))
            (e1MarkGParamG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
              z T.t θ i u)) ∧
        (∀ (θ : physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ))
            (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}) (u : ℂ) Φ,
          ‖e1MarkGParamG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              T.t θ i u Φ‖ ≤
            corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z})
        (Φ : ∀ b, ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit 1 hp).Ωb b),
        AnalyticOnNhd ℂ (fun p : physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) × ℂ =>
          e1MarkGParamG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
            T.t p.1 i p.2 Φ)
          (physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t
            ×ˢ Metric.ball (0 : ℂ) (17 / 16 : ℝ))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}),
        ∀ θ ∈ physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁
            (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t,
        ∀ u ∈ Metric.ball (0 : ℂ) (17 / 16 : ℝ),
          ContinuousOn (e1MarkGParamG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u) (physCarrier (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) 1 hp)) := by
  classical
  subst hϱ
  set SG := hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ with hSG
  have hp' : 0 < SG.p₁ := hp
  have hp0 : 0 < p₁ := hp
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  have hcov : ∀ b, CovSetup SG.G' 1 k
      (LocalCover.cube 1 k (LocalCover.blockSite k b))
      (LocalCover.fam 1 (LocalCover.blockSite k b)) := fun b => (hV b).1
  have hopt : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube 1 k (LocalCover.blockSite k b)) ∧
        MeetsOne 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) W₀ ∧
        bondCost (scaleW L 1 T.m₁ k) E₀ =
          treeLenCovOne 1 k (LocalCover.cube 1 k (LocalCover.blockSite k b)) :=
    fun b => (hV b).2.2.1
  have hdvd1 : L ^ 1 ∣ N₁ := by rwa [hm₀] at h3N
  obtain ⟨F₁, Sol, hF⟩ := markCorrFamily_fromTowerG T hm₀ D hN hν0 hν hβ hp0 hRU rfl
    (S := SG) rfl hp
  refine ⟨F₁, Sol, fun z => ?_⟩
  obtain ⟨hP, hJ2, hJ4, hcnt, hblk⟩ := hF z
  have hout := markedOutDecCorr_fields SG SG.hG'
    T.hd hdvd1 hcov hopt z
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) hP hJ2 hJ4 (ρ := p₁) hp le_rfl hp' T.t_pos
    ((SG.β : ℝ) : ℂ)
  obtain ⟨hmeas, hdep, hhol⟩ := hout
  have hF0 := corrF0G_pos T hk hβ hp0
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have := scalePosG T k
    positivity
  have hR := corrRG_pos T hk hb0 hp0
  have hU := (by norm_num : (0:ℝ) < 17 / 16)
  have hdepG : ∀ θ ∈ physV SG SG.a₁
        SG.ν T.t,
      ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1DomG SG) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp
          z T.t θ i u) := by
    intro θ hθ i u
    by_cases hu : ‖u‖ < (17 / 16 : ℝ)
    · have e : e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
        funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hθ.1 hu
      rw [e]
      exact hdep i.1 i.2 _ hθ.1 u (e1_rad_ltG T hk hβ hp0 hRU hu.le)
    · intro Φ Φ' _
      rw [e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ fun h => hu h.2,
        e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ' fun h => hu h.2]
  have hbdG : ∀ (θ : physParam N SG)
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1DomG SG) z}) (u : ℂ) Φ,
      ‖e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
        T.t θ i u Φ‖ ≤
        corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) i.1) := by
    intro θ i u Φ
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
        XiCRaw SG.G' (compWeight L SG.a₁)
          SG.ν (k + 1) 1 T.t ∧ ‖u‖ < (17 / 16 : ℝ)
    · rw [e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2]
      exact (hcnt _ hc.1 u hc.2.le Φ).1 i.1
    · rw [e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ hc, norm_zero]
      positivity
  have hmeasG : ∀ (θ : physParam N SG)
      (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
        (e1DomG SG) z}) (u : ℂ),
      Measurable (e1MarkGParamG SG (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u) := by
    intro θ i u
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
        XiCRaw SG.G' (compWeight L SG.a₁)
          SG.ν (k + 1) 1 T.t ∧ ‖u‖ < (17 / 16 : ℝ)
    · have e : e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
        funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hc.1 hc.2
      rw [e]
      exact hmeas i.1 _ hc.1 u (e1_rad_ltG T hk hβ hp0 hRU hc.2.le)
    · have e : e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = fun _ => 0 :=
        funext fun Φ => e1MarkGParamG_of_not _ _ _ _ hp z T.t θ i u Φ hc
      rw [e]
      exact measurable_const
  have hopen : IsOpen (physV SG SG.a₁
      SG.ν T.t) :=
    isOpen_physV _ _ _ _ (bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν)
  refine ⟨?_, hmeasG, fun Lb _ Lab => ⟨fun θ hθ => ?_, fun θ i u Φ => ?_⟩, ?_, ?_⟩
  · obtain ⟨Y, hY⟩ := e1DomG_bridgeFamily_nonempty T hm₀ D rfl z
    exact ⟨⟨Y, hY⟩⟩
  · exact (commonAnchor_marks_fields (Lab := Lab)
      (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega) (fun _ => Set.univ)
      (e1DomG SG) ((e1DomG_isDj T hm₀ D rfl)) z (ι := {Y' // Y' ∈ bridgeFamily 1
        (fun _ => Set.univ) (e1DomG SG) z}) id (fun _ => corrF0G T k β p₁)
      (2 * T.κdec - 1)
      (fun i u => e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z T.t θ i u) (hdepG θ hθ) (hbdG θ)).1
  · exact hbdG θ i u Φ
  · intro i Φ
    have han := hhol i.1 Φ (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) hR hR
      (e1_rad_RR_ltG T hk hβ hp0)
    have hmono := han.mono (Set.prod_mono (subset_refl _)
      (Metric.ball_subset_ball (by linarith : (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)))
    refine hmono.congr (hopen.prod Metric.isOpen_ball) fun p hp'' => ?_
    exact (e1MarkGParamG_of_mem _ _ _ _ hp z T.t p.1 i p.2 Φ hp''.1.1
      (mem_ball_zero_iff.1 hp''.2)).symm
  · intro i θ hθ u hu
    have hu' : ‖u‖ < (17 / 16 : ℝ) := mem_ball_zero_iff.1 hu
    have e : e1MarkGParamG SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z T.t θ i u = _ :=
      funext fun Φ => e1MarkGParamG_of_mem _ _ _ _ hp z T.t θ i u Φ hθ.1 hu'
    rw [e]
    refine (continuous_markedOutDec_decMarkCorrTerm SG _ _ p₁ hp _ _ _ z
      i.1 fun b Y => ?_).continuousOn
    exact ((hblk b).2.1 Y _ hθ.1 u (e1_rad_ltG T hk hβ hp0 hRU hu'.le)).1

open Classical in
/-- **The `ParamMarkFamily` of the marks of the energy record on the common labels.**  One family
of pairs `(F₁, Sol)`, chosen before every parameter, such that for every root `z`, every label
system `Lab₀` and every activity `A₀` on the common labels that carries a `ParamMarkFamily` without
marks over `physV`, `ball 0 2` and `physCarrier` (the form returned by
`zeroSourceActivity_common_fromTower`), the activity `A₀` together with the marks `e1MarkGParamG`
anchored at the bridge labels of `z` form a `ParamMarkFamily` over `physV`, `ball 0 (17 / 16 : ℝ)` and the
same carrier, with `κ_G = 2 κ_dec − 1` and `F₀ = corrF0`. -/
theorem e1MarkParamFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ}
    {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (h3N : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    (hp : 0 < (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) :
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 × Fin N → ℂ) × ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
    ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
    ∀ (Lb : Type) [Fintype Lb]
      (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ Lb) {εH κH κ0 Kc : ℝ}
      (A₀ : physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) → ℂ →
        LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
          (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ))
          ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit 1 hp).Ωb εH κH κ0 Kc),
      Nonempty (ParamMarkFamily ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit 1 hp).μ
        (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
          (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)) A₀
        (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
        (physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t)
        (Metric.ball (0 : ℂ) 2) (physCarrier (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) 1 hp)) →
      Nonempty (ParamMarkFamily ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit 1 hp).μ
        (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
          (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)) A₀
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z} =>
          commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)
        (fun θ i u Φ => e1MarkGParamG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
        (2 * T.κdec - 1) (fun _ => corrF0G T k β p₁)
        (physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t)
        (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) (physCarrier (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) 1 hp)) := by
  obtain ⟨F₁, Sol, hF⟩ := e1MarkParam_fields_fromTowerG T hm₀ D h3N hN hν0 hν hβ hϱ hp hRU
  refine ⟨F₁, Sol, fun z Lb _ Lab₀ εH κH κ0 Kc A₀ ⟨hA⟩ => ?_⟩
  obtain ⟨-, hmeas, hdb, hholG, hcontG⟩ := hF z
  have hle : (17 / 16 : ℝ) ≤ 2 := by norm_num
  exact ⟨{ isOpenV := hA.isOpenV
           isOpenU := Metric.isOpen_ball
           seg := fun s hs => by
             rw [mem_ball_zero_iff]
             refine norm_ofReal_lt_of_mem hs ?_
             norm_num
           compact := hA.compact
           measQ := hA.measQ
           carried := hA.carried
           meas := hmeas
           bound := (hdb Lb Lab₀).2
           holA := fun y Φ hΦ => (hA.holA y Φ hΦ).mono
             (Set.prod_mono (subset_refl _) (Metric.ball_subset_ball hle))
           holG := fun i Φ _ => hholG i Φ
           contA := fun y θ hθ u hu => hA.contA y θ hθ u (Metric.ball_subset_ball hle hu)
           contG := fun i θ hθ u hu => hcontG i θ hθ u hu }⟩

end Main

end Balaban.Inhabited
