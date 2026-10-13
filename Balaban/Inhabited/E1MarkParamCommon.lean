/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarksCommon
public import Balaban.Inhabited.E1MarkParamCommonG
public import Balaban.Inhabited.ZeroSourceActivityCommon
public import Balaban.Fluctuation.ParamCarrierLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The marks of the energy record as the marks of a parameter family

`e1MarkG` lands the marks at the datum of the step.  For the renormalized step the energy
coefficients are an analytic family in the datum, so the marks are needed as a family over the
parameter `θ` of the physical parameter space (the raw datum and the source).

`e1MarkGParam` is the rooted corrected output of one family of decoupling pairs at the raw datum of
`θ`, cut off to zero outside the chart `XiCRaw … eps` and outside the disc `‖u‖ < corrU`.  The
family of pairs is chosen once, before every parameter (`markCorrFamily_fromTower`).

* `e1MarkGParam_eq_e1MarkG`: at the raw datum of the step it is the landed `e1MarkG`.
* `e1MarkParam_fields_fromTower`: for every root, the hypotheses of the marks of a parameter family
  in their exact shapes: measurability and the bound for every parameter, analyticity in `(θ, u)` on
  `physV × ball 0 corrU`, continuity in the configuration on the carrier, block locality.
* `e1MarkParamFamily_fromTower`: the `ParamMarkFamily` on the common labels, from the family of the
  zero-source activity without marks.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

section Def

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ ϱm : ℝ}

open Classical in
/-- **The mark of the root `z` at the bridge label `Y′` as a function of the parameter `θ`**: the
rooted corrected output of the pairs `(F₁, Sol)` at the raw datum of `θ`, when this datum lies in
the chart `XiCRaw … eps` and `‖u‖ < corrU`, and `0` otherwise. -/
noncomputable def e1MarkGParam (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
    {Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm}
    (F₁ : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm 2 → (Hm.Ω 1 × Fin 2 → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ m₁ (k + 1)) (eps : ℝ) (θ : physParam 2 S)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) : ℂ :=
  if (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
      XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU then
    markedOutDec 1 (fun _ => Set.univ) (e1Dom S) z
      (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
        (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) u Φ) Y'.1
  else 0

variable (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) {Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm}
  (F₁ : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
  (Sol : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm 2 → (Hm.Ω 1 × Fin 2 → ℂ) × (Hm.Ω 1 → ℂ))
  (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ m₁ (k + 1)) (eps : ℝ) (θ : physParam 2 S)
  (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ)
  (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b)

theorem e1MarkGParam_of_mem
    (hθ : (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
      XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps) (hu : ‖u‖ < corrU) :
    e1MarkGParam S F₁ Sol ρ hp z eps θ Y' u Φ =
      markedOutDec 1 (fun _ => Set.univ) (e1Dom S) z
        (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
          (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
          (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) u Φ) Y'.1 := by
  simp [e1MarkGParam, hθ, hu]

theorem e1MarkGParam_of_not (h : ¬ ((θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
      XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < corrU)) :
    e1MarkGParam S F₁ Sol ρ hp z eps θ Y' u Φ = 0 := by
  simp [e1MarkGParam, h]

/-- **At the raw datum of the step** the mark of the parameter family is the landed `e1MarkG`. -/
theorem e1MarkGParam_eq_e1MarkG
    (hθ : (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) = rawOf S.D')
    (hΘ : rawOf S.D' ∈ XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 eps) :
    e1MarkGParam S F₁ Sol ρ hp z eps θ Y' u Φ = e1MarkG S F₁ Sol ρ hp z Y' u Φ := by
  unfold e1MarkGParam e1MarkG
  rw [hθ]
  simp only [hΘ, true_and]

/-- The general mark `e1MarkGParamG` at `d = L = 3`, `N = 2` is the fixed mark `e1MarkGParam`. -/
theorem e1MarkGParamG_three :
    e1MarkGParamG S F₁ Sol ρ hp z eps θ Y' u Φ = e1MarkGParam S F₁ Sol ρ hp z eps θ Y' u Φ := rfl

end Def

section Main

open Classical in
/-- **The mark hypotheses of the parameter family, for every root.**  One family of pairs
`(F₁, Sol)` (indexed by root and block, chosen before every parameter) such that for every root
`z`, with the marks `e1MarkGParam` of the step `T.step k hk N₁ ν β p₁` at the chart radius `T.t`
and the clamp radius `p₁`: the bridge family is nonempty, the marks are measurable in `Φ` and, for
every label system `Lab` on which the common labels are built, bounded by
`corrF0 · exp (−(2 κ_dec − 1) d_l)` at the anchor, for all parameters, `u` and `Φ`; they are jointly
analytic in `(θ, u)` on `physV × ball 0 corrU` for every `Φ`; continuous in `Φ` on the carrier for
`θ ∈ physV`, `u ∈ ball 0 corrU`; and, for `θ ∈ physV`, depend only on the blocks of the common label
of their anchor. -/
theorem e1MarkParam_fields_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
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
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z} ∧
      (∀ (θ : physParam 2 (T.step k hk N₁ ν β p₁))
        (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        (u : ℂ), Measurable (e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t,
          ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
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
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  have h := e1MarkParam_fields_fromTowerG T.toG rfl (T.scaleDataG_of_fixed D)
    (by simpa using h3N) hN hν0 (by simpa using hν) hβ (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm
    hp hRU'
  simp only [corrF0_toG]
  exact h

open Classical in
/-- **The `ParamMarkFamily` of the marks of the energy record on the common labels.**  One family
of pairs `(F₁, Sol)`, chosen before every parameter, such that for every root `z`, every label
system `Lab₀` and every activity `A₀` on the common labels that carries a `ParamMarkFamily` without
marks over `physV`, `ball 0 2` and `physCarrier` (the form returned by
`zeroSourceActivity_common_fromTower`), the activity `A₀` together with the marks `e1MarkGParam`
anchored at the bridge labels of `z` form a `ParamMarkFamily` over `physV`, `ball 0 corrU` and the
same carrier, with `κ_G = 2 κ_dec − 1` and `F₀ = corrF0`. -/
theorem e1MarkParamFamily_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
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
    ∀ (Lb : Type) [Fintype Lb]
      (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
        Set.univ Lb) {εH κH κ0 Kc : ℝ}
      (A₀ : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ →
        LabelAct (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
          (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D))
          ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εH κH κ0 Kc),
      Nonempty (ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
        (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
          (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A₀
        (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
        (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t)
        (Metric.ball (0 : ℂ) 2) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) →
      Nonempty (ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
        (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
          (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A₀
        (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
            (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
          commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
        (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
        (2 * T.κdec - 1) (fun _ => corrF0 T k β p₁)
        (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t)
        (Metric.ball (0 : ℂ) corrU) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  have h := e1MarkParamFamily_fromTowerG T.toG rfl (T.scaleDataG_of_fixed D)
    (by simpa using h3N) hN hν0 (by simpa using hν) hβ (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm
    hp hRU'
  simp only [corrF0_toG]
  exact h

end Main

end Balaban.Inhabited
