/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1LabelsBudgetG
public import Balaban.Inhabited.DecMarkCorrFamilyFromTower
public import Balaban.Inhabited.ActivityFamilyAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The marks of the energy record on the common labels, general tower

General versions of the definitions and theorems of `E1MarksCommon`: `e1MarkGGen` (the mark of the
root `z` at the bridge label `Y′`, with the body of `e1MarkG` at general `d`, `L`, `N`), the
radius facts `e1_markedRad_eqG`, `e1_rad_ltG`, `e1_rad_RR_ltG`, and `e1Marks_common_fromTowerG`.
The cover index is `1` (`T.m₀ = 1`) and the step setting is `hatStepKG … ϱ …` with
`ϱ = rhoSepG d L T.m₁`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

section Marks

variable {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}

open Classical in
/-- **The mark of the root `z` at the bridge label `Y′`**: the rooted corrected output of the
pairs `(F₁, Sol)` at the datum `rawOf S.D'`, for `‖u‖ < (17 / 16 : ℝ)`, and `0` otherwise. -/
noncomputable def e1MarkGGen (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) : ℂ :=
  if ‖u‖ < (17 / 16 : ℝ) then
    markedOutDec 1 (fun _ => Set.univ) (e1DomG S) z
      (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
        (rawOf S.D') u Φ) Y'.1
  else 0

theorem e1MarkGGen_of_lt (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) {u : ℂ}
    (hu : ‖u‖ < (17 / 16 : ℝ)) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGGen S F₁ Sol ρ hp z Y' u Φ =
      markedOutDec 1 (fun _ => Set.univ) (e1DomG S) z
        (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
          (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
          (rawOf S.D') u Φ) Y'.1 := by
  simp [e1MarkGGen, hu]

theorem e1MarkGGen_of_not_lt (S : StepSetting d L N₁ m₁ k N ϱ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) {u : ℂ}
    (hu : ¬ ‖u‖ < (17 / 16 : ℝ)) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGGen S F₁ Sol ρ hp z Y' u Φ = 0 := by
  simp [e1MarkGGen, hu]

end Marks

section Radius

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k)
  {N₁ : ℕ} [NeZero N₁] {ϱ : ℝ} {ν β p₁ : ℝ}

/-- The marked radius of the step is the radius `decMR` of the tower. -/
theorem e1_markedRad_eqG (hβ : 0 < β) :
    markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ T.κ p₁
      ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      decMRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ := by
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have := scalePosG T k
    positivity
  have hbU : (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ _ hk ν β p₁ T.δ
  rw [hbU]
  exact markedRadG_eq T k hb0.le p₁

/-- For `‖u‖ ≤ (17 / 16 : ℝ)` and `2 (17 / 16 : ℝ) ≤ R`, the disc of the marks lies in the radius of the pairs. -/
theorem e1_rad_ltG (hβ : 0 < β) (hp : 0 < p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)
    {u : ℂ} (hu : ‖u‖ ≤ (17 / 16 : ℝ)) :
    (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ T.κ p₁
      ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have := scalePosG T k
    positivity
  rw [e1_markedRad_eqG T hk hβ]
  have h2 := two_corrRG_mul_decMRG_lt T hk hb0 hp
  have hq := decMRG_pos T hk hb0 hp
  have hU := (by norm_num : (0:ℝ) < 17 / 16)
  rw [norm_zero, add_zero]
  nlinarith

/-- The radius `R + R` of the analyticity of the rooted outputs is admissible. -/
theorem e1_rad_RR_ltG (hβ : 0 < β) (hp : 0 < p₁) :
    (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁ + corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) *
      markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ T.κ p₁
        ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have := scalePosG T k
    positivity
  rw [e1_markedRad_eqG T hk hβ]
  have h2 := two_corrRG_mul_decMRG_lt T hk hb0 hp
  linarith

end Radius

section Main

open Classical in
/-- **The marks of the energy record on the common labels.**  One family of pairs `(F₁, Sol)`
(indexed by root and block) such that for every root `z`, with the marks `e1MarkGGen` of the step
`hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ` at the clamp radius `p₁`: the constant `corrF0` is positive, the disc is
open and contains `[0,1]`, the bridge family is nonempty, the marks are measurable in `Φ`, depend
only on the blocks of the common label of their anchor, satisfy the bound
`‖G‖ ≤ corrF0 · exp (−(2 κ_dec − 1) d_l)` for all `u`, `Φ` (for every label system `Lab` on
which the common labels are built), and are differentiable in `u` on the disc. -/
theorem e1Marks_common_fromTower_pairsG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ}
    {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (h3N : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) :
    0 < corrF0G T k β p₁ ∧ IsOpen (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) (17 / 16 : ℝ)) ∧
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 × Fin N → ℂ) × ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
    (∀ z : RootIdx d L N₁ T.m₁ (k + 1), ∀ b,
      MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).hG' ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁ ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)) ∧
      (∀ Y, AnalyticOnNhd ℂ
          (fun p : (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × Fin N → ℂ)) × (ℂ × ℂ) =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).hG' ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν k b) ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockU z) p.2.1 p.2.2 Y p.1)
          ((XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
            {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ T.κ p₁ ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t})) ∧
      (∀ Y, ∀ ψh : unitPts (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
          ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad d L N k (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ T.κ p₁ ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t →
          AnalyticOnNhd ℂ (fun p : physParam N (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) × ℂ => deriv (fun t : ℂ =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).hG' ((((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν k b) ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockU z) p.2 t Y ((p.1.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), ψh)) 0)
            (physV (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).a₁ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).ν T.t ×ˢ Metric.ball (0 : ℂ) a))) ∧
    ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z} ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z})
        (u : ℂ), Measurable (e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)))
            (e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u)) ∧
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}) (u : ℂ) Φ,
          ‖e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u Φ‖ ≤
            corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z})
        Φ, DifferentiableOn ℂ (fun u => e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u Φ) (Metric.ball (0 : ℂ) (17 / 16 : ℝ))) := by
  classical
  subst hϱ
  set SG := hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ with hSG
  have hp' : 0 < SG.p₁ := hp
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  have hXi : XiCData SG.G' SG.a
      SG.ν (k + 1) 1 T.t SG.D' := D.xi
  refine ⟨corrF0G_pos T hk hβ hp, Metric.isOpen_ball, ?_, ?_⟩
  · intro s hs
    rw [mem_ball_zero_iff]
    refine norm_ofReal_lt_of_mem hs ?_
    norm_num
  obtain ⟨F₁, Sol, hF⟩ := markCorrFamily_fromTowerG T hm₀ D hN hν0 hν hβ hp hRU rfl
    (S := SG) rfl hp
  refine ⟨F₁, Sol, fun z b => ?_, fun z => ?_⟩
  · obtain ⟨hP, hJ2, hJ4, -⟩ := hF z
    exact ⟨hP b, hJ2 b, hJ4 b⟩
  obtain ⟨hP, hJ2, hJ4, hcnt, -⟩ := hF z
  have hΘ : rawOf SG.D' ∈ XiCRaw SG.G'
      (compWeight L SG.a₁) SG.ν (k + 1) 1 T.t :=
    ⟨_, hXi, rfl⟩
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
  have hout := markedOutDecCorr_fields SG SG.hG' T.hd hdvd1 hcov hopt z
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) hP hJ2 hJ4 (ρ := p₁) hp le_rfl hp' T.t_pos
    (((SG.β : ℝ)) : ℂ)
  obtain ⟨hmeas, hdep, hhol⟩ := hout
  have hmeasG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1DomG SG) z}) (u : ℂ),
      Measurable (e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z i u) := by
    intro i u
    by_cases hu : ‖u‖ < (17 / 16 : ℝ)
    · have e : e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z i u = _ := funext fun Φ => e1MarkGGen_of_lt _ _ _ _ hp z i hu Φ
      rw [e]
      exact hmeas i.1 _ hΘ u (e1_rad_ltG T hk hβ hp hRU hu.le)
    · have e : e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z i u = fun _ => 0 := funext fun Φ => e1MarkGGen_of_not_lt _ _ _ _ hp z i hu Φ
      rw [e]
      exact measurable_const
  have hdepG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1DomG SG) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i u) := by
    intro i u
    by_cases hu : ‖u‖ < (17 / 16 : ℝ)
    · have e : e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z i u = _ := funext fun Φ => e1MarkGGen_of_lt _ _ _ _ hp z i hu Φ
      rw [e]
      exact hdep i.1 i.2 _ hΘ u (e1_rad_ltG T hk hβ hp hRU hu.le)
    · intro Φ Φ' _
      rw [e1MarkGGen_of_not_lt _ _ _ _ hp z i hu Φ, e1MarkGGen_of_not_lt _ _ _ _ hp z i hu Φ']
  have hbdG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1DomG SG) z}) (u : ℂ) Φ,
      ‖e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i u Φ‖ ≤
        corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) i.1) := by
    intro i u Φ
    by_cases hu : ‖u‖ < (17 / 16 : ℝ)
    · rw [e1MarkGGen_of_lt _ _ _ _ hp z i hu Φ]
      exact (hcnt _ hΘ u hu.le Φ).1 i.1
    · rw [e1MarkGGen_of_not_lt _ _ _ _ hp z i hu Φ, norm_zero]
      have := corrF0G_pos T hk hβ hp
      positivity
  refine ⟨?_, hmeasG, fun Lb _ Lab => ?_, ?_⟩
  · obtain ⟨Y, hY⟩ := e1DomG_bridgeFamily_nonempty T hm₀ D rfl z
    exact ⟨⟨Y, hY⟩⟩
  · obtain ⟨h1, h2⟩ := commonAnchor_marks_fields (Lab := Lab)
      (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega) (fun _ => Set.univ)
      (e1DomG SG) (e1DomG_isDj T hm₀ D rfl) z (ι := {Y' // Y' ∈ bridgeFamily 1
        (fun _ => Set.univ) (e1DomG SG) z}) id (fun _ => corrF0G T k β p₁)
      (2 * T.κdec - 1)
      (fun i u => e1MarkGGen SG (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z i u) hdepG hbdG
    exact ⟨h1, h2⟩
  · intro i Φ
    have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
      have := scalePosG T k
      positivity
    have hR := corrRG_pos T hk hb0 hp
    have hU := (by norm_num : (0:ℝ) < 17 / 16)
    have he₀ : ((⟨rawOf SG.D', rawOf_mem_rawSub _⟩ :
        rawSub N SG.G'),
        (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) ∈
        physV SG SG.a₁ SG.ν T.t :=
      (mk_mem_physFibre SG SG.hh₀ hXi (g := 0)
        (by simp)).1
    have han := hhol i.1 Φ (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) (corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) hR hR
      (e1_rad_RR_ltG T hk hβ hp)
    have hd := (han.differentiableOn).comp (f := fun u : ℂ => ((⟨⟨rawOf SG.D',
        rawOf_mem_rawSub _⟩, (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)⟩ :
        physParam N SG), u))
      (s := Metric.ball (0 : ℂ) (17 / 16 : ℝ))
      (differentiableOn_const _ |>.prodMk differentiableOn_id) ?_
    · refine hd.congr fun u hu => ?_
      exact e1MarkGGen_of_lt _ _ _ _ hp z i (mem_ball_zero_iff.1 hu) Φ
    · intro u hu
      refine ⟨he₀, ?_⟩
      rw [mem_ball_zero_iff] at hu ⊢
      linarith

/-- **The marks of the energy record on the common labels.**  One family of pairs `(F₁, Sol)`
(indexed by root and block) such that for every root `z`, with the marks `e1MarkGGen` of the step
`hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ` at the clamp radius `p₁`: the constant `corrF0` is positive, the disc is
open and contains `[0,1]`, the bridge family is nonempty, the marks are measurable in `Φ`, depend
only on the blocks of the common label of their anchor, satisfy the bound
`‖G‖ ≤ corrF0 · exp (−(2 κ_dec − 1) d_l)` for all `u`, `Φ` (for every label system `Lab` on
which the common labels are built), and are differentiable in `u` on the disc. -/
theorem e1Marks_common_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ}
    {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    (h3N : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁) (hRU : 2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) :
    0 < corrF0G T k β p₁ ∧ IsOpen (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) (17 / 16 : ℝ)) ∧
    ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        DecParams (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 × Fin N → ℂ) × ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G'.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
    ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z} ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z})
        (u : ℂ), Measurable (e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)))
            (e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u)) ∧
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z}) (u : ℂ) Φ,
          ‖e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u Φ‖ ≤
            corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (e1DomG_isDj T hm₀ D hϱ)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z})
        Φ, DifferentiableOn ℂ (fun u => e1MarkGGen (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u Φ) (Metric.ball (0 : ℂ) (17 / 16 : ℝ))) := by
  obtain ⟨h1, h2, h3, F₁, Sol, -, h⟩ := e1Marks_common_fromTower_pairsG T hm₀ D h3N hN hν0 hν hβ hp hRU hϱ
  exact ⟨h1, h2, h3, F₁, Sol, h⟩

end Main

end Balaban.Inhabited
