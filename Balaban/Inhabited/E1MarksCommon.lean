/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1LabelsBudget
public import Balaban.Inhabited.E1MarksCommonG
public import Balaban.Inhabited.DecMarkCorrFamilyFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The marks of the energy record on the common labels

For a root `z` of the renormalization step at a scale of the shared tower, the marks of the energy
record are the rooted corrected outputs `O_z(u, Φ, Y′)` of one family of decoupling pairs, indexed
by the bridge family of `z`, cut off to zero outside the disc `‖u‖ < corrU` (`e1MarkG`).

`e1Marks_common_fromTower` gives one family of pairs and, for every root, the fields of the marks
record in the shapes of `InterpMarks`: the index type is nonempty (and finite, by the instance of
the finite subtype), the disc is open and contains `[0,1]`, the constant `corrF0` is positive, the
marks are measurable in `Φ`, depend only on the blocks of the common label of the anchor, are
bounded by `corrF0 · exp (−κ_G d_l)` for all `u` and `Φ`, with `κ_G = 2 κ_dec − 1`, and are
differentiable in `u` on the disc.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set

section Marks

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ ϱm : ℝ}

open Classical in
/-- **The mark of the root `z` at the bridge label `Y′`**: the rooted corrected output of the
pairs `(F₁, Sol)` at the datum `rawOf S.D'`, for `‖u‖ < corrU`, and `0` otherwise. -/
noncomputable def e1MarkG (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
    {Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm}
    (F₁ : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm 2 → (Hm.Ω 1 × Fin 2 → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) : ℂ :=
  if ‖u‖ < corrU then
    markedOutDec 1 (fun _ => Set.univ) (e1Dom S) z
      (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
        (rawOf S.D') u Φ) Y'.1
  else 0

theorem e1MarkG_of_lt (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
    {Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm}
    (F₁ : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm 2 → (Hm.Ω 1 × Fin 2 → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) {u : ℂ}
    (hu : ‖u‖ < corrU) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkG S F₁ Sol ρ hp z Y' u Φ =
      markedOutDec 1 (fun _ => Set.univ) (e1Dom S) z
        (decMarkCorrTerm S (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
          (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 S.a₁ S.ν
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol (S.blockU z) ρ hp (S.β : ℂ)
          (rawOf S.D') u Φ) Y'.1 := by
  simp [e1MarkG, hu]

theorem e1MarkG_of_not_lt (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
    {Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm}
    (F₁ : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm 2 → (Hm.Ω 1 × Fin 2 → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) {u : ℂ}
    (hu : ¬ ‖u‖ < corrU) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkG S F₁ Sol ρ hp z Y' u Φ = 0 := by
  simp [e1MarkG, hu]

/-- The general mark `e1MarkGGen` at `d = L = 3`, `N = 2` is the fixed mark `e1MarkG`. -/
theorem e1MarkGGen_three (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
    {Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm}
    (F₁ : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
        (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat Hm 2 → (Hm.Ω 1 × Fin 2 → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx 3 3 N₁ m₁ (k + 1))
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b) :
    e1MarkGGen S F₁ Sol ρ hp z Y' u Φ = e1MarkG S F₁ Sol ρ hp z Y' u Φ := rfl

end Marks

section Radius

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- The marked radius of the step is the radius `decMR` of the tower. -/
theorem e1_markedRad_eq (hβ : 0 < β) :
    markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      decMR T k (β * 3 ^ k) p₁ := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  rw [decMR_toG, ← hb]
  exact e1_markedRad_eqG T.toG hk hβ (ϱ := rhoSep T.m₁)

/-- For `‖u‖ ≤ corrU` and `2 corrU ≤ R`, the disc of the marks lies in the radius of the pairs. -/
theorem e1_rad_lt (hβ : 0 < β) (hp : 0 < p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁)
    {u : ℂ} (hu : ‖u‖ ≤ corrU) :
    (‖u‖ + ‖(0 : ℂ)‖) * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  exact e1_rad_ltG T.toG hk hβ hp hRU' hu (ϱ := rhoSep T.m₁)

/-- The radius `R + R` of the analyticity of the rooted outputs is admissible. -/
theorem e1_rad_RR_lt (hβ : 0 < β) (hp : 0 < p₁) :
    (corrR T k (β * 3 ^ k) p₁ + corrR T k (β * 3 ^ k) p₁) *
      markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := e1_rad_RR_ltG T.toG hk hβ hp (ϱ := rhoSep T.m₁) (N₁ := N₁) (ν := ν)
  rw [hb, ← corrR_toG] at h
  exact h

end Radius

section Main

open Classical in
/-- **The marks of the energy record on the common labels.**  One family of pairs `(F₁, Sol)`
(indexed by root and block) such that for every root `z`, with the marks `e1MarkG` of the step
`T.step k hk N₁ ν β p₁` at the clamp radius `p₁`: the constant `corrF0` is positive, the disc is
open and contains `[0,1]`, the bridge family is nonempty, the marks are measurable in `Φ`, depend
only on the blocks of the common label of their anchor, satisfy the bound
`‖G‖ ≤ corrF0 · exp (−(2 κ_dec − 1) d_l)` for all `u`, `Φ` (for every label system `Lab` on
which the common labels are built), and are differentiable in `u` on the disc. -/
theorem e1Marks_common_fromTower_pairs {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁) :
    0 < corrF0 T k β p₁ ∧ IsOpen (Metric.ball (0 : ℂ) corrU) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) corrU) ∧
    ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
      (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
    (∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1), ∀ b,
      MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁ ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b)) ∧
      (∀ Y, AnalyticOnNhd ℂ
          (fun p : (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ)) × (ℂ × ℂ) =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2.1 p.2.2 Y p.1)
          ((XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ q, ‖ψh q‖ ≤ p₁}) ×ˢ
            {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t})) ∧
      (∀ Y, ∀ ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ, (∀ q, ‖ψh q‖ ≤ p₁) →
          ∀ a b' : ℝ, 0 ≤ a → 0 < b' → (a + b') * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t →
          AnalyticOnNhd ℂ (fun p : physParam 2 (T.step k hk N₁ ν β p₁) × ℂ => deriv (fun t : ℂ =>
            evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (F₁ (z, b)) (Sol (z, b)) (blockEnergyFun (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν k b) ((T.step k hk N₁ ν β p₁).blockU z) p.2 t Y ((p.1.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), ψh)) 0)
            (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ×ˢ Metric.ball (0 : ℂ) a))) ∧
    ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z} ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        (u : ℂ), Measurable (e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
              (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)))
            (e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u)) ∧
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ) Φ,
          ‖e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u Φ‖ ≤
            corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        Φ, DifferentiableOn ℂ (fun u => e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u Φ) (Metric.ball (0 : ℂ) corrU)) := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hRU' : 2 * (17 / 16 : ℝ) ≤ corrRG T.toG k (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) p₁ := by
    rw [hb, ← corrR_toG]; exact hRU
  have h := e1Marks_common_fromTower_pairsG T.toG rfl (T.scaleDataG_of_fixed D)
    (by simpa using h3N) hN hν0 (by simpa using hν) hβ hp hRU' (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm
  simp only [corrF0_toG]
  exact h

/-- **The marks of the energy record on the common labels.**  One family of pairs `(F₁, Sol)`
(indexed by root and block) such that for every root `z`, with the marks `e1MarkG` of the step
`T.step k hk N₁ ν β p₁` at the clamp radius `p₁`: the constant `corrF0` is positive, the disc is
open and contains `[0,1]`, the bridge family is nonempty, the marks are measurable in `Φ`, depend
only on the blocks of the common label of their anchor, satisfy the bound
`‖G‖ ≤ corrF0 · exp (−(2 κ_dec − 1) d_l)` for all `u`, `Φ` (for every label system `Lab` on
which the common labels are built), and are differentiable in `u` on the disc. -/
theorem e1Marks_common_fromTower {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (h3N : 3 ∣ N₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (hβ : 0 < β)
    (hp : 0 < p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁) :
    0 < corrF0 T k β p₁ ∧ IsOpen (Metric.ball (0 : ℂ) corrU) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) corrU) ∧
    ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
      (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
        Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
    ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
      Nonempty {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z} ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        (u : ℂ), Measurable (e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u)) ∧
      (∀ (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb),
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
          DepOn (blocksOf 1 (k + 1) Set.univ
            ((commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
              (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).ysite
              (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)))
            (e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u)) ∧
        (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ) Φ,
          ‖e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z
              i u Φ‖ ≤
            corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)))) ∧
      (∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z})
        Φ, DifferentiableOn ℂ (fun u => e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
          (fun b => Sol (z, b)) p₁ hp z i u Φ) (Metric.ball (0 : ℂ) corrU)) := by
  obtain ⟨h1, h2, h3, F₁, Sol, -, h⟩ := e1Marks_common_fromTower_pairs T D h3N hN hν0 hν hβ hp hRU
  exact ⟨h1, h2, h3, F₁, Sol, h⟩

end Main

end Balaban.Inhabited
