/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1LabelsBudget
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

end Marks

section Radius

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- The marked radius of the step is the radius `decMR` of the tower. -/
theorem e1_markedRad_eq (hβ : 0 < β) :
    markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      decMR T k (β * 3 ^ k) p₁ := by
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * 3 ^ k := by
    have hβS : (T.step k hk N₁ ν β p₁).β = β := rfl
    unfold StepSetting.betaU
    rw [hβS]
    push_cast
    field_simp
  rw [hbU]
  exact markedRad_eq T k hb0.le p₁

/-- For `‖u‖ ≤ corrU` and `2 corrU ≤ R`, the disc of the marks lies in the radius of the pairs. -/
theorem e1_rad_lt (hβ : 0 < β) (hp : 0 < p₁) (hRU : 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁)
    {u : ℂ} (hu : ‖u‖ ≤ corrU) :
    (‖u‖ + ‖(0 : ℂ)‖) * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb0 : 0 < β * 3 ^ k := by positivity
  rw [e1_markedRad_eq T hk hβ]
  have h2 := two_corrR_mul_decMR_lt T hk hb0 hp
  have hq := decMR_pos T hk hb0 hp
  have hU := corrU_pos
  rw [norm_zero, add_zero]
  nlinarith

/-- The radius `R + R` of the analyticity of the rooted outputs is admissible. -/
theorem e1_rad_RR_lt (hβ : 0 < β) (hp : 0 < p₁) :
    (corrR T k (β * 3 ^ k) p₁ + corrR T k (β * 3 ^ k) p₁) *
      markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb0 : 0 < β * 3 ^ k := by positivity
  rw [e1_markedRad_eq T hk hβ]
  have h2 := two_corrR_mul_decMR_lt T hk hb0 hp
  linarith

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
  classical
  have hp' : 0 < (T.step k hk N₁ ν β p₁).p₁ := hp
  obtain ⟨hV, -⟩ := D.covers
  have hXi : XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t (T.step k hk N₁ ν β p₁).D' := D.xi
  refine ⟨corrF0_pos T hk hβ hp, Metric.isOpen_ball, ?_, ?_⟩
  · intro s hs
    rw [mem_ball_zero_iff]
    refine norm_ofReal_lt_of_mem hs ?_
    unfold corrU
    norm_num
  obtain ⟨F₁, Sol, hF⟩ := markCorrFamily_fromTower T D hN hν0 hν hβ hp hRU
    (S := T.step k hk N₁ ν β p₁) rfl hp
  refine ⟨F₁, Sol, fun z b => ?_, fun z => ?_⟩
  · obtain ⟨hP, hJ2, hJ4, -⟩ := hF z
    exact ⟨hP b, hJ2 b, hJ4 b⟩
  obtain ⟨hP, hJ2, hJ4, hcnt, -⟩ := hF z
  have hΘ : rawOf (T.step k hk N₁ ν β p₁).D' ∈ XiCRaw (T.step k hk N₁ ν β p₁).G'
      (compWeight 3 (T.step k hk N₁ ν β p₁).a₁) (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t :=
    ⟨_, hXi, rfl⟩
  have hout := markedOutDecCorr_fields (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).hG'
    (by norm_num) (by simpa using h3N) (fun b => (hV b).1) (fun b => (hV b).2.2.1) z
    (fun b => F₁ (z, b)) (fun b => Sol (z, b)) hP hJ2 hJ4 (ρ := p₁) hp le_rfl hp' T.t_pos
    (((T.step k hk N₁ ν β p₁).β : ℝ) : ℂ)
  obtain ⟨hmeas, hdep, hhol⟩ := hout
  have hmeasG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      Measurable (e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z i u) := by
    intro i u
    by_cases hu : ‖u‖ < corrU
    · have e : e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z i u = _ := funext fun Φ => e1MarkG_of_lt _ _ _ _ hp z i hu Φ
      rw [e]
      exact hmeas i.1 _ hΘ u (e1_rad_lt T hk hβ hp hRU hu.le)
    · have e : e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z i u = fun _ => 0 := funext fun Φ => e1MarkG_of_not_lt _ _ _ _ hp z i hu Φ
      rw [e]
      exact measurable_const
  have hdepG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i u) := by
    intro i u
    by_cases hu : ‖u‖ < corrU
    · have e : e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
          p₁ hp z i u = _ := funext fun Φ => e1MarkG_of_lt _ _ _ _ hp z i hu Φ
      rw [e]
      exact hdep i.1 i.2 _ hΘ u (e1_rad_lt T hk hβ hp hRU hu.le)
    · intro Φ Φ' _
      rw [e1MarkG_of_not_lt _ _ _ _ hp z i hu Φ, e1MarkG_of_not_lt _ _ _ _ hp z i hu Φ']
  have hbdG : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) z}) (u : ℂ) Φ,
      ‖e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z i u Φ‖ ≤
        corrF0 T k β p₁ * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) i.1) := by
    intro i u Φ
    by_cases hu : ‖u‖ < corrU
    · rw [e1MarkG_of_lt _ _ _ _ hp z i hu Φ]
      exact (hcnt _ hΘ u hu.le Φ).1 i.1
    · rw [e1MarkG_of_not_lt _ _ _ _ hp z i hu Φ, norm_zero]
      have := corrF0_pos T hk hβ hp
      positivity
  refine ⟨?_, hmeasG, fun Lb _ Lab => ?_, ?_⟩
  · obtain ⟨Y, hY⟩ := e1Dom_bridgeFamily_nonempty T D z
    exact ⟨⟨Y, hY⟩⟩
  · obtain ⟨h1, h2⟩ := commonAnchor_marks_fields (Lab := Lab)
      (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num) (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D) z (ι := {Y' // Y' ∈ bridgeFamily 1
        (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z}) id (fun _ => corrF0 T k β p₁)
      (2 * T.κdec - 1)
      (fun i u => e1MarkG (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b)) (fun b => Sol (z, b))
        p₁ hp z i u) hdepG hbdG
    exact ⟨h1, h2⟩
  · intro i Φ
    have hR := corrR_pos T hk (by positivity : 0 < β * 3 ^ k) hp
    have hU := corrU_pos
    have he₀ : ((⟨rawOf (T.step k hk N₁ ν β p₁).D', rawOf_mem_rawSub _⟩ :
        rawSub 2 (T.step k hk N₁ ν β p₁).G'),
        (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
        physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t :=
      (mk_mem_physFibre (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).hh₀ hXi (g := 0)
        (by simp)).1
    have han := hhol i.1 Φ (corrR T k (β * 3 ^ k) p₁) (corrR T k (β * 3 ^ k) p₁) hR hR
      (e1_rad_RR_lt T hk hβ hp)
    have hd := (han.differentiableOn).comp (f := fun u : ℂ => ((⟨⟨rawOf (T.step k hk N₁ ν β p₁).D',
        rawOf_mem_rawSub _⟩, (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)⟩ :
        physParam 2 (T.step k hk N₁ ν β p₁)), u))
      (s := Metric.ball (0 : ℂ) corrU)
      (differentiableOn_const _ |>.prodMk differentiableOn_id) ?_
    · refine hd.congr fun u hu => ?_
      exact e1MarkG_of_lt _ _ _ _ hp z i (mem_ball_zero_iff.1 hu) Φ
    · intro u hu
      refine ⟨he₀, ?_⟩
      rw [mem_ball_zero_iff] at hu ⊢
      linarith

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
