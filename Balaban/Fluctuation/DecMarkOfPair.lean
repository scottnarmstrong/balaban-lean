/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DecMarkCorrected


/-!
# One decoupling pair for the decoupled marks

`MarkedEvJointPhysV` asserts that some pair `(F₁, Sol)` has the eight clauses of
`MarkedBlockExpansionDecPair` and the joint analyticity statements.  The field theorems
`decMarkG_fields` and `decMarkCorr_fields` forget the pair.  This file states

* `decMarkPair_exists`: one pair carrying all of its properties together with the fields of both
  mark families, so that further statements can refer to the same pair;
* `decMarkPair_family`: a family of blocks indexed by a type, each with its own cover data and
  hypothesis `MarkedEvJointPhysV`, has a family of such pairs (one pair per block).  The fields
  of block `b` follow from the pair by `decMarkG_fields_of_pair` and `decMarkCorr_fields_of_pair`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField Balaban.Analysis Balaban.Polymer

section Pair

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

/-- **One pair with all its properties.**  From `MarkedEvJointPhysV` there is a single pair
`(F₁, Sol)` with the eight clauses (`MarkedBlockExpansionDecPair`), the four joint analyticity
statements of `MarkedEvJointPhysV`, the fields of the decoupled marks `decMarkG`, and the fields
of the corrected marks `decMarkCorr`, all for this pair. -/
theorem decMarkPair_exists
    (hM : MarkedEvJointPhysV S Hm cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z)
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) (hδ : 0 < δ₁) :
    ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
        F₁ Sol ∧
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y
            ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2))
        ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
      (∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2 t Y
            ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2)) 0)
        ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
((∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) ∧
        Measurable (decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b →
        0 < t₀ → t₀ ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp Θ um Φ‖ ≤
          energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / t₀) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkG S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))) ∧
      ((∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
        (∀ y ∈ Y', box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Y') →
        ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        DepOn (blocksOf m₀ (k + 1) Set.univ Y')
          (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
        (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        Continuous (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um) ∧
        Measurable (decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um)) ∧
      (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ R U : ℝ, 0 < R →
        (R + R) * markedRad d L N k a₁ κ cψ cc < δ₁ → 2 * U ≤ R → ∀ um : ℂ, ‖um‖ ≤ U →
        ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b),
        ‖decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm Y ρ hp Θ um Φ‖ ≤
          4 * (energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / R) * (U / R) ^ 2) ∧
      (∀ Y, ∀ Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b), ∀ a b : ℝ, 0 < a → 0 < b →
        (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
          decMarkCorr S X₁f m₀ j 𝒦X a₁ ν cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z)
            Zm Y ρ hp (p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) p.2 Φ)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a))) := by
  obtain ⟨F₁, Sol, hP, hJ2, hJ3, hJ4, hJ5⟩ := hM
  exact ⟨F₁, Sol, hP, hJ2, hJ3, hJ4, hJ5,
    decMarkG_fields_of_pair S F₁ Sol hP hJ2 hJ4 hρ hρc hp,
    decMarkCorr_fields_of_pair S F₁ Sol hP hJ2 hJ4 hρ hρc hp hδ⟩

end Pair

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ} {cc : ℂ}
variable {ι : Type*} {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ι → ℕ} {𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))}
variable {Zm : ι → Finset (unitPts S.G')}
  {z : ι → Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

/-- **One pair per block.**  For a family of blocks indexed by `ι`, each with its own cover data
and hypothesis `MarkedEvJointPhysV`, there are families `F₁ r`, `Sol r` such that every `r` has the
eight clauses and the four joint analyticity statements for its own pair. -/
theorem decMarkPair_family
    (hM : ∀ r, MarkedEvJointPhysV S Hm cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ (Zm r) (X₁f r) (m₀ r)
      (j r) (𝒦X r) (z r)) :
    ∃ (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      ∀ r, MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ (Zm r) (X₁f r)
        (m₀ r) (j r) (𝒦X r) (z r) (F₁ r) (Sol r) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec (X₁f r) (m₀ r) (j r) (𝒦X r) a₁ ν S.hG' cc (F₁ r) (Sol r)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k (z r)) (Zm r) p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec (X₁f r) (m₀ r) (j r) (𝒦X r) a₁ ν S.hG' cc (F₁ r) (Sol r)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k (z r)) (Zm r) p.2.1 p.2.2 Y
            ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2))
        ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
      (∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec (X₁f r) (m₀ r) (j r) (𝒦X r) a₁ ν S.hG' cc (F₁ r) (Sol r)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k (z r)) (Zm r) p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × ℂ => deriv (fun t : ℂ =>
          evDec (X₁f r) (m₀ r) (j r) (𝒦X r) a₁ ν S.hG' cc (F₁ r) (Sol r)
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k (z r)) (Zm r) p.2 t Y
            ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2)) 0)
        ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  choose F₁ Sol h using hM
  exact ⟨F₁, Sol, h⟩

end Family

end Balaban.Fluctuation
