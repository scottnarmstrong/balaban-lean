/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Inhabited.DetOutputTermsWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the regrouped determinant terms

At every scale `k ≥ 1` and on every torus `3 ∣ N₁`, `5 < N₁` of the landed witness
(`detExpansionLocC_scale`), the record `DetExpansionLocC` has an element whose terms, regrouped on
the collar hulls, satisfy the sum identity, the bound with `λ = κ''` and the constants of
`hullRate` and `hullConst`, the root clause, and locality on the hull itself.  Bounds and locality
are on data of the chart only.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization Balaban.Analysis Balaban.Inhabited.LevelStep Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.Background

/-- **The regrouped determinant terms at the landed witness** (all scales, all tori with
`3 ∣ N₁`, `5 < N₁`). -/
theorem detCollarGrouped_scale {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1)
    (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t : ℝ), 0 < t ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β p₁ δ : ℝ,
      ∀ z, ∃ (κ'' cdet : ℝ)
        (E : DetExpansionLocC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 z t κ'' cdet),
        κ' ≤ κ'' ∧ 1 ≤ cdet ∧
        (∀ D, XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G'
            (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).a (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).ν
            (k + 1) 1 t D →
          (∀ X, ‖E.detGrouped D X‖ ≤
            hullConst 3 3 κ'' cdet * Real.exp (-hullRate 3 3 κ'' * sizeJ 1 (k + 1) X)) ∧
          (∀ X, E.detGrouped D X ≠ 0 → IsPolyDom 1 (k + 1) X ∧
            box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 m₁ (k + 1)) ⊆ X) ∧
          (∀ D₂, XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G'
              (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).a (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).ν
              (k + 1) 1 t D₂ →
            ∀ X, (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
              E.detGrouped D X = E.detGrouped D₂ X)) := by
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, t, BG, κ, ht, -, hrate, hcdet, H⟩ := detExpansionLocC_scale hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, ht, fun k hk N₁ _ h3N hN ν hν0 hν β p₁ δ z => ?_⟩
  obtain ⟨-, hE⟩ := H k hk N₁ h3N hN ν hν0 hν β p₁ δ
  obtain ⟨E, -⟩ := hE z
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have h3 : 3 ≤ 3 ^ (1 + m₁) :=
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (1 + m₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hκ'0 : 0 ≤ κ' := by
    have : 0 ≤ c1 3 3 := by linarith
    rw [hκ'def, hκdecdef, hκ0def]; nlinarith
  refine ⟨_, _, E, hrate, hcdet, fun D hD => ⟨fun X => ?_, fun X hX => ?_, fun D₂ hD₂ X h => ?_⟩⟩
  · exact E.detGrouped_bound (le_refl 3) hN1 (by linarith) (by linarith) hD X
  · exact E.detGrouped_anchor (le_refl 3) hN1 hD hX
  · exact E.detGrouped_local (le_refl 3) hN1 h3 hD hD₂ h

end Balaban.Inhabited
