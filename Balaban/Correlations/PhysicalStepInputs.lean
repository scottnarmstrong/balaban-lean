/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.Correlations.RealSequences
public import Balaban.Inhabited.StepTowerScale
public import Balaban.Fluctuation.LocalClassInherit

/-!
# Coherent physical inputs to the landed scale tower

The tower accepts a fine-unit coupling and mass at each scale. These algebraic
identities supply those inputs from one running coefficient sequence. They do
not assert that the successor density produces that sequence.
-/

@[expose] public section

namespace Balaban.Correlations

open Balaban Balaban.Flow Balaban.SmallField Balaban.SmallField.Def6v2
  Balaban.Inhabited Balaban.Inhabited.LevelStep Finset

/-- The fine-unit coupling at scale `k` is the same bare coupling multiplied by
the accumulated field-strength renormalization. -/
theorem betaFine_betaR (ξ : ℕ → Fin 3 → ℝ) (β : ℝ) (k : ℕ) :
    betaFine 3 3 k (betaR 3 3 ξ β k) = β * gammaR ξ k := by
  rw [betaFine, betaR_eq]
  have h3 : (3 : ℝ) ^ k ≠ 0 := by positivity
  norm_num
  field_simp

/-- The fine-unit physical mass at scale `k` is `ν δ_k`. -/
theorem physMass_deltaR (ξ : ℕ → Fin 3 → ℝ) (ν : ℝ) (k : ℕ) :
    physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k) = ν * deltaR ξ k := by
  have h3 : (3 : ℝ) ^ k ≠ 0 := by positivity
  unfold physMass
  rw [show 2 * k = k * 2 by omega, pow_mul]
  field_simp
  ring

/-- The actual `StepTower.step` at scale `k` has the prescribed physical input
coupling, rather than a fresh bare coupling. -/
theorem step_betaU_betaR {κmin : ℝ} (T : StepTower κmin) (ξ : ℕ → Fin 3 → ℝ)
    (β ν p₁ : ℝ) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] :
    (T.step k hk N₁
      (physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k))
      (betaFine 3 3 k (betaR 3 3 ξ β k)) p₁).betaU = betaR 3 3 ξ β k := by
  rw [StepTower.step, hatStepK_betaU]
  unfold betaFine
  norm_num

/-- Consecutive physical fine-unit masses obey the same factor as the running
mass coefficient. This is the algebraic step needed for one coherent sequence. -/
theorem physMass_deltaR_succ (ξ : ℕ → Fin 3 → ℝ) (ν : ℝ) (k : ℕ) :
    physMass 3 (k + 1) (ν * (3 : ℝ) ^ (2 * (k + 1)) * deltaR ξ (k + 1)) =
      physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k) *
        ((1 + ξ k 2) / (1 + ξ k 1)) := by
  rw [physMass_deltaR, physMass_deltaR, deltaR_eq, prod_range_succ]
  rw [← deltaR_eq]
  ring

/-- The next fine coupling uses the same sequence `ξ`, with no new bare
coupling at scale `k+1`. -/
theorem betaFine_betaR_succ (ξ : ℕ → Fin 3 → ℝ) (β : ℝ) (k : ℕ) :
    betaFine 3 3 (k + 1) (betaR 3 3 ξ β (k + 1)) =
      betaFine 3 3 k (betaR 3 3 ξ β k) * (1 + ξ k 2)⁻¹ := by
  rw [betaFine_betaR, betaFine_betaR, gammaR_eq, prod_range_succ]
  rw [← gammaR_eq]
  ring

/-- A uniform quarter-ball bound keeps both physical renormalization
denominators positive at every step. -/
theorem physical_denominators_pos {ξ : ℕ → Fin 3 → ℝ}
    (hξ : ∀ k, ‖ξ k‖ ≤ 1 / 4) (k : ℕ) :
    0 < 1 + ξ k 1 ∧ 0 < 1 + ξ k 2 := by
  constructor
  · have h := (abs_le_norm_pi (ξ k) 1).trans (hξ k)
    have := (abs_le.mp h).1
    linarith
  · have h := (abs_le_norm_pi (ξ k) 2).trans (hξ k)
    have := (abs_le.mp h).1
    linarith

/-- Instantiate `StepTower.scale` at every scale with the inputs of one
physical running sequence. The admissibility conditions are exactly those of
the landed scale theorem, evaluated on these inputs. -/
theorem scale_physical_inputs {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) (ξ : ℕ → Fin 3 → ℝ)
    (hξ : ∀ k, ‖ξ k‖ ≤ 1 / 4) (β ν : ℝ) :
    ∃ βray : ℝ, 2 ≤ βray ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      0 ≤ physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k) →
      physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k) *
        (3 : ℝ) ^ (2 * (k + 1)) ≤ 1 →
      βray ≤ betaFine 3 3 k (betaR 3 3 ξ β k) →
      ∀ p₁ : ℝ, 0 < p₁ →
        p₁ ≤ pLog A₁ p (betaFine 3 3 k (betaR 3 3 ξ β k) * (3 : ℝ) ^ k) →
        Nonempty (StepScaleData T k hk N₁
          (physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k))
          (betaFine 3 3 k (betaR 3 3 ξ β k)) p₁) ∧
        (T.step k hk N₁
          (physMass 3 k (ν * (3 : ℝ) ^ (2 * k) * deltaR ξ k))
          (betaFine 3 3 k (betaR 3 3 ξ β k)) p₁).betaU = betaR 3 3 ξ β k ∧
        0 < 1 + ξ k 1 ∧ 0 < 1 + ξ k 2 := by
  obtain ⟨βray, h2, hs⟩ := T.scale hA p
  refine ⟨βray, h2, ?_⟩
  intro k hk N₁ _ h3N hN hν0 hν hβ p₁ hp₁ hpLog
  exact ⟨hs k hk N₁ h3N hN _ hν0 hν _ hβ p₁ hp₁ hpLog,
    step_betaU_betaR T ξ β ν p₁ k hk N₁,
    (physical_denominators_pos hξ k).1, (physical_denominators_pos hξ k).2⟩

end Balaban.Correlations
