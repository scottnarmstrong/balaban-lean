/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RhoZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Tube lemmas for the denominator (Lemma III.8.2)

* `tubeOn_univ_of_data`: when the set `X` contains every block of a data site, the tube `Ψ̃(X; κ)` is `Ψ̃(𝔹_k; κ)`;
* `tubeOn_perturb`: a block field within `ρ` of a field of `Ψ̃(𝔹_k; κ)` on every block lies in `Ψ̃(𝔹_k; κ + 5ρ)`
  (`κ ≤ 1`, `ρ ≤ 1`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

theorem tubeOn_univ_of_data {X : Set (Torus d (N₀ * L ^ (k - k)))} {κ : ℝ} {ψ : BlockField d L N₀ k N}
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (h : TubeOn G X κ ψ) :
    TubeOn G Set.univ κ ψ :=
  ⟨fun x x' hp _ _ => h.1 x x' hp (hdata x hp.1) (hdata x' hp.2.1),
    fun x hx _ => h.2 x hx (hdata x hx)⟩

theorem norm_eu_sq (v : Fin N → ℝ) : ‖eu v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [sq_norm_euc]; rfl

theorem tubeOn_perturb {κ ρ : ℝ} (hκ : κ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {ψ ψ' : BlockField d L N₀ k N}
    (h : TubeOn G Set.univ κ ψ) (hclose : ∀ z, rn (fun i => ψ' z i - ψ z i) ≤ ρ) :
    TubeOn G Set.univ (κ + 5 * ρ) ψ' := by
  have hc : ∀ z, ‖eu (ψ' z) - eu (ψ z)‖ ≤ ρ := fun z => by
    rw [eu_sub, norm_eu]; exact hclose z
  refine ⟨fun x x' hp _ _ => ?_, fun x hx _ => ?_⟩
  · have h1 := h.1 x x' hp trivial trivial
    rw [← norm_eu] at h1 ⊢
    have e : eu (fun i => liftR ψ' x i - liftR ψ' x' i) =
        (eu (fun i => liftR ψ x i - liftR ψ x' i)) + (eu (ψ' (jBlock d L N₀ k k x)) - eu (ψ (jBlock d L N₀ k k x)))
          - (eu (ψ' (jBlock d L N₀ k k x')) - eu (ψ (jBlock d L N₀ k k x'))) := by
      ext i; simp [eu, liftR]
    rw [e]
    calc _ ≤ ‖eu (fun i => liftR ψ x i - liftR ψ x' i)‖ + ‖eu (ψ' (jBlock d L N₀ k k x)) - eu (ψ (jBlock d L N₀ k k x))‖
          + ‖eu (ψ' (jBlock d L N₀ k k x')) - eu (ψ (jBlock d L N₀ k k x'))‖ := by
            refine (norm_sub_le _ _).trans ?_
            gcongr
            exact norm_add_le _ _
      _ < κ + 5 * ρ := by
            have := hc (jBlock d L N₀ k k x); have := hc (jBlock d L N₀ k k x'); linarith
  · have h2 := h.2 x hx trivial
    set z := jBlock d L N₀ k k x
    have ea : ∑ i, ψ z i ^ 2 = ‖eu (ψ z)‖ ^ 2 := (norm_eu_sq _).symm
    have eb : ∑ i, ψ' z i ^ 2 = ‖eu (ψ' z)‖ ^ 2 := (norm_eu_sq _).symm
    rw [ea] at h2; rw [eb]
    have hdiff : |‖eu (ψ' z)‖ - ‖eu (ψ z)‖| ≤ ρ := (abs_norm_sub_norm_le _ _).trans (hc z)
    have hA : ‖eu (ψ z)‖ ^ 2 < 2 := by
      have := (abs_lt.1 h2).2; linarith
    have hAn := norm_nonneg (eu (ψ z))
    have hA2 : ‖eu (ψ z)‖ < 2 := by nlinarith
    have hBn := norm_nonneg (eu (ψ' z))
    have : |‖eu (ψ' z)‖ ^ 2 - ‖eu (ψ z)‖ ^ 2| ≤ 5 * ρ := by
      have : ‖eu (ψ' z)‖ ^ 2 - ‖eu (ψ z)‖ ^ 2 = (‖eu (ψ' z)‖ - ‖eu (ψ z)‖) * (‖eu (ψ' z)‖ + ‖eu (ψ z)‖) := by ring
      rw [this, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖eu (ψ' z)‖ + ‖eu (ψ z)‖)]
      have hb : ‖eu (ψ' z)‖ ≤ ‖eu (ψ z)‖ + ρ := by linarith [(abs_le.1 hdiff).2]
      calc |‖eu (ψ' z)‖ - ‖eu (ψ z)‖| * (‖eu (ψ' z)‖ + ‖eu (ψ z)‖) ≤ ρ * (2 * 2 + 1) := by
            apply mul_le_mul hdiff (by linarith) (by positivity) hρ0
        _ = 5 * ρ := by ring
    rw [abs_lt] at h2 ⊢
    rw [abs_le] at this
    constructor <;> linarith [h2.1, h2.2, this.1, this.2]

end Balaban.LargeField
