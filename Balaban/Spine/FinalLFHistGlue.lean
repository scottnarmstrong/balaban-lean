/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ConfigAssemble
public import Balaban.Spine.FinalLFGlue
import Mathlib.Tactic.Linarith

/-!
# Assembling a history from separated components without a common witness (A6-4)

The history-level gluing for the large-field half of the last integral
(`notes/phase1/A64-DESIGN.md` §2, the history factorization). The landed assembly
`exists_assembled` (`LargeField/R/ConfigAssemble.lean`, the history-level core of Lemma III.10.2)
asks that every clique of the family occur in one history with the same localized histories; that
hypothesis serves only the witnesses of `glue_step`. With the gluing without a witness
(`glue_step_of_sep`, `Spine/FinalLFGlue.lean`) it is not needed:

* `two_mul_L_lt_omega_succ`: `2L < ω_{j+1}` under the radius hypotheses (`R_base ≥ 4L + 20`,
  `λ_j ≥ 1`);
* `exists_glue_of_sepZ`: the localization steps of components pairwise `ω_k`-separated are glued at
  every scale `j < k` (the separation of the lineages, `sep_locSt_of_sepZ`, and `glue_step_of_sep`);
* **`exists_assembled_of_sepZ`**: components of scale `k` of arbitrary histories, pairwise at index
  distance `≥ ω_k`, occur in one history without removals, with the same localized histories
  (through the core `exists_assembled_of_glue`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban RegionHistory

section Omega

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- **`2L < ω_{j+1}`** under the radius hypotheses of the flow (`R_base ≥ 4L + 20`, `λ_j ≥ 1`):
`ω_{j+1} = 2⌊R_base λ_j²⌋ + L + 11 ≥ 9L + 51`. -/
theorem two_mul_L_lt_omega_succ (F0 : FlowSteps S n R k0 K) (j : ℕ) :
    2 * S.L < S.omega (j + 1) := by
  have hRb := F0.RH.base
  have hlam : 1 ≤ S.lam j := F0.RH.one_le j
  have hsq : 1 ≤ S.lam j ^ 2 := one_le_pow₀ hlam
  have hL0 : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
  have h1 : ((S.L : ℕ) : ℝ) ≤ S.Rb * S.lam j ^ 2 := by
    have hRb0 : 0 ≤ S.Rb := by linarith
    calc ((S.L : ℕ) : ℝ) ≤ S.Rb := by linarith
      _ = S.Rb * 1 := (mul_one _).symm
      _ ≤ S.Rb * S.lam j ^ 2 := mul_le_mul_of_nonneg_left hsq hRb0
  have h2 : S.L ≤ ⌊S.Rb * S.lam j ^ 2⌋₊ := Nat.le_floor h1
  unfold Setting.omega
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  omega

end Omega

section Assembly

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {M k : ℕ} [NeZero M] {ι : Type*} {F : Finset ι}
  {Hm : ι → RegionHistory S n R k0 K} {cm : ∀ i, (Hm i).Comp k}
  (F0 : FlowSteps S n R k0 K) (hk : k ≤ K)
  (hsepZ : ∀ i ∈ F, ∀ i' ∈ F, i ≠ i' → ∀ x ∈ (cm i).1, ∀ y ∈ (cm i').1,
    S.omega k ≤ supDist x y)
include F0 hk hsepZ

/-- **The localization steps of separated components are glued** at every scale `j < k`, without
a common witness. -/
theorem exists_glue_of_sepZ {j : ℕ} (hjk : j < k) :
    ∃ u : RegionStep S.d S.L (n j) (n (j + 1)) (R (j - 1)) (R j),
      GlueProps F (fun i => locSt Hm cm i j) (S.omega (j + 1)) (critOpt S k0 (j + 1)) u :=
  glue_step_of_sep (sep_locSt_of_sepZ F0 hk hsepZ hjk) (two_mul_L_lt_omega_succ F0 j)
    F0.ok.two_le_L

/-- **Assembly of a history from separated components, without a common witness**: components
`cm i` of scale `k` of histories `Hm i` (each its own only component, `hcomps`), pairwise at index
distance `≥ ω_k`, occur in one history without removals whose components are exactly these, with the
same localized histories. -/
theorem exists_assembled_of_sepZ (hcomps : ∀ i ∈ F, comps (S.omega k) (cm i).1 = {(cm i).1}) :
    ∃ H : RegionHistory S n R k0 K, (∀ j, H.rem j = ∅) ∧
      (∀ c : H.Comp k, ∃ i ∈ F, (cm i).1 = c.1) ∧
      ∀ i ∈ F, ∃ c : H.Comp k, c.1 = (cm i).1 ∧
        H.localHistory M K k c = (Hm i).localHistory M K k (cm i) :=
  exists_assembled_of_glue F0 hk hsepZ hcomps (fun h => exists_glue_of_sepZ F0 hk hsepZ h)

end Assembly

end Balaban.LargeField
