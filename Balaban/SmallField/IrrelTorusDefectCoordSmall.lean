/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.Def6AvgGeom

/-!
# The centred-coordinate margin from an infinite covering-size bound

The same margin is used for inverse polymer transfer and for the canonical common-shape
partition. Factoring it out avoids repeating the diameter argument.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero N₁] in
/-- An infinite polymer below the side threshold fits the fixed torus chart with the paving
margin. -/
theorem zsmall_of_infPoly_small {P : Consts} {j : ℕ} (hjk : j ≤ k)
    {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : 4 * (diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (P.m₀ + m₁)) X' := by
  intro z hz μ
  have hdiam := infPoly_diam2 hjk hX hz h0
  have hcoord : (|z μ| : ℤ) ≤ ∑ ξ, |z ξ| :=
    Finset.single_le_sum (f := fun ξ => |z ξ|)
      (fun ξ _ => abs_nonneg _) (Finset.mem_univ μ)
  have hcoord' : ((|z μ| : ℤ) : ℝ) ≤ diamA d L P.m₀ m₁ *
      (1 + dInf L m₁ k P.m₀ j X') :=
    (show ((|z μ| : ℤ) : ℝ) ≤ ((∑ ξ, |z ξ| : ℤ) : ℝ) from by
      exact_mod_cast hcoord).trans (by simpa using hdiam)
  have hq : (0 : ℝ) ≤ (L * L ^ (P.m₀ + m₁) : ℕ) := Nat.cast_nonneg _
  have hz0 : (0 : ℝ) ≤ (|z μ| : ℤ) := by exact_mod_cast abs_nonneg (z μ)
  have hreal : (2 : ℝ) * (((|z μ| : ℤ) : ℝ) +
      ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by linarith
  exact_mod_cast hreal

omit [NeZero L] [NeZero N₁] in
/-- The arithmetic form of the side threshold, shared by finite and infinite tails. -/
theorem side_threshold_le {A t Q R : ℝ} (hA : 0 < A)
    (hnot : ¬ 4 * (A * (1 + t) + Q + 1) < R) :
    (R - 4 * Q - 4) / (4 * A) - 1 ≤ t := by
  have hle := le_of_not_gt hnot
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ (by positivity : 0 < 4 * A)).2
  nlinarith

end Balaban.SmallField.Def6
