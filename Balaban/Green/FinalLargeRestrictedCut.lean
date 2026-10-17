/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalInteractionCutoff

/-!
# The global cut family with selected columns removed

This is the row estimate for literal deletion of the selected columns of the landed global
cut family. It does not identify the covariance of P7's variational problem with holes.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Green

/-- A bounded field on the complement of `Z`, extended by zero on `Z`, satisfies exactly
the landed final cut-family bound. The constant is independent of `Z`. -/
theorem restricted_taggedCfin_mulVec_le
    {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (Z : Finset (L1Torus d N₀))
    {ψ : L1Torus d N₀ → ℂ} (hψ : ∀ y, ‖ψ y‖ ≤ ρ)
    (x : L1Torus d N₀) :
    ‖∑ y, taggedCfin d L N₀ k M v a s x y *
        (if y ∈ Z then 0 else ψ y)‖ ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ := by
  apply norm_taggedCfin_mulVec_le hd hk hv0 hv1 ha1 ha2 hmass hM
    hκ hMB hMκ hs hρ (ψ := fun y => if y ∈ Z then 0 else ψ y)
  · intro y
    by_cases hy : y ∈ Z
    · simp [hy, hρ]
    · simpa [hy] using hψ y

end Balaban.Green
