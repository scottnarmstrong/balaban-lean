/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvFlow

/-!
# The terminal block coefficient of a converted window piece

P6 (2.31) preserves the coupling times each layer coefficient. The resulting terminal
coefficient can differ between pieces, even when the target action has one common weight.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {U : Type*} {S : Set U} {j k : ℕ}
  {G : GeneratingSet d L N₀ K ϱ} {X : Region G} {br : MassBranch}

/-- The coefficient invariant of a conversion chain, accumulated from its first scale
to any later scale. -/
theorem ConvChain.coeff_from_start (C : ConvChain S j k G X br N)
    {m : ℕ} (hm1 : j + 1 ≤ m) (hmk : m ≤ k) (ℓ : ℕ) :
    C.β (j + 1) * C.a (j + 1) ℓ = C.β m * C.a m ℓ := by
  induction m, hm1 using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    have hstep := C.coeff (m + 1) (by omega) hmk ℓ
    simpa only [Nat.add_sub_cancel] using (ih (by omega)).trans hstep

/-- The layer weight changes by the same RG factor as the fine-unit coupling in
the reverse direction. This is the adjacent-scale form of the chain invariant. -/
theorem ConvChain.coeff_step_of_beta_step (C : ConvChain S j k G X br N)
    {n : ℕ} (hn : j + 1 ≤ n) (hnk : n + 1 ≤ k) (ξ : ℝ)
    (hβstep : C.β n = C.β (n + 1) * (1 + ξ)) (ℓ : ℕ) :
    C.a (n + 1) ℓ = C.a n ℓ * (1 + ξ) := by
  have hc := C.coeff (n + 1) (by omega) hnk ℓ
  have hne := C.β_ne (n + 1) (by omega) hnk
  simp only [Nat.add_sub_cancel] at hc
  rw [hβstep] at hc
  apply (mul_left_cancel₀ hne)
  calc
    C.β (n + 1) * C.a (n + 1) ℓ =
        (C.β (n + 1) * (1 + ξ)) * C.a n ℓ := hc.symm
    _ = C.β (n + 1) * (C.a n ℓ * (1 + ξ)) := by ring

/-- The exact coefficient difference at the terminal scale against a common window weight.
For a pieceChain, its initial coefficient is cs.aw and its coupling is betaCanon. -/
theorem ConvChain.coeff_target_mismatch (C : ConvChain S j k G X br N)
    (hjk : j + 1 ≤ k) (ak : ℕ → ℝ) (ℓ : ℕ) :
    C.β k * (C.a k ℓ - ak ℓ) =
      C.β (j + 1) * C.a (j + 1) ℓ - C.β k * ak ℓ := by
  rw [mul_sub, ← C.coeff_from_start hjk le_rfl ℓ]

/-- The coefficient mismatch is a finite, absolute block charge. The hypothesis is
the originating-piece block read budget; no analytic response is inferred from it. -/
theorem coeff_mismatch_sum_le {ι : Type*} (s : Finset ι)
    (βj βk B : ℝ) (a : ι → ℝ) (r : ι → ℂ)
    (hB : ∑ x ∈ s, ‖(a x : ℂ) * r x‖ ≤ B) :
    ‖∑ x ∈ s, (((βj - βk) * a x : ℝ) : ℂ) * r x‖ ≤
      |βj - βk| * B := by
  calc
    ‖∑ x ∈ s, (((βj - βk) * a x : ℝ) : ℂ) * r x‖
        ≤ ∑ x ∈ s, ‖(((βj - βk) * a x : ℝ) : ℂ) * r x‖ :=
          norm_sum_le _ _
    _ = |βj - βk| * ∑ x ∈ s, ‖(a x : ℂ) * r x‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          ring
    _ ≤ |βj - βk| * B :=
          mul_le_mul_of_nonneg_left hB (abs_nonneg _)

end Balaban.LargeField.ActionConv
