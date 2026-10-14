/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalComplexMatrix
public import Balaban.Green.FinalTagColumn
public import Balaban.Green.FinalTaggedSqrt

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The tagged row and column estimates for the perturbed final operator

The row and column estimates of the path-tagged macroblock parametrix hold for any coercive matrix
with exponentially decaying entries (`taggedK_row_sum_of_coercive`, `taggedG_column_sum_of_coercive`,
`taggedCfin_row_bound_of_coercive`); the estimates for `finalOp` are their instances.  Here they are
specialised to `finalOp + E` with `WSmall r η E` and `η < finalGap d L`, which is the form of the
Hessian off the constant saddle (`notes/phase1/FINALPHYS.md`, leaf L1).

For `U = finalOp + E` the gap is `g = finalGap d L - η`, the entry constant is
`A = finalDecayC d L + η`, the entry rate is `δ = min (blockDecayRate d) r`, and `ε` is any positive
number with `ε ≤ δ` and `ε ≤ ctRate A δ g (ballConst d (δ / 4))` (for instance the minimum of the
two, which is positive).
-/

@[expose] public section

open Finset Matrix MeasureTheory Set

namespace Balaban.Green

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- Row sums of the tagged defect of `finalOp + E`. -/
theorem taggedK_row_sum_finalPert (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) {ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ min (blockDecayRate d) r)
    (hεc : ε ≤ ctRate (finalDecayC d L + η) (min (blockDecayRate d) r) (finalGap d L - η)
      (ballConst d (min (blockDecayRate d) r / 4)))
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ σ : ℝ} (hκ : 0 ≤ κ) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ ε / 8) (hκM : κ * 7 ^ d ≤ ε / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, Real.exp (σ * dist x y) *
        ‖taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a + E) t s x y‖ ≤
      16 * 7 ^ d * (finalDecayC d L + η) * pdLip d / ((finalGap d L - η) * ε) *
        (ballConst d (ε / 2) * ballConst d (3 * ε / 4)) * Real.exp (pdH d * κ) / M := by
  have hC := finalDecayC_pos (L := L) hd
  exact taggedK_row_sum_of_coercive (finalOp d L N₀ k v a + E) (by linarith)
    (lt_min (blockDecayRate_pos hd) hr) (by linarith)
    (finalPert_isCoercive hd hv0 hv1 ha1 hmass hr.le hE)
    (finalPert_entry_decay hd hk hv0 ha1 ha2 hE) hε hεδ hεc ht hM hκ hσ0 hσ hκM hs x

/-- Column sums of the tagged approximate Green function of `finalOp + E`. -/
theorem taggedG_column_sum_finalPert (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) {ε : ℝ} (hε : 0 < ε)
    (hεc : ε ≤ ctRate (finalDecayC d L + η) (min (blockDecayRate d) r) (finalGap d L - η)
      (ballConst d (min (blockDecayRate d) r / 4)))
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hσ : σ ≤ ε / 8) (hκM : κ * 7 ^ d ≤ ε / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (y : L1Torus d N₀) :
    ∑ x, Real.exp (σ * dist x y) *
        ‖taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a + E) t s x y‖ ≤
      2 * Real.exp (pdH d * κ) * ballConst d (ε / 2) / ((finalGap d L - η) + t) := by
  have hC := finalDecayC_pos (L := L) hd
  exact taggedG_column_sum_of_coercive (finalOp d L N₀ k v a + E) (by linarith)
    (lt_min (blockDecayRate_pos hd) hr) (by linarith)
    (finalPert_isCoercive hd hv0 hv1 ha1 hmass hr.le hE)
    (finalPert_entry_decay hd hk hv0 ha1 ha2 hE) hε hεc ht hM hκ hσ hκM hs y

/-- Row sums of the Stieltjes square root of the tagged family of `finalOp + E`. -/
theorem taggedCfin_row_bound_finalPert (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall r η E) {ε : ℝ} (hε : 0 < ε)
    (hεδ : ε ≤ min (blockDecayRate d) r)
    (hεc : ε ≤ ctRate (finalDecayC d L + η) (min (blockDecayRate d) r) (finalGap d L - η)
      (ballConst d (min (blockDecayRate d) r / 4)))
    {M : ℕ} (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * ((16 * 7 ^ d * (finalDecayC d L + η) * pdLip d / ((finalGap d L - η) * ε) *
      (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ ε * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ ε / 8) (x : L1Torus d N₀) :
    ∑ y, Real.exp (σ * dist x y) * ‖(((1 / Real.pi : ℝ) : ℂ) •
        Localization.intMat (volume.restrict (Ioi (0 : ℝ)))
          (fun t => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
            taggedGfin Finset.univ (macBoxF d N₀ M)
              (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
              (finalOp d L N₀ k v a + E) t s)) x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) /
        Real.sqrt (finalGap d L - η) := by
  have hC := finalDecayC_pos (L := L) hd
  exact taggedCfin_row_bound_of_coercive (finalOp d L N₀ k v a + E) (by linarith)
    (lt_min (blockDecayRate_pos hd) hr) (by linarith)
    (finalPert_isCoercive hd hv0 hv1 ha1 hmass hr.le hE)
    (finalPert_entry_decay hd hk hv0 ha1 ha2 hE) hε hεδ hεc hM hκ hMB hMκ hs hσ0 hσ x

end Balaban.Green
