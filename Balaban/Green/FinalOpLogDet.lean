/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLogDet
public import Balaban.Green.FinalTaggedRow
public import Balaban.Green.FinalCfinInverse
public import Balaban.Green.FinalPathDefect

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The interpolated final operator: invertibility on the full closed polydisc

The tagged parametrix `taggedGfin s = G_*(s) (1 - K(s))⁻¹` of `finalOp + t` vanishes at `s = 0`
(every tag set is nonempty), so it is not invertible on any polydisc centred at `0`
(`taggedGfin_not_isUnit_zero`).  The part of the interpolated operator that stays invertible on the
whole closed polydisc `‖s p‖ ≤ e^κ` is the defect factor `1 - K(s, t)`: its weighted row sums
satisfy `‖K(s, t)‖ ≤ B e^{H κ}/M ≤ 1/4`, so `1 - K(s, t)` is invertible with the weighted row sums
of the inverse at most `4/3` (`taggedDefect_isUnit_inv_weighted`).  At `s = 0` it is the identity
and at `s = 1` it is the product `(finalOp + t) · G_*(1, t)` of the shifted operator and the
partition-of-unity box resolvent (`det_one_sub_taggedK_one`).
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- At `s = 0` all tags vanish and the tagged defect is `0`. -/
theorem taggedK_zero (hM : 0 < M) (hd : 0 < d) (t : ℝ) :
    taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t (0 : MacIdx d N₀ M → ℂ) = 0 := by
  ext x y
  simp [taggedK, taggedMat, tagMon_macTags_zero hM hd]

/-- **Obstruction.**  The tagged parametrix of `finalOp + t` is `0` at `s = 0`, hence not
invertible there; no polydisc centred at `0` is a domain of invertibility of `taggedGfin`. -/
theorem taggedGfin_not_isUnit_zero (hM : 0 < M) (hd : 0 < d) (t : ℝ) (x : L1Torus d N₀) :
    ¬ IsUnit (taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t
      (0 : MacIdx d N₀ M → ℂ)) := by
  intro h
  rw [taggedGfin_zero hM hd, isUnit_zero_iff] at h
  have := congrFun (congrFun h x) x
  simp at this

/-- **Invertibility on the full closed polydisc.**  Under the hypotheses of `taggedGfin_final`,
for `0 ≤ r ≤ ε/8` and every `s` with `‖s p‖ ≤ e^κ`, the defect `1 - K(s, t)` of the interpolated
parametrix of `finalOp + t` is invertible, and the weighted row sums of its inverse are at most
`4/3`. -/
theorem taggedDefect_isUnit_inv_weighted (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) :
    IsUnit (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s) ∧
      ∀ x, ∑ y, Real.exp (r * dist x y) *
        ‖(1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s)⁻¹ x y‖ ≤ 4 / 3 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have hw1 : ∀ x y : L1Torus d N₀, 1 ≤ Real.exp (r * dist x y) := fun x y =>
    Real.one_le_exp (mul_nonneg hr0 dist_nonneg)
  have hww : ∀ x : L1Torus d N₀, Real.exp (r * dist x x) = 1 := fun x => by simp
  have hsub : ∀ x u y : L1Torus d N₀,
      Real.exp (r * dist x y) ≤ Real.exp (r * dist x u) * Real.exp (r * dist u y) := by
    intro x u y
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [dist_triangle x u y])
  have hinv := weightedRow_inv_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw1 hww hsub
    (taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t s) (q := 1 / 4) (by norm_num)
    (fun x => (taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x).trans hq)
  have h43 : 1 / (1 - (1 / 4 : ℝ)) = 4 / 3 := by norm_num
  rw [h43] at hinv
  exact hinv

/-- **The value at `s = 1`.**  `1 - K(1, t) = (finalOp + t) · G_*(1, t)`, so the determinant of the
interpolated defect at `s = 1` is the determinant of the shifted final operator times the
determinant of the partition-of-unity box resolvent `∑_z χ_z G_z`. -/
theorem det_one_sub_taggedK_one (t : ℝ) :
    (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det =
      (shiftMat (finalOp d L N₀ k v a) t).det *
        (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det := by
  rw [taggedK_one, taggedG_one, ← Matrix.det_mul,
    ← parametrix_identity Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (fun u => by
        exact_mod_cast macChi_sum (d := d) (m := N₀) (M := M) u) (finalOp d L N₀ k v a) t]

end Balaban.Green
