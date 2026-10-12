/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSolve
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `DecHyp` is inhabited

The constant unit field `φ₀ ≡ e₀` with `α₀ = 0`, `δΨ = 0`, `f₁ = 0`, `δ₀ = δ₁ = 0`
(`gdef G φ₀ = 0`, `φ₀` has no gradient or Laplacian).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **`DecHyp` is inhabited** (for both values of `ιU`), from the standing hypotheses `BgHyp`. -/
theorem decHyp_nonempty {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L K ϱ a ν)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (hN : 0 < N) (ιU : Bool) :
    DecHyp (N := N) G a ν ιU 0 (fun _ i => (unitVec hN i : ℂ)) 0 0 0 0 := by
  have hg : gdef G (fun (_ : CTorus d L N₁ m₁ K) i => (unitVec hN i : ℂ)) = 0 := by
    funext x
    have := sum_sq_unitVec hN
    simp only [gdef, Pi.zero_apply, ← pow_two]
    exact_mod_cast sub_eq_zero.2 this
  have hz : negLap (zeroExt (G.Ω 1) (gdef G (fun (_ : CTorus d L N₁ m₁ K) i => (unitVec hN i : ℂ))))
      = 0 := by
    rw [hg]
    funext x
    simp [negLap, zeroExt]
  refine ⟨H.green, le_rfl, le_rfl, zero_le_one, ⟨fun x _ μ => ?_, fun x _ => ?_⟩, fun x _ => ?_,
    fun x => ?_, fun x i => ?_, fun x _ => ?_, fun _ x => ?_, fun _ x => ?_⟩
  · simp [vn]
  · simp only [vn]
    simp
    funext i
    simp only [Pi.zero_apply]
    ring
  · have : vn (fun i => (unitVec hN i : ℂ)) = 1 := by
      have h := sum_sq_unitVec hN
      simp only [vn, EuclideanSpace.norm_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp [h]
    rw [this]; norm_num
  · simp
  · simp
  · simp [vn]
  · simp [hg]
  · simp [hz]

end Balaban.Inhabited
