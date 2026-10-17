/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomLocal
public import Balaban.Symmetry.Rotation
import Mathlib.Tactic.Linarith

/-!
# Coordinate control for a real orthogonal frame
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Matrix Finset

/-- Every entry of a real orthogonal matrix has absolute value at most one. -/
theorem realOrth_entry_abs_le_one {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.transpose * Q = 1) (i k : Fin N) : |Q i k| ≤ 1 := by
  have hcol : ∑ l : Fin N, (Q l k) ^ 2 = 1 := by
    have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M k k) hQ
    simpa [Matrix.mul_apply, dotProduct, sq] using hh
  have hle : (Q i k) ^ 2 ≤ ∑ l : Fin N, (Q l k) ^ 2 := by
    exact Finset.single_le_sum (fun l _ => sq_nonneg (Q l k)) (Finset.mem_univ i)
  rw [hcol] at hle
  nlinarith [abs_nonneg (Q i k), sq_abs (Q i k)]

/-- A nonzero real centre admits an orthogonal frame that carries its normalized vector to
the reference coordinate, with a uniform entry bound. -/
theorem exists_real_center_frame {N : ℕ} {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁)
    (p : Fin N → ℝ) (hp : 0 < rn p) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ,
      Q.transpose * Q = 1 ∧
      Q.mulVec p = rn p • (Pi.single i₀ 1 : Fin N → ℝ) ∧
      Q.mulVec (fun i => p i / rn p) = Pi.single i₀ 1 ∧
      ∀ i k, |Q i k| ≤ 1 := by
  have hp0 : p ≠ 0 := by
    intro he
    subst p
    simp [rn] at hp
  obtain ⟨Q, hQ, hQp, -⟩ := Balaban.Symmetry.exists_rotation hne p p hp0
  have heq : Real.sqrt (p ⬝ᵥ p) = rn p := by
    simp [rn, dotProduct, sq]
  rw [heq] at hQp
  refine ⟨Q, hQ, hQp, ?_, realOrth_entry_abs_le_one hQ⟩
  have hnorm : (fun i => p i / rn p) = (rn p)⁻¹ • p := by
    funext i
    simp [smul_eq_mul, inv_mul_eq_div]
  rw [hnorm, Matrix.mulVec_smul, hQp, smul_smul]
  simp [hp.ne']

end Balaban.SmallField
