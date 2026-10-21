/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficientAvg

/-!
# A rotation carrying two coordinate axes to an orthonormal pair

For an orthonormal pair `a, b` of real vectors and two distinct indices `i₀ ≠ i₁` there is a real
orthogonal matrix `Q` with `Q e_{i₀} = a` and `Q e_{i₁} = b` (an orthonormal basis extending the
pair).  It carries the coefficient `v₂` at the axes `(a, b)` to the one at `(e_{i₀}, e_{i₁})`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Matrix

/-- An orthonormal pair extends to an orthonormal basis of `ℝ^N`. -/
theorem exists_orth_basis_pair {N : ℕ} (i0 i1 : Fin N) (hne : i0 ≠ i1)
    (a b : EuclideanSpace ℝ (Fin N)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = 0) :
    ∃ B : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), B i0 = a ∧ B i1 = b := by
  classical
  let v : Fin N → EuclideanSpace ℝ (Fin N) := fun i => if i = i0 then a else b
  have hv : Orthonormal ℝ (({i0, i1} : Set (Fin N)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = i0 ∨ i = i1 := by simpa using hi
    have hj' : j = i0 ∨ j = i1 := by simpa using hj
    have hba : inner ℝ b a = 0 := by rw [real_inner_comm]; exact hab
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [v, hne, hne.symm, ha, hb, hab, hba]
  obtain ⟨B, hB⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
    (s := {i0, i1}) (v := v)
  refine ⟨B, ?_, ?_⟩
  · have := hB i0 (by simp); simpa [v] using this
  · have := hB i1 (by simp); simpa [v, hne.symm] using this

/-- **The rotation of a pair of axes**: for an orthonormal pair `a, b` and distinct indices there is
a real orthogonal `Q` with `Q e_{i₀} = a`, `Q e_{i₁} = b` (as complex vectors). -/
theorem exists_rot_pair {N : ℕ} (i0 i1 : Fin N) (hne : i0 ≠ i1)
    (a b : EuclideanSpace ℝ (Fin N)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = 0) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 ∧
      (fun i => ((a i : ℝ) : ℂ)) = cmat Q *ᵥ (Pi.single i0 1 : Fin N → ℂ) ∧
      (fun i => ((b i : ℝ) : ℂ)) = cmat Q *ᵥ (Pi.single i1 1 : Fin N → ℂ) := by
  obtain ⟨B, hB0, hB1⟩ := exists_orth_basis_pair i0 i1 hne a b ha hb hab
  refine ⟨Matrix.of fun i k => B k i, ?_, ?_, ?_⟩
  · ext p q
    have h1 := B.orthonormal
    rw [orthonormal_iff_ite] at h1
    have h2 := h1 p q
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [PiLp.inner_apply] at h2
    simp only [RCLike.inner_apply, conj_trivial] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  · funext i
    simp only [cmat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single i0]
    · simp [hB0]
    · intro k _ hk; simp [hk]
    · simp
  · funext i
    simp only [cmat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single i1]
    · simp [hB1]
    · intro k _ hk; simp [hk]
    · simp

end Balaban.LargeField.Def7v2
