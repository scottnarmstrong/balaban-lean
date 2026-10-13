/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.XiCDomains
public import Balaban.Fluctuation.InteractionSymmRot
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Every unit vector is a rotation of the coordinate unit vector

The frozen root quantifies every unit external field `h`, while the step is proved at the
coordinate vector `unitVec`.  This file shows:

* `orthogonal_to_unitVec`: for a unit vector `h` there is a real orthogonal matrix `Q`
  (`Qᵀ Q = 1`) with `Q e₀ = h` (a Householder reflection);
* `orthogonal_to_unitVec_euclidean`: the same for `h` in `EuclideanSpace ℝ (Fin N)` with `‖h‖ = 1`;
* `rot_cmat_h_const`, `rot_cmat_xiCData`: the datum `D.rot (cmat Q)` of a step datum with constant
  external field `e₀` has constant external field `Q e₀`, and stays in the chart.

The landed rotation lemmas only need `Qᵀ Q = 1`, so `O(N)` suffices.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Matrix

variable {N : ℕ}

/-- **Every unit vector of `EuclideanSpace ℝ (Fin N)` is the image of the coordinate unit vector
under a real orthogonal matrix.** -/
theorem orthogonal_to_unitVec_euclidean (hN : 0 < N) (hv : EuclideanSpace ℝ (Fin N))
    (hh : ‖hv‖ = 1) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 ∧ Q *ᵥ unitVec hN = fun i => hv i := by
  set i₀ : Fin N := ⟨0, hN⟩ with hi₀
  set e : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single i₀ 1 with he
  have hne : ‖e‖ = ‖hv‖ := by rw [hh, he]; simp
  set R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
    Submodule.reflection (ℝ ∙ (e - hv))ᗮ with hR
  have hRe : R e = hv := Submodule.reflection_sub hne
  refine ⟨Matrix.of fun i k => R (EuclideanSpace.single k 1) i, ?_, ?_⟩
  · ext a b
    have h1 : inner ℝ (R (EuclideanSpace.single a (1 : ℝ))) (R (EuclideanSpace.single b (1 : ℝ))) =
        inner ℝ (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ)) :=
      R.inner_map_map _ _
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [EuclideanSpace.inner_single_left] at h1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h1
    simp only [PiLp.single_apply] at h1
    by_cases hab : a = b
    · subst hab
      simp at h1
      simpa [mul_comm] using h1
    · simp [hab] at h1 ⊢
      simpa [mul_comm] using h1
  · funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_eq_single i₀]
    · have h0 : unitVec hN i₀ = 1 := by simp [unitVec, hi₀]
      rw [h0, mul_one, ← hRe]
    · intro b _ hb
      have h0 : unitVec hN b = 0 := by simp [unitVec, hi₀] at hb ⊢; exact hb
      rw [h0, mul_zero]
    · simp

/-- **`orthogonal_to_unitVec`**: a vector `h : Fin N → ℝ` with `∑ hᵢ² = 1` is `Q e₀` for a real
orthogonal matrix `Q`. -/
theorem orthogonal_to_unitVec (hN : 0 < N) (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 ∧ Q *ᵥ unitVec hN = h := by
  have hn : ‖(WithLp.toLp 2 h : EuclideanSpace ℝ (Fin N))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simpa using hh
  exact orthogonal_to_unitVec_euclidean hN (WithLp.toLp 2 h) hn

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The rotated step datum has constant external field `Q e₀`. -/
theorem rot_cmat_h_const {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (D : BgData G N)
    (h₀ : Fin N → ℝ) (hh₀ : ∀ x i, D.h x i = (h₀ i : ℂ)) (Q : Matrix (Fin N) (Fin N) ℝ) :
    ∀ x i, (D.rot (cmat Q)).h x i = ((Q *ᵥ h₀) i : ℂ) := by
  intro x i
  have : D.h x = fun j => (h₀ j : ℂ) := funext (hh₀ x)
  show (cmat Q *ᵥ D.h x) i = _
  rw [this, cmat_mulVec]

/-- The rotated datum stays in the chart `Ξ^c`. -/
theorem rot_cmat_xiCData {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ} {D : BgData G N}
    (h : XiCData G a ν n σ ε D) : XiCData G a ν n σ ε (D.rot (cmat Q)) :=
  xiCData_rot hQ h

end Balaban.Inhabited
