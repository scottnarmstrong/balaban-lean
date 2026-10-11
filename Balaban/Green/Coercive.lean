/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coercive matrices and entries of right inverses

For a finite index type `ι` and a complex matrix `A : Matrix ι ι ℂ`, the real part of the
quadratic form is `reQuad A v = Re ∑ᵢ conj(vᵢ) (A v)ᵢ`.  `A` is `γ`-*coercive* when
`γ ∑ᵢ |vᵢ|² ≤ reQuad A v` for all `v`; no Hermitian hypothesis is made.

Main results (all elementary, without operator norms):

* `Balaban.Green.reQuad_ge_of_entry_bound`: the Schur test for the quadratic form;
* `Balaban.Green.isUnit_of_isCoercive`: coercive matrices are invertible;
* `Balaban.Green.norm_entry_le_of_mul_eq_one`: a right inverse `G` of a `γ`-coercive matrix
  satisfies `‖G x y‖ ≤ γ⁻¹`.

This is the first layer of the Combes–Thomas estimate (G-4 of the Balaban roadmap); the method
follows `FroehlichSpencer.Infra.Green.CombesThomas` (Armstrong–Loher; public repository
`scottnarmstrong/Frohlich-Spencer`, commit b47bc3d), with the Hermitian hypothesis replaced by coercivity.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real part of the quadratic form `⟨v, A v⟩ = ∑ᵢ conj(vᵢ) (A v)ᵢ`. -/
noncomputable def reQuad (A : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ := (∑ i, star (v i) * (A *ᵥ v) i).re

/-- The squared Euclidean norm `∑ᵢ ‖vᵢ‖²`. -/
noncomputable def sqNorm (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

/-- `A` is `γ`-coercive: `γ ‖v‖² ≤ Re ⟨v, A v⟩` for every vector `v`. -/
def IsCoercive (A : Matrix ι ι ℂ) (γ : ℝ) : Prop := ∀ v : ι → ℂ, γ * sqNorm v ≤ reQuad A v

omit [DecidableEq ι] in
lemma sqNorm_nonneg (v : ι → ℂ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
lemma reQuad_add (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    reQuad (A + B) v = reQuad A v + reQuad B v := by
  simp [reQuad, Matrix.add_mulVec, mul_add, Finset.sum_add_distrib]

lemma reQuad_smul_one (t : ℝ) (v : ι → ℂ) :
    reQuad ((t : ℂ) • (1 : Matrix ι ι ℂ)) v = t * sqNorm v := by
  have h : ∀ i, star (v i) * (((t : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ v) i = ((t * ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [Complex.star_def, mul_left_comm, Complex.conj_mul']
    push_cast
    ring
  simp only [reQuad, h, sqNorm, ← Complex.ofReal_sum, Complex.ofReal_re, Finset.mul_sum]

lemma IsCoercive.add_smul_one {A : Matrix ι ι ℂ} {γ : ℝ} (h : IsCoercive A γ) (t : ℝ) : IsCoercive (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) (γ + t) := by
  intro v
  rw [reQuad_add, reQuad_smul_one]
  have := h v
  linarith

omit [DecidableEq ι] in
/-- Schur test for the quadratic form: if `‖D x y‖ ≤ E x y` with row and column sums of `E`
bounded by `S`, then `Re ⟨v, D v⟩ ≥ -S ‖v‖²`. -/
theorem reQuad_ge_of_entry_bound (D : Matrix ι ι ℂ) (E : ι → ι → ℝ)
    (hDE : ∀ x y, ‖D x y‖ ≤ E x y) {S : ℝ}
    (hrow : ∀ x, ∑ y, E x y ≤ S) (hcol : ∀ y, ∑ x, E x y ≤ S) (v : ι → ℂ) :
    -(S * sqNorm v) ≤ reQuad D v := by
  have hE : ∀ x y, 0 ≤ E x y := fun x y => (norm_nonneg _).trans (hDE x y)
  have h1 : |reQuad D v| ≤ ∑ x, ∑ y, E x y * ((‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [show star (v x) * (D x y * v y) = star (v x) * D x y * v y by ring]
    simp only [norm_mul, norm_star]
    have := hDE x y
    have h2 : ‖v x‖ * ‖v y‖ ≤ (‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖v x‖ - ‖v y‖)]
    calc ‖v x‖ * ‖D x y‖ * ‖v y‖ = ‖D x y‖ * (‖v x‖ * ‖v y‖) := by ring
      _ ≤ E x y * ((‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2) :=
        mul_le_mul this h2 (by positivity) (hE x y)
  have h2 : ∑ x, ∑ y, E x y * ((‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2) ≤ S * sqNorm v := by
    have e : ∑ x, ∑ y, E x y * ((‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2)
        = (1 / 2) * (∑ x, ‖v x‖ ^ 2 * ∑ y, E x y) + (1 / 2) * (∑ y, ‖v y‖ ^ 2 * ∑ x, E x y) := by
      have : ∑ y, ‖v y‖ ^ 2 * ∑ x, E x y = ∑ x, ∑ y, ‖v y‖ ^ 2 * E x y := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
      rw [this]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    have a1 : ∑ x, ‖v x‖ ^ 2 * ∑ y, E x y ≤ S * sqNorm v := by
      rw [sqNorm, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hrow x) (sq_nonneg _)
    have a2 : ∑ y, ‖v y‖ ^ 2 * ∑ x, E x y ≤ S * sqNorm v := by
      rw [sqNorm, Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hcol y) (sq_nonneg _)
    rw [e]; linarith
  linarith [neg_abs_le (reQuad D v)]

/-- A coercive matrix is invertible. -/
theorem isUnit_of_isCoercive {B : Matrix ι ι ℂ} {γ : ℝ} (hγ : 0 < γ) (hB : IsCoercive B γ) :
    IsUnit B := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have h0 : B *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, hvw, sub_self]
  have h := hB (v - w)
  have : reQuad B (v - w) = 0 := by simp [reQuad, h0]
  have hN : sqNorm (v - w) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith
  have : sqNorm (v - w) = 0 := le_antisymm hN (sqNorm_nonneg _)
  funext i
  have hi : ‖(v - w) i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 this i (Finset.mem_univ _)
  have : (v - w) i = 0 := norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hi)
  simpa [sub_eq_zero] using this

/-- Entries of a right inverse of a `γ`-coercive matrix are bounded by `γ⁻¹`. -/
theorem norm_entry_le_of_mul_eq_one {B G : Matrix ι ι ℂ} {γ : ℝ} (hγ : 0 < γ)
    (hB : IsCoercive B γ) (hG : B * G = 1) (x y : ι) : ‖G x y‖ ≤ γ⁻¹ := by
  set u : ι → ℂ := fun i => G i y with hu
  have hBu : B *ᵥ u = fun i => if i = y then 1 else 0 := by
    funext i
    have := congrFun (congrFun hG i) y
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.mulVec, dotProduct, hu] using this
  have hq : reQuad B u = (star (u y)).re := by
    simp [reQuad, hBu]
  set N := sqNorm u with hN
  have h3 : γ * N ≤ ‖u y‖ := by
    have := hB u
    rw [hq] at this
    refine this.trans ?_
    simpa using (le_abs_self _).trans (Complex.abs_re_le_norm (u y))
  have h1 : ‖u x‖ ^ 2 ≤ N :=
    Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  have h2 : ‖u y‖ ^ 2 ≤ N :=
    Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  set a := ‖u y‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have hag : a * γ ≤ 1 := by
    by_contra hcon
    push Not at hcon
    rcases ha0.eq_or_lt with h0 | h0
    · rw [← h0] at hcon; simp at hcon; linarith
    · nlinarith
  have hinv : 0 < γ⁻¹ := inv_pos.2 hγ
  have ha1 : a ≤ γ⁻¹ := by
    calc a = (a * γ) * γ⁻¹ := by field_simp
      _ ≤ 1 * γ⁻¹ := mul_le_mul_of_nonneg_right hag hinv.le
      _ = γ⁻¹ := one_mul _
  have hN1 : N ≤ γ⁻¹ * γ⁻¹ := by
    have : N ≤ a * γ⁻¹ := by
      calc N = (γ * N) * γ⁻¹ := by field_simp
        _ ≤ a * γ⁻¹ := mul_le_mul_of_nonneg_right h3 hinv.le
    nlinarith
  show ‖u x‖ ≤ γ⁻¹
  by_contra hcon
  push Not at hcon
  nlinarith

end Balaban.Green
