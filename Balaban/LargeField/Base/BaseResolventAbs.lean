/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Coercive
public import Balaban.Multiscale.Constrained
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Abstract coercivity lemmas for the base decoupled resolvent (BASE-KERNEL-3 §1)

Finite-matrix facts used in the proof of Theorem 1.1: operator norm versus the quadratic form,
the inverse of a coercive matrix, the splitting `Q M Q + P` along an orthogonal projection, and
coercivity of the componentwise lift `liftOp`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban.Green
open scoped Matrix.Norms.L2Operator

section OpNorm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The `ℓ²` operator norm is at most `K` once `‖A v‖² ≤ K² ‖v‖²`. -/
theorem l2_opNorm_le_of_sqNorm (A : Matrix m n ℂ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ v : n → ℂ, sqNorm (A *ᵥ v) ≤ K ^ 2 * sqNorm v) : ‖A‖ ≤ K := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  simp only [LinearEquiv.trans_apply, LinearMap.coe_toContinuousLinearMap']
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  have := h x.ofLp
  unfold sqNorm at this
  rw [← Real.sqrt_sq hK, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  simpa using this

/-- Conversely `‖A v‖² ≤ ‖A‖² ‖v‖²`. -/
theorem sqNorm_mulVec_le_opNorm (A : Matrix m n ℂ) (v : n → ℂ) :
    sqNorm (A *ᵥ v) ≤ ‖A‖ ^ 2 * sqNorm v := by
  have := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 v)
  have h0 := norm_nonneg ((EuclideanSpace.equiv m ℂ).symm (A *ᵥ v))
  have h2 := pow_le_pow_left₀ h0 this 2
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at h2
  simpa [sqNorm] using h2

end OpNorm

section Coercive

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A coercive matrix expands the Euclidean norm: `γ² ‖v‖² ≤ ‖B v‖²`. -/
theorem sqNorm_le_of_isCoercive {B : Matrix ι ι ℂ} {γ : ℝ} (hB : IsCoercive B γ)
    (v : ι → ℂ) (hγ : 0 ≤ γ) : γ ^ 2 * sqNorm v ≤ sqNorm (B *ᵥ v) := by
  set w := B *ᵥ v with hw
  have h1 := hB v
  have hS : reQuad B v ≤ ∑ i, ‖v i‖ * ‖w i‖ := by
    unfold reQuad
    refine (Complex.re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, norm_star]
  have hCS : (∑ i, ‖v i‖ * ‖w i‖) ^ 2 ≤ sqNorm v * sqNorm w := by
    unfold sqNorm
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hN := sqNorm_nonneg v
  have hγN : 0 ≤ γ * sqNorm v := mul_nonneg hγ hN
  have h2 : (γ * sqNorm v) ^ 2 ≤ sqNorm v * sqNorm w :=
    (pow_le_pow_left₀ hγN (h1.trans hS) 2).trans hCS
  rcases hN.eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using sqNorm_nonneg w
  · nlinarith

/-- A `γ`-coercive matrix with `γ > 0` is invertible with `‖B⁻¹‖ ≤ γ⁻¹` (`ℓ²` operator norm). -/
theorem opNorm_inv_le_of_isCoercive {B : Matrix ι ι ℂ} {γ : ℝ} (hγ : 0 < γ)
    (hB : IsCoercive B γ) : IsUnit B ∧ ‖B⁻¹‖ ≤ γ⁻¹ := by
  have hU := isUnit_of_isCoercive hγ hB
  refine ⟨hU, l2_opNorm_le_of_sqNorm _ (inv_nonneg.2 hγ.le) fun f => ?_⟩
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have h := sqNorm_le_of_isCoercive hB (B⁻¹ *ᵥ f) hγ.le
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  have : (γ⁻¹) ^ 2 * (γ ^ 2 * sqNorm (B⁻¹ *ᵥ f)) ≤ (γ⁻¹) ^ 2 * sqNorm f :=
    mul_le_mul_of_nonneg_left h (by positivity)
  calc sqNorm (B⁻¹ *ᵥ f) = (γ⁻¹) ^ 2 * (γ ^ 2 * sqNorm (B⁻¹ *ᵥ f)) := by field_simp
    _ ≤ _ := this

omit [DecidableEq ι] in
theorem reQuad_eq_dot (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    reQuad A v = (star v ⬝ᵥ (A *ᵥ v)).re := rfl

theorem reQuad_one (v : ι → ℂ) : reQuad (1 : Matrix ι ι ℂ) v = sqNorm v := by
  unfold reQuad sqNorm
  simp only [Matrix.one_mulVec]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Complex.normSq_eq_conj_mul_self (z := v i)
  have h2 : (star (v i) * v i).re = Complex.normSq (v i) := by
    rw [Complex.star_def, ← h]; simp
  rw [h2, Complex.normSq_eq_norm_sq]

omit [DecidableEq ι] in
theorem dot_mulVec_left (B : Matrix ι ι ℂ) (v w : ι → ℂ) :
    star v ⬝ᵥ (B *ᵥ w) = star (Bᴴ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, conjTranspose_conjTranspose]

/-- Splitting along an orthogonal projection `P` (`Pᴴ = P`, `P² = P`), `Q = 1 - P`. -/
theorem reQuad_proj_split {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    reQuad ((1 - P) * M * (1 - P) + P) v =
      reQuad M ((1 - P) *ᵥ v) + sqNorm (P *ᵥ v) := by
  have hQh : (1 - P)ᴴ = 1 - P := by rw [conjTranspose_sub, conjTranspose_one, hPh]
  have hPv : reQuad P v = sqNorm (P *ᵥ v) := by
    have hP' : P = Pᴴ * P := by rw [hPh, hPP]
    rw [← reQuad_one, reQuad_eq_dot, reQuad_eq_dot]
    conv_lhs => rw [hP', ← Matrix.mulVec_mulVec]
    rw [dot_mulVec_left, conjTranspose_conjTranspose, Matrix.one_mulVec]
  have hQ : reQuad ((1 - P) * M * (1 - P)) v = reQuad M ((1 - P) *ᵥ v) := by
    rw [reQuad_eq_dot, reQuad_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dot_mulVec_left, hQh]
  rw [reQuad_add, hQ, hPv]

theorem sqNorm_proj_split {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (hPP : P * P = P) (v : ι → ℂ) :
    sqNorm v = sqNorm ((1 - P) *ᵥ v) + sqNorm (P *ᵥ v) := by
  classical
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, hPP]; simp
  have := reQuad_proj_split hPh hPP (1 : Matrix ι ι ℂ) v
  rw [Matrix.mul_one, hQQ, sub_add_cancel, reQuad_one, reQuad_one] at this
  exact this

/-- Coercivity through a projection splitting: if `M` is `γ`-coercive with `γ ≤ 1`, then
`Q M Q + P` is `γ`-coercive. -/
theorem isCoercive_proj_split {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    {M : Matrix ι ι ℂ} {γ : ℝ} (hγ1 : γ ≤ 1) (hM : IsCoercive M γ) :
    IsCoercive ((1 - P) * M * (1 - P) + P) γ := by
  intro v
  rw [reQuad_proj_split hPh hPP, sqNorm_proj_split hPh hPP v]
  have h1 := hM ((1 - P) *ᵥ v)
  have h2 := sqNorm_nonneg (P *ᵥ v)
  nlinarith

omit [DecidableEq ι] in
theorem reQuad_zero (v : ι → ℂ) : reQuad (0 : Matrix ι ι ℂ) v = 0 := by
  simp [reQuad]

omit [DecidableEq ι] in
theorem reQuad_realSmul (r : ℝ) (T : Matrix ι ι ℂ) (v : ι → ℂ) :
    reQuad (((r : ℝ) : ℂ) • T) v = r * reQuad T v := by
  simp only [reQuad_eq_dot, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

omit [DecidableEq ι] in
theorem reQuad_sum_nonneg {κ : Type*} [DecidableEq κ] {S : Finset κ}
    (M : κ → Matrix ι ι ℂ) (r : κ → ℝ) (v : ι → ℂ)
    (hr : ∀ b ∈ S, 0 ≤ r b) (hM : ∀ b ∈ S, 0 ≤ reQuad (M b) v) :
    0 ≤ reQuad (∑ b ∈ S, ((r b : ℝ) : ℂ) • M b) v := by
  induction S using Finset.induction_on with
  | empty => simp [reQuad_zero]
  | insert b S hb ih =>
    rw [Finset.sum_insert hb, reQuad_add, reQuad_realSmul]
    have := ih (fun c hc => hr c (Finset.mem_insert_of_mem hc))
      (fun c hc => hM c (Finset.mem_insert_of_mem hc))
    have h2 := mul_nonneg (hr b (Finset.mem_insert_self _ _)) (hM b (Finset.mem_insert_self _ _))
    linarith

omit [DecidableEq ι] in
/-- The componentwise lift of a coercive matrix is coercive. -/
theorem isCoercive_liftOp {N : ℕ} {H : Matrix ι ι ℂ} {γ : ℝ} (hH : IsCoercive H γ) :
    IsCoercive (Balaban.Multiscale.liftOp N H) γ := by
  intro u
  have key : reQuad (Balaban.Multiscale.liftOp N H) u =
      ∑ i : Fin N, reQuad H (fun z => u (z, i)) := by
    unfold reQuad
    rw [← Complex.re_sum, Fintype.sum_prod_type_right]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    simp only [Matrix.mulVec, dotProduct, Balaban.Multiscale.liftOp]
    rw [Fintype.sum_prod_type_right]
    simp [Finset.sum_ite_eq]
  have key2 : sqNorm u = ∑ i : Fin N, sqNorm (fun z => u (z, i)) := by
    unfold sqNorm
    rw [Fintype.sum_prod_type_right]
  rw [key, key2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hH _

/-- The rank-one projection `P = E Eᵀ` onto the span of a real unit field `e`
(`P (z,i) (w,j) = δ_{zw} e_z(i) e_z(j)`). -/
noncomputable def unitProj {N : ℕ} (e : ι → Fin N → ℝ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  Balaban.Multiscale.fieldMul (fun z i => (e z i : ℂ)) *
    (Balaban.Multiscale.fieldMul (fun z i => (e z i : ℂ)))ᵀ

theorem unitProj_apply {N : ℕ} (e : ι → Fin N → ℝ) (p q : ι × Fin N) :
    unitProj e p q = if p.1 = q.1 then (e p.1 p.2 : ℂ) * (e p.1 q.2 : ℂ) else 0 := by
  unfold unitProj
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Balaban.Multiscale.fieldMul]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases h1 : p.1 = y
    · have : q.1 ≠ y := fun h2 => h (h1.trans h2.symm)
      simp [this]
    · simp [h1]

theorem unitProj_conjTranspose {N : ℕ} (e : ι → Fin N → ℝ) : (unitProj e)ᴴ = unitProj e := by
  ext p q
  rw [Matrix.conjTranspose_apply, unitProj_apply, unitProj_apply]
  by_cases h : q.1 = p.1
  · simp [h, mul_comm]
  · simp [h, Ne.symm h]

theorem unitProj_mul_self {N : ℕ} (e : ι → Fin N → ℝ) (he : ∀ z, ∑ i, e z i ^ 2 = 1) :
    unitProj e * unitProj e = unitProj e := by
  ext ⟨z, i⟩ ⟨w, j⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [unitProj_apply]
  by_cases h : z = w
  · subst h
    have hc : (∑ k : Fin N, (e z k : ℂ) ^ 2) = 1 := by exact_mod_cast he z
    calc ∑ y : ι, ∑ k : Fin N, (if z = y then (e z i : ℂ) * (e z k : ℂ) else 0) *
          (if y = z then (e y k : ℂ) * (e y j : ℂ) else 0)
        = ∑ k : Fin N, (e z i : ℂ) * (e z k : ℂ) * ((e z k : ℂ) * (e z j : ℂ)) := by
          rw [Finset.sum_eq_single z]
          · simp
          · intro y _ hy
            refine Finset.sum_eq_zero fun k _ => ?_
            simp [Ne.symm hy]
          · simp
      _ = (e z i : ℂ) * (e z j : ℂ) * ∑ k : Fin N, (e z k : ℂ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = _ := by simp [hc]
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : z = y
    · have : y ≠ w := fun h2 => h (h1.trans h2)
      simp [this]
    · simp [h1]

end Coercive

end Balaban.LargeField.Base
