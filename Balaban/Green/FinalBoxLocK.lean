/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCut
public import Balaban.Green.GaussianChangeGeneral
public import Balaban.LargeField.Base.BaseChartCutSqrt

/-!
# The Gaussian variable of the box integral is the cut field at `s = 1` (A6-3, the K-link)

The box integral of the last integral changes variables by `v = K^{-1/2} w` with
`K = β D` (the real positive definite square root `pdSqrtInv`, `D` the final Hessian read on the
blocks through an equivalence `e`).  After complexification this is the cut field of the final
Hessian at `s = 1`:

  `(pdSqrtInv ((β • D).submatrix e e)).map ofReal = (√β⁻¹ : ℂ) • (boxCut 1).submatrix e e`.

* `pdSqrtInv_smul`, `pdSqrtInv_submatrix`: `pdSqrtInv (c • K) = √c⁻¹ • pdSqrtInv K` and the
  reindexing along an equivalence (uniqueness of the square root, `pdSqrtInv_unique`);
* `finalHessian_posDef`: the final Hessian is positive definite for `0 < ν ≤ 1`, `a ≥ 1/2`,
  `|h| = 1` (symmetry `finalHessian_transpose`, coercivity `finalHessian_form_ge_mass`);
* `pdSqrtInv_finalHessian_map`: `(pdSqrtInv D).map ofReal = boxCut 1` (`pdSqrtInv_map_eq_sqrtMat`,
  `finalHessianC_ofReal`, `boxCut_one`);
* `pdSqrtInv_smul_finalHessian_submatrix_map`: the link for `K = (β • D).submatrix e e`.
-/

@[expose] public section

namespace Balaban.Green

open Matrix

section Sqrt

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `pdSqrtInv (c • K) = √c⁻¹ • pdSqrtInv K` for `c > 0` and `K` positive definite. -/
theorem pdSqrtInv_smul {K : Matrix ι ι ℝ} (hK : K.PosDef) {c : ℝ} (hc : 0 < c) :
    pdSqrtInv (c • K) = Real.sqrt c⁻¹ • pdSqrtInv K := by
  symm
  refine pdSqrtInv_unique ((pdSqrtInv_posSemidef K).smul (Real.sqrt_nonneg _)) ?_
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 hK.isUnit
  have hcK : (c • K)⁻¹ = c⁻¹ • K⁻¹ := by
    have := Matrix.inv_smul' (A := K) (Units.mk0 c hc.ne') hdet
    simpa [Units.smul_def] using this
  rw [hcK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pdSqrtInv_mul_self hK,
    Real.mul_self_sqrt (inv_nonneg.2 hc.le)]

/-- `pdSqrtInv` commutes with the reindexing along an equivalence. -/
theorem pdSqrtInv_submatrix {K : Matrix κ κ ℝ} (hK : K.PosDef) (e : ι ≃ κ) :
    pdSqrtInv (K.submatrix e e) = (pdSqrtInv K).submatrix e e := by
  symm
  refine pdSqrtInv_unique ((posSemidef_submatrix_equiv e).2 (pdSqrtInv_posSemidef K)) ?_
  rw [Matrix.submatrix_mul_equiv, pdSqrtInv_mul_self hK, Matrix.inv_submatrix_equiv]

end Sqrt

section Hessian

variable {d ℓ Nb m N : ℕ} [NeZero ℓ] [NeZero m]

/-- **The final Hessian is positive definite** for `0 < ν ≤ 1`, `a ≥ 1/2` and `|h| = 1`. -/
theorem finalHessian_posDef (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (ha : 1 / 2 ≤ a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (finalHessian d ℓ Nb m ν a h).PosDef := by
  have ha0 : 0 < a := by linarith
  have hsym := finalHessian_transpose hℓ hN hd hν.le ha0 hh
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hsym
  · have hgap := finalHessian_form_ge_mass hℓ hN hd hν.le hν1 ha hh x
    have hxx : 0 < x ⬝ᵥ x := by
      obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
      refine lt_of_lt_of_le (mul_self_pos.2 hy) ?_
      exact Finset.single_le_sum (f := fun y => x y * x y) (fun _ _ => mul_self_nonneg _)
        (Finset.mem_univ y)
    have hc : 0 < 1 / (8 * (d : ℝ) + 3) * ν := by positivity
    simpa using lt_of_lt_of_le (mul_pos hc hxx) hgap

end Hessian

section Link

variable {d L N₀ k M N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **The real inverse square root of the final Hessian is the cut field at `s = 1`.** -/
theorem pdSqrtInv_finalHessian_map [NeZero N] {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ = N₀ * L ^ k)
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 < v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (pdSqrtInv (finalHessian d ℓ (L ^ k) N₀ v a h)).map (algebraMap ℝ ℂ) =
      boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1) := by
  subst hℓ
  have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hpd := finalHessian_posDef (N := N) (ℓ := N₀ * L ^ k) (Nb := L ^ k) (m := N₀)
    (mul_comm N₀ (L ^ k)) hN hd hv0 hv1 ha1 hh
  have : Nonempty (Torus d N₀ × Fin N) := ⟨((0 : Torus d N₀), (0 : Fin N))⟩
  have hs : ∑ i, ((h i : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : ∑ i, ((h i : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hh
    rw [this]; exact one_ne_zero
  rw [LargeField.pdSqrtInv_map_eq_sqrtMat _ hpd,
    ← finalHessianC_ofReal (L := L) (N₀ := N₀) (k := k) hd hv0.le (by linarith) hh,
    boxCut_one hd hk hv0.le hv1 ha1 ha2 hmass hM hκ hMB hMκ hs]
  rfl

/-- **The K-link**: for `K = (β • D).submatrix e e`, `D` the final Hessian and `e` an
equivalence of the index sets, `(pdSqrtInv K).map ofReal = √β⁻¹ • (boxCut 1).submatrix e e`. -/
theorem pdSqrtInv_smul_finalHessian_submatrix_map [NeZero N] {ℓ : ℕ} [NeZero ℓ]
    (hℓ : ℓ = N₀ * L ^ k) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ Torus d N₀ × Fin N) {β : ℝ} (hβ : 0 < β)
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 < v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (pdSqrtInv ((β • finalHessian d ℓ (L ^ k) N₀ v a h).submatrix e e)).map (algebraMap ℝ ℂ) =
      ((Real.sqrt β⁻¹ : ℝ) : ℂ) •
        (boxCut d L N₀ k M v a (fun i => (h i : ℂ)) (fun _ => 1)).submatrix e e := by
  have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hpd := finalHessian_posDef (N := N) (ℓ := ℓ) (Nb := L ^ k) (m := N₀)
    (hℓ.trans (mul_comm N₀ (L ^ k))) hN hd hv0 hv1 ha1 hh
  rw [pdSqrtInv_submatrix (hpd.smul hβ) e, pdSqrtInv_smul hpd hβ,
    ← pdSqrtInv_finalHessian_map hℓ hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hh]
  ext p q
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  rfl

end Link

end Balaban.Green
