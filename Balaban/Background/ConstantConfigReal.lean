/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.Matrix.Orthogonal

/-!
# Constant configurations at `λ = ∞`: real data

For constant data `(ψ, h)` (P2 §2, Prop. 2.1 at `λ = ∞`) the variational problem is to minimise
`(a/2)|ψ - φ|² + (ν/2)|φ - h|²` over the unit sphere `φ ⬝ᵥ φ = 1`.  With `w = aψ + νh ≠ 0` the
unique minimiser is `φ = w/√(w ⬝ᵥ w)`, with multiplier `α = √(w ⬝ᵥ w) - a - ν`; it is the unique
solution of the Euler–Lagrange system
`a(φ - ψ) + ν(φ - h) + αφ = 0`, `φ ⬝ᵥ φ = 1` with `|α| < a + ν`.
It is covariant under the orthogonal group.
-/

@[expose] public section

open Matrix

namespace Balaban.Background

variable {ι : Type*} [Fintype ι]

/-- The constant-configuration functional `(a/2)|ψ - φ|² + (ν/2)|φ - h|²`. -/
noncomputable def constObjective (a ν : ℝ) (ψ h φ : ι → ℝ) : ℝ :=
  a / 2 * ((ψ - φ) ⬝ᵥ (ψ - φ)) + ν / 2 * ((φ - h) ⬝ᵥ (φ - h))

/-- The vector `w = aψ + νh`. -/
def blendVec (a ν : ℝ) (ψ h : ι → ℝ) : ι → ℝ := a • ψ + ν • h

/-- The explicit constrained minimiser `φ = w / √(w ⬝ᵥ w)`. -/
noncomputable def constMinimizer (a ν : ℝ) (ψ h : ι → ℝ) : ι → ℝ :=
  (Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h))⁻¹ • blendVec a ν ψ h

/-- The Lagrange multiplier `α = √(w ⬝ᵥ w) - a - ν`. -/
noncomputable def constMultiplier (a ν : ℝ) (ψ h : ι → ℝ) : ℝ :=
  Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) - a - ν

section Basic

variable {a ν α : ℝ} {ψ h φ : ι → ℝ}

theorem constObjective_eq (hφ : φ ⬝ᵥ φ = 1) :
    constObjective a ν ψ h φ =
      a / 2 * (ψ ⬝ᵥ ψ + 1) + ν / 2 * (1 + h ⬝ᵥ h) - φ ⬝ᵥ blendVec a ν ψ h := by
  unfold constObjective blendVec
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hφ]
  rw [dotProduct_comm φ ψ, dotProduct_comm φ h]
  ring

theorem dotSelf_nonneg (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

theorem blend_dot_pos (hw : blendVec a ν ψ h ≠ 0) :
    0 < blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h := by
  have : blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h ≠ 0 := by
    intro h0; exact hw (dotProduct_self_eq_zero.mp h0)
  exact lt_of_le_of_ne (dotSelf_nonneg _) (Ne.symm this)

theorem sqrt_blend_pos (hw : blendVec a ν ψ h ≠ 0) :
    0 < Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) :=
  Real.sqrt_pos.mpr (blend_dot_pos hw)

theorem constMinimizer_dot (hw : blendVec a ν ψ h ≠ 0) :
    constMinimizer a ν ψ h ⬝ᵥ constMinimizer a ν ψ h = 1 := by
  have hn := sqrt_blend_pos hw
  have hsq := Real.sq_sqrt (blend_dot_pos hw).le
  unfold constMinimizer
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp
  linarith

theorem constMinimizer_dot_blend (hw : blendVec a ν ψ h ≠ 0) :
    constMinimizer a ν ψ h ⬝ᵥ blendVec a ν ψ h = Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) := by
  have hn := sqrt_blend_pos hw
  have hsq := Real.sq_sqrt (blend_dot_pos hw).le
  unfold constMinimizer
  rw [smul_dotProduct, smul_eq_mul]
  field_simp
  linarith

/-- Key identity: `|φ - φ*|² = 2 - 2 φ ⬝ w / √(w ⬝ w)` on the unit sphere. -/
theorem dot_sub_minimizer (hw : blendVec a ν ψ h ≠ 0) (hφ : φ ⬝ᵥ φ = 1) :
    (φ - constMinimizer a ν ψ h) ⬝ᵥ (φ - constMinimizer a ν ψ h) =
      2 - 2 * (φ ⬝ᵥ blendVec a ν ψ h) / Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) := by
  have hn := sqrt_blend_pos hw
  have h1 := constMinimizer_dot hw
  have h2 : φ ⬝ᵥ constMinimizer a ν ψ h =
      (φ ⬝ᵥ blendVec a ν ψ h) / Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) := by
    unfold constMinimizer
    rw [dotProduct_smul, smul_eq_mul]; field_simp
  simp only [sub_dotProduct, dotProduct_sub, hφ, h1]
  rw [dotProduct_comm (constMinimizer a ν ψ h) φ, h2]
  ring

theorem dot_blend_le (hw : blendVec a ν ψ h ≠ 0) (hφ : φ ⬝ᵥ φ = 1) :
    φ ⬝ᵥ blendVec a ν ψ h ≤ Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) := by
  have hn := sqrt_blend_pos hw
  have := dotSelf_nonneg (φ - constMinimizer a ν ψ h)
  rw [dot_sub_minimizer hw hφ] at this
  have h3 : 2 * (φ ⬝ᵥ blendVec a ν ψ h) / Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) ≤ 2 := by
    linarith
  rw [div_le_iff₀ hn] at h3
  linarith

theorem eq_constMinimizer_of_dot_eq (hw : blendVec a ν ψ h ≠ 0) (hφ : φ ⬝ᵥ φ = 1)
    (heq : φ ⬝ᵥ blendVec a ν ψ h = Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h)) :
    φ = constMinimizer a ν ψ h := by
  have hn := sqrt_blend_pos hw
  have hd := dot_sub_minimizer hw hφ
  rw [heq, mul_div_assoc, div_self hn.ne'] at hd
  have h0 : (φ - constMinimizer a ν ψ h) ⬝ᵥ (φ - constMinimizer a ν ψ h) = 0 := by
    rw [hd]; ring
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp h0)

/-- **Minimiser.**  For `w = aψ + νh ≠ 0` the explicit point minimises the
functional on the unit sphere. -/
theorem constMinimizer_le (hw : blendVec a ν ψ h ≠ 0) (hφ : φ ⬝ᵥ φ = 1) :
    constObjective a ν ψ h (constMinimizer a ν ψ h) ≤ constObjective a ν ψ h φ := by
  rw [constObjective_eq hφ, constObjective_eq (constMinimizer_dot hw),
    constMinimizer_dot_blend hw]
  linarith [dot_blend_le hw hφ]

/-- **Uniqueness of the minimiser** on the unit sphere. -/
theorem eq_constMinimizer_of_le (hw : blendVec a ν ψ h ≠ 0)
    (hφ : φ ⬝ᵥ φ = 1)
    (hmin : ∀ φ' : ι → ℝ, φ' ⬝ᵥ φ' = 1 → constObjective a ν ψ h φ ≤ constObjective a ν ψ h φ') :
    φ = constMinimizer a ν ψ h := by
  have := hmin _ (constMinimizer_dot hw)
  rw [constObjective_eq hφ, constObjective_eq (constMinimizer_dot hw),
    constMinimizer_dot_blend hw] at this
  exact eq_constMinimizer_of_dot_eq hw hφ (le_antisymm (dot_blend_le hw hφ) (by linarith))

/-- The Euler–Lagrange equation `a(φ - ψ) + ν(φ - h) + αφ = 0`. -/
def IsConstEL (a ν : ℝ) (ψ h φ : ι → ℝ) (α : ℝ) : Prop :=
  a • (φ - ψ) + ν • (φ - h) + α • φ = 0

omit [Fintype ι] in
theorem isConstEL_iff : IsConstEL a ν ψ h φ α ↔ (a + ν + α) • φ = blendVec a ν ψ h := by
  unfold IsConstEL blendVec
  constructor
  · intro H
    funext i
    have := congrFun H i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith
  · intro H
    funext i
    have := congrFun H i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith

theorem constMinimizer_isConstEL (hw : blendVec a ν ψ h ≠ 0) :
    IsConstEL a ν ψ h (constMinimizer a ν ψ h) (constMultiplier a ν ψ h) := by
  have hn := sqrt_blend_pos hw
  rw [isConstEL_iff]
  have : a + ν + constMultiplier a ν ψ h =
      Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) := by
    unfold constMultiplier; ring
  rw [this]
  unfold constMinimizer
  rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

/-- **Uniqueness for the Euler–Lagrange system** with `|α| < a + ν`: the solution is
`(φ*, α*)`. -/
theorem eq_of_isConstEL (hφ : φ ⬝ᵥ φ = 1) (hEL : IsConstEL a ν ψ h φ α)
    (hα : |α| < a + ν) :
    blendVec a ν ψ h ≠ 0 ∧ φ = constMinimizer a ν ψ h ∧ α = constMultiplier a ν ψ h := by
  rw [isConstEL_iff] at hEL
  have hs : 0 < a + ν + α := by have := abs_lt.mp hα; linarith
  have hww : blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h = (a + ν + α) ^ 2 := by
    rw [← hEL, smul_dotProduct, dotProduct_smul, hφ]; simp [sq]
  have hsq : Real.sqrt (blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h) = a + ν + α := by
    rw [hww]; exact Real.sqrt_sq hs.le
  have hw : blendVec a ν ψ h ≠ 0 := by
    intro h0
    rw [h0] at hww
    have := pow_pos hs 2
    simp at hww
    nlinarith
  refine ⟨hw, ?_, ?_⟩
  · unfold constMinimizer
    rw [hsq, ← hEL, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  · unfold constMultiplier; rw [hsq]; ring

/-- Range of P2: for `a > 1/2` the constant `c = 1/2` can be used in the uniqueness. -/
theorem eq_of_isConstEL_half (ha : 1 / 2 < a) (hν : 0 ≤ ν) (hφ : φ ⬝ᵥ φ = 1)
    (hEL : IsConstEL a ν ψ h φ α) (hα : |α| < 1 / 2) :
    blendVec a ν ψ h ≠ 0 ∧ φ = constMinimizer a ν ψ h ∧ α = constMultiplier a ν ψ h :=
  eq_of_isConstEL hφ hEL (by linarith)

/-- A sufficient condition for `w ≠ 0`: the angle between `ψ` and `h` is at most `π/2`. -/
theorem blendVec_ne_zero_of_dot_nonneg (hν : 0 < ν) (ha : 0 ≤ a) (hh : h ≠ 0)
    (hψh : 0 ≤ ψ ⬝ᵥ h) : blendVec a ν ψ h ≠ 0 := by
  intro h0
  have hd : blendVec a ν ψ h ⬝ᵥ blendVec a ν ψ h = 0 := by rw [h0]; simp
  have hpos : 0 < h ⬝ᵥ h := lt_of_le_of_ne (dotSelf_nonneg h)
    (fun e => hh (dotProduct_self_eq_zero.mp e.symm))
  unfold blendVec at hd
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hd
  rw [dotProduct_comm h ψ] at hd
  nlinarith [dotSelf_nonneg ψ, mul_nonneg ha hν.le, mul_nonneg (mul_nonneg ha ha) (dotSelf_nonneg ψ),
    mul_nonneg (mul_nonneg ha hν.le) hψh, mul_pos hν hν, mul_pos (mul_pos hν hν) hpos]

end Basic

section Covariance

variable {a ν : ℝ} {ψ h : ι → ℝ} [DecidableEq ι]

theorem mulVec_dotProduct_mulVec (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1) (x y : ι → ℝ) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = x ⬝ᵥ y := by
  rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, hR, vecMul_one]

omit [DecidableEq ι] in
theorem blendVec_mulVec (R : Matrix ι ι ℝ) :
    blendVec a ν (R *ᵥ ψ) (R *ᵥ h) = R *ᵥ blendVec a ν ψ h := by
  unfold blendVec
  rw [mulVec_add, mulVec_smul, mulVec_smul]

/-- **`O(N)` covariance**: `φ*(Rψ, Rh) = R φ*(ψ, h)` for `Rᵀ R = 1`. -/
theorem constMinimizer_mulVec (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1) :
    constMinimizer a ν (R *ᵥ ψ) (R *ᵥ h) = R *ᵥ constMinimizer a ν ψ h := by
  unfold constMinimizer
  rw [blendVec_mulVec, mulVec_dotProduct_mulVec R hR, mulVec_smul]

theorem constMultiplier_mulVec (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1) :
    constMultiplier a ν (R *ᵥ ψ) (R *ᵥ h) = constMultiplier a ν ψ h := by
  unfold constMultiplier
  rw [blendVec_mulVec, mulVec_dotProduct_mulVec R hR]

end Covariance

end Balaban.Background
