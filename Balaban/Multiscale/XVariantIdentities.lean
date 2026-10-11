/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Complex.Basic
public import Balaban.Multiscale.Constrained
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The x-variant reduction G-6(b), (b') (GREEN.md §4.7)

Exact finite-dimensional matrix identities over `ℂ`, in the notation of GREEN.md (1.7), (1.8'), §4.7:
`c = a_k`, `T = c + x + a L⁻² Q*Q` (unit-lattice operator on the points of `Ω_{k+1}^{(k)}`),
`A = T⁻¹ = A_{k,x}`, `Q : κ × ι` the block average (`Q_k`, restricted to `Ω_{k+1}^{(k)}`) and
`H̃` everything in the fine operator except the layer term `c Q*Q` on `Ω_{k+1}`.

* `Balaban.Multiscale.xBracket c T = c - c² T⁻¹ = S_x`; `xOperator H̃ Q c T = H̃ + Q* S_x Q`
  (`H_{k,x}`), `xGreen` its inverse `G_{k,x}`.
* `Balaban.Multiscale.xVariant_reduction` (G-6(b)): with `G_D = (H̃ + c Q*Q)⁻¹`,
  `(T - c² Q G_D Q*)⁻¹ = A + c² A Q G_{k,x} Q* A`.
* `Balaban.Multiscale.xBracket_projection` : for `T = (c+x) + b P`, `P` idempotent,
  `S_x = s₁ (1 - P) + s₂ P` with `s₁ = c x/(c+x)`, `s₂ = c (x+b)/(c+x+b)`.
* `Balaban.Multiscale.constrained_green_eq` (N-4): the constrained inverse
  `G_c = E (E* H E)⁻¹ E*` equals `G - Π`, `Π = G φ₀ [φ₀·G φ₀]⁻¹ φ₀·G` (here `Π = G B* (B G B*)⁻¹ B G`).
* `Balaban.Multiscale.xVariant_constrained_reduction` (G-6(b')): the constrained covariance
  `(T - c² Q E (E* H₀ E)⁻¹ E* Q*)⁻¹ = A + c² A Q (G_{k,x} - Π_{k,x}) Q* A`.

The constraint is `B : σ × ι` (`φ ↦ φ₀ · φ`), `B*` its transpose (multiplication by `φ₀`), and `E : ι × ρ`
an embedding of `ker B` (`IsKernelEmbedding`); no symmetry of `H` is needed.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix

variable {κ ι ρ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-! ### Woodbury in inverse form -/

/-- **Woodbury (inverse form).** If `T`, `H` and `D = H - c² R T⁻¹ Q` are invertible then
`(T - c² Q H⁻¹ R)(T⁻¹ + c² T⁻¹ Q D⁻¹ R T⁻¹) = 1`. -/
theorem woodbury_right_inverse (c : ℂ) (Q : Matrix κ ι ℂ) (R : Matrix ι κ ℂ) (T : Matrix κ κ ℂ)
    (H : Matrix ι ι ℂ) (hT : IsUnit T) (hH : IsUnit H)
    (hD : IsUnit (H - c ^ 2 • (R * T⁻¹ * Q))) :
    (T - c ^ 2 • (Q * H⁻¹ * R)) *
      (T⁻¹ + c ^ 2 • (T⁻¹ * Q * (H - c ^ 2 • (R * T⁻¹ * Q))⁻¹ * R * T⁻¹)) = 1 := by
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hT)
  have hHH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hH)
  have hXD : (H - c ^ 2 • (R * T⁻¹ * Q))⁻¹ * (H - c ^ 2 • (R * T⁻¹ * Q)) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hD)
  have hDX : (H - c ^ 2 • (R * T⁻¹ * Q)) * (H - c ^ 2 • (R * T⁻¹ * Q))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hD)
  set X := (H - c ^ 2 • (R * T⁻¹ * Q))⁻¹ with hX
  have hHX : H * X = 1 + c ^ 2 • (R * T⁻¹ * Q * X) := by
    have : H = (H - c ^ 2 • (R * T⁻¹ * Q)) + c ^ 2 • (R * T⁻¹ * Q) := by abel
    calc H * X = ((H - c ^ 2 • (R * T⁻¹ * Q)) + c ^ 2 • (R * T⁻¹ * Q)) * X := by rw [← this]
      _ = _ := by rw [Matrix.add_mul, hDX, Matrix.smul_mul]
  have key : X = H⁻¹ + c ^ 2 • (H⁻¹ * R * T⁻¹ * Q * X) := by
    calc X = H⁻¹ * (H * X) := by rw [← Matrix.mul_assoc, hHH, Matrix.one_mul]
      _ = _ := by
        rw [hHX, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
        simp only [Matrix.mul_assoc]
  have key2 : Q * X * R * T⁻¹ =
      Q * H⁻¹ * R * T⁻¹ + c ^ 2 • (Q * H⁻¹ * R * T⁻¹ * Q * X * R * T⁻¹) := by
    have := congrArg (fun Y => Q * Y * R * T⁻¹) key
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc] at this ⊢
    exact this
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_assoc]
  rw [hTT]
  simp only [Matrix.mul_assoc] at key2
  have e : T * (T⁻¹ * (Q * (X * (R * T⁻¹)))) = Q * (X * (R * T⁻¹)) := by
    rw [← Matrix.mul_assoc T, hTT, Matrix.one_mul]
  rw [e]
  linear_combination (norm := module) (c ^ 2) • key2

theorem woodbury_inv_eq (c : ℂ) (Q : Matrix κ ι ℂ) (R : Matrix ι κ ℂ) (T : Matrix κ κ ℂ)
    (H : Matrix ι ι ℂ) (hT : IsUnit T) (hH : IsUnit H)
    (hD : IsUnit (H - c ^ 2 • (R * T⁻¹ * Q))) :
    (T - c ^ 2 • (Q * H⁻¹ * R))⁻¹ =
      T⁻¹ + c ^ 2 • (T⁻¹ * Q * (H - c ^ 2 • (R * T⁻¹ * Q))⁻¹ * R * T⁻¹) :=
  Matrix.inv_eq_right_inv (woodbury_right_inverse c Q R T H hT hH hD)

/-! ### The x-variant -/

/-- The bracket `S_x = c - c² T⁻¹ = c - c² A_{k,x}` of (1.7), a matrix on the unit-lattice points
of `Ω_{k+1}^{(k)}`. -/
noncomputable def xBracket (c : ℂ) (T : Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  c • (1 : Matrix κ κ ℂ) - c ^ 2 • T⁻¹

/-- The operator `H_{k,x} = H̃ + Q* S_x Q` of (1.7). -/
noncomputable def xOperator (Ht : Matrix ι ι ℂ) (Q : Matrix κ ι ℂ) (c : ℂ) (T : Matrix κ κ ℂ) :
    Matrix ι ι ℂ :=
  Ht + Qᵀ * xBracket c T * Q

/-- `G_{k,x} = H_{k,x}⁻¹`. -/
noncomputable def xGreen (Ht : Matrix ι ι ℂ) (Q : Matrix κ ι ℂ) (c : ℂ) (T : Matrix κ κ ℂ) :
    Matrix ι ι ℂ :=
  (xOperator Ht Q c T)⁻¹

omit [Fintype ι] [DecidableEq ι] in
theorem xOperator_eq (Ht : Matrix ι ι ℂ) (Q : Matrix κ ι ℂ) (c : ℂ) (T : Matrix κ κ ℂ) :
    xOperator Ht Q c T = (Ht + c • (Qᵀ * Q)) - c ^ 2 • (Qᵀ * T⁻¹ * Q) := by
  unfold xOperator xBracket
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.mul_assoc]
  abel

/-- **G-6(b)**, the Woodbury line of §4.7: with `G_D = (H̃ + c Q*Q)⁻¹` and `T` invertible,
`(T - c² Q G_D Q*)(A + c² A Q G_{k,x} Q* A) = 1`, `A = T⁻¹`. -/
theorem xVariant_reduction_mul (c : ℂ) (Q : Matrix κ ι ℂ) (Ht : Matrix ι ι ℂ) (T : Matrix κ κ ℂ)
    (hT : IsUnit T) (hHD : IsUnit (Ht + c • (Qᵀ * Q))) (hHx : IsUnit (xOperator Ht Q c T)) :
    (T - c ^ 2 • (Q * (Ht + c • (Qᵀ * Q))⁻¹ * Qᵀ)) *
      (T⁻¹ + c ^ 2 • (T⁻¹ * Q * xGreen Ht Q c T * Qᵀ * T⁻¹)) = 1 := by
  rw [xOperator_eq] at hHx
  have := woodbury_right_inverse c Q Qᵀ T _ hT hHD hHx
  rw [xGreen, xOperator_eq]
  exact this

/-- **G-6(b)** with the covariance written as an inverse:
`(T - c² Q G_D Q*)⁻¹ = A + c² A Q G_{k,x} Q* A`. With `T = c + Y` (`Y = x + a L⁻² Q*Q` on the
unit lattice) the matrix `T - c² Q G_D Q*` is `Y + Δ_unc`, `Δ_unc = c - c² Q G_D Q*`
(`xVariant_reduction_delta`). -/
theorem xVariant_reduction (c : ℂ) (Q : Matrix κ ι ℂ) (Ht : Matrix ι ι ℂ) (T : Matrix κ κ ℂ)
    (hT : IsUnit T) (hHD : IsUnit (Ht + c • (Qᵀ * Q))) (hHx : IsUnit (xOperator Ht Q c T)) :
    (T - c ^ 2 • (Q * (Ht + c • (Qᵀ * Q))⁻¹ * Qᵀ))⁻¹ =
      T⁻¹ + c ^ 2 • (T⁻¹ * Q * xGreen Ht Q c T * Qᵀ * T⁻¹) :=
  Matrix.inv_eq_right_inv (xVariant_reduction_mul c Q Ht T hT hHD hHx)

omit [Fintype κ] [DecidableEq ι] in
/-- `T - c² Q G_D Q* = Y + (c - c² Q G_D Q*)` when `T = c + Y`. -/
theorem xVariant_reduction_delta (c : ℂ) (Y : Matrix κ κ ℂ) (Q : Matrix κ ι ℂ)
    (G : Matrix ι ι ℂ) (T : Matrix κ κ ℂ) (hT : T = c • 1 + Y) :
    T - c ^ 2 • (Q * G * Qᵀ) = Y + (c • (1 : Matrix κ κ ℂ) - c ^ 2 • (Q * G * Qᵀ)) := by
  subst hT
  abel_nf

/-! ### The bracket on the eigenspaces of a projection -/

/-- For `T = (c+x) + b P` with `P` idempotent: `T * ((c+x)⁻¹ (1 - P) + (c+x+b)⁻¹ P) = 1`. -/
theorem projection_mul_inv (c x b : ℂ) (P : Matrix κ κ ℂ) (hP : P * P = P) (h1 : c + x ≠ 0)
    (h2 : c + x + b ≠ 0) :
    ((c + x) • (1 : Matrix κ κ ℂ) + b • P) *
      ((c + x)⁻¹ • ((1 : Matrix κ κ ℂ) - P) + (c + x + b)⁻¹ • P) = 1 := by
  have hPP : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
  have hPP' : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    have : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [this, hP]; abel
  have e1 : ((c + x) • (1 : Matrix κ κ ℂ) + b • P) =
      (c + x) • ((1 : Matrix κ κ ℂ) - P) + (c + x + b) • P := by module
  rw [e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hP, hPP, hPP', hQQ,
    smul_zero, add_zero, zero_add, smul_smul]
  rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
  module

/-- For `T = (c+x) + b P` with `P` idempotent: `A_{k,x} = T⁻¹ = (c+x)⁻¹ (1 - P) + (c+x+b)⁻¹ P`. -/
theorem inv_projection (c x b : ℂ) (P : Matrix κ κ ℂ) (hP : P * P = P) (h1 : c + x ≠ 0)
    (h2 : c + x + b ≠ 0) :
    ((c + x) • (1 : Matrix κ κ ℂ) + b • P)⁻¹ =
      (c + x)⁻¹ • ((1 : Matrix κ κ ℂ) - P) + (c + x + b)⁻¹ • P :=
  Matrix.inv_eq_right_inv (projection_mul_inv c x b P hP h1 h2)

/-- The bracket on the two eigenspaces of the projection `P = Q'*Q'`:
`S_x = s₁ (1 - P) + s₂ P`, `s₁ = c x/(c+x)`, `s₂ = c (x+b)/(c+x+b)` (GREEN.md §4.7(b)). -/
theorem xBracket_projection (c x b : ℂ) (P : Matrix κ κ ℂ) (hP : P * P = P) (h1 : c + x ≠ 0)
    (h2 : c + x + b ≠ 0) :
    xBracket c ((c + x) • (1 : Matrix κ κ ℂ) + b • P) =
      (c * x / (c + x)) • ((1 : Matrix κ κ ℂ) - P) +
        (c * (x + b) / (c + x + b)) • P := by
  unfold xBracket
  rw [inv_projection c x b P hP h1 h2]
  have e1 : c * x / (c + x) = c - c ^ 2 * (c + x)⁻¹ := by field_simp; ring
  have e2 : c * (x + b) / (c + x + b) = c - c ^ 2 * (c + x + b)⁻¹ := by field_simp; ring
  rw [e1, e2]
  module

omit [Fintype ι] [DecidableEq ι] in
/-- **G-6(b), block form.** If `T = (c + x) + b P` with `P` idempotent on the unit lattice, `Q*Q = P_k`
and `Q* P Q = P_{k+1}` (the fine block projections), then
`H_{k,x} = H̃ + (c x/(c+x)) P_k + (c (x+b)/(c+x+b) - c x/(c+x)) P_{k+1}`, the operator of (1.7). -/
theorem xOperator_blocks (c x b : ℂ) (Q : Matrix κ ι ℂ) (P : Matrix κ κ ℂ) (hP : P * P = P)
    (h1 : c + x ≠ 0) (h2 : c + x + b ≠ 0) (Ht Pk Pk1 : Matrix ι ι ℂ) (hQ1 : Qᵀ * Q = Pk)
    (hQ2 : Qᵀ * P * Q = Pk1) :
    xOperator Ht Q c ((c + x) • (1 : Matrix κ κ ℂ) + b • P) =
      Ht + (c * x / (c + x)) • Pk +
        (c * (x + b) / (c + x + b) - c * x / (c + x)) • Pk1 := by
  unfold xOperator
  rw [xBracket_projection c x b P hP h1 h2]
  have key : ∀ α β : ℂ, Qᵀ * (α • ((1 : Matrix κ κ ℂ) - P) + β • P) * Q =
      α • (Qᵀ * Q) + (β - α) • (Qᵀ * P * Q) := by
    intro α β
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    module
  rw [key, hQ1, hQ2, ← add_assoc]

/-! ### The constrained inverse -/

/-- `E` embeds `ker B`: `B E = 0`, `E` injective and every `v` with `B v = 0` is `E w`. -/
structure IsKernelEmbedding (B : Matrix σ ι ℂ) (E : Matrix ι ρ ℂ) : Prop where
  comp_zero : B * E = 0
  injective : Function.Injective E.mulVec
  surj : ∀ v, B *ᵥ v = 0 → ∃ w, v = E *ᵥ w

/-- The projection `Π = G B* (B G B*)⁻¹ B G` (`B*` is the transpose; GREEN.md (1.8')). -/
noncomputable def constraintPi (G : Matrix ι ι ℂ) (B : Matrix σ ι ℂ) : Matrix ι ι ℂ :=
  G * Bᵀ * (B * G * Bᵀ)⁻¹ * B * G

omit [DecidableEq ι] [DecidableEq σ] [Fintype σ] [DecidableEq ρ] in
theorem IsKernelEmbedding.cancel {B : Matrix σ ι ℂ} {E : Matrix ι ρ ℂ} (hE : IsKernelEmbedding B E)
    {τ : Type*} {Y Z : Matrix ρ τ ℂ} (h : E * Y = E * Z) : Y = Z := by
  ext r j
  have := congrFun (hE.injective (a₁ := fun s => Y s j) (a₂ := fun s => Z s j) (by
    ext i
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)) r
  exact this

omit [DecidableEq ι] [DecidableEq ρ] [Fintype σ] [DecidableEq σ] in
theorem IsKernelEmbedding.factor {B : Matrix σ ι ℂ} {E : Matrix ι ρ ℂ} (hE : IsKernelEmbedding B E)
    {τ : Type*} {N : Matrix ι τ ℂ} (h : B * N = 0) : ∃ K : Matrix ρ τ ℂ, N = E * K := by
  have hcol : ∀ j, ∃ w, (fun i => N i j) = E *ᵥ w := fun j => by
    refine hE.surj _ ?_
    ext s
    have := congrFun (congrFun h s) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  choose w hw using hcol
  refine ⟨Matrix.of fun r j => w j r, ?_⟩
  ext i j
  have := congrFun (hw j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/-- **N-4, the constrained inverse.** Let `G H = 1`, `B G B*` invertible and `E` an embedding of
`ker B`. Then `E* H E` is invertible and `E (E* H E)⁻¹ E* = G - Π`. -/
theorem constrained_green_eq (G H : Matrix ι ι ℂ) (hGH : G * H = 1) (B : Matrix σ ι ℂ)
    (E : Matrix ι ρ ℂ) (hE : IsKernelEmbedding B E) (hS : IsUnit (B * G * Bᵀ)) :
    IsUnit (Eᵀ * H * E) ∧ E * (Eᵀ * H * E)⁻¹ * Eᵀ = G - constraintPi G B := by
  have hSS : (B * G * Bᵀ) * (B * G * Bᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hS)
  have hSS' : (B * G * Bᵀ)⁻¹ * (B * G * Bᵀ) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hS)
  set N := G - constraintPi G B with hN
  have hBN : B * N = 0 := by
    rw [hN, constraintPi, Matrix.mul_sub]
    have : B * (G * Bᵀ * (B * G * Bᵀ)⁻¹ * B * G) = B * G := by
      simp only [← Matrix.mul_assoc]
      rw [show B * G * Bᵀ * (B * G * Bᵀ)⁻¹ = 1 from hSS, Matrix.one_mul]
    rw [this, sub_self]
  have hNB : N * Bᵀ = 0 := by
    rw [hN, constraintPi, Matrix.sub_mul]
    have : G * Bᵀ * (B * G * Bᵀ)⁻¹ * B * G * Bᵀ = G * Bᵀ := by
      calc _ = G * Bᵀ * ((B * G * Bᵀ)⁻¹ * (B * G * Bᵀ)) := by simp only [Matrix.mul_assoc]
        _ = G * Bᵀ := by rw [hSS', Matrix.mul_one]
    rw [this, sub_self]
  have hNHE : N * H * E = E := by
    have h1 : N * H = 1 - G * Bᵀ * (B * G * Bᵀ)⁻¹ * B := by
      rw [hN, constraintPi, Matrix.sub_mul, hGH]
      simp only [Matrix.mul_assoc, hGH, Matrix.mul_one]
    rw [h1, Matrix.sub_mul, Matrix.one_mul]
    have : G * Bᵀ * (B * G * Bᵀ)⁻¹ * B * E = 0 := by
      rw [Matrix.mul_assoc, hE.comp_zero, Matrix.mul_zero]
    rw [this, sub_zero]
  obtain ⟨K1, hK1⟩ := hE.factor hBN
  have hK1B : K1 * Bᵀ = 0 := by
    refine hE.cancel (Y := K1 * Bᵀ) (Z := 0) ?_
    rw [← Matrix.mul_assoc, ← hK1, hNB, Matrix.mul_zero]
  have hBK : B * K1ᵀ = 0 := by
    have := congrArg Matrix.transpose hK1B
    simpa [Matrix.transpose_mul] using this
  obtain ⟨K3, hK3⟩ := hE.factor hBK
  have hK1' : K1 = K3ᵀ * Eᵀ := by
    have := congrArg Matrix.transpose hK3
    simpa [Matrix.transpose_mul] using this
  have hNE : N = E * (K3ᵀ * Eᵀ) := by rw [hK1, hK1']
  have h1 : K3ᵀ * (Eᵀ * H * E) = 1 := by
    refine hE.cancel (Y := K3ᵀ * (Eᵀ * H * E)) (Z := 1) ?_
    calc E * (K3ᵀ * (Eᵀ * H * E)) = (E * (K3ᵀ * Eᵀ)) * H * E := by simp only [Matrix.mul_assoc]
      _ = N * H * E := by rw [hNE]
      _ = E * (1 : Matrix ρ ρ ℂ) := by rw [hNHE, Matrix.mul_one]
  have h2 : (Eᵀ * H * E) * K3ᵀ = 1 := mul_eq_one_comm.1 h1
  have hU : IsUnit (Eᵀ * H * E) := (Matrix.isUnit_iff_isUnit_det _).2
    (Matrix.isUnit_det_of_right_inverse h2)
  refine ⟨hU, ?_⟩
  have hinv : (Eᵀ * H * E)⁻¹ = K3ᵀ := Matrix.inv_eq_right_inv h2
  rw [hinv, Matrix.mul_assoc]
  exact hNE.symm

/-- **G-6(b'), the constrained covariance.** With `H₀ = H̃ + c Q*Q`, `G_c = E (E* H₀ E)⁻¹ E*` and
`Π_{k,x} = G_{k,x} B* (B G_{k,x} B*)⁻¹ B G_{k,x}`:
`(T - c² Q G_c Q*)⁻¹ = A + c² A Q (G_{k,x} - Π_{k,x}) Q* A`. -/
theorem xVariant_constrained_reduction (c : ℂ) (Q : Matrix κ ι ℂ) (Ht : Matrix ι ι ℂ)
    (T : Matrix κ κ ℂ) (hT : IsUnit T) (B : Matrix σ ι ℂ) (E : Matrix ι ρ ℂ)
    (hE : IsKernelEmbedding B E) (hH' : IsUnit (Eᵀ * (Ht + c • (Qᵀ * Q)) * E))
    (hHx : IsUnit (xOperator Ht Q c T)) (hS : IsUnit (B * xGreen Ht Q c T * Bᵀ)) :
    (T - c ^ 2 • (Q * (E * (Eᵀ * (Ht + c • (Qᵀ * Q)) * E)⁻¹ * Eᵀ) * Qᵀ))⁻¹ =
      T⁻¹ + c ^ 2 • (T⁻¹ * Q * (xGreen Ht Q c T - constraintPi (xGreen Ht Q c T) B) * Qᵀ * T⁻¹) := by
  have hGH : xGreen Ht Q c T * xOperator Ht Q c T = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hHx)
  obtain ⟨hM, hEq⟩ := constrained_green_eq (xGreen Ht Q c T) (xOperator Ht Q c T) hGH B E hE hS
  have hD : Eᵀ * (Ht + c • (Qᵀ * Q)) * E - c ^ 2 • ((Eᵀ * Qᵀ) * T⁻¹ * (Q * E)) =
      Eᵀ * xOperator Ht Q c T * E := by
    rw [xOperator_eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hW := woodbury_inv_eq c (Q * E) (Eᵀ * Qᵀ) T (Eᵀ * (Ht + c • (Qᵀ * Q)) * E) hT hH'
    (by rw [hD]; exact hM)
  rw [hD] at hW
  have e1 : Q * (E * (Eᵀ * (Ht + c • (Qᵀ * Q)) * E)⁻¹ * Eᵀ) * Qᵀ =
      Q * E * (Eᵀ * (Ht + c • (Qᵀ * Q)) * E)⁻¹ * (Eᵀ * Qᵀ) := by
    simp only [Matrix.mul_assoc]
  rw [e1, hW, ← hEq]
  congr 2
  simp only [Matrix.mul_assoc]

section Bridge

variable {ι' : Type*} [Fintype ι'] [DecidableEq ι'] {N : ℕ}

/-- The constrained operator `Π` of `Balaban/Multiscale/Constrained.lean` (W8c) is `constraintPi` of the
componentwise lift `liftOp N A` with the constraint `B = (fieldMul φ₀)ᵀ`, i.e. `B v = φ₀ · v`. -/
theorem constrainedOp_eq_constraintPi (A : Matrix ι' ι' ℂ) (φ : ι' → Fin N → ℂ) :
    constrainedOp A φ = constraintPi (liftOp N A) (fieldMul φ)ᵀ := by
  unfold constrainedOp constraintPi constraintForm
  simp only [Matrix.transpose_transpose, Matrix.mul_assoc]

end Bridge

end Balaban.Multiscale
