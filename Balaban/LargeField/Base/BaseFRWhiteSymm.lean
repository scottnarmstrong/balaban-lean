/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteFirst

/-!
# Symmetry of the first-step whitening and the bilinear identity

`A_e = Q_e (H ⊗ I) Q_e + P_e` is complex symmetric (`Hᵀ = H`, `P_e = E Eᵀ`, `Q_e = 1 - P_e`), hence
`K_e = 1 - (γ/J²) A_e`, `S_R(K_e)` and `W` are symmetric, and the bilinear form
`⟨W ψ', A_e W ψ'⟩ = |ψ'|² + ⟨ψ', D_R ψ'⟩` (with `⟨a, b⟩ = ∑ a_i b_i`, no conjugation) holds for every
complex `ψ'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Balaban.Green Balaban.LargeField.Base Balaban.Multiscale
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

section Symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem liftOp_transpose (H : Matrix ι ι ℂ) : (liftOp N H)ᵀ = liftOp N Hᵀ := by
  ext p q
  simp only [Matrix.transpose_apply, liftOp]
  by_cases h : q.2 = p.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem basePart_transpose (e : ι → Fin N → ℂ) : (basePart e)ᵀ = basePart e := by
  unfold basePart
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- **`A_e` is complex symmetric** when `H` is. -/
theorem baseOp_transpose (e : ι → Fin N → ℂ) {H : Matrix ι ι ℂ} (hH : Hᵀ = H) :
    (baseOp N e H)ᵀ = baseOp N e H := by
  unfold baseOp
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, basePart_transpose, liftOp_transpose, hH, Matrix.mul_assoc]

theorem sqrtTrunc_transpose (K : Matrix ι ι ℂ) (R : ℕ) :
    (sqrtTrunc K R)ᵀ = sqrtTrunc Kᵀ R := by
  unfold sqrtTrunc
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.transpose_smul, Matrix.transpose_pow]

theorem whiteK_transpose (γ J : ℝ) {A : Matrix ι ι ℂ} (hA : Aᵀ = A) :
    (whiteK γ J A)ᵀ = whiteK γ J A := by
  unfold whiteK
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hA]

theorem whiteW_transpose (γ J : ℝ) {A : Matrix ι ι ℂ} (hA : Aᵀ = A) (R : ℕ) :
    (whiteW γ J A R)ᵀ = whiteW γ J A R := by
  unfold whiteW
  rw [Matrix.transpose_smul, sqrtTrunc_transpose, whiteK_transpose γ J hA]

/-- **The bilinear whitening identity**: for a complex symmetric `A`, every complex `ψ`,
`⟨W ψ, A W ψ⟩ = ⟨ψ, ψ⟩ + ⟨ψ, D_R ψ⟩`, `⟨a, b⟩ = ∑ a_i b_i`. -/
theorem whiteW_bilinear {γ J : ℝ} (hγ : 0 < γ) (hJ : 0 < J) {A : Matrix ι ι ℂ} (hA : Aᵀ = A)
    (R : ℕ) (ψ : ι → ℂ) :
    (whiteW γ J A R *ᵥ ψ) ⬝ᵥ (A *ᵥ (whiteW γ J A R *ᵥ ψ)) =
      ψ ⬝ᵥ ψ + ψ ⬝ᵥ (whiteDefect (whiteK γ J A) R *ᵥ ψ) := by
  have h := whiteW_mul_mul_whiteW hγ hJ A R
  have e1 : (whiteW γ J A R *ᵥ ψ) ⬝ᵥ (A *ᵥ (whiteW γ J A R *ᵥ ψ)) =
      ψ ⬝ᵥ ((whiteW γ J A R)ᵀ * A * whiteW γ J A R) *ᵥ ψ := by
    have h1 : ∀ (M : Matrix ι ι ℂ) (x : ι → ℂ), (M *ᵥ ψ) ⬝ᵥ x = ψ ⬝ᵥ (Mᵀ *ᵥ x) := fun M x => by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [e1, whiteW_transpose γ J hA, h, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]

end Symm

section First

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)
  {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {s : FineBond d L N₀ → ℂ} (e : G.Ω 1 → Fin N → ℝ)

/-- **`A_e(s)` is complex symmetric.** -/
theorem baseOp_symm_first : (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s))ᵀ =
    baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s) :=
  baseOp_transpose _ (by ext z y; exact baseHamiltonian_symm G a ν α s y z)

/-- `W` of the first step is symmetric. -/
theorem baseWhiteW_transpose (R : ℕ) : (baseWhiteW G a ν α s e R)ᵀ = baseWhiteW G a ν α s e R :=
  whiteW_transpose _ _ (baseOp_symm_first G e) R

/-- **The bilinear whitening identity of the first step**: for every complex `ψ'`,
`⟨W ψ', A_e W ψ'⟩ = ⟨ψ', ψ'⟩ + ⟨ψ', D_R ψ'⟩` (`⟨a, b⟩ = ∑ a_i b_i`). -/
theorem baseWhite_bilinear (hν : 0 ≤ ν) (R : ℕ) (ψ : G.Ω 1 × Fin N → ℂ) :
    (baseWhiteW G a ν α s e R *ᵥ ψ) ⬝ᵥ
        (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s) *ᵥ
          (baseWhiteW G a ν α s e R *ᵥ ψ)) =
      ψ ⬝ᵥ ψ + ψ ⬝ᵥ (whiteDefect (baseWhiteK G a ν α s e) R *ᵥ ψ) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact whiteW_bilinear (half_pos (baseCoercivity_pos hL)) (baseJ_pos (d := d) hν)
    (baseOp_symm_first G e) R ψ

end First

end Balaban.LargeField.FRWhite
