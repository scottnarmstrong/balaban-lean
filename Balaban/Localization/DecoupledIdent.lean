/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSqrt
public import Balaban.Multiscale.XVariantIdentities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# I-4c (iv), algebraic part: `C_x(1) = (x + 𝒜)⁻¹`

At the decoupling vector `s ≡ 1` the decoupled operator `Ĝ_{k,x,1} = H_{k,x}⁻¹`
(`Balaban.Localization.Gsx_one`) and `Π_{x,1}` is the constrained operator of GREEN.md (1.8')
(`constrainedOp_eq`). The landed x-variant reduction
(`Balaban.Multiscale.xVariant_constrained_reduction`, G-6(b')) then identifies the covariance
`C_x(1)` with the inverse of `x + 𝒜`, where

`𝒜 = a_k + b P - a_k² L^{-2k} Q (G_D - Π_D) Q*  =  a L⁻² Q*Q + Δ^{(k)}`

is the operator of GREEN.md §1 with the constrained `Δ^{(k)} = a_k - a_k² L^{-2k} Q (G_D - Π_D) Q*`
(`G_D = H₀⁻¹`, `H₀ = H̃ + a_k L^{-2k} Q*Q|_{Ω_{k+1}}` the Dirichlet operator of `𝔹_k`).
`x ↦ 𝒜` is `x`-independent.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-! ### The block decomposition of `H_{k,x}` -/

section Blocks

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- The `x`-independent part `H̃` of the x-variant operator. -/
noncomputable def xHt (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((latticeLaplacian d (N₁ * L ^ m₁ * L ^ (k + 1)) ν + xAvg0 G a).map
    (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α

/-- `P_k = Q*Q` on `Ω₁`, the block projection of side `L^k` in the top layer. -/
noncomputable def Pk : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((layerBlockMatrix G (k + 1) k).map (algebraMap ℝ ℂ)) (G.Ω 1)

/-- `P_{k+1} = Q*PQ` on `Ω₁`, the block projection of side `L^{k+1}` in the top layer. -/
noncomputable def Pk1 : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((layerBlockMatrix G (k + 1) (k + 1)).map (algebraMap ℝ ℂ)) (G.Ω 1)

variable {G}

theorem xDirichlet_eq_blocks (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) :
    xDirichletOperator G a aT x ν α = xHt G a ν α +
      ((xS1 (a k) x / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) • Pk G +
      (((xS2 (a k) (aT / (L : ℝ) ^ 2) x - xS1 (a k) x) / ((L : ℝ) ^ k) ^ 2 : ℝ) : ℂ) • Pk1 G := by
  unfold xDirichletOperator xFullMatrix xAvgMatrix xHt xAvg0 Pk Pk1 Green.restrictOp
  ext y z
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply, smul_eq_mul, map_add, map_mul]
  split_ifs <;> simp [Complex.coe_algebraMap] <;> ring

end Blocks

/-! ### Lifting to `N`-vector fields -/

section Lift

variable {κι ι ρ : Type*}

theorem liftRect_mul [Fintype ι] (A : Matrix κι ι ℂ) (B : Matrix ι ρ ℂ) :
    liftRect N (A * B) = liftRect N A * liftRect N B := by
  ext p q
  simp only [liftRect, mul_apply, Fintype.sum_prod_type]
  by_cases h : p.2 = q.2
  · simp only [h, ↓reduceIte]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single q.2]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · simp only [h, ↓reduceIte]
    refine (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j _ => ?_).symm
    by_cases hj : p.2 = j
    · by_cases hj2 : j = q.2
      · exact absurd (hj.trans hj2) h
      · simp [hj, hj2]
    · simp [hj]

theorem liftOp_eq_liftRect (A : Matrix ι ι ℂ) : liftOp N A = liftRect N A := rfl

theorem liftRect_add (A B : Matrix κι ι ℂ) : liftRect N (A + B) = liftRect N A + liftRect N B := by
  ext p q
  by_cases h : p.2 = q.2 <;> simp [liftRect, h]

theorem liftRect_sub (A B : Matrix κι ι ℂ) : liftRect N (A - B) = liftRect N A - liftRect N B := by
  ext p q
  by_cases h : p.2 = q.2 <;> simp [liftRect, h]

theorem liftRect_smul (c : ℂ) (A : Matrix κι ι ℂ) : liftRect N (c • A) = c • liftRect N A := by
  ext p q
  by_cases h : p.2 = q.2 <;> simp [liftRect, h]

end Lift

section LiftBlocks

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ}
  {P : Matrix κι κι ℂ}

variable (G Q P) in
/-- The block identities of the unit lattice: `Q*Q = P_k` and `Q* P Q = P_{k+1}` on `Ω₁`. -/
structure IsUnitLatticeB : Prop extends IsUnitLattice G Q P where
  blk1 : Qᵀ * Q = Pk G
  blk2 : Qᵀ * P * Q = Pk1 G

omit [DecidableEq κι] in
theorem IsUnitLatticeB.blk1v (H : IsUnitLatticeB G Q P) :
    (liftRect N Q)ᵀ * liftRect N Q = liftOp N (Pk G) := by
  rw [liftRect_transpose, ← liftRect_mul, ← H.blk1]; rfl

omit [DecidableEq κι] in
theorem IsUnitLatticeB.blk2v (H : IsUnitLatticeB G Q P) :
    (liftRect N Q)ᵀ * liftOp N P * liftRect N Q = liftOp N (Pk1 G) := by
  rw [liftRect_transpose, liftOp_eq_liftRect, ← liftRect_mul, ← liftRect_mul, ← H.blk2]
  rfl

end LiftBlocks

/-! ### Kernel embeddings -/

section Kernel

open Module

theorem exists_kernelEmbedding {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (B : Matrix σ ι ℂ) : ∃ (n : ℕ) (E : Matrix ι (Fin n) ℂ), IsKernelEmbedding B E := by
  classical
  let K := LinearMap.ker B.mulVecLin
  let b := Module.finBasis ℂ K
  let E : Matrix ι (Fin (finrank ℂ K)) ℂ := Matrix.of fun i r => (b r : ι → ℂ) i
  have hE : ∀ c : Fin (finrank ℂ K) → ℂ, E *ᵥ c = ((∑ r, c r • b r : K) : ι → ℂ) := by
    intro c
    funext i
    simp [E, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine ⟨finrank ℂ K, E, ?_, ?_, ?_⟩
  · ext s r
    have hr : B *ᵥ (b r : ι → ℂ) = 0 := by
      rw [← Matrix.mulVecLin_apply]
      exact LinearMap.mem_ker.1 (b r).2
    have := congrFun hr s
    simpa [E, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  · intro w w' hww
    have h0 : E *ᵥ (w - w') = 0 := by rw [Matrix.mulVec_sub, hww, sub_self]
    rw [hE] at h0
    have h1 : (∑ r, (w - w') r • b r : K) = 0 := Subtype.ext h0
    have h2 : w - w' = 0 := by
      rw [← b.repr_sum_self (w - w'), h1]
      simp
    exact sub_eq_zero.1 h2
  · intro v hv
    have hvK : v ∈ K := by simpa [K, LinearMap.mem_ker] using hv
    refine ⟨b.repr ⟨v, hvK⟩, ?_⟩
    rw [hE]
    have := b.sum_repr ⟨v, hvK⟩
    exact (congrArg Subtype.val this).symm

end Kernel

/-! ### The constrained reduction with a unit-ness statement -/

section Reduction

variable {κ' ι' ρ σ : Type*} [Fintype κ'] [DecidableEq κ'] [Fintype ι'] [DecidableEq ι']
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- The product form of `Balaban.Multiscale.xVariant_constrained_reduction` (G-6(b')): the matrix
`T - c² Q E (E* H₀ E)⁻¹ E* Q*` times `A + c² A Q (G_{k,x} - Π_{k,x}) Q* A` is the identity, so
both are invertible. -/
theorem xVariant_constrained_mul (c : ℂ) (Q : Matrix κ' ι' ℂ) (Ht : Matrix ι' ι' ℂ)
    (T : Matrix κ' κ' ℂ) (hT : IsUnit T) (B : Matrix σ ι' ℂ) (E : Matrix ι' ρ ℂ)
    (hE : IsKernelEmbedding B E) (hH' : IsUnit (Eᵀ * (Ht + c • (Qᵀ * Q)) * E))
    (hHx : IsUnit (xOperator Ht Q c T)) (hS : IsUnit (B * xGreen Ht Q c T * Bᵀ)) :
    (T - c ^ 2 • (Q * (E * (Eᵀ * (Ht + c • (Qᵀ * Q)) * E)⁻¹ * Eᵀ) * Qᵀ)) *
      (T⁻¹ + c ^ 2 • (T⁻¹ * Q * (xGreen Ht Q c T - constraintPi (xGreen Ht Q c T) B) * Qᵀ * T⁻¹))
      = 1 := by
  have hGH : xGreen Ht Q c T * xOperator Ht Q c T = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hHx)
  obtain ⟨hM, hEq⟩ := constrained_green_eq (xGreen Ht Q c T) (xOperator Ht Q c T) hGH B E hE hS
  have hD : Eᵀ * (Ht + c • (Qᵀ * Q)) * E - c ^ 2 • ((Eᵀ * Qᵀ) * T⁻¹ * (Q * E)) =
      Eᵀ * xOperator Ht Q c T * E := by
    rw [xOperator_eq]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hW := woodbury_right_inverse c (Q * E) (Eᵀ * Qᵀ) T (Eᵀ * (Ht + c • (Qᵀ * Q)) * E) hT hH'
    (by rw [hD]; exact hM)
  rw [hD] at hW
  have e1 : Q * (E * (Eᵀ * (Ht + c • (Qᵀ * Q)) * E)⁻¹ * Eᵀ) * Qᵀ =
      Q * E * (Eᵀ * (Ht + c • (Qᵀ * Q)) * E)⁻¹ * (Eᵀ * Qᵀ) := by
    simp only [Matrix.mul_assoc]
  have e2 : T⁻¹ * Q * (xGreen Ht Q c T - constraintPi (xGreen Ht Q c T) B) * Qᵀ * T⁻¹ =
      T⁻¹ * (Q * E) * (Eᵀ * xOperator Ht Q c T * E)⁻¹ * (Eᵀ * Qᵀ) * T⁻¹ := by
    rw [← hEq]
    simp only [Matrix.mul_assoc]
  rw [e1, e2]
  exact hW

end Reduction

end Balaban.Localization
