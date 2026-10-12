/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ExpansionLocal
public import Balaban.Background.Equivariance
public import Balaban.Background.EquivarianceDomain

/-!
# `O(N)`-invariance of the interaction `V^{(k)}` and of its block terms (FLUCTUATION Lemma 2.3)

For a complex orthogonal `R` (`Rᵀ R = 1`) acting on the base field `φ₁`, the data tangent `ψ'` and
the field `φ'`, the interaction `V^{(k)}(ψ') = ½⟨α¹, φ'·φ'⟩ + ½⟨φ₂, H_k φ₂⟩` is invariant
(`interactionV_rot`), as are its density (`interactionDensity_rot`) and its block terms
`V^{(k)}(z)` (`interactionBlock_rot`).  The ingredients are the covariance of the linear
responses `φ¹ = (G_k - Π_k) S` and `α¹` (`phiOne_rot`, `alphaOne_rot`): the constraint form
`φ_{k+1} · G_k φ_{k+1}` is invariant and the constrained operator `Π_k` is conjugated by the
rotation lifted to `Ω₁ × [N]` (`rotLift`).  The multiplier `α_{k+1}` is a scalar field and does
not rotate.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Fluctuation
open Balaban.Multiscale Balaban.Background Finset Matrix

section RotLift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The rotation `R` of the `Fin N` index as a matrix on `ι × Fin N`. -/
def rotLift (R : Matrix (Fin N) (Fin N) ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  fun p q => if p.1 = q.1 then R p.2 q.2 else 0

theorem rotLift_mulVec (R : Matrix (Fin N) (Fin N) ℂ) (φ : ι × Fin N → ℂ) :
    rotLift R *ᵥ φ = rotFld R φ := by
  funext p
  simp only [mulVec, dotProduct, rotLift, Fintype.sum_prod_type, rotFld]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro y _ hy; simp [Ne.symm hy]
  · simp

theorem rotLift_mul (R S : Matrix (Fin N) (Fin N) ℂ) :
    (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * rotLift S = rotLift (R * S) := by
  ext p q
  simp only [mul_apply, rotLift, Fintype.sum_prod_type]
  by_cases h : p.1 = q.1
  · simp only [h, ↓reduceIte]
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro y _ hy; simp [hy]
    · simp
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hy : p.1 = y
    · have : ¬ y = q.1 := fun e => h (hy.trans e)
      simp [hy, this]
    · simp [hy]

theorem rotLift_one : (rotLift (1 : Matrix (Fin N) (Fin N) ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ) = 1 := by
  ext p q
  simp only [rotLift, one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

theorem rotLift_transpose (R : Matrix (Fin N) (Fin N) ℂ) :
    (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ)ᵀ = rotLift Rᵀ := by
  ext p q
  simp only [transpose_apply, rotLift]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

theorem liftOp_mul_rotLift (A : Matrix ι ι ℂ) (R : Matrix (Fin N) (Fin N) ℂ) :
    liftOp N A * (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) = rotLift R * liftOp N A := by
  ext p r
  simp only [mul_apply, liftOp, rotLift, Fintype.sum_prod_type]
  have e1 : ∑ y, ∑ j, (if p.2 = j then A p.1 y else 0) * (if y = r.1 then R j r.2 else 0) =
      A p.1 r.1 * R p.2 r.2 := by
    rw [Finset.sum_eq_single r.1]
    · rw [Finset.sum_eq_single p.2]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    · intro y _ hy; simp [hy]
    · simp
  have e2 : ∑ y, ∑ j, (if p.1 = y then R p.2 j else 0) * (if j = r.2 then A y r.1 else 0) =
      R p.2 r.2 * A p.1 r.1 := by
    rw [Finset.sum_eq_single p.1]
    · rw [Finset.sum_eq_single r.2]
      · simp
      · intro j _ hj; simp [hj]
      · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  rw [e1, e2, mul_comm]


theorem fieldMul_rot (R : Matrix (Fin N) (Fin N) ℂ) (φ : ι → Fin N → ℂ) :
    fieldMul (fun x => R *ᵥ φ x) = (rotLift R : Matrix (ι × Fin N) (ι × Fin N) ℂ) * fieldMul φ := by
  ext p y
  simp only [fieldMul, mul_apply, rotLift, Fintype.sum_prod_type, mulVec, dotProduct]
  rw [Finset.sum_eq_single p.1]
  · by_cases h : p.1 = y
    · simp only [h, ↓reduceIte]
    · simp [h]
  · intro z _ hz; simp [Ne.symm hz]
  · simp

theorem constraintForm_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (A : Matrix ι ι ℂ)
    (φ : ι → Fin N → ℂ) :
    constraintForm A (fun x => R *ᵥ φ x) = constraintForm A φ := by
  unfold constraintForm
  rw [fieldMul_rot, Matrix.transpose_mul, rotLift_transpose]
  have h1 : (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) * rotLift R = 1 := by
    rw [rotLift_mul, hR, rotLift_one]
  have h2 := liftOp_mul_rotLift (N := N) A R
  set RL : Matrix (ι × Fin N) (ι × Fin N) ℂ := rotLift R with hRL
  set RT : Matrix (ι × Fin N) (ι × Fin N) ℂ := rotLift Rᵀ with hRT
  set F := fieldMul φ with hF
  set LA := liftOp N A with hLA
  calc Fᵀ * RT * LA * (RL * F) = Fᵀ * (RT * (LA * RL)) * F := by simp only [Matrix.mul_assoc]
    _ = Fᵀ * (RT * (RL * LA)) * F := by rw [h2]
    _ = Fᵀ * LA * F := by
        rw [← Matrix.mul_assoc RT, h1, Matrix.one_mul]

theorem constrainedOp_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (A : Matrix ι ι ℂ)
    (φ : ι → Fin N → ℂ) :
    constrainedOp A (fun x => R *ᵥ φ x) =
      rotLift R * constrainedOp A φ * (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) := by
  unfold constrainedOp
  rw [constraintForm_rot hR, fieldMul_rot, Matrix.transpose_mul, rotLift_transpose]
  have h1 := liftOp_mul_rotLift (N := N) A R
  have h2 : (rotLift Rᵀ : Matrix (ι × Fin N) (ι × Fin N) ℂ) * liftOp N A =
      liftOp N A * rotLift Rᵀ := (liftOp_mul_rotLift (N := N) A Rᵀ).symm
  set RL : Matrix (ι × Fin N) (ι × Fin N) ℂ := rotLift R with hRL
  set RT : Matrix (ι × Fin N) (ι × Fin N) ℂ := rotLift Rᵀ with hRT
  set F := fieldMul φ with hF
  set LA := liftOp N A with hLA
  set C := constraintForm A φ with hC
  calc LA * (RL * F) * C⁻¹ * (Fᵀ * RT) * LA
      = (LA * RL) * F * C⁻¹ * Fᵀ * (RT * LA) := by simp only [Matrix.mul_assoc]
    _ = (RL * LA) * F * C⁻¹ * Fᵀ * (LA * RT) := by rw [h1, h2]
    _ = _ := by simp only [Matrix.mul_assoc]

end RotLift

section Interaction

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

theorem fieldBase_rot (h : Precedes G G') (R : Matrix (Fin N) (Fin N) ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    fieldBase h (rotFld R φ₁) = fun x => R *ᵥ fieldBase h φ₁ x := rfl

theorem qStar_rot (R : Matrix (Fin N) (Fin N) ℂ) (a : ℕ → ℝ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    qStar G a (fun y => R *ᵥ ψ' y) = rotFld R (qStar G a ψ') := by
  funext p
  simp only [qStar, rotFld, mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem phiOne_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Precedes G G')
    (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (S : G.Ω 1 × Fin N → ℂ) :
    phiOne h a ν α₁ (rotFld R φ₁) (rotFld R S) = rotFld R (phiOne h a ν α₁ φ₁ S) := by
  unfold phiOne
  rw [fieldBase_rot, constrainedOp_rot hR, ← rotLift_mulVec, ← rotLift_mulVec]
  have h1 : (rotLift Rᵀ : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) * rotLift R = 1 := by
    rw [rotLift_mul, hR, rotLift_one]
  have hmat : (liftOp N (opHk h a ν α₁)⁻¹ - rotLift R * constrainedOp (opHk h a ν α₁)⁻¹
      (fieldBase h φ₁) * rotLift Rᵀ) * rotLift R =
      rotLift R * (liftOp N (opHk h a ν α₁)⁻¹ - constrainedOp (opHk h a ν α₁)⁻¹
        (fieldBase h φ₁)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, liftOp_mul_rotLift, Matrix.mul_assoc _ (rotLift Rᵀ),
      h1, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, hmat, ← Matrix.mulVec_mulVec]

theorem alphaOne_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Precedes G G')
    (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (S : G.Ω 1 × Fin N → ℂ) :
    alphaOne h a ν α₁ (rotFld R φ₁) (rotFld R S) = alphaOne h a ν α₁ φ₁ S := by
  unfold alphaOne
  rw [fieldBase_rot, constraintForm_rot hR, fieldMul_rot, ← rotLift_mulVec,
    Matrix.transpose_mul, rotLift_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  have h1 : (rotLift Rᵀ : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) * rotLift R = 1 := by
    rw [rotLift_mul, hR, rotLift_one]
  have h2 := liftOp_mul_rotLift (N := N) (opHk h a ν α₁)⁻¹ R
  set RL : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ := rotLift R with hRL
  set RT : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ := rotLift Rᵀ with hRT
  set LA := liftOp N (opHk h a ν α₁)⁻¹ with hLA
  have key : ∀ X : Matrix (G.Ω 1) (G.Ω 1 × Fin N) ℂ, X * RT * LA * RL = X * LA := by
    intro X
    calc X * RT * LA * RL = X * RT * (LA * RL) := by simp only [Matrix.mul_assoc]
      _ = X * (RT * RL) * LA := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = X * LA := by rw [h1, Matrix.mul_one]
  rw [← Matrix.mul_assoc _ (fieldMul (fieldBase h φ₁))ᵀ, key, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]


theorem interactionDensity_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Precedes G G')
    (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) :
    interactionDensity h a ν α₁ (rotFld R φ₁) (fun y => R *ᵥ ψ' y) (rotFld R φ') x =
      interactionDensity h a ν α₁ φ₁ ψ' φ' x := by
  unfold interactionDensity
  rw [qStar_rot, alphaOne_rot hR, phiOne_rot hR, ← rotFld_sub, rotFld_liftOp]
  simp only [svec_rot]
  rw [bilin_vec hR, bilin_vec hR]

theorem interactionBlock_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Precedes G G')
    (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) (m : ℕ)
    (z : Torus d (N₀ * L ^ (K - m))) :
    interactionBlock h a ν α₁ (rotFld R φ₁) (fun y => R *ᵥ ψ' y) (rotFld R φ') m z =
      interactionBlock h a ν α₁ φ₁ ψ' φ' m z := by
  unfold interactionBlock
  exact Finset.sum_congr rfl fun x _ => interactionDensity_rot hR h a ν α₁ φ₁ ψ' φ' x

theorem interactionV_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (h : Precedes G G')
    (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) :
    interactionV h a ν α₁ (rotFld R φ₁) (fun y => R *ᵥ ψ' y) (rotFld R φ') =
      interactionV h a ν α₁ φ₁ ψ' φ' := by
  unfold interactionV
  rw [qStar_rot, alphaOne_rot hR, phiOne_rot hR, ← rotFld_sub, rotFld_liftOp]
  have e : pair G (rotFld R (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')))
      (rotFld R (liftOp N (opHk h a ν α₁) *ᵥ (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')))) =
      pair G (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ'))
        (liftOp N (opHk h a ν α₁) *ᵥ (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ'))) := by
    unfold pair
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact rotFld_bilin hR _ _ x
  rw [e]
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rotFld_bilin hR (ι := G.Ω 1) φ' φ' x]

end Interaction
end Balaban.Fluctuation
