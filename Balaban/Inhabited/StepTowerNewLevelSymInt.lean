/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymCov
public import Balaban.Fluctuation.LocalClassLatHat

/-!
# Covariance of the interaction `V^{(k)}` under lattice symmetries (`StepTowerNewLevelSymInt`)

For lattice symmetries `Sk` of `𝔹_k` and `Sy` of `𝔹'_k` (the same permutation `σ`) and
`h : Precedes 𝔹_k 𝔹'_k`, the linear responses `φ^{(1)}`, `α^{(1)}`, the quadratic and potential parts
of the interaction `V^{(k)}` (FLUCTUATION Lemma 2.3, P4 (2.4)) are transported:

* `opHk_sym`, `fieldBase_sym`, `constrainedOp_transport`, `constraintForm_transport`;
* `phiOne_sym`, `alphaOne_sym`, `qStar_sym`;
* `interactionV_sym`: `V^{(k)}(σ α, σ φ; σ ψ', σ φ') = V^{(k)}(α, φ; ψ', φ')`.
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence
  Balaban.Localization.DetDecCov Matrix

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [Fintype ι] in
theorem fieldMul_transport (e : ι ≃ ι) (φ φ' : ι → Fin N → ℂ) (hφ : ∀ x i, φ' (e x) i = φ x i) :
    fieldMul φ' = (fieldMul φ).submatrix (e.prodCongr (Equiv.refl (Fin N))).symm e.symm := by
  ext ⟨x', i⟩ y'
  obtain ⟨x, rfl⟩ := e.surjective x'
  obtain ⟨y, rfl⟩ := e.surjective y'
  simp [fieldMul, hφ]

theorem constraintForm_transport (e : ι ≃ ι) (A : Matrix ι ι ℂ) (φ φ' : ι → Fin N → ℂ)
    (hφ : ∀ x i, φ' (e x) i = φ x i) :
    constraintForm (rm e A) φ' = rm e (constraintForm A φ) := by
  unfold constraintForm
  rw [fieldMul_transport e φ φ' hφ, DetDecCov.liftOp_rm]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

theorem constrainedOp_transport (e : ι ≃ ι) (A : Matrix ι ι ℂ) (φ φ' : ι → Fin N → ℂ)
    (hφ : ∀ x i, φ' (e x) i = φ x i) :
    constrainedOp (rm e A) φ' =
      rm (e.prodCongr (Equiv.refl (Fin N))) (constrainedOp A φ) := by
  have hf := fieldMul_transport e φ φ' hφ
  unfold constrainedOp
  rw [constraintForm_transport e A φ φ' hφ, hf, DetDecCov.liftOp_rm, ← rm_inv]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

theorem mulVec_rm_fun {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ κ) (M : Matrix κ κ ℂ)
    (v : κ → ℂ) : rm e M *ᵥ (fun q => v (e.symm q)) = fun q => (M *ᵥ v) (e.symm q) := by
  funext q
  obtain ⟨p, rfl⟩ := e.surjective q
  rw [Equiv.symm_apply_apply]
  exact rm_mulVec_apply e M v p

end General

section Interaction

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
variable {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (Sk : LatSymm G G σ) (Sy : LatSymm G' G' σ) (h : Precedes G G')

theorem restrictα_sym (α₁ : G'.Ω 1 → ℂ) :
    h.restrictα (Sy.mul α₁) = Sk.mul (h.restrictα α₁) := by
  funext x
  show α₁ (Sy.Ω1Equiv.symm (h.incl x)) = α₁ (h.incl (Sk.Ω1Equiv.symm x))
  congr 1

theorem restrictφ_sym (φ₁ : G'.Ω 1 × Fin N → ℂ) :
    h.restrictφ (Sy.fld φ₁) = Sk.fld (h.restrictφ φ₁) := by
  funext q
  show φ₁ (Sy.Ω1Equiv.symm (h.incl q.1), q.2) = φ₁ (h.incl (Sk.Ω1Equiv.symm q.1), q.2)
  congr 2

theorem opHk_sym (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) :
    opHk h a ν (Sy.mul α₁) = rm Sk.Ω1Equiv (opHk h a ν α₁) := by
  unfold opHk
  rw [restrictα_sym Sk Sy h, rm_dirichlet Sk]

theorem fieldBase_sym (φ₁ : G'.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    fieldBase h (Sy.fld φ₁) (Sk.Ω1Equiv x) i = fieldBase h φ₁ x i := by
  show h.restrictφ (Sy.fld φ₁) (Sk.Ω1Equiv x, i) = h.restrictφ φ₁ (x, i)
  rw [restrictφ_sym Sk Sy h, Sk.fld_apply]

theorem fld_eq_comp (v : G.Ω 1 × Fin N → ℂ) :
    Sk.fld v = fun q => v ((Sk.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm q) := rfl

theorem phiOne_sym (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (S : G.Ω 1 × Fin N → ℂ) :
    phiOne h a ν (Sy.mul α₁) (Sy.fld φ₁) (Sk.fld S) = Sk.fld (phiOne h a ν α₁ φ₁ S) := by
  unfold phiOne
  rw [opHk_sym Sk Sy h, ← rm_inv, constrainedOp_transport Sk.Ω1Equiv _ _ _
    (fieldBase_sym Sk Sy h φ₁), DetDecCov.liftOp_rm, ← rm_sub, fld_eq_comp, fld_eq_comp]
  exact mulVec_rm_fun _ _ _

theorem alphaOne_sym (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (S : G.Ω 1 × Fin N → ℂ) :
    alphaOne h a ν (Sy.mul α₁) (Sy.fld φ₁) (Sk.fld S) = Sk.mul (alphaOne h a ν α₁ φ₁ S) := by
  unfold alphaOne
  have hφ := fieldBase_sym Sk Sy h φ₁
  rw [opHk_sym Sk Sy h, ← rm_inv, constraintForm_transport Sk.Ω1Equiv _ _ _ hφ, ← rm_inv,
    fieldMul_transport Sk.Ω1Equiv _ _ hφ, Matrix.transpose_submatrix, DetDecCov.liftOp_rm,
    fld_eq_comp, mulVec_rm_fun, Matrix.submatrix_mulVec_equiv]
  have e1 : ((fun q => (liftOp N (opHk h a ν α₁)⁻¹ *ᵥ S)
      ((Sk.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm q)) ∘
      ⇑(Sk.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm.symm) =
      liftOp N (opHk h a ν α₁)⁻¹ *ᵥ S := by
    funext q
    simp [Equiv.prodCongr_apply, Prod.map]
  rw [e1]
  exact mulVec_rm_fun _ _ _

theorem qStar_sym (a : ℕ → ℝ) (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    qStar G a (symSite σ ψ') = Sk.fld (qStar G a ψ') := by
  funext p
  obtain ⟨x, i⟩ := p
  show _ = qStar G a ψ' (Sk.Ω1Equiv.symm x, i)
  have h1 : G.layerIndex (σ.symm (x : CTorus d L N₁ m₁ (k + 1))) =
      G.layerIndex (x : CTorus d L N₁ m₁ (k + 1)) := by
    have := Sk.layerIndex_eq (σ.symm (x : CTorus d L N₁ m₁ (k + 1)))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  simp only [qStar, symSite]
  show _ = ((a (G.layerIndex (σ.symm (x : CTorus d L N₁ m₁ (k + 1)))) /
    ((L : ℝ) ^ G.layerIndex (σ.symm (x : CTorus d L N₁ m₁ (k + 1)))) ^ 2 : ℝ) : ℂ) * _
  rw [h1]
  rfl

theorem liftOp_mulVec_fld (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (w : G.Ω 1 × Fin N → ℂ) :
    liftOp N (rm Sk.Ω1Equiv A) *ᵥ Sk.fld w = Sk.fld (liftOp N A *ᵥ w) := by
  rw [DetDecCov.liftOp_rm, fld_eq_comp, fld_eq_comp]
  exact mulVec_rm_fun _ _ _

theorem pair_fld (u v : G.Ω 1 × Fin N → ℂ) : pair G (Sk.fld u) (Sk.fld v) = pair G u v := by
  unfold pair
  rw [← Equiv.sum_comp (Sk.Ω1Equiv.prodCongr (Equiv.refl (Fin N)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [LatSymm.fld]

theorem interactionV_sym (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) :
    interactionV h a ν (Sy.mul α₁) (Sy.fld φ₁) (symSite σ ψ') (Sk.fld φ') =
      interactionV h a ν α₁ φ₁ ψ' φ' := by
  unfold interactionV
  rw [qStar_sym Sk, phiOne_sym Sk Sy h, alphaOne_sym Sk Sy h]
  have hsub : Sk.fld φ' - Sk.fld (phiOne h a ν α₁ φ₁ (qStar G a ψ')) =
      Sk.fld (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')) := rfl
  rw [hsub, opHk_sym Sk Sy h, liftOp_mulVec_fld Sk, pair_fld]
  have hsum : ∀ β : G.Ω 1 → ℂ, ∑ x, Sk.mul β x * ∑ i, Sk.fld φ' (x, i) * Sk.fld φ' (x, i) =
      ∑ x, β x * ∑ i, φ' (x, i) * φ' (x, i) := fun β => by
    rw [← Equiv.sum_comp Sk.Ω1Equiv]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [LatSymm.mul_apply, LatSymm.fld_apply]
  rw [hsum]

end Interaction
end Balaban.Inhabited.StepSym
