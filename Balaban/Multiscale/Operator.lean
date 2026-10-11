/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.GeneratingSet
public import Balaban.Green.Coercivity
public import Balaban.Green.Restriction

/-!
# The multiscale Dirichlet operator `H_D(α)` (GREEN.md §1.2–§1.3)

On the fine torus `Torus d (N₀ * L ^ k)` with unit lattice spacing (see the dictionary in
`Balaban/Multiscale/GeneratingSet.lean`):

* `Balaban.Multiscale.avgMatrix G a`: the multiscale averaging form `Q* a Q` of (1.4), the real
  matrix `∑_{j=1}^k a_j L⁻²ʲ · 1_{layer j} P_j 1_{layer j}` with `P_j = blockProjMatrix` the
  `j`-block projection. Its quadratic form is `∑_j a_j L⁻²ʲ ∑_{B ⊂ layer j} ‖P_B u‖²`
  (`Balaban.Multiscale.avgMatrix_quadratic`).
* `Balaban.Multiscale.fullMatrix G a ν = -Δ + ν + Q* a Q` on the whole torus.
* `Balaban.Multiscale.dirichletOperator G a ν α`: `H_D(α)` of (1.6) as a complex matrix on `Ω₁`:
  the restriction (`Balaban.Green.restrictOp`) of `-Δ + ν + Q* a Q` to `Ω₁` (this is the Dirichlet
  Laplacian `χ_Ω₁ Δ χ_Ω₁` of GREEN.md §1.1, `-Δ^D_{Ω₁}`), plus the diagonal `α : Ω₁ → ℂ`.
* `Balaban.Multiscale.zeroExt`: the zero extension `ũ` of a field on `Ω₁`;
  `Balaban.Multiscale.reQuad_dirichletOperator` computes the real part of the form on `ũ`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The multiscale weights satisfy (1.5): `a_j ∈ [1/2, 2]` for `1 ≤ j ≤ k`. -/
def IsAdmissibleWeights (k : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → a j ∈ Set.Icc (1 / 2 : ℝ) 2

section Operator

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The matrix `1_{layer j} P_j 1_{layer j}`, `P_j` the `j`-block projection. -/
noncomputable def layerProjMatrix (j : ℕ) :
    Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ :=
  fun x x' => if x ∈ G.layer j ∧ x' ∈ G.layer j then
    blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) x x' else 0

/-- The multiscale averaging form `Q* a Q` of (1.4) (fine unit spacing, so that the weight on
layer `j` is `a_j ℓ_j⁻² = a_j L⁻²ʲ`). -/
noncomputable def avgMatrix (a : ℕ → ℝ) :
    Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ :=
  ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) • layerProjMatrix G j

/-- The real matrix `-Δ + ν + Q* a Q` on the whole fine torus. -/
noncomputable def fullMatrix (a : ℕ → ℝ) (ν : ℝ) :
    Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ :=
  latticeLaplacian d (N₀ * L ^ k) ν + avgMatrix G a

/-- **The Dirichlet operator** `H_D(α) = -Δ^D_{Ω₁} + Q* a Q + ν + α` of (1.6), as a complex matrix on
`Ω₁`. -/
noncomputable def dirichletOperator (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((fullMatrix G a ν).map (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α

/-- Quadratic form of the layer-`j` matrix: `ψᵀ P_j ψ` for `ψ = 1_{layer j} φ`. -/
theorem layerProjMatrix_quadratic (j : ℕ) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    φ ⬝ᵥ layerProjMatrix G j *ᵥ φ =
      (fun x => if x ∈ G.layer j then φ x else 0) ⬝ᵥ
        blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) *ᵥ
          (fun x => if x ∈ G.layer j then φ x else 0) := by
  simp only [dotProduct, Matrix.mulVec, layerProjMatrix]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ G.layer j
  · simp only [hx, true_and, ite_true]
    congr 1
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hx' : x' ∈ G.layer j <;> simp [hx']
  · simp [hx]

/-- The weight vector of layer `j` for the quadratic form: `ψ_j = 1_{layer j} φ`. -/
noncomputable def layerPart (j : ℕ) (φ : Torus d (N₀ * L ^ k) → ℝ) : Torus d (N₀ * L ^ k) → ℝ :=
  fun x => if x ∈ G.layer j then φ x else 0

/-- Quadratic form of the averaging matrix: `φᵀ (Q* a Q) φ = ∑_j a_j L⁻²ʲ ‖P_j (1_{layer j} φ)‖²`. -/
theorem avgMatrix_quadratic (a : ℕ → ℝ) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    φ ⬝ᵥ avgMatrix G a *ᵥ φ =
      ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) *
        ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) (layerPart G j φ) x) ^ 2 := by
  unfold avgMatrix
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := (Finset.mem_Icc.1 hj).2
  have hℓ := side_eq (N₀ := N₀) (L := L) hjk
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, layerProjMatrix_quadratic]
  congr 1
  simp only [dotProduct, blockProjMatrix_mulVec]
  exact sum_mul_blockProjection hℓ hN _

end Operator

/-- The zero extension to a finite set `Λ` of a field on `Λ`. -/
def zeroExt {ι : Type*} [DecidableEq ι] (Λ : Finset ι) (u : Λ → ℂ) : ι → ℂ :=
  fun i => if h : i ∈ Λ then u ⟨i, h⟩ else 0

theorem reQuad_restrictOp {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (Λ : Finset ι)
    (v : Λ → ℂ) : Green.reQuad (Green.restrictOp A Λ) v = Green.reQuad A (zeroExt Λ v) := by
  have hwΛ : ∀ i : Λ, zeroExt Λ v i = v i := fun i => by simp [zeroExt, i.2]
  unfold Green.reQuad
  congr 1
  rw [Green.sum_eq_sum_subtype Λ _ (fun i hi => by simp [zeroExt, hi])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hwΛ]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  rw [Green.sum_eq_sum_subtype Λ _ (fun j hj => by simp [zeroExt, hj])]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Green.restrictOp, hwΛ]

theorem sqNorm_zeroExt {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Finset ι) (v : Λ → ℂ) :
    Green.sqNorm (zeroExt Λ v) = Green.sqNorm v := by
  have hwΛ : ∀ i : Λ, zeroExt Λ v i = v i := fun i => by simp [zeroExt, i.2]
  unfold Green.sqNorm
  rw [Green.sum_eq_sum_subtype Λ _ (fun i hi => by simp [zeroExt, hi])]
  exact Finset.sum_congr rfl fun i _ => by rw [hwΛ]

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The real part of the form of `H_D(α)` on `u` is the real part of the form of
`-Δ + ν + Q* a Q` on the zero extension, plus `∑ Re α |u|²`. -/
theorem reQuad_dirichletOperator (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ) :
    Green.reQuad (dirichletOperator G a ν α) u =
      Green.reQuad ((fullMatrix G a ν).map (algebraMap ℝ ℂ)) (zeroExt (G.Ω 1) u) +
        ∑ i, (α i).re * ‖u i‖ ^ 2 := by
  unfold dirichletOperator
  rw [Green.reQuad_add, reQuad_restrictOp, reQuad_diagonal]

end Balaban.Multiscale
