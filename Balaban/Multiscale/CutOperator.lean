/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Agmon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The multiscale Dirichlet operator with removed (cut) bonds (LOCALIZATION.md §1.3, §3.1, NC)

For a finite set `cut` of bonds `(x, μ)` (the bond joining `x` to `x + e_μ`) of the fine torus:

* `Balaban.cutLaplacian ν cut`: the matrix `-Δ + ν` with the bonds of `cut` removed
  (`latticeLaplacian` minus the rank-one matrices of the removed bonds); its bilinear form is the
  sum over the retained bonds (`cutLaplacian_bilinear`);
* `Balaban.Multiscale.cutFullMatrix G a ν cut = cutLaplacian ν cut + Q* a Q`;
* `Balaban.Multiscale.cutOperator G a ν cut α`: `H_D(α)` with the bonds of `cut` removed, as a
  complex matrix on `Ω₁`; for `cut = ∅` it is the landed `dirichletOperator`
  (`cutOperator_empty`);
* `Balaban.Multiscale.cutEnergy`: `‖∂ũ‖²` summed over the retained bonds only;
* `Balaban.Multiscale.CutAligned G cut`: no removed bond is a bond inside a block of a layer
  (the block Poincaré inequalities are intact);
* `Balaban.Multiscale.cubeCut G Λ`: the cut of the Neumann cube operator (§1.3): the bonds joining
  `Λ` to `Ω₁ \ Λ` (the bonds to `Ω₁ᶜ` stay: they are the Dirichlet wall);
  `cubeCut_aligned`: it is `CutAligned` when `Λ` is a union of blocks of every layer meeting it.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

section Laplacian

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The vector `δ_{x + e_μ} - δ_x` of the bond `(x, μ)`. -/
def bondVec (b : Torus d ℓ × Fin d) : Torus d ℓ → ℝ :=
  Pi.single (b.1 + Pi.single b.2 1) 1 - Pi.single b.1 1

/-- The matrix of the bond `(x, μ)`: `(φ ↦ (φ(x + e_μ) - φ(x)) (δ_{x+e_μ} - δ_x))`. -/
def bondMatrix (b : Torus d ℓ × Fin d) : Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  Matrix.vecMulVec (bondVec b) (bondVec b)

theorem bondVec_dotProduct (b : Torus d ℓ × Fin d) (φ : Torus d ℓ → ℝ) :
    bondVec b ⬝ᵥ φ = φ (b.1 + Pi.single b.2 1) - φ b.1 := by
  simp [bondVec, sub_dotProduct]

theorem dotProduct_bondVec (b : Torus d ℓ × Fin d) (φ : Torus d ℓ → ℝ) :
    φ ⬝ᵥ bondVec b = φ (b.1 + Pi.single b.2 1) - φ b.1 := by
  rw [dotProduct_comm, bondVec_dotProduct]

theorem bondMatrix_bilinear (b : Torus d ℓ × Fin d) (g φ : Torus d ℓ → ℝ) :
    g ⬝ᵥ bondMatrix b *ᵥ φ =
      (g (b.1 + Pi.single b.2 1) - g b.1) * (φ (b.1 + Pi.single b.2 1) - φ b.1) := by
  unfold bondMatrix
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul, dotProduct_bondVec, bondVec_dotProduct]
  simp [MulOpposite.smul_eq_mul_unop]

/-- The matrix of `-Δ + ν` with the bonds of `cut` removed. -/
def cutLaplacian (ν : ℝ) (cut : Finset (Torus d ℓ × Fin d)) : Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  latticeLaplacian d ℓ ν - ∑ b ∈ cut, bondMatrix b

/-- Without removed bonds one has the lattice Laplacian. -/
@[simp] theorem cutLaplacian_empty (ν : ℝ) :
    cutLaplacian (d := d) (ℓ := ℓ) ν ∅ = latticeLaplacian d ℓ ν := by
  simp [cutLaplacian]

/-- The bilinear form of `-Δ + ν` with removed bonds: the sum over the retained bonds. -/
theorem cutLaplacian_bilinear (ν : ℝ) (cut : Finset (Torus d ℓ × Fin d)) (g φ : Torus d ℓ → ℝ) :
    g ⬝ᵥ cutLaplacian ν cut *ᵥ φ =
      ∑ x, ∑ μ : Fin d, (if (x, μ) ∈ cut then 0 else
        (g (x + Pi.single μ 1) - g x) * (φ (x + Pi.single μ 1) - φ x)) +
        ν * ∑ x, g x * φ x := by
  set T : Torus d ℓ → Fin d → ℝ := fun x μ =>
    (g (x + Pi.single μ 1) - g x) * (φ (x + Pi.single μ 1) - φ x) with hT
  have hcut : g ⬝ᵥ (∑ b ∈ cut, bondMatrix b) *ᵥ φ =
      ∑ x, ∑ μ : Fin d, (if (x, μ) ∈ cut then T x μ else 0) := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    simp only [bondMatrix_bilinear]
    have h1 := Fintype.sum_prod_type' (f := fun x μ => if (x, μ) ∈ cut then T x μ else 0)
    simp only [Prod.mk.eta] at h1
    rw [← h1, Finset.sum_ite_mem, Finset.univ_inter]
  have hall := latticeLaplacian_bilinear ν g φ
  have hdiff : ∑ x, ∑ μ : Fin d, T x μ - ∑ x, ∑ μ : Fin d, (if (x, μ) ∈ cut then T x μ else 0) =
      ∑ x, ∑ μ : Fin d, (if (x, μ) ∈ cut then 0 else T x μ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp
  unfold cutLaplacian
  rw [Matrix.sub_mulVec, dotProduct_sub, hall, hcut]
  linarith

end Laplacian

namespace Multiscale

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Operator

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The real matrix `-Δ + ν + Q* a Q` on the whole fine torus, with the bonds of `cut` removed from
`-Δ`. -/
noncomputable def cutFullMatrix (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) :
    Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ :=
  cutLaplacian ν cut + avgMatrix G a

/-- **The cut Dirichlet operator**: `H_D(α)` of (1.6) with the bonds of `cut` removed, as a complex
matrix on `Ω₁` (the restriction to `Ω₁` of `-Δ_cut + ν + Q* a Q`, plus the diagonal `α`). -/
noncomputable def cutOperator (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (α : G.Ω 1 → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Green.restrictOp ((cutFullMatrix G a ν cut).map (algebraMap ℝ ℂ)) (G.Ω 1) + Matrix.diagonal α

@[simp] theorem cutFullMatrix_empty (a : ℕ → ℝ) (ν : ℝ) :
    cutFullMatrix G a ν ∅ = fullMatrix G a ν := by
  simp [cutFullMatrix, fullMatrix]

/-- With no removed bond one has the landed Dirichlet operator. -/
@[simp] theorem cutOperator_empty (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    cutOperator G a ν ∅ α = dirichletOperator G a ν α := by
  simp [cutOperator, dirichletOperator]

/-- `‖∂v‖²` over the retained bonds only: `∑_{(x,μ) ∉ cut} |v(x + e_μ) - v(x)|²`. -/
noncomputable def cutEnergy (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (v : Torus d (N₀ * L ^ k) → ℂ) : ℝ :=
  ∑ x, ∑ μ : Fin d, if (x, μ) ∈ cut then 0 else ‖v (x + Pi.single μ 1) - v x‖ ^ 2

/-- `‖∂φ‖²` over the retained bonds for a real field. -/
noncomputable def cutLatticeEnergy (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (φ : Torus d (N₀ * L ^ k) → ℝ) : ℝ :=
  ∑ x, ∑ μ : Fin d, if (x, μ) ∈ cut then 0 else (φ (x + Pi.single μ 1) - φ x) ^ 2

theorem cutEnergy_nonneg (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (v : Torus d (N₀ * L ^ k) → ℂ) : 0 ≤ cutEnergy cut v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

theorem cutLatticeEnergy_nonneg (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (φ : Torus d (N₀ * L ^ k) → ℝ) : 0 ≤ cutLatticeEnergy cut φ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

@[simp] theorem cutEnergy_empty (v : Torus d (N₀ * L ^ k) → ℂ) : cutEnergy ∅ v = cEnergy v := by
  simp [cutEnergy, cEnergy]

@[simp] theorem cutLatticeEnergy_empty (φ : Torus d (N₀ * L ^ k) → ℝ) :
    cutLatticeEnergy ∅ φ = latticeEnergy φ := by
  simp [cutLatticeEnergy, latticeEnergy]

theorem cutEnergy_eq (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (v : Torus d (N₀ * L ^ k) → ℂ) :
    cutEnergy cut v = cutLatticeEnergy cut (fun x => (v x).re) +
      cutLatticeEnergy cut (fun x => (v x).im) := by
  unfold cutEnergy cutLatticeEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs
  · simp
  · rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring

/-- The quadratic form of the cut matrix: `φᵀ(-Δ_cut + ν)φ`, the retained bonds. -/
theorem cutLaplacian_quadratic (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (φ : Torus d (N₀ * L ^ k) → ℝ) :
    φ ⬝ᵥ cutLaplacian ν cut *ᵥ φ = cutLatticeEnergy cut φ + ν * ∑ x, φ x ^ 2 := by
  rw [cutLaplacian_bilinear]
  unfold cutLatticeEnergy
  congr 1
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> ring
  · congr 1
    exact Finset.sum_congr rfl fun x _ => by ring

/-- The real part of the form of the cut operator on `u` is the form of
`-Δ_cut + ν + Q* a Q` on the zero extension, plus `∑ Re α |u|²`. -/
theorem reQuad_cutOperator (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (α : G.Ω 1 → ℂ) (u : G.Ω 1 → ℂ) :
    Green.reQuad (cutOperator G a ν cut α) u =
      Green.reQuad ((cutFullMatrix G a ν cut).map (algebraMap ℝ ℂ)) (zeroExt (G.Ω 1) u) +
        ∑ i, (α i).re * ‖u i‖ ^ 2 := by
  unfold cutOperator
  rw [Green.reQuad_add, reQuad_restrictOp, reQuad_diagonal]

/-- The equation `H_cut u = f` at a point of `Ω₁`, in terms of the zero extension. -/
theorem cutOperator_eq {a : ℕ → ℝ} {ν : ℝ} {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    {α : G.Ω 1 → ℂ} {u f : G.Ω 1 → ℂ} (hu : cutOperator G a ν cut α *ᵥ u = f) (x : G.Ω 1) :
    ((cutFullMatrix G a ν cut).map (algebraMap ℝ ℂ) *ᵥ zeroExt (G.Ω 1) u)
        (x : Torus d (N₀ * L ^ k)) + α x * u x = f x := by
  have h := congrFun hu x
  unfold cutOperator at h
  rw [Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal, restrictOp_mulVec] at h
  exact h

/-- No removed bond is a bond inside a block of a layer: the block Poincaré inequalities of the
layer blocks are unaffected by the cut. -/
def CutAligned (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) : Prop :=
  ∀ j ∈ Icc 1 k, ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d), (x, μ) ∈ cut → x ∈ G.layer j →
    ¬ ((x μ).val % L ^ j + 1 < L ^ j)

theorem cutAligned_empty : CutAligned G (∅ : Finset (Torus d (N₀ * L ^ k) × Fin d)) :=
  fun _ _ _ _ h => absurd h (Finset.notMem_empty _)

/-! ### The cut of the Neumann cube operator -/

open scoped Classical in
/-- **The cube cut** (LOCALIZATION.md §1.3): for a finite set `Λ` (the cube `□_z ∩ Ω₁`) the bonds
joining `Λ` to `Ω₁ \ Λ`. The bonds from `Λ` to the complement of `Ω₁` are not cut (they are the
Dirichlet wall). -/
noncomputable def cubeCut (Λ : Finset (Torus d (N₀ * L ^ k))) :
    Finset (Torus d (N₀ * L ^ k) × Fin d) :=
  Finset.univ.filter fun b =>
    (b.1 ∈ Λ ∧ b.1 + Pi.single b.2 1 ∈ G.Ω 1 ∧ b.1 + Pi.single b.2 1 ∉ Λ) ∨
      (b.1 ∉ Λ ∧ b.1 ∈ G.Ω 1 ∧ b.1 + Pi.single b.2 1 ∈ Λ)

theorem mem_cubeCut {Λ : Finset (Torus d (N₀ * L ^ k))} {x : Torus d (N₀ * L ^ k)} {μ : Fin d} :
    (x, μ) ∈ cubeCut G Λ ↔
      (x ∈ Λ ∧ x + Pi.single μ 1 ∈ G.Ω 1 ∧ x + Pi.single μ 1 ∉ Λ) ∨
        (x ∉ Λ ∧ x ∈ G.Ω 1 ∧ x + Pi.single μ 1 ∈ Λ) := by
  simp [cubeCut]

/-- `Λ` is a union of blocks of every layer that it meets. -/
def BlockAligned (Λ : Finset (Torus d (N₀ * L ^ k))) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → ∀ x x' : Torus d (N₀ * L ^ k), x ∈ G.layer j →
    jBlock d L N₀ k j x' = jBlock d L N₀ k j x → (x ∈ Λ ↔ x' ∈ Λ)

/-- The cube cut of a block-aligned set removes no bond inside a block of a layer. -/
theorem cubeCut_aligned {Λ : Finset (Torus d (N₀ * L ^ k))} (hΛ : BlockAligned G Λ) :
    CutAligned G (cubeCut G Λ) := by
  intro j hj x μ hb hx hin
  have hj1 := (Finset.mem_Icc.1 hj).1
  have hjk := (Finset.mem_Icc.1 hj).2
  have hbl : jBlock d L N₀ k j (x + Pi.single μ 1) = jBlock d L N₀ k j x :=
    blockMap_add_single_of_inner (side_eq hjk) hin
  have h := hΛ j hj1 hjk x _ hx hbl
  rcases (mem_cubeCut G).1 hb with ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩
  · exact h3 (h.1 h1)
  · exact h1 (h.2 h3)

end Operator

end Multiscale

end Balaban
