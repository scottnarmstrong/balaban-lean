/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventAbs
public import Balaban.Multiscale.CutCoercivity
public import Balaban.Localization.DecoupledCovAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The direct base decoupled resolvent (BASE-KERNEL-3 §1)

`D = G.Ω 1` is the fine-site chart domain of a one-layer generating set (a union of complete first
blocks, exterior spins held fixed).  `baseCutBonds G` is the set `𝓔` of nearest-neighbour bonds with
both endpoints in `D` but in different first blocks, `baseBond G b = T_b`, and
`baseHamiltonian G a ν α s = H(s) = H_cut + ∑_{b ∈ 𝓔} s_b T_b` (1.2).  The family
`baseOp N e H = Q_e (H ⊗ I_N) Q_e + P_e` is (1.3), and `baseResolvent` is `(A_e(s) + x)⁻¹`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset
open Balaban.LargeField.Base

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The fine bonds `(x, μ)` of the one-layer chart torus. -/
abbrev FineBond (d L N₀ : ℕ) : Type := Torus d (N₀ * L ^ 1) × Fin d

section Defs

variable (G : GeneratingSet d L N₀ 1 ϱ)

/-- **The set `𝓔`** of BASE-KERNEL-3 §1: bonds with both endpoints in `D = Ω₁` but in different
first blocks.  A Dirichlet boundary bond (other endpoint outside `D`) is not in `𝓔`. -/
def baseCutBonds : Finset (FineBond d L N₀) :=
  Finset.univ.filter fun b => b.1 ∈ G.Ω 1 ∧ b.1 + Pi.single b.2 1 ∈ G.Ω 1 ∧
    jBlock d L N₀ 1 1 b.1 ≠ jBlock d L N₀ 1 1 (b.1 + Pi.single b.2 1)

/-- `T_b = D_b^* D_b` on `D`: the restriction to `D` of the bond matrix of `b`. -/
noncomputable def baseBond (b : FineBond d L N₀) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  restrictOp ((bondMatrix b).map (algebraMap ℝ ℂ)) (G.Ω 1)

/-- **`H(s) = H_cut + ∑_{b ∈ 𝓔} s_b T_b`** (1.2), with `H_cut` the cut Dirichlet operator
`cutOperator G a ν 𝓔 α` (`ν = μ_bg`). -/
noncomputable def baseHamiltonian (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : FineBond d L N₀ → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  cutOperator G a ν (baseCutBonds G) α + ∑ b ∈ baseCutBonds G, s b • baseBond G b

end Defs

/-- `P_e = E Eᵀ`, `(E f)_z = e_z f_z`. -/
noncomputable def basePart {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ} (e : ι → Fin N → ℂ) :
    Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  fieldMul e * (fieldMul e)ᵀ

/-- **`A_e = Q_e (H ⊗ I_N) Q_e + P_e`** (1.3), `Q_e = 1 - P_e`. -/
noncomputable def baseOp {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ) (e : ι → Fin N → ℂ)
    (H : Matrix ι ι ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  (1 - basePart e) * liftOp N H * (1 - basePart e) + basePart e

/-- **`𝒞_{e,x} = (A_e + x I)⁻¹`**. -/
noncomputable def baseResolvent {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (e : ι → Fin N → ℂ) (H : Matrix ι ι ℂ) (x : ℝ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  (baseOp N e H + (x : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ))⁻¹

section Endpoints

variable (G : GeneratingSet d L N₀ 1 ϱ)

theorem baseBond_apply (b : FineBond d L N₀) (x y : G.Ω 1) :
    baseBond G b x y = ((bondVec b x : ℝ) : ℂ) * ((bondVec b y : ℝ) : ℂ) := by
  simp [baseBond, restrictOp, bondMatrix, Matrix.vecMulVec_apply]

/-- `H(0) = H_cut`. -/
theorem baseHamiltonian_zero (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    baseHamiltonian G a ν α (fun _ => 0) = cutOperator G a ν (baseCutBonds G) α := by
  simp [baseHamiltonian]

/-- `H(1) = H`, the one-layer Dirichlet operator. -/
theorem baseHamiltonian_one (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    baseHamiltonian G a ν α (fun _ => 1) = dirichletOperator G a ν α := by
  rw [← cutOperator_empty]
  have key : cutFullMatrix G a ν ∅ =
      cutFullMatrix G a ν (baseCutBonds G) + ∑ b ∈ baseCutBonds G, bondMatrix b := by
    simp only [cutFullMatrix, cutLaplacian, Finset.sum_empty, sub_zero]
    abel
  have key2 : restrictOp ((cutFullMatrix G a ν ∅).map (algebraMap ℝ ℂ)) (G.Ω 1) =
      restrictOp ((cutFullMatrix G a ν (baseCutBonds G)).map (algebraMap ℝ ℂ)) (G.Ω 1) +
        ∑ b ∈ baseCutBonds G, baseBond G b := by
    rw [key]
    ext x y
    simp [restrictOp, baseBond, Matrix.sum_apply]
  unfold baseHamiltonian cutOperator
  simp only [one_smul]
  rw [key2]
  abel

/-- `T_b` as a rank-one matrix. -/
theorem baseBond_eq_vecMulVec (b : FineBond d L N₀) :
    baseBond G b = Matrix.vecMulVec (fun x : G.Ω 1 => ((bondVec b x : ℝ) : ℂ))
      (fun x : G.Ω 1 => ((bondVec b x : ℝ) : ℂ)) := by
  ext x y
  rw [baseBond_apply, Matrix.vecMulVec_apply]

/-- Each `T_b` is positive semidefinite. -/
theorem reQuad_baseBond_nonneg (b : FineBond d L N₀) (u : G.Ω 1 → ℂ) :
    0 ≤ reQuad (baseBond G b) u := by
  set vC : G.Ω 1 → ℂ := fun x => ((bondVec b x : ℝ) : ℂ) with hvC
  set w : ℂ := vC ⬝ᵥ u with hw
  have hs : star u ⬝ᵥ vC = star w := by
    rw [hw]
    simp only [dotProduct, star_sum, star_mul']
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [hvC]
    ring
  have h1 : star u ⬝ᵥ (baseBond G b *ᵥ u) = star w * w := by
    rw [baseBond_eq_vecMulVec, Matrix.vecMulVec_mulVec]
    simp only [dotProduct_smul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    rw [hs]
  rw [reQuad_eq_dot, h1, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp [Complex.normSq_nonneg]

/-- Cutting `𝓔` removes no bond inside a first block. -/
theorem baseCutBonds_aligned : CutAligned G (baseCutBonds G) := by
  intro j hj x μ hb _ hin
  have hj1 : j = 1 := by
    have := Finset.mem_Icc.1 hj; omega
  subst hj1
  have hmem := (Finset.mem_filter.1 hb).2
  exact hmem.2.2 (blockMap_add_single_of_inner (side_eq (le_refl 1)) hin).symm

/-- The coercivity constant `c = 1/(4L²)` of BASE-KERNEL-3 Theorem 1.1. -/
noncomputable def baseCoercivity (L : ℕ) : ℝ := 1 / (4 * (L : ℝ) ^ 2)

omit [NeZero N₀] [NeZero L] in
theorem baseCoercivity_pos (hL : 0 < L) : 0 < baseCoercivity L := by
  unfold baseCoercivity
  have : (0 : ℝ) < L := by exact_mod_cast hL
  positivity

omit [NeZero N₀] [NeZero L] in
theorem baseCoercivity_le_one (hL : 0 < L) : baseCoercivity L ≤ 1 := by
  unfold baseCoercivity
  have : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [div_le_one (by positivity)]
  nlinarith

/-- **(1.5)** for real parameters: `Re ⟨u, H(r) u⟩ ≥ c ‖u‖²` (the scalar form). -/
theorem baseHamiltonian_isCoercive_real {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (r : FineBond d L N₀ → ℝ)
    (hr : ∀ b ∈ baseCutBonds G, 0 ≤ r b) :
    IsCoercive (baseHamiltonian G a ν α (fun b => (r b : ℂ))) (baseCoercivity L) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hα' : ∀ x : G.Ω 1, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2) := by
    intro x
    have hx : (x : Torus d (N₀ * L ^ 1)) ∈ G.layer 1 := by
      rw [GeneratingSet.mem_layer]
      exact ⟨x.2, by rw [show 1 + 1 = 1 + 1 from rfl, G.top]; simp⟩
    rw [G.spacing_eq le_rfl le_rfl hx]
    refine (hα x).trans (le_of_eq ?_)
    unfold coerciveConstSharp
    field_simp
    ring
  have hc := cutOperator_isCoercive_min_sharp G (baseCutBonds_aligned G) hν ha α hα'
  intro u
  have h1 := hc u
  have h2 := reQuad_sum_nonneg (S := baseCutBonds G) (baseBond G) r u hr
    (fun b _ => reQuad_baseBond_nonneg G b u)
  unfold baseHamiltonian
  rw [reQuad_add]
  have hconst : coerciveConstSharp * (((L : ℝ) ^ 1) ^ 2)⁻¹ = baseCoercivity L := by
    unfold coerciveConstSharp baseCoercivity; field_simp
  rw [hconst] at h1
  linarith

end Endpoints

end Balaban.LargeField.Base
