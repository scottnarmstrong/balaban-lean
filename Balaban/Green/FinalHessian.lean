/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.UnitLattice
public import Balaban.Flow.StopIndex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The final Hessian at the stopping index and its coercivity

`notes/phase1/FINAL.md` §1 (packages `FinalHessianSplit`, `FinalHessianCoercive`).

At the stopping index the remaining scale-`k_f` spin field is integrated once around the constant
configuration `h` (`|h| = 1`), with a quadratic form that has no next-scale averaging term.  With
`Q` the block average, `G = H⁻¹` and `H = n²(-Δ) + v + a Q*Q` the fine operator of
`Green.fineHamiltonian` (`n` the block size), the form on `N`-component fields of the coarse torus is
`D = a·1 - a² Q G Q* + a² Q G h (h* G h)⁻¹ h* G Q*` (P4 (2.23) at the constant saddle).  Here `h`
inserts the constant spin direction at every fine site.  All matrices are real.

* `finalHessian` is this formula, literally, built from the same `Q`, `Q*` and `G` as
  `unconstrainedUnitOperator`;
* `finalHessian_eq_split`: for `∑ hᵢ² = 1`, `D = a·P_h + U ⊗ (1 - P_h)` with `P_h = 1 ⊗ h hᵀ`;
* `finalHessian_form_ge`: `⟨u, D u⟩ ≥ (8d+3)⁻¹ ⟨u, (-Δ_m + v) u⟩`, hence `≥ (8d+3)⁻¹ v ‖u‖²`;
* `finalHessian_inv`: `D⁻¹ = a⁻¹ P_h + U⁻¹ ⊗ (1 - P_h)`;
* `finalHessian_gap_of_running`: at `k_f` of a running sequence the gap is `7/(8L²(8d+3))`.

Not proved here: the identification of this operator with the Hessian of the physical final density
(`FINAL-HESSIAN-BRIDGE`), the final cutoff, the complex domain and the last expansion.  The operator
`Localization/DecoupledIdentMain.covOp` contains an extra next-scale term and is a different object.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

section Lift

variable {ι κ ρ : Type*} {N : ℕ}

/-- The spin lift `A ⊗ 1`: the scalar matrix `A` acting on each of the `N` spin components. -/
def spinLift (N : ℕ) (A : Matrix ι κ ℝ) : Matrix (ι × Fin N) (κ × Fin N) ℝ :=
  fun p q => if p.2 = q.2 then A p.1 q.1 else 0

/-- Insertion of the constant spin direction `h` at every site: `(insH h) ((x,i), y) = h i` if
`x = y`, else `0`. -/
def insH [DecidableEq ι] (h : Fin N → ℝ) : Matrix (ι × Fin N) ι ℝ :=
  fun p x => if p.1 = x then h p.2 else 0

/-- The spin projection `1 ⊗ (h hᵀ)`. -/
def projH [DecidableEq ι] (h : Fin N → ℝ) : Matrix (ι × Fin N) (ι × Fin N) ℝ :=
  fun p q => if p.1 = q.1 then h p.2 * h q.2 else 0

variable [Fintype ι] [Fintype κ] [Fintype ρ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem spinLift_mul (A : Matrix ι κ ℝ) (B : Matrix κ ρ ℝ) :
    spinLift N (A * B) = spinLift N A * spinLift N B := by
  ext ⟨y, i⟩ ⟨z, j⟩
  simp only [spinLift, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem spinLift_add (A B : Matrix ι κ ℝ) : spinLift N (A + B) = spinLift N A + spinLift N B := by
  ext ⟨y, i⟩ ⟨z, j⟩
  by_cases hij : i = j <;> simp [spinLift, hij]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem spinLift_sub (A B : Matrix ι κ ℝ) : spinLift N (A - B) = spinLift N A - spinLift N B := by
  ext ⟨y, i⟩ ⟨z, j⟩
  by_cases hij : i = j <;> simp [spinLift, hij]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem spinLift_smul (c : ℝ) (A : Matrix ι κ ℝ) : spinLift N (c • A) = c • spinLift N A := by
  ext ⟨y, i⟩ ⟨z, j⟩
  by_cases hij : i = j <;> simp [spinLift, hij]

omit [Fintype ι] in
theorem spinLift_one : spinLift N (1 : Matrix ι ι ℝ) = 1 := by
  ext ⟨y, i⟩ ⟨z, j⟩
  by_cases hij : i = j
  · subst hij; by_cases hyz : y = z <;> simp [spinLift, hyz, Matrix.one_apply]
  · simp [spinLift, hij]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem spinLift_apply_same (A : Matrix ι κ ℝ) (y : ι) (z : κ) (i : Fin N) :
    spinLift N A (y, i) (z, i) = A y z := by simp [spinLift]

theorem insH_transpose_mul (A : Matrix ι ι ℝ) (h : Fin N → ℝ) :
    ((insH (ι := ι) h)ᵀ * spinLift N A * insH (ι := ι) h : Matrix ι ι ℝ) = (∑ i, h i ^ 2) • A := by
  ext x y
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.transpose_apply, insH, spinLift,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

theorem spinLift_mul_insH (A : Matrix ι ι ℝ) (h : Fin N → ℝ) :
    (spinLift N A * insH (ι := ι) h : Matrix (ι × Fin N) ι ℝ) = (insH (ι := ι) h * A : Matrix (ι × Fin N) ι ℝ) := by
  ext ⟨y, i⟩ x
  simp [Matrix.mul_apply, Fintype.sum_prod_type, spinLift, insH, mul_comm]

theorem insH_transpose_mul_spinLift (A : Matrix ι ι ℝ) (h : Fin N → ℝ) :
    ((insH (ι := ι) h)ᵀ * spinLift N A : Matrix ι (ι × Fin N) ℝ) =
      (A * (insH (ι := ι) h)ᵀ : Matrix ι (ι × Fin N) ℝ) := by
  ext x ⟨z, j⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, spinLift, insH, mul_comm]

theorem insH_mul_transpose (h : Fin N → ℝ) :
    (insH (ι := ι) h * (insH (ι := ι) h)ᵀ : Matrix (ι × Fin N) (ι × Fin N) ℝ) = projH (ι := ι) h := by
  ext ⟨y, i⟩ ⟨z, j⟩
  simp only [Matrix.mul_apply, projH, insH, Matrix.transpose_apply]
  by_cases hyz : y = z
  · subst hyz; simp [mul_comm]
  · simp [hyz]

theorem insH_mul_mul_transpose (A : Matrix ι ι ℝ) (h : Fin N → ℝ) :
    ((insH (ι := ι) h * A * (insH (ι := ι) h)ᵀ : Matrix (ι × Fin N) (ι × Fin N) ℝ)) = spinLift N A * projH (ι := ι) h := by
  rw [← insH_mul_transpose, ← Matrix.mul_assoc, ← spinLift_mul_insH]

theorem spinLift_mul_projH (A : Matrix ι κ ℝ) (h : Fin N → ℝ) :
    (spinLift N A * projH (ι := κ) h : Matrix (ι × Fin N) (κ × Fin N) ℝ) =
      (projH (ι := ι) h * spinLift N A : Matrix (ι × Fin N) (κ × Fin N) ℝ) := by
  ext ⟨y, i⟩ ⟨z, j⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, spinLift, projH, Finset.sum_ite_eq, mul_comm]

end Lift

section Hessian

variable {d ℓ Nb m N : ℕ} [NeZero ℓ] [NeZero m]

/-- The final Hessian `D = a - a² Q G Q* + a² Q G h (h* G h)⁻¹ h* G Q*` (P4 (2.23) at the constant
saddle `h`, no next-scale averaging term), with real entries, on `(Torus d m) × Fin N`.  Here
`G = (fineHamiltonian d ℓ Nb m ν a)⁻¹` is the inverse of the fine operator `Nb²(-Δ) + ν + a Q*Q`,
`Q = unitBlockAverageMatrix`, `Q* = blockPullbackMatrix` (the same objects as in
`unconstrainedUnitOperator`), the scalar operators act on every spin component (`spinLift`), and
`h` is inserted at every fine site (`insH`), so `h* G h` is a scalar fine matrix.  This is the
real-matrix operator only; its identification with the Hessian of the physical final density is not
part of this definition. -/
noncomputable def finalHessian (d ℓ Nb m : ℕ) [NeZero ℓ] [NeZero m] (ν a : ℝ) (h : Fin N → ℝ) :
    Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ :=
  a • (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) -
    (a ^ 2) • spinLift N (unitBlockAverageMatrix d ℓ Nb m * (fineHamiltonian d ℓ Nb m ν a)⁻¹ *
      blockPullbackMatrix d ℓ Nb m) +
    (a ^ 2) • (spinLift N (unitBlockAverageMatrix d ℓ Nb m) *
      spinLift N (fineHamiltonian d ℓ Nb m ν a)⁻¹ * insH (ι := Torus d ℓ) h *
      ((insH (ι := Torus d ℓ) h)ᵀ * spinLift N (fineHamiltonian d ℓ Nb m ν a)⁻¹ *
        insH (ι := Torus d ℓ) h)⁻¹ *
      (insH (ι := Torus d ℓ) h)ᵀ * spinLift N (fineHamiltonian d ℓ Nb m ν a)⁻¹ *
      spinLift N (blockPullbackMatrix d ℓ Nb m) :
        Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ)

theorem fineHamiltonian_posDef (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) : (fineHamiltonian d ℓ Nb m ν a).PosDef := by
  have hc : (0 : ℝ) < (Nb : ℝ) ^ 2 := by positivity
  have hH : fineHamiltonian d ℓ Nb m ν a =
      ((Nb : ℝ) ^ 2) • blockHamiltonian d ℓ Nb m (ν / (Nb : ℝ) ^ 2) (a / (Nb : ℝ) ^ 2) := by
    unfold fineHamiltonian blockHamiltonian
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hc.ne']
  rw [hH]
  exact (blockHamiltonian_posDef hℓ hN hd (by positivity) (by positivity)).smul hc

theorem fineHamiltonian_isUnit_det (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) : IsUnit (fineHamiltonian d ℓ Nb m ν a).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (fineHamiltonian_posDef hℓ hN hd hν ha).isUnit


/-- The scalar fine matrix `h* G h` equals `G` when `|h| = 1`. -/
theorem finalHessian_hGh {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (ν a : ℝ) :
    ((insH (ι := Torus d ℓ) h)ᵀ * spinLift N (fineHamiltonian d ℓ Nb m ν a)⁻¹ *
      insH (ι := Torus d ℓ) h : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) =
      (fineHamiltonian d ℓ Nb m ν a)⁻¹ := by
  rw [insH_transpose_mul, hh, one_smul]

/-- **The exact split (F.2).**  For `|h| = 1`, `D = a·P_h + lift(U)·(1 - P_h)` with
`U = unconstrainedUnitOperator`. -/
theorem finalHessian_eq_split (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    finalHessian d ℓ Nb m ν a h =
      a • projH (ι := Torus d m) h +
        spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a) *
          (1 - projH (ι := Torus d m) h) := by
  have hdet := fineHamiltonian_isUnit_det hℓ hN hd hν ha
  set Hm := fineHamiltonian d ℓ Nb m ν a with hHm
  set Q := unitBlockAverageMatrix d ℓ Nb m
  set Qp := blockPullbackMatrix d ℓ Nb m
  have hGH : Hm⁻¹ * Hm = 1 := Matrix.nonsing_inv_mul _ hdet
  have hinv : (Hm⁻¹)⁻¹ = Hm := Matrix.nonsing_inv_nonsing_inv _ hdet
  have key : (spinLift N Q * spinLift N Hm⁻¹ * insH (ι := Torus d ℓ) h *
      ((insH (ι := Torus d ℓ) h)ᵀ * spinLift N Hm⁻¹ * insH (ι := Torus d ℓ) h)⁻¹ *
      (insH (ι := Torus d ℓ) h)ᵀ * spinLift N Hm⁻¹ * spinLift N Qp :
        Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) =
      spinLift N (Q * Hm⁻¹ * Qp) * projH (ι := Torus d m) h := by
    rw [finalHessian_hGh hh, hinv]
    have e1 : (spinLift N Q * spinLift N Hm⁻¹ * insH (ι := Torus d ℓ) h * Hm *
        (insH (ι := Torus d ℓ) h)ᵀ * spinLift N Hm⁻¹ * spinLift N Qp :
          Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) =
        spinLift N Q * (spinLift N Hm⁻¹ * insH (ι := Torus d ℓ) h) * Hm *
          ((insH (ι := Torus d ℓ) h)ᵀ * spinLift N Hm⁻¹) * spinLift N Qp := by
      simp only [Matrix.mul_assoc]
    rw [e1, spinLift_mul_insH, insH_transpose_mul_spinLift]
    have e2 : (spinLift N Q * (insH (ι := Torus d ℓ) h * Hm⁻¹) * Hm *
        (Hm⁻¹ * (insH (ι := Torus d ℓ) h)ᵀ) * spinLift N Qp :
          Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) =
        spinLift N Q * (insH (ι := Torus d ℓ) h * (Hm⁻¹ * Hm * Hm⁻¹) *
          (insH (ι := Torus d ℓ) h)ᵀ) * spinLift N Qp := by
      simp only [Matrix.mul_assoc]
    rw [e2, hGH, Matrix.one_mul, insH_mul_mul_transpose, spinLift_mul, spinLift_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, ← spinLift_mul_projH]
    simp only [Matrix.mul_assoc]
  unfold finalHessian
  rw [key]
  unfold unconstrainedUnitOperator
  rw [spinLift_sub, spinLift_smul, spinLift_smul, spinLift_one]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  abel

theorem spinLift_commute_projH (A : Matrix (Torus d m) (Torus d m) ℝ) (h : Fin N → ℝ) :
    Commute (spinLift N A) (projH (ι := Torus d m) h) :=
  spinLift_mul_projH A h


end Hessian

section Quad

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem quad_conj (B M : Matrix n n ℝ) (u : n → ℝ) :
    (B *ᵥ u) ⬝ᵥ (M *ᵥ (B *ᵥ u)) = u ⬝ᵥ ((Bᵀ * M * B) *ᵥ u) := by
  conv_rhs => rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem split_mat (P M₁ M₂ : Matrix n n ℝ) (hPt : Pᵀ = P) (hPP : P * P = P)
    (h₁ : P * M₁ = M₁ * P) (h₂ : P * M₂ = M₂ * P) :
    Pᵀ * M₁ * P + (1 - P)ᵀ * M₂ * (1 - P) = M₁ * P + M₂ * (1 - P) := by
  have h₂' : (1 - P) * M₂ = M₂ * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, h₂, Matrix.one_mul, Matrix.mul_one]
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
  rw [Matrix.transpose_sub, Matrix.transpose_one, hPt, h₁, Matrix.mul_assoc, hPP,
    h₂', Matrix.mul_assoc, hQ]

end Quad

section Coercive

variable {d ℓ Nb m N : ℕ} [NeZero ℓ] [NeZero m]

theorem projH_transpose {ι : Type*} [DecidableEq ι] (h : Fin N → ℝ) :
    (projH (ι := ι) h)ᵀ = projH h := by
  ext ⟨y, i⟩ ⟨z, j⟩
  by_cases hyz : y = z <;> simp [projH, hyz, mul_comm, eq_comm]

theorem projH_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι] {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) :
    (projH (ι := ι) h * projH h : Matrix (ι × Fin N) (ι × Fin N) ℝ) = projH h := by
  have e : ((insH (ι := ι) h)ᵀ * insH (ι := ι) h : Matrix ι ι ℝ) = 1 := by
    have := insH_transpose_mul (1 : Matrix ι ι ℝ) h
    rwa [spinLift_one, Matrix.mul_one, hh, one_smul] at this
  rw [← insH_mul_transpose]
  have e2 : (insH (ι := ι) h * (insH (ι := ι) h)ᵀ * (insH (ι := ι) h * (insH (ι := ι) h)ᵀ) :
      Matrix (ι × Fin N) (ι × Fin N) ℝ) =
      insH (ι := ι) h * ((insH (ι := ι) h)ᵀ * insH (ι := ι) h) * (insH (ι := ι) h)ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e2, e, Matrix.mul_one]

theorem spinLift_quad {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (w : ι × Fin N → ℝ) :
    w ⬝ᵥ spinLift N M *ᵥ w = ∑ i, (fun y => w (y, i)) ⬝ᵥ M *ᵥ (fun y => w (y, i)) := by
  simp only [dotProduct, Matrix.mulVec, spinLift, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Finset.sum_ite_eq]

theorem sum_sq_spin {ι : Type*} [Fintype ι] (w : ι × Fin N → ℝ) :
    w ⬝ᵥ w = ∑ i, ∑ y, w (y, i) ^ 2 := by
  simp only [dotProduct, Fintype.sum_prod_type, sq]
  rw [Finset.sum_comm]

/-- The quantitative constant `γ₀ = (8d+3)⁻¹`. -/
theorem gamma_mul_le_half {d : ℕ} {ν : ℝ} (hν1 : ν ≤ 1) :
    1 / (8 * (d : ℝ) + 3) * (4 * d + ν) ≤ 1 / 2 := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem longitudinal_ge {d m : ℕ} [NeZero m] {ν a : ℝ} (hν1 : ν ≤ 1)
    (ha : 1 / 2 ≤ a) (w : Torus d m × Fin N → ℝ) :
    1 / (8 * (d : ℝ) + 3) * (w ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ w) ≤ a * (w ⬝ᵥ w) := by
  have hγ : (0 : ℝ) < 1 / (8 * (d : ℝ) + 3) := by positivity
  rw [spinLift_quad, sum_sq_spin, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [latticeLaplacian_quadratic]
  have hE := latticeEnergy_le_four_mul (fun y : Torus d m => w (y, i))
  have hS : 0 ≤ ∑ y : Torus d m, w (y, i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg := gamma_mul_le_half (d := d) hν1
  change 1 / (8 * (d : ℝ) + 3) * (latticeEnergy (fun y : Torus d m => w (y, i)) +
    ν * ∑ y, w (y, i) ^ 2) ≤ a * ∑ y, w (y, i) ^ 2
  have h1 : 1 / (8 * (d : ℝ) + 3) * (latticeEnergy (fun y : Torus d m => w (y, i)) +
      ν * ∑ y, w (y, i) ^ 2) ≤ 1 / (8 * (d : ℝ) + 3) * ((4 * d + ν) * ∑ y, w (y, i) ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hγ.le
  have h2 : 1 / (8 * (d : ℝ) + 3) * ((4 * d + ν) * ∑ y, w (y, i) ^ 2) ≤
      (1 / 2) * ∑ y, w (y, i) ^ 2 := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hg hS
  nlinarith

theorem transverse_ge {d ℓ Nb m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = Nb * m) (hN : 0 < Nb)
    (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (ha : 1 / 2 ≤ a)
    (w : Torus d m × Fin N → ℝ) :
    1 / (8 * (d : ℝ) + 3) * (w ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ w) ≤
      w ⬝ᵥ spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a) *ᵥ w := by
  rw [spinLift_quad, spinLift_quad, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [latticeLaplacian_quadratic]
  have h1 := unconstrainedUnitOperator_lower hℓ hN hd hν (by linarith : 0 < a)
    (fun y : Torus d m => w (y, i))
  have h2 := unconstrained_gamma_ge (d := d) hν hν1 ha
  have hX : 0 ≤ latticeEnergy (fun y : Torus d m => w (y, i)) +
      ν * ∑ y, w (y, i) ^ 2 :=
    add_nonneg (latticeEnergy_nonneg _) (mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  change 1 / (8 * (d : ℝ) + 3) * (latticeEnergy (fun y : Torus d m => w (y, i)) +
    ν * ∑ y, w (y, i) ^ 2) ≤ _
  exact (mul_le_mul_of_nonneg_right h2 hX).trans h1

/-- **Coercivity of the final Hessian.**  For `|h| = 1`, `0 ≤ ν ≤ 1` and `1/2 ≤ a`,
`⟨u, D u⟩ ≥ (8d+3)⁻¹ ⟨u, (-Δ_m + ν) u⟩` for every real field `u` on the coarse torus with `N` spin
components (the longitudinal and transverse spin parts are treated separately).  The upper bound
`a ≤ 2` is not needed. -/
theorem finalHessian_form_ge (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (ha : 1 / 2 ≤ a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (u : Torus d m × Fin N → ℝ) :
    1 / (8 * (d : ℝ) + 3) * (u ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ u) ≤
      u ⬝ᵥ finalHessian d ℓ Nb m ν a h *ᵥ u := by
  have ha0 : 0 < a := by linarith
  set P := projH (ι := Torus d m) h with hP
  set U := spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a) with hU
  have hPt : Pᵀ = P := projH_transpose h
  have hPP : P * P = P := projH_mul_self hh
  have hc1 : P * (a • (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ)) =
      (a • (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ)) * P := by
    simp
  have hcU : P * U = U * P := (spinLift_mul_projH _ h).symm
  have hcK : P * spinLift N (latticeLaplacian d m ν) = spinLift N (latticeLaplacian d m ν) * P :=
    (spinLift_mul_projH _ h).symm
  have hD : finalHessian d ℓ Nb m ν a h =
      Pᵀ * (a • (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ)) * P +
        (1 - P)ᵀ * U * (1 - P) := by
    rw [split_mat P _ _ hPt hPP hc1 hcU, finalHessian_eq_split hℓ hN hd hν ha0 hh]
    simp only [Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hK : spinLift N (latticeLaplacian d m ν) =
      Pᵀ * spinLift N (latticeLaplacian d m ν) * P +
        (1 - P)ᵀ * spinLift N (latticeLaplacian d m ν) * (1 - P) := by
    rw [split_mat P _ _ hPt hPP hcK hcK, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
  have e1 : ∀ x : Torus d m × Fin N → ℝ, x ⬝ᵥ finalHessian d ℓ Nb m ν a h *ᵥ x =
      a * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) + (((1 - P) *ᵥ x) ⬝ᵥ U *ᵥ ((1 - P) *ᵥ x)) := by
    intro x
    rw [hD, Matrix.add_mulVec, dotProduct_add, ← quad_conj, ← quad_conj, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have e2 : u ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ u =
      ((P *ᵥ u) ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ (P *ᵥ u)) +
        (((1 - P) *ᵥ u) ⬝ᵥ spinLift N (latticeLaplacian d m ν) *ᵥ ((1 - P) *ᵥ u)) := by
    rw [quad_conj, quad_conj, ← dotProduct_add, ← Matrix.add_mulVec, ← hK]
  rw [e1, e2, mul_add]
  exact add_le_add ((longitudinal_ge hν1 ha _)) (transverse_ge hℓ hN hd hν hν1 ha _)

/-- Corollary: `⟨u, D u⟩ ≥ (8d+3)⁻¹ ν ‖u‖²`. -/
theorem finalHessian_form_ge_mass (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (ha : 1 / 2 ≤ a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (u : Torus d m × Fin N → ℝ) :
    1 / (8 * (d : ℝ) + 3) * ν * (u ⬝ᵥ u) ≤ u ⬝ᵥ finalHessian d ℓ Nb m ν a h *ᵥ u := by
  refine le_trans ?_ (finalHessian_form_ge hℓ hN hd hν hν1 ha hh u)
  rw [spinLift_quad, sum_sq_spin, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [latticeLaplacian_quadratic]
  have hE := latticeEnergy_nonneg (fun y : Torus d m => u (y, i))
  have hγ : (0 : ℝ) < 1 / (8 * (d : ℝ) + 3) := by positivity
  change _ ≤ 1 / (8 * (d : ℝ) + 3) * (latticeEnergy (fun y : Torus d m => u (y, i)) +
    ν * ∑ y, u (y, i) ^ 2)
  nlinarith [mul_nonneg hγ.le hE]

theorem unconstrainedUnitOperator_isUnit_det {d ℓ Nb m : ℕ} [NeZero ℓ] [NeZero m]
    (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ} (hν : 0 < ν)
    (ha : 0 < a) : IsUnit (unconstrainedUnitOperator d ℓ Nb m ν a).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hUv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 := unconstrainedUnitOperator_lower hℓ hN hd hν.le ha v
  rw [hUv, dotProduct_zero] at h1
  have hS : 0 < ∑ x, v x ^ 2 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hv
    exact lt_of_lt_of_le (by have := sq_pos_of_ne_zero hx; exact this) (Finset.single_le_sum (f := fun x => v x ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ x))
  have hc : 0 < a / (a + 4 * d + ν) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    apply div_pos <;> linarith
  nlinarith [mul_pos hc (mul_pos hν hS), mul_nonneg hc.le (latticeEnergy_nonneg v)]

theorem finalHessian_mul_inv (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (hU : IsUnit (unconstrainedUnitOperator d ℓ Nb m ν a).det) :
    finalHessian d ℓ Nb m ν a h *
      (a⁻¹ • projH (ι := Torus d m) h +
        spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a)⁻¹ * (1 - projH (ι := Torus d m) h)) =
      1 := by
  set P := projH (ι := Torus d m) h with hP
  set A := spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a) with hA
  set B := spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a)⁻¹ with hB
  have hPP : P * P = P := projH_mul_self hh
  have hAB : A * B = 1 := by
    rw [hA, hB, ← spinLift_mul, Matrix.mul_nonsing_inv _ hU, spinLift_one]
  have hPB : P * B = B * P := (spinLift_mul_projH _ h).symm
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, hPP]; simp
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, hPP]; simp
  have hQB : (1 - P) * B = B * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hPB, Matrix.one_mul, Matrix.mul_one]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPP]; simp
  rw [finalHessian_eq_split hℓ hN hd hν ha hh]
  have t1 : (a • P) * (a⁻¹ • P) = P := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul, hPP]
  have t2 : (a • P) * (B * (1 - P)) = 0 := by
    rw [Matrix.smul_mul, ← Matrix.mul_assoc, hPB, Matrix.mul_assoc, hPQ]; simp
  have t3 : (A * (1 - P)) * (a⁻¹ • P) = 0 := by
    rw [Matrix.mul_smul, Matrix.mul_assoc, hQP]; simp
  have t4 : (A * (1 - P)) * (B * (1 - P)) = 1 - P := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - P), hQB, Matrix.mul_assoc, hQQ,
      ← Matrix.mul_assoc, hAB, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, t4]
  simp

/-- `D` is invertible as soon as `U` is. -/
theorem finalHessian_isUnit_det (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (hU : IsUnit (unconstrainedUnitOperator d ℓ Nb m ν a).det) :
    IsUnit (finalHessian d ℓ Nb m ν a h).det :=
  Matrix.isUnit_det_of_right_inverse (finalHessian_mul_inv hℓ hN hd hν ha hh hU)

/-- **The covariance of the last integral.**  If `U` is invertible (it is, for `0 < ν`, by
`unconstrainedUnitOperator_isUnit_det`) then `D⁻¹ = a⁻¹ P_h + lift(U⁻¹)(1 - P_h)`. -/
theorem finalHessian_inv (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1)
    (hU : IsUnit (unconstrainedUnitOperator d ℓ Nb m ν a).det) :
    (finalHessian d ℓ Nb m ν a h)⁻¹ =
      a⁻¹ • projH (ι := Torus d m) h +
        spinLift N (unconstrainedUnitOperator d ℓ Nb m ν a)⁻¹ * (1 - projH (ι := Torus d m) h) :=
  Matrix.inv_eq_right_inv (finalHessian_mul_inv hℓ hN hd hν ha hh hU)

end Coercive

section Stopped

open Balaban.LargeField Balaban.LargeField.StopIndex

/-- **The stopped flow supplies the hypotheses.**  For a running sequence with `RunningHyp` and
`k_f = kStop > 0`, take block size `L^{k_f}` and mass `v = n k_f` (so `(7/8) L⁻² < v < 1`); the
weight `a ∈ (1, 3/2)` of `RunningHyp` lies in `[1/2, 2]`.  Then, for `|h| = 1`,
`⟨u, D u⟩ ≥ 7/(8 L² (8d+3)) ‖u‖²`. -/
theorem finalHessian_gap_of_running {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ}
    (hrun : RunningHyp d L β ν a ε b n) (hpos : 0 < kStop hrun) {ℓ m N : ℕ} [NeZero ℓ]
    [NeZero m] (hℓ : ℓ = L ^ kStop hrun * m) (hd : 0 < d) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) (u : Torus d m × Fin N → ℝ) :
    7 / (8 * (L : ℝ) ^ 2 * (8 * (d : ℝ) + 3)) * (u ⬝ᵥ u) ≤
      u ⬝ᵥ finalHessian d ℓ (L ^ kStop hrun) m (n (kStop hrun)) a h *ᵥ u := by
  have hL : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hrun.hL)
  have hN : 0 < L ^ kStop hrun := by
    have : 0 < L := lt_of_lt_of_le (by norm_num) hrun.hL
    positivity
  have hv0 := kStop_spec hrun
  have hv1 := n_kStop_lt_one hrun hpos
  have hvpos : 0 ≤ n (kStop hrun) := by
    have : 0 < 7 / 8 * ((L : ℝ) ^ 2)⁻¹ := by positivity
    linarith
  have h1 := finalHessian_form_ge_mass hℓ hN hd hvpos hv1.le (by linarith [hrun.ha1] : 1 / 2 ≤ a)
    hh u
  refine le_trans ?_ h1
  have huu : 0 ≤ u ⬝ᵥ u := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hγ : (0 : ℝ) < 1 / (8 * (d : ℝ) + 3) := by positivity
  refine mul_le_mul_of_nonneg_right ?_ huu
  have : 7 / (8 * (L : ℝ) ^ 2 * (8 * (d : ℝ) + 3)) =
      1 / (8 * (d : ℝ) + 3) * (7 / 8 * ((L : ℝ) ^ 2)⁻¹) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hv0.le hγ.le

end Stopped

section Instance

/-- Instance check (`d = 3`, block size `3`, `m = 3`, `a = 1`, `ν = 1/8 ∈ (7/72, 1]`, `h = e₀`,
`N = 2`): the split, the coercive bound and the inverse formula all apply. -/
theorem finalHessian_instance :
    (finalHessian 3 9 3 3 (1 / 8 : ℝ) (1 : ℝ) (Pi.single 0 1 : Fin 2 → ℝ) =
      (1 : ℝ) • projH (ι := Torus 3 3) (Pi.single 0 1 : Fin 2 → ℝ) +
        spinLift 2 (unconstrainedUnitOperator 3 9 3 3 (1 / 8 : ℝ) 1) *
          (1 - projH (ι := Torus 3 3) (Pi.single 0 1 : Fin 2 → ℝ))) ∧
    (∀ u : Torus 3 3 × Fin 2 → ℝ, 1 / (8 * (3 : ℝ) + 3) * (1 / 8) * (u ⬝ᵥ u) ≤
      u ⬝ᵥ finalHessian 3 9 3 3 (1 / 8 : ℝ) (1 : ℝ) (Pi.single 0 1 : Fin 2 → ℝ) *ᵥ u) ∧
    IsUnit (finalHessian 3 9 3 3 (1 / 8 : ℝ) (1 : ℝ) (Pi.single 0 1 : Fin 2 → ℝ)).det := by
  have hh : ∑ i, (Pi.single 0 1 : Fin 2 → ℝ) i ^ 2 = 1 := by
    simp [Fin.sum_univ_two]
  have hℓ : (9 : ℕ) = 3 * 3 := by norm_num
  refine ⟨finalHessian_eq_split hℓ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh,
    fun u => ?_, ?_⟩
  · have := finalHessian_form_ge_mass (d := 3) (m := 3) (Nb := 3) hℓ (by norm_num) (by norm_num)
      (ν := 1 / 8) (a := 1) (by norm_num) (by norm_num) (by norm_num) hh u
    simpa using this
  · have hU := unconstrainedUnitOperator_isUnit_det (d := 3) (m := 3) (Nb := 3) hℓ
      (by norm_num) (by norm_num) (ν := 1 / 8) (a := 1) (by norm_num) (by norm_num)
    exact finalHessian_isUnit_det hℓ (by norm_num) (by norm_num) (ν := 1 / 8) (a := 1)
      (by norm_num) (by norm_num) hh hU

end Instance

end Balaban
