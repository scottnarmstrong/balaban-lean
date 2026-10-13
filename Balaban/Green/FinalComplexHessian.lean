/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalHessian
public import Balaban.Green.FinalComplexMatrix
public import Balaban.Multiscale.Constrained
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The final Hessian for a complex direction (FINAL §3, complex spin structure)

`notes/phase1/FINAL.md` §3.  For a complex vector `h : Fin N → ℂ` with `h·h = ∑ hᵢ² ≠ 0` (bilinear
form, no conjugation) put `P_h = 1 ⊗ (h hᵀ / (h·h))` (`projHC`), an idempotent on
`(sites × Fin N)`.  With a scalar complex operator `U` on the sites (here
`U = finalOp d L N₀ k v a`), the complex final Hessian is
`D(h) = a P_h + (U ⊗ 1)(1 - P_h)` (`finalHessianC`).

* `projHC`, `projHC_mul_self`, `liftOp_mul_projHC`: idempotent, commutes with every spin lift
  `Multiscale.liftOp N A = A ⊗ 1` (the landed lift is reused; there is no new `spinLiftC`).
  For a real unit vector `h` it is the complexification of the landed `projH h`
  (`projHC_ofReal`), so the landed real statements are the special case (`finalHessianC_ofReal`).
* entry bounds for `P_h` (`spinProj_norm_le`), and, for `h` within `ρ ≤ 1/4` of a real unit vector
  (in the sense `∑ᵢ ‖hᵢ - h₀ᵢ‖² ≤ ρ²`): `|h·h - 1| ≤ 2ρ + ρ²`, `h·h ≠ 0`,
  entries of `P_h` at most `25/7`, entries of `P_h - P_{h₀}` at most `11 ρ`.
* `finalHessianC_add_smul_one`, `finalHessianC_resolvent`: `D(h) + t = (a+t) P_h + (U+t)(1-P_h)`
  and its inverse `(a+t)⁻¹ P_h + (U+t)⁻¹ (1-P_h)`.
* entry decay of the resolvent, inverse, and the principal inverse square root
  (`sqrtMat D = a^{-1/2} P_h + (sqrtMat U)(1 - P_h)`), by the landed Combes–Thomas / Stieltjes
  estimates for the scalar operator.
* analyticity in `h` on `{h·h ≠ 0}` and, with a scalar perturbation `U + E(z)`, jointly in `(z, h)`.

NOT proved here: the identification of `finalHessianC` with the Hessian of the physical final
density (`FINAL-HESSIAN-BRIDGE`); the complex chart (`FINAL-COMPLEX-DOMAIN`), which must supply an
open set of chart parameters, a holomorphic map to `(E, h)` with `WSmall r η (E z)`, `η < g_*` and
`h·h ≠ 0` (resp. `h` in the ball above), and the identification of the physical Hessian with
`finalHessianC` for these; the cut-parameter family giving exact locality; the `k_f = 0` branch.
-/

@[expose] public section

open Matrix Finset MeasureTheory Set

namespace Balaban.Green

section Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The spin part `h hᵀ / (h·h)` of the complex projection (`h·h = ∑ hᵢ²`, no conjugation). -/
noncomputable def spinProj (h : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => h i * h j / ∑ k, h k ^ 2

/-- `1 ⊗ S`: the matrix `S` on the spin indices, identity on the sites. -/
noncomputable def idKron (S : Matrix (Fin N) (Fin N) ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  fun p q => if p.1 = q.1 then S p.2 q.2 else 0

/-- The complex spin projection `P_h = 1 ⊗ (h hᵀ / (h·h))` on `(sites × Fin N)`; it is
a projection when `h·h ≠ 0`. -/
noncomputable def projHC (h : Fin N → ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ := idKron (spinProj h)

omit [Fintype ι] in
theorem projHC_apply (h : Fin N → ℂ) (x y : ι) (i j : Fin N) :
    (projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) (x, i) (y, j) =
      if x = y then h i * h j / ∑ k, h k ^ 2 else 0 := rfl

theorem idKron_mul (S T : Matrix (Fin N) (Fin N) ℂ) :
    (idKron S * idKron T : Matrix (ι × Fin N) (ι × Fin N) ℂ) = idKron (S * T) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [idKron, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hxy : x = y
  · subst hxy
    simp
  · simp [hxy]

theorem liftOp_mul_idKron (A : Matrix ι ι ℂ) (S : Matrix (Fin N) (Fin N) ℂ) :
    (Multiscale.liftOp N A * idKron S : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      fun p q => A p.1 q.1 * S p.2 q.2 := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [Multiscale.liftOp, idKron, Matrix.mul_apply, Fintype.sum_prod_type]

theorem idKron_mul_liftOp (A : Matrix ι ι ℂ) (S : Matrix (Fin N) (Fin N) ℂ) :
    (idKron S * Multiscale.liftOp N A : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      fun p q => A p.1 q.1 * S p.2 q.2 := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [Multiscale.liftOp, idKron, Matrix.mul_apply, Fintype.sum_prod_type, mul_comm]

theorem liftOp_comm_idKron (A : Matrix ι ι ℂ) (S : Matrix (Fin N) (Fin N) ℂ) :
    (Multiscale.liftOp N A * idKron S : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      idKron S * Multiscale.liftOp N A := by
  rw [liftOp_mul_idKron, idKron_mul_liftOp]

theorem spinProj_mul_self {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    spinProj h * spinProj h = spinProj h := by
  ext i j
  simp only [spinProj, Matrix.mul_apply]
  have : ∀ k, (h i * h k / ∑ k, h k ^ 2) * (h k * h j / ∑ k, h k ^ 2) =
      (h i * h j / (∑ k, h k ^ 2) ^ 2) * h k ^ 2 := fun k => by
    field_simp
  simp_rw [this]
  rw [← Finset.mul_sum]
  field_simp

/-- `P_h` is idempotent when `h·h ≠ 0`. -/
theorem projHC_mul_self {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    (projHC h * projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) = projHC h := by
  unfold projHC
  rw [idKron_mul, spinProj_mul_self hs]

/-- `P_h` commutes with every spin lift `A ⊗ 1`. -/
theorem liftOp_mul_projHC (h : Fin N → ℂ) (A : Matrix ι ι ℂ) :
    (Multiscale.liftOp N A * projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      projHC h * Multiscale.liftOp N A := liftOp_comm_idKron _ _

theorem one_sub_projHC_mul_self {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    ((1 - projHC h) * (1 - projHC h) : Matrix (ι × Fin N) (ι × Fin N) ℂ) = 1 - projHC h := by
  simp only [mul_sub, sub_mul, one_mul, mul_one, projHC_mul_self hs]
  abel

theorem projHC_mul_one_sub {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    (projHC h * (1 - projHC h) : Matrix (ι × Fin N) (ι × Fin N) ℂ) = 0 := by
  rw [mul_sub, mul_one, projHC_mul_self hs, sub_self]

theorem one_sub_projHC_mul {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    ((1 - projHC h) * projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) = 0 := by
  rw [sub_mul, one_mul, projHC_mul_self hs, sub_self]

/-- Entries of `A ⊗ 1 · (1 - P_h)`: `A x y (δᵢⱼ - hᵢ hⱼ/(h·h))`. -/
theorem liftOp_mul_one_sub_projHC_apply (h : Fin N → ℂ) (A : Matrix ι ι ℂ) (x y : ι) (i j : Fin N) :
    (Multiscale.liftOp N A * (1 - projHC h) : Matrix (ι × Fin N) (ι × Fin N) ℂ) (x, i) (y, j) =
      A x y * ((if i = j then 1 else 0) - spinProj h i j) := by
  rw [mul_sub, mul_one, Matrix.sub_apply]
  have e : (Multiscale.liftOp N A * projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) (x, i) (y, j) =
      A x y * spinProj h i j :=
    congrFun (congrFun (liftOp_mul_idKron A (spinProj h)) (x, i)) (y, j)
  rw [e]
  simp only [Multiscale.liftOp]
  by_cases hij : i = j
  · subst hij; simp [mul_sub]
  · simp [hij]

omit [Fintype ι] in
/-- **Real special case.** For a real unit vector `h`, `P_h` is the complexification of the landed
`projH h`. -/
theorem projHC_ofReal {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    (projHC (fun i => (h i : ℂ)) : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      (projH (ι := ι) h).map (algebraMap ℝ ℂ) := by
  have hs : ∑ k, ((h k : ℂ)) ^ 2 = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hh
    simpa using this
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [projHC_apply, hs, div_one, projH, Matrix.map_apply]
  by_cases hxy : x = y <;> simp [hxy]

/-! ### Entry bounds -/

theorem spinProj_norm_le {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) (i j : Fin N) :
    ‖spinProj h i j‖ ≤ (∑ k, ‖h k‖ ^ 2) / ‖∑ k, h k ^ 2‖ := by
  unfold spinProj
  rw [norm_div, norm_mul]
  have hpos : 0 < ‖∑ k, h k ^ 2‖ := norm_pos_iff.2 hs
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have hi : ‖h i‖ ^ 2 ≤ ∑ k, ‖h k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖h k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hj : ‖h j‖ ^ 2 ≤ ∑ k, ‖h k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖h k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hS : 0 ≤ ∑ k, ‖h k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra hcon
  rw [not_le] at hcon
  have h1 : (∑ k, ‖h k‖ ^ 2) ^ 2 < (‖h i‖ * ‖h j‖) ^ 2 := by
    nlinarith [norm_nonneg (h i), norm_nonneg (h j)]
  have h2 : (‖h i‖ * ‖h j‖) ^ 2 ≤ (∑ k, ‖h k‖ ^ 2) ^ 2 := by
    rw [mul_pow]; nlinarith [sq_nonneg ‖h i‖, sq_nonneg ‖h j‖]
  linarith

end Spin

section Ball

variable {N : ℕ}

/-- **Ball around a real unit vector.**  If `∑ᵢ ‖hᵢ - h₀ᵢ‖² ≤ ρ²`, `∑ h₀ᵢ² = 1`, `0 ≤ ρ`:
`‖h·h - 1‖ ≤ 2ρ + ρ²`. -/
theorem sq_sum_sub_one_le {h : Fin N → ℂ} {h₀ : Fin N → ℝ} (hh₀ : ∑ i, h₀ i ^ 2 = 1) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hd : ∑ i, ‖h i - (h₀ i : ℂ)‖ ^ 2 ≤ ρ ^ 2) :
    ‖(∑ k, h k ^ 2) - 1‖ ≤ 2 * ρ + ρ ^ 2 := by
  have e : (∑ k, h k ^ 2) - 1 =
      ∑ k, (h k - (h₀ k : ℂ)) * ((h k - (h₀ k : ℂ)) + 2 * (h₀ k : ℂ)) := by
    have h1 : (1 : ℂ) = ∑ k, ((h₀ k : ℂ)) ^ 2 := by
      have := congrArg (fun r : ℝ => (r : ℂ)) hh₀
      simpa using this.symm
    rw [h1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hcs : (∑ k, ‖h k - (h₀ k : ℂ)‖ * ‖(h₀ k : ℂ)‖) ^ 2 ≤ ρ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖h k - (h₀ k : ℂ)‖)
      (fun k => ‖(h₀ k : ℂ)‖)
    have h2 : ∑ k, ‖(h₀ k : ℂ)‖ ^ 2 = 1 := by simpa using hh₀
    calc _ ≤ _ := this
      _ ≤ ρ ^ 2 * 1 := by rw [h2]; exact mul_le_mul_of_nonneg_right hd (by norm_num)
      _ = ρ ^ 2 := mul_one _
  have hcs' : ∑ k, ‖h k - (h₀ k : ℂ)‖ * ‖(h₀ k : ℂ)‖ ≤ ρ :=
    abs_le_of_sq_le_sq' hcs hρ |>.2
  rw [e]
  calc ‖∑ k, (h k - (h₀ k : ℂ)) * ((h k - (h₀ k : ℂ)) + 2 * (h₀ k : ℂ))‖
      ≤ ∑ k, ‖(h k - (h₀ k : ℂ)) * ((h k - (h₀ k : ℂ)) + 2 * (h₀ k : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖h k - (h₀ k : ℂ)‖ ^ 2 + 2 * (‖h k - (h₀ k : ℂ)‖ * ‖(h₀ k : ℂ)‖)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        have := norm_add_le (h k - (h₀ k : ℂ)) (2 * (h₀ k : ℂ))
        have h3 : ‖(2 : ℂ) * (h₀ k : ℂ)‖ = 2 * ‖(h₀ k : ℂ)‖ := by simp
        rw [h3] at this
        nlinarith [norm_nonneg (h k - (h₀ k : ℂ))]
    _ = ∑ k, ‖h k - (h₀ k : ℂ)‖ ^ 2 + 2 * ∑ k, ‖h k - (h₀ k : ℂ)‖ * ‖(h₀ k : ℂ)‖ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * ρ + ρ ^ 2 := by linarith

/-- Basic facts for `h` in the ball: `‖h·h - 1‖ ≤ 2ρ + ρ²`, `7/16 ≤ ‖h·h‖` (for `ρ ≤ 1/4`),
coordinates `‖hᵢ - h₀ᵢ‖ ≤ ρ`, `‖hᵢ‖ ≤ 1 + ρ`. -/
theorem ball_facts {h : Fin N → ℂ} {h₀ : Fin N → ℝ} (hh₀ : ∑ i, h₀ i ^ 2 = 1) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ4 : ρ ≤ 1 / 4) (hd : ∑ i, ‖h i - (h₀ i : ℂ)‖ ^ 2 ≤ ρ ^ 2) :
    ‖(∑ k, h k ^ 2) - 1‖ ≤ 2 * ρ + ρ ^ 2 ∧ 7 / 16 ≤ ‖∑ k, h k ^ 2‖ ∧
      (∀ i, ‖h i - (h₀ i : ℂ)‖ ≤ ρ) ∧ (∀ i, ‖h i‖ ≤ 1 + ρ) ∧ (∀ i, ‖(h₀ i : ℂ)‖ ≤ 1) := by
  have h1 := sq_sum_sub_one_le hh₀ hρ hd
  have hδ : ∀ i, ‖h i - (h₀ i : ℂ)‖ ≤ ρ := fun i => by
    have : ‖h i - (h₀ i : ℂ)‖ ^ 2 ≤ ρ ^ 2 :=
      (Finset.single_le_sum (f := fun k => ‖h k - (h₀ k : ℂ)‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)).trans hd
    exact (abs_le_of_sq_le_sq' this hρ).2
  have h0 : ∀ i, ‖(h₀ i : ℂ)‖ ≤ 1 := fun i => by
    have h2 : ∑ k, ‖(h₀ k : ℂ)‖ ^ 2 = 1 := by simpa using hh₀
    have : ‖(h₀ i : ℂ)‖ ^ 2 ≤ 1 ^ 2 := by
      rw [one_pow, ← h2]
      exact Finset.single_le_sum (f := fun k => ‖(h₀ k : ℂ)‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact (abs_le_of_sq_le_sq' this zero_le_one).2
  refine ⟨h1, ?_, hδ, fun i => ?_, h0⟩
  · have := norm_sub_norm_le (1 : ℂ) (∑ k, h k ^ 2)
    rw [norm_sub_rev] at this
    simp only [norm_one] at this
    nlinarith
  · have := norm_le_insert' (h i) (h₀ i : ℂ)
    have h3 : ‖h i‖ ≤ ‖h i - (h₀ i : ℂ)‖ + ‖(h₀ i : ℂ)‖ := by
      calc ‖h i‖ = ‖(h i - (h₀ i : ℂ)) + (h₀ i : ℂ)‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith [hδ i, h0 i]

/-- **Entries of `P_h` in the ball** (`ρ ≤ 1/4`): `‖hᵢ hⱼ/(h·h)‖ ≤ 25/7`, and `h·h ≠ 0`. -/
theorem spinProj_norm_le_ball {h : Fin N → ℂ} {h₀ : Fin N → ℝ} (hh₀ : ∑ i, h₀ i ^ 2 = 1) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ4 : ρ ≤ 1 / 4) (hd : ∑ i, ‖h i - (h₀ i : ℂ)‖ ^ 2 ≤ ρ ^ 2) (i j : Fin N) :
    ∑ k, h k ^ 2 ≠ 0 ∧ ‖spinProj h i j‖ ≤ 25 / 7 := by
  obtain ⟨-, hs, -, hh, -⟩ := ball_facts hh₀ hρ hρ4 hd
  have hpos : 0 < ‖∑ k, h k ^ 2‖ := by linarith
  refine ⟨norm_pos_iff.1 hpos, ?_⟩
  unfold spinProj
  rw [norm_div, norm_mul, div_le_iff₀ hpos]
  have := hh i
  have := hh j
  nlinarith [norm_nonneg (h i), norm_nonneg (h j), mul_le_mul (hh i) (hh j) (norm_nonneg _) (by linarith)]

/-- **Lipschitz bound for `P_h`** (`ρ ≤ 1/4`): `‖hᵢ hⱼ/(h·h) - h₀ᵢ h₀ⱼ‖ ≤ 11 ρ`, i.e. the entries of
`P_h - P_{h₀}` are at most `11 ρ`. -/
theorem spinProj_sub_le_ball {h : Fin N → ℂ} {h₀ : Fin N → ℝ} (hh₀ : ∑ i, h₀ i ^ 2 = 1) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ4 : ρ ≤ 1 / 4) (hd : ∑ i, ‖h i - (h₀ i : ℂ)‖ ^ 2 ≤ ρ ^ 2) (i j : Fin N) :
    ‖spinProj h i j - ((h₀ i * h₀ j : ℝ) : ℂ)‖ ≤ 11 * ρ := by
  obtain ⟨h1, hs, hδ, hh, h0⟩ := ball_facts hh₀ hρ hρ4 hd
  have hpos : 0 < ‖∑ k, h k ^ 2‖ := by linarith
  have hne : ∑ k, h k ^ 2 ≠ 0 := norm_pos_iff.1 hpos
  set s : ℂ := ∑ k, h k ^ 2 with hsdef
  have e : spinProj h i j - ((h₀ i * h₀ j : ℝ) : ℂ) =
      ((h i - (h₀ i : ℂ)) * h j + (h₀ i : ℂ) * (h j - (h₀ j : ℂ)) +
        (h₀ i : ℂ) * (h₀ j : ℂ) * (1 - s)) / s := by
    simp only [spinProj, ← hsdef]
    push_cast
    field_simp
    ring
  rw [e, norm_div, div_le_iff₀ hpos]
  have n1 : ‖(h i - (h₀ i : ℂ)) * h j‖ ≤ ρ * (1 + ρ) := by
    rw [norm_mul]; exact mul_le_mul (hδ i) (hh j) (norm_nonneg _) hρ
  have n2 : ‖(h₀ i : ℂ) * (h j - (h₀ j : ℂ))‖ ≤ 1 * ρ := by
    rw [norm_mul]; exact mul_le_mul (h0 i) (hδ j) (norm_nonneg _) zero_le_one
  have n3 : ‖(h₀ i : ℂ) * (h₀ j : ℂ) * (1 - s)‖ ≤ 1 * 1 * (2 * ρ + ρ ^ 2) := by
    rw [norm_mul, norm_mul, norm_sub_rev]
    exact mul_le_mul (mul_le_mul (h0 i) (h0 j) (norm_nonneg _) zero_le_one) h1 (norm_nonneg _)
      (by norm_num)
  have := norm_add_le ((h i - (h₀ i : ℂ)) * h j + (h₀ i : ℂ) * (h j - (h₀ j : ℂ)))
    ((h₀ i : ℂ) * (h₀ j : ℂ) * (1 - s))
  have := norm_add_le ((h i - (h₀ i : ℂ)) * h j) ((h₀ i : ℂ) * (h j - (h₀ j : ℂ)))
  nlinarith

end Ball

section Hess

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem liftOp_add_eq (A B : Matrix ι ι ℂ) :
    Multiscale.liftOp N (A + B) = Multiscale.liftOp N A + Multiscale.liftOp N B := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j <;> simp [Multiscale.liftOp, hij]

omit [Fintype ι] [DecidableEq ι] in
theorem liftOp_smul_eq (c : ℂ) (A : Matrix ι ι ℂ) :
    Multiscale.liftOp N (c • A) = c • Multiscale.liftOp N A := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j <;> simp [Multiscale.liftOp, hij]

/-- **The complex Hessian from a scalar operator.** `D = a P_h + (U ⊗ 1)(1 - P_h)`. -/
noncomputable def hessC (N : ℕ) (a : ℂ) (U : Matrix ι ι ℂ) (h : Fin N → ℂ) :
    Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  a • projHC h + Multiscale.liftOp N U * (1 - projHC h)

/-- `D + t = (a + t) P_h + (U + t)(1 - P_h)`. -/
theorem hessC_add_smul_one (a t : ℂ) (U : Matrix ι ι ℂ) (h : Fin N → ℂ) :
    hessC N a U h + t • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      hessC N (a + t) (U + t • (1 : Matrix ι ι ℂ)) h := by
  unfold hessC
  rw [liftOp_add_eq, liftOp_smul_eq, Multiscale.liftOp_one]
  simp only [add_smul, add_mul, smul_mul_assoc, one_mul, smul_sub]
  abel

/-- Inverse of the complex Hessian: `D⁻¹ = a⁻¹ P_h + U⁻¹ (1 - P_h)`; `D` is invertible. -/
theorem hessC_inv {a : ℂ} (ha : a ≠ 0) {U : Matrix ι ι ℂ} (hU : IsUnit U) {h : Fin N → ℂ}
    (hs : ∑ k, h k ^ 2 ≠ 0) :
    IsUnit (hessC N a U h) ∧
      (hessC N a U h)⁻¹ =
        a⁻¹ • projHC h + Multiscale.liftOp N U⁻¹ * (1 - projHC h) := by
  have hUd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hUd
  have hPP := projHC_mul_self (ι := ι) hs
  have hc : ∀ B : Matrix ι ι ℂ, (projHC h * Multiscale.liftOp N B : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      Multiscale.liftOp N B * projHC h := fun B => (liftOp_mul_projHC h B).symm
  have h1 : (projHC h * (Multiscale.liftOp N U⁻¹ * (1 - projHC h)) :
      Matrix (ι × Fin N) (ι × Fin N) ℂ) = 0 := by
    rw [← mul_assoc, hc, mul_assoc, projHC_mul_one_sub hs, mul_zero]
  have h2 : ((Multiscale.liftOp N U * (1 - projHC h)) * projHC h :
      Matrix (ι × Fin N) (ι × Fin N) ℂ) = 0 := by
    rw [mul_assoc, one_sub_projHC_mul hs, mul_zero]
  have h3 : ((Multiscale.liftOp N U * (1 - projHC h)) *
      (Multiscale.liftOp N U⁻¹ * (1 - projHC h)) : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
      1 - projHC h := by
    have hc2 : ((1 - projHC h) * Multiscale.liftOp N U⁻¹ : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
        Multiscale.liftOp N U⁻¹ * (1 - projHC h) := by
      rw [sub_mul, mul_sub, mul_one, one_mul, hc]
    rw [mul_assoc, ← mul_assoc (1 - projHC h), hc2, ← mul_assoc, ← mul_assoc,
      ← Multiscale.liftOp_mul, hUU, Multiscale.liftOp_one, one_mul]
    exact one_sub_projHC_mul_self hs
  have hmul : hessC N a U h * (a⁻¹ • projHC h + Multiscale.liftOp N U⁻¹ * (1 - projHC h)) = 1 := by
    unfold hessC
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hPP, h1, h2, h3, smul_zero,
      smul_smul, inv_mul_cancel₀ ha, one_smul, zero_add, add_zero]
    abel
  refine ⟨?_, Matrix.inv_eq_right_inv hmul⟩
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hmul)

/-- **Resolvent of the complex Hessian.** If `a + t ≠ 0` and `U + t` is invertible, then `D + t` is
invertible with inverse `(a+t)⁻¹ P_h + (U+t)⁻¹ (1 - P_h)`. -/
theorem hessC_resolvent {a t : ℂ} (hat : a + t ≠ 0) {U : Matrix ι ι ℂ}
    (hU : IsUnit (U + t • (1 : Matrix ι ι ℂ))) {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    IsUnit (hessC N a U h + t • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ)) ∧
      (hessC N a U h + t • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ))⁻¹ =
        (a + t)⁻¹ • projHC h +
          Multiscale.liftOp N (U + t • (1 : Matrix ι ι ℂ))⁻¹ * (1 - projHC h) := by
  rw [hessC_add_smul_one]
  exact hessC_inv hat hU hs

end Hess

section HessEntries

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Entries of the resolvent: `(D + t)⁻¹ (x,i) (y,j) =
(a+t)⁻¹ [x=y] hᵢhⱼ/(h·h) + (U+t)⁻¹ x y (δᵢⱼ - hᵢhⱼ/(h·h))`. -/
theorem hessC_resolvent_apply {a t : ℂ} (hat : a + t ≠ 0) {U : Matrix ι ι ℂ}
    (hU : IsUnit (U + t • (1 : Matrix ι ι ℂ))) {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0)
    (x y : ι) (i j : Fin N) :
    (hessC N a U h + t • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ))⁻¹ (x, i) (y, j) =
      (a + t)⁻¹ * (if x = y then spinProj h i j else 0) +
        (U + t • (1 : Matrix ι ι ℂ))⁻¹ x y * ((if i = j then 1 else 0) - spinProj h i j) := by
  rw [(hessC_resolvent hat hU hs).2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    liftOp_mul_one_sub_projHC_apply]
  rfl

/-- **Real special case of the algebra.** -/
theorem hessC_ofReal {a : ℝ} (U : Matrix ι ι ℝ) {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) :
    hessC N (a : ℂ) (U.map (algebraMap ℝ ℂ)) (fun i => (h i : ℂ)) =
      (a • projH (ι := ι) h + spinLift N U * (1 - projH (ι := ι) h)).map (algebraMap ℝ ℂ) := by
  have hm : ∀ M : Matrix (ι × Fin N) (ι × Fin N) ℝ,
      M.map (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ).mapMatrix M := fun M => rfl
  have hs : ∀ (c : ℝ) (M : Matrix (ι × Fin N) (ι × Fin N) ℝ),
      (c • M).map (algebraMap ℝ ℂ) = (c : ℂ) • M.map (algebraMap ℝ ℂ) := fun c M => by
    ext p q; simp [Matrix.smul_apply]
  have hl : (spinLift N U).map (algebraMap ℝ ℂ) = Multiscale.liftOp N (U.map (algebraMap ℝ ℂ)) := by
    ext ⟨x, i⟩ ⟨y, j⟩
    by_cases hij : i = j <;> simp [spinLift, Multiscale.liftOp, hij]
  unfold hessC
  rw [projHC_ofReal hh, hm (a • projH (ι := ι) h + spinLift N U * (1 - projH (ι := ι) h)),
    map_add, map_mul, map_sub, map_one]
  simp only [RingHom.mapMatrix_apply, hs, hl]

end HessEntries

section Final

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

private instance : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩

/-- **The complex final Hessian** `D(h) = a P_h + (U ⊗ 1)(1 - P_h)` for a complex direction `h`
with `h·h ≠ 0`, where `U = finalOp d L N₀ k v a` is the scalar reference operator of
`Green/FinalMassGreen.lean`. -/
noncomputable def finalHessianC (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  hessC N (a : ℂ) (finalOp d L N₀ k v a) h

/-- **Real special case.**  For a real unit vector `h`, `finalHessianC` is the complexification of
the landed real `finalHessian` (on `Torus d N₀ × Fin N`; `L1Torus d N₀` is `Torus d N₀` with the
`ℓ¹` metric, and `finalOp` is the complexified `unconstrainedUnitOperator`, so the identification
is by definition). -/
theorem finalHessianC_ofReal (hd : 0 < d) {v a : ℝ} (hv : 0 ≤ v) (ha : 0 < a) {h : Fin N → ℝ}
    (hh : ∑ i, h i ^ 2 = 1) :
    finalHessianC d L N₀ k v a (fun i => (h i : ℂ)) =
      (finalHessian d (N₀ * L ^ k) (L ^ k) N₀ v a h).map (algebraMap ℝ ℂ) := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  rw [finalHessian_eq_split (mul_comm _ _) hN hd hv ha hh]
  exact hessC_ofReal (ι := Torus d N₀) _ hh

end Final

section FinalDecay

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- **Resolvent decay of the complex final Hessian (T3).**  For `h·h ≠ 0` with all entries of
`P_h` (the spin part `hᵢhⱼ/(h·h)`) bounded by `p`, and `t ≥ 0`: `D(h) + t` is invertible and
`‖(D(h) + t)⁻¹ (x,i) (y,j)‖ ≤ p (a+t)⁻¹ [x=y] + (1+p) · 2/(g_*+t) · e^{-r_* dist x y}`. -/
theorem finalHessianC_resolvent_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (finalHessianC d L N₀ k v a h + (t : ℂ) •
        (1 : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ)) ∧
      ∀ (x y : L1Torus d N₀) (i j : Fin N),
        ‖(finalHessianC d L N₀ k v a h + (t : ℂ) •
            (1 : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ))⁻¹ (x, i) (y, j)‖ ≤
          p * (a + t)⁻¹ * (if x = y then 1 else 0) +
            (1 + p) * (2 / (finalGap d L + t)) * Real.exp (-finalRate d L * dist x y) := by
  have ha0 : 0 < a := by linarith
  have hat : (a : ℂ) + (t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]; exact_mod_cast (by linarith : a + t ≠ 0)
  obtain ⟨hU, hb⟩ := finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht
  refine ⟨(hessC_resolvent hat hU hs).1, fun x y i j => ?_⟩
  unfold finalHessianC
  rw [hessC_resolvent_apply hat hU hs]
  have hP : ‖(if x = y then spinProj h i j else 0)‖ ≤ p * (if x = y then 1 else 0) := by
    split_ifs
    · simpa using hp i j
    · simp
  have hD : ‖((if i = j then 1 else 0) - spinProj h i j : ℂ)‖ ≤ 1 + p :=
    (norm_sub_le _ _).trans (add_le_add (by split_ifs <;> simp) (hp i j))
  have hc : ‖((a : ℂ) + (t : ℂ))⁻¹‖ = (a + t)⁻¹ := by
    rw [norm_inv, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hW := hb x y
  have hWn : 0 ≤ 2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y) :=
    le_trans (norm_nonneg _) hW
  calc _ ≤ ‖((a : ℂ) + (t : ℂ))⁻¹ * (if x = y then spinProj h i j else 0)‖ +
        ‖(finalOp d L N₀ k v a + (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y *
          ((if i = j then 1 else 0) - spinProj h i j)‖ := norm_add_le _ _
    _ ≤ (a + t)⁻¹ * (p * (if x = y then 1 else 0)) +
        (2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y)) * (1 + p) := by
        rw [norm_mul, norm_mul, hc]
        exact add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
          (mul_le_mul hW hD (norm_nonneg _) hWn)
    _ = _ := by ring

/-- **Uniform form of the resolvent bound.**  With `g' = min g_* a`, `K = 3p + 2` (and `p ≥ 0`):
`‖(D(h) + t)⁻¹ (x,i) (y,j)‖ ≤ K/(g' + t) · e^{-r_* dist x y}`. -/
theorem finalHessianC_resolvent_decay_uniform (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {t : ℝ} (ht : 0 ≤ t)
    (x y : L1Torus d N₀) (i j : Fin N) :
    ‖(finalHessianC d L N₀ k v a h + (t : ℂ) •
        (1 : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ))⁻¹ (x, i) (y, j)‖ ≤
      (3 * p + 2) / (min (finalGap d L) a + t) * Real.exp (-finalRate d L * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have ha0 : 0 < a := by linarith
  have hm : 0 < min (finalGap d L) a := lt_min hg ha0
  refine ((finalHessianC_resolvent_decay hd hk hv0 hv1 ha1 ha2 hmass hs hp ht).2 x y i j).trans ?_
  have he : 0 < Real.exp (-finalRate d L * dist x y) := Real.exp_pos _
  have h1 : (a + t)⁻¹ ≤ (min (finalGap d L) a + t)⁻¹ :=
    inv_anti₀ (by linarith) (by linarith [min_le_right (finalGap d L) a])
  have h2 : 1 / (finalGap d L + t) ≤ 1 / (min (finalGap d L) a + t) :=
    one_div_le_one_div_of_le (by linarith) (by linarith [min_le_left (finalGap d L) a])
  have h3 : (if x = y then (1 : ℝ) else 0) ≤ Real.exp (-finalRate d L * dist x y) := by
    split_ifs with hxy
    · subst hxy; simp
    · exact he.le
  have hinv : (0 : ℝ) ≤ (a + t)⁻¹ := by positivity
  have e1 : p * (a + t)⁻¹ * (if x = y then 1 else 0) ≤
      p * (min (finalGap d L) a + t)⁻¹ * Real.exp (-finalRate d L * dist x y) := by
    have : (0 : ℝ) ≤ (if x = y then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hp0) h3 this (by positivity)
  have e2 : (1 + p) * (2 / (finalGap d L + t)) * Real.exp (-finalRate d L * dist x y) ≤
      (1 + p) * (2 / (min (finalGap d L) a + t)) * Real.exp (-finalRate d L * dist x y) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by linarith)) he.le
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
    simpa [div_eq_mul_inv, mul_one] using this
  calc _ ≤ _ := add_le_add e1 e2
    _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring

/-- **Inverse of the complex final Hessian (T3, `t = 0`).**  `D(h)` is invertible and
`‖D(h)⁻¹ (x,i) (y,j)‖ ≤ p a⁻¹ [x=y] + (1+p) (2/g_*) e^{-r_* dist x y}`.  For real unit `h`
(`p = 1`) compare the note's `(2 + 2/g_*)`: here `a⁻¹ + 4/g_*`, the factor `1 + p` bounding
`δᵢⱼ - hᵢhⱼ/(h·h)` for complex `h`. -/
theorem finalHessianC_inverse_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) :
    IsUnit (finalHessianC d L N₀ k v a h) ∧
      ∀ (x y : L1Torus d N₀) (i j : Fin N),
        ‖(finalHessianC d L N₀ k v a h)⁻¹ (x, i) (y, j)‖ ≤
          p * a⁻¹ * (if x = y then 1 else 0) +
            (1 + p) * (2 / finalGap d L) * Real.exp (-finalRate d L * dist x y) := by
  obtain ⟨hu, hb⟩ := finalHessianC_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hs hp
    (le_refl (0 : ℝ))
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hu hb
  refine ⟨hu, fun x y i j => ?_⟩
  simpa using hb x y i j

/-- The inverse is `a⁻¹ P_h + (U⁻¹ ⊗ 1)(1 - P_h)` (T2). -/
theorem finalHessianC_inv_eq (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) :
    (finalHessianC d L N₀ k v a h)⁻¹ =
      (a : ℂ)⁻¹ • projHC h + Multiscale.liftOp N (finalOp d L N₀ k v a)⁻¹ * (1 - projHC h) := by
  have ha0 : 0 < a := by linarith
  have hU := (finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass (le_refl (0 : ℝ))).1
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hU
  exact (hessC_inv (Complex.ofReal_ne_zero.2 ha0.ne') hU hs).2

end FinalDecay

section Sqrt

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The Stieltjes integral, entrywise. -/
theorem sqrtMat_apply_eq {κ : Type*} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ ℂ) (p q : κ) :
    Localization.sqrtMat B p q =
      ((1 / Real.pi : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ),
        ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((y : ℂ) • (1 : Matrix κ κ ℂ) + B)⁻¹ p q := rfl

/-- **The principal inverse square root of the complex Hessian (T4).**  For `a > 0`, `U` with
resolvent entries (`ResOK`) and `h·h ≠ 0`, `D(h)` has resolvent entries and
`sqrtMat D(h) = a^{-1/2} P_h + (sqrtMat U ⊗ 1)(1 - P_h)`. -/
theorem sqrtMat_hessC [Nonempty ι] [NeZero N] {a : ℝ} (ha : 0 < a) {U : Matrix ι ι ℂ}
    (hU : Localization.ResOK U) {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0) :
    Localization.ResOK (hessC N (a : ℂ) U h) ∧
      Localization.sqrtMat (hessC N (a : ℂ) U h) =
        ((1 / Real.sqrt a : ℝ) : ℂ) • projHC h +
          Multiscale.liftOp N (Localization.sqrtMat U) * (1 - projHC h) := by
  have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  have hat : ∀ y : ℝ, 0 ≤ y → (a : ℂ) + (y : ℂ) ≠ 0 := fun y hy => by
    rw [← Complex.ofReal_add]; exact_mod_cast (by linarith : a + y ≠ 0)
  have hUy : ∀ y : ℝ, 0 ≤ y → IsUnit (U + (y : ℂ) • (1 : Matrix ι ι ℂ)) := fun y hy => by
    rw [add_comm]; exact hU y hy
  have hA : Localization.ResOK (hessC N (a : ℂ) U h) := fun y hy => by
    rw [add_comm]; exact (hessC_resolvent (hat y hy) (hUy y hy) hs).1
  refine ⟨hA, ?_⟩
  ext ⟨x, i⟩ ⟨z, j⟩
  have hsq : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hres : ∀ y ∈ Ioi (0 : ℝ),
      ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ((y : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) + hessC N (a : ℂ) U h)⁻¹ (x, i) (z, j) =
        (if x = z then spinProj h i j else 0) *
            (((y ^ (-(1 / 2 : ℝ)) * (a + y)⁻¹ : ℝ)) : ℂ) +
          (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((y : ℂ) • (1 : Matrix ι ι ℂ) + U)⁻¹ x z) *
            ((if i = j then 1 else 0) - spinProj h i j) := by
    intro y hy
    have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
    rw [add_comm, hessC_resolvent_apply (hat y hy0) (hUy y hy0) hs, add_comm (U) _]
    push_cast
    ring
  have hf1 : Integrable (fun y : ℝ => (((y ^ (-(1 / 2 : ℝ)) * (a + y)⁻¹ : ℝ)) : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Localization.integrableOn_rpow_inv_add ha).ofReal
  have hf2 := Localization.integrable_sqrt_entry hU x z
  have hI1 : ∫ y in Ioi (0 : ℝ), (((y ^ (-(1 / 2 : ℝ)) * (a + y)⁻¹ : ℝ)) : ℂ) =
      ((Real.pi / Real.sqrt a : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, Localization.integral_rpow_inv_add ha]
  have hlhs : Localization.sqrtMat (hessC N (a : ℂ) U h) (x, i) (z, j) =
      ((1 / Real.pi : ℝ) : ℂ) * ((if x = z then spinProj h i j else 0) *
          ((Real.pi / Real.sqrt a : ℝ) : ℂ) +
        (∫ y in Ioi (0 : ℝ), ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ((y : ℂ) • (1 : Matrix ι ι ℂ) + U)⁻¹ x z) *
          ((if i = j then 1 else 0) - spinProj h i j)) := by
    rw [sqrtMat_apply_eq, setIntegral_congr_fun measurableSet_Ioi hres,
      integral_add (hf1.const_mul _) (hf2.mul_const _), integral_const_mul, integral_mul_const, hI1]
  have hP : (projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) (x, i) (z, j) =
      if x = z then spinProj h i j else 0 := rfl
  rw [hlhs, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hP,
    liftOp_mul_one_sub_projHC_apply, sqrtMat_apply_eq (B := U) x z]
  push_cast
  generalize spinProj h i j = Q
  generalize (∫ y in Ioi (0 : ℝ), ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    ((y : ℂ) • (1 : Matrix ι ι ℂ) + U)⁻¹ x z) = I
  by_cases hxz : x = z <;> simp only [hxz, ite_true, ite_false] <;> field_simp

end Sqrt

section FinalSqrt

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- **Square root of the final complex Hessian (T4).**  `D(h)` has resolvent entries (`ResOK`),
`sqrtMat D(h) = a^{-1/2} P_h + (sqrtMat U ⊗ 1)(1 - P_h)` with `U = finalOp`, and
`sqrtMat D(h)² = D(h)⁻¹`. -/
theorem finalHessianC_sqrt_eq (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) [NeZero N]
    {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) :
    Localization.ResOK (finalHessianC d L N₀ k v a h) ∧
      Localization.sqrtMat (finalHessianC d L N₀ k v a h) =
        ((1 / Real.sqrt a : ℝ) : ℂ) • projHC h +
          Multiscale.liftOp N (Localization.sqrtMat (finalOp d L N₀ k v a)) * (1 - projHC h) ∧
      Localization.sqrtMat (finalHessianC d L N₀ k v a h) *
          Localization.sqrtMat (finalHessianC d L N₀ k v a h) =
        (finalHessianC d L N₀ k v a h)⁻¹ := by
  have ha0 : 0 < a := by linarith
  obtain ⟨hA, he⟩ := sqrtMat_hessC ha0
    (finalMass_resOK (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass) hs
  exact ⟨hA, he, Localization.sqrtMat_mul_self hA⟩

/-- **Entry decay of the square root of the complex final Hessian (T4).**
`‖sqrtMat D(h) (x,i) (y,j)‖ ≤ p a^{-1/2} [x=y] + (1+p) (2/√g_*) e^{-r_* dist x y}`. -/
theorem finalHessianC_sqrt_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) [NeZero N]
    {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    (x y : L1Torus d N₀) (i j : Fin N) :
    ‖Localization.sqrtMat (finalHessianC d L N₀ k v a h) (x, i) (y, j)‖ ≤
      p * (1 / Real.sqrt a) * (if x = y then 1 else 0) +
        (1 + p) * (2 / Real.sqrt (finalGap d L)) * Real.exp (-finalRate d L * dist x y) := by
  have ha0 : 0 < a := by linarith
  rw [(finalHessianC_sqrt_eq (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hs).2.1, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, liftOp_mul_one_sub_projHC_apply]
  have hP : (projHC h : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ) (x, i) (y, j) =
      if x = y then spinProj h i j else 0 := rfl
  rw [hP]
  have hP' : ‖(if x = y then spinProj h i j else 0)‖ ≤ p * (if x = y then 1 else 0) := by
    split_ifs
    · simpa using hp i j
    · simp
  have hD : ‖((if i = j then 1 else 0) - spinProj h i j : ℂ)‖ ≤ 1 + p :=
    (norm_sub_le _ _).trans (add_le_add (by split_ifs <;> simp) (hp i j))
  have hc : ‖((1 / Real.sqrt a : ℝ) : ℂ)‖ = 1 / Real.sqrt a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hW := finalMass_sqrt_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass x y
  have hWn : 0 ≤ 2 / Real.sqrt (finalGap d L) * Real.exp (-finalRate d L * dist x y) :=
    le_trans (norm_nonneg _) hW
  calc _ ≤ ‖((1 / Real.sqrt a : ℝ) : ℂ) * (if x = y then spinProj h i j else 0)‖ +
        ‖Localization.sqrtMat (finalOp d L N₀ k v a) x y *
          ((if i = j then 1 else 0) - spinProj h i j)‖ := norm_add_le _ _
    _ ≤ 1 / Real.sqrt a * (p * (if x = y then 1 else 0)) +
        (2 / Real.sqrt (finalGap d L) * Real.exp (-finalRate d L * dist x y)) * (1 + p) := by
        rw [norm_mul, norm_mul, hc]
        exact add_le_add (mul_le_mul_of_nonneg_left hP' (by positivity))
          (mul_le_mul hW hD (norm_nonneg _) hWn)
    _ = _ := by ring

end FinalSqrt

section Analytic

variable {N : ℕ}

theorem eventually_sum_sq_ne_zero {h₀ : Fin N → ℂ} (hs : ∑ k, h₀ k ^ 2 ≠ 0) :
    ∀ᶠ h in nhds h₀, ∑ k, h k ^ 2 ≠ 0 := by
  have hc : Continuous fun h : Fin N → ℂ => ∑ k, h k ^ 2 :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).pow 2
  exact hc.continuousAt.eventually_ne hs

theorem isOpen_sum_sq_ne_zero : IsOpen {h : Fin N → ℂ | ∑ k, h k ^ 2 ≠ 0} := by
  have hc : Continuous fun h : Fin N → ℂ => ∑ k, h k ^ 2 :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).pow 2
  exact isOpen_ne_fun hc continuous_const

/-- **Holomorphy of the spin projection (T5).**  `h ↦ hᵢhⱼ/(h·h)` is analytic wherever
`h·h ≠ 0`. -/
theorem spinProj_analyticAt {h₀ : Fin N → ℂ} (hs : ∑ k, h₀ k ^ 2 ≠ 0) (i j : Fin N) :
    AnalyticAt ℂ (fun h : Fin N → ℂ => spinProj h i j) h₀ := by
  have hproj : ∀ k, AnalyticAt ℂ (fun h : Fin N → ℂ => h k) h₀ := fun k =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) k).analyticAt h₀
  unfold spinProj
  exact ((hproj i).mul (hproj j)).div
    (Finset.analyticAt_fun_sum _ fun k _ => (hproj k).pow 2) hs

end Analytic

section AnalyticFinal

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- Entries of the inverse: `D⁻¹ (x,i) (y,j) = a⁻¹ [x=y] Qᵢⱼ + U⁻¹ x y (δᵢⱼ - Qᵢⱼ)`. -/
theorem hessC_inv_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {a : ℂ} (ha : a ≠ 0)
    {U : Matrix ι ι ℂ} (hU : IsUnit U) {h : Fin N → ℂ} (hs : ∑ k, h k ^ 2 ≠ 0)
    (x y : ι) (i j : Fin N) :
    (hessC N a U h)⁻¹ (x, i) (y, j) =
      a⁻¹ * (if x = y then spinProj h i j else 0) +
        U⁻¹ x y * ((if i = j then 1 else 0) - spinProj h i j) := by
  rw [(hessC_inv ha hU hs).2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    liftOp_mul_one_sub_projHC_apply]
  rfl

/-- Analyticity of `h ↦ c₁ [x=y] Qᵢⱼ(h) + c₂ (δᵢⱼ - Qᵢⱼ(h))` on `{h·h ≠ 0}`. -/
theorem analyticAt_affine_spinProj {ι : Type*} [DecidableEq ι] {h₀ : Fin N → ℂ}
    (hs : ∑ k, h₀ k ^ 2 ≠ 0) (c₁ c₂ : ℂ) (x y : ι) (i j : Fin N) :
    AnalyticAt ℂ (fun h : Fin N → ℂ => c₁ * (if x = y then spinProj h i j else 0) +
      c₂ * ((if i = j then 1 else 0) - spinProj h i j)) h₀ := by
  have hq := spinProj_analyticAt hs i j
  refine (analyticAt_const.mul ?_).add (analyticAt_const.mul (analyticAt_const.sub hq))
  by_cases hxy : x = y
  · simpa [hxy] using hq
  · simpa [hxy] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin N → ℂ => (0 : ℂ)) h₀)

/-- **Holomorphy in `h` of the inverse (T5).**  On the open set `{h·h ≠ 0}`, every entry of
`D(h)⁻¹` is analytic in `h`. -/
theorem finalHessianC_inv_analytic (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (x y : L1Torus d N₀) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun h : Fin N → ℂ => (finalHessianC d L N₀ k v a h)⁻¹ (x, i) (y, j))
      {h | ∑ k, h k ^ 2 ≠ 0} := by
  have ha0 : 0 < a := by linarith
  have hU := (finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass (le_refl (0 : ℝ))).1
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hU
  have hg : AnalyticOnNhd ℂ (fun h : Fin N → ℂ => (a : ℂ)⁻¹ * (if x = y then spinProj h i j else 0) +
      (finalOp d L N₀ k v a)⁻¹ x y * ((if i = j then 1 else 0) - spinProj h i j))
      {h | ∑ k, h k ^ 2 ≠ 0} := fun h₀ hh₀ =>
    analyticAt_affine_spinProj hh₀ _ _ x y i j
  refine hg.congr isOpen_sum_sq_ne_zero fun h hh => ?_
  exact (hessC_inv_apply (Complex.ofReal_ne_zero.2 ha0.ne') hU hh x y i j).symm

/-- **Holomorphy in `h` of the square root (T5).** -/
theorem finalHessianC_sqrt_analytic (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) [NeZero N]
    (x y : L1Torus d N₀) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun h : Fin N → ℂ =>
        Localization.sqrtMat (finalHessianC d L N₀ k v a h) (x, i) (y, j))
      {h | ∑ k, h k ^ 2 ≠ 0} := by
  have hg : AnalyticOnNhd ℂ (fun h : Fin N → ℂ => ((1 / Real.sqrt a : ℝ) : ℂ) *
      (if x = y then spinProj h i j else 0) +
      Localization.sqrtMat (finalOp d L N₀ k v a) x y * ((if i = j then 1 else 0) - spinProj h i j))
      {h | ∑ k, h k ^ 2 ≠ 0} := fun h₀ hh₀ =>
    analyticAt_affine_spinProj hh₀ _ _ x y i j
  refine hg.congr isOpen_sum_sq_ne_zero fun h hh => ?_
  rw [(finalHessianC_sqrt_eq (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hh).2.1, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, liftOp_mul_one_sub_projHC_apply]
  rfl

/-- **Joint holomorphy of the inverse in `(z, h)` (T5).**  For `E z` with `WSmall r η (E z)`,
`η < g_*`, `E` analytic on the open set `Ω`, and `h·h ≠ 0`: every entry of
`(a P_h + ((U + E z) ⊗ 1)(1 - P_h))⁻¹` is analytic in `(z, h)` on `Ω × {h·h ≠ 0}`. -/
theorem finalPert_hessC_inv_analytic (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {E : ℂ → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    (hana : ∀ z ∈ Ω, ∀ i j, AnalyticAt ℂ (fun w => E w i j) z)
    (hE : ∀ z ∈ Ω, WSmall r η (E z)) (x y : L1Torus d N₀) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun w : ℂ × (Fin N → ℂ) =>
        (hessC N (a : ℂ) (finalOp d L N₀ k v a + E w.1) w.2)⁻¹ (x, i) (y, j))
      (Ω ×ˢ {h | ∑ k, h k ^ 2 ≠ 0}) := by
  have ha0 : 0 < a := by linarith
  have hg : AnalyticOnNhd ℂ (fun w : ℂ × (Fin N → ℂ) => (a : ℂ)⁻¹ *
      (if x = y then spinProj w.2 i j else 0) +
      (finalOp d L N₀ k v a + E w.1)⁻¹ x y * ((if i = j then 1 else 0) - spinProj w.2 i j))
      (Ω ×ˢ {h | ∑ k, h k ^ 2 ≠ 0}) := by
    rintro ⟨z, h₀⟩ ⟨hz, hh₀⟩
    have hq : AnalyticAt ℂ (fun w : ℂ × (Fin N → ℂ) => spinProj w.2 i j) (z, h₀) :=
      (spinProj_analyticAt hh₀ i j).comp analyticAt_snd
    have hW : AnalyticAt ℂ (fun w : ℂ × (Fin N → ℂ) => (finalOp d L N₀ k v a + E w.1)⁻¹ x y)
        (z, h₀) :=
      (finalPert_analytic_inverse (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr hη0 hηg hana hE x y z hz).comp
        (analyticAt_fst (p := (z, h₀)))
    refine (analyticAt_const.mul ?_).add (hW.mul (analyticAt_const.sub hq))
    by_cases hxy : x = y
    · simpa [hxy] using hq
    · simpa [hxy] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × (Fin N → ℂ) => (0 : ℂ)) (z, h₀))
  refine hg.congr (hΩ.prod isOpen_sum_sq_ne_zero) ?_
  rintro ⟨z, h⟩ ⟨hz, hh⟩
  have hU := (finalPert_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr hη0 hηg (hE z hz)
    (le_refl (0 : ℝ))).1
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hU
  exact (hessC_inv_apply (Complex.ofReal_ne_zero.2 ha0.ne') hU hh x y i j).symm

/-- **Joint holomorphy of the square root in `(z, h)` (T5).**  With the same hypotheses
(for `z ∈ ℂ` and `Ω` open), every entry of `sqrtMat (a P_h + ((U + E z) ⊗ 1)(1 - P_h))` is
analytic in `(z, h)` on `Ω × {h·h ≠ 0}`; this uses the landed one-variable
`finalPert_analytic_sqrt` (analytic in `z`) and the exact formula (T4), which is affine in `P_h`. -/
theorem finalPert_hessC_sqrt_analytic (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) [NeZero N]
    {r η : ℝ} (hr : 0 < r) (hη0 : 0 ≤ η) (hηg : η < finalGap d L)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {E : ℂ → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    (hana : ∀ z ∈ Ω, ∀ i j, AnalyticAt ℂ (fun w => E w i j) z)
    (hE : ∀ z ∈ Ω, WSmall r η (E z)) (x y : L1Torus d N₀) (i j : Fin N) :
    AnalyticOnNhd ℂ (fun w : ℂ × (Fin N → ℂ) =>
        Localization.sqrtMat (hessC N (a : ℂ) (finalOp d L N₀ k v a + E w.1) w.2) (x, i) (y, j))
      (Ω ×ˢ {h | ∑ k, h k ^ 2 ≠ 0}) := by
  have ha0 : 0 < a := by linarith
  have hg : AnalyticOnNhd ℂ (fun w : ℂ × (Fin N → ℂ) => ((1 / Real.sqrt a : ℝ) : ℂ) *
      (if x = y then spinProj w.2 i j else 0) +
      Localization.sqrtMat (finalOp d L N₀ k v a + E w.1) x y *
        ((if i = j then 1 else 0) - spinProj w.2 i j))
      (Ω ×ˢ {h | ∑ k, h k ^ 2 ≠ 0}) := by
    rintro ⟨z, h₀⟩ ⟨hz, hh₀⟩
    have hq : AnalyticAt ℂ (fun w : ℂ × (Fin N → ℂ) => spinProj w.2 i j) (z, h₀) :=
      (spinProj_analyticAt hh₀ i j).comp analyticAt_snd
    have hW0 : AnalyticAt ℂ
        (fun z' : ℂ => Localization.sqrtMat (finalOp d L N₀ k v a + E z') x y) z :=
      finalPert_analytic_sqrt (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr hη0 hηg
        hΩ hana hE x y z hz
    have hW : AnalyticAt ℂ (fun w : ℂ × (Fin N → ℂ) =>
        Localization.sqrtMat (finalOp d L N₀ k v a + E w.1) x y) (z, h₀) := by
      have h2 := hW0.comp (analyticAt_fst (𝕜 := ℂ) (p := (z, h₀)))
      exact h2
    refine (analyticAt_const.mul ?_).add (hW.mul (analyticAt_const.sub hq))
    by_cases hxy : x = y
    · simpa [hxy] using hq
    · simpa [hxy] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × (Fin N → ℂ) => (0 : ℂ)) (z, h₀))
  refine hg.congr (hΩ.prod isOpen_sum_sq_ne_zero) ?_
  rintro ⟨z, h⟩ ⟨hz, hh⟩
  dsimp only at hz hh ⊢
  rw [(sqrtMat_hessC ha0 (finalPert_resOK (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr hη0 hηg (hE z hz))
    hh).2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, liftOp_mul_one_sub_projHC_apply]
  rfl

end AnalyticFinal

end Balaban.Green
