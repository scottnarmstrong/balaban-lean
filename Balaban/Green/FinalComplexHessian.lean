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
      A x y * ((if i = j then 1 else 0) - h i * h j / ∑ k, h k ^ 2) := by
  rw [mul_sub, mul_one, Matrix.sub_apply]
  have e : (Multiscale.liftOp N A * projHC h : Matrix (ι × Fin N) (ι × Fin N) ℂ) (x, i) (y, j) =
      A x y * spinProj h i j :=
    congrFun (congrFun (liftOp_mul_idKron A (spinProj h)) (x, i)) (y, j)
  rw [e]
  simp only [Multiscale.liftOp, spinProj]
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

end Balaban.Green
