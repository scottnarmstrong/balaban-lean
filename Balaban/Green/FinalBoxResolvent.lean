/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalCutFamily
public import Balaban.Localization.DecoupledGs

/-!
# Local box resolvents and the exact parametrix identity (FINALFAM leaves 2 and 3, algebra)

This file belongs to the "path-tagged macroblock parametrix" of `notes/phase1/FINALFAM.md`, §4.
**The family below is a construction proposed in that note.  The papers print no formula for it**
(question 18 to the author is pending).  The tagged family `G_fin(s, t)` is not claimed to be the
inverse of any cut operator for `s ≠ 1`, and **no smallness of the defect `K` is proved here**.

For a matrix `U`, a region `B` of sites and `t ≥ 0` put `A = U + t` and let `P_B` be the diagonal
projection onto `B`.

* `boxH U B t = P_B A P_B + (1 - P_B)` and `boxG U B t = (boxH U B t)⁻¹ P_B`;
* for `U = finalOp`, in the mass window of `finalMass_resolvent_decay`, `boxH` is invertible,
  its `B`-block has gap `finalGap d L + t`, its complement block is the identity, and
  `‖boxG x y‖ ≤ 2/(finalGap d L + t) exp(-finalRate d L · dist x y)` for all `x, y`
  (the matrix `boxG` vanishes off `B × B`).  The `B × B` block of `boxH⁻¹` is the `B × B` block
  of the inverse of the two-cell operator `finalOpCut (cutWeight (twoCellLam 0) (twoCellLabel B)) + t`,
  whose complement block is the complement compression of `U + t`, not the identity; the
  transfer is the direct computation `boxH⁻¹ = P_B M⁻¹ P_B + (1 - P_B)` for block-diagonal `M`.
* exact parametrix identity: for diagonal `χ_z` with `∑ χ_z = 1` and `χ_z P_{B_z} = χ_z`
  (support in `B_z`), with `R_z = χ_z - A χ_z G_z`:
  `A (∑ χ_z G_z) = 1 - ∑ R_z`, `R_z = -[U, χ_z] G_z` (this needs only `χ_z P_{B_z} = χ_z`;
  the interior condition of the note only matters for smallness), and
  `(∑ χ_z G_z)(1 - ∑ R_z)⁻¹ = A⁻¹` whenever `1 - ∑ R_z` is invertible;
* the tagged family with monomial tags, its value at `s = 1`, polynomial dependence on the
  parameters, and the abstract Neumann statement.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal projection onto the region `B`. -/
noncomputable def boxP (B : Finset ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i ∈ B then 1 else 0

/-- `U + t`. -/
noncomputable def shiftMat (U : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  U + (t : ℂ) • (1 : Matrix ι ι ℂ)

/-- The local box operator `P_B (U + t) P_B + (1 - P_B)`. -/
noncomputable def boxH (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) : Matrix ι ι ℂ :=
  boxP B * shiftMat U t * boxP B + (1 - boxP B)

/-- The local box resolvent `(boxH U B t)⁻¹ P_B`. -/
noncomputable def boxG (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) : Matrix ι ι ℂ :=
  (boxH U B t)⁻¹ * boxP B

theorem boxP_mul_self (B : Finset ι) : boxP B * boxP B = boxP B := by
  ext i j
  simp only [boxP, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp_all

theorem boxP_one_sub_mul (B : Finset ι) : (1 - boxP B) * boxP B = 0 := by
  rw [sub_mul, one_mul, boxP_mul_self, sub_self]

theorem boxP_mul_one_sub (B : Finset ι) : boxP B * (1 - boxP B) = 0 := by
  rw [mul_sub, mul_one, boxP_mul_self, sub_self]

theorem boxP_one_sub_mul_self (B : Finset ι) : (1 - boxP B) * (1 - boxP B) = 1 - boxP B := by
  rw [mul_sub, mul_one, boxP_one_sub_mul, sub_zero]

theorem boxP_mul_boxH (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    boxP B * boxH U B t = boxH U B t * boxP B := by
  have h1 := boxP_mul_self B
  have h2 := boxP_mul_one_sub B
  have h3 := boxP_one_sub_mul B
  unfold boxH
  rw [mul_add, add_mul, h2, h3]
  simp only [← mul_assoc, h1]
  rw [mul_assoc (boxP B * shiftMat U t) (boxP B) (boxP B), h1]

/-- The inverse of `boxH` from the inverse of a block-diagonal `M` with the same `B`-block. -/
theorem boxH_mul_inv_of {U M : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} (hM : IsUnit M)
    (hMP : M * boxP B = boxP B * M) (hMA : boxP B * M * boxP B = boxP B * shiftMat U t * boxP B) :
    boxH U B t * (boxP B * M⁻¹ * boxP B + (1 - boxP B)) = 1 ∧
    (boxP B * M⁻¹ * boxP B + (1 - boxP B)) * boxH U B t = 1 := by
  have h1 := boxP_mul_self B
  have h2 := boxP_mul_one_sub B
  have h3 := boxP_one_sub_mul B
  have h4 := boxP_one_sub_mul_self B
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hM
  have hMN : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hNM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hdet
  have hsum : boxP B + (1 - boxP B) = 1 := by abel
  unfold boxH
  rw [← hMA]
  generalize boxP B = P at *
  generalize 1 - P = Q at *
  have hNP : M⁻¹ * P = P * M⁻¹ := by
    calc M⁻¹ * P = M⁻¹ * P * (M * M⁻¹) := by rw [hMN, mul_one]
      _ = M⁻¹ * (P * M) * M⁻¹ := by simp only [mul_assoc]
      _ = M⁻¹ * (M * P) * M⁻¹ := by rw [hMP]
      _ = (M⁻¹ * M) * (P * M⁻¹) := by simp only [mul_assoc]
      _ = P * M⁻¹ := by rw [hNM, one_mul]
  have hPMP : P * M * P = M * P := by rw [← hMP, mul_assoc, h1]
  have hPNP : P * M⁻¹ * P = M⁻¹ * P := by rw [← hNP, mul_assoc, h1]
  rw [hPMP, hPNP]
  have e1 : M * P * (M⁻¹ * P) = P := by
    calc M * P * (M⁻¹ * P) = M * (P * M⁻¹) * P := by simp only [mul_assoc]
      _ = M * (M⁻¹ * P) * P := by rw [hNP]
      _ = (M * M⁻¹) * (P * P) := by simp only [mul_assoc]
      _ = P := by rw [hMN, h1, one_mul]
  have e2 : Q * (M⁻¹ * P) = 0 := by
    rw [hNP, ← mul_assoc, h3, zero_mul]
  have e3 : M * P * Q = 0 := by rw [mul_assoc, h2, mul_zero]
  have e4 : M⁻¹ * P * (M * P) = P := by
    calc M⁻¹ * P * (M * P) = M⁻¹ * (P * M) * P := by simp only [mul_assoc]
      _ = M⁻¹ * (M * P) * P := by rw [hMP]
      _ = (M⁻¹ * M) * (P * P) := by simp only [mul_assoc]
      _ = P := by rw [hNM, h1, one_mul]
  have e5 : M⁻¹ * P * Q = 0 := by rw [mul_assoc, h2, mul_zero]
  have e6 : Q * (M * P) = 0 := by
    rw [hMP, ← mul_assoc, h3, zero_mul]
  constructor
  · rw [mul_add, add_mul, add_mul, e1, e2, e3, h4]
    rw [add_zero, zero_add, ← hsum]
  · rw [mul_add, add_mul, add_mul, e4, e5, e6, h4]
    rw [add_zero, zero_add, ← hsum]

omit [Fintype ι] in
theorem boxP_apply (B : Finset ι) (x y : ι) :
    boxP B x y = if x = y then (if x ∈ B then 1 else 0) else 0 := by
  simp [boxP, Matrix.diagonal_apply]

/-- `H⁻¹` commutes with `P_B`. -/
theorem boxP_mul_inv_boxH {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ}
    (hH : IsUnit (boxH U B t)) : (boxH U B t)⁻¹ * boxP B = boxP B * (boxH U B t)⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hH
  have hMN : boxH U B t * (boxH U B t)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hNM : (boxH U B t)⁻¹ * boxH U B t = 1 := Matrix.nonsing_inv_mul _ hdet
  have hMP := (boxP_mul_boxH U B t).symm
  calc (boxH U B t)⁻¹ * boxP B
      = (boxH U B t)⁻¹ * boxP B * (boxH U B t * (boxH U B t)⁻¹) := by rw [hMN, mul_one]
    _ = (boxH U B t)⁻¹ * (boxP B * boxH U B t) * (boxH U B t)⁻¹ := by simp only [mul_assoc]
    _ = (boxH U B t)⁻¹ * (boxH U B t * boxP B) * (boxH U B t)⁻¹ := by rw [← hMP]
    _ = ((boxH U B t)⁻¹ * boxH U B t) * (boxP B * (boxH U B t)⁻¹) := by simp only [mul_assoc]
    _ = _ := by rw [hNM, one_mul]

theorem boxH_mul_boxG {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} (hH : IsUnit (boxH U B t)) :
    boxH U B t * boxG U B t = boxP B := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hH
  unfold boxG
  rw [← mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul]

/-- `boxG` lives on `B × B`: `P_B G = G`. -/
theorem boxP_mul_boxG {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} (hH : IsUnit (boxH U B t)) :
    boxP B * boxG U B t = boxG U B t := by
  unfold boxG
  rw [← mul_assoc, ← boxP_mul_inv_boxH hH, mul_assoc, boxP_mul_self]

theorem boxG_mul_boxP {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} :
    boxG U B t * boxP B = boxG U B t := by
  unfold boxG
  rw [mul_assoc, boxP_mul_self]

/-- `P_B (U + t) G = P_B`. -/
theorem boxP_mul_shift_mul_boxG {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ}
    (hH : IsUnit (boxH U B t)) :
    boxP B * shiftMat U t * boxG U B t = boxP B := by
  have h1 := boxH_mul_boxG hH
  have h2 := boxP_mul_boxG hH
  have h3 : (1 - boxP B) * boxG U B t = 0 := by rw [sub_mul, one_mul, h2, sub_self]
  unfold boxH at h1
  rw [add_mul, h3, add_zero, mul_assoc (boxP B * shiftMat U t) (boxP B) (boxG U B t), h2] at h1
  exact h1

/-- A diagonal `χ` supported in `B` satisfies `χ P_B = χ`. -/
theorem diagonal_mul_boxP {B : Finset ι} {c : ι → ℂ} (hc : ∀ x, c x ≠ 0 → x ∈ B) :
    Matrix.diagonal c * boxP B = Matrix.diagonal c := by
  ext x y
  simp only [boxP, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases h : c x = 0
    · simp [h]
    · simp [hc x h]
  · simp [hxy]

/-- The remainder `R = χ - (U + t) χ G` for a diagonal `χ = diag c`. -/
noncomputable def boxR (U : Matrix ι ι ℂ) (B : Finset ι) (c : ι → ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal c - shiftMat U t * Matrix.diagonal c * boxG U B t

/-- **The exact commutator identity** `R = -[U, χ] G`.  It needs only the invertibility of
`boxH` and `χ P_B = χ` (the support of `χ` lies in `B`). -/
theorem boxR_eq_neg_commutator {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} {c : ι → ℂ}
    (hH : IsUnit (boxH U B t)) (hc : ∀ x, c x ≠ 0 → x ∈ B) :
    boxR U B c t = -((U * Matrix.diagonal c - Matrix.diagonal c * U) * boxG U B t) := by
  have e1 : Matrix.diagonal c = Matrix.diagonal c * shiftMat U t * boxG U B t := by
    calc Matrix.diagonal c = Matrix.diagonal c * boxP B := (diagonal_mul_boxP hc).symm
      _ = Matrix.diagonal c * (boxP B * shiftMat U t * boxG U B t) := by
          rw [boxP_mul_shift_mul_boxG hH]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, diagonal_mul_boxP hc]
  have e2 : shiftMat U t * Matrix.diagonal c - Matrix.diagonal c * shiftMat U t =
      U * Matrix.diagonal c - Matrix.diagonal c * U := by
    simp [shiftMat, add_mul, mul_add]
  unfold boxR
  rw [← e2]
  calc Matrix.diagonal c - shiftMat U t * Matrix.diagonal c * boxG U B t
      = Matrix.diagonal c * shiftMat U t * boxG U B t -
          shiftMat U t * Matrix.diagonal c * boxG U B t := by rw [← e1]
    _ = (Matrix.diagonal c * shiftMat U t - shiftMat U t * Matrix.diagonal c) * boxG U B t :=
        (sub_mul _ _ _).symm
    _ = _ := by rw [← neg_mul, neg_sub]

/-- The columns of `R` lie in `B`. -/
theorem boxR_mul_boxP {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} {c : ι → ℂ}
    (hc : ∀ x, c x ≠ 0 → x ∈ B) : boxR U B c t * boxP B = boxR U B c t := by
  unfold boxR
  rw [sub_mul, mul_assoc, boxG_mul_boxP, diagonal_mul_boxP hc]

/-- **Exact parametrix identity** (i): for diagonal `χ_z` with `∑ χ_z = 1`,
`(U + t) ∑ χ_z G_z = 1 - ∑ R_z`.  No support or invertibility is needed. -/
theorem parametrix_identity {Z : Type*} (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (hsum : ∀ x, ∑ z ∈ S, c z x = 1) (U : Matrix ι ι ℂ) (t : ℝ) :
    shiftMat U t * ∑ z ∈ S, Matrix.diagonal (c z) * boxG U (B z) t =
      1 - ∑ z ∈ S, boxR U (B z) (c z) t := by
  have h1 : ∑ z ∈ S, Matrix.diagonal (c z) = (1 : Matrix ι ι ℂ) := by
    rw [← Matrix.diagonal_one]
    ext x y
    simp only [Matrix.sum_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; simpa using hsum x
    · simp [h]
  rw [Finset.mul_sum]
  have : ∀ z ∈ S, shiftMat U t * (Matrix.diagonal (c z) * boxG U (B z) t) =
      Matrix.diagonal (c z) - boxR U (B z) (c z) t := by
    intro z _
    unfold boxR
    rw [← mul_assoc]; abel
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, h1]

/-- **Parametrix inverse** (iii): if `1 - ∑ R_z` is invertible then
`(∑ χ_z G_z)(1 - ∑ R_z)⁻¹ = (U + t)⁻¹`. -/
theorem parametrix_inv {Z : Type*} (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (hsum : ∀ x, ∑ z ∈ S, c z x = 1) (U : Matrix ι ι ℂ) (t : ℝ)
    (hW : IsUnit (1 - ∑ z ∈ S, boxR U (B z) (c z) t)) :
    (∑ z ∈ S, Matrix.diagonal (c z) * boxG U (B z) t) *
        (1 - ∑ z ∈ S, boxR U (B z) (c z) t)⁻¹ = (shiftMat U t)⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hW
  have hmul : shiftMat U t * ((∑ z ∈ S, Matrix.diagonal (c z) * boxG U (B z) t) *
      (1 - ∑ z ∈ S, boxR U (B z) (c z) t)⁻¹) = 1 := by
    rw [← mul_assoc, parametrix_identity S B c hsum U t, Matrix.mul_nonsing_inv _ hdet]
  exact (Matrix.inv_eq_right_inv hmul).symm

/-- Block-diagonal `M` with the `B`-block of `A`: the facts used for `boxH`. -/
theorem blockDiag_facts {M A : Matrix ι ι ℂ} {B : Finset ι}
    (hM : ∀ x y, M x y = if (x ∈ B ↔ y ∈ B) then A x y else 0) :
    M * boxP B = boxP B * M ∧ boxP B * M * boxP B = boxP B * A * boxP B := by
  constructor
  · ext x y
    simp only [boxP, Matrix.mul_diagonal, Matrix.diagonal_mul, hM]
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx, hy]
  · ext x y
    simp only [boxP, Matrix.mul_diagonal, Matrix.diagonal_mul, hM]
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx, hy]

end Algebra

section Analytic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_matrix_det {F : E → Matrix ι ι ℂ} {s0 : E}
    (h : ∀ x y, AnalyticAt ℂ (fun s => F s x y) s0) : AnalyticAt ℂ (fun s => (F s).det) s0 := by
  simp only [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => h _ _

theorem analyticAt_matrix_inv_entry {F : E → Matrix ι ι ℂ} {s0 : E}
    (h : ∀ x y, AnalyticAt ℂ (fun s => F s x y) s0) (hu : IsUnit (F s0)) (x y : ι) :
    AnalyticAt ℂ (fun s => (F s)⁻¹ x y) s0 := by
  have hdet := analyticAt_matrix_det h
  have hne : (F s0).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  have hadj : AnalyticAt ℂ (fun s => (F s).adjugate x y) s0 := by
    simp only [Matrix.adjugate_apply]
    refine analyticAt_matrix_det (F := fun s => (F s).updateRow y (Pi.single x 1)) fun a b => ?_
    by_cases ha : a = y
    · subst ha; simp only [Matrix.updateRow_self]; exact analyticAt_const
    · simp only [Matrix.updateRow_ne ha]; exact h a b
  have : (fun s => (F s)⁻¹ x y) = fun s => ((F s).det)⁻¹ * (F s).adjugate x y := by
    funext s
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  rw [this]
  exact (hdet.inv hne).mul hadj

omit [DecidableEq ι] in
theorem analyticAt_matrix_mul {F G : E → Matrix ι ι ℂ} {s0 : E}
    (hF : ∀ x y, AnalyticAt ℂ (fun s => F s x y) s0)
    (hG : ∀ x y, AnalyticAt ℂ (fun s => G s x y) s0) (x y : ι) :
    AnalyticAt ℂ (fun s => (F s * G s) x y) s0 := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun w _ => (hF x w).mul (hG w y)

end Analytic

section Neumann

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Abstract Neumann statement.** If the weighted row sums
`∑_y ω(x) ‖K x y‖ / ω(y)` are at most `q < 1`, then `1 - K` is invertible. -/
theorem isUnit_one_sub_of_weighted_row_sum {ω : ι → ℝ} (hω : ∀ x, 0 < ω x)
    {K : Matrix ι ι ℂ} {q : ℝ} (hq : q < 1)
    (hK : ∀ x, ∑ y, ω x * ‖K x y‖ / ω y ≤ q) : IsUnit (1 - K) := by
  refine Matrix.mulVec_injective_iff_isUnit.1 ?_
  intro g g' hgg
  have hlin : (1 - K) *ᵥ (g - g') = 0 := by
    rw [Matrix.mulVec_sub, hgg, sub_self]
  have hh : ∀ x, (g - g') x = ∑ y, K x y * (g - g') y := by
    intro x
    have := congrFun hlin x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct] at this ⊢
    exact sub_eq_zero.1 this
  set h := g - g' with hhdef
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact funext fun x => hι.elim x
  obtain ⟨x0, -, hx0⟩ := Finset.exists_max_image Finset.univ (fun y => ω y * ‖h y‖)
    Finset.univ_nonempty
  set m : ℝ := ω x0 * ‖h x0‖ with hm
  have hm0 : 0 ≤ m := by have := hω x0; positivity
  have hle : m ≤ q * m := by
    calc m = ω x0 * ‖∑ y, K x0 y * h y‖ := by rw [hm, ← hh]
      _ ≤ ω x0 * ∑ y, ‖K x0 y‖ * ‖h y‖ := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun y _ => (norm_mul (K x0 y) (h y)).le)) (hω x0).le
      _ = ∑ y, (ω x0 * ‖K x0 y‖ / ω y) * (ω y * ‖h y‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          have := (hω y).ne'
          field_simp
      _ ≤ ∑ y, (ω x0 * ‖K x0 y‖ / ω y) * m := by
          refine Finset.sum_le_sum fun y _ => ?_
          have : 0 ≤ ω x0 * ‖K x0 y‖ / ω y := by
            have := hω x0; have := hω y; positivity
          exact mul_le_mul_of_nonneg_left (hx0 y (Finset.mem_univ y)) this
      _ = (∑ y, ω x0 * ‖K x0 y‖ / ω y) * m := by rw [Finset.sum_mul]
      _ ≤ q * m := mul_le_mul_of_nonneg_right (hK x0) hm0
  have hm00 : m = 0 := by nlinarith
  funext x
  have h1 : ω x * ‖h x‖ ≤ 0 := hm00 ▸ hx0 x (Finset.mem_univ x)
  have h2 : ‖h x‖ ≤ 0 := by
    by_contra hc
    have hc := not_le.1 hc
    have := hω x
    nlinarith
  have : h x = 0 := norm_le_zero_iff.1 h2
  exact sub_eq_zero.1 this

end Neumann

section Tagged

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Pc : Type*} [Fintype Pc]

/-- The monomial tag `∏_{p ∈ V} s_p` (value `1` at `s = 1`). -/
noncomputable def tagMon (V : Finset Pc) (s : Pc → ℂ) : ℂ := ∏ p ∈ V, s p

/-- The matrix with entries `∑_z τ_z(x, y; s) a_z(x, y)`, where `τ_z = tagMon (V z x y)`. -/
noncomputable def taggedMat (S : Finset Z) (V : Z → ι → ι → Finset Pc) (a : Z → Matrix ι ι ℂ)
    (s : Pc → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun x y => ∑ z ∈ S, tagMon (V z x y) s * a z x y

/-- The tagged `G_*(s, t)`: entries `∑_z τ_z (χ_z G_z)_{xy}`. -/
noncomputable def taggedG (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) (s : Pc → ℂ) : Matrix ι ι ℂ :=
  taggedMat S V (fun z => Matrix.diagonal (c z) * boxG U (B z) t) s

/-- The tagged `K(s, t)`: entries `∑_z τ_z (R_z)_{xy}`. -/
noncomputable def taggedK (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) (s : Pc → ℂ) : Matrix ι ι ℂ :=
  taggedMat S V (fun z => boxR U (B z) (c z) t) s

/-- `G_fin(s, t) = G_*(s, t) (1 - K(s, t))⁻¹` (a construction proposed in FINALFAM). -/
noncomputable def taggedGfin (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) (s : Pc → ℂ) : Matrix ι ι ℂ :=
  taggedG S B c V U t s * (1 - taggedK S B c V U t s)⁻¹

omit [Fintype Pc] in
theorem tagMon_one (V : Finset Pc) : tagMon V (fun _ => 1) = 1 := by
  simp [tagMon]

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
theorem taggedMat_one (S : Finset Z) (V : Z → ι → ι → Finset Pc) (a : Z → Matrix ι ι ℂ) :
    taggedMat S V a (fun _ => 1) = ∑ z ∈ S, a z := by
  ext x y
  simp [taggedMat, tagMon_one, Matrix.sum_apply]

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
/-- Each entry of the tagged matrix is a polynomial in the parameters. -/
theorem taggedMat_poly (S : Finset Z) (V : Z → ι → ι → Finset Pc) (a : Z → Matrix ι ι ℂ)
    (x y : ι) : ∃ p : MvPolynomial Pc ℂ, ∀ s : Pc → ℂ,
      taggedMat S V a s x y = MvPolynomial.eval s p := by
  refine ⟨∑ z ∈ S, MvPolynomial.C (a z x y) * ∏ q ∈ V z x y, MvPolynomial.X q, fun s => ?_⟩
  simp [taggedMat, tagMon, map_sum, map_prod, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
/-- Each entry of the tagged matrix is an analytic function of the parameters. -/
theorem taggedMat_analytic (S : Finset Z) (V : Z → ι → ι → Finset Pc) (a : Z → Matrix ι ι ℂ)
    (x y : ι) (s0 : Pc → ℂ) : AnalyticAt ℂ (fun s => taggedMat S V a s x y) s0 := by
  simp only [taggedMat, Matrix.of_apply]
  refine Finset.analyticAt_fun_sum _ fun z _ => ?_
  refine AnalyticAt.mul ?_ analyticAt_const
  unfold tagMon
  exact Finset.analyticAt_fun_prod _ fun q _ =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Pc => ℂ) q).analyticAt s0

omit [Fintype Pc] in
theorem taggedG_one (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) :
    taggedG S B c V U t (fun _ => 1) = ∑ z ∈ S, Matrix.diagonal (c z) * boxG U (B z) t :=
  taggedMat_one _ _ _

omit [Fintype Pc] in
theorem taggedK_one (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) :
    taggedK S B c V U t (fun _ => 1) = ∑ z ∈ S, boxR U (B z) (c z) t :=
  taggedMat_one _ _ _

/-- **T3.** If the weighted row sums of `K(s, t)` are at most `q < 1` on a set `D` of parameters,
then on `D`: `1 - K(s, t)` is invertible and the entries of `G_fin(s, t)` are analytic; if
`s = 1 ∈ D`, `G_fin(1, t) = (U + t)⁻¹`.  The hypothesis on `K` is the (unproved here) smallness. -/
theorem taggedGfin_of_weighted_row_sum (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (hsum : ∀ x, ∑ z ∈ S, c z x = 1) (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ)
    {ω : ι → ℝ} (hω : ∀ x, 0 < ω x) {q : ℝ} (hq : q < 1) (D : Set (Pc → ℂ))
    (hD : ∀ s ∈ D, ∀ x, ∑ y, ω x * ‖taggedK S B c V U t s x y‖ / ω y ≤ q) :
    (∀ s ∈ D, IsUnit (1 - taggedK S B c V U t s)) ∧
    (∀ x y, AnalyticOnNhd ℂ (fun s => taggedGfin S B c V U t s x y) D) ∧
    ((fun _ => (1 : ℂ)) ∈ D → taggedGfin S B c V U t (fun _ => 1) = (shiftMat U t)⁻¹) := by
  have hu : ∀ s ∈ D, IsUnit (1 - taggedK S B c V U t s) := fun s hs =>
    isUnit_one_sub_of_weighted_row_sum hω hq (hD s hs)
  refine ⟨hu, fun x y s hs => ?_, fun h1 => ?_⟩
  · have hK : ∀ a b, AnalyticAt ℂ (fun s => (1 - taggedK S B c V U t s) a b) s := by
      intro a b
      simp only [Matrix.sub_apply]
      exact analyticAt_const.sub (taggedMat_analytic _ _ _ _ _ _)
    have hI := analyticAt_matrix_inv_entry hK (hu s hs)
    unfold taggedGfin
    exact analyticAt_matrix_mul (fun a b => taggedMat_analytic _ _ _ _ _ _) hI x y
  · unfold taggedGfin
    rw [taggedG_one, taggedK_one]
    exact parametrix_inv S B c hsum U t (by simpa [taggedK_one] using hu _ h1)

end Tagged

section GenericBox

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Cutting a coercive matrix along a region `B` (zeroing the entries between `B` and its
complement) keeps the coercivity constant. -/
theorem isCoercive_blockCut {U : Matrix ι ι ℂ} {g : ℝ} (hU : IsCoercive U g) (B : Finset ι) :
    IsCoercive (Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then U x y else 0) g := by
  intro u
  set u₁ : ι → ℂ := fun i => if i ∈ B then u i else 0 with hu₁
  set u₂ : ι → ℂ := fun i => if i ∈ B then 0 else u i with hu₂
  have hmv : ∀ i, ((Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then U x y else 0) *ᵥ u) i =
      (if i ∈ B then (U *ᵥ u₁) i else (U *ᵥ u₂) i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    by_cases hi : i ∈ B
    · simp only [hi, ite_true]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ B <;> simp [hj, hu₁]
    · simp only [hi, ite_false]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ B <;> simp [hj, hu₂]
  have hq : reQuad (Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then U x y else 0) u =
      reQuad U u₁ + reQuad U u₂ := by
    unfold reQuad
    rw [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmv i]
    by_cases hi : i ∈ B <;> simp [hi, hu₁, hu₂]
  have hs : sqNorm u = sqNorm u₁ + sqNorm u₂ := by
    unfold sqNorm
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ B <;> simp [hi, hu₁, hu₂]
  rw [hq, hs, mul_add]
  exact add_le_add (hU u₁) (hU u₂)

variable {d N₀ : ℕ} [NeZero N₀]

omit [Fintype ι] in
/-- The cut of `U + t` along `B` is the cut of `U`, plus `t`. -/
theorem blockCut_shift_eq (U : Matrix ι ι ℂ) (t : ℝ) (B : Finset ι) :
    (Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then U x y else 0) + (t : ℂ) • (1 : Matrix ι ι ℂ) =
      Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then shiftMat U t x y else 0 := by
  ext x y
  simp only [shiftMat, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases h : (x ∈ B ↔ y ∈ B) <;> simp [h, Matrix.one_apply_ne hxy]

/-- Combes--Thomas for the cut of a decaying coercive `U` on the torus: the cut of `U + t` is
invertible with the decaying inverse bound of `combesThomas`. -/
theorem blockCut_resolvent_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {g A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) {t : ℝ} (ht : 0 ≤ t)
    (B : Finset (L1Torus d N₀)) :
    IsUnit (Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then shiftMat U t x y else 0) ∧
      ∀ x y, ‖(Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then shiftMat U t x y else 0)⁻¹ x y‖ ≤
        2 / (g + t) * Real.exp (-ctRate A δ g (ballConst d (δ / 4)) * dist x y) := by
  have hK : ∀ x : L1Torus d N₀, ∑ y, Real.exp (-(δ / 4) * dist x y) ≤ ballConst d (δ / 4) :=
    fun x => ballSum_L1Torus (d := d) (m := N₀) (by positivity) x
  have hκ : 0 ≤ ballConst d (δ / 4) := ballConst_decay_nonneg (by positivity)
  have hdec : ∀ x y, ‖(Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then U x y else 0) x y‖ ≤
      A * Real.exp (-δ * dist x y) := by
    intro x y
    simp only [Matrix.of_apply]
    split_ifs
    · exact hUdec x y
    · simp only [norm_zero]; positivity
  have h := combesThomas (c₀ := A) (δ₀ := δ) (γ₀ := g) (κ := ballConst d (δ / 4)) hA hδ hg hκ hdec
    hK (isCoercive_blockCut hU B) ht
  rw [blockCut_shift_eq] at h
  refine ⟨h.1, fun x y => ?_⟩
  exact (h.2 x y).trans_eq (by simp only [div_eq_mul_inv])

/-- Invertibility of the box operator and its inverse, for a decaying coercive `U`. -/
theorem boxH_inv_eq_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {g A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) {t : ℝ} (ht : 0 ≤ t)
    (B : Finset (L1Torus d N₀)) :
    IsUnit (boxH U B t) ∧ boxG U B t =
      boxP B * (Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then shiftMat U t x y else 0)⁻¹ *
        boxP B := by
  have hM := (blockCut_resolvent_of_coercive U hA hδ hg hU hUdec ht B).1
  obtain ⟨hMP, hMA⟩ := blockDiag_facts (B := B) (M := Matrix.of fun x y =>
    if (x ∈ B ↔ y ∈ B) then shiftMat U t x y else 0) (A := shiftMat U t) (fun x y => by
      simp only [Matrix.of_apply])
  obtain ⟨hr, hl⟩ := boxH_mul_inv_of (U := U) (t := t) hM hMP hMA
  have hu : IsUnit (boxH U B t) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hr)
  refine ⟨hu, ?_⟩
  have h := Matrix.inv_eq_right_inv hr
  unfold boxG
  rw [h, add_mul, boxP_one_sub_mul, add_zero,
    mul_assoc (boxP B * (Matrix.of fun x y => if (x ∈ B ↔ y ∈ B) then shiftMat U t x y else 0)⁻¹)
      (boxP B) (boxP B), boxP_mul_self]

theorem boxH_isUnit_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {g A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) {t : ℝ} (ht : 0 ≤ t)
    (B : Finset (L1Torus d N₀)) : IsUnit (boxH U B t) :=
  (boxH_inv_eq_of_coercive U hA hδ hg hU hUdec ht B).1

/-- Entry bound of the box resolvent for a decaying coercive `U`. -/
theorem boxG_entry_bound_of_coercive (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {g A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) (hg : 0 < g) (hU : IsCoercive U g)
    (hUdec : ∀ x y, ‖U x y‖ ≤ A * Real.exp (-δ * dist x y)) {t : ℝ} (ht : 0 ≤ t)
    (B : Finset (L1Torus d N₀)) (x y : L1Torus d N₀) :
    ‖boxG U B t x y‖ ≤
      2 / (g + t) * Real.exp (-ctRate A δ g (ballConst d (δ / 4)) * dist x y) := by
  rw [(boxH_inv_eq_of_coercive U hA hδ hg hU hUdec ht B).2]
  simp only [boxP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
  · simpa [hx, hy] using (blockCut_resolvent_of_coercive U hA hδ hg hU hUdec ht B).2 x y
  all_goals
    simp only [hx, hy, ite_true, ite_false, mul_zero, zero_mul, norm_zero]
    positivity

end GenericBox

section Final

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The two-cell operator at `l = 0` plus `t`: `U + t` on `B × B` and on `B^c × B^c`, zero between. -/
noncomputable def twoCellShift (v a t : ℝ) (B : Finset (L1Torus d N₀)) :
    Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  finalOpCut (d := d) (L := L) (k := k)
      (cutWeight (twoCellLam 0) (twoCellLabel (X := (B : Set (L1Torus d N₀))))) v a +
    (t : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)

theorem twoCellShift_apply (v a t : ℝ) (B : Finset (L1Torus d N₀)) (x y : L1Torus d N₀) :
    twoCellShift (k := k) (L := L) v a t B x y =
      if (x ∈ B ↔ y ∈ B) then shiftMat (finalOp d L N₀ k v a) t x y else 0 := by
  unfold twoCellShift shiftMat
  simp only [finalOpCut, Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [cutWeight_twoCell]
  by_cases hxy : x = y
  · subst hxy; simp
  · by_cases h : (x ∈ B ↔ y ∈ B) <;> simp [h, Matrix.one_apply_ne hxy]

/-- The facts about `U = finalOp` used in this file, for `t ≥ 0` in the mass window. -/
theorem finalBox_twoCell_unit (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N₀)) :
    IsUnit (twoCellShift (k := k) (L := L) v a t B) ∧
      ∀ x y, ‖(twoCellShift (k := k) (L := L) v a t B)⁻¹ x y‖ ≤
        2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y) := by
  obtain ⟨h0, h1⟩ := twoCell_mem_convexClass (le_refl (0 : ℝ)) zero_le_one
  exact finalOpCut_resolvent_decay (c := twoCellLabel (X := (B : Set (L1Torus d N₀))))
    (lam := twoCellLam 0) hd hk hv0 hv1 ha1 ha2 hmass h0 h1 ht

/-- **T1, invertibility.** `boxH (finalOp) B t` is invertible, with inverse
`P_B M⁻¹ P_B + (1 - P_B)` where `M` is the two-cell operator plus `t`. -/
theorem boxH_inv_eq (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N₀)) :
    IsUnit (boxH (finalOp d L N₀ k v a) B t) ∧
      (boxH (finalOp d L N₀ k v a) B t)⁻¹ =
        boxP B * (twoCellShift (k := k) (L := L) v a t B)⁻¹ * boxP B + (1 - boxP B) := by
  have hM := (finalBox_twoCell_unit (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass ht B).1
  obtain ⟨hMP, hMA⟩ := blockDiag_facts (B := B) (twoCellShift_apply (k := k) (L := L) v a t B)
  obtain ⟨hr, hl⟩ := boxH_mul_inv_of (U := finalOp d L N₀ k v a) (t := t) hM hMP hMA
  have hu : IsUnit (boxH (finalOp d L N₀ k v a) B t) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hr)
  exact ⟨hu, (Matrix.inv_eq_right_inv hr)⟩

theorem boxH_isUnit_final (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N₀)) :
    IsUnit (boxH (finalOp d L N₀ k v a) B t) :=
  (boxH_inv_eq hd hk hv0 hv1 ha1 ha2 hmass ht B).1

/-- `boxG = P_B M⁻¹ P_B`: entries are those of `M⁻¹` on `B × B` and zero elsewhere. -/
theorem boxG_final_apply (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N₀)) (x y : L1Torus d N₀) :
    boxG (finalOp d L N₀ k v a) B t x y =
      if x ∈ B ∧ y ∈ B then (twoCellShift (k := k) (L := L) v a t B)⁻¹ x y else 0 := by
  have h := (boxH_inv_eq hd hk hv0 hv1 ha1 ha2 hmass ht B).2
  have hG : boxG (finalOp d L N₀ k v a) B t =
      boxP B * (twoCellShift (k := k) (L := L) v a t B)⁻¹ * boxP B := by
    unfold boxG
    rw [h, add_mul, boxP_one_sub_mul, add_zero,
      mul_assoc (boxP B * (twoCellShift (k := k) (L := L) v a t B)⁻¹) (boxP B) (boxP B),
      boxP_mul_self]
  rw [hG]
  simp only [boxP, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx, hy]

/-- **T1, entry bound.** For all `x, y`
`‖boxG x y‖ ≤ 2/(finalGap + t) exp(-finalRate · dist x y)`. -/
theorem boxG_final_entry_bound (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (B : Finset (L1Torus d N₀)) (x y : L1Torus d N₀) :
    ‖boxG (finalOp d L N₀ k v a) B t x y‖ ≤
      2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y) := by
  rw [boxG_final_apply hd hk hv0 hv1 ha1 ha2 hmass ht]
  split_ifs
  · exact (finalBox_twoCell_unit (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass ht B).2 x y
  · have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    have := finalGap_pos (d := d) hL
    simp only [norm_zero]
    positivity

/-- **T1, gap on the box.** For vectors supported in `B`, the quadratic form of `boxH` is bounded
below by `(finalGap d L + t) ‖u‖²`. -/
theorem boxH_final_coercive_on (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (B : Finset (L1Torus d N₀)) (u : L1Torus d N₀ → ℂ) (hu : ∀ i ∉ B, u i = 0) :
    (finalGap d L + t) * sqNorm u ≤ reQuad (boxH (finalOp d L N₀ k v a) B t) u := by
  obtain ⟨h0, h1⟩ := twoCell_mem_convexClass (le_refl (0 : ℝ)) zero_le_one
  have hc := (finalOpCut_isCoercive (k := k) (L := L)
    (c := twoCellLabel (X := (B : Set (L1Torus d N₀)))) hd hv0 hv1 ha1 hmass h0 h1).add_smul_one t u
  obtain ⟨hMP, hMA⟩ := blockDiag_facts (B := B) (twoCellShift_apply (k := k) (L := L) v a t B)
  have hPu : boxP B *ᵥ u = u := by
    funext i
    simp only [boxP, Matrix.mulVec_diagonal]
    by_cases hi : i ∈ B
    · simp [hi]
    · simp [hi, hu i hi]
  have hHP : boxH (finalOp d L N₀ k v a) B t * boxP B =
      twoCellShift (k := k) (L := L) v a t B * boxP B := by
    have e : twoCellShift (k := k) (L := L) v a t B * boxP B =
        boxP B * shiftMat (finalOp d L N₀ k v a) t * boxP B := by
      rw [← hMA, ← hMP, mul_assoc, boxP_mul_self]
    rw [e]
    unfold boxH
    rw [add_mul, boxP_one_sub_mul, add_zero, mul_assoc _ (boxP B) (boxP B), boxP_mul_self]
  have hv : boxH (finalOp d L N₀ k v a) B t *ᵥ u =
      twoCellShift (k := k) (L := L) v a t B *ᵥ u := by
    calc _ = boxH (finalOp d L N₀ k v a) B t *ᵥ (boxP B *ᵥ u) := by rw [hPu]
      _ = (boxH (finalOp d L N₀ k v a) B t * boxP B) *ᵥ u := by rw [Matrix.mulVec_mulVec]
      _ = (twoCellShift (k := k) (L := L) v a t B * boxP B) *ᵥ u := by rw [hHP]
      _ = _ := by rw [← Matrix.mulVec_mulVec, hPu]
  have : reQuad (boxH (finalOp d L N₀ k v a) B t) u =
      reQuad (twoCellShift (k := k) (L := L) v a t B) u := by
    unfold reQuad; rw [hv]
  rw [this]
  exact hc

/-- **T1, complement block.** For vectors vanishing on `B` the quadratic form of `boxH` is
`‖u‖²` (gap `1`, the identity). -/
theorem boxH_coercive_off (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ)
    (B : Finset (L1Torus d N₀)) (u : L1Torus d N₀ → ℂ) (hu : ∀ i ∈ B, u i = 0) :
    reQuad (boxH U B t) u = sqNorm u := by
  have hPu : boxP B *ᵥ u = 0 := by
    funext i
    simp only [boxP, Matrix.mulVec_diagonal]
    by_cases hi : i ∈ B
    · simp [hi, hu i hi]
    · simp [hi]
  have hv : boxH U B t *ᵥ u = u := by
    unfold boxH
    rw [Matrix.add_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hPu, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add, Matrix.sub_mulVec,
      Matrix.one_mulVec, hPu, sub_zero]
  have h1 := reQuad_smul_one (ι := L1Torus d N₀) 1 u
  unfold reQuad at h1 ⊢
  rw [hv]
  simpa using h1

end Final

end Balaban.Green
