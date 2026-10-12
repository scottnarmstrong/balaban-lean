/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormDefs
public import Mathlib.Data.Matrix.Basis

/-!
# Rotations used in the renormalization analysis

* `planeRot`: the rotation by an angle in the coordinate plane `(i, k)` (for the Ward identity),
* `flipMat`: the reflection `x_j ↦ -x_j`,
* `rod`: the rotation of `a` into `q` of Rodrigues (`a·a = q·q = 1`, `1 + a·q ≠ 0`),
* `exists_normalizing_rot`: for `p ∈ ℂ^N` with `p·p = u²`, `‖p‖ ≤ 2`, `|u - 1| ≤ 1/4` there is a
  complex orthogonal `R` with entries bounded by `rotBound N` and `R p = u e_{i₀}`.
-/

@[expose] public section

open Matrix

namespace Balaban.SmallField

variable {N : ℕ}

/-- The matrix `Π = e_i e_iᵀ + e_k e_kᵀ`. -/
def planeProj (i k : Fin N) : Matrix (Fin N) (Fin N) ℂ := single i i 1 + single k k 1

/-- The generator `J = e_k e_iᵀ - e_i e_kᵀ` of rotations in the plane `(i, k)`. -/
def planeGen (i k : Fin N) : Matrix (Fin N) (Fin N) ℂ := single k i 1 - single i k 1

/-- The rotation `1 + (c - 1) Π + s J` in the plane `(i, k)` (a rotation if `c² + s² = 1`). -/
def planeRot (i k : Fin N) (c s : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  1 + (c - 1) • planeProj i k + s • planeGen i k

theorem planeProj_mul (i k : Fin N) (h : i ≠ k) : planeProj i k * planeProj i k = planeProj i k := by
  simp [planeProj, add_mul, mul_add, single_mul_single_same, single_mul_single_of_ne, h, h.symm]

theorem planeProj_mul_gen (i k : Fin N) (h : i ≠ k) :
    planeProj i k * planeGen i k = planeGen i k := by
  simp [planeProj, planeGen, add_mul, mul_sub, single_mul_single_same, single_mul_single_of_ne,
    h, h.symm]

theorem planeGen_mul_proj (i k : Fin N) (h : i ≠ k) :
    planeGen i k * planeProj i k = planeGen i k := by
  simp [planeProj, planeGen, sub_mul, mul_add, single_mul_single_same, single_mul_single_of_ne,
    h, h.symm]
  abel

theorem planeGen_mul_gen (i k : Fin N) (h : i ≠ k) :
    planeGen i k * planeGen i k = -planeProj i k := by
  simp [planeProj, planeGen, sub_mul, mul_sub, single_mul_single_same, single_mul_single_of_ne,
    h, h.symm]
  abel

theorem transpose_planeProj (i k : Fin N) : (planeProj i k).transpose = planeProj i k := by
  simp [planeProj, transpose_single]

theorem transpose_planeGen (i k : Fin N) : (planeGen i k).transpose = -planeGen i k := by
  simp [planeGen, transpose_single]

theorem planeRot_isOrth (i k : Fin N) (h : i ≠ k) (c s : ℂ) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrth (planeRot i k c s) := by
  unfold IsOrth planeRot
  simp only [transpose_add, transpose_smul, transpose_one, transpose_planeProj,
    transpose_planeGen]
  have hP := planeProj_mul i k h
  have hPG := planeProj_mul_gen i k h
  have hGP := planeGen_mul_proj i k h
  have hGG := planeGen_mul_gen i k h
  have e : (1 + (c - 1) • planeProj i k + s • -planeGen i k) *
      (1 + (c - 1) • planeProj i k + s • planeGen i k) =
      1 + ((c - 1) + (c - 1) + (c - 1) * (c - 1) + s * s) • planeProj i k := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_neg,
      neg_mul, hP, hPG, hGP, hGG]
    module
  rw [e]
  have : (c - 1) + (c - 1) + (c - 1) * (c - 1) + s * s = 0 := by linear_combination hcs
  rw [this, zero_smul, add_zero]

/-! ### The dot product -/

theorem dot_comm (v w : Spin N) : dot v w = dot w v := by
  simp [dot, mul_comm]

theorem dot_add_left (u v w : Spin N) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_sub_left (u v w : Spin N) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

theorem dot_smul_left (t : ℂ) (v w : Spin N) : dot (t • v) w = t * dot v w := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_add_right (u v w : Spin N) : dot u (v + w) = dot u v + dot u w := by
  rw [dot_comm, dot_add_left, dot_comm v u, dot_comm w u]

theorem dot_sub_right (u v w : Spin N) : dot u (v - w) = dot u v - dot u w := by
  rw [dot_comm, dot_sub_left, dot_comm v u, dot_comm w u]

theorem dot_smul_right (t : ℂ) (v w : Spin N) : dot v (t • w) = t * dot v w := by
  rw [dot_comm, dot_smul_left, dot_comm]

theorem dot_single_left (i : Fin N) (x : ℂ) (v : Spin N) : dot (Pi.single i x) v = x * v i := by
  simp [dot, Pi.single_apply, mul_comm]

theorem dot_single_right (i : Fin N) (x : ℂ) (v : Spin N) : dot v (Pi.single i x) = v i * x := by
  rw [dot_comm, dot_single_left, mul_comm]

/-! ### The reflection `x_j ↦ -x_j` -/

/-- The reflection `1 - 2 e_j e_jᵀ`. -/
def flipMat (j : Fin N) : Matrix (Fin N) (Fin N) ℂ := 1 - (2 : ℂ) • single j j 1

theorem flipMat_isOrth (j : Fin N) : IsOrth (flipMat j) := by
  unfold IsOrth flipMat
  have h : single j j (1 : ℂ) * single j j 1 = single j j 1 := by
    simp [single_mul_single_same]
  simp only [transpose_sub, transpose_one, transpose_smul, transpose_single]
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h]
  module

theorem entry_single_le (i j a b : Fin N) :
    ‖(single i j (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b‖ ≤ 1 := by
  rw [Matrix.single_apply]
  split_ifs <;> simp

theorem entryBd_flipMat (j : Fin N) : EntryBd N (flipMat j) := by
  intro a b
  have h1 : ‖(1 : Matrix (Fin N) (Fin N) ℂ) a b‖ ≤ 1 := by
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  have h3 := entry_single_le j j a b
  have h2 : ‖((2 : ℂ) • (single j j (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ)) a b‖ ≤ 2 := by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    nlinarith
  unfold flipMat rotBound
  rw [Matrix.sub_apply]
  have := norm_sub_le ((1 : Matrix (Fin N) (Fin N) ℂ) a b)
    (((2 : ℂ) • (single j j (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ)) a b)
  linarith

theorem entryBd_planeRot (i k : Fin N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : ‖s‖ ≤ 1) :
    EntryBd N (planeRot i k c s) := by
  intro a b
  have h1 : ‖(1 : Matrix (Fin N) (Fin N) ℂ) a b‖ ≤ 1 := by
    by_cases h : a = b
    · subst h; simp
    · simp [h]
  have e1 := entry_single_le i i a b
  have e2 := entry_single_le k k a b
  have e3 := entry_single_le k i a b
  have e4 := entry_single_le i k a b
  have hc' : ‖c - 1‖ ≤ 2 := by
    calc ‖c - 1‖ ≤ ‖c‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by simp; linarith
  unfold planeRot planeProj planeGen rotBound
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  have t1 : ‖(c - 1) * ((single i i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b +
      (single k k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b)‖ ≤ 4 := by
    rw [norm_mul]
    have : ‖(single i i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b +
        (single k k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b‖ ≤ 2 :=
      (norm_add_le _ _).trans (by linarith)
    nlinarith [norm_nonneg (c - 1), norm_nonneg ((single i i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b +
        (single k k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b)]
  have t2 : ‖s * ((single k i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b -
      (single i k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b)‖ ≤ 2 := by
    rw [norm_mul]
    have : ‖(single k i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b -
        (single i k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith)
    nlinarith [norm_nonneg s, norm_nonneg ((single k i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b -
        (single i k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b)]
  calc _ ≤ ‖(1 : Matrix (Fin N) (Fin N) ℂ) a b‖ + ‖(c - 1) * ((single i i (1 : ℂ) :
          Matrix (Fin N) (Fin N) ℂ) a b + (single k k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b)‖ +
        ‖s * ((single k i (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b -
          (single i k (1 : ℂ) : Matrix (Fin N) (Fin N) ℂ) a b)‖ :=
        (norm_add₃_le)
    _ ≤ 40 := by linarith

/-! ### Rodrigues' rotation of `a` into `q` -/

section Rodrigues

variable (a q : Spin N)

/-- First auxiliary vector of Rodrigues' formula. -/
noncomputable def rodU : Spin N :=
  (1 + dot a q / (1 + dot a q)) • q - (1 / (1 + dot a q)) • a

/-- Second auxiliary vector of Rodrigues' formula. -/
noncomputable def rodW : Spin N :=
  (1 - dot a q / (1 + dot a q)) • a + (1 / (1 + dot a q)) • q

/-- Rodrigues' rotation `1 + U aᵀ - W qᵀ`: the complex orthogonal matrix with `R a = q`
(for `a·a = q·q = 1`, `1 + a·q ≠ 0`). -/
noncomputable def rod : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i k => (1 : Matrix (Fin N) (Fin N) ℂ) i k + rodU a q i * a k - rodW a q i * q k

variable {a q}

theorem rod_dots (ha : dot a a = 1) (hq : dot q q = 1) (hD : 1 + dot a q ≠ 0) :
    dot (rodU a q) (rodU a q) = 2 / (1 + dot a q) ∧
    dot (rodU a q) (rodW a q) = 2 * dot a q / (1 + dot a q) ∧
    dot (rodW a q) (rodW a q) = 2 / (1 + dot a q) := by
  have hqa : dot q a = dot a q := dot_comm q a
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [rodU, rodW, dot_sub_left, dot_sub_right, dot_add_left, dot_add_right,
      dot_smul_left, dot_smul_right, ha, hq, hqa]
    field_simp
    ring

theorem rod_isOrth (ha : dot a a = 1) (hq : dot q q = 1) (hD : 1 + dot a q ≠ 0) :
    IsOrth (rod a q) := by
  obtain ⟨hUU, hUW, hWW⟩ := rod_dots ha hq hD
  unfold IsOrth
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rod, Matrix.of_apply]
  have e : ∀ l, ((1 : Matrix (Fin N) (Fin N) ℂ) l i + rodU a q l * a i - rodW a q l * q i) *
      ((1 : Matrix (Fin N) (Fin N) ℂ) l k + rodU a q l * a k - rodW a q l * q k) =
      (1 : Matrix (Fin N) (Fin N) ℂ) l i * (1 : Matrix (Fin N) (Fin N) ℂ) l k +
      (1 : Matrix (Fin N) (Fin N) ℂ) l i * (rodU a q l * a k - rodW a q l * q k) +
      (rodU a q l * a i - rodW a q l * q i) * (1 : Matrix (Fin N) (Fin N) ℂ) l k +
      (a i * a k * (rodU a q l * rodU a q l) - a i * q k * (rodU a q l * rodW a q l) -
        q i * a k * (rodU a q l * rodW a q l) + q i * q k * (rodW a q l * rodW a q l)) := by
    intro l; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have s1 : ∑ l, (1 : Matrix (Fin N) (Fin N) ℂ) l i * (1 : Matrix (Fin N) (Fin N) ℂ) l k =
      (1 : Matrix (Fin N) (Fin N) ℂ) i k := by
    simp only [Matrix.one_apply]
    rcases eq_or_ne i k with h | h
    · subst h; simp
    · simp [h, h.symm]
  have s2 : ∑ l, (1 : Matrix (Fin N) (Fin N) ℂ) l i * (rodU a q l * a k - rodW a q l * q k) =
      rodU a q i * a k - rodW a q i * q k := by
    simp [Matrix.one_apply]
  have s3 : ∑ l, (rodU a q l * a i - rodW a q l * q i) * (1 : Matrix (Fin N) (Fin N) ℂ) l k =
      rodU a q k * a i - rodW a q k * q i := by
    simp [Matrix.one_apply]
  have d1 : ∑ l, rodU a q l * rodU a q l = dot (rodU a q) (rodU a q) := rfl
  have d2 : ∑ l, rodU a q l * rodW a q l = dot (rodU a q) (rodW a q) := rfl
  have d3 : ∑ l, rodW a q l * rodW a q l = dot (rodW a q) (rodW a q) := rfl
  rw [s1, s2, s3, d1, d2, d3, hUU, hUW, hWW]
  simp only [rodU, rodW, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem rod_mulVec (ha : dot a a = 1) (hD : 1 + dot a q ≠ 0) :
    (rod a q).mulVec a = q := by
  have hqa : dot q a = dot a q := dot_comm q a
  ext i
  simp only [Matrix.mulVec, rod, Matrix.of_apply]
  have e : ∀ k, ((1 : Matrix (Fin N) (Fin N) ℂ) i k + rodU a q i * a k - rodW a q i * q k) * a k =
      (1 : Matrix (Fin N) (Fin N) ℂ) i k * a k + rodU a q i * (a k * a k) -
        rodW a q i * (q k * a k) := fun k => by ring
  have : ∑ k, ((1 : Matrix (Fin N) (Fin N) ℂ) i k + rodU a q i * a k - rodW a q i * q k) * a k =
      a i + rodU a q i * dot a a - rodW a q i * dot q a := by
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [dot, Matrix.one_apply]
  simp only [dotProduct]
  rw [this, ha, hqa]
  simp only [rodU, rodW, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem rod_entry_le (ha : ∀ k, ‖a k‖ ≤ 1) (hq : ∀ k, ‖q k‖ ≤ 8 / 3)
    (hc : ‖dot a q‖ ≤ 8 / 3) (hD : 1 ≤ ‖1 + dot a q‖) (i k : Fin N) :
    ‖rod a q i k‖ ≤ 30 := by
  set c := dot a q with hcdef
  set D := 1 + c with hDdef
  have hD0 : D ≠ 0 := by
    intro h; rw [h] at hD; simp at hD; linarith
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  have h1D : ‖(1 : ℂ) / D‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one hDpos]; exact hD
  have hcD : ‖c / D‖ ≤ 8 / 3 := by
    rw [norm_div, div_le_iff₀ hDpos]
    nlinarith [norm_nonneg c]
  have hα : ‖1 + c / D‖ ≤ 11 / 3 := by
    calc ‖1 + c / D‖ ≤ ‖(1 : ℂ)‖ + ‖c / D‖ := norm_add_le _ _
      _ ≤ 11 / 3 := by rw [norm_one]; linarith
  have hγ : ‖1 - c / D‖ ≤ 11 / 3 := by
    calc ‖1 - c / D‖ ≤ ‖(1 : ℂ)‖ + ‖c / D‖ := norm_sub_le _ _
      _ ≤ 11 / 3 := by rw [norm_one]; linarith
  have hU : ‖rodU a q i‖ ≤ 11 / 3 * (8 / 3) + 1 := by
    have : rodU a q i = (1 + c / D) * q i - (1 / D) * a i := by
      simp [rodU, hcdef, hDdef]
    rw [this]
    calc _ ≤ ‖(1 + c / D) * q i‖ + ‖(1 / D) * a i‖ := norm_sub_le _ _
      _ ≤ 11 / 3 * (8 / 3) + 1 * 1 := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hα (hq i) (norm_nonneg _) (by norm_num))
          (mul_le_mul h1D (ha i) (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  have hW : ‖rodW a q i‖ ≤ 11 / 3 * 1 + 1 * (8 / 3) := by
    have : rodW a q i = (1 - c / D) * a i + (1 / D) * q i := by
      simp [rodW, hcdef, hDdef]
    rw [this]
    calc _ ≤ ‖(1 - c / D) * a i‖ + ‖(1 / D) * q i‖ := norm_add_le _ _
      _ ≤ 11 / 3 * 1 + 1 * (8 / 3) := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hγ (ha i) (norm_nonneg _) (by norm_num))
          (mul_le_mul h1D (hq i) (norm_nonneg _) (by norm_num))
  have h1 : ‖(1 : Matrix (Fin N) (Fin N) ℂ) i k‖ ≤ 1 := by
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  have hUa : ‖rodU a q i * a k‖ ≤ (11 / 3 * (8 / 3) + 1) * 1 := by
    rw [norm_mul]; exact mul_le_mul hU (ha k) (norm_nonneg _) (by norm_num)
  have hWq : ‖rodW a q i * q k‖ ≤ (11 / 3 * 1 + 1 * (8 / 3)) * (8 / 3) := by
    rw [norm_mul]; exact mul_le_mul hW (hq k) (norm_nonneg _) (by norm_num)
  unfold rod
  rw [Matrix.of_apply]
  calc _ ≤ ‖(1 : Matrix (Fin N) (Fin N) ℂ) i k + rodU a q i * a k‖ + ‖rodW a q i * q k‖ :=
        norm_sub_le _ _
    _ ≤ (‖(1 : Matrix (Fin N) (Fin N) ℂ) i k‖ + ‖rodU a q i * a k‖) + ‖rodW a q i * q k‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 30 := by nlinarith

end Rodrigues

end Balaban.SmallField
