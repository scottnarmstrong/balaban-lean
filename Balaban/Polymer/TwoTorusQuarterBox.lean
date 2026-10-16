/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTorusCloseUnif
public import Balaban.Polymer.TwoTorusFinal
public import Balaban.Localization.DecEquivRelabel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Translation covariance of the last-scale parametrix and the two-sided box (W837, blocker 7)

Draft.
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem submatrix_equiv_add (e : ι ≃ ι) (A B : Matrix ι ι ℂ) :
    (A + B).submatrix e e = A.submatrix e e + B.submatrix e e := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem submatrix_equiv_sub (e : ι ≃ ι) (A B : Matrix ι ι ℂ) :
    (A - B).submatrix e e = A.submatrix e e - B.submatrix e e := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem submatrix_equiv_smul (e : ι ≃ ι) (c : ℂ) (A : Matrix ι ι ℂ) :
    (c • A).submatrix e e = c • A.submatrix e e := rfl

omit [DecidableEq ι] in
theorem submatrix_equiv_mul (e : ι ≃ ι) (A B : Matrix ι ι ℂ) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e :=
  (Matrix.submatrix_mul_equiv A B e e e).symm

omit [Fintype ι] in
theorem boxP_submatrix_equiv (e : ι ≃ ι) {B B' : Finset ι} (hB : ∀ x, e x ∈ B' ↔ x ∈ B) :
    (boxP B').submatrix e e = boxP B := by
  unfold boxP
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  simp only [Function.comp, hB]

omit [Fintype ι] in
theorem shiftMat_submatrix_equiv (e : ι ≃ ι) (U : Matrix ι ι ℂ) (t : ℝ) :
    (shiftMat U t).submatrix e e = shiftMat (U.submatrix e e) t := by
  unfold shiftMat
  rw [submatrix_equiv_add, submatrix_equiv_smul, Matrix.submatrix_one_equiv]

theorem boxH_submatrix_equiv (e : ι ≃ ι) {U U' : Matrix ι ι ℂ} {B B' : Finset ι}
    (hU : U'.submatrix e e = U) (hB : ∀ x, e x ∈ B' ↔ x ∈ B) (t : ℝ) :
    (boxH U' B' t).submatrix e e = boxH U B t := by
  unfold boxH
  rw [submatrix_equiv_add, submatrix_equiv_mul, submatrix_equiv_mul, submatrix_equiv_sub,
    Matrix.submatrix_one_equiv, boxP_submatrix_equiv e hB, shiftMat_submatrix_equiv, hU]

theorem boxG_submatrix_equiv (e : ι ≃ ι) {U U' : Matrix ι ι ℂ} {B B' : Finset ι}
    (hU : U'.submatrix e e = U) (hB : ∀ x, e x ∈ B' ↔ x ∈ B) (t : ℝ) :
    (boxG U' B' t).submatrix e e = boxG U B t := by
  unfold boxG
  rw [submatrix_equiv_mul, boxP_submatrix_equiv e hB]
  congr 1
  have h := boxH_submatrix_equiv e hU hB t
  rw [← h]
  exact (Matrix.inv_submatrix_equiv (boxH U' B' t) e e).symm

theorem boxR_submatrix_equiv (e : ι ≃ ι) {U U' : Matrix ι ι ℂ} {B B' : Finset ι}
    {c c' : ι → ℂ} (hU : U'.submatrix e e = U) (hB : ∀ x, e x ∈ B' ↔ x ∈ B)
    (hc : ∀ x, c' (e x) = c x) (t : ℝ) :
    (boxR U' B' c' t).submatrix e e = boxR U B c t := by
  unfold boxR
  have h : c' ∘ e = c := funext hc
  rw [submatrix_equiv_sub, submatrix_equiv_mul, submatrix_equiv_mul, Matrix.submatrix_diagonal_equiv,
    shiftMat_submatrix_equiv, hU, boxG_submatrix_equiv e hU hB, h]

end Algebra

section Tagged

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Pc : Type*} [Fintype Z] [Fintype Pc]

omit [Fintype Pc] in
theorem tagMon_map_equiv (ρ : Pc ≃ Pc) (V : Finset Pc) (s : Pc → ℂ) :
    tagMon (V.map ρ.toEmbedding) s = tagMon V (s ∘ ρ) := by
  unfold tagMon
  rw [Finset.prod_map]
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
theorem taggedMat_submatrix_equiv (e : ι ≃ ι) (σ : Z ≃ Z) (ρ : Pc ≃ Pc)
    {V V' : Z → ι → ι → Finset Pc} {a a' : Z → Matrix ι ι ℂ}
    (hV : ∀ z x y, V' (σ z) (e x) (e y) = (V z x y).map ρ.toEmbedding)
    (ha : ∀ z, (a' (σ z)).submatrix e e = a z) (s : Pc → ℂ) :
    (taggedMat Finset.univ V' a' s).submatrix e e = taggedMat Finset.univ V a (s ∘ ρ) := by
  ext x y
  simp only [Matrix.submatrix_apply, taggedMat, Matrix.of_apply]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hV, tagMon_map_equiv, ← ha z]
  rfl

theorem taggedG_submatrix_equiv (e : ι ≃ ι) (σ : Z ≃ Z) (ρ : Pc ≃ Pc)
    {V V' : Z → ι → ι → Finset Pc} {B B' : Z → Finset ι} {c c' : Z → ι → ℂ}
    {U U' : Matrix ι ι ℂ}
    (hV : ∀ z x y, V' (σ z) (e x) (e y) = (V z x y).map ρ.toEmbedding)
    (hU : U'.submatrix e e = U) (hB : ∀ z x, e x ∈ B' (σ z) ↔ x ∈ B z)
    (hc : ∀ z x, c' (σ z) (e x) = c z x) (t : ℝ) (s : Pc → ℂ) :
    (taggedG Finset.univ B' c' V' U' t s).submatrix e e =
      taggedG Finset.univ B c V U t (s ∘ ρ) := by
  unfold taggedG
  refine taggedMat_submatrix_equiv e σ ρ hV (fun z => ?_) s
  rw [submatrix_equiv_mul, Matrix.submatrix_diagonal_equiv, boxG_submatrix_equiv e hU (hB z) t]
  have h : (c' (σ z)) ∘ e = c z := funext (hc z)
  rw [h]

theorem taggedK_submatrix_equiv (e : ι ≃ ι) (σ : Z ≃ Z) (ρ : Pc ≃ Pc)
    {V V' : Z → ι → ι → Finset Pc} {B B' : Z → Finset ι} {c c' : Z → ι → ℂ}
    {U U' : Matrix ι ι ℂ}
    (hV : ∀ z x y, V' (σ z) (e x) (e y) = (V z x y).map ρ.toEmbedding)
    (hU : U'.submatrix e e = U) (hB : ∀ z x, e x ∈ B' (σ z) ↔ x ∈ B z)
    (hc : ∀ z x, c' (σ z) (e x) = c z x) (t : ℝ) (s : Pc → ℂ) :
    (taggedK Finset.univ B' c' V' U' t s).submatrix e e =
      taggedK Finset.univ B c V U t (s ∘ ρ) := by
  unfold taggedK
  exact taggedMat_submatrix_equiv e σ ρ hV (fun z => boxR_submatrix_equiv e hU (hB z) (hc z) t) s

theorem taggedGfin_submatrix_equiv (e : ι ≃ ι) (σ : Z ≃ Z) (ρ : Pc ≃ Pc)
    {V V' : Z → ι → ι → Finset Pc} {B B' : Z → Finset ι} {c c' : Z → ι → ℂ}
    {U U' : Matrix ι ι ℂ}
    (hV : ∀ z x y, V' (σ z) (e x) (e y) = (V z x y).map ρ.toEmbedding)
    (hU : U'.submatrix e e = U) (hB : ∀ z x, e x ∈ B' (σ z) ↔ x ∈ B z)
    (hc : ∀ z x, c' (σ z) (e x) = c z x) (t : ℝ) (s : Pc → ℂ) :
    (taggedGfin Finset.univ B' c' V' U' t s).submatrix e e =
      taggedGfin Finset.univ B c V U t (s ∘ ρ) := by
  unfold taggedGfin
  rw [submatrix_equiv_mul, taggedG_submatrix_equiv e σ ρ hV hU hB hc,
    ← taggedK_submatrix_equiv e σ ρ hV hU hB hc t s]
  congr 1
  rw [← Matrix.inv_submatrix_equiv, submatrix_equiv_sub, Matrix.submatrix_one_equiv]

end Tagged


section CellArith

variable {N M : ℕ} [NeZero N]

theorem macK_eq_div_of_dvd (hMN : M ∣ N) : macK N M = N / M := by
  have hM : 0 < M := Nat.pos_of_dvd_of_pos hMN (Nat.pos_of_ne_zero (NeZero.ne N))
  exact macK_eq_div hM (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hMN)

theorem macCell_val_eq (hMN : M ∣ N) (v : ZMod N) : (macCell N M v : ℕ) = v.val / M := by
  have hM : 0 < M := Nat.pos_of_dvd_of_pos hMN (Nat.pos_of_ne_zero (NeZero.ne N))
  have hK := macK_eq_div_of_dvd hMN
  have hlt : v.val / M < macK N M := by
    rw [hK]; exact Nat.div_lt_div_of_lt_of_dvd hMN (ZMod.val_lt v)
  show min (v.val / M) (macK N M - 1) = v.val / M
  omega

theorem macCell_add_cell (hMN : M ∣ N) (v : ZMod N) (p : ℕ) :
    (macCell N M (v + ((M * p : ℕ) : ZMod N)) : ℕ) = ((macCell N M v : ℕ) + p) % macK N M := by
  have hM : 0 < M := Nat.pos_of_dvd_of_pos hMN (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨K, hK⟩ := hMN
  have hKk : macK N M = K := by
    rw [macK_eq_div_of_dvd ⟨K, hK⟩, hK, Nat.mul_div_cancel_left _ hM]
  rw [macCell_val_eq ⟨K, hK⟩, macCell_val_eq ⟨K, hK⟩, hKk, ZMod.val_add, ZMod.val_natCast,
    Nat.add_mod_mod]
  have h1 := Nat.mod_mul_right_div_self (v.val + M * p) M K
  rw [← hK] at h1
  rw [h1, Nat.add_mul_div_left _ _ hM]

omit [NeZero N] in
/-- The cyclic shift of the cell indices by `p` in every coordinate. -/
theorem exists_cellShift (d p : ℕ) :
    ∃ σ : MacIdx d N M ≃ MacIdx d N M, ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M := by
  have : NeZero (macK N M) := ⟨(macK_pos N M).ne'⟩
  refine ⟨Equiv.piCongrRight fun _ => Equiv.addRight (⟨p % macK N M, Nat.mod_lt _ (macK_pos N M)⟩ : Fin (macK N M)), fun z i => ?_⟩
  simp only [Equiv.piCongrRight_apply, Equiv.coe_addRight, Pi.map_apply, Fin.val_add,
    Nat.add_mod_mod]

end CellArith

end Balaban.Green
