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

section Geometry

variable {d N M : ℕ} [NeZero N] {p : ℕ}

theorem dist_translate (e : L1Torus d N ≃ L1Torus d N) {t : Fin d → ZMod N}
    (he : ∀ x i, e x i = x i + t i) (x y : L1Torus d N) : dist (e x) (e y) = dist x y := by
  rw [dist_L1Torus, dist_L1Torus]
  unfold torusDist
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he, he, add_sub_add_right_eq_sub]

theorem isometry_translate (e : L1Torus d N ≃ L1Torus d N) {t : Fin d → ZMod N}
    (he : ∀ x i, e x i = x i + t i) : Isometry e :=
  Isometry.of_dist_eq (dist_translate e he)

theorem mem_macCore_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) (x : L1Torus d N) :
    e x ∈ macCore d N M (σ z) ↔ x ∈ macCore d N M z := by
  unfold macCore
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun i => ?_
  rw [he, Fin.ext_iff, hσ, macCell_add_cell hMN, Fin.ext_iff]
  have h1 := (macCell N M (x i)).isLt
  have h2 := (z i).isLt
  constructor
  · intro h
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' p h) h1 h2
  · intro h; rw [h]

theorem macCore_translate_eq_image (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) : macCore d N M (σ z) = e '' macCore d N M z := by
  ext y
  rw [Set.mem_image]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [← mem_macCore_translate hMN σ hσ e he, e.apply_symm_apply]
    exact hy
  · rintro ⟨x, hx, rfl⟩
    exact (mem_macCore_translate hMN σ hσ e he z x).2 hx

theorem mem_macBox_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) (x : L1Torus d N) :
    e x ∈ macBox d N M (σ z) ↔ x ∈ macBox d N M z := by
  show Metric.infDist (e x) (macCore d N M (σ z)) < 2 * M ↔
    Metric.infDist x (macCore d N M z) < 2 * M
  rw [macCore_translate_eq_image hMN σ hσ e he z, Metric.infDist_image (isometry_translate e he)]

theorem macPhi_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) (x : L1Torus d N) :
    macPhi d N M (σ z) (e x) = macPhi d N M z x := by
  unfold macPhi
  rw [macCore_translate_eq_image hMN σ hσ e he z, Metric.infDist_image (isometry_translate e he)]

theorem macSum_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (x : L1Torus d N) : macSum d N M (e x) = macSum d N M x := by
  unfold macSum
  rw [← Equiv.sum_comp σ]
  exact Finset.sum_congr rfl fun z _ => macPhi_translate hMN σ hσ e he z x

theorem macChi_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) (x : L1Torus d N) :
    macChi d N M (σ z) (e x) = macChi d N M z x := by
  unfold macChi
  rw [macPhi_translate hMN σ hσ e he, macSum_translate hMN σ hσ e he]

theorem mem_macBoxF_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) (x : L1Torus d N) :
    e x ∈ macBoxF d N M (σ z) ↔ x ∈ macBoxF d N M z := by
  rw [mem_macBoxF, mem_macBoxF, mem_macBox_translate hMN σ hσ e he]

theorem mem_macRegion_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (C : Finset (MacIdx d N M)) (x : L1Torus d N) :
    e x ∈ macRegion d N M (C.map σ.toEmbedding) ↔ x ∈ macRegion d N M C := by
  rw [mem_macRegion, mem_macRegion]
  constructor
  · rintro ⟨q, hq, hx⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.1 hq
    exact ⟨c, hc, (mem_macBox_translate hMN σ hσ e he c x).1 hx⟩
  · rintro ⟨c, hc, hx⟩
    exact ⟨σ c, Finset.mem_map_of_mem _ hc, (mem_macBox_translate hMN σ hσ e he c x).2 hx⟩

theorem mem_macArc_translate (a b t u : ZMod N) :
    u + t ∈ macArc (a + t) (b + t) ↔ u ∈ macArc a b := by
  unfold macArc
  rw [add_sub_add_right_eq_sub]
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨e, he, h⟩
    exact ⟨e, he, add_right_cancel (by rw [← h]; ring)⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by ring⟩

theorem mem_macPath_translate (e : L1Torus d N ≃ L1Torus d N) {t : Fin d → ZMod N}
    (he : ∀ x i, e x i = x i + t i) (x y q : L1Torus d N) :
    e q ∈ macPath d N (e x) (e y) ↔ q ∈ macPath d N x y := by
  unfold macPath
  simp only [Set.mem_setOf_eq, he]
  refine exists_congr fun k => ?_
  simp only [add_left_inj]
  rw [mem_macArc_translate]

theorem mem_macTags_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z w : MacIdx d N M) (x y : L1Torus d N) :
    σ w ∈ macTags d N M (σ z) (e x) (e y) ↔ w ∈ macTags d N M z x y := by
  unfold macTags
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hb := mem_macBox_translate hMN σ hσ e he
  have hp := mem_macPath_translate e he x y
  constructor
  · rintro (⟨q, h1, h2⟩ | ⟨q, h1, h2⟩)
    · left
      refine ⟨e.symm q, ?_, ?_⟩
      · rw [← hb]; simpa using h1
      · rw [← hb]; simpa using h2
    · right
      refine ⟨e.symm q, ?_, ?_⟩
      · rw [← hp]; simpa using h1
      · rw [← hb]; simpa using h2
  · rintro (⟨q, h1, h2⟩ | ⟨q, h1, h2⟩)
    · exact Or.inl ⟨e q, (hb _ _).2 h1, (hb _ _).2 h2⟩
    · exact Or.inr ⟨e q, (hp _).2 h1, (hb _ _).2 h2⟩

theorem macTags_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (z : MacIdx d N M) (x y : L1Torus d N) :
    macTags d N M (σ z) (e x) (e y) = (macTags d N M z x y).map σ.toEmbedding := by
  ext w
  obtain ⟨w', rfl⟩ := σ.surjective w
  rw [mem_macTags_translate hMN σ hσ e he]
  simp

end Geometry

section Operator

variable {d : ℕ}

theorem shiftMatrix_translate {ℓ : ℕ} [NeZero ℓ] (ef : Torus d ℓ ≃ Torus d ℓ) {s : Fin d → ZMod ℓ}
    (hef : ∀ x i, ef x i = x i + s i) (μ : Fin d) (x y : Torus d ℓ) :
    shiftMatrix (ℓ := ℓ) μ (ef x) (ef y) = shiftMatrix (ℓ := ℓ) μ x y := by
  unfold shiftMatrix
  have : ef y = ef x + Pi.single μ 1 ↔ y = x + Pi.single μ 1 := by
    constructor
    · intro h
      funext i
      have := congrFun h i
      rw [hef, Pi.add_apply, hef] at this
      rw [Pi.add_apply]
      exact add_right_cancel (this.trans (by ring))
    · rintro rfl
      funext i
      rw [hef, Pi.add_apply, Pi.add_apply, hef]
      ring
  simp only [this]

theorem latticeLaplacian_translate {ℓ : ℕ} [NeZero ℓ] (ef : Torus d ℓ ≃ Torus d ℓ)
    {s : Fin d → ZMod ℓ} (hef : ∀ x i, ef x i = x i + s i) (ν : ℝ) (x y : Torus d ℓ) :
    latticeLaplacian d ℓ ν (ef x) (ef y) = latticeLaplacian d ℓ ν x y := by
  simp only [latticeLaplacian, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix_translate ef hef, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq]

theorem blockMap_translate {B m : ℕ} [NeZero B] [NeZero m] (ef : Torus d (m * B) ≃ Torus d (m * B))
    (t : Fin d → ZMod m)
    (hef : ∀ x i, ef x i = x i + ((B * (t i).val : ℕ) : ZMod (m * B))) (x : Torus d (m * B)) :
    blockMap B m (ef x) = fun i => blockMap B m x i + t i := by
  funext i
  unfold blockMap blockCoord
  have hB := Nat.pos_of_ne_zero (NeZero.ne B)
  have key : ∀ a c : ℕ, (a + B * c) % (m * B) / B = (a / B + c) % m := by
    intro a c
    rw [mul_comm m B, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ hB]
  rw [hef, ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, key]
  rw [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val]

theorem blockProjMatrix_translate {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]
    (ef : Torus d ℓ ≃ Torus d ℓ) (ec : Torus d m ≃ Torus d m)
    (hblock : ∀ x, blockMap N m (ef x) = ec (blockMap N m x)) (x y : Torus d ℓ) :
    blockProjMatrix d ℓ N m (ef x) (ef y) = blockProjMatrix d ℓ N m x y := by
  unfold blockProjMatrix
  simp only [hblock, EmbeddingLike.apply_eq_iff_eq]

theorem fineHamiltonian_translate {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]
    (ef : Torus d ℓ ≃ Torus d ℓ) {s : Fin d → ZMod ℓ} (hef : ∀ x i, ef x i = x i + s i)
    (ec : Torus d m ≃ Torus d m)
    (hblock : ∀ x, blockMap N m (ef x) = ec (blockMap N m x)) (ν a : ℝ) :
    (fineHamiltonian d ℓ N m ν a).submatrix ef ef = fineHamiltonian d ℓ N m ν a := by
  ext x y
  simp only [Matrix.submatrix_apply, fineHamiltonian, Matrix.add_apply, Matrix.smul_apply,
    latticeLaplacian_translate ef hef, blockProjMatrix_translate ef ec hblock]

theorem unconstrainedUnitOperator_translate {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]
    (ef : Torus d ℓ ≃ Torus d ℓ) {s : Fin d → ZMod ℓ} (hef : ∀ x i, ef x i = x i + s i)
    (ec : Torus d m ≃ Torus d m)
    (hblock : ∀ x, blockMap N m (ef x) = ec (blockMap N m x)) (ν a : ℝ) :
    (unconstrainedUnitOperator d ℓ N m ν a).submatrix ec ec = unconstrainedUnitOperator d ℓ N m ν a := by
  have hQ : (unitBlockAverageMatrix d ℓ N m).submatrix ec ef = unitBlockAverageMatrix d ℓ N m := by
    ext y x
    simp only [Matrix.submatrix_apply, unitBlockAverageMatrix, hblock, EmbeddingLike.apply_eq_iff_eq]
  have hP : (blockPullbackMatrix d ℓ N m).submatrix ef ec = blockPullbackMatrix d ℓ N m := by
    ext x y
    simp only [Matrix.submatrix_apply, blockPullbackMatrix, hblock, EmbeddingLike.apply_eq_iff_eq]
  have hH := fineHamiltonian_translate (N := N) (m := m) ef hef ec hblock ν a
  have hmul : (unitBlockAverageMatrix d ℓ N m * (fineHamiltonian d ℓ N m ν a)⁻¹ *
      blockPullbackMatrix d ℓ N m).submatrix ec ec =
      unitBlockAverageMatrix d ℓ N m * (fineHamiltonian d ℓ N m ν a)⁻¹ *
      blockPullbackMatrix d ℓ N m := by
    rw [← Matrix.submatrix_mul_equiv _ _ ec ef ec, ← Matrix.submatrix_mul_equiv _ _ ec ef ef, hQ, hP,
      ← Matrix.inv_submatrix_equiv, hH]
  ext x y
  have := congrFun (congrFun hmul x) y
  simp only [Matrix.submatrix_apply] at this
  simp only [Matrix.submatrix_apply, unconstrainedUnitOperator, Matrix.sub_apply, Matrix.smul_apply,
    this, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]

/-- **The final operator is covariant under translations of the coarse torus.** -/
theorem finalOp_translate {L N k : ℕ} [NeZero N] [NeZero L] (e : L1Torus d N ≃ L1Torus d N)
    {t : Fin d → ZMod N} (he : ∀ x i, e x i = x i + t i) (v a : ℝ) :
    (finalOp d L N k v a).submatrix e e = finalOp d L N k v a := by
  let ef : Torus d (N * L ^ k) ≃ Torus d (N * L ^ k) :=
    Equiv.addRight (fun i => ((L ^ k * (t i).val : ℕ) : ZMod (N * L ^ k)))
  have hef : ∀ x i, ef x i = x i + ((L ^ k * (t i).val : ℕ) : ZMod (N * L ^ k)) := fun x i => rfl
  have hblock : ∀ x, blockMap (L ^ k) N (ef x) = (e : Torus d N → Torus d N) (blockMap (L ^ k) N x) :=
    fun x => by
      rw [blockMap_translate ef t hef x]
      funext i
      exact (he _ i).symm
  have h := unconstrainedUnitOperator_translate (N := L ^ k) (m := N) ef
    (s := fun i => ((L ^ k * (t i).val : ℕ) : ZMod (N * L ^ k))) hef e hblock v a
  ext x y
  have := congrFun (congrFun h x) y
  exact congrArg (algebraMap ℝ ℂ) this

end Operator

end Balaban.Green
