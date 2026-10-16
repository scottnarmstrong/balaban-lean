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

omit [Fintype Pc] in
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

omit [Fintype Pc] in
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

omit [Fintype Pc] in
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
  simp only [Set.mem_ofPred_eq]
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

omit [NeZero N] in
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

omit [NeZero N] in
theorem mem_macPath_translate (e : L1Torus d N ≃ L1Torus d N) {t : Fin d → ZMod N}
    (he : ∀ x i, e x i = x i + t i) (x y q : L1Torus d N) :
    e q ∈ macPath d N (e x) (e y) ↔ q ∈ macPath d N x y := by
  unfold macPath
  simp only [Set.mem_ofPred_eq, he]
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

section Final

open MeasureTheory Set Balaban.Localization

variable {d M N L k : ℕ} [NeZero N] [NeZero L] {p : ℕ}

omit [NeZero N] [NeZero L] in
/-- A translation of the coarse torus with prescribed coordinates exists. -/
theorem exists_translate (t : Fin d → ZMod N) :
    ∃ e : L1Torus d N ≃ L1Torus d N, ∀ x i, e x i = x i + t i :=
  ⟨(Equiv.addRight (t : Torus d N) : Torus d N ≃ Torus d N), fun _ _ => rfl⟩

/-- **The tagged parametrix `G_fin` of the final operator is covariant under the translation by
`p` cells.** -/
theorem taggedGfin_final_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (v a t : ℝ) (s : MacIdx d N M → ℂ) :
    (taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t s).submatrix e e =
      taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t (s ∘ σ) :=
  taggedGfin_submatrix_equiv (ι := L1Torus d N) (Z := MacIdx d N M) (Pc := MacIdx d N M)
    (V := macTags d N M) (V' := macTags d N M) (B := macBoxF d N M) (B' := macBoxF d N M)
    (c := fun z u => ((macChi d N M z u : ℝ) : ℂ)) (c' := fun z u => ((macChi d N M z u : ℝ) : ℂ))
    (U := finalOp d L N k v a) (U' := finalOp d L N k v a)
    e σ σ (fun z x y => macTags_translate hMN σ hσ e he z x y)
    (finalOp_translate (L := L) (k := k) e he v a) (fun z x => mem_macBoxF_translate hMN σ hσ e he z x)
    (fun z x => by simp only [macChi_translate hMN σ hσ e he]) t s

/-- **The Stieltjes square root `taggedCfin` of the final operator is covariant under the
translation by `p` cells.** -/
theorem taggedCfin_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (v a : ℝ) (s : MacIdx d N M → ℂ) :
    (taggedCfin d L N k M v a s).submatrix e e = taggedCfin d L N k M v a (s ∘ σ) := by
  have hG : ∀ t : ℝ, ((((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t s).submatrix e e) =
      (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t (s ∘ σ)) := fun t => by
    rw [← taggedGfin_final_translate (L := L) (k := k) hMN σ hσ e he v a t s]
    rfl
  ext x y
  have hent : ∀ (s' : MacIdx d N M → ℂ) (u w : L1Torus d N),
      (taggedCfin d L N k M v a s') u w = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t s') u w := fun s' u w => by
    unfold taggedCfin
    rw [Matrix.smul_apply]
    simp only [Localization.intMat, smul_eq_mul]
  rw [Matrix.submatrix_apply, hent s (e x) (e y), hent (s ∘ σ) x y]
  have hint : (∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t s) (e x) (e y)) =
      ∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) (finalOp d L N k v a) t (s ∘ σ)) x y :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => congrFun (congrFun (hG t) x) y)
  rw [hint]

section LogDet

open Balaban.Localization Balaban.Analysis

variable {d M N L k : ℕ} [NeZero N] [NeZero L] {p : ℕ}

theorem comp_perm_mem_ball {Z : Type*} [Fintype Z] (σ : Z ≃ Z) {ρ : ℝ} {s : Z → ℂ}
    (hs : s ∈ Metric.ball (0 : Z → ℂ) ρ) : s ∘ σ ∈ Metric.ball (0 : Z → ℂ) ρ := by
  rw [mem_ball_zero_iff] at hs ⊢
  refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => ?_) hs
  exact norm_le_pi_norm s (σ z)

theorem analyticOnNhd_comp_perm {Z : Type*} [Fintype Z] (σ : Z ≃ Z) {ρ : ℝ} {f : (Z → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : Z → ℂ) ρ)) :
    AnalyticOnNhd ℂ (fun s : Z → ℂ => f (s ∘ σ)) (Metric.ball (0 : Z → ℂ) ρ) := by
  let T : (Z → ℂ) →L[ℂ] (Z → ℂ) := ContinuousLinearMap.pi fun z => ContinuousLinearMap.proj (σ z)
  have hT : ∀ s, T s = s ∘ σ := fun s => rfl
  have h := hf.comp (fun s _ => T.analyticAt s) (fun s hs => (hT s ▸ comp_perm_mem_ball σ hs))
  exact h

theorem wSmall_submatrix_equiv {r η : ℝ} (e : L1Torus d N ≃ L1Torus d N) {t : Fin d → ZMod N}
    (he : ∀ x i, e x i = x i + t i) {E : Matrix (L1Torus d N) (L1Torus d N) ℂ}
    (hE : WSmall r η E) : WSmall r η (E.submatrix e.symm e.symm) := by
  have hd : ∀ x y, dist (e.symm x) (e.symm y) = dist x y := fun x y => by
    have := dist_translate e he (e.symm x) (e.symm y)
    simpa using this.symm
  constructor
  · intro x
    have := hE.1 (e.symm x)
    rw [← Equiv.sum_comp e.symm] at this
    simpa [Matrix.submatrix_apply, hd] using this
  · intro y
    have := hE.2 (e.symm y)
    rw [← Equiv.sum_comp e.symm] at this
    simpa [Matrix.submatrix_apply, hd] using this

/-- **The determinant of the perturbed tagged defect is covariant**: the defect built from the
transported perturbation `E ∘ τ⁻¹` at the parameter `s` has the determinant of the defect built
from `E` at the parameter `s ∘ σ`. -/
theorem det_taggedKE_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (E : Matrix (L1Torus d N) (L1Torus d N) ℂ) (v a t : ℝ) (s : MacIdx d N M → ℂ) :
    (1 - taggedMat Finset.univ (macTags d N M)
        (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E.submatrix e.symm e.symm * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s).det =
    (1 - taggedMat Finset.univ (macTags d N M)
        (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t)) (s ∘ σ)).det := by
  rw [← Matrix.det_submatrix_equiv_self e]
  have hU := finalOp_translate (L := L) (k := k) e he v a
  have hmat := taggedMat_submatrix_equiv (ι := L1Torus d N) (Z := MacIdx d N M)
    (Pc := MacIdx d N M) e σ σ (V := macTags d N M) (V' := macTags d N M)
    (a := fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t))
    (a' := fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E.submatrix e.symm e.symm * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t))
    (fun z x y => macTags_translate hMN σ hσ e he z x y) (fun z => by
      have hc : (fun u => ((macChi d N M (σ z) u : ℝ) : ℂ)) ∘ e =
          fun u => ((macChi d N M z u : ℝ) : ℂ) := funext fun u => by
        simp only [Function.comp, macChi_translate hMN σ hσ e he]
      show ((boxR (finalOp d L N k v a) (macBoxF d N M (σ z))
            (fun u => ((macChi d N M (σ z) u : ℝ) : ℂ)) t -
          E.submatrix e.symm e.symm * (Matrix.diagonal (fun u => ((macChi d N M (σ z) u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M (σ z)) t))).submatrix e e = _
      rw [submatrix_equiv_sub, submatrix_equiv_mul, submatrix_equiv_mul,
        Matrix.submatrix_diagonal_equiv, hc,
        boxR_submatrix_equiv e hU (fun x => mem_macBoxF_translate hMN σ hσ e he z x)
          (fun x => congrArg (fun r : ℝ => (r : ℂ)) (macChi_translate hMN σ hσ e he z x)) t,
        boxG_submatrix_equiv e hU (fun x => mem_macBoxF_translate hMN σ hσ e he z x) t,
        Matrix.submatrix_submatrix]
      simp) s
  rw [submatrix_equiv_sub, Matrix.submatrix_one_equiv, hmat]

theorem coef_comp_perm {Z : Type*} [Fintype Z] [DecidableEq Z] (σ : Z ≃ Z) {ρ : ℝ} (hρ : 1 < ρ)
    {f : (Z → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.ball (0 : Z → ℂ) ρ)) (C : Finset Z) :
    coef (fun s : Z → ℂ => f (s ∘ σ)) (C.map σ.toEmbedding) = coef f C := by
  have hρ0 : 0 < ρ := by linarith
  refine coef_relabel hρ σ (f := f) (f' := fun s : Z → ℂ => f (s ∘ σ)) ?_ ?_ (fun s _ => rfl) C
  · rw [polydisc_eq_ball hρ0]; exact hf
  · rw [polydisc_eq_ball hρ0]; exact analyticOnNhd_comp_perm σ hf

section CellMap

variable {d M N N' : ℕ} {p J : ℕ}

theorem cellMap_translate (σ : MacIdx d N M ≃ MacIdx d N M) (σ' : MacIdx d N' M ≃ MacIdx d N' M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (hσ' : ∀ z i, (σ' z i : ℕ) = ((z i : ℕ) + p) % macK N' M)
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, ((z i : ℕ) + p) % macK N M ≤ J + 4 →
        ((e z i : ℕ) + p) % macK N' M = ((z i : ℕ) + p) % macK N M) :
    ∀ z i, (z i : ℕ) ≤ J + 4 →
      (((fun w => σ' (e (σ.symm w))) z i : Fin (macK N' M)) : ℕ) = z i := by
  intro z i hz
  have hz' : (z i : ℕ) = (((σ.symm z) i : ℕ) + p) % macK N M := by
    have := hσ (σ.symm z) i
    rw [Equiv.apply_symm_apply] at this
    exact this
  show ((σ' (e (σ.symm z)) i : Fin (macK N' M)) : ℕ) = z i
  rw [hσ', he (σ.symm z) i (by rw [← hz']; exact hz), ← hz']

theorem window_translate (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M) {C : Finset (MacIdx d N M)}
    (hC : ∀ z ∈ C, ∀ i, 4 ≤ ((z i : ℕ) + p) % macK N M ∧ ((z i : ℕ) + p) % macK N M ≤ J) :
    ∀ z ∈ C.map σ.toEmbedding, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J := by
  intro z hz i
  obtain ⟨c, hc, rfl⟩ := Finset.mem_map.1 hz
  have := hC c hc i
  rw [Equiv.toEmbedding_apply, hσ]
  exact this

theorem image_translate (σ : MacIdx d N M ≃ MacIdx d N M) (σ' : MacIdx d N' M ≃ MacIdx d N' M)
    (e : MacIdx d N M → MacIdx d N' M) (C : Finset (MacIdx d N M)) :
    (C.map σ.toEmbedding).image (fun w => σ' (e (σ.symm w))) =
      (C.image e).map σ'.toEmbedding := by
  classical
  ext w
  simp only [Finset.mem_image, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨e c, ⟨c, hc, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨σ c, ⟨c, hc, rfl⟩, by simp⟩

end CellMap

/-- **The localized coefficients of the logarithm of the perturbed defect on two tori, for supports
in a two-sided box.**  This is `final_coef_logdet_close_twoTorus_unif` for a support whose cells
are, after the cyclic shift by `p` cells in every coordinate, in the window of indices `[4, J]`: the
two tori are identified by the residues of the shifted coordinates, and the cell map `e` is the
identity on the shifted indices `≤ J + 4`. -/
theorem final_coef_logdet_close_twoTorus_box {d M L : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      M ∣ N → M ∣ N' → ∀ {p : ℕ},
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * p : ℕ) : ZMod N') =
        ((((x μ + ((M * p : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + p) % macK N M ≤ J + 4 →
        ((e z i : ℕ) + p) % macK N' M = ((z i : ℕ) + p) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ ((z i : ℕ) + p) % macK N M ∧ ((z i : ℕ) + p) % macK N M ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {t : ℝ}, 0 ≤ t →
      ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
      WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
      (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖E x y - E' (f x) (f y)‖ ≤ εE) →
      ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
      ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
      ell 0 = 0 → ell' 0 = 0 →
      (∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
        (1 - taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s).det =
          Complex.exp (ell s)) →
      (∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s).det =
          Complex.exp (ell' s)) →
      ‖coef ell C - coef ell' (C.image e)‖ ≤
        P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))) + εE) /
          (Real.exp κ - 1) ^ C.card := by
  obtain ⟨P, C₀, c₀, hP0, hC₀, hc₀, hmain⟩ :=
    final_coef_logdet_close_twoTorus_unif (L := L) hd hM hκ hMB hMκ hrE hη0 hη nC
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro k hk J N N' _ _ hN hN' hMN hMN' p f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass t ht E E' hE hE'
    εE hεE hEcl ρ ρ' hρ hρ' ell ell' hell hell' h0 h0' hdet hdet'
  obtain ⟨σ, hσ⟩ := exists_cellShift (N := N) (M := M) d p
  obtain ⟨σ', hσ'⟩ := exists_cellShift (N := N') (M := M) d p
  obtain ⟨e1, he1⟩ := exists_translate (N := N) (d := d) (fun _ => ((M * p : ℕ) : ZMod N))
  obtain ⟨e1', he1'⟩ := exists_translate (N := N') (d := d) (fun _ => ((M * p : ℕ) : ZMod N'))
  have hκ1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hρ1 : 1 < ρ := lt_trans hκ1 hρ
  have hρ1' : 1 < ρ' := lt_trans hκ1 hρ'
  have hemap := cellMap_translate σ σ' hσ hσ' he
  have hcard : (C.map σ.toEmbedding).card ≤ nC := by rw [Finset.card_map]; exact hCc
  have hCw := window_translate σ hσ hC
  have hEcl' : ∀ x ∈ macRegion d N M (C.map σ.toEmbedding), ∀ y ∈ macRegion d N M (C.map σ.toEmbedding),
      ‖E.submatrix e1.symm e1.symm x y -
        E'.submatrix e1'.symm e1'.symm ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) x)
          ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) y)‖ ≤ εE := by
    intro x hx y hy
    have hxx : x = e1 (e1.symm x) := (e1.apply_symm_apply x).symm
    have hyy : y = e1 (e1.symm y) := (e1.apply_symm_apply y).symm
    have hx0 : e1.symm x ∈ macRegion d N M C := by
      rw [← mem_macRegion_translate hMN σ hσ e1 he1 C, ← hxx]; exact hx
    have hy0 : e1.symm y ∈ macRegion d N M C := by
      rw [← mem_macRegion_translate hMN σ hσ e1 he1 C, ← hyy]; exact hy
    have key : ∀ z : L1Torus d N, f (e1.symm z) = e1'.symm
        ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) z) := by
      intro z
      refine (Equiv.eq_symm_apply e1').2 ?_
      funext μ
      have hz : (e1.symm z) μ + ((M * p : ℕ) : ZMod N) = z μ := by
        have := he1 (e1.symm z) μ
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
      exact ((he1' (f (e1.symm z)) μ).trans ((hf (e1.symm z) μ).trans
        (congrArg (fun w : ZMod N => (((w.val : ℕ)) : ZMod N')) hz)))
    have hEc := hEcl _ hx0 _ hy0
    rw [key x, key y] at hEc
    exact hEc
  have hcoefs := hmain hk hN hN' (f := fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N'))
    (fun _ _ => rfl) (e := fun w => σ' (e (σ.symm w))) hemap hcard hCw hv0 hv1 ha1 ha2 hmass ht
    (wSmall_submatrix_equiv e1 he1 hE) (wSmall_submatrix_equiv e1' he1' hE') hεE hEcl' hρ hρ'
    (analyticOnNhd_comp_perm σ hell) (analyticOnNhd_comp_perm σ' hell') h0 h0'
    (fun s hs => by
      rw [det_taggedKE_translate hMN σ hσ e1 he1 E v a t s]
      exact hdet (s ∘ σ) (comp_perm_mem_ball σ hs))
    (fun s hs => by
      rw [det_taggedKE_translate hMN' σ' hσ' e1' he1' E' v a t s]
      exact hdet' (s ∘ σ') (comp_perm_mem_ball σ' hs))
  have himg := image_translate σ σ' e C
  rw [himg, coef_comp_perm σ hρ1 hell, coef_comp_perm σ' hρ1' hell', Finset.card_map] at hcoefs
  exact hcoefs

end LogDet

end Final

section Cutoff

open MeasureTheory Set Balaban.Localization Balaban.Analysis

variable {d M N L k : ℕ} [NeZero N] [NeZero L] {p : ℕ}

/-- The field transport `ψ ↦ ψ ∘ τ⁻¹` is a measurable equivalence. -/
theorem exists_fieldEquiv {ι : Type*} (e : ι ≃ ι) :
    ∃ T : (ι → ℝ) ≃ᵐ (ι → ℝ), ∀ ψ x, T ψ x = ψ (e.symm x) :=
  ⟨MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ), fun _ _ => rfl⟩

theorem fieldEquiv_preimage_box {ι : Type*} (e : ι ≃ ι) (T : (ι → ℝ) ≃ᵐ (ι → ℝ))
    (hT : ∀ ψ x, T ψ x = ψ (e.symm x)) (ρ : ℝ) :
    T ⁻¹' {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} = {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} := by
  ext ψ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hT]
  exact ⟨fun h y => by simpa using h (e y), fun h y => h _⟩

theorem measurableSet_box {ι : Type*} [Finite ι] (ρ : ℝ) :
    MeasurableSet {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} := by
  have : {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ} = ⋂ y, {ψ : ι → ℝ | |ψ y| ≤ ρ} := by
    ext ψ; simp
  rw [this]
  exact MeasurableSet.iInter fun y =>
    measurableSet_le ((measurable_pi_apply y).abs) measurable_const

theorem integral_box_map {ι : Type*} [Finite ι] (e : ι ≃ ι) (T : (ι → ℝ) ≃ᵐ (ι → ℝ))
    (hT : ∀ ψ x, T ψ x = ψ (e.symm x)) (γ : Measure (ι → ℝ)) (ρ : ℝ) (g : (ι → ℝ) → ℂ) :
    ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, g ψ ∂(γ.map T) =
      ∫ ψ in {ψ : ι → ℝ | ∀ y, |ψ y| ≤ ρ}, g (T ψ) ∂γ := by
  rw [Measure.restrict_map T.measurable (measurableSet_box ρ), fieldEquiv_preimage_box e T hT ρ]
  exact integral_map_equiv T g

theorem analyticOnNhd_polydisc_comp_equiv {ι : Type*} [Fintype ι] (e : ι ≃ ι) {R : ℝ}
    {F : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polydisc (0 : ι → ℂ) (fun _ => R))) :
    AnalyticOnNhd ℂ (fun w : ι → ℂ => F (fun x => w (e x))) (polydisc (0 : ι → ℂ) (fun _ => R)) := by
  let T : (ι → ℂ) →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi fun x => ContinuousLinearMap.proj (e x)
  have hT : ∀ w, T w = fun x => w (e x) := fun w => rfl
  exact hF.comp (fun w _ => T.analyticAt w) (fun w hw x => by
    simpa using hw (e x))

theorem cutoff_integral_translate (hMN : M ∣ N) (σ : MacIdx d N M ≃ MacIdx d N M)
    (hσ : ∀ z i, (σ z i : ℕ) = ((z i : ℕ) + p) % macK N M)
    (e : L1Torus d N ≃ L1Torus d N) (he : ∀ x i, e x i = x i + ((M * p : ℕ) : ZMod N))
    (T : (L1Torus d N → ℝ) ≃ᵐ (L1Torus d N → ℝ)) (hT : ∀ ψ x, T ψ x = ψ (e.symm x))
    (γ : Measure (L1Torus d N → ℝ)) (ρ : ℝ) (F : (L1Torus d N → ℂ) → ℂ) (v a : ℝ)
    (s : MacIdx d N M → ℂ) :
    ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, taggedCfin d L N k M v a s (e x) y * ((ψ y : ℝ) : ℂ)) ∂(γ.map T) =
      ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, taggedCfin d L N k M v a (s ∘ σ) x y * ((ψ y : ℝ) : ℂ)) ∂γ := by
  have h := integral_box_map (ι := L1Torus d N) e T hT γ ρ
    (fun ψ => F (fun x => ∑ y, taggedCfin d L N k M v a s (e x) y * ((ψ y : ℝ) : ℂ)))
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_))
  dsimp only
  refine congrArg F (funext fun x => ?_)
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h1 := congrFun (congrFun (taggedCfin_translate (L := L) (k := k) hMN σ hσ e he v a s) x) y
  rw [hT, Equiv.symm_apply_apply]
  exact congrArg (· * _) h1

/-- **The coefficients of the cutoff interaction of the final operators on two tori, for supports in
a two-sided box.**  This is `final_coef_cutoffInteraction_close_twoTorus_unif` for a support whose
cells are, after the cyclic shift by `p` cells in every coordinate, in the window of indices
`[4, J]`; `f` identifies the two tori by the residues of the shifted coordinates and `e` is the
identity on the shifted indices `≤ J + 4`. -/
theorem final_coef_cutoffInteraction_close_twoTorus_box {d M L : ℕ} [NeZero L] (hd : 0 < d)
    (hM : 0 < M) {κ : ℝ}
    (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) (nC : ℕ) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      M ∣ N → M ∣ N' → ∀ {p : ℕ},
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * p : ℕ) : ZMod N') =
        ((((x μ + ((M * p : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + p) % macK N M ≤ J + 4 →
        ((e z i : ℕ) + p) % macK N' M = ((z i : ℕ) + p) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ ((z i : ℕ) + p) % macK N M ∧ ((z i : ℕ) + p) % macK N M ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
      0 ≤ ρ →
      γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ < RF →
      ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
      AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
      AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
      Measurable F → Measurable F' →
      (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
        (∀ x, x ∉ macRegion d N M C → w x = 0) →
        (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
      Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
          (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
        Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
          (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
      ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
        coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
          F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
          (C.image e)‖ ≤
        Lip * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) *
          (P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) /
            Real.sqrt (finalGap d L)) * ρ) *
          (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card := by
  obtain ⟨P, C₀, c₀, hP0, hC₀, hc₀, hmain⟩ :=
    final_coef_cutoffInteraction_close_twoTorus_unif (L := L) hd hM hκ hMB hMκ nC
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro k hk J N N' _ _ hN hN' hMN hMN' p f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass γ γ' ρ RF B'
    Lip hρ hγfin hγfin' hBR F F' hFan hFB hFan' hFB' hFm hFm' hFclose hγ
  obtain ⟨σ, hσ⟩ := exists_cellShift (N := N) (M := M) d p
  obtain ⟨σ', hσ'⟩ := exists_cellShift (N := N') (M := M) d p
  obtain ⟨e1, he1⟩ := exists_translate (N := N) (d := d) (fun _ => ((M * p : ℕ) : ZMod N))
  obtain ⟨e1', he1'⟩ := exists_translate (N := N') (d := d) (fun _ => ((M * p : ℕ) : ZMod N'))
  obtain ⟨T, hT⟩ := exists_fieldEquiv e1
  obtain ⟨T', hT'⟩ := exists_fieldEquiv e1'
  have hκ1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  have hemap := cellMap_translate σ σ' hσ hσ' he
  have hcard : (C.map σ.toEmbedding).card ≤ nC := by rw [Finset.card_map]; exact hCc
  have hCw := window_translate σ hσ hC
  have himg := image_translate σ σ' e C
  obtain ⟨hJan, -⟩ := cutoffInteraction_final (N₀ := N) (k := k) (L := L) (v := v) (a := a) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hγfin hBR hFan hFB
  obtain ⟨hJan', -⟩ := cutoffInteraction_final (N₀ := N') (k := k) (L := L) (v := v) (a := a) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hγfin' hBR hFan' hFB'
  have hJanb : AnalyticOnNhd ℂ (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
      F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (Metric.ball 0 (Real.exp κ)) := by
    rw [← polydisc_eq_ball (Real.exp_pos κ)]; exact hJan
  have hJanb' : AnalyticOnNhd ℂ (fun s : MacIdx d N' M → ℂ => ∫ ψ in {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ},
      F' (fun x => ∑ y, taggedCfin d L N' k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ')
      (Metric.ball 0 (Real.exp κ)) := by
    rw [← polydisc_eq_ball (Real.exp_pos κ)]; exact hJan'
  have key : ∀ z : L1Torus d N, f (e1.symm z) = e1'.symm
      ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) z) := by
    intro z
    refine (Equiv.eq_symm_apply e1').2 ?_
    funext μ
    have hz : (e1.symm z) μ + ((M * p : ℕ) : ZMod N) = z μ := by
      have := he1 (e1.symm z) μ
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    exact ((he1' (f (e1.symm z)) μ).trans ((hf (e1.symm z) μ).trans
      (congrArg (fun w : ZMod N => (((w.val : ℕ)) : ZMod N')) hz)))
  have hmapS : (γ.map T) {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} =
      γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} := by
    rw [Measure.map_apply T.measurable (measurableSet_box ρ), fieldEquiv_preimage_box e1 T hT ρ]
  have hmapS' : (γ'.map T') {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} =
      γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} := by
    rw [Measure.map_apply T'.measurable (measurableSet_box ρ), fieldEquiv_preimage_box e1' T' hT' ρ]
  have hFB1 : ∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F (fun x => w (e1 x))‖ ≤ B' :=
    fun w hw => hFB _ (fun x => by simpa using hw (e1 x))
  have hFB1' : ∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' (fun x => w (e1' x))‖ ≤ B' :=
    fun w hw => hFB' _ (fun x => by simpa using hw (e1' x))
  have hFclose1 : ∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
      (∀ x, x ∉ macRegion d N M (C.map σ.toEmbedding) → w x = 0) →
      (∀ x', x' ∉ macRegion d N' M ((C.map σ.toEmbedding).image (fun w => σ' (e (σ.symm w)))) →
        w' x' = 0) →
      (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ) →
      (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
      (∀ x ∈ macRegion d N M (C.map σ.toEmbedding),
        ‖w' ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) x) - w x‖ ≤ η) →
      ‖F' (fun x => w' (e1' x)) - F (fun x => w (e1 x))‖ ≤ Lip * η := by
    intro w w' hw hw' hbw hbw' η hη hcl
    refine hFclose (fun x => w (e1 x)) (fun x' => w' (e1' x')) (fun x hx => hw _ ?_)
      (fun x' hx' => hw' _ ?_) (fun x => hbw _) (fun x' => hbw' _) η hη (fun x hx => ?_)
    · rwa [mem_macRegion_translate hMN σ hσ e1 he1]
    · rw [himg, mem_macRegion_translate hMN' σ' hσ' e1' he1']; exact hx'
    · have := hcl (e1 x) ((mem_macRegion_translate hMN σ hσ e1 he1 C x).2 hx)
      have h2 : e1' (f x) = (fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) (e1 x) := by
        exact (Equiv.eq_symm_apply e1').1
          ((congrArg f (e1.symm_apply_apply x).symm).trans (key (e1 x)))
      rw [h2]; exact this
  have hγ1 : Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M (C.map σ.toEmbedding))) => ψ q)
        ((γ.map T).restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
      Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M (C.map σ.toEmbedding))) =>
          ψ' ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) q))
        ((γ'.map T').restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) := by
    obtain ⟨Ψ, hΨm, hΨ1, hΨ2⟩ : ∃ Ψ : (↥(macRegion d N M C) → ℝ) →
        (↥(macRegion d N M (C.map σ.toEmbedding)) → ℝ), Measurable Ψ ∧
        (∀ ψ : L1Torus d N → ℝ, (fun q : ↥(macRegion d N M (C.map σ.toEmbedding)) => T ψ q) =
          Ψ (fun q0 : ↥(macRegion d N M C) => ψ q0)) ∧
        (∀ ψ' : L1Torus d N' → ℝ,
          (fun q : ↥(macRegion d N M (C.map σ.toEmbedding)) => T' ψ'
            ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) q)) =
          Ψ (fun q0 : ↥(macRegion d N M C) => ψ' (f q0))) := by
      have hmem : ∀ q : ↥(macRegion d N M (C.map σ.toEmbedding)),
          e1.symm q.1 ∈ macRegion d N M C := fun q =>
        (mem_macRegion_translate hMN σ hσ e1 he1 C (e1.symm q.1)).1
          (by rw [Equiv.apply_symm_apply]; exact q.2)
      refine ⟨fun g q => g ⟨e1.symm q.1, hmem q⟩, ?_, fun ψ => ?_, fun ψ' => ?_⟩
      · exact Measurable.of_eval fun q => measurable_pi_apply _
      · funext q
        exact hT ψ q.1
      · funext q
        exact (hT' ψ' _).trans (congrArg ψ' (key q.1).symm)
    have hS := fieldEquiv_preimage_box e1 T hT ρ
    have hS' := fieldEquiv_preimage_box e1' T' hT' ρ
    have hRm : Measurable (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M (C.map σ.toEmbedding))) => ψ q) :=
      Measurable.of_eval fun q => measurable_pi_apply _
    have hRm' : Measurable (fun (ψ' : L1Torus d N' → ℝ)
        (q : ↥(macRegion d N M (C.map σ.toEmbedding))) =>
          ψ' ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) q)) :=
      Measurable.of_eval fun q => measurable_pi_apply _
    rw [Measure.restrict_map T.measurable (measurableSet_box ρ), hS,
      Measure.restrict_map T'.measurable (measurableSet_box ρ), hS',
      Measure.map_map hRm T.measurable, Measure.map_map hRm' T'.measurable]
    have hc1 : (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M (C.map σ.toEmbedding))) => ψ q) ∘ T =
        Ψ ∘ (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q) :=
      funext fun ψ => hΨ1 ψ
    have hc2 : (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M (C.map σ.toEmbedding))) =>
          ψ' ((fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) q)) ∘ T' =
        Ψ ∘ (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q)) :=
      funext fun ψ' => hΨ2 ψ'
    rw [hc1, hc2, ← Measure.map_map hΨm (Measurable.of_eval fun q => measurable_pi_apply _),
      ← Measure.map_map hΨm (Measurable.of_eval fun q => measurable_pi_apply _), hγ]
  have hcoefs := hmain hk hN hN' (f := fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N'))
    (fun _ _ => rfl) (e := fun w => σ' (e (σ.symm w))) hemap hcard hCw hv0 hv1 ha1 ha2 hmass
    (γ := γ.map T) (γ' := γ'.map T') (ρ := ρ) (RF := RF) (B' := B') (Lip := Lip) hρ
    (by rw [hmapS]; exact hγfin) (by rw [hmapS']; exact hγfin') hBR
    (F := fun w => F (fun x => w (e1 x))) (F' := fun w => F' (fun x => w (e1' x)))
    (analyticOnNhd_polydisc_comp_equiv e1 hFan) hFB1
    (analyticOnNhd_polydisc_comp_equiv e1' hFan') hFB1'
    (hFm.comp (Measurable.of_eval fun x => measurable_pi_apply (e1 x)))
    (hFm'.comp (Measurable.of_eval fun x => measurable_pi_apply (e1' x))) hFclose1 hγ1
  have h1 : coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => ∑ y, taggedCfin d L N k M v a s (e1 x) y * ((ψ y : ℝ) : ℂ)) ∂(γ.map T))
        (C.map σ.toEmbedding) =
      coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C := by
    rw [← coef_comp_perm σ hκ1 hJanb C]
    exact congrArg (fun g => coef g (C.map σ.toEmbedding))
      (funext fun s => cutoff_integral_translate (L := L) (k := k) hMN σ hσ e1 he1 T hT γ ρ F v a s)
  have h2 : coef (fun s : MacIdx d N' M → ℂ => ∫ ψ in {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ},
        F' (fun x => ∑ y, taggedCfin d L N' k M v a s (e1' x) y * ((ψ y : ℝ) : ℂ)) ∂(γ'.map T'))
        ((C.image e).map σ'.toEmbedding) =
      coef (fun s : MacIdx d N' M → ℂ => ∫ ψ in {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ},
          F' (fun x => ∑ y, taggedCfin d L N' k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ')
        (C.image e) := by
    rw [← coef_comp_perm σ' hκ1 hJanb' (C.image e)]
    exact congrArg (fun g => coef g ((C.image e).map σ'.toEmbedding))
      (funext fun s => cutoff_integral_translate (L := L) (k := k) hMN' σ' hσ' e1' he1' T' hT' γ' ρ F' v a s)
  rw [himg, Finset.card_map, hmapS] at hcoefs
  rw [← h1, ← h2]
  exact hcoefs

end Cutoff

section QuarterBox

open MeasureTheory Set Balaban.Localization Balaban.Analysis

theorem box_window {K m z : ℕ} (hz : z < K) (h : z ≤ m ∨ K - m ≤ z) (hK : 2 * m + 5 ≤ K) :
    4 ≤ (z + (m + 4)) % K ∧ (z + (m + 4)) % K ≤ 2 * m + 4 := by
  rcases h with h | h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · have h1 : z + (m + 4) = (z + (m + 4) - K) + K := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem quarter_exponent {N N' M m t : ℕ} [NeZero N] (hMN : M ∣ N) (hN : N ≤ N')
    (hbox : 4 * (m + t) ≤ macK N M) :
    (M : ℝ) * (2 * (t : ℝ) - 7) ≤
      ((min N N' : ℕ) : ℝ) / 2 - (((2 * m + 4 + 3) * M : ℕ) : ℝ) := by
  obtain ⟨K, hK⟩ := hMN
  have hM : 0 < M := Nat.pos_of_dvd_of_pos ⟨K, hK⟩ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hKk : macK N M = K := by
    rw [macK_eq_div_of_dvd ⟨K, hK⟩, hK, Nat.mul_div_cancel_left _ hM]
  rw [hKk] at hbox
  rw [min_eq_left hN, hK]
  have h1 : (4 : ℝ) * ((m : ℝ) + t) ≤ K := by exact_mod_cast hbox
  have h2 : (0 : ℝ) ≤ M := by positivity
  push_cast
  nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]

/-- **The localized coefficients of the logarithm of the perturbed defect on the quarter box
(W837, leaf 2).**  The support `C` has all its cell indices, in every coordinate, within `m` cells
of the origin on either side (`z i ≤ m` or `z i ≥ K - m`, `K = macK N M` the number of cells per
side), and the quarter box `4 m < K` has margin `t ≥ 5` cells: `4 (m + t) ≤ K`.  The tori `N ≤ N'`
(both multiples of `M`) are identified by the residues of the coordinates shifted by `(m + 4) M`.
The two coefficients differ by at most `P (C₀ e^{-c₀ M (2t - 7)} + εE) / (e^κ - 1)^{|C|}`, with
`P, C₀, c₀` independent of the scale `k ≥ 1`, of the tori, of `m`, `t` and of `C`. -/
theorem finalCoef_logdet_close_quarterBox {d M L : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {N N' : ℕ} [NeZero N] [NeZero N'], M ∣ N → M ∣ N' → N ≤ N' →
      ∀ {m t : ℕ}, 5 ≤ t → 4 * (m + t) ≤ macK N M →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod N') =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK N' M = ((z i : ℕ) + (m + 4)) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ)) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {s : ℝ}, 0 ≤ s →
      ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
      WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
      (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖E x y - E' (f x) (f y)‖ ≤ εE) →
      ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
      ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
      ell 0 = 0 → ell' 0 = 0 →
      (∀ s' ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
        (1 - taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) s -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) s)) s').det =
          Complex.exp (ell s')) →
      (∀ s' ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) s -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) s)) s').det =
          Complex.exp (ell' s')) →
      ‖coef ell C - coef ell' (C.image e)‖ ≤
        P * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) + εE) /
          (Real.exp κ - 1) ^ C.card := by
  obtain ⟨P, C₀, c₀, hP0, hC₀, hc₀, hmain⟩ :=
    final_coef_logdet_close_twoTorus_box (L := L) hd hM hκ hMB hMκ hrE hη0 hη nC
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro k hk N N' _ _ hMN hMN' hNN m t ht hbox f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass s hs E E'
    hE hE' εE hεE hEcl ρ ρ' hρ hρ' ell ell' hell hell' h0 h0' hdet hdet'
  have hK : macK N M = N / M := macK_eq_div_of_dvd hMN
  have hMpos : 0 < M := hM
  have hKN : N = M * macK N M := by
    rw [hK]; exact (Nat.mul_div_cancel' hMN).symm
  have hKm : 2 * m + 5 ≤ macK N M := by omega
  have hN1 : 2 * ((2 * m + 4) + 6) * M ≤ N := by
    have : 2 * ((2 * m + 4) + 6) ≤ macK N M := by omega
    calc 2 * ((2 * m + 4) + 6) * M ≤ macK N M * M := Nat.mul_le_mul_right _ this
      _ = N := by rw [mul_comm, ← hKN]
  have hN2 : 2 * ((2 * m + 4) + 6) * M ≤ N' := le_trans hN1 hNN
  have hCw : ∀ z ∈ C, ∀ i, 4 ≤ ((z i : ℕ) + (m + 4)) % macK N M ∧
      ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 4 := fun z hz i =>
    box_window (z i).isLt (hC z hz i) hKm
  have key := hmain hk hN1 hN2 hMN hMN' (p := m + 4) hf
    (fun z i hz => he z i (by omega)) hCc hCw hv0 hv1 ha1 ha2 hmass hs hE hE' hεE hEcl hρ hρ' hell
    hell' h0 h0' hdet hdet'
  refine key.trans ?_
  have hexp := quarter_exponent hMN hNN hbox
  have hle : Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((2 * m + 4 + 3) * M : ℕ) : ℝ))) ≤
      Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) :=
    Real.exp_le_exp.2 (by nlinarith [hc₀, hexp])
  have hden : 0 < (Real.exp κ - 1) ^ C.card := by
    have : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
    exact pow_pos (by linarith) _
  refine div_le_div_of_nonneg_right ?_ hden.le
  exact mul_le_mul_of_nonneg_left (by gcongr) hP0

/-- **The coefficients of the cutoff interaction on the quarter box (W837, leaf 2).**  Same
geometry as `finalCoef_logdet_close_quarterBox`: the support is within `m` cells of the origin,
`4 (m + t) ≤ K`, `t ≥ 5`, `N ≤ N'`; the entries of the Stieltjes families are within
`P C₀ e^{-c₀ M (2t - 7)} / √g`, uniformly in the scale `k ≥ 1`. -/
theorem finalCoef_cutoff_close_quarterBox {d M L : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) (nC : ℕ) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {N N' : ℕ} [NeZero N] [NeZero N'], M ∣ N → M ∣ N' → N ≤ N' →
      ∀ {m t : ℕ}, 5 ≤ t → 4 * (m + t) ≤ macK N M →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod N') =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK N' M = ((z i : ℕ) + (m + 4)) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ)) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
      0 ≤ ρ →
      γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ < RF →
      ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
      AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
      AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
      Measurable F → Measurable F' →
      (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
        (∀ x, x ∉ macRegion d N M C → w x = 0) →
        (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
      Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
          (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
        Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
          (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
      ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
        coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
          F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
          (C.image e)‖ ≤
        Lip * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) *
          (P * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
            Real.sqrt (finalGap d L)) * ρ) *
          (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card := by
  obtain ⟨P, C₀, c₀, hP0, hC₀, hc₀, hmain⟩ :=
    final_coef_cutoffInteraction_close_twoTorus_box (L := L) hd hM hκ hMB hMκ nC
  refine ⟨P, C₀, c₀, hP0, hC₀, hc₀, ?_⟩
  intro k hk N N' _ _ hMN hMN' hNN m t ht hbox f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass γ γ' ρ RF B'
    Lip hρ hγfin hγfin' hBR F F' hFan hFB hFan' hFB' hFm hFm' hFclose hγ
  have hK : macK N M = N / M := macK_eq_div_of_dvd hMN
  have hKN : N = M * macK N M := by
    rw [hK]; exact (Nat.mul_div_cancel' hMN).symm
  have hKm : 2 * m + 5 ≤ macK N M := by omega
  have hN1 : 2 * ((2 * m + 4) + 6) * M ≤ N := by
    have : 2 * ((2 * m + 4) + 6) ≤ macK N M := by omega
    calc 2 * ((2 * m + 4) + 6) * M ≤ macK N M * M := Nat.mul_le_mul_right _ this
      _ = N := by rw [mul_comm, ← hKN]
  have hN2 : 2 * ((2 * m + 4) + 6) * M ≤ N' := le_trans hN1 hNN
  have hCw : ∀ z ∈ C, ∀ i, 4 ≤ ((z i : ℕ) + (m + 4)) % macK N M ∧
      ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 4 := fun z hz i =>
    box_window (z i).isLt (hC z hz i) hKm
  have key := hmain hk hN1 hN2 hMN hMN' (p := m + 4) hf
    (fun z i hz => he z i (by omega)) hCc hCw hv0 hv1 ha1 ha2 hmass hρ hγfin hγfin' hBR hFan hFB
    hFan' hFB' hFm hFm' hFclose hγ
  refine key.trans ?_
  have hexp := quarter_exponent hMN hNN hbox
  have hle : Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((2 * m + 4 + 3) * M : ℕ) : ℝ))) ≤
      Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) :=
    Real.exp_le_exp.2 (by nlinarith [hc₀, hexp])
  have hBc0 : 0 ≤ 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L) := by
    have : 0 ≤ ballConst d (pdEps d L / 2) :=
      ballConst_decay_nonneg (by have := pdEps_pos (d := d) (L := L) hd; positivity)
    positivity
  have hLip : 0 ≤ Lip := by
    have := hFclose 0 0 (fun _ _ => rfl) (fun _ _ => rfl) (fun x => by simpa using mul_nonneg hBc0 hρ)
      (fun x => by simpa using mul_nonneg hBc0 hρ) 1 zero_le_one (fun x _ => by simp)
    exact le_trans (norm_nonneg _) (by simpa using this)
  have hden : 0 < (Real.exp κ - 1) ^ C.card := by
    have : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
    exact pow_pos (by linarith) _
  have hg : 0 < Real.sqrt (finalGap d L) := by
    have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    exact Real.sqrt_pos.2 (finalGap_pos (d := d) hL)
  refine div_le_div_of_nonneg_right ?_ hden.le
  refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
  refine mul_le_mul_of_nonneg_left ?_ hLip
  refine mul_le_mul_of_nonneg_right ?_ hρ
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine div_le_div_of_nonneg_right ?_ hg.le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hC₀.le) hP0

/-- **The two last-integral coefficient families on the quarter box, with common constants
(W837, leaf 2).**  The conjunction of `finalCoef_logdet_close_quarterBox` and
`finalCoef_cutoff_close_quarterBox`: for a support `C` within `m` cells of the origin in every
coordinate, `4 (m + t) ≤ K`, `t ≥ 5`, the coefficients of the logarithm of the perturbed defect, and
those of the cutoff interaction, of the final operators on the tori `N ≤ N'` (multiples of `M`)
differ by at most the stated multiples of `e^{-c₀ M (2t - 7)}`, with `P, C₀, c₀` independent of the
scale `k ≥ 1`, of the tori, of `m`, `t` and of `C`. -/
theorem finalCoef_close_quarterBox {d M L : ℕ} [NeZero L] (hd : 0 < d) (hM : 0 < M)
    {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) :
    ∃ P C₀ c₀ : ℝ, 0 ≤ P ∧ 0 < C₀ ∧ 0 < c₀ ∧ ∀ {k : ℕ}, 1 ≤ k →
      ∀ {N N' : ℕ} [NeZero N] [NeZero N'], M ∣ N → M ∣ N' → N ≤ N' →
      ∀ {m t : ℕ}, 5 ≤ t → 4 * (m + t) ≤ macK N M →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ + ((M * (m + 4) : ℕ) : ZMod N') =
        ((((x μ + ((M * (m + 4) : ℕ) : ZMod N)).val : ℕ)) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, ((z i : ℕ) + (m + 4)) % macK N M ≤ 2 * m + 8 →
        ((e z i : ℕ) + (m + 4)) % macK N' M = ((z i : ℕ) + (m + 4)) % macK N M) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, (z i : ℕ) ≤ m ∨ macK N M - m ≤ (z i : ℕ)) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ((∀ {s : ℝ}, 0 ≤ s →
        ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
        WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
        (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
          ‖E x y - E' (f x) (f y)‖ ≤ εE) →
        ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
        ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
        AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
        ell 0 = 0 → ell' 0 = 0 →
        (∀ s' ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
          (1 - taggedMat Finset.univ (macTags d N M)
            (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
                (fun u => ((macChi d N M z u : ℝ) : ℂ)) s -
              E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
                boxG (finalOp d L N k v a) (macBoxF d N M z) s)) s').det =
            Complex.exp (ell s')) →
        (∀ s' ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
          (1 - taggedMat Finset.univ (macTags d N' M)
            (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
                (fun u => ((macChi d N' M z u : ℝ) : ℂ)) s -
              E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
                boxG (finalOp d L N' k v a) (macBoxF d N' M z) s)) s').det =
            Complex.exp (ell' s')) →
        ‖coef ell C - coef ell' (C.image e)‖ ≤
          P * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7))) + εE) /
            (Real.exp κ - 1) ^ C.card) ∧
       (∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
        0 ≤ ρ →
        γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
        γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
        (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ < RF →
        ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
        AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
        (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
        AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
        (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
        Measurable F → Measurable F' →
        (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
          (∀ x, x ∉ macRegion d N M C → w x = 0) →
          (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
          (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
            Real.sqrt (finalGap d L)) * ρ) →
          (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
            Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
          (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
        Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
            (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
          Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
            (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
        ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
            F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
          coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
            F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
            (C.image e)‖ ≤
          Lip * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) *
            (P * (C₀ * Real.exp (-c₀ * ((M : ℝ) * (2 * (t : ℝ) - 7)))) /
              Real.sqrt (finalGap d L)) * ρ) *
            (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card))
 := by
  obtain ⟨P₁, C₁, c₁, hP₁, hC₁, hc₁, h₁⟩ :=
    finalCoef_logdet_close_quarterBox (L := L) hd hM (by linarith : 0 < κ) hMB hMκ hrE hη0 hη nC
  obtain ⟨P₂, C₂, c₂, hP₂, hC₂, hc₂, h₂⟩ :=
    finalCoef_cutoff_close_quarterBox (L := L) hd hM hκ hMB hMκ nC
  refine ⟨max P₁ P₂, max C₁ C₂, min c₁ c₂, le_trans hP₁ (le_max_left _ _),
    lt_of_lt_of_le hC₁ (le_max_left _ _), lt_min hc₁ hc₂, ?_⟩
  intro k hk N N' _ _ hMN hMN' hNN m t ht hbox f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass
  have hy : (0 : ℝ) ≤ (M : ℝ) * (2 * (t : ℝ) - 7) := by
    have : (5 : ℝ) ≤ t := by exact_mod_cast ht
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith
  have hmono : ∀ {Q₁ Q C₁' C' c₁' c' : ℝ}, 0 ≤ Q₁ → Q₁ ≤ Q → 0 ≤ C₁' → C₁' ≤ C' → c' ≤ c₁' →
      Q₁ * (C₁' * Real.exp (-c₁' * ((M : ℝ) * (2 * (t : ℝ) - 7)))) ≤
        Q * (C' * Real.exp (-c' * ((M : ℝ) * (2 * (t : ℝ) - 7)))) := by
    intro Q₁ Q C₁' C' c₁' c' hQ₁ hQ hC₁' hC' hc
    have hexp : Real.exp (-c₁' * ((M : ℝ) * (2 * (t : ℝ) - 7))) ≤
        Real.exp (-c' * ((M : ℝ) * (2 * (t : ℝ) - 7))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hQ0 : 0 ≤ Q := le_trans hQ₁ hQ
    exact mul_le_mul hQ (mul_le_mul hC' hexp (Real.exp_pos _).le (le_trans hC₁' hC'))
      (mul_nonneg hC₁' (Real.exp_pos _).le) hQ0
  have hmono' : ∀ {εE : ℝ}, 0 ≤ εE →
      P₁ * (C₁ * Real.exp (-c₁ * ((M : ℝ) * (2 * (t : ℝ) - 7))) + εE) ≤
        max P₁ P₂ * (max C₁ C₂ * Real.exp (-min c₁ c₂ * ((M : ℝ) * (2 * (t : ℝ) - 7))) + εE) := by
    intro εE hεE
    have := hmono hP₁ (le_max_left P₁ P₂) hC₁.le (le_max_left C₁ C₂) (min_le_left c₁ c₂)
    have h2 : 0 ≤ max P₁ P₂ := le_trans hP₁ (le_max_left _ _)
    nlinarith [mul_nonneg hP₁ hεE, mul_nonneg h2 hεE, mul_le_mul_of_nonneg_right (le_max_left P₁ P₂) hεE]
  refine ⟨?_, ?_⟩
  · intro s hs E E' hE hE' εE hεE hEcl ρ ρ' hρ hρ' ell ell' hell hell' h0 h0' hdet hdet'
    have key := h₁ hk hMN hMN' hNN ht hbox hf he hCc hC hv0 hv1 ha1 ha2 hmass hs hE hE' hεE hEcl hρ
      hρ' hell hell' h0 h0' hdet hdet'
    refine key.trans ?_
    have hden : 0 < (Real.exp κ - 1) ^ C.card := by
      have : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
      exact pow_pos (by linarith) _
    exact div_le_div_of_nonneg_right (hmono' hεE) hden.le
  · intro γ γ' ρ RF B' Lip hρ hγfin hγfin' hBR F F' hFan hFB hFan' hFB' hFm hFm' hFclose hγ
    have key := h₂ hk hMN hMN' hNN ht hbox hf he hCc hC hv0 hv1 ha1 ha2 hmass hρ hγfin hγfin' hBR
      hFan hFB hFan' hFB' hFm hFm' hFclose hγ
    refine key.trans ?_
    have hBc0 : 0 ≤ 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
      have : 0 ≤ ballConst d (pdEps d L / 2) :=
        ballConst_decay_nonneg (by have := pdEps_pos (d := d) (L := L) hd; positivity)
      positivity
    have hLip : 0 ≤ Lip := by
      have := hFclose 0 0 (fun _ _ => rfl) (fun _ _ => rfl)
        (fun x => by simpa using mul_nonneg hBc0 hρ)
        (fun x => by simpa using mul_nonneg hBc0 hρ) 1 zero_le_one (fun x _ => by simp)
      exact le_trans (norm_nonneg _) (by simpa using this)
    have hden : 0 < (Real.exp κ - 1) ^ C.card := by
      have : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
      exact pow_pos (by linarith) _
    have hg : 0 < Real.sqrt (finalGap d L) := by
      have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
      exact Real.sqrt_pos.2 (finalGap_pos (d := d) hL)
    refine div_le_div_of_nonneg_right ?_ hden.le
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    refine mul_le_mul_of_nonneg_left ?_ hLip
    refine mul_le_mul_of_nonneg_right ?_ hρ
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine div_le_div_of_nonneg_right ?_ hg.le
    exact hmono hP₂ (le_max_right P₁ P₂) hC₂.le (le_max_right C₁ C₂) (min_le_right c₁ c₂)

/-- The identification of the tori by the residues of the shifted coordinates exists. -/
theorem exists_residueMap_box {d N N' M p : ℕ} [NeZero N] [NeZero N'] :
    ∃ f : L1Torus d N → L1Torus d N', ∀ x μ, f x μ + ((M * p : ℕ) : ZMod N') =
      ((((x μ + ((M * p : ℕ) : ZMod N)).val : ℕ)) : ZMod N') :=
  ⟨fun x μ => ((((x μ + ((M * p : ℕ) : ZMod N)).val : ℕ)) : ZMod N') - ((M * p : ℕ) : ZMod N'),
    fun _ _ => sub_add_cancel _ _⟩

theorem macK_le_macK_of_dvd {N N' M : ℕ} [NeZero N] [NeZero N'] (hMN : M ∣ N) (hMN' : M ∣ N')
    (hNN : N ≤ N') : macK N M ≤ macK N' M := by
  rw [macK_eq_div_of_dvd hMN, macK_eq_div_of_dvd hMN']
  exact Nat.div_le_div_right hNN

/-- The cell map that is the identity on the shifted indices exists when `K ≤ K'`. -/
theorem exists_cellMap_box {d N N' M p : ℕ} [NeZero N] [NeZero N']
    (hKK : macK N M ≤ macK N' M) :
    ∃ e : MacIdx d N M → MacIdx d N' M, ∀ z i,
      ((e z i : ℕ) + p) % macK N' M = ((z i : ℕ) + p) % macK N M := by
  have hK : 0 < macK N M := macK_pos N M
  have hK' : 0 < macK N' M := macK_pos N' M
  refine ⟨fun z i => ⟨(((z i : ℕ) + p) % macK N M + (macK N' M - p % macK N' M)) % macK N' M,
    Nat.mod_lt _ hK'⟩, fun z i => ?_⟩
  show ((((z i : ℕ) + p) % macK N M + (macK N' M - p % macK N' M)) % macK N' M + p) %
    macK N' M = _
  set w := ((z i : ℕ) + p) % macK N M with hw
  have hwlt : w < macK N' M := lt_of_lt_of_le (Nat.mod_lt _ hK) hKK
  have hdiv := Nat.mod_add_div p (macK N' M)
  have hmod := Nat.mod_lt p hK'
  have h1 : w + (macK N' M - p % macK N' M) + p = w + macK N' M * (1 + p / macK N' M) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [Nat.mod_add_mod, h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hwlt]

end QuarterBox

end Balaban.Green


