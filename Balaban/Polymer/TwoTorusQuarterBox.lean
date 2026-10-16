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
  -- the transported cell map
  have hemap : ∀ z i, (z i : ℕ) ≤ J + 4 →
      (((fun w => σ' (e (σ.symm w))) z i : Fin (macK N' M)) : ℕ) = z i := by
    intro z i hz
    have hz' : (z i : ℕ) = (((σ.symm z) i : ℕ) + p) % macK N M := by
      have := hσ (σ.symm z) i
      rw [Equiv.apply_symm_apply] at this
      exact this
    show ((σ' (e (σ.symm z)) i : Fin (macK N' M)) : ℕ) = z i
    rw [hσ', he (σ.symm z) i (by rw [← hz']; exact hz), ← hz']
  have hcard : (C.map σ.toEmbedding).card ≤ nC := by rw [Finset.card_map]; exact hCc
  have hCw : ∀ z ∈ C.map σ.toEmbedding, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J := by
    intro z hz i
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.1 hz
    have := hC c hc i
    rw [Equiv.toEmbedding_apply, hσ]
    exact this
  have hf' : ∀ x μ, (fun (x : L1Torus d N) μ => ((((x μ).val : ℕ)) : ZMod N')) x μ =
      ((((x μ).val : ℕ)) : ZMod N') := fun _ _ => rfl
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
  have himg : (C.map σ.toEmbedding).image (fun w => σ' (e (σ.symm w))) =
      (C.image e).map σ'.toEmbedding := by
    ext w
    simp only [Finset.mem_image, Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨e c, ⟨c, hc, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨σ c, ⟨c, hc, rfl⟩, by simp⟩
  rw [himg, coef_comp_perm σ hρ1 hell, coef_comp_perm σ' hρ1' hell', Finset.card_map] at hcoefs
  exact hcoefs

end LogDet

end Final

end Balaban.Green
