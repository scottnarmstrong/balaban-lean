/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalDetRatio
public import Balaban.Polymer.TwoTorusEv

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant-ratio coefficients of the last integral on two tori (W791, FINALPHYS2 leaf E6)

Let `N` and `N'` be two torus sides and `M > 0` the scale of the macro cover
(`Green/FinalMacroCover`).  Both tori are cut into the cells `⌊v / M⌋` of the residues
`v = 0, …, N - 1`, the last cell of each coordinate being the long one.  The map
`f x = (x_μ.val)_μ` identifies the residues `0, …, min N N' - 1` of the two tori, and the map `e`
on the cells is the identity on the cell indices `≤ J + 4`.

**Margins.**  The support `C` consists of cells whose coordinate indices lie in `[4, J]`, and
`2 (J + 6) M ≤ N`, `2 (J + 6) M ≤ N'`.  Then `Y(C)`, the union of the boxes of `C`, lies in the
residues `(2M, (J + 3) M)` of every coordinate, so it stays at distance more than `2M` from the
origin (no wrap-around through `0`) and its diameter is below `(J + 3) M ≤ N / 2` (no winding).
In particular cells touching the last (long) cell of either torus play no role.

**Geometry (all exact).**
* `core_near`, `infDist_lt_iff_vals`, `infDist_lt_iff_transport`: for a point `x` of the window and
  a cell `w` with indices `≤ J + 4`, `dist(x, core_w) < r` (`r ≤ 2M`) is a statement about the
  residues of `x` only; hence `macPhi`, `macSum`, `macChi` correspond (`macChi_transport`) and the
  boxes correspond (`mem_macBox_transport`, `macBoxF_image`).
* `path_transport`, `tags_forward`, `tags_backward`: the path of two points of the window, the tag
  sets `macTags z x y` and the sets of tags that lie in `C` correspond under `e`.
* `macRegion_bijOn`: `f` is a bijection of `Y(C)` onto `Y(e C)`.

**Matrix part.**
* `boxG_transport`, `boxR_transport`, `rowmul_transport`: the box resolvent, the defect and the
  perturbed defect of a matrix read only the stated entries and are carried along an injective
  correspondence of the indices.
* `det_eq_of_bijOn`: a matrix `1 - T` with rows of `T` vanishing off `Y` has the determinant of its
  principal block.

**Result.**
* `taggedKE_entry_twoTorus`, `det_taggedKE_twoTorus`: the entries of the tagged defect
  `K_E(s)` with the boxes of `U`, and its determinant, correspond at parameters supported on `C`
  and on `e C` (equal along `e`) when `U`, `E` correspond on `Y(C)^2`.
* `coef_eq_of_agree_taggedKE_twoTorus`: `coef ell C = coef ell' (e C)` for analytic logarithms.
* `coef_detRatio_eq_twoTorus`: `coef ellE C - coef ell0 C = coef ellE' (e C) - coef ell0' (e C)`,
  the coefficients of the determinant ratio of `Green/FinalDetRatio`
  (`exists_det_ratio_localized`) on the two tori.  The matrices `U`, `U'` (the final operators)
  and `E`, `E'` enter only through their correspondence on `Y(C)^2` (`hU`, `hE`).
* `exists_cellMap`: the maps `e` exist.
-/

@[expose] public section

open Finset Matrix Balaban.Localization Balaban.Analysis

namespace Balaban.Green


section DetAlg
variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

theorem det_eq_det_submatrix_of_rows (A : Matrix X X ℂ) (Y : Finset X)
    (h : ∀ x, x ∉ Y → ∀ y, A x y = (1 : Matrix X X ℂ) x y) :
    A.det = (A.submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X))).det := by
  classical
  set e : {a // a ∈ Y} ⊕ {a // a ∉ Y} ≃ X := Equiv.sumCompl (· ∈ Y) with he
  have hblk : A.submatrix e e = Matrix.fromBlocks
      (A.submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)))
      (A.submatrix (fun q : Y => (q : X)) (fun q : {a // a ∉ Y} => (q : X))) 0 1 := by
    ext (i | i) (j | j)
    · simp [he]
    · simp [he]
    · simp only [Matrix.submatrix_apply, he, Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inl,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [h _ i.2]
      have : (i : X) ≠ (j : X) := fun hh => i.2 (hh ▸ j.2)
      simp [this]
    · simp only [Matrix.submatrix_apply, he, Equiv.sumCompl_apply_inr,
        Matrix.fromBlocks_apply₂₂]
      rw [h _ i.2]
      by_cases hij : i = j
      · subst hij; simp
      · have : (i : X) ≠ (j : X) := fun hh => hij (Subtype.ext hh)
        simp [this, hij]
  rw [← Matrix.det_submatrix_equiv_self e A, hblk, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_eq_of_bijOn (A : Matrix X X ℂ) (A' : Matrix X' X' ℂ) (Y : Finset X) (Y' : Finset X')
    (f : X → X') (hf : Set.BijOn f (Y : Set X) (Y' : Set X'))
    (hA : ∀ x, x ∉ Y → ∀ y, A x y = (1 : Matrix X X ℂ) x y)
    (hA' : ∀ x, x ∉ Y' → ∀ y, A' x y = (1 : Matrix X' X' ℂ) x y)
    (hAA' : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' (f x) (f y)) : A.det = A'.det := by
  rw [det_eq_det_submatrix_of_rows A Y hA, det_eq_det_submatrix_of_rows A' Y' hA']
  have hbij : Function.Bijective (fun q : Y => (⟨f q, hf.mapsTo q.2⟩ : Y')) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (hf.injOn a.2 b.2 this)
    · intro b
      obtain ⟨a, ha, hab⟩ := hf.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  set ε : Y ≃ Y' := Equiv.ofBijective _ hbij with hε
  have : A.submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)) =
      (A'.submatrix (fun q : Y' => (q : X')) (fun q : Y' => (q : X'))).submatrix ε ε := by
    ext i j
    exact hAA' i i.2 j j.2
  rw [this, Matrix.det_submatrix_equiv_self]

end DetAlg

section BoxTransport
variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

theorem boxH_apply (U : Matrix X X ℂ) (B : Finset X) (t : ℝ) (x y : X) :
    boxH U B t x y = (if x ∈ B then (1 : ℂ) else 0) * shiftMat U t x y * (if y ∈ B then (1 : ℂ) else 0)
      + ((1 : Matrix X X ℂ) x y - boxP B x y) := by
  unfold boxH
  rw [Matrix.add_apply, boxP_mul_mul_boxP_apply, Matrix.sub_apply]

/-- The `B`-block of `U + t`. -/
theorem boxH_submatrix (U : Matrix X X ℂ) (B : Finset X) (t : ℝ) (p q : B) :
    boxH U B t p q = shiftMat U t p q := by
  rw [boxH_apply]
  have hp := p.2
  have hq := q.2
  by_cases hpq : (p : X) = q
  · simp [boxP_apply, hpq, hq, Matrix.one_apply]
  · simp [boxP_apply, hpq, hp, hq]

theorem det_boxH (U : Matrix X X ℂ) (B : Finset X) (t : ℝ) :
    (boxH U B t).det =
      ((shiftMat U t).submatrix (fun q : B => (q : X)) (fun q : B => (q : X))).det := by
  classical
  have h := det_eq_det_submatrix_of_rows (boxH U B t) B (fun x hx y => by
    rw [boxH_apply]
    by_cases hxy : x = y
    · subst hxy; simp [hx, boxP_apply]
    · simp [hx, boxP_apply, hxy])
  rw [h]
  congr 1
  ext p q
  exact boxH_submatrix U B t p q


theorem boxG_apply_eq_inv (U : Matrix X X ℂ) (B : Finset X) (t : ℝ) {x y : X} (hx : x ∈ B)
    (hy : y ∈ B) :
    boxG U B t x y =
      (((shiftMat U t).submatrix (fun q : B => (q : X)) (fun q : B => (q : X)))⁻¹)
        ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  set HB := (shiftMat U t).submatrix (fun q : B => (q : X)) (fun q : B => (q : X)) with hHB
  by_cases hu : IsUnit (boxH U B t)
  · have hmul := boxH_mul_boxG hu
    have hGB : HB * (boxG U B t).submatrix (fun q : B => (q : X)) (fun q : B => (q : X)) = 1 := by
      ext p q
      have h1 := congrFun (congrFun hmul p) q
      rw [Matrix.mul_apply] at h1
      rw [Matrix.mul_apply]
      have hs : ∑ u, boxH U B t p u * boxG U B t u q =
          ∑ r : B, boxH U B t p r * boxG U B t r q := by
        rw [Finset.sum_coe_sort B (fun u => boxH U B t p u * boxG U B t u q)]
        symm
        refine Finset.sum_subset (Finset.subset_univ _) (fun u _ hu' => ?_)
        rw [boxH_apply]
        have hpu : (p : X) ≠ u := fun h => hu' (h ▸ p.2)
        simp [p.2, hu', hpu, boxP_apply]
      rw [hs] at h1
      have hbox : boxP B p q = (1 : Matrix B B ℂ) p q := by
        by_cases hpq : p = q
        · subst hpq; simp [boxP_apply, p.2]
        · have : (p : X) ≠ q := fun h => hpq (Subtype.ext h)
          simp [boxP_apply, this, hpq]
      rw [← hbox, ← h1]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [boxH_submatrix]
      rfl
    rw [Matrix.inv_eq_right_inv hGB]
    rfl
  · have hd : ¬ IsUnit (boxH U B t).det := fun h => hu ((Matrix.isUnit_iff_isUnit_det _).2 h)
    have h1 : boxG U B t = 0 := by
      unfold boxG
      rw [Matrix.nonsing_inv_apply_not_isUnit _ hd, zero_mul]
    have h2 : ¬ IsUnit HB.det := by rw [hHB, ← det_boxH]; exact hd
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, h1]
    rfl

theorem boxG_transport (f : X → X') {B : Finset X} {B' : Finset X'} (hB' : B' = B.image f)
    (hinj : Set.InjOn f (B : Set X)) {U : Matrix X X ℂ} {U' : Matrix X' X' ℂ} (t : ℝ)
    (hU : ∀ x ∈ B, ∀ y ∈ B, U x y = U' (f x) (f y)) {x y : X} (hx : x ∈ B) (hy : y ∈ B) :
    boxG U B t x y = boxG U' B' t (f x) (f y) := by
  classical
  subst hB'
  have hfx : f x ∈ B.image f := Finset.mem_image_of_mem f hx
  have hfy : f y ∈ B.image f := Finset.mem_image_of_mem f hy
  rw [boxG_apply_eq_inv U B t hx hy, boxG_apply_eq_inv U' (B.image f) t hfx hfy]
  have hbij : Function.Bijective
      (fun q : B => (⟨f q, Finset.mem_image_of_mem f q.2⟩ : B.image f)) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (hinj a.2 b.2 this)
    · intro b
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 b.2
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  set ε : B ≃ B.image f := Equiv.ofBijective _ hbij with hε
  have hsub : (shiftMat U t).submatrix (fun q : B => (q : X)) (fun q : B => (q : X)) =
      ((shiftMat U' t).submatrix (fun q : B.image f => (q : X')) (fun q : B.image f => (q : X'))).submatrix
        ε ε := by
    ext p q
    simp only [Matrix.submatrix_apply, shiftMat, Matrix.add_apply, Matrix.smul_apply, hε,
      Equiv.ofBijective_apply, hU p p.2 q q.2, Matrix.one_apply]
    have : ((p : X) = q) ↔ (f p = f q) := ⟨fun h => by rw [h], fun h => hinj p.2 q.2 h⟩
    simp only [this]
  rw [hsub, Matrix.inv_submatrix_equiv]
  rfl

theorem rowmul_transport (f : X → X') {Y B : Finset X} (hB : B ⊆ Y) (hinj : Set.InjOn f (Y : Set X))
    {U : Matrix X X ℂ} {U' : Matrix X' X' ℂ} (t : ℝ)
    (hU : ∀ x ∈ Y, ∀ y ∈ Y, U x y = U' (f x) (f y)) {c : X → ℂ} {c' : X' → ℂ}
    (hc : ∀ u, c u ≠ 0 → u ∈ B) (hc' : ∀ u, c' u ≠ 0 → u ∈ B.image f)
    (hcY : ∀ u ∈ Y, c u = c' (f u)) {A : Matrix X X ℂ} {A' : Matrix X' X' ℂ}
    (hA : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' (f x) (f y)) {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    (A * (Matrix.diagonal c * boxG U B t)) x y =
      (A' * (Matrix.diagonal c' * boxG U' (B.image f) t)) (f x) (f y) := by
  classical
  have hBinj : Set.InjOn f (B : Set X) := hinj.mono (by exact_mod_cast hB)
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  have hL : ∑ u, A x u * (c u * boxG U B t u y) = ∑ u ∈ B, A x u * (c u * boxG U B t u y) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => ?_)
    have : c u = 0 := by
      by_contra hne
      exact hu (hc u hne)
    simp [this]
  have hR : ∑ u', A' (f x) u' * (c' u' * boxG U' (B.image f) t u' (f y)) =
      ∑ u' ∈ B.image f, A' (f x) u' * (c' u' * boxG U' (B.image f) t u' (f y)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => ?_)
    have : c' u = 0 := by
      by_contra hne
      exact hu (hc' u hne)
    simp [this]
  rw [hL, hR, Finset.sum_image hBinj]
  refine Finset.sum_congr rfl fun u hu => ?_
  have huY : u ∈ Y := hB hu
  rw [hA x hx u huY, hcY u huY]
  congr 2
  by_cases hyB : y ∈ B
  · exact boxG_transport f rfl hBinj t (fun a ha b hb => hU a (hB ha) b (hB hb)) hu hyB
  · rw [boxG_apply_of_not_mem hyB]
    refine (boxG_apply_of_not_mem ?_).symm
    intro hmem
    obtain ⟨b, hb, hbf⟩ := Finset.mem_image.1 hmem
    exact hyB (by rw [← hinj (hB hb) hy hbf]; exact hb)

theorem boxR_transport (f : X → X') {Y B : Finset X} (hB : B ⊆ Y) (hinj : Set.InjOn f (Y : Set X))
    {U : Matrix X X ℂ} {U' : Matrix X' X' ℂ} (t : ℝ)
    (hU : ∀ x ∈ Y, ∀ y ∈ Y, U x y = U' (f x) (f y)) {c : X → ℂ} {c' : X' → ℂ}
    (hc : ∀ u, c u ≠ 0 → u ∈ B) (hc' : ∀ u, c' u ≠ 0 → u ∈ B.image f)
    (hcY : ∀ u ∈ Y, c u = c' (f u)) {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    boxR U B c t x y = boxR U' (B.image f) c' t (f x) (f y) := by
  classical
  unfold boxR
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 := rowmul_transport f hB hinj t hU hc hc' hcY
    (A := shiftMat U t) (A' := shiftMat U' t) (fun a ha b hb => by
      simp only [shiftMat, Matrix.add_apply, Matrix.smul_apply, hU a ha b hb, Matrix.one_apply]
      have : (a = b) ↔ (f a = f b) := ⟨fun h => by rw [h], fun h => hinj ha hb h⟩
      simp only [this]) hx hy
  rw [h2]
  congr 1
  simp only [Matrix.diagonal_apply]
  have : (x = y) ↔ (f x = f y) := ⟨fun h => by rw [h], fun h => hinj hx hy h⟩
  by_cases hxy : x = y
  · subst hxy; simp [hcY x hx]
  · have h' : ¬ f x = f y := fun h => hxy (hinj hx hy h)
    simp [hxy, h']

end BoxTransport



section Cyc
variable {N : ℕ} [NeZero N]

theorem natAbs_cycRep_sub_eq (a b : ZMod N) :
    (cycRep (a - b)).natAbs =
      min (((a.val : ℤ) - b.val).natAbs) (N - ((a.val : ℤ) - b.val).natAbs) := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have key : ∀ a b : ZMod N, b.val ≤ a.val →
      (cycRep (a - b)).natAbs =
        min (((a.val : ℤ) - b.val).natAbs) (N - ((a.val : ℤ) - b.val).natAbs) := by
    intro a b hab
    have ha := ZMod.val_lt a
    have hv : (a - b).val = a.val - b.val := ZMod.val_sub hab
    unfold cycRep
    rw [hv]
    split_ifs with h <;> omega
  rcases le_total b.val a.val with h | h
  · exact key a b h
  · have := key b a h
    rw [← neg_sub, natAbs_cycRep_neg] at this
    rw [this]
    have e : ((b.val : ℤ) - a.val).natAbs = ((a.val : ℤ) - b.val).natAbs := by omega
    rw [e]

end Cyc

section Geom
variable {d M J N : ℕ} [NeZero N]

omit [NeZero N] in
theorem macK_ge (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) : 2 * (J + 6) ≤ macK N M := by
  have hMN : M ≤ N := by nlinarith
  rw [macK_eq_div hM hMN]
  exact (Nat.le_div_iff_mul_le hM).2 hN

omit [NeZero N] in
theorem macCell_eq_iff (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) (j : Fin (macK N M))
    (hj : (j : ℕ) ≤ J + 4) (v : ZMod N) :
    macCell N M v = j ↔ (j : ℕ) * M ≤ v.val ∧ v.val < ((j : ℕ) + 1) * M := by
  have hK := macK_ge (J := J) hM hN
  have hcell : (macCell N M v : ℕ) = min (v.val / M) (macK N M - 1) := rfl
  constructor
  · intro h
    have h' : (macCell N M v : ℕ) = j := by rw [h]
    rw [hcell] at h'
    have hd : v.val / M = j := by omega
    exact ⟨by rw [← hd]; exact Nat.div_mul_le_self _ _,
      by rw [← hd, Nat.mul_comm]; exact Nat.lt_mul_div_succ _ hM⟩
  · rintro ⟨h1, h2⟩
    apply Fin.ext
    rw [hcell]
    have hd : v.val / M = j := Nat.div_eq_of_lt_le (by linarith) (by linarith)
    omega



theorem core_near (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M) {w : MacIdx d N M} {r : ℝ}
    (hr : r ≤ 2 * M) (h : Metric.infDist x (macCore d N M w) < r) :
    (∀ i, (w i : ℕ) ≤ J + 4) ∧ ∃ c : Fin d → ℕ,
      (∀ i, (w i : ℕ) * M ≤ c i ∧ c i < ((w i : ℕ) + 1) * M) ∧
      (((∑ i, (((c i : ℤ) - (x i).val)).natAbs : ℕ) : ℝ) < r) := by
  have hMN : M ≤ N := by nlinarith
  have hNe : 2 * (J * M) + 12 * M ≤ N := by nlinarith
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff (macCore_nonempty w)).1 h
  have hdist : dist x y = ∑ i, ((cycRep (x i - y i)).natAbs : ℝ) := rfl
  have hcoord : ∀ i, (cycRep (x i - y i)).natAbs < 2 * M := by
    intro i
    have h1 := dist_coord_le x y i
    have h2 : ((cycRep (x i - y i)).natAbs : ℝ) < 2 * M := lt_of_le_of_lt h1 (hxy.trans_le hr)
    exact_mod_cast h2
  have hD : ∀ i, (((x i).val : ℤ) - (y i).val).natAbs < 2 * M ∧
      (w i : ℕ) * M ≤ (y i).val ∧ (y i).val < (x i).val + 2 * M := by
    intro i
    have e1 := natAbs_cycRep_sub_eq (x i) (y i)
    have h3 := hcoord i
    have hb := (macCell_val_bounds hM hMN (hy i)).1
    have hbN := ZMod.val_lt (y i)
    have ha := hx i
    have e2 : (J + 3) * M = J * M + 3 * M := by ring
    rw [e1] at h3
    refine ⟨by omega, hb, by omega⟩
  have hgood : ∀ i, (w i : ℕ) ≤ J + 4 := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hD i
    have ha := hx i
    have : (w i : ℕ) * M < (J + 5) * M := by
      have e2 : (J + 5) * M = J * M + 5 * M := by ring
      have e3 := (hx i).2
      have e4 : (J + 3) * M = J * M + 3 * M := by ring
      omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  refine ⟨hgood, fun i => (y i).val, fun i => ?_, ?_⟩
  · refine ⟨(hD i).2.1, ?_⟩
    have := (macCell_eq_iff hM hN (w i) (hgood i) (y i)).1 (hy i)
    exact this.2
  · have hsum : (∑ i, (((y i).val : ℤ) - (x i).val).natAbs) =
        ∑ i, (cycRep (x i - y i)).natAbs := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 := natAbs_cycRep_sub_eq (x i) (y i)
      have h3 := (hD i).1
      have hbN := ZMod.val_lt (y i)
      have ha := hx i
      have e4 : (J + 3) * M = J * M + 3 * M := by ring
      rw [e1]
      omega
    have : (((∑ i, (((y i).val : ℤ) - (x i).val).natAbs : ℕ)) : ℝ) = dist x y := by
      rw [hdist, hsum]; push_cast; rfl
    rw [this]; exact hxy

theorem infDist_lt_of_vals (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) {x : L1Torus d N}
    {w : MacIdx d N M} {r : ℝ}
    (hw : ∀ i, (w i : ℕ) ≤ J + 4) {c : Fin d → ℕ}
    (hc : ∀ i, (w i : ℕ) * M ≤ c i ∧ c i < ((w i : ℕ) + 1) * M)
    (hs : (((∑ i, (((c i : ℤ) - (x i).val)).natAbs : ℕ) : ℝ) < r)) :
    Metric.infDist x (macCore d N M w) < r := by
  have hMN : M ≤ N := by nlinarith
  have hNe : 2 * (J * M) + 12 * M ≤ N := by nlinarith
  have hcN : ∀ i, c i < N := by
    intro i
    have h1 := (hc i).2
    have h2 : ((w i : ℕ) + 1) * M ≤ (J + 5) * M := Nat.mul_le_mul_right M (by have := hw i; omega)
    have e : (J + 5) * M = J * M + 5 * M := by ring
    omega
  set y : L1Torus d N := fun i => ((c i : ℕ) : ZMod N) with hy
  have hyv : ∀ i, (y i).val = c i := fun i => by
    simp only [hy]; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hcN i)]
  have hyc : y ∈ macCore d N M w := fun i =>
    (macCell_eq_iff hM hN (w i) (hw i) (y i)).2 (by rw [hyv]; exact hc i)
  refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hyc) ?_
  refine lt_of_le_of_lt ?_ hs
  have hdist : dist x y = ∑ i, ((cycRep (x i - y i)).natAbs : ℝ) := rfl
  rw [hdist]
  have : (((∑ i, (((c i : ℤ) - (x i).val)).natAbs : ℕ) : ℝ)) =
      ∑ i, ((((c i : ℤ) - (x i).val).natAbs : ℕ) : ℝ) := by push_cast; rfl
  rw [this]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := natAbs_cycRep_sub_le (x i) (y i)
  rw [hyv] at h1
  have h2 : ((((x i).val : ℤ) - (c i : ℤ)).natAbs) = (((c i : ℤ) - (x i).val).natAbs) := by omega
  rw [h2] at h1
  exact_mod_cast h1

theorem infDist_lt_iff_vals (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M) {w : MacIdx d N M} {r : ℝ}
    (hr : r ≤ 2 * M) (hw : ∀ i, (w i : ℕ) ≤ J + 4) :
    Metric.infDist x (macCore d N M w) < r ↔ ∃ c : Fin d → ℕ,
      (∀ i, (w i : ℕ) * M ≤ c i ∧ c i < ((w i : ℕ) + 1) * M) ∧
      (((∑ i, (((c i : ℤ) - (x i).val)).natAbs : ℕ) : ℝ) < r) :=
  ⟨fun h => (core_near hM hN hx hr h).2,
    fun ⟨_, hc, hs⟩ => infDist_lt_of_vals hM hN hw hc hs⟩

end Geom

section Transport
variable {d M J N N' : ℕ} [NeZero N] [NeZero N']

omit [NeZero N] [NeZero N'] in
theorem val_lift {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x : L1Torus d N} {μ : Fin d}
    (h : (x μ).val < N') : (f x μ).val = (x μ).val := by
  rw [hf, ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem infDist_lt_iff_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M) {w : MacIdx d N M}
    {w' : MacIdx d N' M} (hw : ∀ i, (w i : ℕ) ≤ J + 4) (hww : ∀ i, (w' i : ℕ) = w i) {r : ℝ}
    (hr : r ≤ 2 * M) :
    Metric.infDist x (macCore d N M w) < r ↔ Metric.infDist (f x) (macCore d N' M w') < r := by
  have hN'' : (J + 3) * M ≤ N' := by nlinarith
  have hfx : ∀ i, (f x i).val = (x i).val := fun i =>
    val_lift hf (lt_of_lt_of_le (hx i).2 hN'')
  have hx' : ∀ i, 2 * M < (f x i).val ∧ (f x i).val < (J + 3) * M := fun i => by
    rw [hfx]; exact hx i
  have hw' : ∀ i, (w' i : ℕ) ≤ J + 4 := fun i => by rw [hww]; exact hw i
  rw [infDist_lt_iff_vals hM hN hx hr hw, infDist_lt_iff_vals hM hN' hx' hr hw']
  simp only [hfx, hww]

theorem phi_eq_of_lt_iff {u u' M : ℝ} (hM : 0 < M) (h : ∀ r, r ≤ 2 * M → (u < r ↔ u' < r)) :
    max 0 (1 - u / M) = max 0 (1 - u' / M) := by
  by_cases hu : u < M
  · have hu' : u' < M := (h M (by linarith)).1 hu
    have h1 : u ≤ u' := by
      by_contra hc
      exact lt_irrefl _ ((h u (by linarith)).2 (not_le.1 hc))
    have h2 : u' ≤ u := by
      by_contra hc
      exact lt_irrefl _ ((h u' (by linarith)).1 (not_le.1 hc))
    rw [le_antisymm h1 h2]
  · have hu' : ¬ u' < M := fun hc => hu ((h M (by linarith)).2 hc)
    have e1 : 1 - u / M ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hM]; linarith [not_lt.1 hu]
    have e2 : 1 - u' / M ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hM]; linarith [not_lt.1 hu']
    rw [max_eq_left e1, max_eq_left e2]

theorem macPhi_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M) {w : MacIdx d N M}
    {w' : MacIdx d N' M} (hw : ∀ i, (w i : ℕ) ≤ J + 4) (hww : ∀ i, (w' i : ℕ) = w i) :
    macPhi d N M w x = macPhi d N' M w' (f x) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold macPhi
  refine phi_eq_of_lt_iff hM' fun r hr => ?_
  exact infDist_lt_iff_transport hM hN hN' hf hx hw hww hr

theorem macPhi_ne_zero_good (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M) {w : MacIdx d N M}
    (h : macPhi d N M w x ≠ 0) : ∀ i, (w i : ℕ) ≤ J + 4 := by
  have h1 := (macPhi_ne_zero_iff hM w x).1 h
  have hM' : (M : ℝ) ≤ 2 * M := by have : (0 : ℝ) ≤ M := by positivity
                                   linarith
  exact (core_near hM hN hx hM' h1).1

theorem macSum_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M)
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) :
    macSum d N M x = macSum d N' M (f x) := by
  have hN'' : (J + 3) * M ≤ N' := by nlinarith
  have hx' : ∀ i, 2 * M < (f x i).val ∧ (f x i).val < (J + 3) * M := fun i => by
    rw [val_lift hf (lt_of_lt_of_le (hx i).2 hN'')]; exact hx i
  unfold macSum
  refine Finset.sum_bij_ne_zero (fun w _ _ => e w) (fun _ _ _ => Finset.mem_univ _)
    (fun a _ ha b _ hb hab => ?_) (fun b _ hb => ?_) (fun a _ ha => ?_)
  · have hga := macPhi_ne_zero_good hM hN hx ha
    have hgb := macPhi_ne_zero_good hM hN hx hb
    funext i
    apply Fin.ext
    have := congrFun hab i
    have h1 := he a i (hga i)
    have h2 := he b i (hgb i)
    have h3 : ((e a i : Fin (macK N' M)) : ℕ) = ((e b i : Fin (macK N' M)) : ℕ) := by rw [this]
    omega
  · have hgb := macPhi_ne_zero_good hM hN' hx' hb
    have hlt : ∀ i, (b i : ℕ) < macK N M := fun i => by
      have := macK_ge (J := J) hM hN
      have := hgb i
      omega
    set w : MacIdx d N M := fun i => ⟨(b i : ℕ), hlt i⟩ with hw
    have hgood : ∀ i, (w i : ℕ) ≤ J + 4 := fun i => hgb i
    have hew : e w = b := by
      funext i
      apply Fin.ext
      exact he w i (hgood i)
    have hv := macPhi_transport hM hN hN' hf hx hgood (fun i => he w i (hgood i))
    refine ⟨w, Finset.mem_univ _, ?_, hew⟩
    rw [hv, hew]; exact hb
  · have hga := macPhi_ne_zero_good hM hN hx ha
    exact macPhi_transport hM hN hN' hf hx hga (fun i => he a i (hga i))

theorem macChi_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M)
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {z : MacIdx d N M} (hz : ∀ i, (z i : ℕ) ≤ J + 4) :
    macChi d N M z x = macChi d N' M (e z) (f x) := by
  unfold macChi
  rw [macPhi_transport hM hN hN' hf hx hz (fun i => he z i (hz i)),
    macSum_transport hM hN hN' hf hx he]

omit [NeZero N'] in
theorem mid_of_mem_macBox (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) {z : MacIdx d N M}
    (hz : ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) {x : L1Torus d N} (hx : x ∈ macBox d N M z) :
    ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M := by
  have hMN : M ≤ N := by nlinarith
  have hNe : 2 * (J * M) + 12 * M ≤ N := by nlinarith
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff (macCore_nonempty z)).1 hx
  have hdist : dist x y = ∑ i, ((cycRep (x i - y i)).natAbs : ℝ) := rfl
  intro i
  have h1 := dist_coord_le x y i
  have h2 : ((cycRep (x i - y i)).natAbs : ℝ) < 2 * M := lt_of_le_of_lt h1 hxy
  have h3 : (cycRep (x i - y i)).natAbs < 2 * M := by exact_mod_cast h2
  have e1 := natAbs_cycRep_sub_eq (x i) (y i)
  have hb := (macCell_eq_iff hM hN (z i) (by have := (hz i).2; omega) (y i)).1 (hy i)
  have hb1 : 4 * M ≤ (z i : ℕ) * M := Nat.mul_le_mul_right M (hz i).1
  have hb2 : ((z i : ℕ) + 1) * M ≤ (J + 1) * M := Nat.mul_le_mul_right M (by have := (hz i).2; omega)
  have ha := ZMod.val_lt (x i)
  have hbN := ZMod.val_lt (y i)
  have e2 : (J + 1) * M = J * M + M := by ring
  have e3 : (J + 3) * M = J * M + 3 * M := by ring
  rw [e1] at h3
  constructor <;> omega

theorem mem_macBox_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M) {w : MacIdx d N M}
    {w' : MacIdx d N' M} (hw : ∀ i, (w i : ℕ) ≤ J + 4) (hww : ∀ i, (w' i : ℕ) = w i) :
    x ∈ macBox d N M w ↔ f x ∈ macBox d N' M w' :=
  infDist_lt_iff_transport hM hN hN' hf hx hw hww le_rfl

omit [NeZero N'] in
theorem cycRep_sub_eq_signed (a b : ZMod N) (h : 2 * (((b.val : ℤ) - a.val).natAbs) < N) :
    cycRep (b - a) = (b.val : ℤ) - a.val := by
  have e1 := natAbs_cycRep_sub_eq b a
  have hb := ZMod.val_lt b
  have ha := ZMod.val_lt a
  have e2 : (cycRep (b - a)).natAbs = ((b.val : ℤ) - a.val).natAbs := by
    rw [e1]; omega
  have hcast : (((cycRep (b - a) - ((b.val : ℤ) - a.val) : ℤ)) : ZMod N) = 0 := by
    push_cast
    rw [cast_cycRep]; simp
  have hdvd : (N : ℤ) ∣ cycRep (b - a) - ((b.val : ℤ) - a.val) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcast
  have hlt : (cycRep (b - a) - ((b.val : ℤ) - a.val)).natAbs < (N : ℤ).natAbs := by
    have := Int.natAbs_sub_le (cycRep (b - a)) ((b.val : ℤ) - a.val)
    simp only [Int.natAbs_natCast]
    omega
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hlt
  omega

omit [NeZero N'] in
theorem mem_macArc_iff (a b p : ZMod N) (h : 2 * (((b.val : ℤ) - a.val).natAbs) < N) :
    p ∈ macArc a b ↔ min a.val b.val ≤ p.val ∧ p.val ≤ max a.val b.val := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hp := ZMod.val_lt p
  unfold macArc
  rw [Finset.mem_image, cycRep_sub_eq_signed a b h]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [Finset.mem_Icc] at he
    have hv : (((a + (e : ZMod N)).val : ℕ) : ℤ) = (a.val : ℤ) + e := by
      have h1 : a + (e : ZMod N) = (((a.val : ℤ) + e : ℤ) : ZMod N) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [h1, ZMod.val_intCast]
      apply Int.emod_eq_of_lt <;> omega
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(p.val : ℤ) - a.val, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring

theorem path_transport (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x y p : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M)
    (hy : ∀ i, 2 * M < (y i).val ∧ (y i).val < (J + 3) * M)
    (hp : p ∈ macPath d N x y) :
    (∀ i, 2 * M < (p i).val ∧ (p i).val < (J + 3) * M) ∧ f p ∈ macPath d N' (f x) (f y) := by
  have hN'' : (J + 3) * M ≤ N' := by nlinarith
  have e3 : (J + 3) * M = J * M + 3 * M := by ring
  have hNe : 2 * (J * M) + 12 * M ≤ N := by nlinarith
  have hNe' : 2 * (J * M) + 12 * M ≤ N' := by nlinarith
  have hfv : ∀ (q : L1Torus d N) (i : Fin d), (q i).val < N' → (f q i).val = (q i).val :=
    fun q i h => val_lift hf h
  obtain ⟨k, h1, h2, h3⟩ := hp
  have hxyk : 2 * ((((y k).val : ℤ) - (x k).val).natAbs) < N := by
    have := hx k; have := hy k; omega
  have harc := (mem_macArc_iff (x k) (y k) (p k) hxyk).1 h3
  refine ⟨fun i => ?_, k, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rcases lt_trichotomy i k with hik | hik | hik
    · rw [h1 i hik]; exact hy i
    · subst hik
      have := hx i; have := hy i
      constructor <;> omega
    · rw [h2 i hik]; exact hx i
  · rw [hf, hf, h1 i hi]
  · rw [hf, hf, h2 i hi]
  · have hxk := hx k
    have hyk := hy k
    have hxk' : (f x k).val = (x k).val := hfv x k (by omega)
    have hyk' : (f y k).val = (y k).val := hfv y k (by omega)
    have hpk : (f p k).val = (p k).val := by
      refine hfv p k ?_
      omega
    have hxyk' : 2 * ((((f y k).val : ℤ) - (f x k).val).natAbs) < N' := by
      rw [hxk', hyk']; omega
    rw [mem_macArc_iff (f x k) (f y k) (f p k) hxyk', hxk', hyk', hpk]
    exact harc

theorem tags_forward (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {x y : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M)
    (hy : ∀ i, 2 * M < (y i).val ∧ (y i).val < (J + 3) * M)
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {z : MacIdx d N M} (hz : ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) {w : MacIdx d N M}
    (hw : w ∈ macTags d N M z x y) :
    (∀ i, (w i : ℕ) ≤ J + 4) ∧ e w ∈ macTags d N' M (e z) (f x) (f y) := by
  classical
  have hzg : ∀ i, (z i : ℕ) ≤ J + 4 := fun i => by have := (hz i).2; omega
  unfold macTags at hw ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  have hM2 : (2 : ℝ) * M ≤ 2 * M := le_rfl
  rcases hw with ⟨p, hpw, hpz⟩ | ⟨p, hpath, hpw⟩
  · have hmid := mid_of_mem_macBox hM hN hz hpz
    have hgood := (core_near hM hN hmid hM2 hpw).1
    refine ⟨hgood, Or.inl ⟨f p, ?_, ?_⟩⟩
    · exact (mem_macBox_transport hM hN hN' hf hmid hgood (fun i => he w i (hgood i))).1 hpw
    · exact (mem_macBox_transport hM hN hN' hf hmid hzg (fun i => he z i (hzg i))).1 hpz
  · obtain ⟨hmid, hpath'⟩ := path_transport hM hN hN' hf hx hy hpath
    have hgood := (core_near hM hN hmid hM2 hpw).1
    refine ⟨hgood, Or.inr ⟨f p, hpath', ?_⟩⟩
    exact (mem_macBox_transport hM hN hN' hf hmid hgood (fun i => he w i (hgood i))).1 hpw

omit [NeZero N'] in
theorem lift_lift {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {g : L1Torus d N' → L1Torus d N}
    (hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N)) {x : L1Torus d N}
    (hx : ∀ i, (x i).val < N') : g (f x) = x := by
  funext μ
  rw [hg, val_lift hf (hx μ), ZMod.natCast_zmod_val]

theorem tags_backward (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {g : L1Torus d N' → L1Torus d N}
    (hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N)) {x y : L1Torus d N}
    (hx : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M)
    (hy : ∀ i, 2 * M < (y i).val ∧ (y i).val < (J + 3) * M)
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {e' : MacIdx d N' M → MacIdx d N M}
    (he' : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e' z i : Fin (macK N M)) : ℕ) = z i)
    {z : MacIdx d N M} (hz : ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) {w' : MacIdx d N' M}
    (hw' : w' ∈ macTags d N' M (e z) (f x) (f y)) :
    ∃ w ∈ macTags d N M z x y, e w = w' := by
  have hN'' : (J + 3) * M ≤ N' := by nlinarith
  have hxN : ∀ i, (x i).val < N' := fun i => lt_of_lt_of_le (hx i).2 hN''
  have hyN : ∀ i, (y i).val < N' := fun i => lt_of_lt_of_le (hy i).2 hN''
  have hfx : ∀ i, 2 * M < (f x i).val ∧ (f x i).val < (J + 3) * M := fun i => by
    rw [val_lift hf (hxN i)]; exact hx i
  have hfy : ∀ i, 2 * M < (f y i).val ∧ (f y i).val < (J + 3) * M := fun i => by
    rw [val_lift hf (hyN i)]; exact hy i
  have hez : ∀ i, 4 ≤ (e z i : ℕ) ∧ (e z i : ℕ) ≤ J := fun i => by
    rw [he z i (by have := (hz i).2; omega)]; exact hz i
  obtain ⟨hgood, hmem⟩ := tags_forward hM hN' hN hg hfx hfy he' hez hw'
  have h1 : e' (e z) = z := by
    funext i
    apply Fin.ext
    rw [he' (e z) i (by have := (hez i).2; omega), he z i (by have := (hz i).2; omega)]
  rw [h1, lift_lift hf hg hxN, lift_lift hf hg hyN] at hmem
  refine ⟨e' w', hmem, ?_⟩
  funext i
  apply Fin.ext
  rw [he (e' w') i (by have := he' w' i (hgood i); have := hgood i; omega), he' w' i (hgood i)]

omit [NeZero N'] in
theorem mem_macTags_self (hM : 0 < M) (z : MacIdx d N M) (x y : L1Torus d N) :
    z ∈ macTags d N M z x y := by
  classical
  obtain ⟨p, hp⟩ := macCore_nonempty (d := d) (m := N) (M := M) z
  unfold macTags
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inl ⟨p, mem_macBox_of_mem_macCore hM hp, mem_macBox_of_mem_macCore hM hp⟩

omit [NeZero N'] in
theorem injOn_lift {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) {S : Set (L1Torus d N)}
    (hS : ∀ x ∈ S, ∀ i, (x i).val < N') : Set.InjOn f S := by
  intro x hx y hy hxy
  funext μ
  apply ZMod.val_injective
  have h1 := val_lift hf (hS x hx μ)
  have h2 := val_lift hf (hS y hy μ)
  rw [← h1, ← h2, hxy]

theorem macBoxF_image (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {g : L1Torus d N' → L1Torus d N}
    (hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {z : MacIdx d N M} (hz : ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) :
    macBoxF d N' M (e z) = (macBoxF d N M z).image f := by
  classical
  have hN'' : (J + 3) * M ≤ N' := by nlinarith
  have hN3 : (J + 3) * M ≤ N := by nlinarith
  have hzg : ∀ i, (z i : ℕ) ≤ J + 4 := fun i => by have := (hz i).2; omega
  have hez : ∀ i, 4 ≤ (e z i : ℕ) ∧ (e z i : ℕ) ≤ J := fun i => by
    rw [he z i (hzg i)]; exact hz i
  ext x'
  rw [Finset.mem_image]
  constructor
  · intro hx'
    have hx'b := mem_macBoxF.1 hx'
    have hmid' := mid_of_mem_macBox hM hN' hez hx'b
    have hvals : ∀ i, (x' i).val < N := fun i => lt_of_lt_of_le (hmid' i).2 hN3
    have hgx : ∀ i, 2 * M < (g x' i).val ∧ (g x' i).val < (J + 3) * M := fun i => by
      rw [val_lift hg (hvals i)]; exact hmid' i
    have hfg : f (g x') = x' := lift_lift hg hf hvals
    refine ⟨g x', mem_macBoxF.2 ?_, hfg⟩
    refine (mem_macBox_transport hM hN hN' hf hgx hzg (fun i => he z i (hzg i))).2 ?_
    rw [hfg]; exact hx'b
  · rintro ⟨x, hx, rfl⟩
    have hxb := mem_macBoxF.1 hx
    have hmid := mid_of_mem_macBox hM hN hz hxb
    exact mem_macBoxF.2 ((mem_macBox_transport hM hN hN' hf hmid hzg
      (fun i => he z i (hzg i))).1 hxb)

omit [NeZero N] [NeZero N'] in
theorem exists_cellMap (hM : 0 < M) (hN' : 2 * (J + 6) * M ≤ N') :
    ∃ e : MacIdx d N M → MacIdx d N' M, ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i := by
  have hK := macK_ge (J := J) hM hN'
  refine ⟨fun z i => ⟨min (z i : ℕ) (macK N' M - 1), by omega⟩, fun z i hz => ?_⟩
  show min (z i : ℕ) (macK N' M - 1) = z i
  omega

theorem mid_of_mem_macRegion (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N) {C : Finset (MacIdx d N M)}
    (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) {x : L1Torus d N}
    (hx : x ∈ macRegion d N M C) : ∀ i, 2 * M < (x i).val ∧ (x i).val < (J + 3) * M := by
  obtain ⟨z, hz, hxz⟩ := mem_macRegion.1 hx
  exact mid_of_mem_macBox hM hN (hC z hz) hxz

theorem macRegion_bijOn (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {g : L1Torus d N' → L1Torus d N}
    (hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) :
    Set.BijOn f (macRegion d N M C) (macRegion d N' M (C.image e)) := by
  classical
  have hN'' : (J + 3) * M ≤ N' := by nlinarith
  refine ⟨fun x hx => ?_, ?_, fun y' hy' => ?_⟩
  · obtain ⟨z, hz, hxz⟩ := mem_macRegion.1 hx
    have hmid := mid_of_mem_macBox hM hN (hC z hz) hxz
    have hzg : ∀ i, (z i : ℕ) ≤ J + 4 := fun i => by have := (hC z hz i).2; omega
    exact mem_macRegion.2 ⟨e z, Finset.mem_image_of_mem e hz,
      (mem_macBox_transport hM hN hN' hf hmid hzg (fun i => he z i (hzg i))).1 hxz⟩
  · exact injOn_lift hf (fun x hx i => lt_of_lt_of_le (mid_of_mem_macRegion hM hN hC hx i).2 hN'')
  · obtain ⟨p, hp, hy'p⟩ := mem_macRegion.1 hy'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    have h1 : y' ∈ macBoxF d N' M (e z) := mem_macBoxF.2 hy'p
    rw [macBoxF_image hM hN hN' hf hg he (hC z hz)] at h1
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h1
    exact ⟨x, mem_macRegion.2 ⟨z, hz, mem_macBoxF.1 hx⟩, hxy⟩

theorem taggedKE_entry_twoTorus (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {U E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {U' E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    {t : ℝ}
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, U x y = U' (f x) (f y))
    (hE : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, E x y = E' (f x) (f y))
    {s : MacIdx d N M → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ Balaban.Localization.supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) {x y : L1Torus d N} (hx : x ∈ macRegion d N M C)
    (hy : y ∈ macRegion d N M C) :
    taggedMat Finset.univ (macTags d N M)
      (fun z => boxR U (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG U (macBoxF d N M z) t)) s x y =
    taggedMat Finset.univ (macTags d N' M)
      (fun z => boxR U' (macBoxF d N' M z) (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
        E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
          boxG U' (macBoxF d N' M z) t)) s' (f x) (f y) := by
  classical
  obtain ⟨e', he'⟩ := exists_cellMap (d := d) (N := N') (N' := N) (J := J) hM hN
  set g : L1Torus d N' → L1Torus d N := fun y μ => (((y μ).val : ℕ) : ZMod N) with hgdef
  have hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) := fun _ _ => rfl
  have hmidY : ∀ u, u ∈ macRegion d N M C → ∀ i, 2 * M < (u i).val ∧ (u i).val < (J + 3) * M :=
    fun u hu => mid_of_mem_macRegion hM hN hC hu
  have hxm := hmidY x hx
  have hym := hmidY y hy
  rw [taggedMat_apply_of_supportedOn _ _ _ hs, taggedMat_apply_of_supportedOn _ _ _ hs']
  have hgoodC : ∀ z ∈ C, ∀ i, (z i : ℕ) ≤ J + 4 := fun z hz i => by
    have := (hC z hz i).2; omega
  have hinjE : Set.InjOn e (C : Set (MacIdx d N M)) := by
    intro z1 hz1 z2 hz2 h
    funext i
    apply Fin.ext
    have h1 := he z1 i (hgoodC z1 hz1 i)
    have h2 := he z2 i (hgoodC z2 hz2 i)
    have : ((e z1 i : Fin (macK N' M)) : ℕ) = ((e z2 i : Fin (macK N' M)) : ℕ) := by rw [h]
    omega
  have hVimg : ∀ z ∈ C, macTags d N' M (e z) (f x) (f y) = (macTags d N M z x y).image e := by
    intro z hz
    ext w'
    constructor
    · intro hw'
      obtain ⟨w, hw, rfl⟩ := tags_backward hM hN hN' hf hg hxm hym he he' (hC z hz) hw'
      exact Finset.mem_image_of_mem e hw
    · intro hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hw'
      exact (tags_forward hM hN hN' hf hxm hym he (hC z hz) hw).2
  have hsubset_iff : ∀ z ∈ C, (macTags d N M z x y ⊆ C) ↔
      (macTags d N' M (e z) (f x) (f y) ⊆ C.image e) := by
    intro z hz
    rw [hVimg z hz]
    constructor
    · intro h
      exact Finset.image_subset_image h
    · intro h w hw
      have h1 := h (Finset.mem_image_of_mem e hw)
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h1
      have hwg := (tags_forward hM hN hN' hf hxm hym he (hC z hz) hw).1
      have : w = c := by
        funext i
        apply Fin.ext
        have h1 := he w i (hwg i)
        have h2 := he c i (hgoodC c hc i)
        have : ((e w i : Fin (macK N' M)) : ℕ) = ((e c i : Fin (macK N' M)) : ℕ) := by rw [hce]
        omega
      rw [this]; exact hc
  have hL : (Finset.univ.filter fun z => macTags d N M z x y ⊆ C) =
      C.filter (fun z => macTags d N M z x y ⊆ C) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h (mem_macTags_self hM z x y), h⟩, fun h => h.2⟩
  have hR : (Finset.univ.filter fun z' => macTags d N' M z' (f x) (f y) ⊆ C.image e) =
      (C.filter (fun z => macTags d N M z x y ⊆ C)).image e := by
    ext z'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have hz' : z' ∈ C.image e := h (mem_macTags_self hM z' _ _)
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
      exact ⟨z, ⟨hz, (hsubset_iff z hz).2 h⟩, rfl⟩
    · rintro ⟨z, ⟨hz, h⟩, rfl⟩
      exact (hsubset_iff z hz).1 h
  rw [hL, hR, Finset.sum_image (hinjE.mono (by intro z hz; exact (Finset.mem_filter.1 hz).1))]
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨hzC, hVC⟩ := Finset.mem_filter.1 hz
  rw [hVimg z hzC]
  have hprod : tagMon (macTags d N M z x y) s = tagMon ((macTags d N M z x y).image e) s' := by
    unfold tagMon
    rw [Finset.prod_image (hinjE.mono (by intro w hw; exact hVC hw))]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hss w (hVC hw)]
  rw [hprod]
  congr 1
  set Yset : Finset (L1Torus d N) := Finset.univ.filter (fun u => u ∈ macRegion d N M C) with hYset
  have hYmem : ∀ u, u ∈ Yset ↔ u ∈ macRegion d N M C := fun u => by simp [hYset]
  have hN3 : (J + 3) * M ≤ N' := by nlinarith
  have hinjY : Set.InjOn f (Yset : Set (L1Torus d N)) :=
    injOn_lift hf (fun u hu i => lt_of_lt_of_le (hmidY u ((hYmem u).1 hu) i).2 hN3)
  have hBimg := macBoxF_image hM hN hN' hf hg he (hC z hzC)
  have hBY : macBoxF d N M z ⊆ Yset := fun u hu =>
    (hYmem u).2 (mem_macRegion.2 ⟨z, hzC, mem_macBoxF.1 hu⟩)
  have hUY : ∀ a ∈ Yset, ∀ b ∈ Yset, U a b = U' (f a) (f b) := fun a ha b hb =>
    hU a ((hYmem a).1 ha) b ((hYmem b).1 hb)
  have hEY : ∀ a ∈ Yset, ∀ b ∈ Yset, E a b = E' (f a) (f b) := fun a ha b hb =>
    hE a ((hYmem a).1 ha) b ((hYmem b).1 hb)
  have hc : ∀ u, ((macChi d N M z u : ℝ) : ℂ) ≠ 0 → u ∈ macBoxF d N M z := fun u h =>
    macChi_ne_zero_mem_macBoxF hM h
  have hc' : ∀ u, ((macChi d N' M (e z) u : ℝ) : ℂ) ≠ 0 → u ∈ (macBoxF d N M z).image f :=
    fun u h => hBimg ▸ macChi_ne_zero_mem_macBoxF hM h
  have hcY : ∀ u ∈ Yset, ((macChi d N M z u : ℝ) : ℂ) = ((macChi d N' M (e z) (f u) : ℝ) : ℂ) :=
    fun u hu => by
      rw [macChi_transport hM hN hN' hf (hmidY u ((hYmem u).1 hu)) he (hgoodC z hzC)]
  rw [hBimg, Matrix.sub_apply, Matrix.sub_apply]
  congr 1
  · exact boxR_transport f hBY hinjY t hUY hc hc' hcY ((hYmem x).2 hx) ((hYmem y).2 hy)
  · exact rowmul_transport f hBY hinjY t hUY hc hc' hcY hEY ((hYmem x).2 hx) ((hYmem y).2 hy)


theorem det_taggedKE_twoTorus (hM : 0 < M) (hd : 0 < d) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {U E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {U' E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    {t : ℝ}
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, U x y = U' (f x) (f y))
    (hE : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, E x y = E' (f x) (f y))
    {s : MacIdx d N M → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ Balaban.Localization.supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) :
    (1 - taggedMat Finset.univ (macTags d N M)
      (fun z => boxR U (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG U (macBoxF d N M z) t)) s).det =
    (1 - taggedMat Finset.univ (macTags d N' M)
      (fun z => boxR U' (macBoxF d N' M z) (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
        E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
          boxG U' (macBoxF d N' M z) t)) s').det := by
  classical
  obtain ⟨e', he'⟩ := exists_cellMap (d := d) (N := N') (N' := N) (J := J) hM hN
  set g : L1Torus d N' → L1Torus d N := fun y μ => (((y μ).val : ℕ) : ZMod N) with hgdef
  have hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) := fun _ _ => rfl
  have hbij := macRegion_bijOn hM hN hN' hf hg he hC
  have hN3 : (J + 3) * M ≤ N' := by nlinarith
  have hinjR : Set.InjOn f (macRegion d N M C) :=
    injOn_lift hf (fun u hu i => lt_of_lt_of_le (mid_of_mem_macRegion hM hN hC hu i).2 hN3)
  refine det_eq_of_bijOn _ _ (Finset.univ.filter fun u => u ∈ macRegion d N M C)
    (Finset.univ.filter fun u => u ∈ macRegion d N' M (C.image e)) f (by simpa using hbij) ?_ ?_ ?_
  · intro x hx y
    have hx' : x ∉ macRegion d N M C := by simpa using hx
    rw [Matrix.sub_apply, tm_row_eq_zero hM hd _ hs hx' y, sub_zero]
  · intro x hx y
    have hx' : x ∉ macRegion d N' M (C.image e) := by simpa using hx
    rw [Matrix.sub_apply, tm_row_eq_zero hM hd _ hs' hx' y, sub_zero]
  · intro x hx y hy
    have hx' : x ∈ macRegion d N M C := by simpa using hx
    have hy' : y ∈ macRegion d N M C := by simpa using hy
    rw [Matrix.sub_apply, Matrix.sub_apply,
      taggedKE_entry_twoTorus hM hN hN' hf he hC hU hE hs hs' hss hx' hy']
    congr 1
    simp only [Matrix.one_apply]
    have : (x = y) ↔ (f x = f y) := ⟨fun h => by rw [h], fun h => hinjR hx' hy' h⟩
    simp only [this]

theorem coef_eq_of_agree_taggedKE_twoTorus (hM : 0 < M) (hd : 0 < d)
    (hN : 2 * (J + 6) * M ≤ N) (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {R : ℝ} (hR : 1 < R)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {U E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {U' E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    {t : ℝ}
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, U x y = U' (f x) (f y))
    (hE : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, E x y = E' (f x) (f y))
    {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 R))
    (hell' : ContinuousOn ell' (Metric.ball 0 R)) (h0 : ell 0 = 0) (h0' : ell' 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) R,
      (1 - taggedMat Finset.univ (macTags d N M)
        (fun z => boxR U (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG U (macBoxF d N M z) t)) s).det = Complex.exp (ell s))
    (hdet' : ∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) R,
      (1 - taggedMat Finset.univ (macTags d N' M)
        (fun z => boxR U' (macBoxF d N' M z) (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
          E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
            boxG U' (macBoxF d N' M z) t)) s).det = Complex.exp (ell' s)) :
    coef ell C = coef ell' (C.image e) := by
  classical
  have hR0 : 0 < R := by linarith
  have hgoodC : ∀ z ∈ C, ∀ i, (z i : ℕ) ≤ J + 4 := fun z hz i => by
    have := (hC z hz i).2; omega
  have hinjE : Set.InjOn e (C : Set (MacIdx d N M)) := by
    intro z1 hz1 z2 hz2 h
    funext i
    apply Fin.ext
    have h1 := he z1 i (hgoodC z1 hz1 i)
    have h2 := he z2 i (hgoodC z2 hz2 i)
    have : ((e z1 i : Fin (macK N' M)) : ℕ) = ((e z2 i : Fin (macK N' M)) : ℕ) := by rw [h]
    omega
  -- the transport of a parameter vector supported on `C`
  set τ : (MacIdx d N M → ℂ) → (MacIdx d N' M → ℂ) :=
    fun u j => ∑ i ∈ C.filter (fun i => e i = j), u i with hτ
  have hτe : ∀ u i, i ∈ C → τ u (e i) = u i := by
    intro u i hi
    have : C.filter (fun i' => e i' = e i) = {i} := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hi', h⟩
        exact hinjE hi' hi h
      · rintro rfl
        exact ⟨hi, rfl⟩
    simp [hτ, this]
  have hτsupp : ∀ u, τ u ∈ Balaban.Localization.supportedOn (C.image e) := by
    intro u j hj
    have : C.filter (fun i => e i = j) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hi h
      exact hj (Finset.mem_image.2 ⟨i, hi, h⟩)
    simp [hτ, this]
  have hτnorm : ∀ u, (∀ i, ‖u i‖ < R) → ∀ j, ‖τ u j‖ < R := by
    intro u hu j
    by_cases hj : j ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      rw [hτe u i hi]; exact hu i
    · have := hτsupp u j hj
      rw [this]; simpa using hR0
  have hτcont : Continuous τ :=
    continuous_pi fun j => continuous_finsetSum _ fun i _ => continuous_apply i
  have hτ0 : τ 0 = 0 := by
    funext j; simp [hτ]
  have hRel := Balaban.Polymer.TwoTorusStep.coef_relabel_injOn hR e hinjE
    (f := ell) (f' := ell') (by rw [polydisc_eq_ball hR0]; exact hell) ?_
  · exact hRel.symm
  intro s hs s' hs' hss
  have hsb : s ∈ Metric.ball (0 : MacIdx d N M → ℂ) R := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hR0]; exact hs.2
  have hs'eq : s' = τ s := by
    funext j
    by_cases hj : j ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      rw [hss i hi, hτe s i hi]
    · rw [hs' j hj, hτsupp s j hj]
  rw [hs'eq]
  set S : Set (MacIdx d N M → ℂ) := Metric.ball 0 R ∩ Balaban.Localization.supportedOn C with hS
  have hSconv : Convex ℝ S :=
    (convex_ball _ _).inter (convex_supportedOn C)
  have h0S : (0 : MacIdx d N M → ℂ) ∈ S := ⟨Metric.mem_ball_self hR0, fun i _ => rfl⟩
  have hSτ : ∀ u ∈ S, τ u ∈ Metric.ball (0 : MacIdx d N' M → ℂ) R := by
    intro u hu
    rw [mem_ball_zero_iff, pi_norm_lt_iff hR0]
    exact hτnorm u (by
      have := hu.1
      rw [mem_ball_zero_iff, pi_norm_lt_iff hR0] at this
      exact this)
  have heq : ∀ u ∈ S, ell u = ell' (τ u) := by
    refine eq_of_exp_eq_of_continuousOn hSconv.isPreconnected h0S
      (hell.continuousOn.mono Set.inter_subset_left)
      (hell'.comp hτcont.continuousOn (fun u hu => hSτ u hu)) (by rw [h0, hτ0, h0'])
      fun u hu => ?_
    rw [← hdet u hu.1, ← hdet' (τ u) (hSτ u hu)]
    exact det_taggedKE_twoTorus hM hd hN hN' hf he hC hU hE hu.2 (hτsupp u) (hτe u)
  symm
  exact heq s ⟨hsb, hs.1⟩

theorem coef_detRatio_eq_twoTorus (hM : 0 < M) (hd : 0 < d)
    (hN : 2 * (J + 6) * M ≤ N) (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {κ : ℝ} (hκ : 0 < κ) {ρ ρ' : ℝ} (hρ : Real.exp κ < ρ) (hρ' : Real.exp κ < ρ')
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {U : Matrix (L1Torus d N) (L1Torus d N) ℂ} {U' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    {t : ℝ}
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, U x y = U' (f x) (f y))
    (hE : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, E x y = E' (f x) (f y))
    {ell0 ellE : (MacIdx d N M → ℂ) → ℂ} {ell0' ellE' : (MacIdx d N' M → ℂ) → ℂ}
    (hell0 : AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ))
    (hellE : AnalyticOnNhd ℂ ellE (Metric.ball 0 ρ))
    (hell0' : AnalyticOnNhd ℂ ell0' (Metric.ball 0 ρ'))
    (hellE' : AnalyticOnNhd ℂ ellE' (Metric.ball 0 ρ'))
    (h00 : ell0 0 = 0) (h0E : ellE 0 = 0) (h00' : ell0' 0 = 0) (h0E' : ellE' 0 = 0)
    (hdet0 : ∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
      (1 - taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
        (macTags d N M) U t s).det = Complex.exp (ell0 s))
    (hdetE : ∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
      (1 - taggedMat Finset.univ (macTags d N M)
        (fun z => boxR U (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG U (macBoxF d N M z) t)) s).det = Complex.exp (ellE s))
    (hdet0' : ∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
      (1 - taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) U' t s).det = Complex.exp (ell0' s))
    (hdetE' : ∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
      (1 - taggedMat Finset.univ (macTags d N' M)
        (fun z => boxR U' (macBoxF d N' M z) (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
          E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
            boxG U' (macBoxF d N' M z) t)) s).det = Complex.exp (ellE' s)) :
    coef ellE C - coef ell0 C = coef ellE' (C.image e) - coef ell0' (C.image e) := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hb : Metric.ball (0 : MacIdx d N M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ :=
    Metric.ball_subset_ball hρ.le
  have hb' : Metric.ball (0 : MacIdx d N' M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
    Metric.ball_subset_ball hρ'.le
  have h1 := coef_eq_of_agree_taggedKE_twoTorus hM hd hN hN' hf he hR hC hU hE
    (hellE.mono hb) (hellE'.continuousOn.mono hb') h0E h0E' (fun s hs => hdetE s (hb hs))
    (fun s hs => hdetE' s (hb' hs))
  have hzero : ∀ {N0 : ℕ} [NeZero N0] (U0 : Matrix (L1Torus d N0) (L1Torus d N0) ℂ)
      (s : MacIdx d N0 M → ℂ),
      taggedMat Finset.univ (macTags d N0 M)
        (fun z => boxR U0 (macBoxF d N0 M z) (fun u => ((macChi d N0 M z u : ℝ) : ℂ)) t -
          (0 : Matrix (L1Torus d N0) (L1Torus d N0) ℂ) *
            (Matrix.diagonal (fun u => ((macChi d N0 M z u : ℝ) : ℂ)) *
              boxG U0 (macBoxF d N0 M z) t)) s =
      taggedK Finset.univ (macBoxF d N0 M) (fun z u => ((macChi d N0 M z u : ℝ) : ℂ))
        (macTags d N0 M) U0 t s := fun U0 s => taggedKE_zero_eq U0 t s
  have h0 := coef_eq_of_agree_taggedKE_twoTorus hM hd hN hN' hf he hR hC (E := 0) (E' := 0)
    hU (fun x _ y _ => by simp)
    (hell0.mono hb) (hell0'.continuousOn.mono hb') h00 h00'
    (fun s hs => by rw [hzero]; exact hdet0 s (hb hs))
    (fun s hs => by rw [hzero]; exact hdet0' s (hb' hs))
  rw [h1, h0]

end Transport

end Balaban.Green
