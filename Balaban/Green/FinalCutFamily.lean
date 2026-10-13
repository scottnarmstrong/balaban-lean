/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalMassSqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cut families of the final reference operator (FINAL leaf S2, first part)

For a real cut weight `s : sites → sites → ℝ` the cut operator `finalOpCut s` has entries
`s x y • finalOp x y` (`finalOp` of `Green/FinalMassGreen.lean`).  The weight `s ≡ 1` gives the
full operator; the indicator of "same region" decouples the operator across a region boundary.

Proved here (real weights only):

* for the convex class `s = ∑ⱼ λⱼ 1[x, y in the same cell of the partition Pⱼ]`, `λⱼ ≥ 0`,
  `∑ λⱼ = 1`, the operator `finalOpCut s` is the convex combination of the block-diagonal
  compressions of `finalOp`; it has the same gap `finalGap d L` and the same entry decay as
  `finalOp` (`finalOpCut_isCoercive`, `finalOpCut_entry_decay`);
* for every `t ≥ 0` the matrix `finalOpCut s + t` is invertible, with the resolvent bound
  `2/(g_* + t) exp(-r_* dist x y)` and the inverse square root bound
  `2 g_*^{-1/2} exp(-r_* dist x y)`, with the constants of `finalOp` (uniform in the cut, the
  torus size, `k`, `t`);
* cut-locality: two weights that agree on a region `X` and vanish across its boundary have the same
  resolvent on `X × X`.

Nothing is claimed about complex cut parameters, about the determinant, or about the physical final
density; the constants and the statements are generator-neutral.
-/

@[expose] public section

open Matrix Finset MeasureTheory Set

namespace Balaban.Green

section Weights

variable {ι : Type*}

/-- Entries of `A` multiplied by the real weight `s`. -/
noncomputable def cutMat (s : ι → ι → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun x y => (s x y : ℂ) • A x y

/-- The compression of `A` to the cells of the labelling `c`. -/
noncomputable def blockMat (c : ι → ℕ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun x y => if c x = c y then A x y else 0

/-- The convex cut weight `∑ⱼ λⱼ 1[cⱼ x = cⱼ y]`. -/
noncomputable def cutWeight {J : Type*} [Fintype J] (lam : J → ℝ) (c : J → ι → ℕ) :
    ι → ι → ℝ :=
  fun x y => ∑ j, lam j * (if c j x = c j y then 1 else 0)

end Weights

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem reQuad_sum {J : Type*} (S : Finset J) (f : J → Matrix ι ι ℂ) (u : ι → ℂ) :
    reQuad (∑ j ∈ S, f j) u = ∑ j ∈ S, reQuad (f j) u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reQuad]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, reQuad_add, ih]

omit [DecidableEq ι] in
theorem reQuad_real_smul (r : ℝ) (B : Matrix ι ι ℂ) (u : ι → ℂ) :
    reQuad ((r : ℂ) • B) u = r * reQuad B u := by
  unfold reQuad
  simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_left_comm _ (r : ℂ),
    ← Finset.mul_sum]
  exact Complex.re_ofReal_mul r _

omit [DecidableEq ι] in
/-- The block compression of a coercive matrix is coercive with the same constant. -/
theorem IsCoercive.compress {A : Matrix ι ι ℂ} {γ : ℝ} (hA : IsCoercive A γ) (c : ι → ℕ) :
    IsCoercive (blockMat c A) γ := by
  intro u
  set S : Finset ℕ := Finset.univ.image c with hS
  set uc : ℕ → ι → ℂ := fun m i => if c i = m then u i else 0 with huc
  have hmem : ∀ i, c i ∈ S := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hq : reQuad (blockMat c A) u = ∑ m ∈ S, reQuad A (uc m) := by
    unfold reQuad
    rw [← Complex.re_sum]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : c i = c j
    · rw [Finset.sum_eq_single (c i)]
      · simp [blockMat, huc, h]
      · intro m _ hm
        have : ¬ c i = m := fun e => hm e.symm
        simp [huc, this]
      · intro hn; exact absurd (hmem i) hn
    · rw [Finset.sum_eq_zero]
      · simp [blockMat, h]
      · intro m _
        by_cases h1 : c i = m
        · have : ¬ c j = m := fun e => h (h1.trans e.symm)
          simp [huc, this]
        · simp [huc, h1]
  have hn : sqNorm u = ∑ m ∈ S, sqNorm (uc m) := by
    unfold sqNorm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (c i)]
    · simp [huc]
    · intro m _ hm
      have : ¬ c i = m := fun e => hm e.symm
      simp [huc, this]
    · intro hn; exact absurd (hmem i) hn
  rw [hq, hn, Finset.mul_sum]
  exact Finset.sum_le_sum fun m _ => hA (uc m)

omit [Fintype ι] [DecidableEq ι] in
/-- For a convex cut weight, `cutMat` is the convex combination of block compressions. -/
theorem cutMat_cutWeight {J : Type*} [Fintype J] (lam : J → ℝ) (c : J → ι → ℕ)
    (A : Matrix ι ι ℂ) :
    cutMat (cutWeight lam c) A = ∑ j, (lam j : ℂ) • blockMat (c j) A := by
  ext x y
  simp only [cutMat, cutWeight, blockMat, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : c j x = c j y <;> simp [h]

omit [DecidableEq ι] in
/-- A convex combination of block compressions of a coercive matrix is coercive with the same
constant. -/
theorem isCoercive_cutMat_cutWeight {J : Type*} [Fintype J] {lam : J → ℝ}
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) (c : J → ι → ℕ) {A : Matrix ι ι ℂ} {γ : ℝ}
    (hA : IsCoercive A γ) : IsCoercive (cutMat (cutWeight lam c) A) γ := by
  intro u
  rw [cutMat_cutWeight, reQuad_sum]
  simp only [reQuad_real_smul]
  calc γ * sqNorm u = (∑ j, lam j) * (γ * sqNorm u) := by rw [h1, one_mul]
    _ = ∑ j, lam j * (γ * sqNorm u) := Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left ((hA.compress (c j)) u) (h0 j)

omit [Fintype ι] [DecidableEq ι] in
theorem cutWeight_nonneg {J : Type*} [Fintype J] {lam : J → ℝ} (h0 : ∀ j, 0 ≤ lam j)
    (c : J → ι → ℕ) (x y : ι) : 0 ≤ cutWeight lam c x y :=
  Finset.sum_nonneg fun j _ => mul_nonneg (h0 j) (by split_ifs <;> norm_num)

omit [Fintype ι] [DecidableEq ι] in
theorem cutWeight_le_one {J : Type*} [Fintype J] {lam : J → ℝ} (h0 : ∀ j, 0 ≤ lam j)
    (h1 : ∑ j, lam j = 1) (c : J → ι → ℕ) (x y : ι) : cutWeight lam c x y ≤ 1 := by
  calc cutWeight lam c x y ≤ ∑ j, lam j :=
        Finset.sum_le_sum fun j _ => by
          have := h0 j
          split_ifs <;> linarith
    _ = 1 := h1

omit [Fintype ι] [DecidableEq ι] in
theorem cutWeight_self {J : Type*} [Fintype J] {lam : J → ℝ} (h1 : ∑ j, lam j = 1)
    (c : J → ι → ℕ) (x : ι) : cutWeight lam c x x = 1 := by
  simp [cutWeight, h1]

omit [Fintype ι] [DecidableEq ι] in
theorem cutWeight_comm {J : Type*} [Fintype J] (lam : J → ℝ) (c : J → ι → ℕ) (x y : ι) :
    cutWeight lam c x y = cutWeight lam c y x := by
  unfold cutWeight
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eq_comm (a := c j x)]

omit [Fintype ι] [DecidableEq ι] in
theorem norm_cutMat_le {s : ι → ι → ℝ} (h0 : ∀ x y, 0 ≤ s x y) (h1 : ∀ x y, s x y ≤ 1)
    (A : Matrix ι ι ℂ) (x y : ι) : ‖cutMat s A x y‖ ≤ ‖A x y‖ := by
  simp only [cutMat, Matrix.of_apply, smul_eq_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (h0 x y)]
  calc s x y * ‖A x y‖ ≤ 1 * ‖A x y‖ :=
        mul_le_mul_of_nonneg_right (h1 x y) (norm_nonneg _)
    _ = _ := one_mul _

end Generic

section Locality

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Cut-locality** (generic): let `B, B'` be invertible and block diagonal along the region `X`
(no entries between `X` and its complement), with the same entries on `X × X`.  Then their inverses
agree on `X × X`. -/
theorem inv_eq_on_region {B B' : Matrix ι ι ℂ} (hB : IsUnit B) (hB' : IsUnit B') (X : Set ι)
    [DecidablePred (· ∈ X)]
    (h1 : ∀ x ∈ X, ∀ y ∉ X, B x y = 0) (h2 : ∀ x ∉ X, ∀ y ∈ X, B x y = 0)
    (h1' : ∀ x ∈ X, ∀ y ∉ X, B' x y = 0) (h2' : ∀ x ∉ X, ∀ y ∈ X, B' x y = 0)
    (hXX : ∀ x ∈ X, ∀ y ∈ X, B x y = B' x y) {x y : ι} (hx : x ∈ X) (hy : y ∈ X) :
    B⁻¹ x y = B'⁻¹ x y := by
  set P : Matrix ι ι ℂ := Matrix.diagonal fun i => if i ∈ X then 1 else 0 with hP
  have hPP : P * P = P := by
    ext i j; simp only [hP, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  have comm : ∀ {C : Matrix ι ι ℂ}, (∀ x ∈ X, ∀ y ∉ X, C x y = 0) →
      (∀ x ∉ X, ∀ y ∈ X, C x y = 0) → C * P = P * C := by
    intro C ha hb
    ext i j
    simp only [hP, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp [hi, hj, ha, hb]
  have hBB : P * B * P = P * B' * P := by
    ext i j
    simp only [hP, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp [hi, hj, hXX]
  have hBG : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hB)
  have hBG' : B' * B'⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hB')
  have c1 := comm h1 h2
  have c2 := comm h1' h2'
  -- `B (P G' P) = P`
  have e1 : B * (P * B'⁻¹ * P) = P := by
    have : B * P = P * B * P :=
      calc B * P = P * B := c1
        _ = P * P * B := by rw [hPP]
        _ = P * (P * B) := mul_assoc _ _ _
        _ = P * (B * P) := by rw [c1]
        _ = P * B * P := (mul_assoc _ _ _).symm
    calc B * (P * B'⁻¹ * P) = (B * P) * B'⁻¹ * P := by simp only [mul_assoc]
      _ = (P * B * P) * B'⁻¹ * P := by rw [this]
      _ = (P * B' * P) * B'⁻¹ * P := by rw [hBB]
      _ = P * (B' * P) * B'⁻¹ * P := by simp only [mul_assoc]
      _ = P * (P * B') * B'⁻¹ * P := by rw [c2]
      _ = P * (P * (B' * B'⁻¹)) * P := by simp only [mul_assoc]
      _ = P := by rw [hBG', mul_one, hPP, hPP]
  have e2 : B * (P * B⁻¹ * P) = P := by
    calc B * (P * B⁻¹ * P) = (B * P) * B⁻¹ * P := by simp only [mul_assoc]
      _ = (P * B) * B⁻¹ * P := by rw [c1]
      _ = P * (B * B⁻¹) * P := by simp only [mul_assoc]
      _ = P := by rw [hBG, mul_one, hPP]
  have e3 : P * B'⁻¹ * P = P * B⁻¹ * P := by
    have := e1.trans e2.symm
    have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hB)
    calc P * B'⁻¹ * P = (B⁻¹ * B) * (P * B'⁻¹ * P) := by rw [hinv, one_mul]
      _ = B⁻¹ * (B * (P * B'⁻¹ * P)) := by rw [mul_assoc]
      _ = B⁻¹ * (B * (P * B⁻¹ * P)) := by rw [this]
      _ = P * B⁻¹ * P := by rw [← mul_assoc, hinv, one_mul]
  have := congrFun (congrFun e3 x) y
  simpa [hP, Matrix.mul_diagonal, Matrix.diagonal_mul, hx, hy] using this.symm

end Locality

section Final

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The cut operator: the entries of `finalOp` multiplied by the real weight `s x y`. -/
noncomputable def finalOpCut (s : L1Torus d N₀ → L1Torus d N₀ → ℝ) (v a : ℝ) :
    Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  Matrix.of fun x y => (s x y : ℂ) • finalOp d L N₀ k v a x y

theorem finalOpCut_eq_cutMat (s : L1Torus d N₀ → L1Torus d N₀ → ℝ) (v a : ℝ) :
    finalOpCut (d := d) (L := L) (k := k) s v a = cutMat s (finalOp d L N₀ k v a) := rfl

/-- `s ≡ 1` gives the full operator. -/
theorem finalOpCut_one (v a : ℝ) :
    finalOpCut (d := d) (L := L) (k := k) (fun _ _ => 1) v a = finalOp d L N₀ k v a := by
  ext x y; simp [finalOpCut]

private instance : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩

variable {J : Type*} [Fintype J] {lam : J → ℝ} {c : J → L1Torus d N₀ → ℕ}

/-- **Gap inherited by the convex class** (T1). -/
theorem finalOpCut_isCoercive (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) :
    IsCoercive (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a) (finalGap d L) :=
  isCoercive_cutMat_cutWeight h0 h1 c (finalMass_isCoercive hd hv0 hv1 ha hmass)

/-- **Entry decay inherited by the convex class** (T1). -/
theorem finalOpCut_entry_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1)
    (x y : L1Torus d N₀) :
    ‖finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a x y‖ ≤
      finalDecayC d L * Real.exp (-blockDecayRate d * dist x y) :=
  (norm_cutMat_le (cutWeight_nonneg h0 c) (cutWeight_le_one h0 h1 c) _ x y).trans
    (finalMass_entry_decay hd hk hv0 ha1 ha2 x y)

/-- **Resolvent decay of the cut operator** (T2): for every `t ≥ 0`, `finalOpCut s + t` is
invertible and `|(finalOpCut s + t)⁻¹_{xy}| ≤ 2/(g_* + t) exp(-r_* dist x y)`, with the constants
of `finalOp`, for every convex cut weight and every torus. -/
theorem finalOpCut_resolvent_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a + (t : ℂ) •
        (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)) ∧
      ∀ x y : L1Torus d N₀,
        ‖(finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a + (t : ℂ) •
            (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y‖ ≤
          2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hr := blockDecayRate_pos hd
  have hK : ∀ x : L1Torus d N₀, ∑ y, Real.exp (-(blockDecayRate d / 4) * dist x y) ≤
      ballConst d (blockDecayRate d / 4) :=
    fun x => ballSum_L1Torus (d := d) (m := N₀) (by positivity) x
  have hκ : 0 ≤ ballConst d (blockDecayRate d / 4) := ballConst_decay_nonneg (by positivity)
  have := combesThomas (c₀ := finalDecayC d L) (δ₀ := blockDecayRate d) (γ₀ := finalGap d L)
    (κ := ballConst d (blockDecayRate d / 4)) (finalDecayC_pos hd).le hr (finalGap_pos hL) hκ
    (finalOpCut_entry_decay (c := c) hd hk hv0 ha1 ha2 h0 h1) hK
    (finalOpCut_isCoercive (c := c) hd hv0 hv1 ha1 hmass h0 h1) ht
  refine ⟨this.1, fun x y => ?_⟩
  exact (this.2 x y).trans_eq (by simp only [finalRate, div_eq_mul_inv])

/-- Inverse decay of the cut operator (`t = 0`). -/
theorem finalOpCut_inverse_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) (x y : L1Torus d N₀) :
    ‖(finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a)⁻¹ x y‖ ≤
      2 / finalGap d L * Real.exp (-finalRate d L * dist x y) := by
  have h := (finalOpCut_resolvent_decay (L := L) (N₀ := N₀) (k := k) (c := c) hd hk hv0 hv1
    ha1 ha2 hmass h0 h1 (le_refl (0 : ℝ))).2 x y
  simpa using h

/-- `ResOK` for the cut operator. -/
theorem finalOpCut_resOK (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) :
    Localization.ResOK (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a) := by
  intro x hx
  have := (finalOpCut_resolvent_decay (L := L) (N₀ := N₀) (k := k) (c := c) hd hk hv0 hv1 ha1
    ha2 hmass h0 h1 hx).1
  rwa [add_comm] at this

/-- `sqrtMat` of the cut operator is its inverse square root. -/
theorem finalOpCut_sqrt_mul_self (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) :
    Localization.sqrtMat (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a) *
      Localization.sqrtMat (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a) =
      (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a)⁻¹ :=
  Localization.sqrtMat_mul_self (finalOpCut_resOK (c := c) hd hk hv0 hv1 ha1 ha2 hmass h0 h1)

/-- **Inverse square root decay of the cut operator** (T2), same constants as `finalOp`. -/
theorem finalOpCut_sqrt_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) (x y : L1Torus d N₀) :
    ‖Localization.sqrtMat (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a) x y‖ ≤
      2 / Real.sqrt (finalGap d L) * Real.exp (-finalRate d L * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  set A := finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a with hAdef
  set B0 : ℝ := 2 * Real.exp (-finalRate d L * dist x y) with hB0
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  unfold Localization.sqrtMat
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold Localization.intMat
  have hint : Integrable (fun s : ℝ => B0 * (s ^ (-(1 / 2 : ℝ)) * (finalGap d L + s)⁻¹))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Localization.integrableOn_rpow_inv_add hg).const_mul B0
  have hbound := norm_integral_le_of_norm_le
    (f := fun s : ℝ => (((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((s : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + A)⁻¹) x y)
    hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs => by
      have hs0 : 0 < s := mem_Ioi.mp hs
      have h3 : 0 < s ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hs0 _
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h3.le]
      have := (finalOpCut_resolvent_decay (L := L) (N₀ := N₀) (k := k) (c := c) hd hk hv0 hv1
        ha1 ha2 hmass h0 h1 hs0.le).2 x y
      rw [add_comm] at this
      calc s ^ (-(1 / 2 : ℝ)) * ‖((s : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) +
              A)⁻¹ x y‖
          ≤ s ^ (-(1 / 2 : ℝ)) * (B0 * (finalGap d L + s)⁻¹) := by
            refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) h3.le
            rw [hB0]; ring
        _ = _ := by ring))
  rw [integral_const_mul, Localization.integral_rpow_inv_add hg] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 hg
  rw [abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖∫ s in Ioi (0 : ℝ), (((s ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((s : ℂ) • (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) + A)⁻¹) x y‖
      ≤ 1 / Real.pi * (B0 * (Real.pi / Real.sqrt (finalGap d L))) := by gcongr
    _ = _ := by rw [hB0]; field_simp

/-- **Cut-locality** (T3): two convex cut weights that agree on `X × X` and vanish between `X`
and its complement have the same resolvent on `X × X`, for every `t ≥ 0`. -/
theorem finalOpCut_resolvent_eq_on {J' : Type*} [Fintype J'] {lam' : J' → ℝ}
    {c' : J' → L1Torus d N₀ → ℕ} (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (h0 : ∀ j, 0 ≤ lam j) (h1 : ∑ j, lam j = 1) (h0' : ∀ j, 0 ≤ lam' j) (h1' : ∑ j, lam' j = 1)
    (X : Set (L1Torus d N₀)) [DecidablePred (· ∈ X)]
    (hcut : ∀ x ∈ X, ∀ y ∉ X, cutWeight lam c x y = 0)
    (hcut' : ∀ x ∈ X, ∀ y ∉ X, cutWeight lam' c' x y = 0)
    (hagree : ∀ x ∈ X, ∀ y ∈ X, cutWeight lam c x y = cutWeight lam' c' x y)
    {t : ℝ} (ht : 0 ≤ t) {x y : L1Torus d N₀} (hx : x ∈ X) (hy : y ∈ X) :
    (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam c) v a + (t : ℂ) •
        (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y =
      (finalOpCut (d := d) (L := L) (k := k) (cutWeight lam' c') v a + (t : ℂ) •
        (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y := by
  refine inv_eq_on_region (finalOpCut_resolvent_decay (c := c) hd hk hv0 hv1 ha1 ha2 hmass
    h0 h1 ht).1 (finalOpCut_resolvent_decay (c := c') hd hk hv0 hv1 ha1 ha2 hmass h0' h1' ht).1
    X ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x hx y hy
    simp [finalOpCut, hcut x hx y hy, Matrix.one_apply_ne (ne_of_mem_of_not_mem hx hy)]
  · intro x hx y hy
    have : cutWeight lam c x y = 0 := by rw [cutWeight_comm]; exact hcut y hy x hx
    simp [finalOpCut, this, Matrix.one_apply_ne (ne_of_mem_of_not_mem hy hx).symm]
  · intro x hx y hy
    simp [finalOpCut, hcut' x hx y hy, Matrix.one_apply_ne (ne_of_mem_of_not_mem hx hy)]
  · intro x hx y hy
    have : cutWeight lam' c' x y = 0 := by rw [cutWeight_comm]; exact hcut' y hy x hx
    simp [finalOpCut, this, Matrix.one_apply_ne (ne_of_mem_of_not_mem hy hx).symm]
  · intro x hx y hy
    simp [finalOpCut, hagree x hx y hy]

/-- The two-cell partition `{X, Xᶜ}` interpolated with the trivial one-cell partition: the weights
`λ` and `1 - λ` on the labellings `x ↦ 0` and `x ↦ 1[x ∈ X]`. -/
noncomputable def twoCellLam (l : ℝ) : Fin 2 → ℝ := ![l, 1 - l]

/-- The labellings of the one-cell and the two-cell partition. -/
noncomputable def twoCellLabel (X : Set (L1Torus d N₀)) [DecidablePred (· ∈ X)] :
    Fin 2 → L1Torus d N₀ → ℕ := ![fun _ => 0, fun x => if x ∈ X then 1 else 0]

omit [NeZero N₀] in
theorem cutWeight_twoCell (l : ℝ) (X : Set (L1Torus d N₀)) [DecidablePred (· ∈ X)]
    (x y : L1Torus d N₀) :
    cutWeight (twoCellLam l) (twoCellLabel X) x y =
      l + (1 - l) * (if (x ∈ X ↔ y ∈ X) then 1 else 0) := by
  simp only [cutWeight, twoCellLam, twoCellLabel, Fin.sum_univ_two]
  by_cases hx : x ∈ X <;> by_cases hy : y ∈ X <;> simp [hx, hy]

/-- **Non-vacuity** (T4): for `0 ≤ λ ≤ 1` and any region `X`, the interpolation of the full
operator and the operator decoupled across `∂X` is in the convex class; its weight is `1` on
pairs on the same side and `λ` across.  In particular for `λ < 1` it differs from `s ≡ 1` when
`X` and its complement are both nonempty, and for `λ = 0` it vanishes across `X`. -/
theorem twoCell_mem_convexClass {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    (∀ j, 0 ≤ twoCellLam l j) ∧ ∑ j, twoCellLam l j = 1 := by
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases j <;> simp [twoCellLam] <;> linarith
  · simp [twoCellLam, Fin.sum_univ_two]

omit [NeZero N₀] in
theorem cutWeight_twoCell_cross (l : ℝ) (X : Set (L1Torus d N₀)) [DecidablePred (· ∈ X)]
    {x y : L1Torus d N₀} (hx : x ∈ X) (hy : y ∉ X) :
    cutWeight (twoCellLam l) (twoCellLabel X) x y = l := by
  rw [cutWeight_twoCell]; simp [hx, hy]

omit [NeZero N₀] in
theorem cutWeight_twoCell_same (l : ℝ) (X : Set (L1Torus d N₀)) [DecidablePred (· ∈ X)]
    {x y : L1Torus d N₀} (h : x ∈ X ↔ y ∈ X) :
    cutWeight (twoCellLam l) (twoCellLabel X) x y = 1 := by
  rw [cutWeight_twoCell]; simp [h]

end Final

end Balaban.Green
