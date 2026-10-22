/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocWhiten
public import Balaban.Green.FinalBoxLocRegion

/-!
# The regional localized square root (A6-3, `D_{B,Ω}`, B-1″)

For a region `Ω` of coarse sites (B3: the `k`-blocks over the cubes of `Z_Aᶜ` far from `Z_A`), the
regional Hessian is the principal (Dirichlet) block on `Ω × Fin N` of the final Hessian.  Its
localized square root `finalWhitenReg Ω` takes row `p` from the block-diagonal extension
`regOp Ω (pairOp p) g_*` of the principal block on `Ω` of the operator of the local pair of `p`:

* `finalWhitenReg_univ`: `Ω = univ` gives `finalWhiten`;
* `finalWhitenReg_eq_zero_of_mixed`: the rows in `Ω` do not read the complement and conversely
  (block diagonal);
* `finalWhitenRegBlock`: the block on the subtype `Ω × Fin N` (`regIdx`), the matrix of the regional
  change of variables; `finalHessianRegBlock = hessC a (finalOp|_Ω) h` the regional Hessian;
  `hessC_regOp_submatrix` (the block of the extended Hessian is the regional Hessian) and
  `boxCutU_one_regOp_submatrix` (at `s = 1` the block is `(D|_Ω)^{-1/2}`);
* the row error `norm_finalWhitenReg_sub_le`, the mismatch smallness
  `sum_finalWhitenRegMismatch_le` (the bound `whitenMismatchBound` of `finalWhiten`), its block
  `finalWhitenRegBlock_mismatch_eq`, and invertibility of the full matrix and of the block
  (`exists_isUnit_finalWhitenReg`), with the `CutOpHyp` constants of `finalOp`.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

section Aux

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

omit [NeZero N₀] in
theorem finalGap_le_finalDecayC (hd : 0 < d) : finalGap d L ≤ finalDecayC d L := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hC := blockDecayConst_pos (L := L) hd
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : finalGap d L ≤ 1 := by
    unfold finalGap
    rw [div_le_one (by positivity)]
    nlinarith
  unfold finalDecayC
  linarith

theorem finalOp_transpose (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (ha : 0 < a) :
    (finalOp d L N₀ k v a)ᵀ = finalOp d L N₀ k v a := by
  ext x y
  have h := congrFun (congrFun (unconstrainedUnitOperator_transpose (mul_comm N₀ (L ^ k))
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k) hd hv0 ha) x) y
  exact congrArg (fun r : ℝ => (r : ℂ)) h

end Aux

section RegAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem regOp_transpose (Ω : Finset ι) (U : Matrix ι ι ℂ) (g : ℝ) :
    (regOp Ω U g)ᵀ = regOp Ω Uᵀ g := by
  ext x y
  rw [Matrix.transpose_apply, regOp_apply, regOp_apply, Matrix.transpose_apply]
  by_cases hx : x ∈ Ω <;> by_cases hy : y ∈ Ω <;> by_cases hxy : x = y <;> simp_all [eq_comm]

theorem norm_regOp_sub_le (Ω : Finset ι) (U₁ U₂ : Matrix ι ι ℂ) (g : ℝ) (x y : ι) :
    ‖regOp Ω U₁ g x y - regOp Ω U₂ g x y‖ ≤ ‖U₁ x y - U₂ x y‖ := by
  rw [regOp_apply, regOp_apply]
  split_ifs <;> simp

/-- The regional Hessian `hessC a (regOp Ω U g) h` does not mix `Ω` and its complement. -/
theorem hessC_regOp_eq_zero {N : ℕ} (a : ℂ) (Ω : Finset ι) (U : Matrix ι ι ℂ) (g : ℝ)
    (h : Fin N → ℂ) {p q : ι × Fin N} (hpq : (p.1 ∈ Ω ∧ q.1 ∉ Ω) ∨ (p.1 ∉ Ω ∧ q.1 ∈ Ω)) :
    hessC N a (regOp Ω U g) h p q = 0 := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  have hxy : x ≠ y := by
    rintro rfl
    rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> contradiction
  rw [hessC_apply, regOp_apply]
  have h1 : ¬ (x ∈ Ω ∧ y ∈ Ω) := by
    rcases hpq with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact fun h => h2 h.2
    · exact fun h => h1 h.1
  have h2 : ¬ (x = y ∧ x ∉ Ω) := fun h => hxy h.1
  rw [ite_eq_right_of_eq_false _ _ (eq_false hxy), ite_eq_right_of_eq_false _ _ (eq_false h1),
    ite_eq_right_of_eq_false _ _ (eq_false h2)]
  ring

end RegAux

section Reg

variable {d L N₀ k M N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- The sites `Ω × Fin N` inside `L1Torus × Fin N`. -/
def regIdx (Ω : Finset (L1Torus d N₀)) (N : ℕ) : Ω × Fin N → L1Torus d N₀ × Fin N :=
  fun p => (p.1, p.2)

omit [NeZero N₀] in
theorem regIdx_injective (Ω : Finset (L1Torus d N₀)) (N : ℕ) : Function.Injective (regIdx Ω N) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [regIdx, Prod.mk.injEq] at h
  rw [Subtype.ext h.1, h.2]

omit [NeZero N₀] in
theorem not_mem_of_not_mem_range_regIdx {Ω : Finset (L1Torus d N₀)} {z : L1Torus d N₀ × Fin N}
    (hz : z ∉ Set.range (regIdx Ω N)) : z.1 ∉ Ω := fun h => hz ⟨(⟨z.1, h⟩, z.2), rfl⟩

/-- **The regional localized square root** (`D_{B,Ω}`): row `p` is row `p` of the cut family of
the block-diagonal extension `regOp Ω (pairOp p) g_*` of the principal block on `Ω` of the operator
of the local pair of `p`, at the parameters `1` on `locDom p`. -/
noncomputable def finalWhitenReg (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℂ) (D m : ℕ) :
    Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  whitenOf d N₀ M a (fun p => regOp Ω (pairOp d L N₀ k M N v a D m p) (finalGap d L)) h D
    (fun _ => 1)

/-- The regional localized square root on the subtype `Ω × Fin N` (the matrix of the regional
change of variables). -/
noncomputable def finalWhitenRegBlock (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℂ) (D m : ℕ) : Matrix (Ω × Fin N) (Ω × Fin N) ℂ :=
  (finalWhitenReg d L N₀ k M v a Ω h D m).submatrix (regIdx Ω N) (regIdx Ω N)

/-- **The regional final Hessian**: the principal block on `Ω × Fin N` of the final Hessian,
`hessC a (finalOp|_Ω) h`. -/
noncomputable def finalHessianRegBlock (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℂ) : Matrix (Ω × Fin N) (Ω × Fin N) ℂ :=
  hessC N (a : ℂ) (restrictOp (finalOp d L N₀ k v a) Ω) h

/-- For `Ω` the whole torus the regional square root is `finalWhiten`. -/
theorem finalWhitenReg_univ (h : Fin N → ℂ) (D m : ℕ) :
    finalWhitenReg d L N₀ k M v a Finset.univ h D m = finalWhiten d L N₀ k M v a h D m := by
  unfold finalWhitenReg finalWhiten
  simp only [regOp_univ]

/-- **Block diagonality**: the rows in `Ω` do not read the complement, and conversely. -/
theorem finalWhitenReg_eq_zero_of_mixed (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℂ) (D m : ℕ)
    {p q : L1Torus d N₀ × Fin N} (hpq : (p.1 ∈ Ω ∧ q.1 ∉ Ω) ∨ (p.1 ∉ Ω ∧ q.1 ∈ Ω)) :
    finalWhitenReg d L N₀ k M v a Ω h D m p q = 0 :=
  boxCutU_regOp_eq_zero a Ω _ _ h _ hpq

/-- **The regional square root is real at a real `h`.** -/
theorem finalWhitenReg_real (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℝ) (D m : ℕ)
    (P Q : L1Torus d N₀ × Fin N) :
    (starRingEnd ℂ) (finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m P Q) =
      finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m P Q :=
  whitenOf_real (fun p => conjM_regOp (conjM_map_ofReal (ι := L1Torus d N₀)
    (dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ (pairSites d L N₀ k M N D m p) v a)) Ω _)
    h D P Q

/-- The real matrix of the regional square root. -/
noncomputable def finalWhitenRegR (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℂ) (D m : ℕ) :
    Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℝ :=
  Matrix.of fun p q => (finalWhitenReg d L N₀ k M v a Ω h D m p q).re

theorem finalWhitenRegR_map (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℝ) (D m : ℕ) :
    (finalWhitenRegR d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m).map (algebraMap ℝ ℂ) =
      finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m := by
  ext P Q
  simp only [Matrix.map_apply, finalWhitenRegR, Matrix.of_apply, Complex.coe_algebraMap]
  exact Complex.conj_eq_iff_re.1 (finalWhitenReg_real Ω h D m P Q)

theorem finalWhitenRegR_univ (h : Fin N → ℂ) (D m : ℕ) :
    finalWhitenRegR d L N₀ k M v a Finset.univ h D m = finalWhitenR d L N₀ k M v a h D m := by
  unfold finalWhitenRegR finalWhitenR
  rw [finalWhitenReg_univ]

/-- The block of the extended Hessian is the regional Hessian. -/
theorem hessC_regOp_submatrix (a : ℂ) (Ω : Finset (L1Torus d N₀))
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (g : ℝ) (h : Fin N → ℂ) :
    (hessC N a (regOp Ω U g) h).submatrix (regIdx Ω N) (regIdx Ω N) =
      hessC N a (restrictOp U Ω) h := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [Matrix.submatrix_apply, regIdx, hessC_apply, regOp_apply]
  have h1 : (x : L1Torus d N₀) ∈ Ω ∧ (y : L1Torus d N₀) ∈ Ω := ⟨x.2, y.2⟩
  have h2 : ¬ ((x : L1Torus d N₀) = y ∧ (x : L1Torus d N₀) ∉ Ω) := fun h => h.2 x.2
  rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
    add_zero]
  show _ + U x y * _ = _ + U x y * _
  congr 2
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- **At `s = 1` the block of the cut family is the inverse square root of the regional Hessian**:
`(boxCutU (regOp Ω U g) 1)|_{Ω × Fin N} = (hessC a (U|_Ω) h)^{-1/2}`. -/
theorem boxCutU_one_regOp_submatrix [NeZero N] (Ω : Finset (L1Torus d N₀)) [Nonempty Ω]
    {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {g A δ ε κ : ℝ}
    (hU : CutOpHyp d N₀ M U g A δ ε κ) (hgA : g ≤ A) (ha : 0 < a) {h : Fin N → ℂ}
    (hs : ∑ i, h i ^ 2 ≠ 0) :
    (boxCutU d N₀ M a (regOp Ω U g) h (fun _ => 1)).submatrix (regIdx Ω N) (regIdx Ω N) =
      Localization.sqrtMat (hessC N (a : ℂ) (restrictOp U Ω) h) := by
  have : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩
  have hR := cutOpHyp_regOp hU hgA Ω
  have hres := resOK_of_isCoercive hR.hg hR.coercive
  have hresΩ : Localization.ResOK (restrictOp U Ω) :=
    resOK_of_isCoercive hU.hg (isCoercive_restrictOp hU.coercive Ω)
  rw [boxCutU_one hR ha hs, (sqrtMat_hessC ha hres hs).2, (sqrtMat_hessC ha hresΩ hs).2]
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [Matrix.submatrix_apply, regIdx, Matrix.add_apply, Matrix.smul_apply,
    liftOp_mul_one_sub_projHC_apply, projHC_apply]
  have hsq := congrFun (congrFun (sqrtMat_regOp_submatrix Ω U g hres) x) y
  simp only [Matrix.submatrix_apply] at hsq
  rw [hsq]
  congr 2
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy]

/-- **The row error of the regional square root, entrywise**: against
`boxCutU (regOp Ω finalOp g_*) 1`, the bound of `norm_finalWhiten_sub_le`. -/
theorem norm_finalWhitenReg_sub_le {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (Ω : Finset (L1Torus d N₀)) (D m : ℕ)
    (P Q : L1Torus d N₀ × Fin N) :
    ‖finalWhitenReg d L N₀ k M v a Ω h D m P Q -
        boxCutU d N₀ M a (regOp Ω (finalOp d L N₀ k v a) (finalGap d L)) h (fun _ => 1) P Q‖ ≤
      (boxCutConst d L 1 a κ p * (7 ^ d * whitenTail (16 ^ d) (κ - 1) D) +
        pairErrConst d L v a p * Real.exp (-(pdEps d L / 4 * m))) *
        Real.exp (-r * dist P.1 Q.1) := by
  obtain ⟨hd, hk, hv0, hv1, ha1, ha2, hmass, hM, ht⟩ := hC
  have hκ : 1 ≤ κ := ht.1
  have hκ0 : 0 ≤ κ := by linarith
  have hδ := blockDecayRate_pos hd
  have hq : ((16 ^ d : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1)) < 1 := by
    linarith [ratio_le_of_ties ht]
  have hgA := finalGap_le_finalDecayC (L := L) hd
  exact norm_whitenOf_sub_le hd hM
    (fun P => cutOpHyp_regOp (cutOpHyp_pairOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 ht.2.1 ht.2.2.1
      D m P) hgA Ω)
    (cutOpHyp_regOp (cutOpHyp_finalOp (N₀ := N₀) (k := k) (v := v) (a := a) hd hk hv0 hv1 ha1 ha2
      hmass hM hκ0 ht.2.1 ht.2.2.1) hgA Ω) hκ hq
    (by unfold dirichletCompConst; have := ballConst_decay_nonneg (d := d) hδ; positivity)
    (m : ℝ) (fun P u w => (norm_regOp_sub_le Ω _ _ _ u w).trans
      (norm_pairOp_sub_finalOp_le hd hk hv0 ha1 ha2 hM D m P u w)) hp hr0 hr D P Q

/-- **Smallness of the regional mismatch** `Lᵀ D_Ω L - 1` (full index, `D_Ω` the extended regional
Hessian): the bound `whitenMismatchBound` of `finalWhiten`. -/
theorem sum_finalWhitenRegMismatch_le [NeZero N] {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) {p : ℝ}
    (hp : ∀ i j, ‖spinProj (fun i => (h i : ℂ)) i j‖ ≤ p) {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps d L / 8) (Ω : Finset (L1Torus d N₀)) (D m : ℕ)
    (P : L1Torus d N₀ × Fin N) :
    ∑ Q, Real.exp (r' * dist P.1 Q.1) *
        ‖((finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m)ᵀ *
          hessC N (a : ℂ) (regOp Ω (finalOp d L N₀ k v a) (finalGap d L)) (fun i => (h i : ℂ)) *
          finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m - 1) P Q‖ ≤
      whitenMismatchBound d L N v a κ p r r' D m := by
  have hC' := hC
  obtain ⟨hd, hk, hv0, hv1, ha1, ha2, hmass, hM, ht⟩ := hC'
  have hκ0 : 0 ≤ κ := by linarith [ht.1]
  have hr0 : 0 ≤ r := by linarith
  have ha0 : 0 < a := by linarith
  have hεδ : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hrδ : r' < blockDecayRate d := by linarith
  have hgA := finalGap_le_finalDecayC (L := L) hd
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hU₀ := cutOpHyp_regOp (cutOpHyp_finalOp (N₀ := N₀) (k := k) (v := v) (a := a) hd hk hv0
    hv1 ha1 ha2 hmass hM hκ0 ht.2.1 ht.2.2.1) hgA Ω
  have hs : ∑ i, ((h i : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : ∑ i, ((h i : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast hh
    rw [this]; exact one_ne_zero
  have hT : (regOp Ω (finalOp d L N₀ k v a) (finalGap d L))ᵀ =
      regOp Ω (finalOp d L N₀ k v a) (finalGap d L) := by
    rw [regOp_transpose, finalOp_transpose hd hv0 ha0]
  have hEe : ∀ P Q, ‖(finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m -
      boxCutU d N₀ M a (regOp Ω (finalOp d L N₀ k v a) (finalGap d L)) (fun i => (h i : ℂ))
        (fun _ => 1)) P Q‖ ≤
      (boxCutConst d L 1 a κ p * (7 ^ d * whitenTail (16 ^ d) (κ - 1) D) +
        pairErrConst d L v a p * Real.exp (-(pdEps d L / 4 * m))) *
        Real.exp (-r * dist P.1 Q.1) := fun P Q => by
    rw [Matrix.sub_apply]
    exact norm_finalWhitenReg_sub_le hC hp hr0 hr Ω D m P Q
  exact sum_mismatch_le_of (boxCutU_one_transpose_mul_mul hU₀ hT ha0 hs) hr'0 hr' hrδ
    (fun P Q => (norm_boxCutU_apply_le hU₀ hp (norm_one_le_exp hκ0) hr0 hr P Q).trans
      (le_of_eq (by unfold boxCutConst; push_cast; ring)))
    (fun P Q => norm_hessC_apply_le (norm_regOp_apply_le
      (finalMass_entry_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2)
      (finalGap_pos hL).le hgA Ω) ha0.le hp P Q)
    (fun P => sum_exp_mul_le_of_entry hEe hr' P)
    (fun P => sum_exp_mul_le_of_entry (transpose_entry_le hEe) hr' P) P

/-- **The block of the regional mismatch** is the mismatch of the blocks:
`(Lᵀ D_Ω L - 1)|_{Ω × Fin N} = L_Ωᵀ D_{B,Ω} L_Ω - 1` (all three matrices are block diagonal). -/
theorem finalWhitenRegBlock_mismatch_eq (Ω : Finset (L1Torus d N₀)) (h : Fin N → ℂ) (D m : ℕ) :
    ((finalWhitenReg d L N₀ k M v a Ω h D m)ᵀ *
        hessC N (a : ℂ) (regOp Ω (finalOp d L N₀ k v a) (finalGap d L)) h *
        finalWhitenReg d L N₀ k M v a Ω h D m - 1).submatrix (regIdx Ω N) (regIdx Ω N) =
      (finalWhitenRegBlock d L N₀ k M v a Ω h D m)ᵀ * finalHessianRegBlock d L N₀ k v a Ω h *
        finalWhitenRegBlock d L N₀ k M v a Ω h D m - 1 := by
  rw [mismatch_submatrix_of_block (regIdx Ω N) (regIdx_injective Ω N) _ _
    (fun x z hz => finalWhitenReg_eq_zero_of_mixed Ω h D m
      (Or.inr ⟨not_mem_of_not_mem_range_regIdx hz, x.1.2⟩))
    (fun x z hz => hessC_regOp_eq_zero _ Ω _ _ h
      (Or.inl ⟨x.1.2, not_mem_of_not_mem_range_regIdx hz⟩)),
    hessC_regOp_submatrix]
  rfl

/-- **Invertibility of the regional square root and of its block** (conditional form): if the
mismatch bound is below `1`, the full matrix and its block on `Ω × Fin N` are invertible. -/
theorem isUnit_finalWhitenReg_of_lt_one [NeZero N] {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) {p : ℝ}
    (hp : ∀ i j, ‖spinProj (fun i => (h i : ℂ)) i j‖ ≤ p) {r r' : ℝ} (hr'0 : 0 ≤ r')
    (hr' : r' < r) (hr : r ≤ pdEps d L / 8) (Ω : Finset (L1Torus d N₀)) (D m : ℕ)
    (hsmall : whitenMismatchBound d L N v a κ p r r' D m < 1) :
    IsUnit (finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m) ∧
      IsUnit (finalWhitenRegBlock d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m) := by
  have hW := isUnit_of_mismatch_le hr'0
    (fun P => sum_finalWhitenRegMismatch_le hC hh hp hr'0 hr' hr Ω D m P) hsmall
  refine ⟨hW, ?_⟩
  have h1 := submatrix_mul_submatrix_inv (regIdx Ω N) (regIdx_injective Ω N) hW
    (fun x z hz => finalWhitenReg_eq_zero_of_mixed Ω _ D m
      (Or.inl ⟨x.1.2, not_mem_of_not_mem_range_regIdx hz⟩))
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse h1)

/-- **Invertibility of the regional square root and of its block**: for a real unit `h` and
`0 ≤ r' < r ≤ ε/8`, for every radius `D` and margin `m` beyond some `D₀` (the same `D₀` as for
`finalWhiten`, for every region `Ω`). -/
theorem exists_isUnit_finalWhitenReg [NeZero N] {κ α : ℝ} (hC : BoxCutConsts d L k M v a κ α)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) {r r' : ℝ} (hr'0 : 0 ≤ r') (hr' : r' < r)
    (hr : r ≤ pdEps d L / 8) :
    ∃ D₀ : ℕ, ∀ D m, D₀ ≤ D → D₀ ≤ m → ∀ Ω : Finset (L1Torus d N₀),
      IsUnit (finalWhitenReg d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m) ∧
        IsUnit (finalWhitenRegBlock d L N₀ k M v a Ω (fun i => (h i : ℂ)) D m) := by
  have hd := hC.hd
  have hεδ : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hrδ : r' < blockDecayRate d := by linarith
  obtain ⟨D₀, hD₀⟩ := exists_whitenRadius (N := N) (v := v) (a := a) hC.ties hd
    (by linarith [hC.ha1]) zero_le_one hr' hrδ (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨D₀, fun D m hD hm Ω => isUnit_finalWhitenReg_of_lt_one hC hh
    (norm_spinProj_ofReal_le_one hh) hr'0 hr' hr Ω D m (by linarith [hD₀ D m hD hm])⟩

end Reg

end Balaban.Green
