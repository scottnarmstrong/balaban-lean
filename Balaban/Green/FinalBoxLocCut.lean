/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCore
public import Balaban.Green.FinalConnectedSupport
public import Balaban.Green.FinalComplexHessian
public import Balaban.Polymer.TwoTorusFinal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cut family of the final Hessian and its decoupling (A6-3, box localization)

The cut family is proposed in FINALFAM (the papers print no formula; Roland question 18 pending).
For the final Hessian `D(h) = a P_h + (U ⊗ 1)(1 - P_h)` (`finalHessianC`, `U = finalOp`) put

  `boxCut(s) = a^{-1/2} (m(s) ⊗ 1) P_h + (taggedCfin(s) ⊗ 1)(1 - P_h)`,

where `m(s)` is the diagonal matrix `m(s)(x) = ∑_z s_z χ_z(x)` of the macro-cell partition of unity.
At `s = 1`, `m(1) = 1` and `taggedCfin 1 = sqrtMat U`, so `boxCut 1 = sqrtMat D(h)`
(`boxCut_one`, by `finalHessianC_sqrt_eq`).  The longitudinal part carries the parameters through
`m(s)` (rather than being `s`-independent), so that at parameters vanishing off `C` the whole family
lives on the region of `C`: this is what makes the coefficients exactly local and rooted.

* `boxCut_apply`: the entries, `a^{-1/2} [x = y] m(s)(x) P_h(i, j) + C_fin(s)(x, y) (δ_ij - P_h(i, j))`;
* `cutDecoupling_taggedCfin`, `cutDecoupling_boxCut`: the decoupling property `CutDecoupling` on the
  polydisc of radius `e^κ`, with the patches `macBox i` (resp. `macBox i × Fin N`);
* `boxCut_row_bound`: `∑_q ‖boxCut(s) p q‖ ≤ a^{-1/2} e^κ N p + B (1 + N p)` (`B` the row bound of
  `taggedCfin`, `p` a bound for the entries of `P_h`);
* `rootedExpansion_boxCut`: the rooted Lemma AE for a term `τ` reading the field on `S`, analytic and
  bounded by `M_τ` on the sup-norm ball of radius `r` around a centre `φ₀`, at the field
  `φ₀ + c · boxCut(s) w` with `‖w‖_∞ ≤ ρ`, `m = |c| B_box ρ < r`: the increment bound is
  `M_τ m / (r - m)`.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Scalar

variable {d N₀ M L k : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

theorem patchReg_macBox (C : Finset (MacIdx d N₀ M)) :
    patchReg (fun i => macBox d N₀ M i) C = macRegion d N₀ M C := by
  ext x; simp [patchReg, mem_macRegion]

/-- **The decoupling property of the Stieltjes square-root family** `taggedCfin` on the polydisc
of radius `e^κ`: the support property is `taggedCfinU_eq_zero_of_not_mem`, the splitting is
`taggedCfin_apply_split_of_separated`. -/
theorem cutDecoupling_taggedCfin (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    CutDecoupling (fun i => macBox d N₀ M i) (Real.exp κ)
      (fun s x y => taggedCfin d L N₀ k M v a s x y) where
  supp C s _ hsC x y h := by
    rw [patchReg_macBox]
    by_contra hc
    apply h
    rw [← taggedCfinU_finalOp]
    exact taggedCfinU_eq_zero_of_not_mem hM hd _ hsC hc
  split C A s hs hsC hAC hsep x y := by
    rw [patchReg_macBox, patchReg_macBox] at hsep
    exact taggedCfin_apply_split_of_separated hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hAC hsep
      (fun p => by simpa using (hs p).le) hsC x y

end Scalar

section Box

variable {d N₀ M L k N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- The parameter-weighted partition of unity `m(s)(x) = ∑_z s_z χ_z(x)` (`m(1) = 1`). -/
noncomputable def chiSum (d N₀ M : ℕ) [NeZero N₀] (s : MacIdx d N₀ M → ℂ) (x : L1Torus d N₀) :
    ℂ :=
  ∑ z, s z * ((macChi d N₀ M z x : ℝ) : ℂ)

/-- **The cut family of the final Hessian** (a construction proposed in FINALFAM):
`a^{-1/2} (m(s) ⊗ 1) P_h + (taggedCfin(s) ⊗ 1)(1 - P_h)`. -/
noncomputable def boxCut (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  ((1 / Real.sqrt a : ℝ) : ℂ) • (Multiscale.liftOp N (Matrix.diagonal (chiSum d N₀ M s)) *
      projHC h) +
    Multiscale.liftOp N (taggedCfin d L N₀ k M v a s) * (1 - projHC h)

omit [NeZero L] in
theorem liftOp_mul_idKron_apply (A : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    (S : Matrix (Fin N) (Fin N) ℂ) (x y : L1Torus d N₀) (i j : Fin N) :
    (Multiscale.liftOp N A * idKron S : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ)
      (x, i) (y, j) = A x y * S i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single i]
    · simp [Multiscale.liftOp, idKron]
    · intro l _ hl; simp [Multiscale.liftOp, Ne.symm hl]
    · simp
  · intro z _ hz
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [idKron, hz]
  · simp

omit [NeZero L] [NeZero N₀] in
theorem one_sub_projHC_eq_idKron (h : Fin N → ℂ) :
    (1 - projHC h : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ) =
      idKron (1 - spinProj h) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [Matrix.sub_apply, projHC, idKron, Matrix.one_apply, Prod.mk.injEq]
  by_cases hxy : x = y
  · subst hxy; by_cases hij : i = j <;> simp [hij]
  · simp [hxy]

/-- **The entries of the cut family.** -/
theorem boxCut_apply (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) (x y : L1Torus d N₀)
    (i j : Fin N) :
    boxCut d L N₀ k M v a h s (x, i) (y, j) =
      ((1 / Real.sqrt a : ℝ) : ℂ) * ((if x = y then chiSum d N₀ M s x else 0) * spinProj h i j) +
        taggedCfin d L N₀ k M v a s x y * ((if i = j then 1 else 0) - spinProj h i j) := by
  unfold boxCut
  rw [Matrix.add_apply, Matrix.smul_apply, one_sub_projHC_eq_idKron, projHC,
    liftOp_mul_idKron_apply, liftOp_mul_idKron_apply]
  simp only [Matrix.diagonal_apply, smul_eq_mul, Matrix.sub_apply, Matrix.one_apply]

/-- The patches of the cut family on `sites × Fin N`. -/
def spinBoxPatch (d N₀ M N : ℕ) [NeZero N₀] (i : MacIdx d N₀ M) :
    Set (L1Torus d N₀ × Fin N) :=
  {p | p.1 ∈ macBox d N₀ M i}

theorem mem_patchReg_spinBoxPatch {C : Finset (MacIdx d N₀ M)} {p : L1Torus d N₀ × Fin N} :
    p ∈ patchReg (spinBoxPatch d N₀ M N) C ↔ p.1 ∈ macRegion d N₀ M C := by
  simp [patchReg, spinBoxPatch, mem_macRegion]

theorem chiSum_split {C A : Finset (MacIdx d N₀ M)} {s : MacIdx d N₀ M → ℂ}
    (hsC : s ∈ supportedOn C) (x : L1Torus d N₀) :
    chiSum d N₀ M s x = chiSum d N₀ M (cutTo A s) x + chiSum d N₀ M (cutTo (C \ A) s) x := by
  unfold chiSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hzA : z ∈ A
  · have : z ∉ C \ A := fun h => (Finset.mem_sdiff.1 h).2 hzA
    simp [cutTo, hzA, this]
  · by_cases hzC : z ∈ C
    · have : z ∈ C \ A := Finset.mem_sdiff.2 ⟨hzC, hzA⟩
      simp [cutTo, hzA, this]
    · have : z ∉ C \ A := fun h => hzC (Finset.mem_sdiff.1 h).1
      simp [cutTo, hzA, this, hsC z hzC]

theorem mem_macRegion_of_chiSum_ne_zero (hM : 0 < M) {C : Finset (MacIdx d N₀ M)}
    {s : MacIdx d N₀ M → ℂ} (hsC : s ∈ supportedOn C) {x : L1Torus d N₀}
    (h : chiSum d N₀ M s x ≠ 0) : x ∈ macRegion d N₀ M C := by
  obtain ⟨z, -, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hs : s z ≠ 0 := left_ne_zero_of_mul hz
  have hc : macChi d N₀ M z x ≠ 0 := by
    intro h0; apply hz; simp [h0]
  have hzC : z ∈ C := by
    by_contra hzC; exact hs (hsC z hzC)
  exact mem_macRegion.2 ⟨z, hzC, macChi_mem_box hM hc⟩

omit [NeZero L] in
theorem chiSum_one (x : L1Torus d N₀) : chiSum d N₀ M (fun _ => 1) x = 1 := by
  unfold chiSum
  simp only [one_mul]
  rw [← Complex.ofReal_sum, macChi_sum, Complex.ofReal_one]

omit [NeZero L] in
theorem analyticOnNhd_chiSum (x : L1Torus d N₀) (U : Set (MacIdx d N₀ M → ℂ)) :
    AnalyticOnNhd ℂ (fun s => chiSum d N₀ M s x) U := by
  intro s _
  unfold chiSum
  refine Finset.analyticAt_fun_sum _ fun z _ => ?_
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : MacIdx d N₀ M => ℂ) z).analyticAt
    s).mul analyticAt_const

omit [NeZero L] in
theorem norm_chiSum_le {s : MacIdx d N₀ M → ℂ} {R : ℝ} (hs : ∀ z, ‖s z‖ ≤ R)
    (x : L1Torus d N₀) : ‖chiSum d N₀ M s x‖ ≤ R := by
  unfold chiSum
  calc ‖∑ z, s z * ((macChi d N₀ M z x : ℝ) : ℂ)‖
      ≤ ∑ z, ‖s z * ((macChi d N₀ M z x : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ z, R * macChi d N₀ M z x := by
        refine Finset.sum_le_sum fun z _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (macChi_nonneg z x)]
        exact mul_le_mul_of_nonneg_right (hs z) (macChi_nonneg z x)
    _ = R := by rw [← Finset.mul_sum, macChi_sum, mul_one]

variable (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
  (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
  (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
  (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
include hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ

/-- **The decoupling property of the cut family of the final Hessian.** -/
theorem cutDecoupling_boxCut (h : Fin N → ℂ) :
    CutDecoupling (spinBoxPatch d N₀ M N) (Real.exp κ)
      (fun s p q => boxCut d L N₀ k M v a h s p q) where
  supp C s hs hsC p q hne := by
    obtain ⟨x, i⟩ := p
    obtain ⟨y, j⟩ := q
    rw [boxCut_apply] at hne
    simp only [mem_patchReg_spinBoxPatch]
    by_cases hT : taggedCfin d L N₀ k M v a s x y = 0
    · rw [hT, zero_mul, add_zero] at hne
      have h1 : (if x = y then chiSum d N₀ M s x else 0) ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      by_cases hxy : x = y
      · subst hxy
        simp only [↓reduceIte] at h1
        have := mem_macRegion_of_chiSum_ne_zero hM hsC h1
        exact ⟨this, this⟩
      · exact absurd (by simp [hxy]) h1
    · exact (cutDecoupling_taggedCfin hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ).supp C s hs
        hsC x y hT |>.imp (by rw [patchReg_macBox]; exact id) (by rw [patchReg_macBox]; exact id)
  split C A s hs hsC hAC hsep p q := by
    obtain ⟨x, i⟩ := p
    obtain ⟨y, j⟩ := q
    have hsep' : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      exact Set.disjoint_left.1 hsep
        ((mem_patchReg_spinBoxPatch (p := (z, i))).2 hz)
        ((mem_patchReg_spinBoxPatch (p := (z, i))).2 hz')
    have hT : taggedCfin d L N₀ k M v a s x y =
        taggedCfin d L N₀ k M v a (cutTo A s) x y +
          taggedCfin d L N₀ k M v a (cutTo (C \ A) s) x y :=
      taggedCfin_apply_split_of_separated hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hAC hsep'
        (fun p => by simpa using (hs p).le) hsC x y
    rw [boxCut_apply, boxCut_apply, boxCut_apply, chiSum_split (A := A) hsC x, hT]
    split_ifs <;> ring

/-- **At `s = 1` the cut family is the principal inverse square root of the final Hessian.** -/
theorem boxCut_one [NeZero N] {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) :
    boxCut d L N₀ k M v a h (fun _ => 1) =
      Localization.sqrtMat (finalHessianC d L N₀ k v a h) := by
  rw [(finalHessianC_sqrt_eq hd hk hv0 hv1 ha1 ha2 hmass hs).2.1]
  unfold boxCut
  have hdiag : Matrix.diagonal (chiSum d N₀ M (fun _ => 1)) = 1 := by
    rw [show chiSum d N₀ M (fun _ => 1) = fun _ => 1 from funext (chiSum_one)]
    rfl
  rw [hdiag, Multiscale.liftOp_one, one_mul,
    taggedCfin_one hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ]

/-- **Analyticity of the entries of the cut family** on the polydisc of radius `e^κ`. -/
theorem analyticOnNhd_boxCut (h : Fin N → ℂ) (p q : L1Torus d N₀ × Fin N) :
    AnalyticOnNhd ℂ (fun s => boxCut d L N₀ k M v a h s p q)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  simp only [boxCut_apply]
  have hT : AnalyticOnNhd ℂ (fun s => taggedCfin d L N₀ k M v a s x y)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :=
    (taggedCfin_analyticOnNhd (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk hv0
      hv1 ha1 ha2 hmass hM hκ hMB hMκ x y).mono fun s hs p => by simpa using hs p
  intro s hs
  refine (analyticAt_const.mul ?_).add ((hT s hs).mul analyticAt_const)
  by_cases hxy : x = y
  · simp only [hxy, ↓reduceIte]
    exact (analyticOnNhd_chiSum y _ s hs).mul analyticAt_const
  · simp only [hxy, ↓reduceIte, zero_mul]
    exact analyticAt_const

/-- The row-sum constant of the cut family: `a^{-1/2} e^κ N p + B (1 + N p)`, `B` the row bound of
`taggedCfin` and `p` a bound for the entries of `P_h`. -/
noncomputable def boxCutConst (d L N : ℕ) (a κ p : ℝ) : ℝ :=
  1 / Real.sqrt a * Real.exp κ * (N * p) +
    4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) / Real.sqrt (finalGap d L) *
      (1 + N * p)

/-- **Row sums of the cut family.** -/
theorem boxCut_row_bound {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ z, ‖s z‖ ≤ Real.exp κ) (q : L1Torus d N₀ × Fin N) :
    ∑ q', ‖boxCut d L N₀ k M v a h s q q'‖ ≤ boxCutConst d L N a κ p := by
  obtain ⟨x, i⟩ := q
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp i i)
  have hsq : 0 ≤ 1 / Real.sqrt a := by positivity
  set B := 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
    Real.sqrt (finalGap d L) with hB
  have hrow := taggedCfin_row_bound (N₀ := N₀) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hs (r := 0) le_rfl
    (by have := pdEps_pos (d := d) (L := L) hd; positivity) x
  simp only [zero_mul, Real.exp_zero, one_mul] at hrow
  have hspin : ∀ j, ‖((if i = j then 1 else 0 : ℂ) - spinProj h i j)‖ ≤
      (if i = j then 1 else 0) + p := by
    intro j
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hp i j))
    by_cases hij : i = j <;> simp [hij]
  have hsumspin : ∑ j : Fin N, ((if i = j then (1 : ℝ) else 0) + p) = 1 + N * p := by
    rw [Finset.sum_add_distrib]
    simp
  rw [Fintype.sum_prod_type]
  calc ∑ y, ∑ j, ‖boxCut d L N₀ k M v a h s (x, i) (y, j)‖
      ≤ ∑ y, ∑ j, (1 / Real.sqrt a * ((if x = y then ‖chiSum d N₀ M s x‖ else 0) * p) +
          ‖taggedCfin d L N₀ k M v a s x y‖ * ((if i = j then 1 else 0) + p)) := by
        refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun j _ => ?_
        rw [boxCut_apply]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsq, norm_mul]
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hp i j) (norm_nonneg _) ?_) hsq
          · by_cases hxy : x = y <;> simp [hxy]
          · by_cases hxy : x = y <;> simp [hxy]
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hspin j) (norm_nonneg _)
    _ = 1 / Real.sqrt a * ‖chiSum d N₀ M s x‖ * (N * p) +
          (∑ y, ‖taggedCfin d L N₀ k M v a s x y‖) * (1 + N * p) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsumspin]
        rw [Finset.sum_mul]
        congr 1
        rw [Finset.sum_eq_single x]
        · simp; ring
        · intro y _ hy; simp [Ne.symm hy]
        · simp
    _ ≤ boxCutConst d L N a κ p := by
        unfold boxCutConst
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right hrow (by positivity))
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (norm_chiSum_le hs x) hsq) (by positivity)

end Box

section Expansion

variable {d N₀ M L k N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

theorem boxCutConst_nonneg (hd : 0 < d) {p κ : ℝ} (hp0 : 0 ≤ p) :
    0 ≤ boxCutConst d L N a κ p := by
  have hB0 : 0 ≤ ballConst d (pdEps d L / 2) :=
    ballConst_decay_nonneg (by have := pdEps_pos (d := d) (L := L) hd; positivity)
  unfold boxCutConst
  refine add_nonneg (by positivity) (mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg (by positivity) hB0)) (Real.sqrt_nonneg _)) (by positivity))

/-- **The cut fields of the box stay near the centre**: for `‖w‖_∞ ≤ ρ` and parameters of the
polydisc of radius `e^κ`, `‖φ₀ + c · boxCut(s) w - φ₀‖_∞ ≤ |c| · boxCutConst · ρ`. -/
theorem linField_boxCut_mem_closedBall (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℂ} {p : ℝ} (hp0 : 0 ≤ p) (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) (c : ℂ)
    (φ₀ : L1Torus d N₀ × Fin N → ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {w : L1Torus d N₀ × Fin N → ℂ}
    (hw : ∀ q, ‖w q‖ ≤ ρ) {s : MacIdx d N₀ M → ℂ}
    (hs : s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :
    linField φ₀ (fun s q q' => c * boxCut d L N₀ k M v a h s q q') s w ∈
      Metric.closedBall φ₀ (‖c‖ * boxCutConst d L N a κ p * ρ) := by
  have hsb : ∀ z, ‖s z‖ ≤ Real.exp κ := fun z => by simpa using (hs z).le
  have hm0 : 0 ≤ ‖c‖ * boxCutConst d L N a κ p * ρ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (boxCutConst_nonneg hd hp0)) hρ
  rw [Metric.mem_closedBall, dist_pi_le_iff hm0]
  intro q
  rw [dist_eq_norm]
  simp only [linField, add_sub_cancel_left]
  calc ‖∑ y, c * boxCut d L N₀ k M v a h s q y * w y‖
      ≤ ∑ y, ‖c * boxCut d L N₀ k M v a h s q y * w y‖ := norm_sum_le _ _
    _ ≤ ∑ y, ‖c‖ * ‖boxCut d L N₀ k M v a h s q y‖ * ρ := by
        refine Finset.sum_le_sum fun y _ => ?_
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_left (hw y) (by positivity)
    _ = ‖c‖ * (∑ y, ‖boxCut d L N₀ k M v a h s q y‖) * ρ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ‖c‖ * boxCutConst d L N a κ p * ρ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) hρ
        exact boxCut_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp hsb q

open Classical in
/-- **The rooted Lemma AE for a term of the final cut field.**  Let `τ` read the field only on `S`,
be analytic and bounded by `M_τ` on the sup-norm ball of radius `r` around a centre `φ₀`.  For
`c ∈ ℂ` (in the application `c = β_k^{-1/2}`) and a variable `w` with `‖w‖_∞ ≤ ρ`,
`m = ‖c‖ · boxCutConst · ρ < r`, the term at the cut field `Φ(s, w) = φ₀ + c · boxCut(s) w` has
the expansion `τ(Φ(1, w)) = τ(φ₀) + ∑_{C ≠ ∅ rooted at S} coef_C(w)`, the coefficients of non-rooted
families vanish, `coef_C(w)` depends on `w` only on the region of `C`, and
`‖coef_C(w)‖ ≤ M_τ m / (r - m) · e^{-(κ-1)|C|}` for `C ≠ ∅`. -/
theorem rootedExpansion_boxCut (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {h : Fin N → ℂ} {p : ℝ} (hp0 : 0 ≤ p) (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) (c : ℂ)
    (φ₀ : L1Torus d N₀ × Fin N → ℂ) {S : Set (L1Torus d N₀ × Fin N)}
    {τ : (L1Torus d N₀ × Fin N → ℂ) → ℂ} (hτ : ReadsOn S τ) {r Mτ : ℝ}
    (hτan : AnalyticOnNhd ℂ τ (Metric.ball φ₀ r)) (hτb : ∀ u ∈ Metric.ball φ₀ r, ‖τ u‖ ≤ Mτ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (w : L1Torus d N₀ × Fin N → ℂ) (hw : ∀ q, ‖w q‖ ≤ ρ)
    (hm : ‖c‖ * boxCutConst d L N a κ p * ρ < r) :
    let T : (MacIdx d N₀ M → ℂ) → L1Torus d N₀ × Fin N → L1Torus d N₀ × Fin N → ℂ :=
      fun s q q' => c * boxCut d L N₀ k M v a h s q q'
    let m : ℝ := ‖c‖ * boxCutConst d L N a κ p * ρ
    τ (linField φ₀ T (fun _ => 1) w) = τ φ₀ +
        ∑ C ∈ Finset.univ.filter (fun C : Finset (MacIdx d N₀ M) =>
          C.Nonempty ∧ IsRootedFamily (spinBoxPatch d N₀ M N) S C),
          rootedCoef τ φ₀ T w C ∧
      (∀ C, ¬ IsRootedFamily (spinBoxPatch d N₀ M N) S C → rootedCoef τ φ₀ T w C = 0) ∧
      (∀ C (w' : L1Torus d N₀ × Fin N → ℂ), (∀ y ∈ patchReg (spinBoxPatch d N₀ M N) C,
        w y = w' y) → rootedCoef τ φ₀ T w C = rootedCoef τ φ₀ T w' C) ∧
      (∀ C, C.Nonempty → ‖rootedCoef τ φ₀ T w C‖ ≤
        Mτ * m / (r - m) * Real.exp (-(κ - 1) * C.card)) := by
  intro T m
  have hκ0 : 0 ≤ κ := by linarith
  have hT : CutDecoupling (spinBoxPatch d N₀ M N) (Real.exp κ) T :=
    CutDecoupling.const_mul (cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h) c
  have hTan : ∀ q q', AnalyticOnNhd ℂ (fun s => T s q q')
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := fun q q' s hs =>
    analyticAt_const.mul (analyticOnNhd_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h q q' s hs)
  have hm0 : 0 ≤ m :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (boxCutConst_nonneg hd hp0)) hρ
  have hmr : m < r := hm
  have hMτ : 0 ≤ Mτ := (norm_nonneg _).trans (hτb φ₀ (Metric.mem_ball_self (hm0.trans_lt hmr)))
  have hsub : Metric.closedBall φ₀ m ⊆ Metric.ball φ₀ r := Metric.closedBall_subset_ball hmr
  refine rootedExpansion_linField hκ hT hTan hτ (hτan.mono hsub) φ₀ w
    (fun s hs => linField_boxCut_mem_closedBall hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp0 hp c
      φ₀ hρ hw hs) ?_
  · intro u hu
    have hu' : u ∈ Metric.ball φ₀ r := hsub hu
    have h1 := norm_sub_le_of_ball (hτan.differentiableOn) hτb hu'
    have hd0 : dist u φ₀ ≤ m := Metric.mem_closedBall.1 hu
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by linarith [hd0]) (by linarith)]
    have hdn : 0 ≤ dist u φ₀ := dist_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hd0 hMτ]

end Expansion


end Balaban.Green
