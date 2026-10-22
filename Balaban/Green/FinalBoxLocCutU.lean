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
# The cut family of a Hessian with a general unit-lattice operator (A6-3, shared core)

For a matrix `U` on the sites of the unit lattice satisfying `CutOpHyp` (coercive with a gap,
exponentially decaying entries, the macro-size ties of the tagged parametrix) and a direction `h`,
the Hessian `hessC a U h = a P_h + (U ⊗ 1)(1 - P_h)` has the cut family

  `boxCutU a U h s = a^{-1/2} (m(s) ⊗ 1) P_h + (taggedCfinU U s ⊗ 1)(1 - P_h)`,

with `m(s)(x) = ∑_z s_z χ_z(x)` (`chiSum`).  This is shared: the cut family `boxCut` of the final
Hessian is the instance `U = finalOp` (FinalBoxLocCut), and the local-pair operators of the
localized square root (Amendment B-1″) and the regional problems use the same family.

* `resOK_of_isCoercive`: a coercive matrix has invertible resolvents on `[0, ∞)`;
* `cutDecoupling_taggedCfinU`, `cutDecoupling_boxCutU`: the decoupling property on the polydisc of
  radius `e^κ` (patches `macBox i`, resp. `macBox i × Fin N`);
* `boxCutU_apply`, `analyticOnNhd_boxCutU`, `boxCutU_row_bound`, `norm_boxCutU_apply_le`: entries,
  analyticity, row sums `a^{-1/2} e^κ N p + B (1 + N p)` and entry decay;
* `boxCutU_one`: `boxCutU a U h 1 = sqrtMat (hessC a U h)` (the principal inverse square root).

`chiSum`, `spinBoxPatch`, `patchReg_macBox` and the `chiSum` lemmas are moved verbatim from
FinalBoxLocCut.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Res

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A coercive matrix has invertible resolvents on `[0, ∞)`.** -/
theorem resOK_of_isCoercive {U : Matrix ι ι ℂ} {g : ℝ} (hg : 0 < g) (hU : IsCoercive U g) :
    Localization.ResOK U := fun x hx =>
  isUnit_of_isCoercive hg fun v => by
    rw [reQuad_add, reQuad_smul_one]
    have := hU v
    have := sqNorm_nonneg v
    nlinarith

end Res

section Scalar

variable {d N₀ M : ℕ} [NeZero N₀]

theorem patchReg_macBox (C : Finset (MacIdx d N₀ M)) :
    patchReg (fun i => macBox d N₀ M i) C = macRegion d N₀ M C := by
  ext x; simp [patchReg, mem_macRegion]

/-- **The decoupling property of the Stieltjes square-root family of a general matrix** on the
polydisc of radius `e^κ` (shared core): the support property is `taggedCfinU_eq_zero_of_not_mem`,
the splitting is `taggedCfinU_apply_split_of_separated`. -/
theorem cutDecoupling_taggedCfinU (hd : 0 < d) {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    {g A δ ε κ : ℝ} (hU : CutOpHyp d N₀ M U g A δ ε κ) :
    CutDecoupling (fun i => macBox d N₀ M i) (Real.exp κ)
      (fun s x y => taggedCfinU d N₀ M U s x y) where
  supp C s _ hsC x y h := by
    rw [patchReg_macBox]
    by_contra hc
    exact h (taggedCfinU_eq_zero_of_not_mem hU.hM hd _ hsC hc)
  split C A s hs hsC hAC hsep x y := by
    rw [patchReg_macBox, patchReg_macBox] at hsep
    exact taggedCfinU_apply_split_of_separated hd hU hAC hsep
      (fun p => by simpa using (hs p).le) hsC x y

end Scalar

section Box

variable {d N₀ M N : ℕ} [NeZero N₀]

/-- The parameter-weighted partition of unity `m(s)(x) = ∑_z s_z χ_z(x)` (`m(1) = 1`). -/
noncomputable def chiSum (d N₀ M : ℕ) [NeZero N₀] (s : MacIdx d N₀ M → ℂ) (x : L1Torus d N₀) :
    ℂ :=
  ∑ z, s z * ((macChi d N₀ M z x : ℝ) : ℂ)

/-- **The cut family of the Hessian of a general matrix** (shared; a construction proposed in
FINALFAM): `a^{-1/2} (m(s) ⊗ 1) P_h + (taggedCfinU U s ⊗ 1)(1 - P_h)`. -/
noncomputable def boxCutU (d N₀ M : ℕ) [NeZero N₀] {N : ℕ} (a : ℝ)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  ((1 / Real.sqrt a : ℝ) : ℂ) • (Multiscale.liftOp N (Matrix.diagonal (chiSum d N₀ M s)) *
      projHC h) +
    Multiscale.liftOp N (taggedCfinU d N₀ M U s) * (1 - projHC h)

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

omit [NeZero N₀] in
theorem one_sub_projHC_eq_idKron (h : Fin N → ℂ) :
    (1 - projHC h : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ) =
      idKron (1 - spinProj h) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [Matrix.sub_apply, projHC, idKron, Matrix.one_apply, Prod.mk.injEq]
  by_cases hxy : x = y
  · subst hxy; by_cases hij : i = j <;> simp [hij]
  · simp [hxy]

/-- **The entries of the cut family.** -/
theorem boxCutU_apply (a : ℝ) (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (h : Fin N → ℂ)
    (s : MacIdx d N₀ M → ℂ) (x y : L1Torus d N₀) (i j : Fin N) :
    boxCutU d N₀ M a U h s (x, i) (y, j) =
      ((1 / Real.sqrt a : ℝ) : ℂ) * ((if x = y then chiSum d N₀ M s x else 0) * spinProj h i j) +
        taggedCfinU d N₀ M U s x y * ((if i = j then 1 else 0) - spinProj h i j) := by
  unfold boxCutU
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

theorem chiSum_one (x : L1Torus d N₀) : chiSum d N₀ M (fun _ => 1) x = 1 := by
  unfold chiSum
  simp only [one_mul]
  rw [← Complex.ofReal_sum, macChi_sum, Complex.ofReal_one]

theorem analyticOnNhd_chiSum (x : L1Torus d N₀) (U : Set (MacIdx d N₀ M → ℂ)) :
    AnalyticOnNhd ℂ (fun s => chiSum d N₀ M s x) U := by
  intro s _
  unfold chiSum
  refine Finset.analyticAt_fun_sum _ fun z _ => ?_
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : MacIdx d N₀ M => ℂ) z).analyticAt
    s).mul analyticAt_const

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

variable {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {g A δ ε κ a : ℝ}

/-- **The decoupling property of the cut family** (shared core). -/
theorem cutDecoupling_boxCutU (hd : 0 < d) (hU : CutOpHyp d N₀ M U g A δ ε κ) (h : Fin N → ℂ) :
    CutDecoupling (spinBoxPatch d N₀ M N) (Real.exp κ)
      (fun s p q => boxCutU d N₀ M a U h s p q) where
  supp C s hs hsC p q hne := by
    obtain ⟨x, i⟩ := p
    obtain ⟨y, j⟩ := q
    rw [boxCutU_apply] at hne
    simp only [mem_patchReg_spinBoxPatch]
    by_cases hT : taggedCfinU d N₀ M U s x y = 0
    · rw [hT, zero_mul, add_zero] at hne
      have h1 : (if x = y then chiSum d N₀ M s x else 0) ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      by_cases hxy : x = y
      · subst hxy
        simp only [↓reduceIte] at h1
        have := mem_macRegion_of_chiSum_ne_zero hU.hM hsC h1
        exact ⟨this, this⟩
      · exact absurd (by simp [hxy]) h1
    · exact (cutDecoupling_taggedCfinU hd hU).supp C s hs hsC x y hT |>.imp
        (by rw [patchReg_macBox]; exact id) (by rw [patchReg_macBox]; exact id)
  split C A s hs hsC hAC hsep p q := by
    obtain ⟨x, i⟩ := p
    obtain ⟨y, j⟩ := q
    have hsep' : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)) := by
      rw [Set.disjoint_left]
      intro z hz hz'
      exact Set.disjoint_left.1 hsep
        ((mem_patchReg_spinBoxPatch (p := (z, i))).2 hz)
        ((mem_patchReg_spinBoxPatch (p := (z, i))).2 hz')
    have hT : taggedCfinU d N₀ M U s x y =
        taggedCfinU d N₀ M U (cutTo A s) x y + taggedCfinU d N₀ M U (cutTo (C \ A) s) x y :=
      taggedCfinU_apply_split_of_separated hd hU hAC hsep' (fun p => by simpa using (hs p).le)
        hsC x y
    rw [boxCutU_apply, boxCutU_apply, boxCutU_apply, chiSum_split (A := A) hsC x, hT]
    split_ifs <;> ring

/-- **At `s = 1` the cut family is the principal inverse square root of the Hessian**
(shared core). -/
theorem boxCutU_one [NeZero N] (hU : CutOpHyp d N₀ M U g A δ ε κ) (ha : 0 < a) {h : Fin N → ℂ}
    (hs : ∑ i, h i ^ 2 ≠ 0) :
    boxCutU d N₀ M a U h (fun _ => 1) = Localization.sqrtMat (hessC N (a : ℂ) U h) := by
  have : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩
  rw [(sqrtMat_hessC ha (resOK_of_isCoercive hU.hg hU.coercive) hs).2]
  unfold boxCutU
  have hdiag : Matrix.diagonal (chiSum d N₀ M (fun _ => 1)) = 1 := by
    rw [show chiSum d N₀ M (fun _ => 1) = fun _ => 1 from funext (chiSum_one)]
    rfl
  rw [hdiag, Multiscale.liftOp_one, one_mul, taggedCfinU_one hU]

/-- **Analyticity of the entries of the cut family** on the polydisc of radius `e^κ`
(shared core). -/
theorem analyticOnNhd_boxCutU (hU : CutOpHyp d N₀ M U g A δ ε κ) (h : Fin N → ℂ)
    (p q : L1Torus d N₀ × Fin N) :
    AnalyticOnNhd ℂ (fun s => boxCutU d N₀ M a U h s p q)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  simp only [boxCutU_apply]
  have hT : AnalyticOnNhd ℂ (fun s => taggedCfinU d N₀ M U s x y)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :=
    (analyticOnNhd_taggedCfinU hU x y).mono fun s hs p => by simpa using hs p
  intro s hs
  refine (analyticAt_const.mul ?_).add ((hT s hs).mul analyticAt_const)
  by_cases hxy : x = y
  · simp only [hxy, ↓reduceIte]
    exact (analyticOnNhd_chiSum y _ s hs).mul analyticAt_const
  · simp only [hxy, ↓reduceIte, zero_mul]
    exact analyticAt_const

/-- **Row sums of the cut family** (shared core): for `p` a bound of the entries of `P_h` and `s`
in the closed polydisc, `∑_q ‖boxCutU s p q‖ ≤ a^{-1/2} e^κ N p + B (1 + N p)`,
`B = (4/3) · 2 e^{Hκ} ballConst(ε/2) / √g` the row bound of `taggedCfinU`. -/
theorem boxCutU_row_bound (hU : CutOpHyp d N₀ M U g A δ ε κ) {h : Fin N → ℂ} {p : ℝ}
    (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {s : MacIdx d N₀ M → ℂ} (hs : ∀ z, ‖s z‖ ≤ Real.exp κ)
    (q : L1Torus d N₀ × Fin N) :
    ∑ q', ‖boxCutU d N₀ M a U h s q q'‖ ≤
      1 / Real.sqrt a * Real.exp κ * (N * p) +
        4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) / Real.sqrt g * (1 + N * p) := by
  obtain ⟨x, i⟩ := q
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp i i)
  have hsq : 0 ≤ 1 / Real.sqrt a := by positivity
  have hrow := taggedCfinU_row_bound hU hs (r := 0) le_rfl
    (by have := hU.hε; positivity) x
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
  calc ∑ y, ∑ j, ‖boxCutU d N₀ M a U h s (x, i) (y, j)‖
      ≤ ∑ y, ∑ j, (1 / Real.sqrt a * ((if x = y then ‖chiSum d N₀ M s x‖ else 0) * p) +
          ‖taggedCfinU d N₀ M U s x y‖ * ((if i = j then 1 else 0) + p)) := by
        refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun j _ => ?_
        rw [boxCutU_apply]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsq, norm_mul]
          refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ (hp i j) (norm_nonneg _) ?_) hsq
          · by_cases hxy : x = y <;> simp [hxy]
          · by_cases hxy : x = y <;> simp [hxy]
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hspin j) (norm_nonneg _)
    _ = 1 / Real.sqrt a * ‖chiSum d N₀ M s x‖ * (N * p) +
          (∑ y, ‖taggedCfinU d N₀ M U s x y‖) * (1 + N * p) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsumspin]
        rw [Finset.sum_mul]
        congr 1
        rw [Finset.sum_eq_single x]
        · simp; ring
        · intro y _ hy; simp [Ne.symm hy]
        · simp
    _ ≤ _ := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right hrow (by positivity))
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (norm_chiSum_le hs x) hsq) (by positivity)

/-- **The entry bound of the cut family** (shared core): for `0 ≤ r ≤ ε/8`,
`‖boxCutU s p q‖ ≤ (a^{-1/2} e^κ p + B (1 + p)) e^{-r |p - q|}`. -/
theorem norm_boxCutU_apply_le (hU : CutOpHyp d N₀ M U g A δ ε κ) {h : Fin N → ℂ} {p : ℝ}
    (hp : ∀ i j, ‖spinProj h i j‖ ≤ p) {s : MacIdx d N₀ M → ℂ} (hs : ∀ z, ‖s z‖ ≤ Real.exp κ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ ε / 8) (P Q : L1Torus d N₀ × Fin N) :
    ‖boxCutU d N₀ M a U h s P Q‖ ≤
      (1 / Real.sqrt a * Real.exp κ * p +
        4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) / Real.sqrt g * (1 + p)) *
        Real.exp (-r * dist P.1 Q.1) := by
  obtain ⟨x, i⟩ := P
  obtain ⟨y, j⟩ := Q
  have hp0 : 0 ≤ p := (norm_nonneg _).trans (hp i i)
  have hsq : 0 ≤ 1 / Real.sqrt a := by positivity
  have hT := taggedCfinU_entry_bound hU hs hr0 hr x y
  rw [boxCutU_apply]
  set B := 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (ε / 2)) / Real.sqrt g
  have hspin : ‖((if i = j then 1 else 0 : ℂ) - spinProj h i j)‖ ≤ 1 + p := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ (hp i j))
    by_cases hij : i = j <;> simp [hij]
  have h2 : ‖taggedCfinU d N₀ M U s x y * ((if i = j then 1 else 0 : ℂ) - spinProj h i j)‖ ≤
      B * Real.exp (-r * dist x y) * (1 + p) := by
    rw [norm_mul]
    exact mul_le_mul hT hspin (norm_nonneg _) ((norm_nonneg _).trans hT)
  refine (norm_add_le _ _).trans ?_
  by_cases hxy : x = y
  · subst hxy
    simp only [dist_self, mul_zero, Real.exp_zero, mul_one, ↓reduceIte] at h2 ⊢
    have h1 : ‖((1 / Real.sqrt a : ℝ) : ℂ) * (chiSum d N₀ M s x * spinProj h i j)‖ ≤
        1 / Real.sqrt a * Real.exp κ * p := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hsq, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_chiSum_le hs x) (hp i j) (norm_nonneg _)
        (Real.exp_pos _).le) hsq
    linarith
  · simp only [hxy, ↓reduceIte, zero_mul, mul_zero, norm_zero, zero_add]
    have hE0 : 0 ≤ Real.exp (-r * dist x y) := (Real.exp_pos _).le
    have hA0 : 0 ≤ 1 / Real.sqrt a * Real.exp κ * p := by positivity
    nlinarith

end Box

end Balaban.Green
