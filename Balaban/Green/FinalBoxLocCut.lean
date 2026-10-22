/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCutU
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
`boxCut` is the instance `U = finalOp` of the shared family `boxCutU` (FinalBoxLocCutU), and its
lemmas below are the instances of the shared cores at `cutOpHyp_finalOp`.

* `boxCut_apply`: the entries, `a^{-1/2} [x = y] m(s)(x) P_h(i, j) + C_fin(s)(x, y) (δ_ij - P_h(i, j))`;
* `cutDecoupling_taggedCfin`, `cutDecoupling_boxCut`: the decoupling property `CutDecoupling` on the
  polydisc of radius `e^κ`, with the patches `macBox i` (resp. `macBox i × Fin N`);
* `boxCut_row_bound`: `∑_q ‖boxCut(s) p q‖ ≤ a^{-1/2} e^κ N p + B (1 + N p)` (`B` the row bound of
  `taggedCfin`, `p` a bound for the entries of `P_h`);
* `rootedExpansion_boxCut`: the rooted Lemma AE for a term `τ` reading the field on `S`, analytic and
  bounded by `M_τ` on the sup-norm ball of radius `r` around a centre `φ₀`, at the field
  `φ₀ + c · boxCut(s) w` with `‖w‖_∞ ≤ ρ`, `m = |c| B_box ρ < r`: the increment bound is
  `M_τ m / (r - m)`.  The cores `linField_mem_closedBall_of_row_bound` and `rootedExpansion_of_row_bound` take any
  decoupled cut family with analytic entries and bounded rows (`linField_boxCut_mem_closedBall`
  and `rootedExpansion_boxCut` are their instances).
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Scalar

variable {d N₀ M L k : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **The decoupling property of the Stieltjes square-root family** `taggedCfin` on the polydisc
of radius `e^κ`: the support property is `taggedCfinU_eq_zero_of_not_mem`, the splitting is
`taggedCfin_apply_split_of_separated`. -/
theorem cutDecoupling_taggedCfin (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    CutDecoupling (fun i => macBox d N₀ M i) (Real.exp κ)
      (fun s x y => taggedCfin d L N₀ k M v a s x y) where
  supp := (cutDecoupling_taggedCfinU hd
    (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ)).supp
  split := (cutDecoupling_taggedCfinU hd
    (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ)).split

end Scalar

section Box

variable {d N₀ M L k N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **The cut family of the final Hessian** (a construction proposed in FINALFAM):
`a^{-1/2} (m(s) ⊗ 1) P_h + (taggedCfin(s) ⊗ 1)(1 - P_h)`, the instance `U = finalOp` of the
shared family `boxCutU`. -/
noncomputable def boxCut (d L N₀ k M : ℕ) [NeZero N₀] [NeZero L] {N : ℕ} (v a : ℝ)
    (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ :=
  boxCutU d N₀ M a (finalOp d L N₀ k v a) h s

/-- **The entries of the cut family.** -/
theorem boxCut_apply (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) (x y : L1Torus d N₀)
    (i j : Fin N) :
    boxCut d L N₀ k M v a h s (x, i) (y, j) =
      ((1 / Real.sqrt a : ℝ) : ℂ) * ((if x = y then chiSum d N₀ M s x else 0) * spinProj h i j) +
        taggedCfin d L N₀ k M v a s x y * ((if i = j then 1 else 0) - spinProj h i j) :=
  boxCutU_apply a (finalOp d L N₀ k v a) h s x y i j

variable (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
  (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
  (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
  (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
include hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ

/-- **The decoupling property of the cut family of the final Hessian.** -/
theorem cutDecoupling_boxCut (h : Fin N → ℂ) :
    CutDecoupling (spinBoxPatch d N₀ M N) (Real.exp κ)
      (fun s p q => boxCut d L N₀ k M v a h s p q) :=
  cutDecoupling_boxCutU hd (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ) h

/-- **At `s = 1` the cut family is the principal inverse square root of the final Hessian.** -/
theorem boxCut_one [NeZero N] {h : Fin N → ℂ} (hs : ∑ i, h i ^ 2 ≠ 0) :
    boxCut d L N₀ k M v a h (fun _ => 1) =
      Localization.sqrtMat (finalHessianC d L N₀ k v a h) :=
  boxCutU_one (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ) (by linarith) hs

/-- **Analyticity of the entries of the cut family** on the polydisc of radius `e^κ`. -/
theorem analyticOnNhd_boxCut (h : Fin N → ℂ) (p q : L1Torus d N₀ × Fin N) :
    AnalyticOnNhd ℂ (fun s => boxCut d L N₀ k M v a h s p q)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :=
  analyticOnNhd_boxCutU (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ) h p q

/-- The row-sum constant of the cut family: `a^{-1/2} e^κ N p + B (1 + N p)`, `B` the row bound of
`taggedCfin` and `p` a bound for the entries of `P_h`. -/
noncomputable def boxCutConst (d L N : ℕ) (a κ p : ℝ) : ℝ :=
  1 / Real.sqrt a * Real.exp κ * (N * p) +
    4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) / Real.sqrt (finalGap d L) *
      (1 + N * p)

/-- **Row sums of the cut family.** -/
theorem boxCut_row_bound {h : Fin N → ℂ} {p : ℝ} (hp : ∀ i j, ‖spinProj h i j‖ ≤ p)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ z, ‖s z‖ ≤ Real.exp κ) (q : L1Torus d N₀ × Fin N) :
    ∑ q', ‖boxCut d L N₀ k M v a h s q q'‖ ≤ boxCutConst d L N a κ p :=
  boxCutU_row_bound (cutOpHyp_finalOp hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ) hp hs q

end Box

section RowBound

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

omit [Fintype ι] [DecidableEq ι] in
/-- **The cut fields stay near the centre** (core): if the row sums of `T(s)` are at most `B` for
`s ∈ U`, then for `‖w‖_∞ ≤ ρ`, `‖φ₀ + c · T(s) w - φ₀‖_∞ ≤ |c| B ρ`. -/
theorem linField_mem_closedBall_of_row_bound {T : (ι → ℂ) → Ω → Ω → ℂ} {U : Set (ι → ℂ)}
    {B : ℝ} (hB0 : 0 ≤ B) (hrow : ∀ s ∈ U, ∀ q, ∑ q', ‖T s q q'‖ ≤ B) (c : ℂ) (φ₀ : Ω → ℂ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) {w : Ω → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ) {s : ι → ℂ} (hs : s ∈ U) :
    linField φ₀ (fun s q q' => c * T s q q') s w ∈ Metric.closedBall φ₀ (‖c‖ * B * ρ) := by
  have hm0 : 0 ≤ ‖c‖ * B * ρ := mul_nonneg (mul_nonneg (norm_nonneg _) hB0) hρ
  rw [Metric.mem_closedBall, dist_pi_le_iff hm0]
  intro q
  rw [dist_eq_norm]
  simp only [linField, add_sub_cancel_left]
  calc ‖∑ y, c * T s q y * w y‖
      ≤ ∑ y, ‖c * T s q y * w y‖ := norm_sum_le _ _
    _ ≤ ∑ y, ‖c‖ * ‖T s q y‖ * ρ := by
        refine Finset.sum_le_sum fun y _ => ?_
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_left (hw y) (by positivity)
    _ = ‖c‖ * (∑ y, ‖T s q y‖) * ρ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ‖c‖ * B * ρ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrow s hs q) (norm_nonneg _)) hρ

open Classical in
/-- **The rooted Lemma AE for a term of a cut field with bounded rows** (core).  Let `T` have the
decoupling property on the polydisc of radius `e^κ`, `κ ≥ 1`, analytic entries and row sums at
most `B` there; let `τ` read the field only on `S`, be analytic and bounded by `M_τ` on the
sup-norm ball of radius `r` around `φ₀`.  For `c ∈ ℂ` and `‖w‖_∞ ≤ ρ`, `m = |c| B ρ < r`:
`τ(φ₀ + c T(1) w) = τ(φ₀) + ∑_{C ≠ ∅ rooted at S} coef_C(w)`, the coefficients of non-rooted
families vanish, `coef_C(w)` depends on `w` only on the region of `C`, and
`‖coef_C(w)‖ ≤ M_τ m / (r - m) · e^{-(κ-1)|C|}` for `C ≠ ∅`. -/
theorem rootedExpansion_of_row_bound {P : ι → Set Ω} {T : (ι → ℂ) → Ω → Ω → ℂ} {κ : ℝ}
    (hκ : 1 ≤ κ) (hT : CutDecoupling P (Real.exp κ) T)
    (hTan : ∀ q q', AnalyticOnNhd ℂ (fun s => T s q q')
      (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hrow : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ q, ∑ q', ‖T s q q'‖ ≤ B)
    (c : ℂ) (φ₀ : Ω → ℂ) {S : Set Ω} {τ : (Ω → ℂ) → ℂ} (hτ : ReadsOn S τ) {r Mτ : ℝ}
    (hτan : AnalyticOnNhd ℂ τ (Metric.ball φ₀ r)) (hτb : ∀ u ∈ Metric.ball φ₀ r, ‖τ u‖ ≤ Mτ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (w : Ω → ℂ) (hw : ∀ q, ‖w q‖ ≤ ρ) (hm : ‖c‖ * B * ρ < r) :
    let T' : (ι → ℂ) → Ω → Ω → ℂ := fun s q q' => c * T s q q'
    let m : ℝ := ‖c‖ * B * ρ
    τ (linField φ₀ T' (fun _ => 1) w) = τ φ₀ +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧ IsRootedFamily P S C),
          rootedCoef τ φ₀ T' w C ∧
      (∀ C, ¬ IsRootedFamily P S C → rootedCoef τ φ₀ T' w C = 0) ∧
      (∀ C (w' : Ω → ℂ), (∀ y ∈ patchReg P C, w y = w' y) →
        rootedCoef τ φ₀ T' w C = rootedCoef τ φ₀ T' w' C) ∧
      (∀ C, C.Nonempty → ‖rootedCoef τ φ₀ T' w C‖ ≤
        Mτ * m / (r - m) * Real.exp (-(κ - 1) * C.card)) := by
  intro T' m
  have hT' : CutDecoupling P (Real.exp κ) T' := CutDecoupling.const_mul hT c
  have hT'an : ∀ q q', AnalyticOnNhd ℂ (fun s => T' s q q')
      (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := fun q q' s hs =>
    analyticAt_const.mul (hTan q q' s hs)
  have hm0 : 0 ≤ m := mul_nonneg (mul_nonneg (norm_nonneg _) hB0) hρ
  have hmr : m < r := hm
  have hMτ : 0 ≤ Mτ := (norm_nonneg _).trans (hτb φ₀ (Metric.mem_ball_self (hm0.trans_lt hmr)))
  have hsub : Metric.closedBall φ₀ m ⊆ Metric.ball φ₀ r := Metric.closedBall_subset_ball hmr
  refine rootedExpansion_linField hκ hT' hT'an hτ (hτan.mono hsub) φ₀ w
    (fun s hs => linField_mem_closedBall_of_row_bound hB0 hrow c φ₀ hρ hw hs) ?_
  · intro u hu
    have hu' : u ∈ Metric.ball φ₀ r := hsub hu
    have h1 := norm_sub_le_of_ball (hτan.differentiableOn) hτb hu'
    have hd0 : dist u φ₀ ≤ m := Metric.mem_closedBall.1 hu
    refine h1.trans ?_
    rw [div_le_div_iff₀ (by linarith [hd0]) (by linarith)]
    have hdn : 0 ≤ dist u φ₀ := dist_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hd0 hMτ]

end RowBound

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
      Metric.closedBall φ₀ (‖c‖ * boxCutConst d L N a κ p * ρ) :=
  linField_mem_closedBall_of_row_bound (boxCutConst_nonneg hd hp0)
    (fun s hs q => boxCut_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp
      (fun z => by simpa using (hs z).le) q) c φ₀ hρ hw hs

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
  have hκ0 : 0 ≤ κ := by linarith
  exact rootedExpansion_of_row_bound hκ
    (cutDecoupling_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h)
    (fun q q' => analyticOnNhd_boxCut hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ h q q')
    (boxCutConst_nonneg hd hp0)
    (fun s hs q => boxCut_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hp
      (fun z => by simpa using (hs z).le) q) c φ₀ hτ hτan hτb hρ w hw hm

end Expansion


end Balaban.Green
