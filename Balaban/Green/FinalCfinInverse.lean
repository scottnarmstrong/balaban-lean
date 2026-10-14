/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedSqrt
public import Balaban.Green.FinalMassSqrt
public import Balaban.Green.FinalTagSupport
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Invertibility of the Stieltjes cut family of the final operator (FINALPHYS, L2 remainder)

This file belongs to the tagged parametrix of `notes/phase1/FINALFAM.md`; the construction is
proposed there and the papers print no formula for it.

Write `C(s) = taggedCfin s` and `R(s) = C(s) C(s) U - 1`, `U = finalOp`.

* **Refutation of the statement on polydiscs centred at `0`.**  Every tag set `macTags z x y`
  is nonempty (it contains the cell of `x`), so `taggedCfin 0 = 0`
  (`taggedCfin_zero`).  Hence `R(0) = -1`, `C(0)` is not invertible, and no bound
  `‖R(s)‖ ≤ q < 1` holds on any polydisc `{‖s p‖ ≤ ρ}` (`ρ ≥ 0`), however small
  (`taggedCfin_sq_mul_final_zero`, `taggedCfin_not_isUnit_zero`).  In particular the cut family
  has no analytic logarithm of its determinant on a polydisc around `0`.
* **Largest radius.**  On the closed polydisc `‖s p‖ ≤ e^κ` the weighted row sums of `R(s)` are at
  most `B = 1 + B_C² A_U` (`taggedCfin_sq_mul_final_weighted_bound`), independent of `M`.
  `R` is analytic and `R(1) = 0`; the Schwarz lemma on complex lines through `s = 1` gives
  `‖R(s)‖ ≤ B δ / (e^κ - 1)` for `‖s p - 1‖ ≤ δ < e^κ - 1`
  (`taggedCfin_sq_mul_final_near_one`).
* **Invertibility.**  For `B δ ≤ (e^κ - 1)/2` the matrix `C(s)` is invertible with weighted row
  sums of the inverse at most `2 B_C A_U` (`taggedCfin_isUnit_near_one`).
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Zero

variable {d N₀ M : ℕ} [NeZero N₀]

theorem macTags_nonempty (hM : 0 < M) (hd : 0 < d) (z : MacIdx d N₀ M) (x y : L1Torus d N₀) :
    (macTags d N₀ M z x y).Nonempty := by
  classical
  obtain ⟨w, hw, -⟩ := macCore_partition (M := M) x
  have hq := mem_macBox_of_mem_macCore hM hw
  refine ⟨w, ?_⟩
  simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨x, macPath_start hd x y, hq⟩

theorem tagMon_macTags_zero (hM : 0 < M) (hd : 0 < d) (z : MacIdx d N₀ M) (x y : L1Torus d N₀) :
    tagMon (macTags d N₀ M z x y) (0 : MacIdx d N₀ M → ℂ) = 0 := by
  obtain ⟨p, hp⟩ := macTags_nonempty (N₀ := N₀) hM hd z x y
  exact Finset.prod_eq_zero hp (Pi.zero_apply p)

end Zero

section Main

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

theorem taggedGfin_zero (hM : 0 < M) (hd : 0 < d) (t : ℝ) :
    taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t (0 : MacIdx d N₀ M → ℂ) = 0 := by
  have h : taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t (0 : MacIdx d N₀ M → ℂ) = 0 := by
    ext x y
    simp [taggedG, taggedMat, tagMon_macTags_zero hM hd]
  unfold taggedGfin
  rw [h, zero_mul]

/-- At `s = 0` all tags vanish, so `taggedCfin 0 = 0`. -/
theorem taggedCfin_zero (hM : 0 < M) (hd : 0 < d) :
    taggedCfin d L N₀ k M v a (0 : MacIdx d N₀ M → ℂ) = 0 := by
  unfold taggedCfin
  have h : (fun t : ℝ => ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (0 : MacIdx d N₀ M → ℂ)) =
      fun _ => (0 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) := by
    funext t
    rw [taggedGfin_zero hM hd, smul_zero]
  rw [h]
  ext p q
  simp [Localization.intMat]

end Main

section Schwarz

/-- Schwarz lemma on complex lines through `s = 1`: an analytic `F` on the open polydisc
`‖s p‖ < e^κ`, bounded by `B` there and vanishing at `s = 1`, satisfies
`‖F s‖ ≤ B δ / (e^κ - 1)` whenever `‖s p - 1‖ ≤ δ < e^κ - 1`. -/
theorem norm_le_of_analyticOnNhd_polydisc_one {P : Type*} [Fintype P] {κ : ℝ}
    (F : (P → ℂ) → ℂ) (hF : AnalyticOnNhd ℂ F {s | ∀ p, ‖s p‖ < Real.exp κ}) {B : ℝ}
    (hB : ∀ s : P → ℂ, (∀ p, ‖s p‖ < Real.exp κ) → ‖F s‖ ≤ B) (h1 : F (fun _ => 1) = 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < Real.exp κ - 1) {s : P → ℂ} (hs : ∀ p, ‖s p - 1‖ ≤ δ) :
    ‖F s‖ ≤ B * δ / (Real.exp κ - 1) := by
  set u : P → ℂ := fun p => s p - 1 with hu
  set φ : ℂ → (P → ℂ) := fun l p => 1 + l * u p with hφ
  set R₁ : ℝ := (Real.exp κ - 1) / δ with hR₁
  have hρ : 0 < Real.exp κ - 1 := lt_trans hδ0 hδ
  have hR₁pos : 0 < R₁ := div_pos hρ hδ0
  have hmaps : Set.MapsTo φ (Metric.ball (0 : ℂ) R₁) {s | ∀ p, ‖s p‖ < Real.exp κ} := by
    intro l hl p
    rw [Metric.mem_ball, dist_zero_right] at hl
    simp only [hφ]
    calc ‖1 + l * u p‖ ≤ ‖(1 : ℂ)‖ + ‖l * u p‖ := norm_add_le _ _
      _ = 1 + ‖l‖ * ‖u p‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + ‖l‖ * δ := by gcongr; exact hs p
      _ < 1 + R₁ * δ := by gcongr
      _ = Real.exp κ := by rw [hR₁]; field_simp; ring
  have hφd : Differentiable ℂ φ := by
    rw [hφ]
    refine differentiable_pi.2 fun p => ?_
    fun_prop
  have hg : DifferentiableOn ℂ (fun l => F (φ l)) (Metric.ball (0 : ℂ) R₁) :=
    hF.differentiableOn.comp hφd.differentiableOn hmaps
  have hφ0 : φ 0 = fun _ => 1 := by funext p; simp [hφ]
  have hg0 : F (φ 0) = 0 := by rw [hφ0]; exact h1
  have hmg : Set.MapsTo (fun l => F (φ l)) (Metric.ball (0 : ℂ) R₁)
      (Metric.closedBall (F (φ 0)) B) := by
    intro l hl
    rw [Metric.mem_closedBall, hg0, dist_zero_right]
    exact hB _ (hmaps hl)
  have h1ball : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R₁ := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, hR₁, lt_div_iff₀ hδ0]
    linarith
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hg hmg h1ball
  have hφ1 : φ 1 = s := by funext p; simp [hφ, hu]
  rw [hφ1, hg0, dist_zero_right, dist_zero_right, norm_one, hR₁] at this
  calc ‖F s‖ ≤ B / ((Real.exp κ - 1) / δ) * 1 := this
    _ = _ := by field_simp

end Schwarz

section Zero2

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **The identity.**  `C(s) C(s) U = 1 + R(s)` with the explicit defect
`R(s) = C(s) C(s) U - 1`. -/
theorem taggedCfin_sq_mul_final (s : MacIdx d N₀ M → ℂ) :
    taggedCfin d L N₀ k M v a s * taggedCfin d L N₀ k M v a s * finalOp d L N₀ k v a =
      1 + (taggedCfin d L N₀ k M v a s * taggedCfin d L N₀ k M v a s * finalOp d L N₀ k v a - 1) :=
  (add_sub_cancel _ _).symm

/-- **Obstruction.**  At `s = 0` the defect is `R(0) = -1`. -/
theorem taggedCfin_sq_mul_final_zero (hM : 0 < M) (hd : 0 < d) :
    taggedCfin d L N₀ k M v a (0 : MacIdx d N₀ M → ℂ) *
      taggedCfin d L N₀ k M v a (0 : MacIdx d N₀ M → ℂ) * finalOp d L N₀ k v a - 1 = -1 := by
  rw [taggedCfin_zero hM hd]
  simp

/-- **Obstruction.**  `taggedCfin 0` is not invertible; every polydisc `{‖s p‖ ≤ ρ}`, `ρ ≥ 0`,
contains `s = 0`, so `taggedCfin s` is not invertible on any polydisc centred at `0`. -/
theorem taggedCfin_not_isUnit_zero (hM : 0 < M) (hd : 0 < d) (x : L1Torus d N₀) :
    ¬ IsUnit (taggedCfin d L N₀ k M v a (0 : MacIdx d N₀ M → ℂ)) := by
  intro h
  rw [taggedCfin_zero hM hd, isUnit_zero_iff] at h
  have := congrFun (congrFun h x) x
  simp at this

/-- **Obstruction.**  The weighted row sums of `R(0)` equal `1` for every weight `e^{r dist}`, so
no bound `‖R(s)‖ ≤ q < 1` holds on a polydisc centred at `0`. -/
theorem taggedCfin_sq_mul_final_weighted_zero (hM : 0 < M) (hd : 0 < d) (r : ℝ)
    (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) * ‖(taggedCfin d L N₀ k M v a (0 : MacIdx d N₀ M → ℂ) *
      taggedCfin d L N₀ k M v a (0 : MacIdx d N₀ M → ℂ) * finalOp d L N₀ k v a - 1) x y‖ = 1 := by
  rw [taggedCfin_sq_mul_final_zero hM hd]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Matrix.neg_apply, Ne.symm hy]
  · simp

end Zero2

section Pos

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

local notation "Cf" => taggedCfin d L N₀ k M v a
local notation "Uf" => finalOp d L N₀ k v a

private theorem expw_facts (r : ℝ) (hr0 : 0 ≤ r) :
    (∀ x y : L1Torus d N₀, 1 ≤ Real.exp (r * dist x y)) ∧
    (∀ x : L1Torus d N₀, Real.exp (r * dist x x) = 1) ∧
    (∀ x u y : L1Torus d N₀,
      Real.exp (r * dist x y) ≤ Real.exp (r * dist x u) * Real.exp (r * dist u y)) :=
  ⟨fun x y => Real.one_le_exp (mul_nonneg hr0 dist_nonneg), fun x => by simp,
    fun x u y => by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [dist_triangle x u y])⟩

/-- Weighted row sums of the final operator. -/
theorem finalOp_weighted_row_sum (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {r : ℝ} (hr : r < blockDecayRate d) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) * ‖finalOp d L N₀ k v a x y‖ ≤
      finalDecayC d L * ballConst d (blockDecayRate d - r) := by
  have hterm : ∀ y : L1Torus d N₀, Real.exp (r * dist x y) * ‖finalOp d L N₀ k v a x y‖ ≤
      finalDecayC d L * Real.exp (-(blockDecayRate d - r) * dist x y) := by
    intro y
    have h := finalMass_entry_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2 x y
    calc _ ≤ Real.exp (r * dist x y) *
          (finalDecayC d L * Real.exp (-blockDecayRate d * dist x y)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = finalDecayC d L * (Real.exp (r * dist x y) * Real.exp (-blockDecayRate d * dist x y)) := by
          ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  calc _ ≤ ∑ y : L1Torus d N₀, finalDecayC d L * Real.exp (-(blockDecayRate d - r) * dist x y) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = finalDecayC d L * ∑ y : L1Torus d N₀, Real.exp (-(blockDecayRate d - r) * dist x y) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by linarith) x)
        (finalDecayC_pos hd).le

variable (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
  (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
  (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
include hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ

/-- **Weighted bound of the defect on the closed polydisc.**  With `B_C` the row constant of
`taggedCfin_row_bound` and `A_U` the row constant of `finalOp`: for `‖s p‖ ≤ e^κ`,
`0 ≤ r ≤ ε/8`, `∑_y e^{r dist x y} ‖(C(s) C(s) U - 1) x y‖ ≤ B_C² A_U + 1`.  The bound does
not depend on `M`. -/
theorem taggedCfin_sq_mul_final_weighted_bound {s : MacIdx d N₀ M → ℂ}
    (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) * ‖(Cf s * Cf s * Uf - 1) x y‖ ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (finalDecayC d L * ballConst d (blockDecayRate d - r)) + 1 := by
  have hε := pdEps_pos (d := d) (L := L) hd
  have hδ0 : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hrδ : r < blockDecayRate d := by linarith
  obtain ⟨hw1, hww, hsub⟩ := expw_facts (d := d) (N₀ := N₀) r hr0
  have hw0 : ∀ x y : L1Torus d N₀, 0 ≤ Real.exp (r * dist x y) := fun x y => (Real.exp_pos _).le
  have hBC : 0 ≤ 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
    have : 0 ≤ ballConst d (pdEps d L / 2) := ballConst_decay_nonneg (by positivity)
    positivity
  have hAU : 0 ≤ finalDecayC d L * ballConst d (blockDecayRate d - r) :=
    mul_nonneg (finalDecayC_pos hd).le (ballConst_decay_nonneg (by linarith))
  have hC : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖Cf s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) :=
    fun x => taggedCfin_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hs hr0 hr x
  have hCC : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖(Cf s * Cf s) x y‖ ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) :=
    fun x => weightedRow_mul_le _ hw0 hsub _ _ hBC hC hC x
  have hU : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖Uf x y‖ ≤
      finalDecayC d L * ballConst d (blockDecayRate d - r) :=
    fun x => finalOp_weighted_row_sum hd hk hv0 ha1 ha2 hrδ x
  have hP := weightedRow_mul_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw0 hsub
    (Cf s * Cf s) Uf hAU hCC hU x
  have hone : ∑ y, Real.exp (r * dist x y) * ‖(1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) x y‖
      = 1 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  calc _ ≤ ∑ y, (Real.exp (r * dist x y) * ‖(Cf s * Cf s * Uf) x y‖ +
        Real.exp (r * dist x y) * ‖(1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) x y‖) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by
          simpa only [Matrix.sub_apply] using norm_sub_le _ _) (hw0 _ _)
    _ = _ := by rw [Finset.sum_add_distrib, hone]
    _ ≤ _ := by linarith

/-- The defect `C(s) C(s) U - 1` vanishes at `s = 1`. -/
theorem taggedCfin_sq_mul_final_one :
    Cf (fun _ => 1) * Cf (fun _ => 1) * Uf - 1 = 0 := by
  rw [taggedCfin_one hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ, sub_eq_zero]
  rw [finalMass_sqrt_mul_self hd hk hv0 hv1 ha1 ha2 hmass]
  have hu := (finalMass_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass
    (le_refl (0 : ℝ))).1
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at hu
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)

/-- Every entry of the defect is analytic on the open polydisc. -/
theorem taggedCfin_sq_mul_final_entry_analyticOnNhd (x y : L1Torus d N₀) :
    AnalyticOnNhd ℂ (fun s => (Cf s * Cf s * Uf - 1) x y)
      {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ < Real.exp κ} := by
  intro s hs
  have hC : ∀ p q, AnalyticAt ℂ (fun s => Cf s p q) s := fun p q =>
    taggedCfin_analyticOnNhd (L := L) (k := k) (v := v) (a := a) hd hk hv0 hv1 ha1 ha2 hmass hM
      hκ hMB hMκ p q s hs
  simp only [Matrix.sub_apply, Matrix.mul_apply]
  refine AnalyticAt.sub ?_ analyticAt_const
  refine Finset.analyticAt_fun_sum _ fun u _ => ?_
  refine AnalyticAt.mul ?_ analyticAt_const
  exact Finset.analyticAt_fun_sum _ fun w _ => (hC x w).mul (hC w u)

/-- **Nearest true statement (largest radius).**  On the polydisc `‖s p - 1‖ ≤ δ` centred at
`s = 1`, with `δ < e^κ - 1`, the defect satisfies
`∑_y e^{r dist x y} ‖R(s) x y‖ ≤ (B_C² A_U + 1) δ / (e^κ - 1)`. -/
theorem taggedCfin_sq_mul_final_near_one {s : MacIdx d N₀ M → ℂ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < Real.exp κ - 1) (hsδ : ∀ p, ‖s p - 1‖ ≤ δ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) * ‖(Cf s * Cf s * Uf - 1) x y‖ ≤
      ((4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (finalDecayC d L * ballConst d (blockDecayRate d - r)) + 1) * δ / (Real.exp κ - 1) := by
  classical
  set R : (MacIdx d N₀ M → ℂ) → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
    fun s => Cf s * Cf s * Uf - 1 with hR
  set z : L1Torus d N₀ → ℂ := fun y => R s x y with hz
  set c : L1Torus d N₀ → ℂ := fun y =>
    ((Real.exp (r * dist x y) : ℝ) : ℂ) * ((starRingEnd ℂ) (z y) / ((‖z y‖ : ℝ) : ℂ)) with hc
  have hcz : ∀ y, c y * z y = ((Real.exp (r * dist x y) * ‖z y‖ : ℝ) : ℂ) := by
    intro y
    by_cases h0 : z y = 0
    · simp [hc, h0]
    · have hn : ((‖z y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
      simp only [hc]
      have : (starRingEnd ℂ) (z y) * z y = ((‖z y‖ : ℝ) : ℂ) ^ 2 := by
        rw [mul_comm, Complex.mul_conj']
      rw [Complex.ofReal_mul]
      calc _ = ((Real.exp (r * dist x y) : ℝ) : ℂ) * (((starRingEnd ℂ) (z y) * z y) /
            ((‖z y‖ : ℝ) : ℂ)) := by ring
        _ = _ := by rw [this]; field_simp
  have hcn : ∀ y, ‖c y‖ ≤ Real.exp (r * dist x y) := by
    intro y
    simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_div, Complex.norm_conj, abs_norm]
    by_cases h0 : ‖z y‖ = 0
    · simp [h0, (Real.exp_pos _).le]
    · rw [div_self h0, mul_one]
  set F : (MacIdx d N₀ M → ℂ) → ℂ := fun s => ∑ y, c y * R s x y with hF
  have hFan : AnalyticOnNhd ℂ F {s | ∀ p, ‖s p‖ < Real.exp κ} := by
    intro s' hs'
    refine Finset.analyticAt_fun_sum _ fun y _ => analyticAt_const.mul ?_
    exact taggedCfin_sq_mul_final_entry_analyticOnNhd hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
      x y s' hs'
  have hB : ∀ s' : MacIdx d N₀ M → ℂ, (∀ p, ‖s' p‖ < Real.exp κ) → ‖F s'‖ ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (finalDecayC d L * ballConst d (blockDecayRate d - r)) + 1 := by
    intro s' hs'
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun y _ => ?_).trans
      (taggedCfin_sq_mul_final_weighted_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
        (fun p => (hs' p).le) hr0 hr x))
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      norm_div, Complex.norm_conj, abs_norm]
    by_cases h0 : ‖z y‖ = 0
    · simp [h0, (Real.exp_pos _).le]
    · rw [div_self h0, mul_one]
  have h1 : F (fun _ => 1) = 0 := by
    simp only [hF, hR]
    rw [taggedCfin_sq_mul_final_one hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ]
    simp
  have key := norm_le_of_analyticOnNhd_polydisc_one F hFan hB h1 hδ0 hδ hsδ
  have hFs : F s = ((∑ y, Real.exp (r * dist x y) * ‖(Cf s * Cf s * Uf - 1) x y‖ : ℝ) : ℂ) := by
    simp only [hF]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    exact hcz y
  rw [hFs, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun y _ =>
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] at key
  exact key

/-- **Invertibility near `s = 1`.**  If `B δ ≤ (e^κ - 1)/2`, where
`B = B_C² A_U + 1` is the constant of `taggedCfin_sq_mul_final_weighted_bound`, then for
`‖s p - 1‖ ≤ δ` the matrix `C(s)` is invertible and the weighted row sums of its inverse are at
most `2 B_C A_U`; also the weighted row sums of `(C(s) C(s) U)⁻¹` are at most `2`. -/
theorem taggedCfin_isUnit_near_one {s : MacIdx d N₀ M → ℂ} {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < Real.exp κ - 1) (hsδ : ∀ p, ‖s p - 1‖ ≤ δ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8)
    (hq : ((4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (finalDecayC d L * ballConst d (blockDecayRate d - r)) + 1) * δ ≤ (Real.exp κ - 1) / 2) :
    IsUnit (Cf s) ∧
      (∀ x, ∑ y, Real.exp (r * dist x y) * ‖(Cf s * Cf s * Uf)⁻¹ x y‖ ≤ 2) ∧
      ∀ x, ∑ y, Real.exp (r * dist x y) * ‖(Cf s)⁻¹ x y‖ ≤
        2 * ((4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * (finalDecayC d L * ballConst d (blockDecayRate d - r))) := by
  have hε := pdEps_pos (d := d) (L := L) hd
  have hδ0' : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hrδ : r < blockDecayRate d := by linarith
  have hρ : 0 < Real.exp κ - 1 := lt_trans hδ0 hδ
  obtain ⟨hw1, hww, hsub⟩ := expw_facts (d := d) (N₀ := N₀) r hr0
  have hw0 : ∀ x y : L1Torus d N₀, 0 ≤ Real.exp (r * dist x y) := fun x y => (Real.exp_pos _).le
  have hBC : 0 ≤ 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
    have : 0 ≤ ballConst d (pdEps d L / 2) := ballConst_decay_nonneg (by positivity)
    positivity
  have hAU : 0 ≤ finalDecayC d L * ballConst d (blockDecayRate d - r) :=
    mul_nonneg (finalDecayC_pos hd).le (ballConst_decay_nonneg (by linarith))
  have hnear := fun x => taggedCfin_sq_mul_final_near_one hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB
    hMκ hδ0 hδ hsδ hr0 hr x
  have hK : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖(-(Cf s * Cf s * Uf - 1)) x y‖ ≤ 1 / 2 := by
    intro x
    simp only [Matrix.neg_apply, norm_neg]
    refine (hnear x).trans ?_
    rw [div_le_iff₀ hρ]
    linarith
  have hinv := weightedRow_inv_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw1 hww hsub
    (-(Cf s * Cf s * Uf - 1)) (q := 1 / 2) (by norm_num) hK
  have hP : (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) - -(Cf s * Cf s * Uf - 1) =
      Cf s * Cf s * Uf := by abel
  rw [hP] at hinv
  have h2 : 1 / (1 - (1 / 2 : ℝ)) = 2 := by norm_num
  rw [h2] at hinv
  obtain ⟨hPu, hPb⟩ := hinv
  have hdet : IsUnit (Cf s).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 hPu
    rw [Matrix.det_mul, Matrix.det_mul] at this
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left this)
  have hCu : IsUnit (Cf s) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  refine ⟨hCu, hPb, ?_⟩
  have hinvC : (Cf s)⁻¹ = Cf s * Uf * (Cf s * Cf s * Uf)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc Cf s * (Cf s * Uf * (Cf s * Cf s * Uf)⁻¹) = (Cf s * Cf s * Uf) * (Cf s * Cf s * Uf)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hPu)
  have hC : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖Cf s x y‖ ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := fun x =>
    taggedCfin_row_bound hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ
      (fun p => by
        have := hsδ p
        calc ‖s p‖ = ‖(s p - 1) + 1‖ := by ring_nf
          _ ≤ ‖s p - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ ≤ δ + 1 := by rw [norm_one]; linarith
          _ ≤ Real.exp κ := by linarith) hr0 hr x
  have hU : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖Uf x y‖ ≤
      finalDecayC d L * ballConst d (blockDecayRate d - r) :=
    fun x => finalOp_weighted_row_sum hd hk hv0 ha1 ha2 hrδ x
  have hCU : ∀ x, ∑ y, Real.exp (r * dist x y) * ‖(Cf s * Uf) x y‖ ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * (finalDecayC d L * ballConst d (blockDecayRate d - r)) :=
    fun x => weightedRow_mul_le _ hw0 hsub _ _ hAU hC hU x
  intro x
  rw [hinvC]
  exact (weightedRow_mul_le _ hw0 hsub _ _ (by norm_num) hCU hPb x).trans_eq (mul_comm _ _)

end Pos

end Balaban.Green
