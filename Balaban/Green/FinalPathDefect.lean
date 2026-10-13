/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxResolvent
public import Balaban.Green.FinalMacroCover
public import Balaban.Green.FinalMassGreen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The path defect of the box-resolvent parametrix is small (FINALFAM leaf 3, rows)

This file belongs to the "path-tagged macroblock parametrix" of `notes/phase1/FINALFAM.md`, §4–§5.
**The construction is proposed in that note.  The papers print no formula for it** (question 18 to
the author is pending); nothing here claims it is the papers' construction.

Let `U` be the final operator in the mass window of `finalMass_resolvent_decay`, `t ≥ 0`, and
let `B_z`, `χ_z` be the boxes and the partition of unity of the macro cover at scale `M`.  Put
`ε = min (δ₀, r_*)`, where `δ₀` is the entry decay rate of `U` and `r_*` the decay rate of the
box resolvent.

* `boxR_final_entry_bound` (T1): the defect `R_z = -[U, χ_z] G_z` of one box satisfies
  `‖R_z x y‖ ≤ (C₁ / M) · (g_* + t)⁻¹ · exp (-(ε/2) dist x y)`, with `C₁` independent of
  `M`, `t`, `z`, the torus size and `k`.  The factor `1/M` is the Lipschitz constant of `χ_z`.
* `taggedK_row_sum` (T2): for tag parameters `s` with `‖s p‖ ≤ e^κ`, the tagged defect satisfies
  `∑_y e^{r dist x y} ‖K(s,t) x y‖ ≤ q`, `q = B e^{H κ} / M`, as soon as `r ≤ ε/8` and
  `κ 7^d ≤ (ε/8) M`.  With `r = 0` this is the weighted row-sum hypothesis (weight `ω ≡ 1`) of
  `taggedGfin_of_weighted_row_sum`; `taggedK_weighted_row_sum` gives the weight
  `ω x = e^{r dist x₀ x}`.
* `taggedGfin_final` (T3): for `M ≥ 4 B e^{Hκ}` (so `q ≤ 1/4`) and `M ≥ 8 κ 7^d / ε`, `1 - K(s,t)`
  is invertible on the closed polydisc `‖s p‖ ≤ e^κ`, the entries of `G_fin(s,t)` are analytic
  there, and `G_fin(1,t) = (U + t)⁻¹`.
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Defs

open scoped Classical in
/-- The box `B_z` of the macro cover as a finite set. -/
noncomputable def macBoxF (d N₀ M : ℕ) [NeZero N₀] (z : MacIdx d N₀ M) : Finset (L1Torus d N₀) :=
  univ.filter fun x => x ∈ macBox d N₀ M z

theorem mem_macBoxF {d N₀ M : ℕ} [NeZero N₀] {z : MacIdx d N₀ M} {x : L1Torus d N₀} :
    x ∈ macBoxF d N₀ M z ↔ x ∈ macBox d N₀ M z := by
  classical
  simp [macBoxF]

/-- The rate `ε = min (δ₀, r_*)`. -/
noncomputable def pdEps (d L : ℕ) : ℝ := min (blockDecayRate d) (finalRate d L)

/-- The Lipschitz constant `1 + 2·7^d` of the cutoffs (times `1/M`). -/
noncomputable def pdLip (d : ℕ) : ℝ := 1 + 2 * 7 ^ d

/-- The constant `C₁` of T1. -/
noncomputable def pdC1 (d L : ℕ) : ℝ :=
  8 * finalDecayC d L * pdLip d / pdEps d L * ballConst d (pdEps d L / 4)

/-- The constant `H = 16^d + 9 d 7^d` of the tag count. -/
noncomputable def pdH (d : ℕ) : ℝ := 16 ^ d + 9 * d * 7 ^ d

/-- The constant `B` of T2. -/
noncomputable def pdB (d L : ℕ) : ℝ :=
  16 * 7 ^ d * finalDecayC d L * pdLip d / (finalGap d L * pdEps d L) *
    (ballConst d (pdEps d L / 2) * ballConst d (3 * pdEps d L / 4))

theorem pdEps_pos {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 < pdEps d L :=
  lt_min (blockDecayRate_pos hd) (finalRate_pos hd)

open scoped Classical in
/-- Indicator that `z` is a cell whose box contains `x` or `w`. -/
noncomputable def pdInd {d N₀ M : ℕ} [NeZero N₀] (z : MacIdx d N₀ M) (x w : L1Torus d N₀) : ℝ :=
  if x ∈ macBox d N₀ M z ∨ w ∈ macBox d N₀ M z then 1 else 0

theorem pdInd_nonneg {d N₀ M : ℕ} [NeZero N₀] (z : MacIdx d N₀ M) (x w : L1Torus d N₀) :
    0 ≤ pdInd z x w := by
  unfold pdInd; split_ifs <;> norm_num

theorem pdInd_le_one {d N₀ M : ℕ} [NeZero N₀] (z : MacIdx d N₀ M) (x w : L1Torus d N₀) :
    pdInd z x w ≤ 1 := by
  unfold pdInd; split_ifs <;> norm_num

theorem sum_pdInd_le {d N₀ M : ℕ} [NeZero N₀] (hM : 0 < M) (x w : L1Torus d N₀) :
    ∑ z : MacIdx d N₀ M, pdInd z x w ≤ 2 * 7 ^ d := by
  classical
  have h1 : ∀ z : MacIdx d N₀ M, pdInd z x w ≤
      (if x ∈ macBox d N₀ M z then 1 else 0) + (if w ∈ macBox d N₀ M z then 1 else 0) := by
    intro z
    unfold pdInd
    by_cases hx : x ∈ macBox d N₀ M z <;> by_cases hw : w ∈ macBox d N₀ M z <;> simp [hx, hw]
  refine (Finset.sum_le_sum fun z _ => h1 z).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have hx := macBox_overlap (d := d) (m := N₀) hM x
  have hw := macBox_overlap (d := d) (m := N₀) hM w
  have hx' : ((univ.filter fun z : MacIdx d N₀ M => x ∈ macBox d N₀ M z).card : ℝ) ≤ 7 ^ d := by
    exact_mod_cast hx
  have hw' : ((univ.filter fun z : MacIdx d N₀ M => w ∈ macBox d N₀ M z).card : ℝ) ≤ 7 ^ d := by
    exact_mod_cast hw
  convert add_le_add hx' hw' using 1
  ring

end Defs

section Analysis

/-- `a e^{-p a} ≤ (1/s) e^{-(p - s) a}` for `s > 0`, `a ≥ 0`. -/
theorem mul_exp_le {a p s : ℝ} (hs : 0 < s) :
    a * Real.exp (-p * a) ≤ (1 / s) * Real.exp (-(p - s) * a) := by
  have h1 : s * a + 1 ≤ Real.exp (s * a) := Real.add_one_le_exp _
  have h2 : a ≤ (1 / s) * Real.exp (s * a) := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
    nlinarith
  calc a * Real.exp (-p * a) ≤ (1 / s) * Real.exp (s * a) * Real.exp (-p * a) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (1 / s) * Real.exp (-(p - s) * a) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end Analysis

section Defect

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- Entry bound of one defect, before summing: the sum runs over the intermediate site `w`. -/
theorem boxR_final_le_sum (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) (z : MacIdx d N₀ M) (x y : L1Torus d N₀) :
    ‖boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
        (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t x y‖ ≤
      2 * finalDecayC d L * pdLip d / (M * (finalGap d L + t)) *
        ∑ w, pdInd z x w * (dist x w * Real.exp (-pdEps d L * (dist x w + dist w y))) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε := pdEps_pos (d := d) (L := L) hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hsupp : ∀ u, ((macChi d N₀ M z u : ℝ) : ℂ) ≠ 0 → u ∈ macBoxF d N₀ M z := fun u hu =>
    mem_macBoxF.2 (macChi_mem_box hM (by exact_mod_cast hu))
  rw [boxR_eq_neg_commutator (boxH_isUnit_final hd hk hv0 hv1 ha1 ha2 hmass ht _) hsupp,
    Matrix.neg_apply, norm_neg, Matrix.mul_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : x ∈ macBox d N₀ M z ∨ w ∈ macBox d N₀ M z
  · have hind : pdInd z x w = 1 := by unfold pdInd; simp [h]
    rw [hind, one_mul]
    set A := dist x w with hA
    set b := dist w y with hb
    have hA0 : 0 ≤ A := dist_nonneg
    have hb0 : 0 ≤ b := dist_nonneg
    have hU := finalMass_entry_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2 x w
    have hG := boxG_final_entry_bound (L := L) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht
      (macBoxF d N₀ M z) w y
    have hΔ : ‖((macChi d N₀ M z w : ℝ) : ℂ) - ((macChi d N₀ M z x : ℝ) : ℂ)‖ ≤
        pdLip d * (A / M) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact macChi_lipschitz hM z x w
    have e1 : Real.exp (-blockDecayRate d * A) ≤ Real.exp (-pdEps d L * A) := by
      apply Real.exp_le_exp.2
      have : pdEps d L ≤ blockDecayRate d := min_le_left _ _
      nlinarith
    have e2 : Real.exp (-finalRate d L * b) ≤ Real.exp (-pdEps d L * b) := by
      apply Real.exp_le_exp.2
      have : pdEps d L ≤ finalRate d L := min_le_right _ _
      nlinarith
    have e3 : Real.exp (-pdEps d L * (A + b)) =
        Real.exp (-pdEps d L * A) * Real.exp (-pdEps d L * b) := by
      rw [← Real.exp_add]; congr 1; ring
    have hrw : (finalOp d L N₀ k v a x w * ((macChi d N₀ M z w : ℝ) : ℂ) -
        ((macChi d N₀ M z x : ℝ) : ℂ) * finalOp d L N₀ k v a x w) *
        boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t w y =
        finalOp d L N₀ k v a x w * (((macChi d N₀ M z w : ℝ) : ℂ) -
          ((macChi d N₀ M z x : ℝ) : ℂ)) *
        boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t w y := by ring
    rw [hrw, norm_mul, norm_mul]
    have hC := (finalDecayC_pos (L := L) hd).le
    have hlip : 0 ≤ pdLip d := by unfold pdLip; positivity
    calc _ ≤ (finalDecayC d L * Real.exp (-pdEps d L * A)) * (pdLip d * (A / M)) *
          (2 / (finalGap d L + t) * Real.exp (-pdEps d L * b)) := by
          gcongr
          · exact hU.trans (by gcongr)
          · exact hG.trans (by gcongr)
      _ = _ := by
          rw [e3]; field_simp
  · replace h := not_or.1 h
    have hx : macChi d N₀ M z x = 0 := by
      by_contra hc; exact h.1 (macChi_mem_box hM hc)
    have hw : macChi d N₀ M z w = 0 := by
      by_contra hc; exact h.2 (macChi_mem_box hM hc)
    have hind : pdInd z x w = 0 := by unfold pdInd; simp [h.1, h.2]
    simp [hx, hw, hind]

/-- **T1.** Entry bound of one defect: for `U = finalOp` in the mass window, `t ≥ 0`, a cell `z`
of the macro cover at scale `M`,
`‖R_z x y‖ ≤ (C₁ / M) · (g_* + t)⁻¹ · exp (-(ε/2) dist x y)`.  The constants `C₁ = pdC1 d L` and
`ε = pdEps d L` depend on `d` and `L` only. -/
theorem boxR_final_entry_bound (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) (z : MacIdx d N₀ M) (x y : L1Torus d N₀) :
    ‖boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
        (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t x y‖ ≤
      pdC1 d L / M * (1 / (finalGap d L + t)) * Real.exp (-(pdEps d L / 2) * dist x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε := pdEps_pos (d := d) (L := L) hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  refine (boxR_final_le_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM z x y).trans ?_
  have hterm : ∀ w : L1Torus d N₀,
      pdInd z x w * (dist x w * Real.exp (-pdEps d L * (dist x w + dist w y))) ≤
        (4 / pdEps d L) * Real.exp (-(pdEps d L / 4) * dist x w) *
          Real.exp (-(pdEps d L / 2) * dist x y) := by
    intro w
    have hA0 : 0 ≤ dist x w := dist_nonneg
    have hb0 : 0 ≤ dist w y := dist_nonneg
    have htri : dist x y ≤ dist x w + dist w y := dist_triangle x w y
    have h1 : Real.exp (-pdEps d L * (dist x w + dist w y)) ≤
        Real.exp (-(pdEps d L / 2) * dist x w) * Real.exp (-(pdEps d L / 2) * dist x y) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have h2 := mul_exp_le (a := dist x w) (p := pdEps d L / 2) (s := pdEps d L / 4)
      (by positivity)
    have h3 : (1 / (pdEps d L / 4)) = 4 / pdEps d L := by field_simp
    have h4 : -(pdEps d L / 2 - pdEps d L / 4) = -(pdEps d L / 4) := by ring
    rw [h3, h4] at h2
    have hexp : 0 ≤ Real.exp (-(pdEps d L / 2) * dist x y) := (Real.exp_pos _).le
    calc _ ≤ 1 * (dist x w * Real.exp (-pdEps d L * (dist x w + dist w y))) :=
          mul_le_mul_of_nonneg_right (pdInd_le_one z x w) (by positivity)
      _ ≤ dist x w * (Real.exp (-(pdEps d L / 2) * dist x w) *
            Real.exp (-(pdEps d L / 2) * dist x y)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left h1 hA0
      _ = (dist x w * Real.exp (-(pdEps d L / 2) * dist x w)) *
            Real.exp (-(pdEps d L / 2) * dist x y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hexp
  have hsum : ∑ w : L1Torus d N₀,
      pdInd z x w * (dist x w * Real.exp (-pdEps d L * (dist x w + dist w y))) ≤
        (4 / pdEps d L) * ballConst d (pdEps d L / 4) * Real.exp (-(pdEps d L / 2) * dist x y) := by
    refine (Finset.sum_le_sum fun w _ => hterm w).trans ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by positivity) x) (by positivity)
  have hA : 0 ≤ 2 * finalDecayC d L * pdLip d / (M * (finalGap d L + t)) := by
    have := (finalDecayC_pos (L := L) hd).le
    have : 0 ≤ pdLip d := by unfold pdLip; positivity
    positivity
  refine (mul_le_mul_of_nonneg_left hsum hA).trans (le_of_eq ?_)
  unfold pdC1
  field_simp
  ring

end Defect

section Tagged

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- Termwise bound used for the double sum in T2. -/
theorem pd_double_term {σ ε : ℝ} (hε : 0 < ε) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ε / 4)
    (x w y : L1Torus d N₀) :
    Real.exp (σ * dist x y) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) ≤
      (4 / ε) * Real.exp (-(ε / 2) * dist x w) * Real.exp (-(3 * ε / 4) * dist w y) := by
  have hA0 : 0 ≤ dist x w := dist_nonneg
  have hb0 : 0 ≤ dist w y := dist_nonneg
  have htri : dist x y ≤ dist x w + dist w y := dist_triangle x w y
  have h1 : Real.exp (σ * dist x y) * Real.exp (-ε * (dist x w + dist w y)) ≤
      Real.exp (-(3 * ε / 4) * dist x w) * Real.exp (-(3 * ε / 4) * dist w y) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : σ * dist x y ≤ σ * (dist x w + dist w y) := mul_le_mul_of_nonneg_left htri hσ0
    nlinarith
  have h2 := mul_exp_le (a := dist x w) (p := 3 * ε / 4) (s := ε / 4) (by positivity)
  have h3 : (1 / (ε / 4)) = 4 / ε := by field_simp
  have h4 : -(3 * ε / 4 - ε / 4) = -(ε / 2) := by ring
  rw [h3, h4] at h2
  calc _ = dist x w * (Real.exp (σ * dist x y) * Real.exp (-ε * (dist x w + dist w y))) := by ring
    _ ≤ dist x w * (Real.exp (-(3 * ε / 4) * dist x w) * Real.exp (-(3 * ε / 4) * dist w y)) :=
        mul_le_mul_of_nonneg_left h1 hA0
    _ = (dist x w * Real.exp (-(3 * ε / 4) * dist x w)) * Real.exp (-(3 * ε / 4) * dist w y) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- The double sum in T2. -/
theorem pd_double_sum {σ ε : ℝ} (hε : 0 < ε) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ε / 4)
    (x : L1Torus d N₀) :
    ∑ y : L1Torus d N₀, ∑ w : L1Torus d N₀,
        Real.exp (σ * dist x y) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) ≤
      (4 / ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4)) := by
  have h1 : ∑ y : L1Torus d N₀, ∑ w : L1Torus d N₀,
        Real.exp (σ * dist x y) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) ≤
      ∑ y : L1Torus d N₀, ∑ w : L1Torus d N₀, (4 / ε) * Real.exp (-(ε / 2) * dist x w) *
        Real.exp (-(3 * ε / 4) * dist w y) :=
    Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun w _ => pd_double_term hε hσ0 hσ x w y
  refine h1.trans ?_
  rw [Finset.sum_comm]
  have h2 : ∀ w : L1Torus d N₀, ∑ y : L1Torus d N₀, (4 / ε) * Real.exp (-(ε / 2) * dist x w) *
        Real.exp (-(3 * ε / 4) * dist w y) ≤
      (4 / ε) * Real.exp (-(ε / 2) * dist x w) * ballConst d (3 * ε / 4) := by
    intro w
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by positivity) w) (by positivity)
  refine (Finset.sum_le_sum fun w _ => h2 w).trans ?_
  rw [← Finset.sum_mul]
  have : ∑ w : L1Torus d N₀, (4 / ε) * Real.exp (-(ε / 2) * dist x w) =
      (4 / ε) * ∑ w : L1Torus d N₀, Real.exp (-(ε / 2) * dist x w) := by rw [Finset.mul_sum]
  rw [this]
  have hb : 0 ≤ ballConst d (3 * ε / 4) := ballConst_decay_nonneg (by positivity)
  calc _ ≤ (4 / ε) * ballConst d (ε / 2) * ballConst d (3 * ε / 4) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by positivity) x) (by positivity)) hb
    _ = _ := by ring

/-- The tag monomial is bounded by `e^{κ |V|}` on the polydisc `‖s p‖ ≤ e^κ`. -/
theorem norm_tagMon_le {Pc : Type*} (V : Finset Pc) {s : Pc → ℂ} {κ : ℝ}
    (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) : ‖tagMon V s‖ ≤ Real.exp (κ * V.card) := by
  unfold tagMon
  rw [norm_prod]
  calc ∏ p ∈ V, ‖s p‖ ≤ ∏ _p ∈ V, Real.exp κ :=
        Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => hs p
    _ = Real.exp (κ * V.card) := by
        rw [Finset.prod_const, mul_comm, Real.exp_nat_mul]

/-- **T2.** Row sums of the tagged defect.  For tag parameters `s` with `‖s p‖ ≤ e^κ`,
`0 ≤ r ≤ ε/8` and `κ 7^d ≤ (ε/8) M`:
`∑_y e^{r dist x y} ‖K(s,t) x y‖ ≤ B e^{H κ} / M`, with `B = pdB d L`, `H = pdH d`. -/
theorem taggedK_row_sum (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) *
        ‖taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤
      pdB d L * Real.exp (pdH d * κ) / M := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε := pdEps_pos (d := d) (L := L) hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hC := (finalDecayC_pos (L := L) hd).le
  have hlip : 0 ≤ pdLip d := by unfold pdLip; positivity
  set ε := pdEps d L with hεdef
  set σ : ℝ := r + κ * 7 ^ d / M with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  have hσ : σ ≤ ε / 4 := by
    have : κ * 7 ^ d / M ≤ ε / 8 := by rw [div_le_iff₀ hM']; linarith
    linarith
  set A₀ : ℝ := 2 * finalDecayC d L * pdLip d / (M * (finalGap d L + t)) with hA₀
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hA₀le : A₀ ≤ 2 * finalDecayC d L * pdLip d / (M * finalGap d L) := by
    rw [hA₀]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  -- pointwise bound on the entries
  have hentry : ∀ y : L1Torus d N₀,
      ‖taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤
        Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
          (A₀ * (2 * 7 ^ d)) *
          ∑ w, dist x w * Real.exp (-ε * (dist x w + dist w y)) := by
    intro y
    have hE : ∀ z : MacIdx d N₀ M, ‖tagMon (macTags d N₀ M z x y) s‖ ≤
        Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) := by
      intro z
      refine (norm_tagMon_le _ hs).trans ?_
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := macTags_card_le hM z x y
      unfold pdH
      nlinarith
    unfold taggedK taggedMat
    rw [Matrix.of_apply]
    refine (norm_sum_le _ _).trans ?_
    have hz : ∀ z ∈ (Finset.univ : Finset (MacIdx d N₀ M)),
        ‖tagMon (macTags d N₀ M z x y) s *
            boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t x y‖ ≤
          Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) * A₀ *
            ∑ w, pdInd z x w * (dist x w * Real.exp (-ε * (dist x w + dist w y))) := by
      intro z _
      rw [norm_mul]
      calc _ ≤ (Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M))) *
            (A₀ * ∑ w, pdInd z x w * (dist x w * Real.exp (-ε * (dist x w + dist w y)))) :=
            mul_le_mul (hE z) (boxR_final_le_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM z x y)
              (norm_nonneg _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hz).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have hF : ∀ w : L1Torus d N₀, 0 ≤ dist x w * Real.exp (-ε * (dist x w + dist w y)) :=
      fun w => mul_nonneg dist_nonneg (Real.exp_pos _).le
    have hle : ∑ w, (∑ z : MacIdx d N₀ M, pdInd z x w) *
          (dist x w * Real.exp (-ε * (dist x w + dist w y))) ≤
        ∑ w, (2 * 7 ^ d) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) :=
      Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (sum_pdInd_le hM x w) (hF w)
    rw [← Finset.mul_sum] at hle
    calc _ ≤ Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) * A₀ *
          ((2 * 7 ^ d) * ∑ w, dist x w * Real.exp (-ε * (dist x w + dist w y))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by ring
  have hexp : ∀ y : L1Torus d N₀, Real.exp (r * dist x y) *
      Real.exp (κ * 7 ^ d * (dist x y / M)) = Real.exp (σ * dist x y) := by
    intro y
    rw [← Real.exp_add]; congr 1; simp only [hσdef]; ring
  have hdbl := pd_double_sum (d := d) (N₀ := N₀) hε hσ0 hσ x
  calc _ ≤ ∑ y : L1Torus d N₀, Real.exp (r * dist x y) *
        (Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
          (A₀ * (2 * 7 ^ d)) *
          ∑ w, dist x w * Real.exp (-ε * (dist x w + dist w y))) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hentry y) (Real.exp_pos _).le
    _ = Real.exp (pdH d * κ) * (A₀ * (2 * 7 ^ d)) * ∑ y : L1Torus d N₀, ∑ w : L1Torus d N₀,
          Real.exp (σ * dist x y) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.mul_sum, ← hexp y]; ring
    _ ≤ Real.exp (pdH d * κ) * (A₀ * (2 * 7 ^ d)) *
          ((4 / ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) :=
        mul_le_mul_of_nonneg_left hdbl (by positivity)
    _ ≤ Real.exp (pdH d * κ) * ((2 * finalDecayC d L * pdLip d / (M * finalGap d L)) * (2 * 7 ^ d)) *
          ((4 / ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4))) := by
        have hb1 : 0 ≤ ballConst d (ε / 2) := ballConst_decay_nonneg (by positivity)
        have hb2 : 0 ≤ ballConst d (3 * ε / 4) := ballConst_decay_nonneg (by positivity)
        gcongr
    _ = _ := by
        unfold pdB
        simp only [← hεdef]
        field_simp
        ring_nf

/-- **T2, weighted form.**  With the weight `ω x = e^{r dist x₀ x}` the weighted row sums of the
tagged defect are at most `B e^{H κ} / M`; this is the hypothesis `hD` of
`taggedGfin_of_weighted_row_sum`. -/
theorem taggedK_weighted_row_sum (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x₀ x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x₀ x) *
        ‖taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ / Real.exp (r * dist x₀ y) ≤
      pdB d L * Real.exp (pdH d * κ) / M := by
  refine le_trans (Finset.sum_le_sum fun y _ => ?_)
    (taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x)
  rw [mul_div_right_comm, ← Real.exp_sub]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.2
  have h1 : dist x₀ x ≤ dist x₀ y + dist x y := (dist_triangle x₀ y x).trans_eq (by rw [dist_comm y x])
  nlinarith

/-- **T3.**  For `M ≥ 4 B e^{H κ}` (so that `q = B e^{Hκ}/M ≤ 1/4`) and `M ≥ 8 κ 7^d / ε`, on the
closed polydisc `‖s p‖ ≤ e^κ` the matrix `1 - K(s,t)` is invertible, the entries of `G_fin(s,t)`
are analytic, and `G_fin(1,t) = (U + t)⁻¹`. -/
theorem taggedGfin_final (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 ∧
    (∀ s ∈ {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ ≤ Real.exp κ},
      IsUnit (1 - taggedK Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
        (finalOp d L N₀ k v a) t s)) ∧
    (∀ x y, AnalyticOnNhd ℂ (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
        (finalOp d L N₀ k v a) t s x y) {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ ≤ Real.exp κ}) ∧
    taggedGfin Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
        (finalOp d L N₀ k v a) t (fun _ => 1) =
      (shiftMat (finalOp d L N₀ k v a) t)⁻¹ := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hε := pdEps_pos (d := d) (L := L) hd
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have hD := taggedGfin_of_weighted_row_sum Finset.univ (macBoxF d N₀ M)
    (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
    (fun u => by exact_mod_cast macChi_sum (d := d) (m := N₀) (M := M) u)
    (macTags d N₀ M) (finalOp d L N₀ k v a) t (ω := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (q := pdB d L * Real.exp (pdH d * κ) / M) (by linarith)
    {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ ≤ Real.exp κ} (by
      intro s hs x
      have := taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ le_rfl
        (by positivity) hκM hs x
      simpa using this)
  exact ⟨hq, hD.1, hD.2.1, hD.2.2 (fun p => by simpa using Real.one_le_exp hκ)⟩

end Tagged

end Balaban.Green
