/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTaggedRow

/-!
# Column estimates for the final tagged parametrix without loss of decay rate

The pointwise commutator bound controls both endpoint sums. Summing the intermediate
site last proves the column contraction with exactly the row constant `pdB`.
No symmetry of `macTags`, `boxR` or the complex tagged family is required.
This completes the optional same-rate column estimate in FINALFAM2, T1.
It concerns the proposed reference family, not the physical final integral.
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Column norms of a product, obtained by transposing both factors in reverse order. -/
theorem weightedColumn_mul_le (w : ι → ι → ℝ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hsub : ∀ x u y, w x y ≤ w x u * w u y) (A B : Matrix ι ι ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hA : ∀ u, ∑ x, w x u * ‖A x u‖ ≤ a)
    (hB : ∀ y, ∑ u, w u y * ‖B u y‖ ≤ b) (y : ι) :
    ∑ x, w x y * ‖(A * B) x y‖ ≤ a * b := by
  have h := weightedRow_mul_le (fun x y => w y x) (fun x y => hw0 y x)
    (fun x u y => (hsub y u x).trans_eq (mul_comm _ _)) Bᵀ Aᵀ ha hB hA y
  simpa only [← Matrix.transpose_mul, Matrix.transpose_apply, mul_comm b a] using h

/-- Column contraction bounds the column norm of the inverse, without symmetry. -/
theorem weightedColumn_inv_le (w : ι → ι → ℝ) (hw1 : ∀ x y, 1 ≤ w x y)
    (hww : ∀ x, w x x = 1) (hsub : ∀ x u y, w x y ≤ w x u * w u y)
    (K : Matrix ι ι ℂ) {q : ℝ} (hq : q < 1)
    (hK : ∀ y, ∑ x, w x y * ‖K x y‖ ≤ q) :
    IsUnit (1 - K) ∧ ∀ y, ∑ x, w x y * ‖(1 - K)⁻¹ x y‖ ≤ 1 / (1 - q) := by
  have h := weightedRow_inv_le (fun x y => w y x) (fun x y => hw1 y x) hww
    (fun x u y => (hsub y u x).trans_eq (mul_comm _ _)) Kᵀ hq hK
  have heq : 1 - Kᵀ = (1 - K)ᵀ := by rw [Matrix.transpose_sub, Matrix.transpose_one]
  rw [heq, ← Matrix.transpose_nonsing_inv] at h
  exact ⟨(Matrix.isUnit_transpose _).mp h.1, h.2⟩

end Generic

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The scalar convolution majorant has the same column and row bound. -/
theorem pd_double_sum_column {σ ε : ℝ} (hε : 0 < ε) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ε / 4)
    (y : L1Torus d N₀) :
    ∑ x : L1Torus d N₀, ∑ w : L1Torus d N₀,
        Real.exp (σ * dist x y) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) ≤
      (4 / ε) * (ballConst d (ε / 2) * ballConst d (3 * ε / 4)) := by
  refine (Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun w _ =>
    pd_double_term hε hσ0 hσ x w y).trans ?_
  rw [Finset.sum_comm]
  have hinner : ∀ w : L1Torus d N₀,
      ∑ x, (4 / ε) * Real.exp (-(ε / 2) * dist x w) *
        Real.exp (-(3 * ε / 4) * dist w y) ≤
      ((4 / ε) * ballConst d (ε / 2)) * Real.exp (-(3 * ε / 4) * dist w y) := by
    intro w
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [dist_comm] using ballSum_L1Torus d N₀ (show 0 < ε / 2 by positivity) w
  refine (Finset.sum_le_sum fun w _ => hinner w).trans ?_
  rw [← Finset.mul_sum]
  have hb : 0 ≤ ballConst d (ε / 2) := ballConst_decay_nonneg (by positivity)
  calc _ ≤ ((4 / ε) * ballConst d (ε / 2)) * ballConst d (3 * ε / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [dist_comm] using
            ballSum_L1Torus d N₀ (show 0 < 3 * ε / 4 by positivity) y
    _ = _ := by ring

/-- The tagged defect contracts in the weighted column norm with the same constant
and rate as `taggedK_row_sum`. -/
theorem taggedK_column_sum (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (y : L1Torus d N₀) :
    ∑ x, Real.exp (r * dist x y) *
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
  have hentry := fun x => taggedK_entry_le_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hs x y
  have hexp : ∀ x : L1Torus d N₀, Real.exp (r * dist x y) *
      Real.exp (κ * 7 ^ d * (dist x y / M)) = Real.exp (σ * dist x y) := by
    intro x
    rw [← Real.exp_add]; congr 1; simp only [hσdef]; ring
  have hdbl := pd_double_sum_column (d := d) (N₀ := N₀) hε hσ0 hσ y
  calc _ ≤ ∑ x : L1Torus d N₀, Real.exp (r * dist x y) *
        (Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
          (A₀ * (2 * 7 ^ d)) *
          ∑ w, dist x w * Real.exp (-ε * (dist x w + dist w y))) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hentry x) (Real.exp_pos _).le
    _ = Real.exp (pdH d * κ) * (A₀ * (2 * 7 ^ d)) * ∑ x : L1Torus d N₀, ∑ w : L1Torus d N₀,
          Real.exp (σ * dist x y) * (dist x w * Real.exp (-ε * (dist x w + dist w y))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum, ← hexp x]; ring
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


/-- Column bound for the tagged approximate Green function at the full rate. -/
theorem taggedG_column_sum (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (y : L1Torus d N₀) :
    ∑ x, Real.exp (r * dist x y) *
        ‖taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤ taggedA0 d L κ t := by
  have hg := finalGap_pos (d := d) (Nat.pos_of_ne_zero (NeZero.ne L))
  have hε := pdEps_pos (d := d) (L := L) hd
  let ε := pdEps d L
  have hentry := fun x => taggedG_weighted_entry_bound hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x y
  calc _ ≤ ∑ x : L1Torus d N₀, 2 * Real.exp (pdH d * κ) / (finalGap d L + t) *
        Real.exp (-(ε / 2) * dist x y) := Finset.sum_le_sum fun x _ => hentry x
    _ = 2 * Real.exp (pdH d * κ) / (finalGap d L + t) *
        ∑ x : L1Torus d N₀, Real.exp (-(ε / 2) * dist x y) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp (pdH d * κ) / (finalGap d L + t) * ballConst d (ε / 2) :=
        mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using ballSum_L1Torus d N₀ (show 0 < ε / 2 by positivity) y) (by positivity)
    _ = taggedA0 d L κ t := by unfold taggedA0; ring

/-- Column bound for the final tagged resolvent at the full row rate, with no extra
ball constant and under exactly the existing macro-scale conditions. -/
theorem taggedGfin_column_bound_same_rate (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (y : L1Torus d N₀) :
    ∑ x, Real.exp (r * dist x y) *
        ‖taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤ 4 / 3 * taggedA0 d L κ t := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hε := pdEps_pos (d := d) (L := L) hd
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have hw1 : ∀ x y : L1Torus d N₀, 1 ≤ Real.exp (r * dist x y) := fun x y =>
    Real.one_le_exp (mul_nonneg hr0 dist_nonneg)
  have hww : ∀ x : L1Torus d N₀, Real.exp (r * dist x x) = 1 := fun x => by simp
  have hsub : ∀ x u y : L1Torus d N₀,
      Real.exp (r * dist x y) ≤ Real.exp (r * dist x u) * Real.exp (r * dist u y) := by
    intro x u y
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [dist_triangle x u y])
  have hinv := weightedColumn_inv_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw1 hww hsub
    (taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t s) (q := 1 / 4) (by norm_num)
    (fun x => (taggedK_column_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x).trans hq)
  have h43 : 1 / (1 - (1 / 4 : ℝ)) = 4 / 3 := by norm_num
  rw [h43] at hinv
  have hA0 := taggedA0_nonneg (d := d) (L := L) hd hL (κ := κ) ht
  unfold taggedGfin
  rw [mul_comm (4 / 3 : ℝ)]
  exact weightedColumn_mul_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y))
    (fun x y => (Real.exp_pos _).le) hsub _ _ hA0 (a := taggedA0 d L κ t)
    (fun y => taggedG_column_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs y)
    hinv.2 y

end Balaban.Green
