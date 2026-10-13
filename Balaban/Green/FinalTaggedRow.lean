/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalPathDefect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A weighted row bound for the tagged parametrix family (FINALFAM2, T2)

This file belongs to the "path-tagged macroblock parametrix" of `notes/phase1/FINALFAM.md`.
**The construction is proposed in FINALFAM; the papers print no formula for it** (question 18 to
the author is pending); nothing here claims it is the papers' construction.

Fix `d`, `L`, `N₀`, `k`, the final operator `U` in the mass window, a macro scale `M` and tag
parameters `s` with `‖s p‖ ≤ e^κ`.  Write `w x y = e^{r dist x y}`.

* `weightedRow_inv_le` (generic): if `w ≥ 1`, `w x x = 1` and `w x y ≤ w x u w u y`, and the
  weighted row sums `∑_y w x y ‖K x y‖` are at most `q < 1`, then `1 - K` is invertible and the
  weighted row sums of `(1 - K)⁻¹` are at most `1 / (1 - q)`.
* `taggedG_row_sum`: the weighted row sums of `taggedG` are at most `taggedA0 d L κ t`, where
  `taggedA0 d L κ t = 2 e^{H κ} B₀ / (g + t)`.
* `taggedGfin_row_bound`: for `0 ≤ r ≤ ε/8`, all `t ≥ 0` and all `s` in the closed polydisc,
  the weighted row sums of `taggedGfin` are at most `(4/3) taggedA0 d L κ t`; with the entry bound
  `taggedGfin_entry_bound` and the rate-loss column bound `taggedGfin_column_bound`.
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Weighted row sums of a product: `∑_y w x y ‖(A B) x y‖ ≤ a b`. -/
theorem weightedRow_mul_le (w : ι → ι → ℝ) (hw0 : ∀ x y, 0 ≤ w x y)
    (hsub : ∀ x u y, w x y ≤ w x u * w u y) (A B : Matrix ι ι ℂ) {a b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ x, ∑ u, w x u * ‖A x u‖ ≤ a) (hB : ∀ u, ∑ y, w u y * ‖B u y‖ ≤ b) (x : ι) :
    ∑ y, w x y * ‖(A * B) x y‖ ≤ a * b := by
  have h1 : ∀ y, w x y * ‖(A * B) x y‖ ≤ ∑ u, (w x u * ‖A x u‖) * (w u y * ‖B u y‖) := by
    intro y
    rw [Matrix.mul_apply]
    calc w x y * ‖∑ u, A x u * B u y‖ ≤ w x y * ∑ u, ‖A x u‖ * ‖B u y‖ := by
          apply mul_le_mul_of_nonneg_left _ (hw0 x y)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun u _ => norm_mul _ _
      _ = ∑ u, w x y * (‖A x u‖ * ‖B u y‖) := by rw [Finset.mul_sum]
      _ ≤ ∑ u, (w x u * ‖A x u‖) * (w u y * ‖B u y‖) := by
          refine Finset.sum_le_sum fun u _ => ?_
          have := mul_le_mul_of_nonneg_right (hsub x u y)
            (mul_nonneg (norm_nonneg (A x u)) (norm_nonneg (B u y)))
          calc w x y * (‖A x u‖ * ‖B u y‖)
              ≤ (w x u * w u y) * (‖A x u‖ * ‖B u y‖) := this
            _ = _ := by ring
  calc ∑ y, w x y * ‖(A * B) x y‖ ≤ ∑ y, ∑ u, (w x u * ‖A x u‖) * (w u y * ‖B u y‖) :=
        Finset.sum_le_sum fun y _ => h1 y
    _ = ∑ u, (w x u * ‖A x u‖) * ∑ y, (w u y * ‖B u y‖) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ u, (w x u * ‖A x u‖) * b :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (hB u) (mul_nonneg (hw0 x u) (norm_nonneg _))
    _ = (∑ u, w x u * ‖A x u‖) * b := by rw [Finset.sum_mul]
    _ ≤ a * b := mul_le_mul_of_nonneg_right (hA x) hb

/-- **T1 (generic Neumann bound in a weighted row-sum norm).**  If `w ≥ 1`, `w x x = 1`, `w` is
submultiplicative along paths and the weighted row sums of `K` are at most `q < 1`, then `1 - K` is
invertible and the weighted row sums of `(1 - K)⁻¹` are at most `1 / (1 - q)`. -/
theorem weightedRow_inv_le (w : ι → ι → ℝ) (hw1 : ∀ x y, 1 ≤ w x y) (hww : ∀ x, w x x = 1)
    (hsub : ∀ x u y, w x y ≤ w x u * w u y) (K : Matrix ι ι ℂ) {q : ℝ} (hq : q < 1)
    (hK : ∀ x, ∑ y, w x y * ‖K x y‖ ≤ q) :
    IsUnit (1 - K) ∧ ∀ x, ∑ y, w x y * ‖(1 - K)⁻¹ x y‖ ≤ 1 / (1 - q) := by
  have hw0 : ∀ x y, 0 ≤ w x y := fun x y => zero_le_one.trans (hw1 x y)
  have hu : IsUnit (1 - K) := by
    refine isUnit_one_sub_of_weighted_row_sum (ω := fun _ => (1 : ℝ)) (fun _ => one_pos) hq
      fun x => ?_
    refine le_trans (Finset.sum_le_sum fun y _ => ?_) (hK x)
    simp only [one_mul, div_one]
    exact le_mul_of_one_le_left (norm_nonneg _) (hw1 x y)
  refine ⟨hu, ?_⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact fun x => (hι.false x).elim
  set J : Matrix ι ι ℂ := (1 - K)⁻¹ with hJ
  have hJeq : J = 1 + K * J := by
    have h : (1 - K) * J = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    calc J = (1 - K) * J + K * J := by rw [sub_mul, one_mul]; abel
      _ = _ := by rw [h]
  set N : ι → ℝ := fun x => ∑ y, w x y * ‖J x y‖ with hN
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max N
  have hN0 : 0 ≤ N x₀ := Finset.sum_nonneg fun y _ => mul_nonneg (hw0 _ _) (norm_nonneg _)
  have hone : ∀ x, ∑ y, w x y * ‖(1 : Matrix ι ι ℂ) x y‖ = 1 := by
    intro x
    rw [Finset.sum_eq_single x]
    · simp [hww]
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  have hkey : ∀ x, N x ≤ 1 + q * N x₀ := by
    intro x
    have hm := weightedRow_mul_le w hw0 hsub K J hN0 hK (fun u => hx₀ u) x
    calc N x = ∑ y, w x y * ‖(1 + K * J) x y‖ := by
          simp only [hN]; rw [← hJeq]
      _ ≤ ∑ y, (w x y * ‖(1 : Matrix ι ι ℂ) x y‖ + w x y * ‖(K * J) x y‖) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (by simpa using norm_add_le _ _) (hw0 _ _)
      _ = 1 + ∑ y, w x y * ‖(K * J) x y‖ := by
          rw [Finset.sum_add_distrib, hone]
      _ ≤ 1 + q * N x₀ := by linarith
  have h0 : N x₀ * (1 - q) ≤ 1 := by nlinarith [hkey x₀]
  intro x
  have hq1 : 0 < 1 - q := by linarith
  calc N x ≤ N x₀ := hx₀ x
    _ ≤ 1 / (1 - q) := by rw [le_div_iff₀ hq1]; exact h0

end Generic

section Tagged

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The constant `A₀(t) = 2 e^{H κ} B₀ / (g + t)` with `B₀ = ballConst d (ε/2)`. -/
noncomputable def taggedA0 (d L : ℕ) (κ t : ℝ) : ℝ :=
  2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2) / (finalGap d L + t)

theorem taggedA0_nonneg (hd : 0 < d) (hL : 0 < L) {κ t : ℝ} (ht : 0 ≤ t) :
    0 ≤ taggedA0 d L κ t := by
  have hg := finalGap_pos (d := d) hL
  have hε := pdEps_pos (d := d) (L := L) hd
  have : 0 ≤ ballConst d (pdEps d L / 2) := ballConst_decay_nonneg (by positivity)
  unfold taggedA0
  positivity

/-- **T2.** Weighted row sums of the tagged `G_*`: for `‖s p‖ ≤ e^κ`, `0 ≤ r ≤ ε/8` and
`κ 7^d ≤ (ε/8) M`, `∑_y e^{r dist x y} ‖G_*(s,t) x y‖ ≤ A₀(t)`. -/
theorem taggedG_row_sum (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ) (hr0 : 0 ≤ r)
    (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) *
        ‖taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤ taggedA0 d L κ t := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε := pdEps_pos (d := d) (L := L) hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set ε := pdEps d L with hεdef
  have hεr : ε ≤ finalRate d L := min_le_right _ _
  have hgt : 0 < finalGap d L + t := by linarith
  have hκM' : κ * 7 ^ d / M ≤ ε / 8 := by rw [div_le_iff₀ hM']; linarith
  have hentry : ∀ y : L1Torus d N₀,
      Real.exp (r * dist x y) *
        ‖taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤
        2 * Real.exp (pdH d * κ) / (finalGap d L + t) * Real.exp (-(ε / 2) * dist x y) := by
    intro y
    have hdist : 0 ≤ dist x y := dist_nonneg
    have hz : ∀ z ∈ (Finset.univ : Finset (MacIdx d N₀ M)),
        ‖tagMon (macTags d N₀ M z x y) s *
          (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t) x y‖ ≤
        macChi d N₀ M z x * (Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
          (2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y))) := by
      intro z _
      rw [Matrix.diagonal_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (macChi_nonneg z x)]
      have hE : ‖tagMon (macTags d N₀ M z x y) s‖ ≤
          Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) := by
        refine (norm_tagMon_le _ hs).trans ?_
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have := macTags_card_le hM z x y
        unfold pdH
        nlinarith
      have hG := boxG_final_entry_bound (L := L) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht
        (macBoxF d N₀ M z) x y
      have hχ := macChi_nonneg (d := d) (m := N₀) (M := M) z x
      calc _ = macChi d N₀ M z x * (‖tagMon (macTags d N₀ M z x y) s‖ *
            ‖boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t x y‖) := by ring
        _ ≤ _ := by gcongr
    unfold taggedG taggedMat
    rw [Matrix.of_apply]
    have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hz)
    rw [← Finset.sum_mul, macChi_sum, one_mul] at hsum
    have hfin : Real.exp (r * dist x y) * (Real.exp (pdH d * κ) *
        Real.exp (κ * 7 ^ d * (dist x y / M)) *
          (2 / (finalGap d L + t) * Real.exp (-finalRate d L * dist x y))) ≤
        2 * Real.exp (pdH d * κ) / (finalGap d L + t) * Real.exp (-(ε / 2) * dist x y) := by
      have hexp : Real.exp (r * dist x y) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
          Real.exp (-finalRate d L * dist x y) ≤ Real.exp (-(ε / 2) * dist x y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : κ * 7 ^ d * (dist x y / M) = (κ * 7 ^ d / M) * dist x y := by ring
        rw [h1]
        nlinarith
      calc _ = (2 * Real.exp (pdH d * κ) / (finalGap d L + t)) *
            (Real.exp (r * dist x y) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
              Real.exp (-finalRate d L * dist x y)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
    exact (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le).trans hfin
  calc _ ≤ ∑ y : L1Torus d N₀, 2 * Real.exp (pdH d * κ) / (finalGap d L + t) *
        Real.exp (-(ε / 2) * dist x y) := Finset.sum_le_sum fun y _ => hentry y
    _ = 2 * Real.exp (pdH d * κ) / (finalGap d L + t) *
        ∑ y : L1Torus d N₀, Real.exp (-(ε / 2) * dist x y) := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.exp (pdH d * κ) / (finalGap d L + t) * ballConst d (ε / 2) :=
        mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by positivity) x) (by positivity)
    _ = taggedA0 d L κ t := by unfold taggedA0; ring

/-- **T3.**  Weighted row sums of the tagged family: under the hypotheses of `taggedGfin_final`
and `0 ≤ r ≤ ε/8`, for every `s` in the closed polydisc `‖s p‖ ≤ e^κ`,
`∑_y e^{r dist x y} ‖G_fin(s,t) x y‖ ≤ (4/3) A₀(t)`. -/
theorem taggedGfin_row_bound (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) *
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
  have hinv := weightedRow_inv_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw1 hww hsub
    (taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t s) (q := 1 / 4) (by norm_num)
    (fun x => (taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x).trans hq)
  have h43 : 1 / (1 - (1 / 4 : ℝ)) = 4 / 3 := by norm_num
  rw [h43] at hinv
  have hA0 := taggedA0_nonneg (d := d) (L := L) hd hL (κ := κ) ht
  unfold taggedGfin
  rw [mul_comm (4 / 3 : ℝ)]
  exact weightedRow_mul_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y))
    (fun x y => (Real.exp_pos _).le) hsub _ _ (by norm_num) (a := taggedA0 d L κ t)
    (fun x => taggedG_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x)
    hinv.2 x

/-- **T3, entry bound.**  `‖G_fin(s,t) x y‖ ≤ (4/3) A₀(t) e^{-r dist x y}`. -/
theorem taggedGfin_entry_bound (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x y : L1Torus d N₀) :
    ‖taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤
      4 / 3 * taggedA0 d L κ t * Real.exp (-r * dist x y) := by
  have h := taggedGfin_row_bound hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ hr0 hr hs x
  have h1 : Real.exp (r * dist x y) * ‖taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
      (finalOp d L N₀ k v a) t s x y‖ ≤ 4 / 3 * taggedA0 d L κ t :=
    (Finset.single_le_sum (f := fun y => Real.exp (r * dist x y) * ‖taggedGfin Finset.univ
      (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
      (finalOp d L N₀ k v a) t s x y‖) (fun y _ => mul_nonneg (Real.exp_pos _).le
        (norm_nonneg _)) (Finset.mem_univ y)).trans h
  have h2 : Real.exp (-r * dist x y) * Real.exp (r * dist x y) = 1 := by
    rw [← Real.exp_add]; simp
  calc _ = Real.exp (-r * dist x y) * (Real.exp (r * dist x y) * ‖taggedGfin Finset.univ
        (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
        (finalOp d L N₀ k v a) t s x y‖) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ Real.exp (-r * dist x y) * (4 / 3 * taggedA0 d L κ t) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := by ring

/-- **T3, rate-loss column bound.**  For `0 ≤ r' < r ≤ ε/8`,
`∑_x e^{r' dist x y} ‖G_fin(s,t) x y‖ ≤ (4/3) A₀(t) ballConst d (r - r')`. -/
theorem taggedGfin_column_bound (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) {M : ℕ} (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {r r' : ℝ} (hr'0 : 0 ≤ r') (hrr : r' < r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (y : L1Torus d N₀) :
    ∑ x, Real.exp (r' * dist x y) *
        ‖taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤
      4 / 3 * taggedA0 d L κ t * ballConst d (r - r') := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hr0 : 0 ≤ r := hr'0.trans hrr.le
  have hA0 := taggedA0_nonneg (d := d) (L := L) hd hL (κ := κ) ht
  have hterm : ∀ x : L1Torus d N₀, Real.exp (r' * dist x y) *
      ‖taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤
      4 / 3 * taggedA0 d L κ t * Real.exp (-(r - r') * dist y x) := by
    intro x
    have h := taggedGfin_entry_bound hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ hr0 hr hs x y
    rw [dist_comm y x]
    calc _ ≤ Real.exp (r' * dist x y) * (4 / 3 * taggedA0 d L κ t * Real.exp (-r * dist x y)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = 4 / 3 * taggedA0 d L κ t * (Real.exp (r' * dist x y) * Real.exp (-r * dist x y)) := by
          ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  calc _ ≤ ∑ x : L1Torus d N₀, 4 / 3 * taggedA0 d L κ t * Real.exp (-(r - r') * dist y x) :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = 4 / 3 * taggedA0 d L κ t * ∑ x : L1Torus d N₀, Real.exp (-(r - r') * dist y x) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ballSum_L1Torus d N₀ (by linarith) y) (by positivity)

end Tagged

end Balaban.Green
