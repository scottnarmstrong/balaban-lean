/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.Assembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The hard-spin bound of LF-1 (proof of Theorem II.4.1 (b))

`hs_abstract` is the algebraic core: for a vector `ψ ≠ 0`, the block average `Q`, a unit vector `h`,
`½(‖ψ‖-1)² + m(1 - h·ψ/‖ψ‖) ≤ (1+6m)‖ψ-Q‖² + (½+2m) r + m J`, where `1-‖Q‖² ≤ r/2` and
`‖Q-h‖² ≤ J`.  Then the block bound `hardSpin_block_bound` and the sum over the blocks.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hs_abstract (ψ Q h : E) (hψ : ψ ≠ 0) (hh : ‖h‖ = 1) (hQ : ‖Q‖ ≤ 1) {m r J : ℝ}
    (hm0 : 0 ≤ m) (hr : 1 - ‖Q‖ ^ 2 ≤ r / 2) (hJ : ‖Q - h‖ ^ 2 ≤ J) :
    1 / 2 * (‖ψ‖ - 1) ^ 2 + m * (1 - inner ℝ h (‖ψ‖⁻¹ • ψ)) ≤
      (1 + 6 * m) * ‖ψ - Q‖ ^ 2 + (1 / 2 + 2 * m) * r + m * J := by
  have hn : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  set u : E := ‖ψ‖⁻¹ • ψ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  set Δ := ‖ψ - Q‖ ^ 2 with hΔ
  set P := (‖ψ‖ - 1) ^ 2 with hP
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  -- (‖ψ‖ - 1)² ≤ 2Δ + r
  have hP1 : P ≤ 2 * Δ + r := by
    have ha : |‖ψ‖ - ‖Q‖| ≤ ‖ψ - Q‖ := abs_norm_sub_norm_le ψ Q
    have ha2 : (‖ψ‖ - ‖Q‖) ^ 2 ≤ Δ := by
      calc (‖ψ‖ - ‖Q‖) ^ 2 = |‖ψ‖ - ‖Q‖| ^ 2 := (sq_abs _).symm
        _ ≤ ‖ψ - Q‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
    have hb : (1 - ‖Q‖) ^ 2 ≤ 1 - ‖Q‖ ^ 2 := by nlinarith
    have : P = ((‖ψ‖ - ‖Q‖) - (1 - ‖Q‖)) ^ 2 := by rw [hP]; ring
    rw [this]
    nlinarith [sq_nonneg ((‖ψ‖ - ‖Q‖) + (1 - ‖Q‖))]
  -- ‖u - ψ‖ = |‖ψ‖ - 1|
  have hnu : ‖ψ - u‖ = |‖ψ‖ - 1| := by
    have : ψ - u = (1 - ‖ψ‖⁻¹) • ψ := by rw [hu, sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs]
    have h2 : (1 - ‖ψ‖⁻¹) * ‖ψ‖ = ‖ψ‖ - 1 := by field_simp
    calc |1 - ‖ψ‖⁻¹| * ‖ψ‖ = |(1 - ‖ψ‖⁻¹) * ‖ψ‖| := by rw [abs_mul, abs_of_pos hn]
      _ = |‖ψ‖ - 1| := by rw [h2]
  have hUQ : ‖u - Q‖ ^ 2 ≤ 2 * P + 2 * Δ := by
    have h1 : ‖u - Q‖ ≤ ‖ψ - u‖ + ‖ψ - Q‖ := by
      calc ‖u - Q‖ = ‖(ψ - Q) - (ψ - u)‖ := by congr 1; abel
        _ ≤ ‖ψ - Q‖ + ‖ψ - u‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have h2 : ‖ψ - u‖ ^ 2 = P := by rw [hnu, sq_abs, hP]
    nlinarith [sq_nonneg (‖ψ - u‖ - ‖ψ - Q‖), norm_nonneg (ψ - u), norm_nonneg (ψ - Q),
      norm_nonneg (u - Q)]
  have hin : 1 - inner ℝ h u = 1 / 2 * ‖u - h‖ ^ 2 := by
    rw [norm_sub_sq_real, hu1, hh, real_inner_comm]; ring
  have huh : ‖u - h‖ ^ 2 ≤ 2 * ‖u - Q‖ ^ 2 + 2 * ‖Q - h‖ ^ 2 := by
    have : ‖u - h‖ ≤ ‖u - Q‖ + ‖Q - h‖ := by
      calc ‖u - h‖ = ‖(u - Q) + (Q - h)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    nlinarith [sq_nonneg (‖u - Q‖ - ‖Q - h‖), norm_nonneg (u - h), norm_nonneg (u - Q),
      norm_nonneg (Q - h)]
  have hfin : 1 - inner ℝ h u ≤ 6 * Δ + 2 * r + J := by
    rw [hin]; nlinarith [hUQ, huh, hP1, hJ]
  have hm := mul_le_mul_of_nonneg_left hfin hm0
  nlinarith [hP1, hm]

end Abstract

section Block

variable {Nspin d L N₀ q : ℕ} [NeZero N₀] [NeZero L]

theorem norm_bavg_le_one {n : ℕ} (hn : n ≤ q)
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) (y : Blk d L N₀ q n)
    (hφ : ∀ x ∈ fib d L N₀ q n y, ‖φ x‖ = 1) : ‖bavgL d L N₀ q n φ y‖ ≤ 1 := by
  have hN : (0 : ℝ) < ((L ^ n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    push_cast; positivity
  unfold bavgL bavg
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hN.le, inv_mul_le_iff₀ hN]
  calc ‖∑ x ∈ blockFibre (L ^ n) (N₀ * L ^ (q - n)) y, φ x‖
      ≤ ∑ x ∈ blockFibre (L ^ n) (N₀ * L ^ (q - n)) y, ‖φ x‖ := norm_sum_le _ _
    _ = ∑ x ∈ blockFibre (L ^ n) (N₀ * L ^ (q - n)) y, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [← fib_eq_blockFibre] at hx
        exact hφ x hx
    _ = ((L ^ n : ℕ) : ℝ) ^ d * 1 := by
        rw [Finset.sum_const, ← fib_eq_blockFibre, card_fib hn]; simp

/-- The block bound of the proof of (b). -/
theorem hardSpin_block_bound {n : ℕ} (hn : n ≤ q) (hd : 2 ≤ d)
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) (y : Blk d L N₀ q n)
    (hφ : ∀ x ∈ fib d L N₀ q n y, ‖φ x‖ = 1) (h : EuclideanSpace ℝ (Fin Nspin)) (hh : ‖h‖ = 1)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ * (L : ℝ) ^ (2 * n) ≤ 1) (ψy : EuclideanSpace ℝ (Fin Nspin))
    (hψ : ψy ≠ 0) :
    (L : ℝ) ^ (n * (d - 2)) * (1 / 2 * (‖ψy‖ - 1) ^ 2 +
        μ * (L : ℝ) ^ (2 * n) * (1 - inner ℝ h (‖ψy‖⁻¹ • ψy))) ≤
      7 * ((L : ℝ) ^ (n * (d - 2)) * ‖ψy - bavgL d L N₀ q n φ y‖ ^ 2) +
        5 / 2 * bondE (fib d L N₀ q n y) φ + μ * ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2 := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL0
  set Q := bavgL d L N₀ q n φ y with hQ
  set ε := bondE (fib d L N₀ q n y) φ with hε
  have hε0 : 0 ≤ ε := bondE_nonneg _ _
  set w : ℝ := ((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹ with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hWw : (L : ℝ) ^ (n * (d - 2)) * w = 1 := weight_mul_c hd hL0 n
  have hK : (0 : ℝ) < ((L : ℝ) ^ n) ^ d := by positivity
  have hcast : ((L ^ n : ℕ) : ℝ) = (L : ℝ) ^ n := by push_cast; ring
  have h1 : 1 - ‖Q‖ ^ 2 ≤ (w * ε) / 2 := by
    have := hardSpin_one_sub_sq_le (sideEq (L := L) (N₀ := N₀) hn) φ y
      (fun x hx => hφ x (by rw [fib_eq_blockFibre]; exact hx))
    rw [← fib_eq_blockFibre, hcast] at this
    rw [hQ, bavgL_eq, hε, hw]
    linarith
  have hQ1 : ‖Q‖ ≤ 1 := norm_bavg_le_one hn φ y hφ
  -- Jensen for `‖Q - h‖²`
  have hJ : ‖Q - h‖ ^ 2 ≤ (((L : ℝ) ^ n) ^ d)⁻¹ * ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2 := by
    have hcard : ((fib d L N₀ q n y).card : ℝ) = ((L : ℝ) ^ n) ^ d := by
      rw [card_fib hn]; push_cast; ring
    have hsum : ∑ x ∈ fib d L N₀ q n y, φ x = (((L : ℝ) ^ n) ^ d) • Q := by
      rw [fib_eq_blockFibre, sum_blockFibre_eq_smul_bavg (sideEq (L := L) (N₀ := N₀) hn) φ y, hcast]
      rfl
    have e : Q - h = (((L : ℝ) ^ n) ^ d)⁻¹ • ∑ x ∈ fib d L N₀ q n y, (φ x - h) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hsum, ← Nat.cast_smul_eq_nsmul ℝ, hcard,
        smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hK.ne', one_smul, one_smul]
    rw [e]
    exact sq_norm_avg_le _ _ hcard hK
  set m : ℝ := μ * ((L : ℝ) ^ n) ^ 2 with hm
  have hm0 : 0 ≤ m := by rw [hm]; positivity
  have hm1 : m ≤ 1 := by
    rw [hm, ← pow_mul, mul_comm n 2]; exact hμ
  have hmain := hs_abstract ψy Q h hψ hh hQ1 hm0 h1 hJ
  have hEq : μ * (L : ℝ) ^ (2 * n) = m := by rw [hm, ← pow_mul, mul_comm n 2]
  rw [hEq]
  have hΔ0 : 0 ≤ ‖ψy - Q‖ ^ 2 := by positivity
  have hWt : 0 ≤ (L : ℝ) ^ (n * (d - 2)) := by positivity
  have hS0 : 0 ≤ ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  calc _ ≤ (L : ℝ) ^ (n * (d - 2)) * ((1 + 6 * m) * ‖ψy - Q‖ ^ 2 + (1 / 2 + 2 * m) * (w * ε) +
        m * ((((L : ℝ) ^ n) ^ d)⁻¹ * ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain hWt
    _ = (1 + 6 * m) * ((L : ℝ) ^ (n * (d - 2)) * ‖ψy - Q‖ ^ 2) +
        (1 / 2 + 2 * m) * ε * ((L : ℝ) ^ (n * (d - 2)) * w) +
        μ * ((L : ℝ) ^ (n * (d - 2)) * w) * ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2 := by
        have e1 : m * (((L : ℝ) ^ n) ^ d)⁻¹ = μ * w := by rw [hm, hw]; ring
        linear_combination ((L : ℝ) ^ (n * (d - 2)) * ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2) * e1
    _ ≤ _ := by
        rw [hWw]
        nlinarith [mul_nonneg hWt hΔ0, mul_nonneg (sub_nonneg.2 hm1) (mul_nonneg hWt hΔ0),
          mul_nonneg (sub_nonneg.2 hm1) hε0]

end Block

section Total

variable {Nspin d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- Blocks of `T_n(S)` partition `S`. -/
theorem sum_fib_le {n : ℕ} (S : Finset (Site d L N₀ q)) (F : Site d L N₀ q → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hS : IsBlockUnion L N₀ q n S) :
    ∑ y ∈ tBlocks d L N₀ q n S, ∑ x ∈ fib d L N₀ q n y, F x ≤ ∑ x ∈ S, F x := by
  have := sum_sum_family_le (tBlocks d L N₀ q n S) (fun y => fib d L N₀ q n y) S
    (fun y hy => ?_) 1 (fun x => ?_) F hF
  · simpa using this
  · exact fib_subset_of_mem_tBlocks hS hy
  · refine (Finset.card_le_card (t := {blkMap d L N₀ q n x}) ?_).trans
      (Finset.card_singleton _).le
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_singleton]
    exact (mem_fib.1 hy.2).symm

theorem sum_bk_range_eq (G : GeneratingSet d L N₀ q ϱ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin)) :
    ∑ n ∈ Finset.range (q + 1), bk G X φ ψ n = ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n := by
  rw [sum_Icc_one_eq_sum_range (bk G X φ ψ) q, Finset.sum_range_succ', bk_zero, add_zero]

/-- **Total bound of Theorem II.4.1 (b)**. -/
theorem hardSpin_total (G : GeneratingSet d L N₀ q ϱ) (hd : 2 ≤ d) (X : Finset (Site d L N₀ q))
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ X, ‖φ x‖ = 1)
    (h : EuclideanSpace ℝ (Fin Nspin)) (hh : ‖h‖ = 1) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ * (L : ℝ) ^ (2 * q) ≤ 1)
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin))
    (hψ : ∀ n, 1 ≤ n → n ≤ q → ∀ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), psiFull φ ψ n y ≠ 0) :
    ∑ n ∈ Finset.range (q + 1), ((L : ℝ) ^ (n * (d - 2)) *
        ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          (1 / 2 * (‖psiFull φ ψ n y‖ - 1) ^ 2 + μ * (L : ℝ) ^ (2 * n) *
            (1 - inner ℝ h (‖psiFull φ ψ n y‖⁻¹ • psiFull φ ψ n y)))) ≤
      7 * ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n + 5 / 2 * bondE X φ +
        μ * ∑ x ∈ X, ‖φ x - h‖ ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hE5 : 0 ≤ 5 / 2 * (1 : ℝ) := by norm_num
  have hS1 := sum_bondE_lam_le G X φ
  have hF0 : ∀ x : Site d L N₀ q, 0 ≤ ‖φ x - h‖ ^ 2 := fun x => by positivity
  have hS2 := sum_sum_family_le (Finset.range (q + 1)) (fun n => lam G n ∩ X) X
    (fun n _ => Finset.inter_subset_right) 1 (fun x => ?_) (fun x => ‖φ x - h‖ ^ 2) hF0
  swap
  · refine (Finset.card_le_card (t := {G.layerIndex x}) ?_).trans (Finset.card_singleton _).le
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_singleton]
    exact ((mem_lam_iff G (by omega) x).1 (Finset.mem_inter.1 hn.2).1).symm
  have hblock : ∀ n ∈ Finset.range (q + 1), ((L : ℝ) ^ (n * (d - 2)) *
        ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          (1 / 2 * (‖psiFull φ ψ n y‖ - 1) ^ 2 + μ * (L : ℝ) ^ (2 * n) *
            (1 - inner ℝ h (‖psiFull φ ψ n y‖⁻¹ • psiFull φ ψ n y)))) ≤
      7 * bk G X φ ψ n + 5 / 2 * bondE (lam G n ∩ X) φ +
        μ * ∑ x ∈ lam G n ∩ X, ‖φ x - h‖ ^ 2 := by
    intro n hn
    have hnq : n ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have hU := isBlockUnion_lam G hX hnq
    have hsubS : ∀ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), fib d L N₀ q n y ⊆ X := fun y hy =>
      (fib_subset_of_mem_tBlocks hU hy).trans Finset.inter_subset_right
    have hμn : μ * (L : ℝ) ^ (2 * n) ≤ 1 := by
      refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega)) hμ0) hμ
    have hpsi : ∀ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), psiFull φ ψ n y ≠ 0 := by
      intro y hy
      by_cases h0 : n = 0
      · subst h0
        obtain ⟨x, hx, rfl⟩ := mem_tBlocks.1 hy
        rw [psiFull_zero, bavgL_zero]
        intro hz
        have := hφ x (Finset.mem_inter.1 hx).2
        rw [blkMap_zero] at hz
        rw [hz] at this
        simp at this
      · exact hψ n (Nat.one_le_iff_ne_zero.2 h0) hnq y hy
    rw [Finset.mul_sum]
    calc _ ≤ ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          (7 * ((L : ℝ) ^ (n * (d - 2)) * ‖psiFull φ ψ n y - bavgL d L N₀ q n φ y‖ ^ 2) +
            5 / 2 * bondE (fib d L N₀ q n y) φ + μ * ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2) := by
          refine Finset.sum_le_sum fun y hy => ?_
          exact hardSpin_block_bound hnq hd φ y (fun x hx => hφ x (hsubS y hy hx)) h hh hμ0 hμn _
            (hpsi y hy)
      _ = 7 * bk G X φ ψ n + 5 / 2 * ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), bondE (fib d L N₀ q n y) φ +
          μ * ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), ∑ x ∈ fib d L N₀ q n y, ‖φ x - h‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [bk, ← Finset.mul_sum]
      _ ≤ _ := by
          have b1 : ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X), bondE (fib d L N₀ q n y) φ ≤
              bondE (lam G n ∩ X) φ := by
            have := sum_bondE_family_le (tBlocks d L N₀ q n (lam G n ∩ X))
              (fun y => fib d L N₀ q n y) (lam G n ∩ X)
              (fun y hy => fib_subset_of_mem_tBlocks hU hy) 1 (fun x => ?_) φ
            · simpa using this
            · refine (Finset.card_le_card (t := {blkMap d L N₀ q n x}) ?_).trans
                (Finset.card_singleton _).le
              intro y hy
              rw [Finset.mem_filter] at hy
              rw [Finset.mem_singleton]
              exact (mem_fib.1 hy.2).symm
          have b2 := sum_fib_le (n := n) (lam G n ∩ X) (fun x => ‖φ x - h‖ ^ 2) hF0 hU
          have := mul_le_mul_of_nonneg_left b2 hμ0
          linarith
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_bk_range_eq]
  have := mul_le_mul_of_nonneg_left hS2 hμ0
  simp only [Nat.cast_one, one_mul] at hS2 this
  linarith

end Total

end Balaban.LargeField
