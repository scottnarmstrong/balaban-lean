/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.LocCutoff

/-!
# Lattice sums of the Green's function bounds (Lemma P)

* `sum_ball_pow_le`: `∑_{w ∈ B_R(0)} (1 + ‖w‖)^{-(d-p)} ≤ d 2^d (R+1)^p` for `1 ≤ p ≤ d`
  (shell counting on `ℤ^d`).
* `sum_translate_le`: a rearrangement inequality: for a finite set `A` with at most as many points as
  the ball `B_R(0)`, `∑_{z ∈ A} F(y₀ - z) ≤ ∑_{w ∈ B_R(0)} F(w)` for `F` a nonnegative function of
  `‖w‖` that is nonincreasing.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

/-- The sup norm of a lattice point, as a natural number. -/
def latticeNorm (z : Fin d → ℤ) : ℕ := Finset.univ.sup fun i => (z i).natAbs

theorem norm_eq_latticeNorm (z : Fin d → ℤ) : ‖z‖ = (latticeNorm z : ℝ) := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    intro i
    rw [Int.norm_eq_abs]
    have : (z i).natAbs ≤ latticeNorm z := Finset.le_sup (f := fun i => (z i).natAbs)
      (Finset.mem_univ i)
    have h2 : |((z i : ℤ) : ℝ)| = ((z i).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2]
    exact_mod_cast this
  · have : latticeNorm z ≤ ⌊‖z‖⌋₊ := by
      refine Finset.sup_le fun i _ => ?_
      refine Nat.le_floor ?_
      have := norm_le_pi_norm z i
      rw [Int.norm_eq_abs] at this
      have h2 : |((z i : ℤ) : ℝ)| = ((z i).natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [← h2]
      exact this
    exact (Nat.cast_le.2 this).trans (Nat.floor_le (norm_nonneg _))

theorem mem_latticeBall_nat {z : Fin d → ℤ} {M : ℕ} :
    z ∈ latticeBall (0 : Fin d → ℤ) (M : ℝ) ↔ latticeNorm z ≤ M := by
  rw [mem_latticeBall (Nat.cast_nonneg _), sub_zero, norm_eq_latticeNorm]
  exact Nat.cast_le

theorem card_latticeBall_nat (x₀ : Fin d → ℤ) (m : ℕ) :
    (latticeBall x₀ (m : ℝ)).card = (2 * m + 1) ^ d := by
  rw [latticeBall, Fintype.card_piFinset]
  have hc : ∀ i : Fin d, (Finset.Icc (x₀ i - ⌊(m : ℝ)⌋) (x₀ i + ⌊(m : ℝ)⌋)).card = 2 * m + 1 := by
    intro i
    rw [Int.card_Icc, Int.floor_natCast]
    omega
  rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem pow_succ_sub_le (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) (n : ℕ) :
    a ^ (n + 1) - b ^ (n + 1) ≤ (n + 1) * a ^ n * (a - b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : b ^ (n + 1) ≤ a ^ (n + 1) := pow_le_pow_left₀ hb hab _
      have h0 : 0 ≤ a - b := by linarith
      have h2 : a ^ (n + 1 + 1) - b ^ (n + 1 + 1) =
          a * (a ^ (n + 1) - b ^ (n + 1)) + b ^ (n + 1) * (a - b) := by ring
      rw [h2]
      have h3 : a * (a ^ (n + 1) - b ^ (n + 1)) ≤ a * ((n + 1) * a ^ n * (a - b)) :=
        mul_le_mul_of_nonneg_left ih (hb.trans hab)
      have h4 : b ^ (n + 1) * (a - b) ≤ a ^ (n + 1) * (a - b) :=
        mul_le_mul_of_nonneg_right h1 h0
      have h5 : a * ((n + 1) * a ^ n * (a - b)) + a ^ (n + 1) * (a - b) =
          (((n + 1 : ℕ) : ℝ) + 1) * a ^ (n + 1) * (a - b) := by push_cast; ring
      push_cast at h5 ⊢
      linarith

/-- The number of lattice points with sup norm exactly `m ≥ 1`. -/
theorem card_shell_le (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hd : d = n + 1) :
    (((latticeBall (0 : Fin d → ℤ) (m : ℝ)).card : ℝ) -
        (latticeBall (0 : Fin d → ℤ) ((m - 1 : ℕ) : ℝ)).card) ≤
      d * 2 * (2 * (m : ℝ) + 1) ^ n := by
  rw [card_latticeBall_nat, card_latticeBall_nat]
  have h := pow_succ_sub_le (2 * (m : ℝ) + 1) (2 * ((m - 1 : ℕ) : ℝ) + 1) (by positivity)
    (by have : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
        linarith) n
  have e : (2 * (m : ℝ) + 1) - (2 * ((m - 1 : ℕ) : ℝ) + 1) = 2 := by
    have : ((m - 1 : ℕ) : ℝ) = m - 1 := by
      rw [Nat.cast_sub hm]; simp
    rw [this]; ring
  rw [e] at h
  subst hd
  convert h using 1
  · push_cast; ring_nf
  · push_cast; ring

theorem card_fiber_le (hd : 1 ≤ d) (m : ℕ) (M : ℕ) (hm : m ≤ M) :
    (((latticeBall (0 : Fin d → ℤ) (M : ℝ)).filter fun w => latticeNorm w = m).card : ℝ) ≤
      d * 2 ^ d * ((m : ℝ) + 1) ^ (d - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hd1 : ((n + 1 : ℕ) : ℝ) ≥ 1 := by exact_mod_cast hd
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · have : (latticeBall (0 : Fin (n + 1) → ℤ) (M : ℝ)).filter (fun w => latticeNorm w = 0) =
        latticeBall (0 : Fin (n + 1) → ℤ) ((0 : ℕ) : ℝ) := by
      ext w
      simp only [Finset.mem_filter, mem_latticeBall_nat]
      omega
    rw [this, card_latticeBall_nat]
    simp only [Nat.cast_zero, mul_zero, zero_add, one_pow, Nat.cast_one]
    have h2 : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
    push_cast at hd1 ⊢
    nlinarith
  · have : (latticeBall (0 : Fin (n + 1) → ℤ) (M : ℝ)).filter (fun w => latticeNorm w = m) =
        latticeBall (0 : Fin (n + 1) → ℤ) (m : ℝ) \ latticeBall 0 ((m - 1 : ℕ) : ℝ) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_sdiff, mem_latticeBall_nat]
      omega
    rw [this, Finset.card_sdiff_of_subset (fun w hw => by
      simp only [mem_latticeBall_nat] at hw ⊢; omega)]
    push_cast [Nat.cast_sub (show (latticeBall (0 : Fin (n + 1) → ℤ) ((m - 1 : ℕ) : ℝ)).card ≤
      (latticeBall (0 : Fin (n + 1) → ℤ) (m : ℝ)).card from
      Finset.card_le_card (fun w hw => by
        simp only [mem_latticeBall_nat] at hw ⊢; omega))]
    have h := card_shell_le (d := n + 1) m hm1 n rfl
    refine h.trans ?_
    have h3 : (2 * (m : ℝ) + 1) ^ n ≤ 2 ^ n * ((m : ℝ) + 1) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    push_cast
    calc ((n : ℝ) + 1) * 2 * (2 * (m : ℝ) + 1) ^ n ≤ ((n : ℝ) + 1) * 2 *
          (2 ^ n * ((m : ℝ) + 1) ^ n) := by gcongr
      _ = _ := by ring

theorem sum_ball_pow_le (hd : 1 ≤ d) {p : ℕ} (hp : 1 ≤ p) (hpd : p ≤ d) {R : ℝ} (hR : 0 ≤ R) :
    ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, 1 / (1 + ‖w‖) ^ (d - p) ≤
      d * 2 ^ d * (R + 1) ^ p := by
  set M := ⌊R⌋₊ with hM
  have hball : latticeBall (0 : Fin d → ℤ) R = latticeBall 0 (M : ℝ) := by
    ext w
    rw [mem_latticeBall hR, mem_latticeBall (r := (M : ℝ)) (Nat.cast_nonneg _), sub_zero,
      norm_eq_latticeNorm]
    rw [← Nat.le_floor_iff hR]
    exact (Nat.cast_le (α := ℝ)).symm
  rw [hball]
  have hmaps : ∀ w ∈ latticeBall (0 : Fin d → ℤ) (M : ℝ), latticeNorm w ∈ Finset.range (M + 1) :=
    fun w hw => Finset.mem_range.2 (Nat.lt_succ_of_le (mem_latticeBall_nat.1 hw))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ m ∈ Finset.range (M + 1),
      ∑ w ∈ (latticeBall (0 : Fin d → ℤ) (M : ℝ)).filter (fun w => latticeNorm w = m),
        1 / (1 + ‖w‖) ^ (d - p) ≤ d * 2 ^ d * ((m : ℝ) + 1) ^ (p - 1) := by
    intro m hm
    have hmM : m ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have h1 : ∀ w ∈ (latticeBall (0 : Fin d → ℤ) (M : ℝ)).filter (fun w => latticeNorm w = m),
        1 / (1 + ‖w‖) ^ (d - p) = 1 / (1 + (m : ℝ)) ^ (d - p) := by
      intro w hw
      rw [norm_eq_latticeNorm, (Finset.mem_filter.1 hw).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have h2 := card_fiber_le hd m M hmM
    have hpos : 0 < ((m : ℝ) + 1) := by positivity
    have e : ((m : ℝ) + 1) ^ (d - 1) * (1 / (1 + (m : ℝ)) ^ (d - p)) = ((m : ℝ) + 1) ^ (p - 1) := by
      rw [add_comm (1 : ℝ) m, one_div, ← pow_sub₀ _ hpos.ne' (by omega)]
      congr 1
      omega
    calc _ ≤ (d * 2 ^ d * ((m : ℝ) + 1) ^ (d - 1)) * (1 / (1 + (m : ℝ)) ^ (d - p)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = d * 2 ^ d * (((m : ℝ) + 1) ^ (d - 1) * (1 / (1 + (m : ℝ)) ^ (d - p))) := by ring
      _ = _ := by rw [e]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h3 : ∑ m ∈ Finset.range (M + 1), ((m : ℝ) + 1) ^ (p - 1) ≤ ((M : ℝ) + 1) ^ p := by
    calc _ ≤ ∑ _m ∈ Finset.range (M + 1), ((M : ℝ) + 1) ^ (p - 1) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have : (m : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
          exact pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = ((M : ℝ) + 1) ^ p := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          rw [← pow_succ']
          congr 1
          omega
  have h4 : ((M : ℝ) + 1) ^ p ≤ (R + 1) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith [Nat.floor_le hR]) _
  have hc : (0 : ℝ) ≤ d * 2 ^ d := by positivity
  exact mul_le_mul_of_nonneg_left (h3.trans h4) hc

/-- Rearrangement: a set with at most as many points as the ball `B_R(0)` has a smaller sum of a
radially nonincreasing nonnegative function (centred anywhere) than the ball. -/
theorem sum_translate_le (φ : ℝ → ℝ) (hφ0 : ∀ r, 0 ≤ φ r)
    (hφ : ∀ r r', 0 ≤ r → r ≤ r' → φ r' ≤ φ r) {R : ℝ} (hR : 0 ≤ R)
    (A : Finset (Fin d → ℤ)) (hA : A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card)
    (y₀ : Fin d → ℤ) :
    ∑ z ∈ A, φ ‖y₀ - z‖ ≤ ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, φ ‖w‖ := by
  classical
  set B := latticeBall (0 : Fin d → ℤ) R with hB
  set A' := A.image (fun z => y₀ - z) with hA'
  have hinj : Function.Injective (fun z : Fin d → ℤ => y₀ - z) := sub_right_injective
  have hcard : A'.card = A.card := Finset.card_image_of_injective _ hinj
  have hsum : ∑ z ∈ A, φ ‖y₀ - z‖ = ∑ w ∈ A', φ ‖w‖ := by
    rw [hA', Finset.sum_image (fun a _ b _ h => hinj h)]
  rw [hsum]
  have e1 := Finset.sum_inter_add_sum_sdiff A' B (fun w => φ ‖w‖)
  have e2 := Finset.sum_inter_add_sum_sdiff B A' (fun w => φ ‖w‖)
  rw [Finset.inter_comm] at e2
  have hc1 := Finset.card_sdiff_add_card_inter A' B
  have hc2 := Finset.card_sdiff_add_card_inter B A'
  rw [Finset.inter_comm] at hc2
  have hcc : (A' \ B).card ≤ (B \ A').card := by omega
  have hu : ∑ w ∈ A' \ B, φ ‖w‖ ≤ (A' \ B).card • φ R := by
    refine Finset.sum_le_card_nsmul _ _ _ fun w hw => ?_
    have : R < ‖w‖ := by
      have := (Finset.mem_sdiff.1 hw).2
      rwa [hB, mem_latticeBall hR, sub_zero, not_le] at this
    exact hφ R ‖w‖ hR this.le
  have hl : (B \ A').card • φ R ≤ ∑ w ∈ B \ A', φ ‖w‖ := by
    refine Finset.card_nsmul_le_sum _ _ _ fun w hw => ?_
    have : ‖w‖ ≤ R := by
      have := (Finset.mem_sdiff.1 hw).1
      rwa [hB, mem_latticeBall hR, sub_zero] at this
    exact hφ ‖w‖ R (norm_nonneg _) this
  have hm : (A' \ B).card • φ R ≤ (B \ A').card • φ R := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcc) (hφ0 R)
  linarith

end Balaban.LatticeGreen
