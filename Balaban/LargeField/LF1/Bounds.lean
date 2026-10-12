/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The intra-layer and cross-pair bounds of LF-1 (proof of Theorem II.4.1 (a))

* `intra_bound`: `(L^{n(d-2)}/2) ∑_{{y,y'}∈P_n} ‖ψ_n(y) - ψ_n(y')‖² ≤ 3d Bk_n + 3 E(S)`;
* `cross_bound`: `(L^{(n+1)(d-2)}/2) ∑_{P^×_{n+1}} ‖ψ_{n+1}(b₊) - (Qψ_n)(b₋)‖²
   ≤ 3d Bk_{n+1} + (3d/4) Bk_n + 6 E(S^×)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Intra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ} [NeZero N₀] [NeZero L]

omit [NeZero L] in
/-- `L^{n(d-2)} · N² N^{-d} = 1` for `N = L^n`. -/
theorem weight_mul_c (hd : 2 ≤ d) (hL : 0 < L) (n : ℕ) :
    (L : ℝ) ^ (n * (d - 2)) * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hL' : (L : ℝ) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel_left]
  rw [← pow_mul, ← pow_mul, mul_add, pow_add]
  field_simp

open Classical in
/-- The one-pair estimate: `‖ψ y - ψ y'‖² ≤ 3Δ y + 3Δ y' + 3 c · bondEdir`, `y' = y + e_μ`. -/
theorem pair_estimate {n : ℕ} (hn : n ≤ q) (φ : Site d L N₀ q → E) (ψn : Blk d L N₀ q n → E)
    (y : Blk d L N₀ q n) (μ : Fin d) :
    ‖ψn y - ψn (y + Pi.single μ 1)‖ ^ 2 ≤
      3 * ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2 +
      3 * ‖ψn (y + Pi.single μ 1) - bavgL d L N₀ q n φ (y + Pi.single μ 1)‖ ^ 2 +
      3 * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹) *
        bondEdir μ (fib d L N₀ q n y ∪ fib d L N₀ q n (y + Pi.single μ 1)) φ := by
  set y' := y + Pi.single μ 1 with hy'
  have h1 := sq_norm_add3_le (ψn y - bavgL d L N₀ q n φ y)
    (bavgL d L N₀ q n φ y - bavgL d L N₀ q n φ y')
    (bavgL d L N₀ q n φ y' - ψn y')
  have e : ψn y - bavgL d L N₀ q n φ y + (bavgL d L N₀ q n φ y - bavgL d L N₀ q n φ y') +
      (bavgL d L N₀ q n φ y' - ψn y') = ψn y - ψn y' := by abel
  rw [e] at h1
  have h2 := adjacent_blockAvg_sq_le (sideEq (L := L) (N₀ := N₀) hn) φ y μ
  rw [← fib_eq_blockFibre, ← fib_eq_blockFibre] at h2
  have hc : ((L ^ n : ℕ) : ℝ) = (L : ℝ) ^ n := by push_cast; ring
  rw [hc] at h2
  have h3 : ‖bavgL d L N₀ q n φ y' - ψn y'‖ = ‖ψn y' - bavgL d L N₀ q n φ y'‖ := norm_sub_rev _ _
  rw [h3] at h1
  unfold bavgL
  have := h2
  unfold bavgL at h1
  nlinarith [h1, h2]

section Abstract

variable {d m : ℕ} [NeZero m]

open Classical in
/-- Abstract assembly of the directed sum. -/
theorem directed_sum_le (T : Finset (Torus d m)) (μ : Fin d)
    (Nm : Torus d m → Torus d m → ℝ) (Δ β : Torus d m → ℝ) (c B : ℝ)
    (hΔ0 : ∀ y, 0 ≤ Δ y) (hc : 0 ≤ c)
    (hpair : ∀ y ∈ T, y + Pi.single μ 1 ∈ T →
      Nm y (y + Pi.single μ 1) ≤ 3 * Δ y + 3 * Δ (y + Pi.single μ 1) + 3 * c * β y)
    (hC : ∑ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then β y else 0) ≤ 2 * B) :
    ∑ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Nm y (y + Pi.single μ 1) else 0) ≤
      6 * ∑ y ∈ T, Δ y + 6 * c * B := by
  have hA := sum_ite_le_self T (fun y => y + Pi.single μ 1 ∈ T) Δ hΔ0
  have hB := sum_shift_le_self T (Pi.single μ 1) Δ hΔ0
  have hpt : ∀ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Nm y (y + Pi.single μ 1) else 0) ≤
      3 * (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Δ y else 0) +
      3 * (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Δ (y + Pi.single μ 1) else 0) +
      3 * c * (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then β y else 0) := by
    intro y
    by_cases h : y ∈ T ∧ y + Pi.single μ 1 ∈ T
    · simp only [ite_eq_left h]
      exact hpair y h.1 h.2
    · simp only [ite_eq_right h]; simp
  calc _ ≤ ∑ y, (3 * (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Δ y else 0) +
          3 * (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Δ (y + Pi.single μ 1) else 0) +
          3 * c * (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then β y else 0)) :=
        Finset.sum_le_sum fun y _ => hpt y
    _ = 3 * ∑ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Δ y else 0) +
        3 * ∑ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then Δ (y + Pi.single μ 1) else 0) +
        3 * c * ∑ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then β y else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 3 * ∑ y ∈ T, Δ y + 3 * ∑ y ∈ T, Δ y + 3 * c * (2 * B) := by
        have := mul_le_mul_of_nonneg_left hC (by positivity : 0 ≤ 3 * c)
        linarith
    _ = _ := by ring

end Abstract

open Classical in
/-- The directed sum over the bonds in direction `μ`. -/
theorem directed_bound {n : ℕ} (hn : n ≤ q) (S : Finset (Site d L N₀ q))
    (hS : IsBlockUnion L N₀ q n S) (φ : Site d L N₀ q → E) (ψn : Blk d L N₀ q n → E)
    (μ : Fin d) :
    ∑ y, (if y ∈ tBlocks d L N₀ q n S ∧ y + Pi.single μ 1 ∈ tBlocks d L N₀ q n S then
        ‖ψn y - ψn (y + Pi.single μ 1)‖ ^ 2 else 0) ≤
      6 * ∑ y ∈ tBlocks d L N₀ q n S, ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2 +
        6 * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹) * bondEdir μ S φ := by
  refine directed_sum_le (tBlocks d L N₀ q n S) μ (fun y y' => ‖ψn y - ψn y'‖ ^ 2)
    (fun y => ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2)
    (fun y => bondEdir μ (fib d L N₀ q n y ∪ fib d L N₀ q n (y + Pi.single μ 1)) φ) _ _
    (fun y => by positivity) (by positivity) (fun y _ _ => pair_estimate hn φ ψn y μ) ?_
  rw [← Finset.sum_filter]
  refine (sum_bondEdir_union_le μ (Pi.single μ 1)
    (Finset.univ.filter fun y => y ∈ tBlocks d L N₀ q n S ∧
      y + Pi.single μ 1 ∈ tBlocks d L N₀ q n S) S ?_ φ)
  intro y hy
  rw [Finset.mem_filter] at hy
  exact Finset.union_subset (fib_subset_of_mem_tBlocks hS hy.2.1)
    (fib_subset_of_mem_tBlocks hS hy.2.2)

open Classical in
/-- **Intra-layer bound**: `(L^{n(d-2)}/2) ∑_{{y,y'}∈P_n} ‖ψ_n y - ψ_n y'‖² ≤ 3d Bk_n + 3 E(S)`. -/
theorem intra_bound {n : ℕ} (hn : n ≤ q) (hd : 2 ≤ d) (S : Finset (Site d L N₀ q))
    (hS : IsBlockUnion L N₀ q n S) (φ : Site d L N₀ q → E) (ψn : Blk d L N₀ q n → E) :
    ((L : ℝ) ^ (n * (d - 2)) / 2) * pairSumT (tBlocks d L N₀ q n S) ψn ≤
      3 * d * ((L : ℝ) ^ (n * (d - 2)) *
        ∑ y ∈ tBlocks d L N₀ q n S, ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2) + 3 * bondE S φ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hsum : pairSumT (tBlocks d L N₀ q n S) ψn ≤
      6 * d * ∑ y ∈ tBlocks d L N₀ q n S, ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2 +
        6 * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹) * bondE S φ := by
    refine (pairSumT_le _ ψn).trans ?_
    calc _ ≤ ∑ μ : Fin d, (6 * ∑ y ∈ tBlocks d L N₀ q n S, ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2 +
          6 * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹) * bondEdir μ S φ) :=
          Finset.sum_le_sum fun μ _ => directed_bound hn S hS φ ψn μ
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ← Finset.mul_sum]
          unfold bondE
          ring
  have hw := weight_mul_c hd hL n
  have hw0 : 0 ≤ (L : ℝ) ^ (n * (d - 2)) / 2 := by positivity
  calc _ ≤ ((L : ℝ) ^ (n * (d - 2)) / 2) * (6 * d *
          ∑ y ∈ tBlocks d L N₀ q n S, ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2 +
        6 * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹) * bondE S φ) :=
        mul_le_mul_of_nonneg_left hsum hw0
    _ = 3 * d * ((L : ℝ) ^ (n * (d - 2)) *
          ∑ y ∈ tBlocks d L N₀ q n S, ‖ψn y - bavgL d L N₀ q n φ y‖ ^ 2) +
        3 * ((L : ℝ) ^ (n * (d - 2)) * (((L : ℝ) ^ n) ^ 2 * (((L : ℝ) ^ n) ^ d)⁻¹)) *
          bondE S φ := by ring
    _ = _ := by rw [hw]; ring

section Cross

open Classical in
theorem qCoarse_sub {n : ℕ} (f g : Blk d L N₀ q n → E) (b : Blk d L N₀ q (n + 1)) :
    qCoarse d L N₀ q n f b - qCoarse d L N₀ q n g b =
      ((L : ℝ) ^ d)⁻¹ • ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = b), (f s - g s) := by
  unfold qCoarse
  rw [← smul_sub, Finset.sum_sub_distrib]

open Classical in
/-- The one-pair estimate of the cross term. -/
theorem cross_estimate {n : ℕ} (hn : n < q) (φ : Site d L N₀ q → E)
    (ψ1 : Blk d L N₀ q (n + 1) → E) (ψ0 : Blk d L N₀ q n → E)
    (bp bm : Blk d L N₀ q (n + 1)) :
    ‖ψ1 bp - qCoarse d L N₀ q n ψ0 bm‖ ^ 2 ≤
      3 * ‖ψ1 bp - bavgL d L N₀ q (n + 1) φ bp‖ ^ 2 +
      3 * ‖bavgL d L N₀ q (n + 1) φ bp - bavgL d L N₀ q (n + 1) φ bm‖ ^ 2 +
      3 * (((L : ℝ) ^ d)⁻¹ * ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = bm),
        ‖ψ0 s - bavgL d L N₀ q n φ s‖ ^ 2) := by
  have hL : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hcard : ((Finset.univ.filter (fun s : Blk d L N₀ q n => coarse d L N₀ q n s = bm)).card : ℝ)
      = (L : ℝ) ^ d := by
    rw [card_coarse_fibre hn]; push_cast; ring
  have hq := bavgL_succ hn φ bm
  have e : ψ1 bp - qCoarse d L N₀ q n ψ0 bm =
      (ψ1 bp - bavgL d L N₀ q (n + 1) φ bp) +
      (bavgL d L N₀ q (n + 1) φ bp - bavgL d L N₀ q (n + 1) φ bm) +
      (qCoarse d L N₀ q n (bavgL d L N₀ q n φ) bm - qCoarse d L N₀ q n ψ0 bm) := by
    rw [← hq]; abel
  have h3 := sq_norm_add3_le (ψ1 bp - bavgL d L N₀ q (n + 1) φ bp)
    (bavgL d L N₀ q (n + 1) φ bp - bavgL d L N₀ q (n + 1) φ bm)
    (qCoarse d L N₀ q n (bavgL d L N₀ q n φ) bm - qCoarse d L N₀ q n ψ0 bm)
  rw [← e] at h3
  have hj : ‖qCoarse d L N₀ q n (bavgL d L N₀ q n φ) bm - qCoarse d L N₀ q n ψ0 bm‖ ^ 2 ≤
      ((L : ℝ) ^ d)⁻¹ * ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = bm),
        ‖ψ0 s - bavgL d L N₀ q n φ s‖ ^ 2 := by
    rw [qCoarse_sub]
    refine (sq_norm_avg_le _ _ hcard hL).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [norm_sub_rev]
  linarith

/-- II.4.2 in the form used for pairs `(b, b + v)`, `v = ±e_μ`. -/
theorem bavgL_pair_le {k : ℕ} (hk : k ≤ q) (φ : Site d L N₀ q → E) (b : Blk d L N₀ q k)
    (μ : Fin d) {v : Blk d L N₀ q k} (hv : v = Pi.single μ 1 ∨ v = -Pi.single μ 1) :
    ‖bavgL d L N₀ q k φ b - bavgL d L N₀ q k φ (b + v)‖ ^ 2 ≤
      (((L : ℝ) ^ k) ^ 2 * (((L : ℝ) ^ k) ^ d)⁻¹) *
        bondEdir μ (fib d L N₀ q k b ∪ fib d L N₀ q k (b + v)) φ := by
  have hc : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by push_cast; ring
  rcases hv with rfl | rfl
  · have h2 := adjacent_blockAvg_sq_le (sideEq (L := L) (N₀ := N₀) hk) φ b μ
    rw [← fib_eq_blockFibre, ← fib_eq_blockFibre, hc] at h2
    exact h2
  · have h2 := adjacent_blockAvg_sq_le (sideEq (L := L) (N₀ := N₀) hk) φ (b + -Pi.single μ 1) μ
    rw [← fib_eq_blockFibre, ← fib_eq_blockFibre, hc] at h2
    have e : b + -Pi.single μ 1 + Pi.single μ 1 = b := by abel
    rw [e, Finset.union_comm] at h2
    rw [norm_sub_rev]
    exact h2

variable {ϱ : ℝ}

/-- The condition defining the cross pairs `(b₊, b₋)` of `P^×_{n+1}(X)` (besides adjacency). -/
def CrossK (G : GeneratingSet d L N₀ q ϱ) (n : ℕ) (X : Finset (Site d L N₀ q))
    (bp bm : Blk d L N₀ q (n + 1)) : Prop :=
  fib d L N₀ q (n + 1) bp ⊆ X ∩ G.Ω (n + 1) ∧ fib d L N₀ q (n + 1) bm ⊆ X ∧
    Disjoint (fib d L N₀ q (n + 1) bm) (G.Ω (n + 1))

open Classical in
/-- The sum over the pairs `(b, b + v)`, `v = ±e_μ`, of the cross term. -/
theorem cross_dir_bound (G : GeneratingSet d L N₀ q ϱ) {n : ℕ} (hn : n < q)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) (X : Finset (Site d L N₀ q)) (φ : Site d L N₀ q → E)
    (ψ1 : Blk d L N₀ q (n + 1) → E) (ψ0 : Blk d L N₀ q n → E)
    (hψ0 : n = 0 → ∀ s, ψ0 s = bavgL d L N₀ q n φ s) (μ : Fin d) {v : Blk d L N₀ q (n + 1)}
    (hv : v = Pi.single μ 1 ∨ v = -Pi.single μ 1) :
    ∑ bp : Blk d L N₀ q (n + 1), (if CrossK G n X bp (bp + v) then
        ‖ψ1 bp - qCoarse d L N₀ q n ψ0 (bp + v)‖ ^ 2 else 0) ≤
      3 * ∑ y ∈ tBlocks d L N₀ q (n + 1) (lam G (n + 1) ∩ X),
          ‖ψ1 y - bavgL d L N₀ q (n + 1) φ y‖ ^ 2 +
        6 * (((L : ℝ) ^ (n + 1)) ^ 2 * (((L : ℝ) ^ (n + 1)) ^ d)⁻¹) *
          bondEdir μ ((lam G n ∪ lam G (n + 1)) ∩ X) φ +
        3 * (((L : ℝ) ^ d)⁻¹ * ∑ s ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          ‖ψ0 s - bavgL d L N₀ q n φ s‖ ^ 2) := by
  have hLd : (0 : ℝ) < ((L : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set T1 := tBlocks d L N₀ q (n + 1) (lam G (n + 1) ∩ X) with hT1
  set T0 := tBlocks d L N₀ q n (lam G n ∩ X) with hT0
  set Δ1 : Blk d L N₀ q (n + 1) → ℝ := fun y => ‖ψ1 y - bavgL d L N₀ q (n + 1) φ y‖ ^ 2 with hΔ1
  set Δ0 : Blk d L N₀ q n → ℝ := fun s => ‖ψ0 s - bavgL d L N₀ q n φ s‖ ^ 2 with hΔ0
  set W : Blk d L N₀ q n → ℝ := fun s => if s ∈ T0 then Δ0 s else 0 with hW
  set c1 : ℝ := ((L : ℝ) ^ (n + 1)) ^ 2 * (((L : ℝ) ^ (n + 1)) ^ d)⁻¹ with hc1
  have hΔ10 : ∀ y, 0 ≤ Δ1 y := fun y => by rw [hΔ1]; positivity
  have hW0 : ∀ s, 0 ≤ W s := fun s => by
    rw [hW]; simp only; split_ifs
    exacts [by rw [hΔ0]; positivity, le_rfl]
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hgs : ∀ y : Blk d L N₀ q (n + 1), 0 ≤ ∑ s ∈ Finset.univ.filter
      (fun s => coarse d L N₀ q n s = y), W s := fun y => Finset.sum_nonneg fun s _ => hW0 s
  -- geometry of a pair satisfying the condition
  have hadj : ∀ bp, CrossK G n X bp (bp + v) →
      ∃ μ' : Fin d, bp + v = bp + Pi.single μ' 1 ∨ bp = (bp + v) + Pi.single μ' 1 := by
    intro bp _
    rcases hv with rfl | rfl
    · exact ⟨μ, Or.inl rfl⟩
    · exact ⟨μ, Or.inr (by abel)⟩
  have hsub : ∀ bp, CrossK G n X bp (bp + v) → fib d L N₀ q (n + 1) bp ⊆ lam G (n + 1) ∩ X ∧
      fib d L N₀ q (n + 1) (bp + v) ⊆ lam G n ∩ X := fun bp hK =>
    cross_fib_subsets G hn hϱ (hadj bp hK) hK.1 hK.2.1 hK.2.2
  have hbp : ∀ bp, CrossK G n X bp (bp + v) → bp ∈ T1 := by
    intro bp hK
    obtain ⟨x, hx⟩ := fib_nonempty (d := d) (L := L) (N₀ := N₀) (q := q) (n := n + 1) (by omega) bp
    exact mem_tBlocks.2 ⟨x, (hsub bp hK).1 hx, mem_fib.1 hx⟩
  have hΔW : ∀ bp, CrossK G n X bp (bp + v) → ∀ s, coarse d L N₀ q n s = bp + v → Δ0 s ≤ W s := by
    intro bp hK s hs
    by_cases h0 : n = 0
    · have := hψ0 h0 s
      rw [hΔ0]; simp only [this, sub_self, norm_zero]
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num]
      exact hW0 s
    · have hsT : s ∈ T0 := by
        obtain ⟨x, hx⟩ := fib_nonempty (d := d) (L := L) (N₀ := N₀) (q := q) (n := n) hn.le s
        exact mem_tBlocks.2 ⟨x, (hsub bp hK).2 (fib_subset_of_coarse hn hs hx), mem_fib.1 hx⟩
      rw [hW]; simp only [hsT, ↓reduceIte, le_refl]
  -- the pointwise estimate
  have hpt : ∀ bp, (if CrossK G n X bp (bp + v) then
        ‖ψ1 bp - qCoarse d L N₀ q n ψ0 (bp + v)‖ ^ 2 else 0) ≤
      3 * (if bp ∈ T1 then Δ1 bp else 0) +
      3 * c1 * (if CrossK G n X bp (bp + v) then
        bondEdir μ (fib d L N₀ q (n + 1) bp ∪ fib d L N₀ q (n + 1) (bp + v)) φ else 0) +
      3 * (((L : ℝ) ^ d)⁻¹ * ∑ s ∈ Finset.univ.filter
        (fun s => coarse d L N₀ q n s = bp + v), W s) := by
    intro bp
    have hb0 : 0 ≤ bondEdir μ (fib d L N₀ q (n + 1) bp ∪ fib d L N₀ q (n + 1) (bp + v)) φ :=
      bondEdir_nonneg _ _ _
    by_cases hK : CrossK G n X bp (bp + v)
    · simp only [ite_eq_left hK, ite_eq_left (hbp bp hK)]
      have h1 := cross_estimate hn φ ψ1 ψ0 bp (bp + v)
      have h2 := bavgL_pair_le (k := n + 1) (by omega) φ bp μ hv
      have h3 : ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = bp + v), Δ0 s ≤
          ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = bp + v), W s :=
        Finset.sum_le_sum fun s hs => hΔW bp hK s (Finset.mem_filter.1 hs).2
      have h4 := mul_le_mul_of_nonneg_left h3 hLd.le
      show _ ≤ 3 * Δ1 bp + 3 * c1 * _ + _
      nlinarith [h1, h2, h4]
    · simp only [ite_eq_right hK]
      have h5 : 0 ≤ (if bp ∈ T1 then Δ1 bp else 0) := by
        split_ifs; exacts [hΔ10 bp, le_rfl]
      have h6 := hgs (bp + v)
      nlinarith [mul_nonneg hLd.le h6]
  -- summation
  calc _ ≤ ∑ bp : Blk d L N₀ q (n + 1), (3 * (if bp ∈ T1 then Δ1 bp else 0) +
        3 * c1 * (if CrossK G n X bp (bp + v) then
          bondEdir μ (fib d L N₀ q (n + 1) bp ∪ fib d L N₀ q (n + 1) (bp + v)) φ else 0) +
        3 * (((L : ℝ) ^ d)⁻¹ * ∑ s ∈ Finset.univ.filter
          (fun s => coarse d L N₀ q n s = bp + v), W s)) :=
        Finset.sum_le_sum fun bp _ => hpt bp
    _ = 3 * ∑ bp : Blk d L N₀ q (n + 1), (if bp ∈ T1 then Δ1 bp else 0) +
        3 * c1 * ∑ bp : Blk d L N₀ q (n + 1), (if CrossK G n X bp (bp + v) then
          bondEdir μ (fib d L N₀ q (n + 1) bp ∪ fib d L N₀ q (n + 1) (bp + v)) φ else 0) +
        3 * (((L : ℝ) ^ d)⁻¹ * ∑ bp : Blk d L N₀ q (n + 1), ∑ s ∈ Finset.univ.filter
          (fun s => coarse d L N₀ q n s = bp + v), W s) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 3 * ∑ y ∈ T1, Δ1 y + 3 * c1 * (2 * bondEdir μ ((lam G n ∪ lam G (n + 1)) ∩ X) φ) +
        3 * (((L : ℝ) ^ d)⁻¹ * ∑ s ∈ T0, Δ0 s) := by
        have hA : ∑ bp : Blk d L N₀ q (n + 1), (if bp ∈ T1 then Δ1 bp else 0) = ∑ y ∈ T1, Δ1 y :=
          (sum_mem_eq T1 Δ1).symm
        have hB : ∑ bp : Blk d L N₀ q (n + 1), (if CrossK G n X bp (bp + v) then
            bondEdir μ (fib d L N₀ q (n + 1) bp ∪ fib d L N₀ q (n + 1) (bp + v)) φ else 0) ≤
            2 * bondEdir μ ((lam G n ∪ lam G (n + 1)) ∩ X) φ := by
          rw [← Finset.sum_filter]
          refine sum_bondEdir_union_le μ v _ _ ?_ φ
          intro bp hbp'
          have hK := (Finset.mem_filter.1 hbp').2
          obtain ⟨h1, h2⟩ := hsub bp hK
          refine Finset.union_subset ?_ ?_
          · intro x hx
            have := h1 hx
            rw [Finset.mem_inter] at this ⊢
            exact ⟨Finset.mem_union_right _ this.1, this.2⟩
          · intro x hx
            have := h2 hx
            rw [Finset.mem_inter] at this ⊢
            exact ⟨Finset.mem_union_left _ this.1, this.2⟩
        have hC : ∑ bp : Blk d L N₀ q (n + 1), ∑ s ∈ Finset.univ.filter
            (fun s => coarse d L N₀ q n s = bp + v), W s = ∑ s ∈ T0, Δ0 s := by
          rw [sum_shift v (fun bm => ∑ s ∈ Finset.univ.filter (fun s => coarse d L N₀ q n s = bm), W s)]
          rw [Finset.sum_fiberwise Finset.univ (coarse d L N₀ q n) W]
          rw [sum_mem_eq T0 Δ0]
        rw [hA, hC]
        have := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 3 * c1)
        linarith
    _ = _ := by ring

omit [NeZero L] in
theorem weight_succ_le (hd : 2 ≤ d) (hL : 2 ≤ L) (n : ℕ) :
    (L : ℝ) ^ ((n + 1) * (d - 2)) * ((L : ℝ) ^ d)⁻¹ ≤ (1 / 4) * (L : ℝ) ^ (n * (d - 2)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hpos : (0 : ℝ) < L := by linarith
  simp only [Nat.add_sub_cancel_left]
  have e : (L : ℝ) ^ ((n + 1) * k) * ((L : ℝ) ^ (2 + k))⁻¹ =
      (L : ℝ) ^ (n * k) * ((L : ℝ) ^ 2)⁻¹ := by
    rw [add_mul, one_mul, pow_add, pow_add, mul_inv]
    field_simp
  rw [e]
  have h4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hp : (0 : ℝ) < (L : ℝ) ^ (n * k) := by positivity
  have : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h4
  nlinarith

open Classical in
/-- **Cross bound**: `(L^{(n+1)(d-2)}/2) ∑_{P^×_{n+1}} ‖ψ_{n+1}(b₊) - (Qψ_n)(b₋)‖²
 ≤ 3d Bk_{n+1} + (3d/4) Bk_n + 6 E(S^×)`. -/
theorem cross_bound (G : GeneratingSet d L N₀ q ϱ) {n : ℕ} (hn : n < q) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) (X : Finset (Site d L N₀ q)) (φ : Site d L N₀ q → E)
    (ψf : (m : ℕ) → Blk d L N₀ q m → E) (hψf0 : ∀ y, ψf 0 y = bavgL d L N₀ q 0 φ y) :
    ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) * crossSumP G n X ψf ≤
      3 * d * ((L : ℝ) ^ ((n + 1) * (d - 2)) *
        ∑ y ∈ tBlocks d L N₀ q (n + 1) (lam G (n + 1) ∩ X),
          ‖ψf (n + 1) y - bavgL d L N₀ q (n + 1) φ y‖ ^ 2) +
      (3 * d / 4) * ((L : ℝ) ^ (n * (d - 2)) * ∑ s ∈ tBlocks d L N₀ q n (lam G n ∩ X),
          ‖ψf n s - bavgL d L N₀ q n φ s‖ ^ 2) +
      6 * bondE ((lam G n ∪ lam G (n + 1)) ∩ X) φ := by
  have hL0 : 0 < L := by omega
  have hψ0 : n = 0 → ∀ s, ψf n s = bavgL d L N₀ q n φ s := by
    rintro rfl s; exact hψf0 s
  set T1 := tBlocks d L N₀ q (n + 1) (lam G (n + 1) ∩ X) with hT1
  set T0 := tBlocks d L N₀ q n (lam G n ∩ X) with hT0
  set Sx := (lam G n ∪ lam G (n + 1)) ∩ X with hSx
  set A1 := ∑ y ∈ T1, ‖ψf (n + 1) y - bavgL d L N₀ q (n + 1) φ y‖ ^ 2 with hA1
  set A0 := ∑ s ∈ T0, ‖ψf n s - bavgL d L N₀ q n φ s‖ ^ 2 with hA0
  have hA0n : 0 ≤ A0 := Finset.sum_nonneg fun _ _ => by positivity
  have hA1n : 0 ≤ A1 := Finset.sum_nonneg fun _ _ => by positivity
  set c1 : ℝ := ((L : ℝ) ^ (n + 1)) ^ 2 * (((L : ℝ) ^ (n + 1)) ^ d)⁻¹ with hc1
  have hsum : crossSumP G n X ψf ≤
      6 * d * A1 + 12 * c1 * bondE Sx φ + 6 * d * (((L : ℝ) ^ d)⁻¹ * A0) := by
    have hF0 : ∀ bp bm : Blk d L N₀ q (n + 1), 0 ≤ ‖ψf (n + 1) bp - qCoarse d L N₀ q n (ψf n) bm‖ ^ 2 :=
      fun _ _ => by positivity
    have h1 := sum_adj_le (CrossK G n X)
      (fun bp bm => ‖ψf (n + 1) bp - qCoarse d L N₀ q n (ψf n) bm‖ ^ 2) hF0
    have h2 : crossSumP G n X ψf = ∑ bp : Blk d L N₀ q (n + 1), ∑ bm : Blk d L N₀ q (n + 1),
        (if AdjT bp bm ∧ CrossK G n X bp bm then
          ‖ψf (n + 1) bp - qCoarse d L N₀ q n (ψf n) bm‖ ^ 2 else 0) := by
      unfold crossSumP CrossK
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by congr
    rw [h2]
    refine h1.trans ?_
    have hP := fun μ => cross_dir_bound G hn hϱ X φ (ψf (n + 1)) (ψf n) hψ0 μ
      (v := Pi.single μ 1) (Or.inl rfl)
    have hM := fun μ => cross_dir_bound G hn hϱ X φ (ψf (n + 1)) (ψf n) hψ0 μ
      (v := -Pi.single μ 1) (Or.inr rfl)
    calc _ ≤ ∑ μ : Fin d, (3 * A1 + 6 * c1 * bondEdir μ Sx φ + 3 * (((L : ℝ) ^ d)⁻¹ * A0)) +
          ∑ μ : Fin d, (3 * A1 + 6 * c1 * bondEdir μ Sx φ + 3 * (((L : ℝ) ^ d)⁻¹ * A0)) :=
          add_le_add (Finset.sum_le_sum fun μ _ => hP μ) (Finset.sum_le_sum fun μ _ => hM μ)
      _ = _ := by
          rw [← two_mul, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul,
            ← Finset.mul_sum]
          unfold bondE
          ring
  have hw := weight_mul_c hd hL0 (n + 1)
  have hws := weight_succ_le hd hL n
  have hw0 : 0 ≤ (L : ℝ) ^ ((n + 1) * (d - 2)) / 2 := by positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  calc ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) * crossSumP G n X ψf
      ≤ ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
        (6 * d * A1 + 12 * c1 * bondE Sx φ + 6 * d * (((L : ℝ) ^ d)⁻¹ * A0)) :=
        mul_le_mul_of_nonneg_left hsum hw0
    _ = 3 * d * ((L : ℝ) ^ ((n + 1) * (d - 2)) * A1) +
        6 * ((L : ℝ) ^ ((n + 1) * (d - 2)) * c1) * bondE Sx φ +
        3 * d * ((L : ℝ) ^ ((n + 1) * (d - 2)) * ((L : ℝ) ^ d)⁻¹) * A0 := by ring
    _ ≤ 3 * d * ((L : ℝ) ^ ((n + 1) * (d - 2)) * A1) + 6 * 1 * bondE Sx φ +
        3 * d * ((1 / 4) * (L : ℝ) ^ (n * (d - 2))) * A0 := by
        rw [hc1, hw]
        gcongr
    _ = _ := by ring

end Cross

end Intra

end Balaban.LargeField
