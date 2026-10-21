/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.SmallFactorAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# LF-1 for a violation in the top layer of an arbitrary generating set (P6 (3.5)-(3.6))

`R/SmallFactorAction.lean` proves the cost of a violation of `Ψ̃` for the *single-scale* generating
set (`Ω_n = 𝕋` for `n ≤ k`, so that `Λ_k = 𝕋`).  The base step of Lemma II.7.8 needs the same
statement for the history's generating set at level `1`, whose top layer `Λ_1 = Ω_1` is a proper
subset of the torus.  The statements here are for an arbitrary generating set and the blocks of the
top layer `lam G q ∩ X`:

* `lf1_pair_gain`: two adjacent `q`-blocks `y, y'` of `Λ_q ∩ X` cost
  `γ₀ L^{q(d-2)} |ψ_q(y) - ψ_q(y')|²/2` (LF-1 (a));
* `lf1_point_gain`: a `q`-block `y` of `Λ_q ∩ X` on whose fibre the field `φ` is a unit field costs
  `γ₀ L^{q(d-2)} (|ψ_q(y)| - 1)²/2` (LF-1 (b), without the condition `ψ_q(y) ≠ 0`);
* `lf1_violation_gain`: if `ψ_q ∉ Ψ̃(blocks ⊂ Xc; θ)` for a set `Xc ⊆ Λ_q ∩ X` on which `φ`
  is a unit field, the cost is at least `γ₀ L^{q(d-2)} θ²/2`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Top

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- For `n ≥ 1` the layer `Λ_n` is `Ω_n ∖ Ω_{n+1}`. -/
theorem lam_of_pos (G : GeneratingSet d L N₀ q ϱ) {n : ℕ} (hn : 1 ≤ n) : lam G n = G.layer n := by
  unfold lam
  split_ifs with h0
  · omega
  · rfl

/-- **Two adjacent blocks of the top layer cost** `γ₀ L^{q(d-2)} |ψ_q(y) - ψ_q(y')|²/2`. -/
theorem lf1_pair_gain (G : GeneratingSet d L N₀ q ϱ) (hq : 1 ≤ q) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights q a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ q)}
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) {y y' : Blk d L N₀ q q}
    (hy : y ∈ tBlocks d L N₀ q q (lam G q ∩ X)) (hy' : y' ∈ tBlocks d L N₀ q q (lam G q ∩ X))
    (hadj : AdjT y y') :
    gamma0 d * ((L : ℝ) ^ (q * (d - 2)) / 2 * ‖ψ q y - ψ q y'‖ ^ 2) ≤
      actionG G a μ h X ψ φ := by
  refine le_trans ?_ (lf1_gradient G hd hL hϱ ha hμ h X hX ψ φ)
  have hg : 0 ≤ gamma0 d := by unfold gamma0; positivity
  refine mul_le_mul_of_nonneg_left ?_ hg
  have hnn : ∀ n ∈ Finset.range (q + 1), 0 ≤ ((L : ℝ) ^ (n * (d - 2)) / 2) *
      pairSumT (tBlocks d L N₀ q n (lam G n ∩ X)) (psiFull φ ψ n) := fun n _ =>
    mul_nonneg (by positivity) (pairSumT_nonneg _ _)
  have hcr : 0 ≤ ∑ n ∈ Finset.range q, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
      crossSumP G n X (psiFull φ ψ) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (crossSumP_nonneg _ _ _ _)
  have h1 := Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.lt_succ_self q))
  rw [psiFull_of_pos φ ψ hq] at h1
  have h2 := le_pairSumT (tBlocks d L N₀ q q (lam G q ∩ X)) (ψ q) hy hy' hadj
  have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (q * (d - 2)) / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hL0
  linarith

/-- **A unit block of the top layer with `|ψ_q(y)| ≠ 1` costs** `γ₀ L^{q(d-2)} (|ψ_q(y)| - 1)²/2`,
when `φ` is a unit field on the fibre of `y` (LF-1 (b) without the condition `ψ_q(y) ≠ 0`). -/
theorem lf1_point_gain (G : GeneratingSet d L N₀ q ϱ) (hq : 1 ≤ q) (hd : 2 ≤ d)
    {a : ℕ → ℝ} (ha : IsAdmissibleWeights q a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X : Finset (Site d L N₀ q)}
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) {y : Blk d L N₀ q q}
    (hy : y ∈ tBlocks d L N₀ q q (lam G q ∩ X)) (hφ : ∀ x ∈ fib d L N₀ q q y, ‖φ x‖ = 1) :
    gamma0 d * ((L : ℝ) ^ (q * (d - 2)) * (1 / 2 * (‖ψ q y‖ - 1) ^ 2)) ≤
      actionG G a μ h X ψ φ := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hlam : lam G q = G.layer q := lam_of_pos G hq
  have hXq : IsBlockUnion L N₀ q q (X ∩ G.layer q) := hX q hq le_rfl
  have hlX : lam G q ∩ X = X ∩ G.layer q := by rw [hlam, Finset.inter_comm]
  rw [hlX] at hy
  set Q := bavgL d L N₀ q q φ y with hQ
  set ε := bondE (fib d L N₀ q q y) φ with hε
  have hε0 : 0 ≤ ε := bondE_nonneg _ _
  set Lk : ℝ := (L : ℝ) ^ (q * (d - 2)) with hLk
  have hLkpos : 0 < Lk := by positivity
  set w : ℝ := ((L : ℝ) ^ q) ^ 2 * (((L : ℝ) ^ q) ^ d)⁻¹ with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hWw : Lk * w = 1 := weight_mul_c hd hL0 q
  have hcast : ((L ^ q : ℕ) : ℝ) = (L : ℝ) ^ q := by push_cast; ring
  have h1 : 1 - ‖Q‖ ^ 2 ≤ (w * ε) / 2 := by
    have := hardSpin_one_sub_sq_le (sideEq (L := L) (N₀ := N₀) (le_refl q)) φ y hφ
    rw [← fib_eq_blockFibre, hcast] at this
    rw [hQ, bavgL_eq, hε, hw]
    linarith
  have hQ1 : ‖Q‖ ≤ 1 := norm_bavg_le_one le_rfl φ y hφ
  set Δ := ‖ψ q y - Q‖ ^ 2 with hΔ
  set P := (‖ψ q y‖ - 1) ^ 2 with hP
  have hQ0 : 0 ≤ ‖Q‖ := norm_nonneg _
  have hP1 : P ≤ 2 * Δ + 2 * (1 - ‖Q‖ ^ 2) := by
    have h2 : |‖ψ q y‖ - ‖Q‖| ≤ ‖ψ q y - Q‖ := abs_norm_sub_norm_le _ _
    have ha2 : (‖ψ q y‖ - ‖Q‖) ^ 2 ≤ Δ := by
      calc (‖ψ q y‖ - ‖Q‖) ^ 2 = |‖ψ q y‖ - ‖Q‖| ^ 2 := (sq_abs _).symm
        _ ≤ ‖ψ q y - Q‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hb : (1 - ‖Q‖) ^ 2 ≤ 1 - ‖Q‖ ^ 2 := by nlinarith
    have : P = ((‖ψ q y‖ - ‖Q‖) - (1 - ‖Q‖)) ^ 2 := by rw [hP]; ring
    rw [this]
    nlinarith [sq_nonneg ((‖ψ q y‖ - ‖Q‖) + (1 - ‖Q‖))]
  -- lower bound for the action
  have hac := actionG_ge G ha (μ := μ) h X ψ φ
  have hblock : Lk * Δ ≤ bk G X φ ψ q := by
    unfold bk
    rw [psiFull_of_pos φ ψ hq, hlX]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun y' => ‖ψ q y' - bavgL d L N₀ q q φ y'‖ ^ 2)
        (fun y' _ => by positivity) hy) hLkpos.le
  have hBk : 0 ≤ ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n := Finset.sum_nonneg fun n _ => bk_nonneg G X φ ψ n
  have hbkq : bk G X φ ψ q ≤ ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n :=
    Finset.single_le_sum (f := fun n => bk G X φ ψ n) (fun n _ => bk_nonneg G X φ ψ n)
      (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)
  have hbond : ε ≤ bondE X φ := bondE_mono ((fib_subset_of_mem_tBlocks hXq hy).trans Finset.inter_subset_left) φ
  have hmass : 0 ≤ μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  have hact : 1 / 4 * (Lk * Δ) + 1 / 2 * ε ≤ actionG G a μ h X ψ φ := by
    linarith
  have hr : Lk * (1 - ‖Q‖ ^ 2) ≤ ε / 2 := by
    calc Lk * (1 - ‖Q‖ ^ 2) ≤ Lk * ((w * ε) / 2) := mul_le_mul_of_nonneg_left h1 hLkpos.le
      _ = (Lk * w) * ε / 2 := by ring
      _ = ε / 2 := by rw [hWw]; ring
  have hg : gamma0 d ≤ 1 / 4 := by
    unfold gamma0
    have : (4 : ℝ) ≤ 28 * d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hPnn : 0 ≤ Lk * (1 / 2 * P) := by positivity
  have hkey : Lk * (1 / 2 * P) ≤ Lk * Δ + ε / 2 := by nlinarith
  calc gamma0 d * (Lk * (1 / 2 * P)) ≤ 1 / 4 * (Lk * (1 / 2 * P)) :=
        mul_le_mul_of_nonneg_right hg hPnn
    _ ≤ 1 / 4 * (Lk * Δ + ε / 2) := by linarith
    _ ≤ _ := by linarith

/-- **A violation of `Ψ̃` in the top layer costs** `γ₀ L^{q(d-2)} θ²/2`: if `Xc ⊆ Λ_q ∩ X` is a
set of sites on which `φ` is a unit field and `ψ_q ∉ Ψ̃(blocks ⊂ Xc; θ)`, then either two
adjacent blocks of `Xc` differ by at least `θ` (LF-1 (a)) or a block has `||ψ_q| - 1| ≥ θ`
(LF-1 (b)). -/
theorem lf1_violation_gain (G : GeneratingSet d L N₀ q ϱ) (hq : 1 ≤ q) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a : ℕ → ℝ} (ha : IsAdmissibleWeights q a) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {X Xc : Finset (Site d L N₀ q)}
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (hXcX : Xc ⊆ lam G q ∩ X)
    (ψ : (m : ℕ) → Blk d L N₀ q m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ q → EuclideanSpace ℝ (Fin Nspin)) (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1) {θ : ℝ}
    (hθ : 0 ≤ θ) (hviol : ¬ PsiTildeSet {y : Blk d L N₀ q q | fib d L N₀ q q y ⊆ Xc} (ψ q) θ) :
    gamma0 d * ((L : ℝ) ^ (q * (d - 2)) * (θ ^ 2 / 2)) ≤ actionG G a μ h X ψ φ := by
  have hg0 : 0 ≤ gamma0 d := by unfold gamma0; positivity
  have hmem : ∀ y : Blk d L N₀ q q, fib d L N₀ q q y ⊆ Xc →
      y ∈ tBlocks d L N₀ q q (lam G q ∩ X) := fun y hy => by
    obtain ⟨x, hx⟩ := fib_nonempty le_rfl y
    exact mem_tBlocks.2 ⟨x, hXcX (hy hx), mem_fib.1 hx⟩
  unfold PsiTildeSet at hviol
  rw [not_and_or] at hviol
  rcases hviol with hb | hp
  · push Not at hb
    obtain ⟨y, hy, y', hy', hadj, hbig⟩ := hb
    have := lf1_pair_gain G hq hd hL hϱ ha hμ h hX ψ φ (hmem y hy) (hmem y' hy') hadj
    refine le_trans ?_ this
    have h9 : θ ^ 2 ≤ ‖ψ q y - ψ q y'‖ ^ 2 := pow_le_pow_left₀ hθ hbig 2
    have := mul_le_mul_of_nonneg_left h9 (by positivity : 0 ≤ (L : ℝ) ^ (q * (d - 2)) / 2)
    exact mul_le_mul_of_nonneg_left (by nlinarith) hg0
  · push Not at hp
    obtain ⟨y, hy, hbig⟩ := hp
    have := lf1_point_gain G hq hd ha hμ h hX ψ φ (hmem y hy) (fun x hx => hφ x (hy hx))
    refine le_trans ?_ this
    have h9 : θ ^ 2 ≤ (‖ψ q y‖ - 1) ^ 2 := by
      have : θ ^ 2 ≤ |‖ψ q y‖ - 1| ^ 2 := pow_le_pow_left₀ hθ hbig 2
      rwa [sq_abs] at this
    have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (q * (d - 2)) := by positivity
    exact mul_le_mul_of_nonneg_left (by nlinarith) hg0

end Top

end Balaban.LargeField
