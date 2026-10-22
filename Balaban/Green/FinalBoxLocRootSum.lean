/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocW5
public import Balaban.Green.FinalBoxLocTies

/-!
# (W5) of the local form from sums over the roots (A6-3, item (L4))

`sum_norm_localFormOf_le_of_coef` bounds `∑_{Y ∋ x} ‖W_Y‖ ω(Y)` by sums over the terms `a` and the
root cells of their roots.  For terms normalized at the centre (`τ_a(φ₀) = 0`) and a cell graph of
degree at most `Δ` with `Δ² q < 1` (`q = θ e^{-(κ-1)}`) this is at most `B₁ + n_b B₂ B₃`, where

* `B₁` bounds the sum over the terms whose root contains the block `x` of
  `β_a = b_a ω(R_a) (1 + A)^{#root cells of a}`, `A = q / (1 - Δ² q)` (`animalSumConst Δ q`);
* `B₂` bounds, for every cell `l`, the sum of `β_a` over the terms of which `l` is a root cell;
* `B₃ = animalSumConst2 Δ q = q / (1 - Δ² q)²` bounds `∑_{K ∋ i animal} |K| q^{|K|}`;
* `n_b` bounds the number of patches containing `x` (`sum_norm_localFormOf_le_of_rootSums`).

The constants depend on the terms only through the root sums `B₁`, `B₂`.  For the macro cover:
`card_rootCells_le` (a root `R` has at most `16^d · #cells(R)` root cells).
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization

/-- The bound `q / (1 - Δ² q)` of the sums of `q^{|K|}` over the animals through a cell. -/
noncomputable def animalSumConst (Δ : ℕ) (q : ℝ) : ℝ := q / (1 - (Δ : ℝ) ^ 2 * q)

theorem animalSumConst_nonneg {Δ : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq : (Δ : ℝ) ^ 2 * q < 1) :
    0 ≤ animalSumConst Δ q :=
  div_nonneg hq0 (by linarith)

section Animals

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Set Ω}

open Classical in
/-- **The animals through a cell**: `∑_{K ∋ i} q^{|K|} ≤ q / (1 - Δ² q)` for a cell graph of
degree at most `Δ` and `0 < q`, `Δ² q < 1`. -/
theorem sum_animalsAt_prod_le {Δ : ℕ} (hΔ : ∀ v, (cellGraph P).degree v ≤ Δ) {q : ℝ}
    (hq0 : 0 < q) (hq : (Δ : ℝ) ^ 2 * q < 1) (i : ι) :
    ∑ K ∈ animalsAt P i, ∏ _l ∈ K, q ≤ animalSumConst Δ q := by
  have e : ∀ K : Finset ι, ∏ _l ∈ K, q = Real.exp (-(-Real.log q) * K.card) := by
    intro K
    rw [Finset.prod_const, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hq0]
  simp only [e]
  refine (sum_animalsAt_exp_le hΔ _ i).trans ?_
  have hq' : (Δ : ℝ) ^ 2 * Real.exp (-(-Real.log q)) < 1 := by
    rwa [neg_neg, Real.exp_log hq0]
  refine (sum_range_pow_exp_le hq' _).trans (le_of_eq ?_)
  rw [neg_neg, Real.exp_log hq0, animalSumConst]

/-- `∑_{n < m} (n + 1) x^n ≤ 1 / (1 - x)²` for `0 ≤ x < 1`. -/
theorem sum_range_succ_mul_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    ∑ n ∈ Finset.range m, ((n : ℝ) + 1) * x ^ n ≤ 1 / (1 - x) ^ 2 := by
  have key : ∀ m : ℕ, (∑ n ∈ Finset.range m, ((n : ℝ) + 1) * x ^ n) * (1 - x) ^ 2 =
      1 - ((m : ℝ) + 1) * x ^ m + m * x ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      push_cast
      ring
  have hpos : 0 < (1 - x) ^ 2 := pow_pos (by linarith) 2
  rw [le_div_iff₀ hpos, key]
  have h1 : 0 ≤ x ^ m * (((m : ℝ) + 1) - m * x) := by
    refine mul_nonneg (pow_nonneg hx0 m) ?_
    have : (m : ℝ) * x ≤ m := mul_le_of_le_one_right (Nat.cast_nonneg m) hx1.le
    linarith
  have e : ((m : ℝ) + 1) * x ^ m - m * x ^ (m + 1) = x ^ m * (((m : ℝ) + 1) - m * x) := by ring
  linarith

/-- The bound `q / (1 - Δ² q)²` of the sums of `|K| q^{|K|}` over the animals through a cell. -/
noncomputable def animalSumConst2 (Δ : ℕ) (q : ℝ) : ℝ := q / (1 - (Δ : ℝ) ^ 2 * q) ^ 2

theorem animalSumConst2_nonneg {Δ : ℕ} {q : ℝ} (hq0 : 0 ≤ q) : 0 ≤ animalSumConst2 Δ q :=
  div_nonneg hq0 (sq_nonneg _)

open Classical in
/-- **The animals through a cell, weighted by their size**:
`∑_{K ∋ i} |K| q^{|K|} ≤ q / (1 - Δ² q)²` (`sum_animalsAt_weight_le` with `f n = n q^n`). -/
theorem sum_animalsAt_card_prod_le {Δ : ℕ} (hΔ : ∀ v, (cellGraph P).degree v ≤ Δ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq : (Δ : ℝ) ^ 2 * q < 1) (i : ι) :
    ∑ K ∈ animalsAt P i, (K.card : ℝ) * ∏ _l ∈ K, q ≤ animalSumConst2 Δ q := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun K _ => by rw [Finset.prod_const]))
    ((sum_animalsAt_weight_le hΔ (fun n : ℕ => (n : ℝ) * q ^ n)
      (fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hq0 n)) i).trans ?_)
  have e2 : ∀ n : ℕ, (Δ : ℝ) ^ (2 * n) * (((n + 1 : ℕ) : ℝ) * q ^ (n + 1)) =
      q * (((n : ℝ) + 1) * ((Δ : ℝ) ^ 2 * q) ^ n) := by
    intro n
    push_cast
    ring
  simp only [e2, ← Finset.mul_sum]
  unfold animalSumConst2
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (sum_range_succ_mul_pow_le (by positivity) hq _) hq0

end Animals

section Form

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Type*} [Fintype A]

open Classical in
/-- **(W5) from the root sums.**  See the module docstring. -/
theorem sum_norm_localFormOf_le_of_rootSums {τ : A → (Λ × Fin N → ℂ) → ℂ} {RA : A → Finset Λ}
    {PB : ι → Finset Λ} {φ₀ : Λ × Fin N → ℂ} {T : (ι → ℂ) → Λ × Fin N → Λ × Fin N → ℂ}
    (w : Λ × Fin N → ℂ) (x : Λ) {κ θ : ℝ} (hθ : 0 < θ) {b : A → ℝ} (hb : ∀ a, 0 ≤ b a)
    (hcoef : ∀ a C, C.Nonempty → IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C →
      ‖rootedCoef (τ a) φ₀ T w C‖ ≤ b a * Real.exp (-(κ - 1) * C.card))
    (hτ0 : ∀ a, τ a φ₀ = 0)
    (ω : Finset Λ → ℝ) (hω0 : ∀ Y, 0 ≤ ω Y)
    (hω : ∀ a C, ω (rootRegion (RA a) PB C) ≤ ω (RA a) * θ ^ C.card)
    {Δ : ℕ} (hΔ : ∀ v, (cellGraph (blockPatch N PB)).degree v ≤ Δ)
    (hq : (Δ : ℝ) ^ 2 * (θ * Real.exp (-(κ - 1))) < 1)
    {B₁ B₂ : ℝ} {nb : ℕ}
    (h1 : ∑ a ∈ Finset.univ.filter (fun a => x ∈ RA a), b a * ω (RA a) *
      (1 + animalSumConst Δ (θ * Real.exp (-(κ - 1)))) ^
        (rootCells (blockPatch N PB) (blockSites N (RA a))).card ≤ B₁)
    (h2 : ∀ l, ∑ a ∈ Finset.univ.filter (fun a => l ∈ rootCells (blockPatch N PB)
        (blockSites N (RA a))), b a * ω (RA a) *
      (1 + animalSumConst Δ (θ * Real.exp (-(κ - 1)))) ^
        (rootCells (blockPatch N PB) (blockSites N (RA a))).card ≤ B₂)
    (hB₂ : 0 ≤ B₂)
    (hnb : (Finset.univ.filter fun i => x ∈ PB i).card ≤ nb) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset Λ => x ∈ Y), ‖localFormOf τ RA PB φ₀ T Y w‖ * ω Y ≤
      B₁ + nb * B₂ * animalSumConst2 Δ (θ * Real.exp (-(κ - 1))) := by
  set P := blockPatch N PB with hP
  set q : ℝ := θ * Real.exp (-(κ - 1)) with hqdef
  have hq0 : 0 < q := mul_pos hθ (Real.exp_pos _)
  have hqe : (Δ : ℝ) ^ 2 * q < 1 := hq
  set Ac := animalSumConst Δ q with hAc
  set B₃ := animalSumConst2 Δ q with hB₃
  have hAc0 : 0 ≤ Ac := animalSumConst_nonneg hq0.le hqe
  have hB₃0 : 0 ≤ B₃ := animalSumConst2_nonneg hq0.le
  set Pr : A → ℝ := fun a => ∏ i ∈ rootCells P (blockSites N (RA a)),
    (1 + ∑ K ∈ animalsAt P i, ∏ _l ∈ K, q) with hPr
  set β : A → ℝ := fun a => b a * ω (RA a) *
    (1 + Ac) ^ (rootCells P (blockSites N (RA a))).card with hβ
  have hPr0 : ∀ a, 0 ≤ Pr a := fun a => Finset.prod_nonneg fun i _ =>
    add_nonneg zero_le_one (Finset.sum_nonneg fun K _ => Finset.prod_nonneg fun _ _ => hq0.le)
  have hPrle : ∀ a, Pr a ≤ (1 + Ac) ^ (rootCells P (blockSites N (RA a))).card := by
    intro a
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun i _ => add_nonneg zero_le_one
      (Finset.sum_nonneg fun K _ => Finset.prod_nonneg fun _ _ => hq0.le)) fun i _ => ?_
    have := sum_animalsAt_prod_le hΔ hq0 hqe i
    linarith
  have hβ0 : ∀ a, 0 ≤ β a := fun a =>
    mul_nonneg (mul_nonneg (hb a) (hω0 _)) (pow_nonneg (add_nonneg zero_le_one hAc0) _)
  have hbωPr : ∀ a, b a * ω (RA a) * Pr a ≤ β a := fun a =>
    mul_le_mul_of_nonneg_left (hPrle a) (mul_nonneg (hb a) (hω0 _))
  refine (sum_norm_localFormOf_le_of_coef w x hθ.le hb hcoef ω hω0 hω).trans ?_
  simp only [hτ0, norm_zero, zero_add]
  refine add_le_add ?_ ?_
  · -- the terms rooted at `x`
    rw [← Finset.sum_filter]
    refine le_trans (Finset.sum_le_sum fun a _ => ?_) h1
    calc b a * Pr a * ω (RA a) = b a * ω (RA a) * Pr a := by ring
      _ ≤ β a := hbωPr a
  · -- the terms reaching `x` through a patch
    have hcount : ∀ i₀, ∑ a, b a * ω (RA a) * ∑ l ∈ rootCells P (blockSites N (RA a)),
        (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ _m ∈ K, q) * Pr a ≤ B₂ * B₃ := by
      intro i₀
      set F : ι → ℝ := fun l => ∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ _m ∈ K, q
        with hF
      have hF0 : ∀ l, 0 ≤ F l := fun l => Finset.sum_nonneg fun K _ =>
        Finset.prod_nonneg fun _ _ => hq0.le
      have e1 : ∀ a, b a * ω (RA a) * ∑ l ∈ rootCells P (blockSites N (RA a)), F l * Pr a ≤
          ∑ l, (if l ∈ rootCells P (blockSites N (RA a)) then β a else 0) * F l := by
        intro a
        rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun l => l ∈ rootCells P (blockSites N (RA a)))]
        have h0 : ∑ l ∈ Finset.univ.filter (fun l => l ∉ rootCells P (blockSites N (RA a))),
            (if l ∈ rootCells P (blockSites N (RA a)) then β a else 0) * F l = 0 :=
          Finset.sum_eq_zero fun l hl => by simp [(Finset.mem_filter.1 hl).2]
        rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
        refine Finset.sum_le_sum fun l hl => ?_
        simp only [hl, ↓reduceIte]
        calc b a * ω (RA a) * (F l * Pr a) = (b a * ω (RA a) * Pr a) * F l := by ring
          _ ≤ β a * F l := mul_le_mul_of_nonneg_right (hbωPr a) (hF0 l)
      refine (Finset.sum_le_sum fun a _ => e1 a).trans ?_
      rw [Finset.sum_comm]
      have e2 : ∀ l, ∑ a, (if l ∈ rootCells P (blockSites N (RA a)) then β a else 0) * F l =
          (∑ a ∈ Finset.univ.filter (fun a => l ∈ rootCells P (blockSites N (RA a))), β a) *
            F l := by
        intro l
        rw [Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        split_ifs <;> simp
      simp only [e2]
      calc ∑ l, (∑ a ∈ Finset.univ.filter (fun a => l ∈ rootCells P (blockSites N (RA a))),
              β a) * F l
          ≤ ∑ l, B₂ * F l := Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_right (h2 l) (hF0 l)
        _ = B₂ * ∑ l, F l := by rw [Finset.mul_sum]
        _ ≤ B₂ * B₃ := by
          refine mul_le_mul_of_nonneg_left ?_ hB₂
          have key : ∀ K : Finset ι, (∑ l, if Polymer.IsAnimal (cellGraph P) K ∧ l ∈ K then
              (if i₀ ∈ K then ∏ _m ∈ K, q else 0) else 0) =
              if Polymer.IsAnimal (cellGraph P) K ∧ i₀ ∈ K then (K.card : ℝ) * ∏ _m ∈ K, q
              else 0 := by
            intro K
            by_cases hA : Polymer.IsAnimal (cellGraph P) K
            · by_cases hi : i₀ ∈ K
              · simp only [hA, hi, true_and, and_self, ↓reduceIte]
                rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
              · simp [hA, hi]
            · simp [hA]
          have e3 : ∑ l, F l = ∑ K ∈ animalsAt P i₀, (K.card : ℝ) * ∏ _l ∈ K, q := by
            simp only [hF, animalsAt, Finset.sum_filter]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun K _ => key K
          rw [e3]
          exact sum_animalsAt_card_prod_le hΔ hq0.le hq i₀
    calc ∑ i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i), ∑ a, b a * ω (RA a) *
          ∑ l ∈ rootCells P (blockSites N (RA a)),
            (∑ K ∈ (animalsAt P l).filter (fun K => i₀ ∈ K), ∏ _m ∈ K, q) * Pr a
        ≤ ∑ _i₀ ∈ Finset.univ.filter (fun i : ι => x ∈ PB i), B₂ * B₃ :=
          Finset.sum_le_sum fun i₀ _ => hcount i₀
      _ ≤ nb * B₂ * B₃ := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnb) (mul_nonneg hB₂ hB₃0)

end Form

section Macro

variable {d N₀ M N : ℕ} [NeZero N₀]

open Classical in
/-- **The root cells of a root**: the boxes meeting a set `R` of blocks number at most
`16^d · #cells(R)`. -/
theorem card_rootCells_le (hM : 0 < M) (R : Finset (L1Torus d N₀)) :
    (rootCells (blockPatch N (macBoxF d N₀ M)) (blockSites N R)).card ≤
      16 ^ d * macCellCount d N₀ M R := by
  have hsub : rootCells (blockPatch N (macBoxF d N₀ M)) (blockSites N R) ⊆
      (R.image (macZ (d := d) M)).biUnion fun z => Finset.univ.filter fun w : MacIdx d N₀ M =>
        ∃ p, p ∈ macBox d N₀ M w ∧ p ∈ macBox d N₀ M z := by
    intro i hi
    obtain ⟨p, hpP, hpR⟩ := mem_rootCells.1 hi
    have hp1 : p.1 ∈ macBox d N₀ M i := mem_macBoxF.1 hpP
    refine Finset.mem_biUnion.2 ⟨macZ M p.1, Finset.mem_image_of_mem _ hpR, ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, p.1, hp1,
      macCore_subset_box _ hM (mem_macCore_macZ p.1)⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  unfold macCellCount
  rw [mul_comm]
  refine (Finset.sum_le_sum fun z _ => macTags_near_card hM z).trans (le_of_eq ?_)
  rw [Finset.sum_const, smul_eq_mul]

end Macro

end Balaban.Green
