/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Lattice.BlockAverage
public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr

/-!
# Block Poincaré inequality on the torus

Item 1 of brief W2b; GREEN.md Lemma 4.1. Fields are real functions on `Torus d ℓ`
(`ℓ = N * m`, blocks of side `N` as in `Balaban/Lattice/Blocks.lean`), with unit lattice spacing
(the scaling `η = 1/N` of GREEN.md is restored in `Balaban/Green/Coercivity.lean`).

Main results:
* `Balaban.blockPoincare`: with `P = Q* Q = blockProjection N m`,
  `∑ₓ (φ x - (P φ) x)² ≤ (d / 2) N² · innerEnergy N φ`, where `innerEnergy N φ` is the energy of the
  bonds `x → x + e_μ` that stay inside a block (the bond is counted iff
  `(x μ).val % N + 1 < N`);
* `Balaban.blockPoincare_latticeEnergy`: the same with the full Dirichlet energy
  `latticeEnergy φ = ∑ₓ ∑_μ (φ(x + e_μ) - φ x)²`.

The constant `d / 2` (instead of the sharp `1/8` per direction of GREEN.md Lemma 4.1) comes from the
following elementary proof, which avoids Fourier analysis and the Efron–Stein inequality: the
variance is half the normalised pair sum `pairSum`, the one-dimensional pair sum is bounded by
Cauchy–Schwarz along the path between two points (`pairSum_le_oneD`), and the step
`d → d + 1` splits `f(a, y) - f(b, y') = (f(a, y) - f(b, y)) + (f(b, y) - f(b, y'))` with the weights
`(d + 1, (d + 1) / d)` (`pairSum_succ_le`), giving `pairSum ≤ d N^{d+2} innerEnergy` (`pairSum_le`).
-/

@[expose] public section

namespace Balaban

open Finset

section OneD

variable {ℓ N m : ℕ} [NeZero ℓ]

/-- The squared bond difference at `c`, counted only when the bond `c → c+1` stays inside a
block of side `N`. -/
noncomputable def innerGap (N : ℕ) (g : ZMod ℓ → ℝ) (c : ZMod ℓ) : ℝ :=
  if c.val % N + 1 < N then (g (c + 1) - g c) ^ 2 else 0

omit [NeZero ℓ] in
theorem innerGap_nonneg (N : ℕ) (g : ZMod ℓ → ℝ) (c : ZMod ℓ) : 0 ≤ innerGap N g c := by
  unfold innerGap; split_ifs <;> positivity

omit [NeZero ℓ] in
theorem ite_innerGap_nonneg (p : Prop) [Decidable p] (N : ℕ) (g : ZMod ℓ → ℝ) (c : ZMod ℓ) :
    0 ≤ if p then innerGap N g c else 0 := by
  split_ifs
  · exact innerGap_nonneg N g c
  · exact le_rfl

theorem nat_mod_succ_lt_of_div_eq {N n n' : ℕ} (hN : 0 < N) (hn : n < n')
    (hd : n / N = n' / N) : n % N + 1 < N := by
  have h1 : (n + 1) / N = n / N := by
    have a1 : n / N ≤ (n + 1) / N := Nat.div_le_div_right (by omega)
    have a2 : (n + 1) / N ≤ n' / N := Nat.div_le_div_right (by omega)
    omega
  rw [Nat.succ_div] at h1
  have := Nat.mod_lt n hN
  by_contra hc
  have hdvd : N ∣ n + 1 := by
    refine ⟨n / N + 1, ?_⟩
    have e := Nat.div_add_mod n N
    have : n % N + 1 = N := by omega
    nlinarith
  simp [hdvd] at h1

theorem sq_diff_le_aux [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (g : ZMod ℓ → ℝ) (a b : ZMod ℓ)
    (hab : a.val ≤ b.val) (hd : a.val / N = b.val / N) :
    (g a - g b) ^ 2 ≤ N * ∑ c, if blockCoord N m c = blockCoord N m a then innerGap N g c else 0 := by
  obtain ⟨k, hk⟩ : ∃ k, b.val = a.val + k := ⟨b.val - a.val, by omega⟩
  have hbl : b.val < ℓ := ZMod.val_lt b
  set cc : ℕ → ZMod ℓ := fun i => ((a.val + i : ℕ) : ZMod ℓ) with hcc
  have hval : ∀ i, i ≤ k → (cc i).val = a.val + i := fun i hi => by
    simp only [hcc]; exact ZMod.val_natCast_of_lt (by omega)
  have hb : g b = g (cc k) := by
    simp only [hcc]; rw [← hk, ZMod.natCast_zmod_val]
  have ha : g a = g (cc 0) := by simp [hcc]
  have htel : g b - g a = ∑ i ∈ range k, (g (cc (i + 1)) - g (cc i)) := by
    rw [Finset.sum_range_sub (fun i => g (cc i)), hb, ha]
  have hstep : ∀ i ∈ range k, (g (cc (i + 1)) - g (cc i)) ^ 2 =
      if blockCoord N m (cc i) = blockCoord N m a then innerGap N g (cc i) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hv := hval i hi.le
    have hdi : (cc i).val / N = a.val / N := by
      rw [hv]
      have l1 : a.val / N ≤ (a.val + i) / N := Nat.div_le_div_right (by omega)
      have l2 : (a.val + i) / N ≤ b.val / N := Nat.div_le_div_right (by omega)
      omega
    have hbc : blockCoord N m (cc i) = blockCoord N m a := by
      apply ZMod.val_injective
      rw [blockCoord_val hℓ, blockCoord_val hℓ, hdi]
    have hlt : (cc i).val % N + 1 < N :=
      nat_mod_succ_lt_of_div_eq hN (by omega : (cc i).val < b.val) (by rw [hdi, hd])
    have hcc1 : cc i + 1 = cc (i + 1) := by
      simp only [hcc]; push_cast; ring
    simp only [innerGap, hbc, hlt, hcc1, ↓reduceIte]
  have hcs := sq_sum_le_card_mul_sum_sq (s := range k) (f := fun i => g (cc (i + 1)) - g (cc i))
  rw [← htel, Finset.card_range, Finset.sum_congr rfl hstep] at hcs
  have hinj : Set.InjOn cc (range k : Finset ℕ) := by
    intro i hi j hj hij
    have h1 := hval i (Finset.mem_range.1 (Finset.mem_coe.1 hi)).le
    have h2 := hval j (Finset.mem_range.1 (Finset.mem_coe.1 hj)).le
    have := congrArg ZMod.val hij
    omega
  have hsub : ∑ i ∈ range k, (if blockCoord N m (cc i) = blockCoord N m a then innerGap N g (cc i) else 0)
      ≤ ∑ c, if blockCoord N m c = blockCoord N m a then innerGap N g c else 0 := by
    rw [← Finset.sum_image (f := fun c => if blockCoord N m c = blockCoord N m a then innerGap N g c else 0) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => ite_innerGap_nonneg _ N g c)
  have hkN : (k : ℝ) ≤ N := by
    have : k < N := by
      by_contra hc
      have e1 := Nat.div_add_mod a.val N
      have e2 := Nat.div_add_mod b.val N
      have hm := Nat.mod_lt a.val hN
      have hm2 := Nat.mod_lt b.val hN
      rw [← hd] at e2
      omega
    exact_mod_cast this.le
  have hS : 0 ≤ ∑ c, if blockCoord N m c = blockCoord N m a then innerGap N g c else 0 :=
    Finset.sum_nonneg fun c _ => ite_innerGap_nonneg _ N g c
  have hnn : 0 ≤ ∑ i ∈ range k, (if blockCoord N m (cc i) = blockCoord N m a then
      innerGap N g (cc i) else 0) := Finset.sum_nonneg fun i _ => ite_innerGap_nonneg _ N g _
  have h2 := mul_le_mul hkN hsub hnn (Nat.cast_nonneg N)
  have h3 : (g a - g b) ^ 2 = (g b - g a) ^ 2 := by ring
  linarith

theorem sum_ite_blockCoord_eq [NeZero m] (hℓ : ℓ = N * m) (y : ZMod m) (K : ℝ) :
    (∑ a : ZMod ℓ, if blockCoord N m a = y then K else 0) = N * K := by
  rw [← Finset.sum_filter, Finset.sum_const, card_blockCoord_fibre hℓ, nsmul_eq_mul]

theorem sq_diff_le [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (g : ZMod ℓ → ℝ) (a b : ZMod ℓ)
    (hab : blockCoord N m a = blockCoord N m b) :
    (g a - g b) ^ 2 ≤ N * ∑ c, if blockCoord N m c = blockCoord N m a then innerGap N g c else 0 := by
  have hd : a.val / N = b.val / N := by
    have := congrArg ZMod.val hab
    rwa [blockCoord_val hℓ, blockCoord_val hℓ] at this
  rcases le_total a.val b.val with h | h
  · exact sq_diff_le_aux hℓ hN g a b h hd
  · have := sq_diff_le_aux hℓ hN g b a h hd.symm
    rw [← hab] at this
    calc (g a - g b) ^ 2 = (g b - g a) ^ 2 := by ring
      _ ≤ _ := this

/-- One-dimensional Poincaré inequality for the pair sum over blocks of side `N`:
`∑_{a ~ b} (g a - g b)² ≤ N³ ∑_{bonds inside blocks} (g(c+1) - g c)²`. -/
theorem pairSum_le_oneD [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (g : ZMod ℓ → ℝ) :
    (∑ a, ∑ b, if blockCoord N m a = blockCoord N m b then (g a - g b) ^ 2 else 0) ≤
      (N : ℝ) ^ 3 * ∑ c, innerGap N g c := by
  set Gb : ZMod ℓ → ℝ := fun a => ∑ c, if blockCoord N m c = blockCoord N m a then innerGap N g c else 0
    with hGb
  have hA : ∀ a b : ZMod ℓ, (if blockCoord N m a = blockCoord N m b then (g a - g b) ^ 2 else 0) ≤
      if blockCoord N m b = blockCoord N m a then N * Gb a else 0 := by
    intro a b
    by_cases h : blockCoord N m a = blockCoord N m b
    · simp only [h, ↓reduceIte]
      exact sq_diff_le hℓ hN g a b h
    · have h' : ¬ blockCoord N m b = blockCoord N m a := fun e => h e.symm
      simp [h, h']
  calc (∑ a, ∑ b, if blockCoord N m a = blockCoord N m b then (g a - g b) ^ 2 else 0)
      ≤ ∑ a, ∑ b : ZMod ℓ, (if blockCoord N m b = blockCoord N m a then (N : ℝ) * Gb a else 0) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hA a b
    _ = ∑ a, (N : ℝ) * ((N : ℝ) * Gb a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact sum_ite_blockCoord_eq hℓ _ _
    _ = (N : ℝ) ^ 2 * ∑ a, Gb a := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
    _ = (N : ℝ) ^ 2 * ((N : ℝ) * ∑ c, innerGap N g c) := by
        congr 1
        simp only [hGb]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        have := sum_ite_blockCoord_eq (N := N) (m := m) hℓ (blockCoord N m c) (innerGap N g c)
        simpa [eq_comm] using this
    _ = _ := by ring

end OneD

section Cube

variable {ℓ N m : ℕ} [NeZero ℓ]

theorem sum_pi_succ {α : Type*} [Fintype α] {d : ℕ} (F : (Fin (d + 1) → α) → ℝ) :
    ∑ x, F x = ∑ a : α, ∑ y : Fin d → α, F (Fin.cons a y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d + 1) => α)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Same-block relation on `(Fin d → ZMod ℓ)`: all coordinates lie in the same block of side `N`. -/
def SameBlock (N m : ℕ) {d : ℕ} (x x' : Fin d → ZMod ℓ) : Prop :=
  ∀ i, blockCoord N m (x i) = blockCoord N m (x' i)

instance {d : ℕ} (x x' : Fin d → ZMod ℓ) : Decidable (SameBlock N m x x') := by
  unfold SameBlock; infer_instance

/-- The pair sum `∑_{x ~ x'} (f x - f x')²` over all pairs in a common block. -/
noncomputable def pairSum (N m : ℕ) {d : ℕ} (f : (Fin d → ZMod ℓ) → ℝ) : ℝ :=
  ∑ x, ∑ x', if SameBlock N m x x' then (f x - f x') ^ 2 else 0

/-- The energy of the bonds `x → x + e_μ` that stay inside a block of side `N`. -/
noncomputable def innerEnergy (N : ℕ) {d : ℕ} (f : (Fin d → ZMod ℓ) → ℝ) : ℝ :=
  ∑ x, ∑ μ : Fin d, if (x μ).val % N + 1 < N then
    (f (Function.update x μ (x μ + 1)) - f x) ^ 2 else 0

theorem innerEnergy_succ {d : ℕ} (f : (Fin (d + 1) → ZMod ℓ) → ℝ) :
    innerEnergy N f = (∑ y : Fin d → ZMod ℓ, ∑ c : ZMod ℓ,
        innerGap N (fun a => f (Fin.cons a y)) c) +
      ∑ a : ZMod ℓ, innerEnergy N (fun y : Fin d → ZMod ℓ => f (Fin.cons a y)) := by
  unfold innerEnergy
  rw [sum_pi_succ]
  simp only [Fin.sum_univ_succ, Finset.sum_add_distrib, Fin.cons_zero, Fin.cons_succ,
    Fin.update_cons_zero, ← Fin.cons_update]
  congr 1
  · rw [Finset.sum_comm]; rfl

theorem filter_sameBlock {d : ℕ} (y : Fin d → ZMod ℓ) :
    (Finset.univ.filter fun y' : Fin d → ZMod ℓ => SameBlock N m y y') =
      blockFibre N m (blockMap N m y) := by
  refine Finset.ext fun y' => ?_
  rw [Finset.mem_filter, mem_blockFibre]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · funext i; exact (h.2 i).symm
  · exact ⟨Finset.mem_univ _, fun i => (congrFun h i).symm⟩

theorem sum_ite_sameBlock {d : ℕ} [NeZero m] (hℓ : ℓ = N * m) (y : Fin d → ZMod ℓ) (K : ℝ) :
    (∑ y' : Fin d → ZMod ℓ, if SameBlock N m y y' then K else 0) = (N : ℝ) ^ d * K := by
  rw [← Finset.sum_filter, filter_sameBlock, Finset.sum_const, card_blockFibre hℓ, nsmul_eq_mul]
  simp

omit [NeZero ℓ] in
theorem sameBlock_cons {d : ℕ} (a b : ZMod ℓ) (y y' : Fin d → ZMod ℓ) :
    SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') ↔
      blockCoord N m a = blockCoord N m b ∧ SameBlock N m y y' := by
  simp [SameBlock, Fin.forall_fin_succ]

theorem sq_add_le_aux (d : ℕ) (p q : ℝ) (hq : q = 0 ∨ 0 < d) :
    (p + q) ^ 2 ≤ ((d : ℝ) + 1) * p ^ 2 + (((d : ℝ) + 1) / d) * q ^ 2 := by
  rcases hq with h | h
  · subst h
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [sq_nonneg p]
  · have hd : (0 : ℝ) < d := by exact_mod_cast h
    have key : 0 ≤ (q - d * p) ^ 2 := sq_nonneg _
    have : (p + q) ^ 2 * d ≤ (((d : ℝ) + 1) * p ^ 2) * d + ((d : ℝ) + 1) * q ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, ← sub_nonneg]
    have h2 : ((d : ℝ) + 1) * p ^ 2 + (((d : ℝ) + 1) * q ^ 2) / d - (p + q) ^ 2 =
        (((d : ℝ) + 1) * p ^ 2 * d + ((d : ℝ) + 1) * q ^ 2 - (p + q) ^ 2 * d) / d := by
      field_simp
    rw [h2]
    exact div_nonneg (by linarith) hd.le

theorem pairSum_zero (f : (Fin 0 → ZMod ℓ) → ℝ) : pairSum N m f = 0 := by
  unfold pairSum
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun x' _ => ?_
  rw [Subsingleton.elim x' x]
  simp

theorem pairSum_succ_le {d : ℕ} [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (H : ∀ f : (Fin d → ZMod ℓ) → ℝ, pairSum N m f ≤ d * (N : ℝ) ^ (d + 2) * innerEnergy N f)
    (f : (Fin (d + 1) → ZMod ℓ) → ℝ) :
    pairSum N m f ≤ ((d : ℝ) + 1) * (N : ℝ) ^ (d + 1 + 2) * innerEnergy N f := by
  set K : ℝ := ((d : ℝ) + 1) / d with hK
  have hK0 : 0 ≤ K := by positivity
  have hpt : ∀ (a b : ZMod ℓ) (y y' : Fin d → ZMod ℓ),
      (if SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') then
        (f (Fin.cons a y) - f (Fin.cons b y')) ^ 2 else 0) ≤
      ((d : ℝ) + 1) * (if SameBlock N m y y' then
          (if blockCoord N m a = blockCoord N m b then (f (Fin.cons a y) - f (Fin.cons b y)) ^ 2
            else 0) else 0) +
        K * (if blockCoord N m a = blockCoord N m b then
          (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0) else 0) := by
    intro a b y y'
    by_cases hA : blockCoord N m a = blockCoord N m b
    · by_cases hB : SameBlock N m y y'
      · have hc : SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') :=
          (sameBlock_cons a b y y').2 ⟨hA, hB⟩
        simp only [hc, hA, hB, ↓reduceIte]
        have hq : f (Fin.cons b y) - f (Fin.cons b y') = 0 ∨ 0 < d := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · subst h0
            left
            rw [Subsingleton.elim y y']; simp
          · exact Or.inr h0
        have := sq_add_le_aux d (f (Fin.cons a y) - f (Fin.cons b y))
          (f (Fin.cons b y) - f (Fin.cons b y')) hq
        have e : f (Fin.cons a y) - f (Fin.cons b y) + (f (Fin.cons b y) - f (Fin.cons b y')) =
            f (Fin.cons a y) - f (Fin.cons b y') := by ring
        rw [e] at this
        exact this
      · have hc : ¬ SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') :=
          fun h => hB ((sameBlock_cons a b y y').1 h).2
        simp only [hc, hB, hA, ↓reduceIte, mul_zero, add_zero, le_refl]
    · have hc : ¬ SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') :=
        fun h => hA ((sameBlock_cons a b y y').1 h).1
      simp only [hc, hA, ↓reduceIte, ite_self, mul_zero, add_zero, le_refl]
  have hsplit : pairSum N m f = ∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b : ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
      (if SameBlock N m (Fin.cons a y : Fin (d + 1) → ZMod ℓ) (Fin.cons b y') then
        (f (Fin.cons a y) - f (Fin.cons b y')) ^ 2 else 0) := by
    unfold pairSum
    simp only [sum_pi_succ]
  have T1 : (∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b : ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
      (if SameBlock N m y y' then
          (if blockCoord N m a = blockCoord N m b then (f (Fin.cons a y) - f (Fin.cons b y)) ^ 2
            else 0) else 0)) ≤
      (N : ℝ) ^ d * ((N : ℝ) ^ 3 * ∑ y : Fin d → ZMod ℓ, ∑ c : ZMod ℓ,
        innerGap N (fun a => f (Fin.cons a y)) c) := by
    calc _ = ∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b,
          (N : ℝ) ^ d * (if blockCoord N m a = blockCoord N m b then
            (f (Fin.cons a y) - f (Fin.cons b y)) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun b _ => sum_ite_sameBlock hℓ y _
      _ = (N : ℝ) ^ d * ∑ y : Fin d → ZMod ℓ, ∑ a : ZMod ℓ, ∑ b : ZMod ℓ,
          (if blockCoord N m a = blockCoord N m b then
            (f (Fin.cons a y) - f (Fin.cons b y)) ^ 2 else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
      _ ≤ (N : ℝ) ^ d * ∑ y : Fin d → ZMod ℓ, ((N : ℝ) ^ 3 * ∑ c : ZMod ℓ,
          innerGap N (fun a => f (Fin.cons a y)) c) := by
          gcongr with y
          exact pairSum_le_oneD hℓ hN (fun a => f (Fin.cons a y))
      _ = _ := by rw [← Finset.mul_sum]
  have T2 : (∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b : ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
      (if blockCoord N m a = blockCoord N m b then
          (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0) else 0)) ≤
      (N : ℝ) * ∑ b : ZMod ℓ, (d : ℝ) * (N : ℝ) ^ (d + 2) * innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) := by
    calc _ = ∑ b : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ, ∑ a : ZMod ℓ,
          (if blockCoord N m a = blockCoord N m b then
          (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0) else 0) := by
          calc _ = ∑ a : ZMod ℓ, ∑ b : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
                (if blockCoord N m a = blockCoord N m b then
                (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0)
                  else 0) :=
                Finset.sum_congr rfl fun a _ => Finset.sum_comm
            _ = ∑ b : ZMod ℓ, ∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
                (if blockCoord N m a = blockCoord N m b then
                (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0)
                  else 0) := Finset.sum_comm
            _ = _ := Finset.sum_congr rfl fun b _ => by
                rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ b : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
          (N : ℝ) * (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2
            else 0) :=
          Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun y' _ => by
              have := sum_ite_blockCoord_eq (N := N) (m := m) hℓ (blockCoord N m b)
                (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0)
              simpa using this
      _ = (N : ℝ) * ∑ b : ZMod ℓ, pairSum N m (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) := by
          unfold pairSum
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr with b
          exact H _
  have hS1 : 0 ≤ ∑ y : Fin d → ZMod ℓ, ∑ c : ZMod ℓ, innerGap N (fun a => f (Fin.cons a y)) c :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun c _ => innerGap_nonneg _ _ _
  have hE : 0 ≤ ∑ b : ZMod ℓ, innerEnergy N (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) :=
    Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => by
      split_ifs <;> positivity
  have hKd : K * d ≤ (d : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; simp
    · have : (d : ℝ) ≠ 0 := by positivity
      rw [hK, div_mul_cancel₀ _ this]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ b : ZMod ℓ, (d : ℝ) * (N : ℝ) ^ (d + 2) * innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) =
      (d : ℝ) * (N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) := by rw [Finset.mul_sum]
  have hmain : pairSum N m f ≤ ((d : ℝ) + 1) * ((N : ℝ) ^ d * ((N : ℝ) ^ 3 * ∑ y : Fin d → ZMod ℓ,
        ∑ c : ZMod ℓ, innerGap N (fun a => f (Fin.cons a y)) c)) +
      K * ((N : ℝ) * ((d : ℝ) * (N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)))) := by
    rw [hsplit]
    calc _ ≤ ∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b : ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
          (((d : ℝ) + 1) * (if SameBlock N m y y' then
          (if blockCoord N m a = blockCoord N m b then (f (Fin.cons a y) - f (Fin.cons b y)) ^ 2
            else 0) else 0) +
          K * (if blockCoord N m a = blockCoord N m b then
          (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0) else 0)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun b _ =>
            Finset.sum_le_sum fun y' _ => hpt a b y y'
      _ = ((d : ℝ) + 1) * (∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b : ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
          (if SameBlock N m y y' then
          (if blockCoord N m a = blockCoord N m b then (f (Fin.cons a y) - f (Fin.cons b y)) ^ 2
            else 0) else 0)) + K * (∑ a : ZMod ℓ, ∑ y : Fin d → ZMod ℓ, ∑ b : ZMod ℓ, ∑ y' : Fin d → ZMod ℓ,
          (if blockCoord N m a = blockCoord N m b then
          (if SameBlock N m y y' then (f (Fin.cons b y) - f (Fin.cons b y')) ^ 2 else 0) else 0)) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left T1 (by positivity))
          (mul_le_mul_of_nonneg_left (T2.trans (le_of_eq (by rw [hsum]))) hK0)
  rw [innerEnergy_succ]
  have e1 : (N : ℝ) ^ (d + 1 + 2) = (N : ℝ) ^ d * (N : ℝ) ^ 3 := by ring
  have hX : 0 ≤ (N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) := by positivity
  have hY : K * (d : ℝ) * ((N : ℝ) * ((N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)))) ≤
      ((d : ℝ) + 1) * ((N : ℝ) * ((N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
        (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)))) :=
    mul_le_mul_of_nonneg_right hKd (by positivity)
  have e2 : (N : ℝ) * (N : ℝ) ^ (d + 2) = (N : ℝ) ^ d * (N : ℝ) ^ 3 := by ring
  calc pairSum N m f ≤ _ := hmain
    _ ≤ _ := by
      rw [e1]
      have e3 : K * ((N : ℝ) * ((d : ℝ) * (N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
          (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)))) = K * (d : ℝ) * ((N : ℝ) *
          ((N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
          (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)))) := by ring
      have e4 : ((d : ℝ) + 1) * ((N : ℝ) * ((N : ℝ) ^ (d + 2) * ∑ b : ZMod ℓ, innerEnergy N
          (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)))) = ((d : ℝ) + 1) * ((N : ℝ) ^ d *
          (N : ℝ) ^ 3) * ∑ b : ZMod ℓ, innerEnergy N (fun y : Fin d → ZMod ℓ => f (Fin.cons b y)) := by
        ring
      have e5 : ((d : ℝ) + 1) * ((N : ℝ) ^ d * ((N : ℝ) ^ 3 * ∑ y : Fin d → ZMod ℓ,
        ∑ c : ZMod ℓ, innerGap N (fun a => f (Fin.cons a y)) c)) = ((d : ℝ) + 1) * ((N : ℝ) ^ d *
          (N : ℝ) ^ 3) * ∑ y : Fin d → ZMod ℓ,
        ∑ c : ZMod ℓ, innerGap N (fun a => f (Fin.cons a y)) c := by ring
      rw [e3, e5]
      nlinarith [hY, e4]

theorem pairSum_le [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) :
    ∀ (d : ℕ) (f : (Fin d → ZMod ℓ) → ℝ),
      pairSum N m f ≤ (d : ℝ) * (N : ℝ) ^ (d + 2) * innerEnergy N f
  | 0, f => by rw [pairSum_zero]; simp
  | d + 1, f => by
    have := pairSum_succ_le hℓ hN (pairSum_le hℓ hN d) f
    simpa using this

section Torus

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem sum_sum_fibre (hℓ : ℓ = N * m) (g : Torus d ℓ → ℝ) :
    ∑ x : Torus d ℓ, ∑ x' ∈ blockFibre N m (blockMap N m x), g x' = (N : ℝ) ^ d * ∑ x, g x := by
  calc ∑ x : Torus d ℓ, ∑ x' ∈ blockFibre N m (blockMap N m x), g x'
      = ∑ y : Torus d m, ∑ x ∈ blockFibre N m y, ∑ x' ∈ blockFibre N m (blockMap N m x), g x' :=
        (Finset.sum_fiberwise Finset.univ (blockMap N m)
          (fun x => ∑ x' ∈ blockFibre N m (blockMap N m x), g x')).symm
    _ = ∑ y : Torus d m, ∑ x ∈ blockFibre N m y, ∑ x' ∈ blockFibre N m y, g x' := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
        rw [mem_blockFibre.mp hx]
    _ = ∑ y : Torus d m, (N : ℝ) ^ d * ∑ x' ∈ blockFibre N m y, g x' := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_const, card_blockFibre hℓ, nsmul_eq_mul]
        simp
    _ = (N : ℝ) ^ d * ∑ x, g x := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_fiberwise Finset.univ (blockMap N m) g

theorem pairSum_eq (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    pairSum N m φ = 2 * (N : ℝ) ^ d * ∑ x, (φ x - blockProjection N m φ x) ^ 2 := by
  have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
  have hP : ∀ x, ∑ x' ∈ blockFibre N m (blockMap N m x), φ x' = (N : ℝ) ^ d * blockProjection N m φ x := by
    intro x
    rw [blockProjection_apply, blockAverage_apply]
    field_simp
  have hrow : ∀ x : Torus d ℓ, (∑ x' : Torus d ℓ, if SameBlock N m x x' then (φ x - φ x') ^ 2 else 0) =
      (N : ℝ) ^ d * φ x ^ 2 - 2 * φ x * ((N : ℝ) ^ d * blockProjection N m φ x) +
        ∑ x' ∈ blockFibre N m (blockMap N m x), φ x' ^ 2 := by
    intro x
    rw [← Finset.sum_filter, filter_sameBlock]
    have : ∀ x' ∈ blockFibre N m (blockMap N m x), (φ x - φ x') ^ 2 =
        φ x ^ 2 - 2 * φ x * φ x' + φ x' ^ 2 := fun x' _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hP, Finset.sum_const, card_blockFibre hℓ, nsmul_eq_mul]
    simp
  have hsq : ∑ x, φ x * blockProjection N m φ x = ∑ x, (blockProjection N m φ x) ^ 2 := by
    have h := blockProjection_selfAdjoint (m := m) (d := d) (ℓ := ℓ) hN
      (wf := 1) (wc := (N : ℝ) ^ d * 1) (by simp) φ (blockProjection N m φ)
    rw [blockProjection_idem hℓ hN] at h
    unfold latticeInner at h
    simp only [one_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => by ring
  unfold pairSum
  rw [Finset.sum_congr rfl fun x _ => hrow x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_sum_fibre hℓ (fun x' => φ x' ^ 2)]
  have : ∀ x, (φ x - blockProjection N m φ x) ^ 2 =
      φ x ^ 2 - 2 * (φ x * blockProjection N m φ x) + (blockProjection N m φ x) ^ 2 := fun x => by ring
  rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← hsq]
  have : ∑ x, (N : ℝ) ^ d * φ x ^ 2 = (N : ℝ) ^ d * ∑ x, φ x ^ 2 := by rw [Finset.mul_sum]
  have h2 : ∑ x, 2 * φ x * ((N : ℝ) ^ d * blockProjection N m φ x) =
      2 * (N : ℝ) ^ d * ∑ x, φ x * blockProjection N m φ x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have h3 : ∑ x, 2 * (φ x * blockProjection N m φ x) = 2 * ∑ x, φ x * blockProjection N m φ x := by
    rw [Finset.mul_sum]
  rw [h2, h3]
  ring

/-- **Block Poincaré inequality on the torus.** For a field `φ` on `Torus d ℓ` and blocks of side
`N` (`ℓ = N * m`), the variance of `φ` over the blocks is controlled by the energy of the bonds
inside the blocks:
`∑ₓ (φ x - (Q* Q φ) x)² ≤ (d / 2) N² ∑ₓ ∑_μ [bond x → x + e_μ inside a block] (φ(x + e_μ) - φ x)²`.
-/
theorem blockPoincare (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    ∑ x, (φ x - blockProjection N m φ x) ^ 2 ≤ ((d : ℝ) / 2) * (N : ℝ) ^ 2 * innerEnergy N φ := by
  have h := pairSum_le hℓ hN d φ
  rw [pairSum_eq hℓ hN] at h
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have e : (d : ℝ) * (N : ℝ) ^ (d + 2) * innerEnergy N φ =
      2 * (N : ℝ) ^ d * (((d : ℝ) / 2) * (N : ℝ) ^ 2 * innerEnergy N φ) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h (by positivity)

/-- The full Dirichlet energy `∑ₓ ∑_μ (φ(x + e_μ) - φ x)²` of a field on the torus (all bonds). -/
noncomputable def latticeEnergy (φ : Torus d ℓ → ℝ) : ℝ :=
  ∑ x, ∑ μ : Fin d, (φ (x + Pi.single μ 1) - φ x) ^ 2

omit [NeZero ℓ] in
theorem update_eq_add_single (x : Torus d ℓ) (μ : Fin d) :
    Function.update x μ (x μ + 1) = x + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · simp [h]

theorem latticeEnergy_nonneg (φ : Torus d ℓ → ℝ) : 0 ≤ latticeEnergy φ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem innerEnergy_nonneg (φ : Torus d ℓ → ℝ) : 0 ≤ innerEnergy N φ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The energy of the bonds inside blocks is at most the full energy. -/
theorem innerEnergy_le_latticeEnergy (φ : Torus d ℓ → ℝ) :
    innerEnergy N φ ≤ latticeEnergy φ := by
  unfold innerEnergy latticeEnergy
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => ?_
  rw [update_eq_add_single]
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

/-- **Block Poincaré inequality, full-energy form.** -/
theorem blockPoincare_latticeEnergy (hℓ : ℓ = N * m) (hN : 0 < N) (φ : Torus d ℓ → ℝ) :
    ∑ x, (φ x - blockProjection N m φ x) ^ 2 ≤ ((d : ℝ) / 2) * (N : ℝ) ^ 2 * latticeEnergy φ :=
  (blockPoincare hℓ hN φ).trans
    (mul_le_mul_of_nonneg_left (innerEnergy_le_latticeEnergy φ) (by positivity))

end Torus

end Cube

end Balaban
