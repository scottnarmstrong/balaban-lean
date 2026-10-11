/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.C1Star
public import Balaban.Correlations.Consequences

/-!
# Limits along the tori with side divisible by `q^n`

`LimAlong q f A` (defined in `C1Star.lean`) is the convergence `f ℓ → A` through the tori `ℓ`
with `q ^ n ∣ ℓ`, `n → ∞`.  This file develops its algebra (uniqueness, sums, products with
constants, eventual equality, bounds passing to the limit) and Step A of CORRELATIONS.md §3: the
limits of `blockM, blockGtr, blockGlg` (Theorem 4.1) from the clauses of Root-F, and the first
bullet of Root-C from them.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

namespace LimAlong

variable {q : ℕ} {f g : (ℓ : ℕ) → [NeZero ℓ] → ℝ} {A B c : ℝ}

theorem unique (hq : 2 ≤ q) (hA : LimAlong q f A) (hB : LimAlong q f B) : A = B := by
  by_contra hne
  have hpos : 0 < |A - B| / 2 := by
    have : A - B ≠ 0 := sub_ne_zero.2 hne
    positivity
  obtain ⟨n0, h0⟩ := hA _ hpos
  obtain ⟨n1, h1⟩ := hB _ hpos
  have : NeZero (q ^ (max n0 n1)) := ⟨(pow_pos (by omega) _).ne'⟩
  have e0 := h0 (q ^ max n0 n1) (pow_dvd_pow q (le_max_left _ _))
  have e1 := h1 (q ^ max n0 n1) (pow_dvd_pow q (le_max_right _ _))
  have : |A - B| < |A - B| := by
    calc |A - B| = |(f (q ^ max n0 n1) - B) - (f (q ^ max n0 n1) - A)| := by ring_nf
      _ ≤ |f (q ^ max n0 n1) - B| + |f (q ^ max n0 n1) - A| := abs_sub _ _
      _ < |A - B| / 2 + |A - B| / 2 := add_lt_add e1 e0
      _ = |A - B| := by ring
  exact lt_irrefl _ this

/-- A bound valid on all large tori passes to the limit. -/
theorem abs_sub_le (hq : 2 ≤ q) (hA : LimAlong q f A)
    (hb : ∃ n₁ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₁ ∣ ℓ → |f ℓ - c| ≤ B) : |A - c| ≤ B := by
  obtain ⟨n₁, hn₁⟩ := hb
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n₀, hn₀⟩ := hA ε hε
  have : NeZero (q ^ (max n₀ n₁)) := ⟨(pow_pos (by omega) _).ne'⟩
  have e0 := hn₀ (q ^ max n₀ n₁) (pow_dvd_pow q (le_max_left _ _))
  have e1 := hn₁ (q ^ max n₀ n₁) (pow_dvd_pow q (le_max_right _ _))
  calc |A - c| = |(f (q ^ max n₀ n₁) - c) - (f (q ^ max n₀ n₁) - A)| := by ring_nf
    _ ≤ |f (q ^ max n₀ n₁) - c| + |f (q ^ max n₀ n₁) - A| := abs_sub _ _
    _ < B + ε := add_lt_add_of_le_of_lt e1 e0

theorem congr (h : ∃ n₁ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₁ ∣ ℓ → f ℓ = g ℓ)
    (hf : LimAlong q f A) : LimAlong q g A := by
  obtain ⟨n₁, hn₁⟩ := h
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hf ε hε
  refine ⟨max n₀ n₁, fun ℓ _ hd => ?_⟩
  rw [← hn₁ ℓ (dvd_trans (pow_dvd_pow q (le_max_right _ _)) hd)]
  exact hn₀ ℓ (dvd_trans (pow_dvd_pow q (le_max_left _ _)) hd)

theorem const (c : ℝ) : LimAlong q (fun _ _ => c) c := fun ε hε => ⟨0, fun _ _ _ => by simpa using hε⟩

theorem add (hf : LimAlong q f A) (hg : LimAlong q g B) :
    LimAlong q (fun ℓ _ => f ℓ + g ℓ) (A + B) := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hf (ε / 2) (by positivity)
  obtain ⟨n₁, hn₁⟩ := hg (ε / 2) (by positivity)
  refine ⟨max n₀ n₁, fun ℓ _ hd => ?_⟩
  have e0 := hn₀ ℓ (dvd_trans (pow_dvd_pow q (le_max_left _ _)) hd)
  have e1 := hn₁ ℓ (dvd_trans (pow_dvd_pow q (le_max_right _ _)) hd)
  calc |f ℓ + g ℓ - (A + B)| = |(f ℓ - A) + (g ℓ - B)| := by ring_nf
    _ ≤ |f ℓ - A| + |g ℓ - B| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e0 e1
    _ = ε := by ring

theorem const_mul (c : ℝ) (hf : LimAlong q f A) : LimAlong q (fun ℓ _ => c * f ℓ) (c * A) := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := hf (ε / (|c| + 1)) (by positivity)
  refine ⟨n₀, fun ℓ _ hd => ?_⟩
  have e0 := hn₀ ℓ hd
  have hc : 0 < |c| + 1 := by positivity
  calc |c * f ℓ - c * A| = |c| * |f ℓ - A| := by rw [← mul_sub, abs_mul]
    _ ≤ (|c| + 1) * |f ℓ - A| := by
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (|c| + 1) * (ε / (|c| + 1)) := mul_lt_mul_of_pos_left e0 hc
    _ = ε := by field_simp

theorem sum {ι : Type*} (s : Finset ι) {F : ι → (ℓ : ℕ) → [NeZero ℓ] → ℝ} {a : ι → ℝ}
    (hF : ∀ i ∈ s, LimAlong q (F i) (a i)) :
    LimAlong q (fun ℓ _ => ∑ i ∈ s, F i ℓ) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const 0 : LimAlong q (fun _ _ => (0 : ℝ)) 0)
  | insert i s hi ih =>
    have h1 := hF i (Finset.mem_insert_self _ _)
    have h2 := ih fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have := h1.add h2
    rw [Finset.sum_insert hi]
    refine (congr ⟨0, fun ℓ _ _ => ?_⟩ this)
    rw [Finset.sum_insert hi]

end LimAlong

variable {d N : ℕ}

theorem embedZ_zero (ℓ : ℕ) : embedZ ℓ (0 : Fin d → ℤ) = 0 := by
  funext μ
  simp [embedZ]

theorem embedZ_sub (ℓ : ℕ) (x y : Fin d → ℤ) : embedZ ℓ x - embedZ ℓ y = embedZ ℓ (x - y) := by
  funext μ
  simp [embedZ]

/-- Step A (Theorem 4.1): the limits of the three scalars of Lemma 0.2 along the tori with side
divisible by `(M L)^n`. -/
theorem exists_limits {L M kf : ℕ} {β ν δ : ℝ} {T : RootFFamily d N} (hN : 2 ≤ N)
    (hcl : RootFClauses d N L M β ν (EuclideanSpace.single (idx₀ hN) 1) kf (kappaStar d) 1 δ T)
    (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hM : 1 ≤ M) :
    ∃ m : ℝ, ∃ Gtr Glg : (Fin d → ℤ) → ℝ,
      LimAlong (M * L) (fun ℓ _ => blockM d N ℓ hN β ν) m ∧
      (∀ z, LimAlong (M * L) (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ z)) (Gtr z)) ∧
      (∀ z, LimAlong (M * L) (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ z)) (Glg z)) := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨m, hm⟩ := onePoint_tendsto_along_multiples hcl hd hδ hL hM (by norm_num) le_rfl
    (0 : Fin d → ℤ) (idx₀ hN)
  have h2 : ∀ (i : Fin N) z, ∃ G : ℝ, ∀ ε > 0, ∃ n0 : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ],
      (M * L) ^ n0 ∣ ℓ → |twoPointTruncated d N ℓ β ν (EuclideanSpace.single (idx₀ hN) 1)
        (embedZ ℓ z) (embedZ ℓ 0) i i - G| < ε := fun i z =>
    twoPoint_tendsto_along_multiples hcl hd hδ hL hM (by norm_num) le_rfl z 0 i i
  choose Gtr hGtr using fun z => h2 (idx₁ hN) z
  choose Glg hGlg using fun z => h2 (idx₀ hN) z
  refine ⟨m, Gtr, Glg, ?_, ?_, ?_⟩
  · intro ε hε
    obtain ⟨n0, hn0⟩ := hm ε hε
    refine ⟨n0, fun ℓ _ hdv => ?_⟩
    have := hn0 ℓ hdv
    simpa [blockM, embedZ_zero] using this
  · intro z ε hε
    obtain ⟨n0, hn0⟩ := hGtr z ε hε
    refine ⟨n0, fun ℓ _ hdv => ?_⟩
    have := hn0 ℓ hdv
    simpa [blockGtr, embedZ_zero] using this
  · intro z ε hε
    obtain ⟨n0, hn0⟩ := hGlg z ε hε
    refine ⟨n0, fun ℓ _ hdv => ?_⟩
    have := hn0 ℓ hdv
    simpa [blockGlg, embedZ_zero] using this

theorem sum_sq_eq_one {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) : ∑ j, h j ^ 2 = 1 := by
  have := EuclideanSpace.norm_eq h
  rw [hh] at this
  have h0 : 0 ≤ ∑ j, ‖h j‖ ^ 2 := by positivity
  have h1 := (Real.sqrt_eq_one).1 this.symm
  simpa using h1

theorem sq_le_one {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (i : Fin N) : h i ^ 2 ≤ 1 := by
  rw [← sum_sq_eq_one hh]
  exact Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem abs_le_one_of_norm {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (i : Fin N) :
    |h i| ≤ 1 := by
  have := sq_le_one hh i
  nlinarith [abs_nonneg (h i), sq_abs (h i)]

theorem abs_mul_le_one {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (i k : Fin N) :
    |h i * h k| ≤ 1 := by
  rw [abs_mul]
  calc |h i| * |h k| ≤ 1 * 1 :=
        mul_le_mul (abs_le_one_of_norm hh i) (abs_le_one_of_norm hh k) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem abs_delta_sub_le_one {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (i k : Fin N) :
    |(if i = k then (1 : ℝ) else 0) - h i * h k| ≤ 1 := by
  by_cases hik : i = k
  · subst hik
    have := sq_le_one hh i
    simp only [↓reduceIte, abs_le]
    constructor <;> nlinarith [sq_nonneg (h i)]
  · simp only [hik, ↓reduceIte, zero_sub, abs_neg]
    exact abs_mul_le_one hh i k

/-- The first bullet of Root-C from the limits of the three scalars (Lemma 0.2 (c)). -/
theorem bullet_one (hN : 2 ≤ N) {q : ℕ} {β ν m : ℝ} {Gtr Glg : (Fin d → ℤ) → ℝ}
    (hm : LimAlong q (fun ℓ _ => blockM d N ℓ hN β ν) m)
    (hGtr : ∀ z, LimAlong q (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ z)) (Gtr z))
    (hGlg : ∀ z, LimAlong q (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ z)) (Glg z))
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) (x y : Fin d → ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₀ ∣ ℓ →
      (∀ i, |onePoint d N ℓ β ν h (fun μ => (x μ : ZMod ℓ)) i - m * h i| < ε) ∧
      ∀ i k, |twoPointTruncated d N ℓ β ν h (fun μ => (x μ : ZMod ℓ))
          (fun μ => (y μ : ZMod ℓ)) i k
        - (Gtr (x - y) * ((if i = k then 1 else 0) - h i * h k)
            + Glg (x - y) * (h i * h k))| < ε := by
  obtain ⟨n0, h0⟩ := hm (ε / 2) (by positivity)
  obtain ⟨n1, h1⟩ := hGtr (x - y) (ε / 2) (by positivity)
  obtain ⟨n2, h2⟩ := hGlg (x - y) (ε / 2) (by positivity)
  refine ⟨max n0 (max n1 n2), fun ℓ _ hd => ?_⟩
  have e0 := h0 ℓ (dvd_trans (pow_dvd_pow q (le_max_left _ _)) hd)
  have e1 := h1 ℓ (dvd_trans (pow_dvd_pow q ((le_max_left _ _).trans (le_max_right _ _))) hd)
  have e2 := h2 ℓ (dvd_trans (pow_dvd_pow q ((le_max_right _ _).trans (le_max_right _ _))) hd)
  refine ⟨fun i => ?_, fun i k => ?_⟩
  · have h1 : onePoint d N ℓ β ν h (fun μ => (x μ : ZMod ℓ)) i = blockM d N ℓ hN β ν * h i :=
      onePoint_eq_blockM_mul hN β ν h hh _ i
    rw [h1, ← sub_mul, abs_mul]
    calc |blockM d N ℓ hN β ν - m| * |h i| ≤ |blockM d N ℓ hN β ν - m| * 1 :=
          mul_le_mul_of_nonneg_left (abs_le_one_of_norm hh i) (abs_nonneg _)
      _ < ε := by rw [mul_one]; linarith
  · have h1 : twoPointTruncated d N ℓ β ν h (fun μ => (x μ : ZMod ℓ))
        (fun μ => (y μ : ZMod ℓ)) i k =
        blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)) * ((if i = k then 1 else 0) - h i * h k)
          + blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)) * (h i * h k) := by
      have := twoPointTruncated_eq_block hN β ν h hh (embedZ ℓ x) (embedZ ℓ y) i k
      rw [embedZ_sub] at this
      exact this
    rw [h1]
    have hA := abs_delta_sub_le_one hh i k
    have hB := abs_mul_le_one hh i k
    calc _ = |(blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)) - Gtr (x - y)) *
            ((if i = k then (1 : ℝ) else 0) - h i * h k) +
          (blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)) - Glg (x - y)) * (h i * h k)| := by
          ring_nf
      _ ≤ |(blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)) - Gtr (x - y)) *
            ((if i = k then (1 : ℝ) else 0) - h i * h k)| +
          |(blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)) - Glg (x - y)) * (h i * h k)| :=
          abs_add_le _ _
      _ ≤ |blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)) - Gtr (x - y)| * 1 +
          |blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)) - Glg (x - y)| * 1 := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
      _ < ε := by rw [mul_one, mul_one]; linarith

end Balaban.Correlations
