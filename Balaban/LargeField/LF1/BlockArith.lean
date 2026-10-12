/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Lattice.Blocks
public import Balaban.Green.BallSums
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Block arithmetic on `ZMod ℓ` and on the torus (helper for LF-1)

For `ℓ = N * m`: the block coordinate `blockCoord N m` of a shifted site (`blockCoord_add_natCast`),
the shift by one block (`blockMap_add_side`), the position of `x + t e_μ` for `0 ≤ t ≤ N`
(`blockMap_add_natCast_cases`), the cyclic distance of sites in the same or in adjacent blocks
(`natAbs_cycRep_sub_le_two_mul`, `torusDist_le_of_adjacent`), and the bonds that stay inside a
block (`blockMap_add_single_of_mod`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Finset

section Coord

variable {ℓ N m : ℕ}

theorem pos_right_of_eq [NeZero ℓ] (hℓ : ℓ = N * m) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · exact absurd (by simp [hℓ, h]) (NeZero.ne ℓ)
  · exact h

theorem pos_left_of_eq [NeZero ℓ] (hℓ : ℓ = N * m) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exact absurd (by simp [hℓ, h]) (NeZero.ne ℓ)
  · exact h

/-- The block coordinate of the site `N k + r` (`r < N`) is `k`. -/
theorem blockCoord_natCast [NeZero ℓ] (hℓ : ℓ = N * m) (k r : ℕ) (hr : r < N) :
    blockCoord N m ((N * k + r : ℕ) : ZMod ℓ) = (k : ZMod m) := by
  have hm := pos_right_of_eq hℓ
  have hN := pos_left_of_eq hℓ
  unfold blockCoord
  rw [ZMod.val_natCast, hℓ]
  have h1 : N * k + r = N * m * (k / m) + (N * (k % m) + r) := by
    have := Nat.div_add_mod k m
    calc N * k + r = N * (m * (k / m) + k % m) + r := by rw [this]
      _ = _ := by ring
  have h2 : N * (k % m) + r < N * m := by
    have : k % m < m := Nat.mod_lt _ hm
    nlinarith
  have h3 : (N * k + r) % (N * m) = N * (k % m) + r := by
    rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
  rw [h3, Nat.mul_add_div hN, Nat.div_eq_of_lt hr, add_zero, ZMod.natCast_mod]

theorem val_eq_mul_add (a : ZMod ℓ) [NeZero ℓ] :
    a = ((N * (a.val / N) + a.val % N : ℕ) : ZMod ℓ) := by
  rw [Nat.div_add_mod, ZMod.natCast_zmod_val]

/-- The block coordinate of `a + t`: shifted by `(a.val % N + t) / N` blocks. -/
theorem blockCoord_add_natCast [NeZero ℓ] (hℓ : ℓ = N * m) (a : ZMod ℓ) (t : ℕ) :
    blockCoord N m (a + (t : ZMod ℓ)) =
      blockCoord N m a + (((a.val % N + t) / N : ℕ) : ZMod m) := by
  have hN := pos_left_of_eq hℓ
  set u := a.val / N with hu
  set r := a.val % N with hr
  have hrN : r < N := Nat.mod_lt _ hN
  have ha : a = ((N * u + r : ℕ) : ZMod ℓ) := val_eq_mul_add a
  have hbc : blockCoord N m a = (u : ZMod m) := by
    rw [ha, blockCoord_natCast hℓ u r hrN]
  have hnat : N * u + r + t = N * (u + (r + t) / N) + (r + t) % N := by
    have := Nat.div_add_mod (r + t) N
    nlinarith
  have hs : a + (t : ZMod ℓ) = ((N * (u + (r + t) / N) + (r + t) % N : ℕ) : ZMod ℓ) := by
    calc a + (t : ZMod ℓ) = ((N * u + r : ℕ) : ZMod ℓ) + (t : ZMod ℓ) := by rw [← ha]
      _ = ((N * u + r + t : ℕ) : ZMod ℓ) := by push_cast; ring
      _ = _ := by rw [hnat]
  rw [hs, blockCoord_natCast hℓ _ _ (Nat.mod_lt _ hN), hbc]
  push_cast; rfl

theorem blockCoord_add_natCast_of_lt [NeZero ℓ] (hℓ : ℓ = N * m) (a : ZMod ℓ) {t : ℕ}
    (h : a.val % N + t < N) : blockCoord N m (a + (t : ZMod ℓ)) = blockCoord N m a := by
  rw [blockCoord_add_natCast hℓ, Nat.div_eq_of_lt h]; simp

theorem blockCoord_add_side [NeZero ℓ] (hℓ : ℓ = N * m) (a : ZMod ℓ) :
    blockCoord N m (a + (N : ZMod ℓ)) = blockCoord N m a + 1 := by
  have hN := pos_left_of_eq hℓ
  rw [blockCoord_add_natCast hℓ, Nat.add_div_right _ hN, Nat.div_eq_of_lt (Nat.mod_lt _ hN)]
  simp

theorem blockCoord_sub_side [NeZero ℓ] (hℓ : ℓ = N * m) (a : ZMod ℓ) :
    blockCoord N m (a - (N : ZMod ℓ)) = blockCoord N m a - 1 := by
  have := blockCoord_add_side hℓ (a - (N : ZMod ℓ))
  rw [sub_add_cancel] at this
  rw [this]; ring

/-- A shift by `0 ≤ t ≤ N` moves by at most one block. -/
theorem blockCoord_add_natCast_cases [NeZero ℓ] (hℓ : ℓ = N * m) (a : ZMod ℓ) {t : ℕ}
    (ht : t ≤ N) : blockCoord N m (a + (t : ZMod ℓ)) = blockCoord N m a ∨
      blockCoord N m (a + (t : ZMod ℓ)) = blockCoord N m a + 1 := by
  have hN := pos_left_of_eq hℓ
  have hrN : a.val % N < N := Nat.mod_lt _ hN
  have hc : (a.val % N + t) / N ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hN]; omega
  rw [blockCoord_add_natCast hℓ]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-- Sites in the same block are at cyclic distance `< N`. -/
theorem natAbs_cycRep_sub_lt [NeZero ℓ] (hℓ : ℓ = N * m) {a a' : ZMod ℓ}
    (h : blockCoord N m a = blockCoord N m a') : (Green.cycRep (a - a')).natAbs < N := by
  have hN := pos_left_of_eq hℓ
  have hm := pos_right_of_eq hℓ
  have : NeZero m := ⟨hm.ne'⟩
  have hu : a.val / N = a'.val / N := by
    have := congrArg ZMod.val h
    rwa [blockCoord_val hℓ, blockCoord_val hℓ] at this
  have h1 := val_eq_mul_add (N := N) a
  have h2 := val_eq_mul_add (N := N) a'
  rw [hu] at h1
  set u := a'.val / N
  set r := a.val % N with hr
  set r' := a'.val % N with hr'
  have e : a - a' = (((r : ℕ) : ℤ) - ((r' : ℕ) : ℤ) : ℤ) := by
    calc a - a' = ((N * u + r : ℕ) : ZMod ℓ) - ((N * u + r' : ℕ) : ZMod ℓ) := by rw [← h1, ← h2]
      _ = _ := by push_cast; ring
  have := Green.natAbs_cycRep_le_of_cast (a - a') _ e.symm
  have h3 : r < N := Nat.mod_lt _ hN
  have h4 : r' < N := Nat.mod_lt _ hN
  omega

theorem natAbs_cycRep_natCast_le [NeZero ℓ] (t : ℕ) :
    (Green.cycRep (t : ZMod ℓ)).natAbs ≤ t :=
  Green.natAbs_cycRep_le_of_cast _ (t : ℤ) (by simp) |>.trans (by simp)

/-- Sites in the same or in adjacent blocks are at cyclic distance `≤ 2 N`. -/
theorem natAbs_cycRep_sub_le_two_mul [NeZero ℓ] (hℓ : ℓ = N * m) {a a' : ZMod ℓ}
    (h : blockCoord N m a = blockCoord N m a' ∨ blockCoord N m a' = blockCoord N m a + 1 ∨
      blockCoord N m a = blockCoord N m a' + 1) : (Green.cycRep (a - a')).natAbs ≤ 2 * N := by
  have hN := pos_left_of_eq hℓ
  have hm := pos_right_of_eq hℓ
  have : NeZero m := ⟨hm.ne'⟩
  -- the case `a'` one block after `a`
  have key : ∀ {a a' : ZMod ℓ}, blockCoord N m a' = blockCoord N m a + 1 →
      (Green.cycRep (a - a')).natAbs ≤ 2 * N := by
    intro a a' h1
    have h2 : blockCoord N m (a' - (N : ZMod ℓ)) = blockCoord N m a := by
      rw [blockCoord_sub_side hℓ, h1]; ring
    have h3 := natAbs_cycRep_sub_lt hℓ h2.symm
    have e : a - a' = (a - (a' - (N : ZMod ℓ))) + (-(N : ZMod ℓ)) := by ring
    rw [e]
    refine (Green.natAbs_cycRep_add_le _ _).trans ?_
    rw [Green.natAbs_cycRep_neg]
    have h4 := natAbs_cycRep_natCast_le (ℓ := ℓ) N
    omega
  rcases h with h | h | h
  · have := natAbs_cycRep_sub_lt hℓ h; omega
  · exact key h
  · have := key h
    rw [← neg_sub, Green.natAbs_cycRep_neg] at this
    exact this

/-- A bond that stays inside a block does not change the block coordinate. -/
theorem blockCoord_add_one_of_mod [NeZero ℓ] (hℓ : ℓ = N * m) (a : ZMod ℓ)
    (h : a.val % N + 1 < N) : blockCoord N m (a + 1) = blockCoord N m a := by
  have := blockCoord_add_natCast_of_lt hℓ a (t := 1) h
  simpa using this

end Coord

section Torus

variable {d ℓ N m : ℕ}

theorem blockMap_add_single_natCast [NeZero ℓ] (hℓ : ℓ = N * m) (x : Torus d ℓ) (μ : Fin d)
    (t : ℕ) : blockMap N m (x + Pi.single μ (t : ZMod ℓ)) =
      blockMap N m x + Pi.single μ ((((x μ).val % N + t) / N : ℕ) : ZMod m) := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [blockMap, blockCoord_add_natCast hℓ]
  · simp [blockMap, h]

/-- Shifting by one block side shifts the block by one. -/
theorem blockMap_add_single_side [NeZero ℓ] (hℓ : ℓ = N * m) (x : Torus d ℓ) (μ : Fin d) :
    blockMap N m (x + Pi.single μ (N : ZMod ℓ)) = blockMap N m x + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [blockMap, blockCoord_add_side hℓ]
  · simp [blockMap, h]

theorem blockMap_sub_single_side [NeZero ℓ] (hℓ : ℓ = N * m) (x : Torus d ℓ) (μ : Fin d) :
    blockMap N m (x - Pi.single μ (N : ZMod ℓ)) = blockMap N m x - Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h
    simp [blockMap, blockCoord_sub_side hℓ]
  · simp [blockMap, h]

/-- A shift by `0 ≤ t ≤ N` stays in the block or moves to the next one. -/
theorem blockMap_add_single_cases [NeZero ℓ] (hℓ : ℓ = N * m) (x : Torus d ℓ) (μ : Fin d)
    {t : ℕ} (ht : t ≤ N) : blockMap N m (x + Pi.single μ (t : ZMod ℓ)) = blockMap N m x ∨
      blockMap N m (x + Pi.single μ (t : ZMod ℓ)) = blockMap N m x + Pi.single μ 1 := by
  rcases blockCoord_add_natCast_cases hℓ (x μ) ht with h | h
  · left
    funext i
    by_cases hi : i = μ
    · subst hi; simpa [blockMap] using h
    · simp [blockMap, hi]
  · right
    funext i
    by_cases hi : i = μ
    · subst hi; simpa [blockMap] using h
    · simp [blockMap, hi]

/-- A bond `x → x + e_μ` that stays inside a block (`(x μ).val % N + 1 < N`). -/
theorem blockMap_add_single_one_of_mod [NeZero ℓ] (hℓ : ℓ = N * m) (x : Torus d ℓ) (μ : Fin d)
    (h : (x μ).val % N + 1 < N) : blockMap N m (x + Pi.single μ 1) = blockMap N m x := by
  funext i
  by_cases hi : i = μ
  · subst hi; simpa [blockMap] using blockCoord_add_one_of_mod hℓ (x i) h
  · simp [blockMap, hi]

/-- Sites in adjacent (or equal) blocks are at `ℓ¹` distance `≤ 2 d N`. -/
theorem torusDist_le_of_blocks [NeZero ℓ] (hℓ : ℓ = N * m) {x z : Torus d ℓ}
    (h : ∀ i, blockMap N m x i = blockMap N m z i ∨
      blockMap N m z i = blockMap N m x i + 1 ∨ blockMap N m x i = blockMap N m z i + 1) :
    Green.torusDist d ℓ x z ≤ 2 * d * N := by
  have hm := pos_right_of_eq hℓ
  have : NeZero m := ⟨hm.ne'⟩
  unfold Green.torusDist
  have : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      (((Green.cycRep (x i - z i)).natAbs : ℕ) : ℝ) ≤ 2 * N := by
    intro i _
    exact_mod_cast natAbs_cycRep_sub_le_two_mul hℓ (h i)
  calc _ ≤ ∑ _i : Fin d, (2 * (N : ℝ)) := Finset.sum_le_sum this
    _ = 2 * d * N := by simp; ring

/-- Two blocks differing by `±e_μ`: all coordinates are equal or differ by `±1`. -/
theorem coord_cases_of_single {d m : ℕ} (b : Torus d m) (μ : Fin d) {σ : ZMod m}
    (hσ : σ = 1 ∨ σ = -1) (i : Fin d) :
    b i = (b + (Pi.single μ σ : Torus d m)) i ∨ (b + (Pi.single μ σ : Torus d m)) i = b i + 1 ∨
      b i = (b + (Pi.single μ σ : Torus d m)) i + 1 := by
  by_cases h : i = μ
  · subst h
    rcases hσ with rfl | rfl
    · right; left; simp
    · right; right; simp
  · left; simp [Pi.single_eq_of_ne h]

end Torus

end Balaban.LargeField
