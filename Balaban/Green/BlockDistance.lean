/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BallSums
public import Balaban.Lattice.Blocks
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Block maps and the `ℓ¹` torus distance

Elementary facts about the block map `Balaban.blockMap N m : Torus d ℓ → Torus d m`
(`ℓ = N * m`) and the `ℓ¹` torus distance `Balaban.Green.torusDist`, used to compare the fine
distance (in units of the block side `N`) with the coarse distance:

* `Balaban.blockMap_eq_iff_val`: two sites lie in the same block iff `val / N` agree coordinatewise
  (independent of the number `m` of blocks);
* `Balaban.exists_blockMap_eq`: every block is nonempty;
* `Balaban.Green.torusDist_coarse_le`: for sites `z, z'` of the blocks `y, y'`,
  `dist_coarse y y' ≤ dist_fine z z' / N + d`;
* `Balaban.Green.torusDist_le_of_blockMap_eq`: sites in the same block are at distance `≤ d N`.
-/

@[expose] public section

namespace Balaban

open Finset

variable {d ℓ N m : ℕ}

/-- Two sites lie in the same `N`-block iff `val / N` agree coordinatewise. -/
theorem blockMap_eq_iff_val [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (x x' : Torus d ℓ) :
    blockMap N m x = blockMap N m x' ↔ ∀ i, (x i).val / N = (x' i).val / N := by
  constructor
  · intro h i
    have h1 := congrFun h i
    rw [blockMap_apply, blockMap_apply] at h1
    have h2 := congrArg ZMod.val h1
    rwa [blockCoord_val hℓ, blockCoord_val hℓ] at h2
  · intro h
    funext i
    rw [blockMap_apply, blockMap_apply]
    apply ZMod.val_injective
    rw [blockCoord_val hℓ, blockCoord_val hℓ]
    exact h i

/-- The block map does not depend on the (propositionally equal) number of blocks. -/
theorem blockMap_eq_iff_of_sides [NeZero ℓ] {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂]
    (h₁ : ℓ = N * m₁) (h₂ : ℓ = N * m₂) (x x' : Torus d ℓ) :
    blockMap N m₁ x = blockMap N m₁ x' ↔ blockMap N m₂ x = blockMap N m₂ x' := by
  rw [blockMap_eq_iff_val h₁, blockMap_eq_iff_val h₂]

/-- Every block is nonempty: the block map is surjective. -/
theorem exists_blockMap_eq [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (y : Torus d m) :
    ∃ z : Torus d ℓ, blockMap N m z = y := by
  have hc : 0 < (blockFibre N m y : Finset (Torus d ℓ)).card := by
    rw [card_blockFibre hℓ]; positivity
  obtain ⟨z, hz⟩ := Finset.card_pos.1 hc
  exact ⟨z, mem_blockFibre.1 hz⟩

namespace Green

/-- Integer arithmetic behind the comparison of distances. -/
theorem abs_mul_le_of_decomp {n κ r r' N : ℤ} (h : κ = N * n + (r - r'))
    (hr0 : 0 ≤ r) (hr : r < N) (hr' : 0 ≤ r') (hr'' : r' < N) : |n| * N ≤ |κ| + N := by
  have h1 := le_abs_self κ
  have h2 := neg_abs_le κ
  rcases le_total 0 n with hn | hn
  · rw [abs_of_nonneg hn]
    nlinarith
  · rw [abs_of_nonpos hn]
    nlinarith

variable [NeZero ℓ] [NeZero m]

/-- One coordinate: the coarse cyclic distance is at most the fine one over `N`, plus one. -/
theorem natAbs_cycRep_blockCoord_le (hℓ : ℓ = N * m) (hN : 0 < N) (a a' : ZMod ℓ) :
    ((cycRep (blockCoord N m a - blockCoord N m a')).natAbs : ℝ) ≤
      ((cycRep (a - a')).natAbs : ℝ) / N + 1 := by
  set κ : ℤ := cycRep (a - a') with hκ
  have hκc : ((κ : ℤ) : ZMod ℓ) = a - a' := cast_cycRep _
  have hdvd : (ℓ : ℤ) ∣ κ - ((a.val : ℤ) - (a'.val : ℤ)) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hκc, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  obtain ⟨t, ht⟩ := hdvd
  set bv := a.val / N with hbv
  set bv' := a'.val / N with hbv'
  set r := a.val % N with hr
  set r' := a'.val % N with hr'
  have ha : a.val = N * bv + r := (Nat.div_add_mod a.val N).symm
  have ha' : a'.val = N * bv' + r' := (Nat.div_add_mod a'.val N).symm
  set n : ℤ := ((bv : ℤ) - bv') + m * t with hn
  have hrN : r < N := Nat.mod_lt _ hN
  have hdec : κ = (N : ℤ) * n + ((r : ℤ) - r') := by
    have e1 : (ℓ : ℤ) = N * m := by exact_mod_cast hℓ
    have e2 : (a.val : ℤ) = N * bv + r := by exact_mod_cast ha
    have e3 : (a'.val : ℤ) = N * bv' + r' := by exact_mod_cast ha'
    rw [e1] at ht
    rw [hn]
    linear_combination ht + e2 - e3
  have hcast : ((n : ℤ) : ZMod m) = blockCoord N m a - blockCoord N m a' := by
    rw [hn]
    push_cast
    simp [blockCoord, hbv, hbv']
  have hle := natAbs_cycRep_le_of_cast (blockCoord N m a - blockCoord N m a') n hcast
  have hint := abs_mul_le_of_decomp (N := (N : ℤ)) hdec
    (by positivity) (by exact_mod_cast hrN) (by positivity) (by exact_mod_cast Nat.mod_lt _ hN)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hreal : ((n.natAbs : ℕ) : ℝ) * N ≤ (κ.natAbs : ℝ) + N := by
    have : ((|n| * N : ℤ) : ℝ) ≤ ((|κ| + N : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at this
    simpa [Int.cast_abs, Nat.cast_natAbs] using this
  have h3 : ((cycRep (blockCoord N m a - blockCoord N m a')).natAbs : ℝ) ≤ n.natAbs := by
    exact_mod_cast hle
  rw [← sub_nonneg]
  have : (κ.natAbs : ℝ) / N + 1 - (n.natAbs : ℝ) = ((κ.natAbs : ℝ) + N - n.natAbs * N) / N := by
    field_simp
  have h4 : 0 ≤ ((κ.natAbs : ℝ) / N + 1) - n.natAbs := by
    rw [this]; apply div_nonneg _ hN'.le; linarith
  linarith

/-- For sites `z, z'` of the blocks `y, y'`, the coarse distance is at most the fine distance
divided by the block side, plus `d`. -/
theorem torusDist_coarse_le (hℓ : ℓ = N * m) (hN : 0 < N) {z z' : Torus d ℓ} {y y' : Torus d m}
    (hz : blockMap N m z = y) (hz' : blockMap N m z' = y') :
    torusDist d m y y' ≤ torusDist d ℓ z z' / N + d := by
  subst hz hz'
  unfold torusDist
  have h1 : (d : ℝ) = ∑ _i : Fin d, (1 : ℝ) := by simp
  have h2 : (∑ i, ((cycRep (z i - z' i)).natAbs : ℝ)) / N =
      ∑ i, ((cycRep (z i - z' i)).natAbs : ℝ) / N := Finset.sum_div _ _ _
  rw [h2, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  exact natAbs_cycRep_blockCoord_le hℓ hN _ _

/-- Sites of one block are at `ℓ¹` distance at most `d N`. -/
theorem torusDist_le_of_blockMap_eq (hℓ : ℓ = N * m) (hN : 0 < N) {x x' : Torus d ℓ}
    (h : blockMap N m x = blockMap N m x') : torusDist d ℓ x x' ≤ d * N := by
  have hv := (blockMap_eq_iff_val hℓ x x').1 h
  unfold torusDist
  have : (d : ℝ) * N = ∑ _i : Fin d, (N : ℝ) := by simp
  rw [this]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := natAbs_cycRep_le_of_cast (x i - x' i) ((x i).val - (x' i).val : ℤ) (by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have h2 := hv i
  have h3 : ((x i).val - (x' i).val : ℤ).natAbs ≤ N := by
    have a1 := Nat.div_add_mod (x i).val N
    have a2 := Nat.div_add_mod (x' i).val N
    have a3 := Nat.mod_lt (x i).val hN
    have a4 := Nat.mod_lt (x' i).val hN
    rw [h2] at a1
    omega
  exact_mod_cast h1.trans h3

end Green

end Balaban
