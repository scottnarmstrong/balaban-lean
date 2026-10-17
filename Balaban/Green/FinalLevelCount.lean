/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayCoef
public import Balaban.Green.FinalLiftDecaySum
public import Balaban.Green.FinalLogDetLocal
public import Balaban.Green.BlockDistance
public import Balaban.LargeField.R.RRemovedCapEnergy
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The read sets, the sites at each distance level and their count (blocker 5)

Counting lemmas on the torus: a ball of the `ℓ¹` distance with radius `R` has at most `(2R+1)^d`
points; a fibre of the unit-block map has at most `(L^k)^d` points;  Path distance: in a generating set with `Ω₁` the whole torus every two
sites are at path distance at most `∑_i (b_i - a_i).val`.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Localization

namespace Balaban.Green

section Count

variable {d m : ℕ} [NeZero m]

/-- A ball of the `ℓ¹` distance of radius `R` has at most `(2R+1)^d` points. -/
theorem card_torus_ball_le (t : Balaban.Torus d m) (R : ℕ) :
    (univ.filter fun w : Balaban.Torus d m => torusDist d m t w ≤ R).card ≤ (2 * R + 1) ^ d := by
  classical
  have hsub : (univ.filter fun w : Balaban.Torus d m => torusDist d m t w ≤ R) ⊆
      Fintype.piFinset (fun i => univ.filter fun v : ZMod m => (cycRep (t i - v)).natAbs ≤ R) := by
    intro w hw
    rw [Fintype.mem_piFinset]
    intro i
    have hw' := (mem_filter.1 hw).2
    have h1 : ((cycRep (t i - w i)).natAbs : ℝ) ≤ torusDist d m t w :=
      Finset.single_le_sum (f := fun i => ((cycRep (t i - w i)).natAbs : ℝ))
        (fun _ _ => Nat.cast_nonneg _) (mem_univ i)
    exact mem_filter.2 ⟨mem_univ _, by exact_mod_cast h1.trans hw'⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = ∏ i, (univ.filter fun v : ZMod m => (cycRep (t i - v)).natAbs ≤ R).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * R + 1) := Finset.prod_le_prod fun i _ => card_cyc_ball_le _ R
    _ = (2 * R + 1) ^ d := by simp

/-- The residues with a given quotient by `s` are at most `s`. -/
theorem card_val_div_le {s : ℕ} (hs : 0 < s) (c : ℕ) :
    (univ.filter fun v : ZMod m => v.val / s = c).card ≤ s := by
  classical
  have hmap : ∀ v ∈ (univ.filter fun v : ZMod m => v.val / s = c), v.val % s ∈ range s := fun v _ =>
    mem_range.2 (Nat.mod_lt _ hs)
  refine (card_le_card_of_injOn (fun v : ZMod m => v.val % s) hmap ?_).trans (by simp)
  intro v hv w hw hvw
  have hv' : v.val / s = c := by simpa using hv
  have hw' : w.val / s = c := by simpa using hw
  apply ZMod.val_injective
  have e1 := Nat.div_add_mod v.val s
  have e2 := Nat.div_add_mod w.val s
  simp only at hvw
  rw [hv'] at e1
  rw [hw'] at e2
  omega

/-- The sites of the fine torus with a given unit block: at most `(L^k)^d`. -/
theorem card_unitBlock_fiber_le {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]
    (u : UnitTorus d L N₁ m₁ k) :
    (univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => unitBlock x = u).card ≤ (L ^ k) ^ d := by
  classical
  have hs : 0 < L ^ k := pow_pos (NeZero.pos L) k
  rcases (univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => unitBlock x = u).eq_empty_or_nonempty with
    h | ⟨x0, hx0⟩
  · rw [h]; simp
  have hsub : (univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => unitBlock x = u) ⊆
      Fintype.piFinset (fun i => univ.filter fun v : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)) =>
        v.val / L ^ k = (x0 i).val / L ^ k) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    have hx' := (mem_filter.1 hx).2
    have hx0' := (mem_filter.1 hx0).2
    exact mem_filter.2 ⟨mem_univ _, (unitBlock_eq_iff x x0).1 (hx'.trans hx0'.symm) i⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = ∏ i, (univ.filter fun v : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)) =>
        v.val / L ^ k = (x0 i).val / L ^ k).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, L ^ k := Finset.prod_le_prod fun i _ => card_val_div_le hs _
    _ = (L ^ k) ^ d := by simp

end Count

section Path

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- In a generating set with `Ω₁` the whole torus, the path distance of two sites is at most the
sum of the coordinate differences (each in `[0, m)`). -/
theorem pathDist_le_sumVal (G : GeneratingSet d L N₀ k ϱ) (hΩ : G.Ω 1 = Finset.univ) :
    ∀ (n : ℕ) (a b : Balaban.Torus d (N₀ * L ^ k)), ∑ i, (b i - a i).val = n →
      G.pathDist a b ≤ ENNReal.ofReal n := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have hab : a = b := by
      funext i
      have h0 : (b i - a i).val = 0 := (Finset.sum_eq_zero_iff.1 h) i (mem_univ i)
      exact (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 h0)).symm
    subst hab
    rw [GeneratingSet.pathDist_self (hΩ ▸ mem_univ a)]
    exact bot_le
  | succ n ih =>
    intro a b h
    obtain ⟨i, hi⟩ : ∃ i, (b i - a i).val ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at h
    have hpos : 1 ≤ (b i - a i).val := Nat.one_le_iff_ne_zero.2 hi
    have hm : 1 < N₀ * L ^ k := by
      have := ZMod.val_lt (b i - a i)
      omega
    have : Fact (1 < N₀ * L ^ k) := ⟨hm⟩
    obtain ⟨a', ha'def⟩ : ∃ a' : Balaban.Torus d (N₀ * L ^ k), a' =
        a + Pi.single i (1 : ZMod (N₀ * L ^ k)) := ⟨_, rfl⟩
    have hval : ∀ j, (b j - a' j).val =
        if j = i then (b i - a i).val - 1 else (b j - a j).val := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [ha'def]
        simp only [Pi.add_apply, Pi.single_eq_same, ite_true]
        rw [show b j - (a j + 1) = (b j - a j) - 1 by ring,
          ZMod.val_sub (by rw [ZMod.val_one]; exact hpos), ZMod.val_one]
      · rw [ha'def]
        simp [hj]
    have hsum : ∑ j, (b j - a' j).val = n := by
      have h1 := Finset.add_sum_erase univ (fun j => (b j - a j).val) (mem_univ i)
      have h2 := Finset.add_sum_erase univ (fun j => (b j - a' j).val) (mem_univ i)
      have h3 : ∑ j ∈ univ.erase i, (b j - a' j).val =
          ∑ j ∈ univ.erase i, (b j - a j).val :=
        Finset.sum_congr rfl fun j hj => by rw [hval j]; simp [Finset.ne_of_mem_erase hj]
      have h4 : (b i - a' i).val = (b i - a i).val - 1 := by simpa using hval i
      omega
    have ha : a ∈ G.Ω 1 := hΩ ▸ mem_univ a
    have ha' : a' ∈ G.Ω 1 := hΩ ▸ mem_univ _
    have e1 : G.pathDist a a' ≤ ENNReal.ofReal 1 :=
      (GeneratingSet.pathDist_le_bondCost ha ha' ⟨i, Or.inl ha'def⟩).trans
        (ENNReal.ofReal_le_ofReal (G.bondCost_le_one ha _))
    calc G.pathDist a b ≤ G.pathDist a a' + G.pathDist a' b :=
          G.pathDist_triangle _ _ _
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal n := add_le_add e1 (ih _ _ hsum)
      _ = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := by
          rw [← ENNReal.ofReal_add (by norm_num) (Nat.cast_nonneg n)]
          congr 1; push_cast; ring

/-- Every two sites are at path distance at most `d (N₀ L^k)`. -/
theorem pathDist_le_dim_mul (G : GeneratingSet d L N₀ k ϱ) (hΩ : G.Ω 1 = Finset.univ)
    (a b : Balaban.Torus d (N₀ * L ^ k)) :
    G.pathDist a b ≤ ENNReal.ofReal ((d * (N₀ * L ^ k) : ℕ) : ℝ) := by
  refine (pathDist_le_sumVal G hΩ _ a b rfl).trans (ENNReal.ofReal_le_ofReal ?_)
  have : ∑ i, (b i - a i).val ≤ ∑ _i : Fin d, (N₀ * L ^ k) :=
    Finset.sum_le_sum fun i _ => (ZMod.val_lt _).le
  have h2 : ((∑ i, (b i - a i).val : ℕ) : ℝ) ≤ ((d * (N₀ * L ^ k) : ℕ) : ℝ) := by
    exact_mod_cast this.trans (by simp)
  exact h2

end Path

end Balaban.Green
