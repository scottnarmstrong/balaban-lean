module

public import Balaban.LargeField.R.ZeroDomainRef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Monotone paths inside a box of the torus (used for Lemma III.4.6)

Two points of a box `box a s` of the torus `ℤ_m^d` (`s_i ≤ m`) are joined inside the box by a path of
at most `∑_i (s_i - 1)` nearest-neighbour steps (`box_reach`): the monotone lattice path of the source
("a monotone path inside the box", P7 p. 509; "monotone lattice paths inside the block",
Lemma III.4.2 (a)).  `reach_dist_le` turns this into the bound for a function with bounded bond
differences.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section BoxReach

variable {d m : ℕ} [NeZero m] {s : Fin d → ℕ}

theorem box_val_lt {a x : Torus d m} (hs : ∀ i, s i ≤ m) (hx : x ∈ box a s) (i : Fin d) :
    (x i - a i).val < s i := by
  obtain ⟨j, hj, hxj⟩ := hx i
  have h : x i - a i = (j : ZMod m) := by rw [hxj]; ring
  rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le hj (hs i))]
  exact hj

theorem mem_box_of_val_lt {a x : Torus d m} (hx : ∀ i, (x i - a i).val < s i) :
    x ∈ box a s := by
  intro i
  refine ⟨(x i - a i).val, hx i, ?_⟩
  rw [ZMod.natCast_zmod_val]; ring

theorem eq_of_val_eq {a x y : Torus d m} (h : ∀ i, (x i - a i).val = (y i - a i).val) : x = y := by
  funext i
  have := ZMod.val_injective m (h i)
  exact sub_left_injective this

/-- The potential: the `ℓ¹`-distance of the box coordinates. -/
def boxDist (a x y : Torus d m) : ℕ :=
  ∑ i, (((x i - a i).val : ℤ) - ((y i - a i).val : ℤ)).natAbs

theorem step_up {a x : Torus d m} (hs : ∀ i, s i ≤ m) (hx : x ∈ box a s) (i : Fin d)
    (h : (x i - a i).val + 1 < s i) :
    (x + Pi.single i 1 : Torus d m) ∈ box a s ∧ (((x + Pi.single i 1 : Torus d m)) i - a i).val = (x i - a i).val + 1 ∧
      ∀ j, j ≠ i → ((x + Pi.single i 1 : Torus d m)) j = x j := by
  have hm : (x i - a i).val + 1 < m := lt_of_lt_of_le h (hs i)
  have hi : ((x + Pi.single i 1 : Torus d m)) i - a i = (((x i - a i).val + 1 : ℕ) : ZMod m) := by
    simp only [Pi.add_apply, Pi.single_eq_same, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    ring
  have hv : (((x + Pi.single i 1 : Torus d m)) i - a i).val = (x i - a i).val + 1 := by
    rw [hi, ZMod.val_natCast, Nat.mod_eq_of_lt hm]
  have hother : ∀ j, j ≠ i → ((x + Pi.single i 1 : Torus d m)) j = x j := by
    intro j hj
    simp [hj]
  refine ⟨?_, hv, hother⟩
  apply mem_box_of_val_lt
  intro j
  by_cases hj : j = i
  · subst hj; rw [hv]; exact h
  · rw [hother j hj]; exact box_val_lt hs hx j

theorem step_down {a x : Torus d m} (hs : ∀ i, s i ≤ m) (hx : x ∈ box a s) (i : Fin d)
    (h : 1 ≤ (x i - a i).val) :
    (x - Pi.single i 1 : Torus d m) ∈ box a s ∧ (((x - Pi.single i 1 : Torus d m)) i - a i).val = (x i - a i).val - 1 ∧
      ∀ j, j ≠ i → ((x - Pi.single i 1 : Torus d m)) j = x j := by
  have hlt := box_val_lt hs hx i
  have hm : (x i - a i).val - 1 < m := by
    have := hs i; omega
  have hi : ((x - Pi.single i 1 : Torus d m)) i - a i = (((x i - a i).val - 1 : ℕ) : ZMod m) := by
    simp only [Pi.sub_apply, Pi.single_eq_same]
    rw [Nat.cast_sub h, ZMod.natCast_zmod_val]
    simp
    ring
  have hv : (((x - Pi.single i 1 : Torus d m)) i - a i).val = (x i - a i).val - 1 := by
    rw [hi, ZMod.val_natCast, Nat.mod_eq_of_lt hm]
  have hother : ∀ j, j ≠ i → ((x - Pi.single i 1 : Torus d m)) j = x j := by
    intro j hj
    simp [hj]
  refine ⟨?_, hv, hother⟩
  apply mem_box_of_val_lt
  intro j
  by_cases hj : j = i
  · subst hj; rw [hv]; omega
  · rw [hother j hj]; exact box_val_lt hs hx j

theorem boxDist_le (hs : ∀ i, s i ≤ m) {a x y : Torus d m} (hx : x ∈ box a s) (hy : y ∈ box a s) :
    boxDist a x y ≤ ∑ i, (s i - 1) := by
  unfold boxDist
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := box_val_lt hs hx i
  have h2 := box_val_lt hs hy i
  omega

/-- **Monotone path in a box**: any two points of `box a s` (`s_i ≤ m`) are joined inside the box by at
most `boxDist a x y ≤ ∑ (s_i - 1)` nearest-neighbour steps. -/
theorem box_reach_aux (hs : ∀ i, s i ≤ m) {a : Torus d m} :
    ∀ T : ℕ, ∀ x y : Torus d m, x ∈ box a s → y ∈ box a s → boxDist a x y = T →
      ∃ n ≤ T, ReachIn torusAdj (box a s) x y n := by
  intro T
  induction T with
  | zero =>
    intro x y hx hy hT
    have h0 : ∀ i, (x i - a i).val = (y i - a i).val := by
      intro i
      unfold boxDist at hT
      have := (Finset.sum_eq_zero_iff.mp hT) i (Finset.mem_univ i)
      omega
    have := eq_of_val_eq h0
    subst this
    exact ⟨0, le_rfl, ReachIn.refl _ hx⟩
  | succ T ih =>
    intro x y hx hy hT
    have hex : ∃ i, (x i - a i).val ≠ (y i - a i).val := by
      by_contra hcon
      push Not at hcon
      have : boxDist a x y = 0 := by
        unfold boxDist
        exact Finset.sum_eq_zero fun i _ => by have := hcon i; omega
      omega
    obtain ⟨i, hi⟩ := hex
    have hsum : ∀ y' : Torus d m, (∀ j, j ≠ i → y' j = y j) →
        boxDist a x y' + (((x i - a i).val : ℤ) - ((y i - a i).val : ℤ)).natAbs =
          boxDist a x y + (((x i - a i).val : ℤ) - ((y' i - a i).val : ℤ)).natAbs := by
      intro y' hy'
      have e1 : boxDist a x y' = (((x i - a i).val : ℤ) - ((y' i - a i).val : ℤ)).natAbs +
          ∑ j ∈ Finset.univ.erase i, (((x j - a j).val : ℤ) - ((y' j - a j).val : ℤ)).natAbs :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have e2 : boxDist a x y = (((x i - a i).val : ℤ) - ((y i - a i).val : ℤ)).natAbs +
          ∑ j ∈ Finset.univ.erase i, (((x j - a j).val : ℤ) - ((y j - a j).val : ℤ)).natAbs :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      have e3 : ∑ j ∈ Finset.univ.erase i, (((x j - a j).val : ℤ) - ((y' j - a j).val : ℤ)).natAbs =
          ∑ j ∈ Finset.univ.erase i, (((x j - a j).val : ℤ) - ((y j - a j).val : ℤ)).natAbs := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hy' j (Finset.ne_of_mem_erase hj)]
      omega
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · -- move `y` down towards `x`
      have h1 : 1 ≤ (y i - a i).val := by omega
      obtain ⟨hy'mem, hy'v, hy'o⟩ := step_down hs hy i h1
      have hd := hsum _ hy'o
      have hxy' : boxDist a x (y - Pi.single i 1 : Torus d m) = T := by
        rw [hy'v] at hd
        omega
      obtain ⟨n, hn, hr⟩ := ih x (y - Pi.single i 1 : Torus d m) hx hy'mem hxy'
      refine ⟨n + 1, by omega, ReachIn.step hr hy ⟨i, Or.inl ?_⟩⟩
      simp
    · -- move `y` up towards `x`
      have hlt' : (y i - a i).val + 1 < s i := by
        have := box_val_lt hs hx i; omega
      obtain ⟨hy'mem, hy'v, hy'o⟩ := step_up hs hy i hlt'
      have hd := hsum _ hy'o
      have hxy' : boxDist a x (y + Pi.single i 1 : Torus d m) = T := by
        rw [hy'v] at hd
        omega
      obtain ⟨n, hn, hr⟩ := ih x (y + Pi.single i 1 : Torus d m) hx hy'mem hxy'
      refine ⟨n + 1, by omega, ReachIn.step hr hy ⟨i, Or.inr ?_⟩⟩
      simp

theorem box_reach (hs : ∀ i, s i ≤ m) {a x y : Torus d m} (hx : x ∈ box a s) (hy : y ∈ box a s) :
    ∃ n ≤ ∑ i, (s i - 1), ReachIn torusAdj (box a s) x y n := by
  obtain ⟨n, hn, hr⟩ := box_reach_aux hs (boxDist a x y) x y hx hy rfl
  exact ⟨n, hn.trans (boxDist_le hs hx hy), hr⟩

end BoxReach

section Bound

variable {α E : Type*} [PseudoMetricSpace E] {adj : α → α → Prop} {P : Set α}

/-- A function whose bond differences along `adj` inside `P` are at most `B` changes by at most `n B`
along an `n`-step path. -/
theorem reach_dist_le (f : α → E) {B : ℝ} (hB : ∀ x ∈ P, ∀ y ∈ P, adj x y → dist (f x) (f y) ≤ B)
    {z z' : α} {n : ℕ} (h : ReachIn adj P z z' n) : dist (f z) (f z') ≤ n * B := by
  induction h with
  | refl hu => simp
  | @step v w n hr hw ha ih =>
    have hv := ReachIn.mem_right hr
    calc dist (f z) (f w) ≤ dist (f z) (f v) + dist (f v) (f w) := dist_triangle _ _ _
      _ ≤ n * B + B := add_le_add ih (hB v hv w hw ha)
      _ = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring

end Bound

end Balaban.LargeField
