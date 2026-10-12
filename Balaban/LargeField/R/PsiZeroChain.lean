/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ZeroDomainRef

/-!
# Paths from a box to its layer

From every block of a box one reaches the layer `shellOut` of the box in at most `s₀` neighbour steps along the
first coordinate, so a field with increments `≤ κ` along neighbouring blocks changes by at most `s₀ κ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Chain

variable {d m : ℕ} [NeZero m]

theorem supDist_add_single_le (y : Torus d m) (μ : Fin d) : supDist (y + Pi.single μ 1) y ≤ 1 := by
  rw [supDist_le_iff]
  intro i
  rw [cycNorm_le_iff]
  refine ⟨if i = μ then 1 else 0, ?_, ?_⟩
  · split_ifs <;> simp
  · by_cases h : i = μ
    · subst h; simp
    · simp [h]

/-- From a point of a box one reaches the layer of the box in at most `s₀` neighbour steps along the
first coordinate. -/
theorem box_chain {E : Type*} [SeminormedAddCommGroup E] (hd : 0 < d) (a : Torus d m) (s : Fin d → ℕ)
    (hs : ∀ i, s i + 2 ≤ m) (f : Torus d m → E) {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ y y', (y ∈ box a s ∨ y ∈ shellOut (box a s)) → (y' ∈ box a s ∨ y' ∈ shellOut (box a s)) →
      torusAdj y y' → ‖f y - f y'‖ ≤ κ) :
    ∀ n : ℕ, ∀ y ∈ box a s, ∀ j : ℕ, j < s ⟨0, hd⟩ → y ⟨0, hd⟩ = a ⟨0, hd⟩ + (j : ZMod m) →
      s ⟨0, hd⟩ - j ≤ n + 1 → ∃ z' ∈ shellOut (box a s), ‖f y - f z'‖ ≤ (n + 1) * κ := by
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  intro n
  induction n with
  | zero =>
    intro y hy j hj hyj hle
    have hjs : j + 1 = s i0 := by omega
    have hy'box : y + Pi.single i0 1 ∉ box a s := by
      intro hb
      obtain ⟨j', hj', hjj⟩ := hb i0
      have e1 : a i0 + (j : ZMod m) + 1 = a i0 + (j' : ZMod m) := by
        simpa [hyj] using hjj
      have e2 : (s i0 : ZMod m) = (j' : ZMod m) := by
        have : ((j + 1 : ℕ) : ZMod m) = (j' : ZMod m) := by
          push_cast; linear_combination e1
        rwa [hjs] at this
      rw [ZMod.natCast_eq_natCast_iff'] at e2
      have := hs i0
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e2
      omega
    refine ⟨y + Pi.single i0 1, ⟨hy'box, y, hy, supDist_add_single_le y i0⟩, ?_⟩
    have := hκ y (y + Pi.single i0 1) (Or.inl hy) (Or.inr ⟨hy'box, y, hy, supDist_add_single_le y i0⟩)
      ⟨i0, Or.inl rfl⟩
    simpa using this
  | succ n ih =>
    intro y hy j hj hyj hle
    by_cases hj1 : j + 1 < s i0
    · have hy' : y + Pi.single i0 1 ∈ box a s := by
        intro i
        by_cases hi : i = i0
        · subst hi
          exact ⟨j + 1, hj1, by simp [hyj]; ring⟩
        · obtain ⟨j', hj', hjj⟩ := hy i
          exact ⟨j', hj', by simpa [Pi.single_eq_of_ne hi] using hjj⟩
      obtain ⟨z', hz', hb⟩ := ih (y + Pi.single i0 1) hy' (j + 1) hj1 (by simp [hyj]; ring)
        (by omega)
      refine ⟨z', hz', ?_⟩
      have h1 := hκ y (y + Pi.single i0 1) (Or.inl hy) (Or.inl hy') ⟨i0, Or.inl rfl⟩
      calc ‖f y - f z'‖ = ‖(f y - f (y + Pi.single i0 1)) + (f (y + Pi.single i0 1) - f z')‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖f y - f (y + Pi.single i0 1)‖ + ‖f (y + Pi.single i0 1) - f z'‖ := norm_add_le _ _
        _ ≤ κ + (n + 1) * κ := add_le_add h1 hb
        _ = ((n + 1 : ℕ) + 1) * κ := by push_cast; ring
    · have hjs : j + 1 = s i0 := by omega
      have := ih y hy j hj hyj (by omega)
      obtain ⟨z', hz', hb⟩ := this
      refine ⟨z', hz', hb.trans ?_⟩
      push_cast
      nlinarith

end Chain

end Balaban.LargeField
