/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkHalo
public import Balaban.Green.BallSums
import Mathlib.Tactic.Linarith

/-!
# `KF0FRBall`: the `ℓ¹` balls of the torus are nearest-neighbour connected

`torusBall x r = {y : |x - y|₁ ≤ r}` is connected for the nearest-neighbour adjacency
(`nnConnected_torusBall`): from any `y` of the ball, one step towards `x` along a coordinate in
which `y` differs from `x` lowers the distance to `x` by at least one and stays in the ball.
-/

@[expose] public section

namespace Balaban.LargeField.KF0FR

open Balaban.Green

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The closed `ℓ¹` ball of the torus. -/
noncomputable def torusBall (x : Torus d ℓ) (r : ℝ) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun y => torusDist d ℓ x y ≤ r

theorem mem_torusBall {x y : Torus d ℓ} {r : ℝ} : y ∈ torusBall x r ↔ torusDist d ℓ x y ≤ r := by
  simp [torusBall]

/-- The `ℓ¹` distance as a natural number. -/
def distN (x y : Torus d ℓ) : ℕ := ∑ μ, (cycRep (x μ - y μ)).natAbs

omit [NeZero ℓ] in
theorem torusDist_eq_distN (x y : Torus d ℓ) : torusDist d ℓ x y = (distN x y : ℝ) := by
  simp [torusDist, distN]

/-- **A step towards the center** lowers the distance by at least one. -/
theorem exists_step_toward {x y : Torus d ℓ} (hxy : y ≠ x) :
    ∃ (μ : Fin d) (y' : Torus d ℓ), (y' = y + Pi.single μ 1 ∨ y = y' + Pi.single μ 1) ∧
      distN x y' + 1 ≤ distN x y := by
  have : ∃ μ, cycRep (x μ - y μ) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hxy
    funext μ
    have h := cycRep_injective (m := ℓ) ((hall μ).trans (by
      have : cycRep (0 : ZMod ℓ) = 0 := by
        have := natAbs_cycRep_zero (m := ℓ); omega
      exact this.symm))
    exact (sub_eq_zero.1 h).symm
  obtain ⟨μ, hμ⟩ := this
  set c := cycRep (x μ - y μ) with hc
  set e : ℤ := if 0 < c then 1 else -1 with he
  set y' : Torus d ℓ := y + ((e : ℤ) : ZMod ℓ) • (Pi.single μ 1 : Torus d ℓ) with hy'
  have hcoord : ∀ ν, x ν - y' ν = if ν = μ then (((c - e : ℤ)) : ZMod ℓ) else x ν - y ν := by
    intro ν
    by_cases hν : ν = μ
    · subst hν
      simp only [hy', Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        ite_true]
      rw [Int.cast_sub, hc, cast_cycRep]; ring
    · simp [hy', hν]
  refine ⟨μ, y', ?_, ?_⟩
  · by_cases hc0 : 0 < c
    · left; simp [hy', he, hc0]
    · right
      simp only [hy', he, hc0, ite_false]
      ext ν
      by_cases hν : ν = μ
      · subst hν; simp
      · simp [Pi.single_eq_of_ne hν]
  · unfold distN
    have hμterm : (cycRep (x μ - y' μ)).natAbs + 1 ≤ (cycRep (x μ - y μ)).natAbs := by
      have h1 := natAbs_cycRep_le_of_cast (x μ - y' μ) (c - e) (by rw [hcoord μ, ite_eq_left rfl])
      have h2 : (c - e).natAbs + 1 = c.natAbs := by
        rw [he]; split_ifs with h0 <;> omega
      rw [hc] at h2
      omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ μ)]
    have hrest : ∑ ν ∈ Finset.univ.erase μ, (cycRep (x ν - y' ν)).natAbs =
        ∑ ν ∈ Finset.univ.erase μ, (cycRep (x ν - y ν)).natAbs :=
      Finset.sum_congr rfl fun ν hν => by
        rw [hcoord ν, ite_eq_right (Finset.ne_of_mem_erase hν)]
    rw [hrest]
    omega

/-- **The `ℓ¹` balls are nearest-neighbour connected.** -/
theorem nnConnected_torusBall (x : Torus d ℓ) (r : ℝ) : NNConnected (torusBall x r) := by
  have hreach : ∀ n : ℕ, ∀ y, distN x y ≤ n → y ∈ torusBall x r →
      Relation.ReflTransGen (NNAdjIn (torusBall x r)) y x := by
    intro n
    induction n with
    | zero =>
      intro y hy _
      have : y = x := by
        by_contra hne
        obtain ⟨μ, y', -, hlt⟩ := exists_step_toward hne
        omega
      rw [this]
    | succ n ih =>
      intro y hy hyB
      by_cases hne : y = x
      · rw [hne]
      · obtain ⟨μ, y', hstep, hlt⟩ := exists_step_toward hne
        have hy'B : y' ∈ torusBall x r := by
          rw [mem_torusBall, torusDist_eq_distN] at hyB ⊢
          have : (distN x y' : ℝ) ≤ distN x y := by exact_mod_cast (by omega : distN x y' ≤ distN x y)
          linarith
        refine Relation.ReflTransGen.head ⟨hyB, hy'B, μ, hstep⟩ (ih y' (by omega) hy'B)
  have hsymm : ∀ a b, NNAdjIn (torusBall x r) a b → NNAdjIn (torusBall x r) b a := by
    rintro a b ⟨ha, hb, μ, h | h⟩
    · exact ⟨hb, ha, μ, Or.inr h⟩
    · exact ⟨hb, ha, μ, Or.inl h⟩
  have hsym : ∀ p q, Relation.ReflTransGen (NNAdjIn (torusBall x r)) p q →
      Relation.ReflTransGen (NNAdjIn (torusBall x r)) q p := by
    intro p q h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih
  intro a ha b hb
  exact (hreach _ a le_rfl ha).trans (hsym _ _ (hreach _ b le_rfl hb))

end Balaban.LargeField.KF0FR
