/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedCore
import Mathlib.Tactic.Linarith

/-!
# Entropy cost of coverage labels

A fixed linked cluster with activation set \`A\` produces at most \`2^|A|\` coverage labels.
The extra count is paid by the footprint decay before applying the linked gas estimate.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Coverage

variable {B T Y : Type*} [Fintype B] [Fintype T] [Fintype Y]

omit [Fintype B] [Fintype T] in
/-- If a coverage label is determined by its parent and a subset of the parent's marks,
the number of labels over one parent is at most \`2^|A|\`. -/
theorem gasLinked_coverage_fibre_count
    (parent : Y → T) (activation : Y → Finset B) (marks : T → Finset B)
    (hsub : ∀ y, activation y ⊆ marks (parent y))
    (hinj : ∀ y y', parent y = parent y' →
      activation y = activation y' → y = y')
    (t : T) :
    ((Finset.univ.filter (fun y : Y => parent y = t)).card : ℝ) ≤
      (2 : ℝ) ^ (marks t).card := by
  classical
  let s : Finset Y := Finset.univ.filter (fun y => parent y = t)
  have himg : s.image activation ⊆ (marks t).powerset := by
    intro S hS
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hS
    have hyt : parent y = t := (Finset.mem_filter.mp hy).2
    simpa only [Finset.mem_powerset, hyt] using hsub y
  have hinjOn : Set.InjOn activation (s : Set Y) := by
    intro y hy y' hy' he
    exact hinj y y' ((Finset.mem_filter.mp hy).2.trans
      ((Finset.mem_filter.mp hy').2).symm) he
  have hnat : s.card ≤ 2 ^ (marks t).card := by
    calc
      s.card = (s.image activation).card :=
        (Finset.card_image_of_injOn hinjOn).symm
      _ ≤ ((marks t).powerset).card := Finset.card_le_card himg
      _ = 2 ^ (marks t).card := Finset.card_powerset _
  exact_mod_cast hnat

/-- The factor \`2^|A|\` uses \`c₁ log 2\` units of footprint decay and leaves the
volume-independent prefactor \`exp (c₁ log 2)\`. -/
theorem gasLinked_coverage_count_exp_le (n : ℕ) (D : ℝ)
    {c1 κ κ0 : ℝ} (hD : 0 ≤ D)
    (hn : (n : ℝ) ≤ c1 * (1 + D))
    (hκ : κ0 + c1 * Real.log 2 ≤ κ) :
    (2 : ℝ) ^ n * Real.exp (-κ * D) ≤
      Real.exp (c1 * Real.log 2) * Real.exp (-κ0 * D) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpow : ((2 : ℝ) ^ n) = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right hn hlog
  have h2 := mul_le_mul_of_nonneg_right hκ hD
  nlinarith

omit [Fintype B] in
/-- Parent entropy survives the power-set expansion of coverage labels. The extra
\`2^|A|\` labels are paid by \`c₁ log 2\` of the decay rate. -/
theorem gasLinked_coverage_entropy
    (parent : Y → T) (activation : Y → Finset B)
    (marks footprint : T → Finset B) (d : Finset B → ℝ)
    (hsub : ∀ y, activation y ⊆ marks (parent y))
    (hinj : ∀ y y', parent y = parent y' →
      activation y = activation y' → y = y')
    {c1 κ κ0 K0 : ℝ}
    (hd : ∀ S, 0 ≤ d S)
    (hmarks : ∀ t, ((marks t).card : ℝ) ≤ c1 * (1 + d (footprint t)))
    (hκ : κ0 + c1 * Real.log 2 ≤ κ)
    (hbase : ∀ b : B,
      ∑ t ∈ Finset.univ.filter (fun t => b ∈ footprint t),
        Real.exp (-κ0 * d (footprint t)) ≤ K0)
    (b : B) :
    ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint (parent y)),
      Real.exp (-κ * d (footprint (parent y))) ≤
        Real.exp (c1 * Real.log 2) * K0 := by
  classical
  let s : Finset Y := Finset.univ.filter (fun y => b ∈ footprint (parent y))
  let u : Finset T := Finset.univ.filter (fun t => b ∈ footprint t)
  have hsu : s.image parent ⊆ u := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have hfib : ∀ t ∈ s.image parent,
      ((s.filter (fun y => parent y = t)).card : ℝ) ≤
        (2 : ℝ) ^ (marks t).card := by
    intro t _
    have hinc : s.filter (fun y => parent y = t) ⊆
        Finset.univ.filter (fun y : Y => parent y = t) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    exact (by exact_mod_cast Finset.card_le_card hinc : _ ≤
      ((Finset.univ.filter (fun y : Y => parent y = t)).card : ℝ)).trans
      (gasLinked_coverage_fibre_count parent activation marks hsub hinj t)
  have hcomp := Finset.sum_comp
    (fun t => Real.exp (-κ * d (footprint t))) parent (s := s)
  calc
    ∑ y ∈ s, Real.exp (-κ * d (footprint (parent y))) =
        ∑ t ∈ s.image parent,
          ((s.filter (fun y => parent y = t)).card •
            Real.exp (-κ * d (footprint t))) := hcomp
    _ ≤ ∑ t ∈ s.image parent,
          (2 : ℝ) ^ (marks t).card * Real.exp (-κ * d (footprint t)) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hfib t ht) (Real.exp_nonneg _)
    _ ≤ ∑ t ∈ s.image parent,
          Real.exp (c1 * Real.log 2) * Real.exp (-κ0 * d (footprint t)) := by
        apply Finset.sum_le_sum
        intro t _
        exact gasLinked_coverage_count_exp_le _ _ (hd _) (hmarks t) hκ
    _ = Real.exp (c1 * Real.log 2) *
          ∑ t ∈ s.image parent, Real.exp (-κ0 * d (footprint t)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (c1 * Real.log 2) *
          ∑ t ∈ u, Real.exp (-κ0 * d (footprint t)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsu
          (fun _ _ _ => Real.exp_nonneg _)
    _ ≤ Real.exp (c1 * Real.log 2) * K0 :=
        mul_le_mul_of_nonneg_left (hbase b) (Real.exp_nonneg _)

end Coverage

end Balaban.Polymer
