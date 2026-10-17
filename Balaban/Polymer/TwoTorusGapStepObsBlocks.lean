/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsV

/-!
# The blocks of the coarse torus under a translation and the recentring map (item 24, blocker 7)

`blockSite_add_coarse`: the corner of the translated block is the translated corner; the coarse
translation of a translation by a multiple of `L^(k+1)` is `⌊t / L^(k+1)⌋`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Blocks

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L]

/-- The arithmetic of `blockSite_add_coarse` in `ZMod`. -/
theorem zmod_block_add {n c p : ℕ} [NeZero n] [NeZero c] (hp : 0 < p) (hn : n = p * c)
    (x : ZMod c) (y : ZMod n) (hy : p ∣ y.val) :
    ((p * (x + (((y.val / p : ℕ)) : ZMod c)).val : ℕ) : ZMod n) =
      ((p * x.val : ℕ) : ZMod n) + y := by
  obtain ⟨q, hq⟩ := hy
  have htv : y.val < p * c := by rw [← hn]; exact ZMod.val_lt _
  have hqc : q < c := by
    rw [hq] at htv
    exact lt_of_mul_lt_mul_left htv (Nat.zero_le _)
  have hdiv : y.val / p = q := by rw [hq, Nat.mul_div_cancel_left _ hp]
  rw [hdiv]
  conv_rhs => rw [← ZMod.natCast_zmod_val y, hq]
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hqc]
  have hmod := Nat.mod_add_div (x.val + q) c
  have e : p * (x.val + q) = p * ((x.val + q) % c) + n * ((x.val + q) / c) := by
    rw [hn]
    conv_lhs => rw [← hmod]
    ring
  have h2 : ((p * ((x.val + q) % c) : ℕ) : ZMod n) = ((p * (x.val + q) : ℕ) : ZMod n) := by
    rw [e]
    push_cast
    simp
  rw [h2]
  push_cast
  ring

/-- **The corner of the translated block is the translated corner.**  For a translation `t` by a
multiple of `L^(k+1)` whose coarse translation is `τ μ = ⌊t μ / L^(k+1)⌋`. -/
theorem blockSite_add_coarse (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ (k + 1) ∣ (t μ).val)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    LocalCover.blockSite k (b + fun μ => ((((t μ).val / L ^ (k + 1) : ℕ)) :
      ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))) = LocalCover.blockSite k b + t := by
  funext μ
  have hnc : N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)) = N₁ * L ^ m₁ := by
    rw [Nat.sub_self, pow_zero, mul_one]
  have : NeZero (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) :=
    ⟨by have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  exact zmod_block_add (pow_pos (NeZero.pos L) _) (by rw [hnc, mul_comm]) (b μ) (t μ) (ht μ)

end Blocks

section BlocksRec

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L]

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

/-- **The recentred coarse block.**  The coarse recentring `b ↦ bc (b + τA) - τB`, `τ = ⌊t / L^(k+1)⌋`,
has the corner map `x ↦ bm (x + tA) - tB`: the corner of the image block, translated by `tB`, is the
`bm`-image of the translated corner. -/
theorem blockSite_recentred {rc r : ℕ} (tA : CTorus d L N₁ m₁ (k + 1))
    (tB : CTorus d L N₁' m₁ (k + 1)) (htA : ∀ μ, L ^ (k + 1) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ (k + 1) ∣ (tB μ).val) (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
      (b + fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
        ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))))
    (hr : L ^ (k + 1) * rc ≤ r) (hs : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    LocalCover.blockSite k (bc (b + fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
        ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))) -
      fun μ => ((((tB μ).val / L ^ (k + 1) : ℕ)) : ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
      + tB = bm (LocalCover.blockSite k b + tA) := by
  rw [← blockSite_add_coarse tB htB, sub_add_cancel,
    blockSite_boxMap (K := k + 1) (r := r) le_rfl _ hz hr hs, blockSite_add_coarse tA htA]

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- **A bijection between filtered sums.** -/
theorem sum_ite_bij {α β : Type*} [Fintype α] [Fintype β] (pA : α → Prop) (pB : β → Prop)
    [DecidablePred pA] [DecidablePred pB]
    (F : α → ℂ) (F' : β → ℂ) (ψ : α → β) (hmap : ∀ a, pA a → pB (ψ a) ∧ F' (ψ a) = F a)
    (hinj : ∀ a₁ a₂, pA a₁ → pA a₂ → ψ a₁ = ψ a₂ → a₁ = a₂)
    (hsurj : ∀ b, pB b → ∃ a, pA a ∧ ψ a = b) :
    (∑ b, if pB b then F' b else 0) = ∑ a, if pA a then F a else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun a _ => ψ a) (fun a ha => ?_) (fun a₁ ha₁ a₂ ha₂ h => ?_)
    (fun b hb => ?_) (fun a ha => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmap a (Finset.mem_filter.1 ha).2).1⟩
  · exact hinj a₁ a₂ (Finset.mem_filter.1 ha₁).2 (Finset.mem_filter.1 ha₂).2 h
  · obtain ⟨a, ha, rfl⟩ := hsurj b (Finset.mem_filter.1 hb).2
    exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩, rfl⟩
  · exact (hmap a (Finset.mem_filter.1 ha).2).2.symm

end BlocksRec

end Balaban.Polymer.TwoTorusStep
