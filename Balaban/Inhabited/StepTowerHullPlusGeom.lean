/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSumSize

/-!
# Neighbouring cells lie in one aligned `π′` box (`StepTowerHullPlusGeom`)

If `L ≥ 3` and the cells of side `a` of two sites `x`, `s` are equal or `*`-adjacent
(`CellNear`), there is an aligned box of side `L a` containing both sites
(`exists_box_of_cellNear`): the box based at the base of the cell of `x` shifted by `-a` in every
direction.  This is the geometric input for the hull of a thickened cube set.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization

section Geom

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **Two cells at index distance at most one lie in an aligned box of side `L a`.** -/
theorem exists_box_of_cellNear (hN : L ^ m₀ ∣ N₁) (hL : 3 ≤ L)
    {x s : CTorus d L N₁ m₁ K} (h : CellNear (L := L) (N₁ := N₁) (m₁ := m₁) m₀ K x s) :
    ∃ b : CTorus d L N₁ m₁ K, Aligned (cellSide L m₀ m₁ K) b ∧
      x ∈ box b (L * cellSide L m₀ m₁ K) ∧ s ∈ box b (L * cellSide L m₀ m₁ K) := by
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  set a := cellSide L m₀ m₁ K with hadef
  set n := N₁ * L ^ m₁ * L ^ K with hn
  have han : a ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) ha
  obtain ⟨q, hq, hcb⟩ := h
  have hq' : ∀ μ, -1 ≤ q μ ∧ q μ ≤ 1 := fun μ => by
    have := hq μ
    rw [abs_le] at this
    exact_mod_cast this
  have hLa : 3 * a ≤ L * a := Nat.mul_le_mul_right a hL
  refine ⟨cbase a x + natT (fun _ => n - a), ?_, ?_, ?_⟩
  · refine aligned_add_natT ha (aligned_cbase x) fun μ => ?_
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_sub ha (dvd_refl a))
  · obtain ⟨r, hr, hx⟩ := mem_box_cbase ha0 x
    refine ⟨fun μ => r μ + a, fun μ => ?_, ?_⟩
    · have := hr μ
      show r μ + a < L * a
      omega
    · conv_lhs => rw [hx]
      funext μ
      simp only [natT, Pi.add_apply, Nat.cast_add, Nat.cast_sub han]
      rw [show ((n : ℕ) : ZMod n) = 0 from ZMod.natCast_self n]
      ring
  · obtain ⟨w, hw, hs⟩ := mem_box_cbase ha0 s
    refine ⟨fun μ => (a * (q μ + 1)).toNat + w μ, fun μ => ?_, ?_⟩
    · show (a * (q μ + 1)).toNat + w μ < L * a
      have h1 := hw μ
      have h2 := hq' μ
      have h3 : (a * (q μ + 1)).toNat ≤ 2 * a := by
        have : a * (q μ + 1) ≤ (a : ℤ) * 2 := mul_le_mul_of_nonneg_left (by omega) (by positivity)
        omega
      omega
    · conv_lhs => rw [hs, hcb]
      funext μ
      have h2 := hq' μ
      have h3 : (((a * (q μ + 1)).toNat : ℕ) : ℤ) = a * (q μ + 1) :=
        Int.toNat_of_nonneg (mul_nonneg (by positivity) (by omega))
      have h4 : (((a * (q μ + 1)).toNat : ℕ) : ZMod n) = (((a : ℤ) * (q μ + 1) : ℤ) : ZMod n) := by
        rw [← h3]; simp
      simp only [natT, Pi.add_apply, Nat.cast_add, Nat.cast_sub han, h4]
      rw [show ((n : ℕ) : ZMod n) = 0 from ZMod.natCast_self n]
      push_cast
      ring

end Geom

end Balaban.Inhabited
