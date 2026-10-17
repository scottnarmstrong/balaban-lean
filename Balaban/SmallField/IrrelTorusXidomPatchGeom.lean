/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomWitness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Full-field bound for the inverse-rotated tube witness

The inverse-rotated polydisc field agrees with the original local field on the placed blocks.
Outside those blocks it is constant. Its distance from the reference spin is controlled at the
centre by the tube witness and the original local bound.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ k N j : ℕ} [NeZero L] [NeZero N₁]
  {i₀ : Fin N} {ν r : ℝ} {S : Finset (Site d)}
  {y : CTorus d L N₁ m₁ k} {c : Cfg d N S}

/-- The full inverse-rotated field stays in the larger rectangular spin chart when the
original data on the placed blocks are within the anisotropic spin radius. -/
theorem inverse_rotated_field_close
    (hr : 0 ≤ r)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsOrth R) (hRb : EntryBd N R)
    (hRc : rotCfgL R S c ∈ polyAniso i₀ ν r S)
    (hy0 : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (y - y) ∈ S)
    (hlocal : ∀ z, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S →
      ∀ i, ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) i -
        (Pi.single i₀ 1 : Spin N) i‖ ≤ r) :
    ∀ z i, ‖(rotField R.transpose
      (fun w => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (rotCfgL R S c) (w - y))) z i - (Pi.single i₀ 1 : Spin N) i‖ ≤
      r * (1 + N * rotB N) := by
  let e : Spin N := Pi.single i₀ 1
  let v : Fld d L N₁ m₁ k N := fun w =>
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (w - y)
  let vR : Fld d L N₁ m₁ k N := fun w =>
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S (rotCfgL R S c) (w - y)
  have hB0 : 0 ≤ rotB N := by unfold rotB; positivity
  have hB40 : (40 : ℝ) ≤ rotB N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
    unfold rotB
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hRt : ∀ i l, ‖R.transpose i l‖ ≤ rotB N := by
    intro i l
    have h40 : ‖R.transpose i l‖ ≤ 40 := by
      simpa only [Matrix.transpose_apply] using (entryBd_bound hRb l i)
    exact h40.trans hB40
  have hanchor : ‖R.transpose.mulVec e - e‖ ≤ r * (1 + N * rotB N) := by
    have hnear : ‖v y - e‖ ≤ r := by
      rw [pi_norm_le_iff_of_nonneg hr]
      intro i
      exact hlocal y hy0 i
    have hrotY : vR y = R.mulVec (v y) :=
      fieldOf_rot R c hy0
    have hpoly : ‖vR y - e‖ ≤ r := by
      rw [pi_norm_le_iff_of_nonneg hr]
      intro i
      exact fieldOf_sub_le_poly hRc hr (y - y) i
    have horth : R.transpose.mulVec (R.mulVec (v y)) = v y := by
      rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    have he : R.transpose.mulVec e - e =
        R.transpose.mulVec (e - vR y) + (v y - e) := by
      rw [hrotY, Matrix.mulVec_sub, horth]
      abel
    rw [he]
    calc
      _ ≤ ‖R.transpose.mulVec (e - vR y)‖ + ‖v y - e‖ := norm_add_le _ _
      _ ≤ N * rotB N * ‖e - vR y‖ + r := by
        gcongr
        exact norm_mulVec_le hB0 hRt _
      _ ≤ N * rotB N * r + r := by
        gcongr
        rw [norm_sub_rev]
        exact hpoly
      _ = r * (1 + N * rotB N) := by ring
  intro z i
  by_cases hz : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S
  · have heq : (rotField R.transpose vR) z = v z := by
      have hrot := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁)
        (m₁ := m₁) (k := k) R c hz
      change vR z = R.mulVec (v z) at hrot
      simp only [rotField, hrot]
      rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    change ‖(rotField R.transpose vR) z i - e i‖ ≤ _
    rw [heq]
    exact (hlocal z hz i).trans (by nlinarith [mul_nonneg (Nat.cast_nonneg N) hB0])
  · have heq : vR z = e := by
      funext l
      simp [vR, fieldOf, hz, e]
    change ‖(rotField R.transpose vR) z i - e i‖ ≤ _
    simp only [rotField, heq]
    exact (norm_le_pi_norm _ i).trans hanchor

end Balaban.SmallField.Def6v2
