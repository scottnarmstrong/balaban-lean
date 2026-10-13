/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivPermute

/-!
# Reflection symmetry of the periodized bump

The one-dimensional spline `bsp` and its periodization `perN` are even.  Consequently the bump
of the block of base `y₀` and scale `L ^ m` is reflection symmetric: if the coordinate `μ₀` of
the torus is reflected, `x_μ₀ ↦ c - 1 - x_μ₀`, and the base point is moved to the opposite corner
`y₀_μ₀ ↦ c - L ^ m - y₀_μ₀` of the image cube, the bump value is unchanged (`bump_reflect`),
for every `c` (no divisibility is needed for this identity).  This is the evenness needed for the
reflection clauses of `CoverSymm` and `BlockSymm` with the corner-corrected action on the centres.
The structures themselves for reflections are not constructed in this file.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset

theorem bsp_neg (t : ℝ) : bsp (-t) = bsp t := by
  rcases le_total t (-3 / 2) with h | h
  · rw [bsp_far_left h, bsp_far_right (by linarith)]
  rcases le_total t (-1 / 2) with h' | h'
  · rw [bsp_left h h', bsp_right (by linarith) (by linarith)]; ring
  rcases le_total t (1 / 2) with h'' | h''
  · rw [bsp_mid h' h'', bsp_mid (by linarith) (by linarith)]; ring
  rcases le_total t (3 / 2) with h3 | h3
  · rw [bsp_right h'' h3, bsp_left (by linarith) (by linarith)]; ring
  · rw [bsp_far_right h3, bsp_far_left (by linarith)]

theorem perN_neg (r α : ℝ) : perN r (-α) = perN r α := by
  unfold perN
  rw [← finsum_comp_equiv (Equiv.neg ℤ) (f := fun p : ℤ => bsp (α + p * r))]
  refine finsum_congr fun p => ?_
  simp only [Equiv.neg_apply]
  rw [← bsp_neg]
  congr 1
  push_cast; ring

theorem exists_val_eq {n : ℕ} [NeZero n] (u : ZMod n) (z : ℤ) (h : u = (z : ZMod n)) :
    ∃ e : ℤ, ((u.val : ℕ) : ℝ) = (z : ℝ) + (n : ℝ) * e := by
  have h1 : (((u.val : ℕ) : ℤ) : ZMod n) = ((z : ℤ) : ZMod n) := by
    rw [← h]; simp
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  refine ⟨-e, ?_⟩
  have : (z : ℝ) - ((u.val : ℕ) : ℝ) = (n : ℝ) * e := by exact_mod_cast he
  push_cast; linarith

section Bump

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- **The periodized bump is reflection symmetric.**  Reflecting the coordinate `μ₀` by
`x ↦ c - 1 - x` and moving the base point of the block to the opposite corner
`y₀ ↦ c - L ^ m - y₀` of the image cube leaves the bump unchanged. -/
theorem bump_reflect (m : ℕ) (μ₀ : Fin d) (c : ZMod (N₀ * L ^ k))
    (y0 x : Torus d (N₀ * L ^ k)) :
    bump m (Function.update y0 μ₀ (c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) - y0 μ₀))
      (reflPerm μ₀ c x) = bump m y0 x := by
  unfold bump
  refine Finset.prod_congr rfl fun μ _ => ?_
  by_cases hμ : μ = μ₀
  · subst hμ
    simp only [reflPerm, Equiv.coe_fn_mk, Function.update_self]
    unfold perFac bumpCentre
    simp only [Function.update_self]
    obtain ⟨e1, h1⟩ := exists_val_eq (c - 1 - x μ) ((c.val : ℤ) - 1 - (x μ).val)
      (by push_cast; simp)
    obtain ⟨e2, h2⟩ := exists_val_eq (c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) - y0 μ)
      ((c.val : ℤ) - (L ^ m : ℕ) - (y0 μ).val) (by push_cast; simp)
    have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have key : ((((c - 1 - x μ).val : ℕ) : ℝ) - ((((c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) -
          y0 μ).val : ℕ) : ℝ) + (((L : ℝ) ^ m - 1) / 2))) / (L : ℝ) ^ m =
        -((((x μ).val : ℕ) : ℝ) - ((((y0 μ).val : ℕ) : ℝ) + (((L : ℝ) ^ m - 1) / 2))) /
          (L : ℝ) ^ m + ((e1 - e2 : ℤ) : ℝ) * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) := by
      rw [h1, h2]
      push_cast
      field_simp
      ring
    rw [key, perN_add_int_mul, neg_div, perN_neg]
  · have : Function.update y0 μ₀ (c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) - y0 μ₀) μ = y0 μ :=
      Function.update_of_ne hμ _ _
    simp only [reflPerm, Equiv.coe_fn_mk, Function.update_of_ne hμ]
    unfold perFac bumpCentre
    rw [this]

end Bump

end Balaban.Localization.DecEquiv
