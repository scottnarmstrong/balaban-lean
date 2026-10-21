/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonLocal

/-!
# Distances on the step torus and the cell neighbourhood

`supDist_sameCell`: two sites of one cell of side `a` are within `a - 1`.
`exists_int_of_supDist`: a site within sup-distance `r` of `p` is `p` moved by an integer vector of
sup norm at most `r`.  `mem_nbhd_of_supDist`: if `r + 6 M ≤ (L - 1) a_K` (`M = L^{K+m₁}`), the
`6 M`-neighbourhood of the sup-distance `r` ball around `p` lies in the cell neighbourhood
`nbhd m₀ p`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LocalCover Balaban.LargeField

section Dist

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
theorem supDist_sameCell {n a : ℕ} [NeZero n] (ha : 0 < a) {x y : Torus d n}
    (h : SameCell a x y) : supDist x y ≤ a - 1 := by
  rw [supDist_le_iff]
  intro μ
  rw [cycNorm_le_iff]
  refine ⟨((x μ - y μ).val : ℤ) * 0 + ((x μ).val : ℤ) - ((y μ).val : ℤ), ?_, by simp⟩
  have h1 := h μ
  have h2 := Nat.div_add_mod (x μ).val a
  have h3 := Nat.div_add_mod (y μ).val a
  have h4 := Nat.mod_lt (x μ).val ha
  have h5 := Nat.mod_lt (y μ).val ha
  rw [h1] at h2
  rw [abs_le]
  generalize (x μ).val = xv at *
  generalize (y μ).val = yv at *
  generalize a * (yv / a) = q at *
  generalize xv % a = r at *
  generalize yv % a = r' at *
  omega

omit [NeZero L] [NeZero N₁] in
theorem exists_int_of_supDist {n r : ℕ} [NeZero n] {x p : Torus d n} (h : supDist x p ≤ r) :
    ∃ u : Fin d → ℤ, x = p + (intTorus u : Torus d n) ∧ ∀ μ, |u μ| ≤ r := by
  rw [supDist_le_iff] at h
  choose u hu using fun μ => (cycNorm_le_iff _ _).1 (h μ)
  refine ⟨u, funext fun μ => ?_, fun μ => (hu μ).1⟩
  simp only [Pi.add_apply, intTorus_apply, (hu μ).2]
  ring

/-- **The `6 M`-neighbourhood of a ball around `p` lies in the cell neighbourhood of `p`.** -/
theorem mem_nbhd_of_supDist (m₀ : ℕ) {r : ℕ} (hr : (r : ℝ) + 6 * (L : ℝ) ^ ((k + 1) + m₁) ≤
      (((L - 1) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ))
    {p x : CTorus d L N₁ m₁ (k + 1)} (hx : supDist x p ≤ r) (hL : 1 ≤ L)
    (w : Fin d → ℤ) (hw : ∀ μ, |(w μ : ℝ)| < 6 * (L : ℝ) ^ ((k + 1) + m₁)) :
    x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) ∈ nbhd m₀ p := by
  obtain ⟨u, rfl, hu⟩ := exists_int_of_supDist hx
  have e : p + (intTorus u : CTorus d L N₁ m₁ (k + 1)) + intTorus w =
      p + (intTorus (u + w) : CTorus d L N₁ m₁ (k + 1)) := by
    funext μ; simp only [Pi.add_apply, intTorus_apply]; push_cast; ring
  rw [e]
  have := add_intTorus_mem_cellNbhd hL (mem_cell m₀ p) (u + w) fun μ => by
    have h1 : |(u μ : ℝ)| ≤ r := by
      have := hu μ
      exact_mod_cast this
    have h2 := hw μ
    have h3 : |((u + w) μ : ℝ)| ≤ |(u μ : ℝ)| + |(w μ : ℝ)| := by
      simp only [Pi.add_apply]
      push_cast
      exact abs_add_le _ _
    have h4 : |(((u + w) μ : ℤ) : ℝ)| ≤ (((L - 1) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) := by
      linarith
    exact_mod_cast h4
  exact this

end Dist

end Balaban.Inhabited
