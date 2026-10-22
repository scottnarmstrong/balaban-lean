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
sup norm at most `r`.
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

end Dist

end Balaban.Inhabited
