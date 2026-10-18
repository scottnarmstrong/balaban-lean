/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.Def6AvgLimit

/-!
# Pair separation on a shape below the thermodynamic chart threshold

This is the geometry shared by the scalar trace and each entry of the raw matrix.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField

variable {d L m₁ k m₀ j : ℕ} [NeZero L]

/-- Every two block positions of a good shape below `tauY` differ by less than half the
block-torus side in every coordinate. -/
theorem pair_small_of_tauY (hjk : j ≤ k) {y : Site d} {X' : Finset (Site d)} {n : ℕ}
    (hy : y ∈ X') (hgood : GoodAt L m₁ k m₀ j X' n)
    (hsz : sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y)
    {z z' : Site d} (hz : z ∈ X') (hz' : z' ∈ X') (μ : Fin d) :
    2 * |z μ - z' μ| < ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
  have hsmall := small_coords_of_tauY hjk hy hgood hsz
  have h1 := hsmall z hz μ
  have h2 := hsmall z' hz' μ
  have h3 := abs_nonneg (z μ)
  have h4 := abs_nonneg (z' μ)
  have h5 : |z μ - z' μ| ≤ |z μ| + |z' μ| := abs_sub _ _
  have h6 : (0 : ℤ) ≤ ((L * L ^ (m₀ + m₁) : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

end Balaban.SmallField.Def6
