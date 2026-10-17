/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.Derivatives
public import Balaban.Correlations.KF0RootFPartial
import Mathlib.Tactic.FieldSimp

/-!
# The common physical-mass factor in the normalized observable

The factorization of a physical partition function into a source-independent scalar and a
normalized integral is an explicitly named input.  Its scalar cancels from the landed
`logPartition`, while the normalized integral still contains the external field.  The second
theorem feeds a physical polymer exponential identity to the landed observable-form lemma;
it does not assert that such a polymer expansion has been produced.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Correlations

/-- Any nonzero factor independent of `g` cancels *inside* the landed normalized logarithm.
For the hard-spin mass-square convention this factor is the product of the one-site
normalizations.  The field-dependent normalized integral `I` remains. -/
theorem logPartition_eq_of_common_mass_factor {d N ℓ : ℕ} [NeZero ℓ]
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (I : (Torus d ℓ → Fin N → ℂ) → ℂ) (z : ℂ)
    (hz : z ≠ 0) (hI0 : I 0 ≠ 0)
    (hfactor : ∀ g, partitionFunction d N ℓ β ν h g = z * I g)
    (g : Torus d ℓ → Fin N → ℂ) :
    logPartition d N ℓ β ν h g = Complex.log (I g / I 0) := by
  unfold logPartition
  rw [hfactor g, hfactor 0]
  congr 1
  field_simp

/-- The P7 observable form after a physical polymer expansion of the normalized integral.
`hfactor` is the exact kept-mass factorization and `hpoly` is the missing physical polymer
exponential identity; analyticity of the localized polymer terms is stated separately. -/
theorem logPartition_observable_of_kept_mass_factor {d N ℓ : ℕ} [NeZero ℓ] [NeZero N]
    (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (I : (Torus d ℓ → Fin N → ℂ) → ℂ) (z : ℂ)
    (hz : z ≠ 0) (hI0 : I 0 ≠ 0)
    (hfactor : ∀ g, partitionFunction d N ℓ β ν h g = z * I g)
    (p : (ℓ' : ℕ) → Finset (Torus d ℓ') → (Torus d ℓ' → Fin N → ℂ) → ℂ)
    (hana : ∀ X : Finset (Torus d ℓ), AnalyticOnNhd ℂ (p ℓ X)
      (ball1 (Torus d ℓ) (Fin N)))
    (hpoly : ∀ g : Torus d ℓ → Fin N → ℂ, l1 g < 1 →
      I g / I 0 = Complex.exp (∑ x, ∑ i, g x i * (h i : ℂ)
        + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0)))
    (g : Torus d ℓ → Fin N → ℂ) (hg : l1 g < 1) :
    logPartition d N ℓ β ν h g =
      ∑ x, ∑ i, g x i * (h i : ℂ)
        + ∑ X : Finset (Torus d ℓ), (p ℓ X g - p ℓ X 0) := by
  have hexp : ∀ g' : Torus d ℓ → Fin N → ℂ, l1 g' < 1 →
      partitionFunction d N ℓ β ν h g' / partitionFunction d N ℓ β ν h 0 =
        Complex.exp (∑ x, ∑ i, g' x i * (h i : ℂ)
          + ∑ X : Finset (Torus d ℓ), (p ℓ X g' - p ℓ X 0)) := by
    intro g' hg'
    rw [hfactor g', hfactor 0]
    have hcancel : z * I g' / (z * I 0) = I g' / I 0 := by field_simp
    rw [hcancel]
    exact hpoly g' hg'
  change Complex.log (partitionFunction d N ℓ β ν h g /
    partitionFunction d N ℓ β ν h 0) = _
  exact log_partition_eq_of_exp hana hexp hg

end Balaban.LargeField
