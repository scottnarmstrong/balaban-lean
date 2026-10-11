/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Model.PartitionFunction
public import Balaban.Frozen.Geometry.IsPolymer
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# The clauses of Root-F, as a predicate

Conditional on the clauses of Root-F; consumed by the Root-C provider.  Root-F
(`Balaban.logPartition_multiscale`) is a draft root and is not imported; `RootFClauses` copies the
clauses it asserts about the family `T` of terms, so that the consequences developed in
`Balaban/Correlations/` are theorems *about the clauses* (hypotheses `RootFClauses ...`), never
proofs of Root-F.  `RootFStatement` copies the type of Root-F, and `rootFStatement_iff` records
that it is `∃ δ > 0, ∀ κ c₉, ∃ L M β₀, ∀ β ≥ β₀, ... ∃ kf, ... ∃ T, RootFClauses ...`.
-/

@[expose] public section

namespace Balaban.Correlations

/-- The type of the family of terms `T ℓ j x X g` of Root-F. -/
abbrev RootFFamily (d N : ℕ) : Type :=
  (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → (Fin N → ℂ)

/-- The clauses of Root-F on one admissible torus: vanishing off polymers, locality, analyticity,
the bound on `∑ ∑ ‖g‖ ≤ 1/2`, and the identity for `log (Z(g)/Z(0))`. -/
def RootFTorusClauses (d N L M : ℕ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
    (κ c₉ δ : ℝ) (T : RootFFamily d N) (ℓ : ℕ) [NeZero ℓ] : Prop :=
  (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
    T ℓ j x X = 0) ∧
  (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
    T ℓ j x X g = T ℓ j x X g') ∧
  (∀ j x X, AnalyticOnNhd ℂ (T ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
  (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
    ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
    ‖T ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
      * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
  ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
    Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
      ∑ x, ∑ i, g x i * (h i : ℂ)
        + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
            g x i * T ℓ j x X g i

/-- The agreement clause of Root-F: the terms of two admissible tori agree on the images of a
finite set `A ⊂ ℤ^d` contained in the box `|y_μ| < min(ℓ, ℓ')/4`. -/
def RootFAgreement (d N L M : ℕ) (kf : ℕ) (T : RootFFamily d N) : Prop :=
  ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
    ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
      a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
      T ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
          (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
        T ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
          (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))

/-- The clauses of Root-F about the family `T` of terms, for fixed data
`d N L M β ν h kf κ c₉ δ`. -/
def RootFClauses (d N L M : ℕ) (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
    (κ c₉ δ : ℝ) (T : RootFFamily d N) : Prop :=
  (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
    RootFTorusClauses d N L M β ν h kf κ c₉ δ T ℓ) ∧
  RootFAgreement d N L M kf T

/-- The statement of Root-F, copied from the frozen root (which is not imported), with the
clauses unfolded. -/
def RootFStatement (d N : ℕ) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
    ∃ T : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) →
        (Fin N → ℂ),
      (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
          T ℓ j x X = 0) ∧
        (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
          T ℓ j x X g = T ℓ j x X g') ∧
        (∀ j x X, AnalyticOnNhd ℂ (T ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
        (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
          ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
          ‖T ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0) =
            ∑ x, ∑ i, g x i * (h i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))

/-- Root-F's conclusion is `∃ δ > 0, ∀ κ c₉, ∃ L M β₀, ∀ β ≥ β₀, ... ∃ kf, ... ∃ T,
RootFClauses ...`. -/
theorem rootFStatement_iff (d N : ℕ) :
    RootFStatement d N ↔
      ∃ δ : ℝ, 0 < δ ∧
      ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
      ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
      ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
      ∃ T : RootFFamily d N, RootFClauses d N L M β ν h kf κ c₉ δ T :=
  Iff.rfl

end Balaban.Correlations
