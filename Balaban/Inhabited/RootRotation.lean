/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.SymmetryPartition
public import Balaban.Frozen.Geometry.IsPolymer
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Root-F for an arbitrary unit external field, by rotation

The rotation identity of the partition function, `Z(R h, g) = Z(h, Rᵀ g)`, and the `ℓ¹` estimate
`‖Rᵀ g‖₁ ≤ √N ‖g‖₁` are in `Balaban/Model/SymmetryPartition.lean`
(`partitionFunction_rot`, `sum_norm_rotSource_le`).  This file adds:

* `exists_linearIsometryEquiv_apply_single`: every unit vector is the image of the coordinate
  vector `e₀` under a linear isometry equivalence of `ℝ^N`;
* `rootF_clauses_transfer`: the clauses of Root-F for a family `T` at the field `e` on the source
  ball of radius `√N` (analyticity and the log identity on `∑‖g‖₁ < √N`, the bound on
  `∑‖g‖₁ ≤ √N / 2`) give the clauses of Root-F at the field `R e`, on the unit ball and the
  half ball, for the transported family `R T(·; Rᵀ g)`, with the bound constant multiplied by `√N`;
* `rootF_clauses_unitField`: the same from the coordinate vector to an arbitrary unit field.
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- Every unit vector of `ℝ^N` is the image of a coordinate unit vector under a linear isometry
equivalence of `ℝ^N` (a Householder reflection). -/
theorem exists_linearIsometryEquiv_apply_single {N : ℕ} (i₀ : Fin N)
    (v : EuclideanSpace ℝ (Fin N)) (hv : ‖v‖ = 1) :
    ∃ R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N),
      R (EuclideanSpace.single i₀ 1) = v := by
  have hne : ‖(EuclideanSpace.single i₀ (1 : ℝ) : EuclideanSpace ℝ (Fin N))‖ = ‖v‖ := by
    rw [hv]; simp
  exact ⟨Submodule.reflection (ℝ ∙ (EuclideanSpace.single i₀ (1 : ℝ) - v))ᗮ,
    Submodule.reflection_sub hne⟩

/-- The pairing of a source with the coordinates of the rotated field. -/
theorem sum_rotSource_mul_apply {d N ℓ : ℕ}
    (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℂ) (x : Torus d ℓ) :
    ∑ i, rotSource R g x i * ((e i : ℝ) : ℂ) = ∑ i, g x i * (((R e) i : ℝ) : ℂ) := by
  simp only [rotSource, rot_apply_coord R, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Root-F's clauses transfer along a rotation of the field.**  If `T0` satisfies the clauses
of Root-F at the field `e` with the source radius `√N` in place of `1` (support, locality,
analyticity on `∑‖g‖₁ < √N`, the bound on `∑‖g‖₁ ≤ √N / 2`, the logarithm identity for
`∑‖g‖₁ < √N`, independence of the torus), then `T ℓ j x X g = R (T0 ℓ j x X (Rᵀ g))` satisfies
the clauses of Root-F at the field `R e`, with radii `1` and `1/2` and the bound constant
multiplied by `√N` (the operator norm of `R` from `ℓ^∞` to `ℓ^∞`, at most `√N`). -/
theorem rootF_clauses_transfer (d N : ℕ) (hN : 0 < N) (δ κ c₉ : ℝ) (L M kf : ℕ) (β ν : ℝ)
    (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (e : EuclideanSpace ℝ (Fin N))
    (T0 : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) →
        (Fin N → ℂ))
    (hT0 :
      (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
          T0 ℓ j x X = 0) ∧
        (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
          T0 ℓ j x X g = T0 ℓ j x X g') ∧
        (∀ j x X, AnalyticOnNhd ℂ (T0 ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < Real.sqrt N}) ∧
        (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
          ∑ y, ∑ i, ‖g y i‖ ≤ Real.sqrt N / 2 →
          ‖T0 ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < Real.sqrt N →
          Complex.log (partitionFunction d N ℓ β ν e g / partitionFunction d N ℓ β ν e 0) =
            ∑ x, ∑ i, g x i * (e i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T0 ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T0 ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T0 ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))) :
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
          ‖T ℓ j x X g‖ ≤ Real.sqrt N * c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          Complex.log (partitionFunction d N ℓ β ν (R e) g / partitionFunction d N ℓ β ν (R e) 0) =
            ∑ x, ∑ i, g x i * ((R e) i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) := by
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine ⟨fun ℓ j x X => rotFamily R (T0 ℓ j) x X, ?_, ?_⟩
  · intro ℓ _ hdvd
    obtain ⟨hsupp, hloc, han, hbd, hlog⟩ := hT0.1 ℓ hdvd
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j x X hjx
      funext g
      funext i
      simp [rotFamily, hsupp j x X hjx]
      simp [rotVec]
    · intro j x X g g' hg
      exact rotFamily_local R (T0 ℓ j) x X (hloc j x X) g g' hg
    · intro j x X
      exact rotFamily_analytic R (T0 ℓ j) hN x X 1 (by simpa using han j x X)
    · intro j hj x X g hg
      have hg' : ∑ y, ∑ i, ‖rotSource R g y i‖ ≤ Real.sqrt N / 2 :=
        (sum_norm_rotSource_le R g).trans (by nlinarith)
      calc ‖rotFamily R (T0 ℓ j) x X g‖ ≤ Real.sqrt N * ‖T0 ℓ j x X (rotSource R g)‖ :=
            norm_rotFamily_le R (T0 ℓ j) x X g
        _ ≤ Real.sqrt N * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) :=
            mul_le_mul_of_nonneg_left (hbd j hj x X _ hg') hsq.le
        _ = _ := by ring
    · intro g hg
      have hg' : ∑ y, ∑ i, ‖rotSource R g y i‖ < Real.sqrt N :=
        lt_of_le_of_lt (sum_norm_rotSource_le R g) (by nlinarith)
      have h0 : rotSource R (0 : Torus d ℓ → Fin N → ℂ) = 0 := by
        funext x i; simp [rotSource]
      rw [partitionFunction_rot R β ν e g, partitionFunction_rot R β ν e 0, h0,
        hlog _ hg']
      congr 1
      · exact Finset.sum_congr rfl fun x _ => sum_rotSource_mul_apply R e g x
      · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun X _ => ?_
        exact (rotFamily_pairing R (T0 ℓ j) x X g).symm
  · intro ℓ ℓ' _ _ hd hd' j a A g ha hA
    have key := hT0.2 ℓ ℓ' hd hd' j a A
      (fun y i => ∑ k, (rotEntry R k i : ℂ) * g y k) ha hA
    show rotVec R _ = rotVec R _
    exact congrArg (rotVec R) key

/-- **Root-F's clauses from the coordinate field to every unit field.** -/
theorem rootF_clauses_unitField (d N : ℕ) (hN : 0 < N) (δ κ c₉ : ℝ) (L M kf : ℕ) (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (T0 : (ℓ : ℕ) → ℕ → Torus d ℓ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) →
        (Fin N → ℂ))
    (hT0 :
      (∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
        (∀ j x X, ¬ (j ∈ Finset.Icc 1 (kf + 1) ∧ x ∈ X ∧ IsPolymer d ℓ (M * L ^ j) X) →
          T0 ℓ j x X = 0) ∧
        (∀ j x X (g g' : Torus d ℓ → Fin N → ℂ), (∀ y ∈ X, g y = g' y) →
          T0 ℓ j x X g = T0 ℓ j x X g') ∧
        (∀ j x X, AnalyticOnNhd ℂ (T0 ℓ j x X) {g | ∑ y, ∑ i, ‖g y i‖ < Real.sqrt N}) ∧
        (∀ j ∈ Finset.Icc 1 (kf + 1), ∀ x X (g : Torus d ℓ → Fin N → ℂ),
          ∑ y, ∑ i, ‖g y i‖ ≤ Real.sqrt N / 2 →
          ‖T0 ℓ j x X g‖ ≤ c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
            * Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ j) ^ d)) ∧
        ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < Real.sqrt N →
          Complex.log (partitionFunction d N ℓ β ν
              (EuclideanSpace.single ⟨0, hN⟩ 1) g /
              partitionFunction d N ℓ β ν (EuclideanSpace.single ⟨0, hN⟩ 1) 0) =
            ∑ x, ∑ i, g x i * ((EuclideanSpace.single ⟨0, hN⟩ (1 : ℝ) :
                EuclideanSpace ℝ (Fin N)) i : ℂ)
              + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ x, ∑ X : Finset (Torus d ℓ), ∑ i,
                  g x i * T0 ℓ j x X g i) ∧
      ∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'], M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
        ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (g : (Fin d → ℤ) → Fin N → ℂ),
          a ∈ A → (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
          T0 ℓ j (fun μ => (a μ : ZMod ℓ)) (A.image fun y μ => (y μ : ZMod ℓ))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
            T0 ℓ' j (fun μ => (a μ : ZMod ℓ')) (A.image fun y μ => (y μ : ZMod ℓ'))
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))) :
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
          ‖T ℓ j x X g‖ ≤ Real.sqrt N * c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))
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
              (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ)) := by
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_apply_single (⟨0, hN⟩ : Fin N) h hh
  subst hR
  exact rootF_clauses_transfer d N hN δ κ c₉ L M kf β ν R _ T0 hT0

end Balaban
