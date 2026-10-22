/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFirstRetained

/-!
# The generating set of a base record

At the first step the generating set has the single top scale `k = 1`: the separation condition is
empty, `Ω_2 = ∅`, and `Ω_1` only has to be a union of first blocks.  So every set `Ωc` of cubes of
`𝕋_1` is the good region of a generating set `baseGen Ωc`, whose `Ω 1` is the fine set of `Ωc`
(`mem_baseGen`), and every set `P` of failed cubes is the failed set of the base record
`BaseRecord.trivial P` with empty `Q`, `R`, `S`, whose good region is `Region.Omega L P univ`.
Hence the family of generating sets of `baseRho1_eq_sum_retained` is canonical
(`baseRho1_eq_sum_retained_canon`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Classical MeasureTheory

noncomputable section

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- **The generating set of a set of cubes of `𝕋_1`**: `Ω 1` is the fine set of the cubes, and
`Ω j = ∅` for `j ≠ 1`. -/
def baseGen (ϱ : ℝ) (Ωc : Set (Torus d n)) : GeneratingSet d L (1 * n) 1 ϱ where
  Ω j := if j = 1 then Finset.univ.filter fun x : Torus d (1 * n * L ^ 1) =>
    cubeMap (baseSectorN L n) L 1 1 1 x ∈ Ωc else ∅
  top := by simp
  subset := by
    intro j hj1 hjk
    have : j = 1 := by omega
    subst this
    simp
  blockUnion := by
    intro j hj1 hjk x x' hxx'
    have hj : j = 1 := by omega
    subst hj
    have hnn : ∀ i, i < 1 → baseSectorN L n i = L * baseSectorN L n (i + 1) :=
      baseSectorN_step L n
    have e : cubeMap (baseSectorN L n) L 1 1 1 x = cubeMap (baseSectorN L n) L 1 1 1 x' := by
      rw [← cubeMap_eq_comp hnn le_rfl x, ← cubeMap_eq_comp hnn le_rfl x']
      exact congrArg _ hxx'
    simp [e]
  separation := by
    intro j hj1 hjk
    omega

/-- The sites of the good region of `baseGen`. -/
theorem mem_baseGen (ϱ : ℝ) (Ωc : Set (Torus d n)) (x : Torus d (1 * n * L ^ 1)) :
    x ∈ (baseGen (L := L) ϱ Ωc).Ω 1 ↔ cubeMap (baseSectorN L n) L 1 1 1 x ∈ Ωc := by
  simp [baseGen]

/-- **The base record with failed cubes `P` and no other cubes.** -/
def BaseRecord.trivial {Rk : ℝ} (P : Set (Torus d n)) : BaseRecord d L n Rk where
  P := P
  Q := ∅
  R := ∅
  S := ∅
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := Set.empty_subset _

/-- **The good region of the failed set `P`**, as the cubes of `𝕋_1`. -/
abbrev goodRegion (P : Finset (Torus d n)) : Set (Torus d n) :=
  Region.Omega L (↑P : Set (Torus d n)) Set.univ

/-- **The first density as a sum over the sets `P` of failed cubes, with the canonical generating
sets.**  The family of generating sets of `baseRho1_eq_sum_retained` is `P ↦ baseGen (Ω(P))`. -/
theorem baseRho1_eq_sum_retained_canon [NeZero N] (ϱ : ℝ) (β a z ν : ℝ) (regimeB : Prop)
    (δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (ε₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    baseRho1 d N L n β a z ν h ψ g =
      ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset,
          ∫ σ : ↥(retSet (baseGen (L := L) ϱ (goodRegion (L := L) P))) →
              Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
            ∫ ψ' : (baseGen (L := L) ϱ (goodRegion (L := L) P)).Ω 1 →
                Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
              ((firstWeight P regimeB ν δ₀ h (z • ψ)
                  (baseMerge (baseGen (L := L) ϱ (goodRegion (L := L) P))
                    (retExtend (baseGen (L := L) ϱ (goodRegion (L := L) P)) σ ε₀) ψ') : ℝ) :
                  ℂ) *
                firstPhysDensity β a ν h g (z • ψ)
                  (baseMerge (baseGen (L := L) ϱ (goodRegion (L := L) P))
                    (retExtend (baseGen (L := L) ϱ (goodRegion (L := L) P)) σ ε₀) ψ')
              ∂(Measure.pi fun _ : (baseGen (L := L) ϱ (goodRegion (L := L) P)).Ω 1 =>
                (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
            ∂(Measure.pi fun _ : ↥(retSet (baseGen (L := L) ϱ (goodRegion (L := L) P))) =>
              (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  have h1 := baseRho1_eq_sum_retained (L := L) (ϱ := ϱ) β a z ν regimeB δ₀ h g ψ
    (fun P => baseGen (L := L) ϱ (goodRegion (L := L) P)) Finset.univ.powerset ε₀
  rw [h1]
  congr 1
  have hf : (Finset.univ : Finset (Torus d n)).powerset.filter
      (fun P => P ∈ (Finset.univ : Finset (Torus d n)).powerset) =
      (Finset.univ : Finset (Torus d n)).powerset :=
    Finset.filter_true_of_mem fun P hP => hP
  have hf' : (Finset.univ : Finset (Torus d n)).powerset.filter
      (fun P => P ∉ (Finset.univ : Finset (Torus d n)).powerset) = ∅ :=
    Finset.filter_false_of_mem fun P hP => not_not.2 hP
  rw [hf, hf']
  simp

end

end Balaban.LargeField
