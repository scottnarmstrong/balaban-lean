/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Estimates

/-!
# Boxes in `ℤ^d` and their images in the tori; torus independence of the terms

Conditional on the clauses of Root-F; consumed by the Root-C provider.  For `R ≥ 1` the box
`boxZ R = {w ∈ ℤ^d : |w_μ| < R}` embeds into every torus of side `ℓ ≥ 4 R` by `embedZ ℓ w = w mod ℓ`
(`valMinAbs ∘ embedZ ℓ = id`).  The agreement clause of Root-F makes the terms `T_j(x, A; 0)` and
the derivatives `D_{y,k} T_j(x, A; 0)` of two admissible tori coincide on the images of the finite
subsets `A ⊆ boxZ R` (`value_agree`, `fderiv_agree`).  The sum over all polymers is split into the
sum over subsets of the box and the remaining sum (`sum_split`).
-/

@[expose] public section

open scoped Classical

namespace Balaban.Correlations

open Balaban Finset

/-- The box `{w ∈ ℤ^d : |w_μ| < R}`. -/
noncomputable def boxZ (d R : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Ioo (-(R : ℤ)) R

/-- Reduction modulo `ℓ`. -/
abbrev embedZ {d : ℕ} (ℓ : ℕ) (w : Fin d → ℤ) : Torus d ℓ := fun μ => (w μ : ZMod ℓ)

theorem mem_boxZ {d R : ℕ} {w : Fin d → ℤ} : w ∈ boxZ d R ↔ ∀ μ, |w μ| < R := by
  simp [boxZ, Fintype.mem_piFinset, abs_lt]

variable {d N ℓ ℓ' R : ℕ} [NeZero ℓ] [NeZero ℓ']

theorem valMinAbs_embedZ (hℓ : 4 * R ≤ ℓ) {w : Fin d → ℤ} (hw : w ∈ boxZ d R) (μ : Fin d) :
    ZMod.valMinAbs (embedZ ℓ w μ) = w μ := by
  have h := mem_boxZ.1 hw μ
  rw [abs_lt] at h
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩ <;> nlinarith [(by exact_mod_cast hℓ : (4 * R : ℤ) ≤ ℓ)]

theorem embedZ_injOn (hℓ : 4 * R ≤ ℓ) : Set.InjOn (embedZ (d := d) ℓ) (boxZ d R : Set (Fin d → ℤ)) := by
  intro w hw w' hw' h
  funext μ
  have e1 := valMinAbs_embedZ hℓ (Finset.mem_coe.1 hw) μ
  have e2 := valMinAbs_embedZ hℓ (Finset.mem_coe.1 hw') μ
  rw [← e1, ← e2, h]

omit [NeZero ℓ] in
theorem embedZ_valMinAbs (z : Torus d ℓ) : embedZ ℓ (fun μ => ZMod.valMinAbs (z μ)) = z := by
  funext μ
  simp [embedZ]

/-- The image of the box in the torus. -/
noncomputable def boxT (d R ℓ : ℕ) [NeZero ℓ] : Finset (Torus d ℓ) :=
  (boxZ d R).image (embedZ ℓ)

theorem mem_boxT {z : Torus d ℓ} : z ∈ boxT d R ℓ ↔ ∃ w ∈ boxZ d R, embedZ ℓ w = z := by
  simp [boxT]

/-- A site outside the image of the box has a coordinate of absolute value `≥ R`. -/
theorem exists_far {z : Torus d ℓ} (hz : z ∉ boxT d R ℓ) : ∃ μ, R ≤ |ZMod.valMinAbs (z μ)| := by
  by_contra hcon
  push Not at hcon
  exact hz (mem_boxT.2 ⟨fun μ => ZMod.valMinAbs (z μ), mem_boxZ.2 hcon, embedZ_valMinAbs z⟩)

/-- Subsets of the box and subsets of its image correspond. -/
theorem sum_split (hℓ : 4 * R ≤ ℓ) (f : Finset (Torus d ℓ) → ℂ) :
    ∑ X : Finset (Torus d ℓ), f X =
      ∑ A ∈ (boxZ d R).powerset, f (A.image (embedZ ℓ)) +
        ∑ X ∈ Finset.univ.filter (fun X : Finset (Torus d ℓ) => ¬ X ⊆ boxT d R ℓ), f X := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun X : Finset (Torus d ℓ) =>
    X ⊆ boxT d R ℓ)]
  congr 1
  symm
  refine Finset.sum_bij (fun A _ => A.image (embedZ ℓ)) ?_ ?_ ?_ ?_
  · intro A hA
    rw [mem_powerset] at hA
    simp only [mem_filter, mem_univ, true_and]
    exact Finset.image_subset_image hA
  · intro A hA A' hA' h
    rw [mem_powerset] at hA hA'
    ext w
    constructor
    · intro hw
      have : embedZ ℓ w ∈ A'.image (embedZ ℓ) := h ▸ mem_image_of_mem _ hw
      obtain ⟨w', hw', hww'⟩ := mem_image.1 this
      have := embedZ_injOn hℓ (Finset.mem_coe.2 (hA' hw')) (Finset.mem_coe.2 (hA hw)) hww'
      exact this ▸ hw'
    · intro hw
      have : embedZ ℓ w ∈ A.image (embedZ ℓ) := h ▸ mem_image_of_mem _ hw
      obtain ⟨w', hw', hww'⟩ := mem_image.1 this
      have := embedZ_injOn hℓ (Finset.mem_coe.2 (hA hw')) (Finset.mem_coe.2 (hA' hw)) hww'
      exact this ▸ hw'
  · intro X hX
    simp only [mem_filter, mem_univ, true_and] at hX
    refine ⟨X.image fun z μ => ZMod.valMinAbs (z μ), ?_, ?_⟩
    · rw [mem_powerset]
      intro w hw
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hw
      obtain ⟨w', hw', rfl⟩ := mem_boxT.1 (hX hz)
      have : (fun μ => ZMod.valMinAbs (embedZ ℓ w' μ)) = w' := funext (valMinAbs_embedZ hℓ hw')
      rw [this]
      exact hw'
    · ext z
      simp only [mem_image]
      constructor
      · rintro ⟨w, ⟨z', hz', rfl⟩, rfl⟩
        rwa [embedZ_valMinAbs]
      · intro hz
        exact ⟨_, ⟨z, hz, rfl⟩, embedZ_valMinAbs z⟩
  · intro A _
    rfl

end Balaban.Correlations
