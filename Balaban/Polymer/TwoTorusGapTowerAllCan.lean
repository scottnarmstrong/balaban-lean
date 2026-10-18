/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerRootFBox
public import Balaban.Polymer.TwoTorusGapTowerDataOrigin

/-!
# The canonical torus forces a bounded family (blocker 7)

In `towerGapScale_rootFSites_box` the canonical torus `can` satisfies `K ℓ ≤ K (can X)` for every
torus `ℓ` and every polymer `X` of `ℓ` in the quarter box.  The one-site polymer `{0}` is such a
polymer on every torus, so the numbers `K ℓ` of cells per side are bounded by `K (can {0})`.  Hence
the statement can be used for a family of tori with bounded `K` (for instance a finite family, see
`exists_can_of_finite`) and never for the family of all admissible sides, where `K` is unbounded.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

/-- The one-site block animal gives the polymer `{0}` of every torus of the family. -/
theorem zero_mem_P_and_Q {ι : Type*} (d : ℕ) (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4) (ℓ : ι) :
    ({0} : Finset (Fin d → ℤ)) ∈ P ℓ ∧ Q ℓ {0} := by
  refine ⟨(hP ℓ _).2 ⟨{0}, ⟨⟨0, by simp⟩, ?_⟩, ?_⟩, (hQ ℓ _).2 (by simp)⟩
  · refine { preconnected := fun u v => ?_, nonempty := ⟨⟨0, by simp⟩⟩ }
    have hu : (u : Balaban.Torus d (K ℓ)) = 0 := by simpa using u.2
    have hv : (v : Balaban.Torus d (K ℓ)) = 0 := by simpa using v.2
    rw [Subtype.ext (hu.trans hv.symm)]
  · ext x; simp [funext_iff]

/-- The canonical torus of `towerGapScale_rootFSites_box` bounds `K` on the whole family. -/
theorem K_bounded_of_can {ι : Type*} (d : ℕ) (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)]
    (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
    (can : Finset (Fin d → ℤ) → ι)
    (hP : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
      X = Y.image (fun b μ => (b μ).valMinAbs))
    (hQ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
    (hcanK : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X)) :
    ∀ ℓ, K ℓ ≤ K (can {0}) := fun ℓ =>
  hcanK ℓ _ (zero_mem_P_and_Q d K P Q hP hQ ℓ).1 (zero_mem_P_and_Q d K P Q hP hQ ℓ).2

end Balaban.Polymer.TwoTorusStep
