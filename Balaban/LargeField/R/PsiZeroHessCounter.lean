/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessRef

/-!
# The defect of the bare statement of `PsiZeroInput` (PSIZERO-HESS §1)

The bare assertion that `BgHyp` yields a `PsiZeroInput` for every box is false: the geometry (1.1) is needed.

* `not_psiZeroInput_emptyGen`: for the legal generating set with `Ω_j = ∅` at every level (`emptyGen`) the
  effective action vanishes identically (`effAction_emptyGen`), so no `PsiZeroInput` exists for a nonempty box
  (a proper box with an inactive top layer).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Empty

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The generating set with `Ω_j = ∅` for all `j` (a legal generating set: all conditions are vacuous). -/
def emptyGen (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (ϱ : ℝ) : GeneratingSet d L N₀ k ϱ where
  Ω := fun _ => ∅
  top := rfl
  subset := fun _ _ _ => Finset.Subset.refl _
  blockUnion := fun _ _ _ x x' _ => by simp
  separation := fun _ _ _ x _ y hy => absurd hy (Finset.notMem_empty y)

theorem dataSites_emptyGen : dataSites (emptyGen d L N₀ k ϱ) = ∅ := by
  ext x
  simp [mem_dataSites, mem_collar, emptyGen]

/-- With `Ω_j = ∅` the effective action vanishes for every block field. -/
theorem effAction_emptyGen (a : ℕ → ℝ) (ψ : BlockField d L N₀ k N) :
    effAction (emptyGen d L N₀ k ϱ) a ψ = 0 := by
  have : IsEmpty ↥((emptyGen d L N₀ k ϱ).Ω 1) := ⟨fun x => by simpa [emptyGen] using x.2⟩
  have h1 : (emptyGen d L N₀ k ϱ).Ω 1 = ∅ := rfl
  unfold effAction action
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
  simp [h1]

theorem not_psiZeroInput_emptyGen [NeZero N] (hN : 0 < N) (a : ℕ → ℝ) (b0 : Torus d (N₀ * L ^ (k - k)))
    (w : Fin d → ℕ) (X : Set (Torus d (N₀ * L ^ (k - k)))) (hZ : (box b0 w).Nonempty) :
    IsEmpty (PsiZeroInput (N := N) (emptyGen d L N₀ k ϱ) a b0 w X) := by
  refine ⟨fun inp => ?_⟩
  obtain ⟨z, hz⟩ := hZ
  have hzf : z ∈ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w := mem_boxFinset.2 hz
  set v : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N :=
    EuclideanSpace.single (⟨z, hzf⟩, ⟨0, hN⟩) 1 with hv
  have hvn : ‖v‖ = 1 := by simp [hv]
  have ht : TubeOn (N := N) (emptyGen d L N₀ k ϱ) Set.univ inp.η₀ (fun _ _ => (0 : ℝ)) := by
    refine ⟨fun x x' h => ?_, fun x hx => ?_⟩
    · have := h.1; rw [dataSites_emptyGen] at this; simp at this
    · rw [dataSites_emptyGen] at hx; simp at hx
  have h := inp.hess _ inp.η₀ inp.η₀_pos le_rfl ht v
  have hF : effOn (N := N) (emptyGen d L N₀ k ϱ) a (boxFinset b0 w) (fun _ _ => (0 : ℝ)) = fun _ => 0 := by
    funext u; exact effAction_emptyGen a _
  rw [hF, hvn] at h
  simp at h
  linarith [inp.c_pos]

end Empty

end Balaban.LargeField
