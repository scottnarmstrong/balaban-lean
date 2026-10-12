module

public import Balaban.LargeField.History.StepSeeds

/-!
# Removing components

If `Rm` is a set of components of `X` (width `ω`), the components of `X ∖ ⋃ Rm` are exactly the
components of `X` not in `Rm`.  This is the structure of `Z_k = Z^pre_k ∖ ⋃ Rem_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

variable {d n ω : ℕ} [NeZero n] {X : Finset (Torus d n)} {Rm : Finset (Finset (Torus d n))}

theorem finOf_coe (X : Finset (Torus d n)) : finOf (X : Set (Torus d n)) = X := by
  ext x; simp

/-- Two points of a component of a finset are linked inside it. -/
theorem comp_linked_self_of_comp {C : Finset (Torus d n)} (hC : C ∈ comps ω X) {x y : Torus d n}
    (hx : x ∈ C) (hy : y ∈ C) : Linked ω (C : Set (Torus d n)) x y :=
  comp_linked_self (X := (X : Set (Torus d n))) (by rw [finOf_coe]; exact hC) hx hy

theorem comp_subset_sdiff (hRm : Rm ⊆ comps ω X) {Y : Finset (Torus d n)}
    (hY : Y ∈ comps ω X) (hYR : Y ∉ Rm) : Y ⊆ X \ Rm.biUnion id := by
  intro z hz
  refine Finset.mem_sdiff.mpr ⟨comp_subset hY hz, ?_⟩
  intro hzU
  obtain ⟨r, hr, hzr⟩ := Finset.mem_biUnion.mp hzU
  exact hYR (comp_eq_of_mem hY (hRm hr) hz hzr ▸ hr)

/-- The components of `X ∖ ⋃ Rm` are the components of `X` not in `Rm`. -/
theorem mem_comps_sdiff (hRm : Rm ⊆ comps ω X) {Y : Finset (Torus d n)} :
    Y ∈ comps ω (X \ Rm.biUnion id) ↔ Y ∈ comps ω X ∧ Y ∉ Rm := by
  constructor
  · intro hY
    obtain ⟨x, hxX', rfl⟩ := mem_comps_iff.mp hY
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hxX').1
    obtain ⟨C, hC, hxC⟩ := mem_comp_self (ω := ω) hxX
    have hCR : C ∉ Rm := by
      intro hCR
      exact (Finset.mem_sdiff.mp hxX').2 (Finset.mem_biUnion.mpr ⟨C, hCR, hxC⟩)
    have hCX' := comp_subset_sdiff hRm hC hCR
    have : linkClass ω (X \ Rm.biUnion id) x = C := by
      ext y
      rw [mem_linkClass]
      constructor
      · rintro ⟨hy, hl⟩
        have hl' : Linked ω (X : Set (Torus d n)) x y :=
          hl.mono (by exact_mod_cast Finset.sdiff_subset)
        exact (mem_comp_iff hC hxC).mpr ⟨(Finset.mem_sdiff.mp hy).1, hl'⟩
      · intro hy
        exact ⟨hCX' hy, (comp_linked_self_of_comp hC hxC hy).mono (by exact_mod_cast hCX')⟩
    rw [this]
    exact ⟨hC, hCR⟩
  · rintro ⟨hY, hYR⟩
    obtain ⟨x, hx⟩ := comp_nonempty hY
    have hYX' := comp_subset_sdiff hRm hY hYR
    refine mem_comps_iff.mpr ⟨x, hYX' hx, ?_⟩
    ext y
    rw [mem_linkClass]
    constructor
    · intro hy
      exact ⟨hYX' hy, (comp_linked_self_of_comp hY hx hy).mono (by exact_mod_cast hYX')⟩
    · rintro ⟨hy, hl⟩
      have hl' : Linked ω (X : Set (Torus d n)) x y :=
        hl.mono (by exact_mod_cast Finset.sdiff_subset)
      exact (mem_comp_iff hY hx).mpr ⟨(Finset.mem_sdiff.mp hy).1, hl'⟩

end Balaban.LargeField
