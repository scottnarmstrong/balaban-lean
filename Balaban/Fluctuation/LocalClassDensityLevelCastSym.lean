/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelCastGeom

/-!
# Symmetry groups and blocks across the cast of the step torus (`LocalClassDensityLevelCastSym`)

For `N₁' L ^ m₁' = N₁ L ^ m₁` and `m₀' + m₁' = m₀ + m₁` the translations, reflections and
coordinate exchanges are conjugated into each other by the cast `e`, so `e` carries the full level
group and the `M`-paving group of the torus `(N₁', m₁')` onto those of `(N₁, m₁)`; the block base
`blockBase` and the alignment correspond.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField

section Sym

variable {d L N₁ N₁' m₁ m₁' K : ℕ}

private theorem castT_nsmul_single' {n n' : ℕ} (h : n = n') (s : ℕ) (μ : Fin d) :
    castT h (s • (Pi.single μ 1 : Torus d n)) = s • (Pi.single μ 1 : Torus d n') := by
  cases h
  rfl

private theorem castT_flip' {n n' : ℕ} (h : n = n') (s : ℕ) (μ : Fin d) (x : Torus d n) :
    castT h (Function.update x μ ((s : ZMod n) - 1 - x μ)) =
      Function.update (castT h x) μ ((s : ZMod n') - 1 - (castT h x) μ) := by
  cases h
  rfl

private theorem castT_swap' {n n' : ℕ} (h : n = n') (μ ν : Fin d) (x : Torus d n) :
    castT h (x ∘ Equiv.swap μ ν) = castT h x ∘ Equiv.swap μ ν := by
  cases h
  rfl

variable (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
  {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K} (he : ∀ x, e x = castT (castSide_eq hc K) x)

include he

/-- The cast conjugates translations. -/
theorem castEquiv_transBy (s : ℕ) (μ : Fin d) :
    e.permCongrHom (transBy (d := d) (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) s μ) =
      transBy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) s μ := by
  apply Equiv.ext
  intro x
  change e (transBy s μ (e.symm x)) = transBy s μ x
  unfold transBy
  change e ((e.symm x) + s • (Pi.single μ 1 : CTorus d L N₁' m₁' K)) =
    x + s • (Pi.single μ 1 : CTorus d L N₁ m₁ K)
  rw [he, castT_add, castT_nsmul_single']
  simp [← he]

/-- The cast conjugates coordinate reflections. -/
theorem castEquiv_flipBy (s : ℕ) (μ : Fin d) :
    e.permCongrHom (flipBy (d := d) (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) s μ) =
      flipBy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) s μ := by
  apply Equiv.ext
  intro x
  change e (flipBy s μ (e.symm x)) = flipBy s μ x
  unfold flipBy
  simp only [Equiv.coe_fn_mk]
  rw [he, castT_flip']
  simp [← he]

/-- The cast conjugates coordinate exchanges. -/
theorem castEquiv_swapJ (μ ν : Fin d) :
    e.permCongrHom (swapJ (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) (d := d) μ ν) =
      swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) μ ν := by
  apply Equiv.ext
  intro x
  change e (swapJ μ ν (e.symm x)) = swapJ μ ν x
  unfold swapJ
  simp only [Equiv.coe_fn_mk]
  rw [he, castT_swap']
  simp [← he]

/-- The groups generated at side `s` are conjugate under the cast. -/
theorem castEquiv_symGroupBy (s : ℕ) :
    Subgroup.map e.permCongrHom
      (symGroupBy (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) (d := d) s) =
      symGroupBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) s := by
  simp only [symGroupBy, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
    · exact Or.inl (Or.inl ⟨μ, castEquiv_transBy hc he s μ⟩)
    · exact Or.inl (Or.inr ⟨μ, castEquiv_flipBy hc he s μ⟩)
    · exact Or.inr ⟨μ, ν, castEquiv_swapJ hc he μ ν⟩
  · intro hg
    rcases hg with ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
    · exact ⟨transBy s μ, Or.inl (Or.inl ⟨μ, rfl⟩), castEquiv_transBy hc he s μ⟩
    · exact ⟨flipBy s μ, Or.inl (Or.inr ⟨μ, rfl⟩), castEquiv_flipBy hc he s μ⟩
    · exact ⟨swapJ μ ν, Or.inr ⟨μ, ν, rfl⟩, castEquiv_swapJ hc he μ ν⟩

/-- The full level groups are conjugate under the cast. -/
theorem castEquiv_fullJSymGroup (j : ℕ) :
    Subgroup.map e.permCongrHom
      (fullJSymGroup (N₁ := N₁') (m₁ := m₁') (k := K) (d := d) L j) =
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j :=
  castEquiv_symGroupBy hc he (L ^ j)

/-- The paving groups are conjugate under the cast, when the cell sides agree. -/
theorem castEquiv_pavingSymGroup {m₀ m₀' : ℕ} (hm : m₀' + m₁' = m₀ + m₁) (j : ℕ) :
    Subgroup.map e.permCongrHom
      (pavingSymGroup (N₁ := N₁') (m₁ := m₁') (k := K) (d := d) L m₀' j) =
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ j := by
  unfold pavingSymGroup
  rw [cellSide_eq_of_add hm j]
  exact castEquiv_symGroupBy hc he _

/-- The block base commutes with the cast. -/
theorem castEquiv_blockBase (j : ℕ) (y : CTorus d L N₁' m₁' K) :
    e (blockBase (N₁ := N₁') (m₁ := m₁') (k := K) (d := d) L j y) =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L j (e y) := by
  unfold blockBase
  rw [he, he]
  exact castT_cbase _ _ _

/-- Alignment is unchanged by the cast. -/
theorem castEquiv_aligned_iff (a : ℕ) (y : CTorus d L N₁' m₁' K) :
    Aligned a (e y) ↔ Aligned a y := by
  constructor
  · intro h μ
    have := h μ
    rwa [he, castT_val] at this
  · intro h μ
    rw [he, castT_val]
    exact h μ

end Sym

end Balaban.Fluctuation
