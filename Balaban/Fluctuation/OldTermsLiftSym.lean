/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftAction

/-!
# Symmetry groups under the physical torus equivalence

The generator formulas depend only on the physical modulus.  Conjugation by
the modulus cast therefore identifies the old and new symmetry groups.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

private theorem castT_nsmul_single {n n' : ℕ} (h : n = n') (s : ℕ) (μ : Fin d) :
    castT h (s • (Pi.single μ 1 : Torus d n)) =
      s • (Pi.single μ 1 : Torus d n') := by
  cases h
  rfl

private theorem castT_flip {n n' : ℕ} (h : n = n') (s : ℕ) (μ : Fin d)
    (x : Torus d n) :
    castT h (Function.update x μ ((s : ZMod n) - 1 - x μ)) =
      Function.update (castT h x) μ ((s : ZMod n') - 1 - (castT h x) μ) := by
  cases h
  rfl

private theorem castT_swap {n n' : ℕ} (h : n = n') (μ ν : Fin d)
    (x : Torus d n) :
    castT h (x ∘ Equiv.swap μ ν) = castT h x ∘ Equiv.swap μ ν := by
  cases h
  rfl

omit [NeZero L] [NeZero N₁] in
/-- The physical-site equivalence conjugates translations. -/
theorem oldTorusEquiv_transBy (s : ℕ) (μ : Fin d) :
    (oldTorusEquiv (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).permCongrHom
      (transBy (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) s μ) =
    transBy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) s μ := by
  apply Equiv.ext
  intro x
  change oldTorusEquiv (transBy s μ (oldTorusEquiv.symm x)) = transBy s μ x
  unfold transBy
  change oldTorusEquiv ((oldTorusEquiv.symm x) +
      s • (Pi.single μ 1 : CTorus d L (L * N₁) m₁ k)) =
    x + s • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1))
  rw [oldTorusEquiv_apply, castT_add, castT_nsmul_single]
  simp [← oldTorusEquiv_apply]

omit [NeZero L] [NeZero N₁] in
/-- The physical-site equivalence conjugates coordinate reflections. -/
theorem oldTorusEquiv_flipBy (s : ℕ) (μ : Fin d) :
    (oldTorusEquiv (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).permCongrHom
      (flipBy (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) s μ) =
    flipBy (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) s μ := by
  apply Equiv.ext
  intro x
  change oldTorusEquiv (flipBy s μ (oldTorusEquiv.symm x)) = flipBy s μ x
  unfold flipBy
  simp only [Equiv.coe_fn_mk]
  rw [oldTorusEquiv_apply, castT_flip]
  simp [← oldTorusEquiv_apply]

omit [NeZero L] [NeZero N₁] in
/-- The physical-site equivalence conjugates coordinate exchanges. -/
theorem oldTorusEquiv_swapJ (μ ν : Fin d) :
    (oldTorusEquiv (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).permCongrHom
      (swapJ (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) μ ν) =
    swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) μ ν := by
  apply Equiv.ext
  intro x
  change oldTorusEquiv (swapJ μ ν (oldTorusEquiv.symm x)) = swapJ μ ν x
  unfold swapJ
  simp only [Equiv.coe_fn_mk]
  rw [oldTorusEquiv_apply, castT_swap]
  simp [← oldTorusEquiv_apply]

omit [NeZero L] [NeZero N₁] in
/-- The old and new symmetry groups generated at side `s` are conjugate. -/
theorem oldTorusEquiv_symGroupBy (s : ℕ) :
    Subgroup.map (oldTorusEquiv (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k)).permCongrHom
      (symGroupBy (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) s) =
      symGroupBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) s := by
  simp only [symGroupBy, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases hr with ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
    · exact Or.inl (Or.inl ⟨μ, oldTorusEquiv_transBy s μ⟩)
    · exact Or.inl (Or.inr ⟨μ, oldTorusEquiv_flipBy s μ⟩)
    · exact Or.inr ⟨μ, ν, oldTorusEquiv_swapJ μ ν⟩
  · intro hg
    rcases hg with ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
    · exact ⟨transBy s μ, Or.inl (Or.inl ⟨μ, rfl⟩), oldTorusEquiv_transBy s μ⟩
    · exact ⟨flipBy s μ, Or.inl (Or.inr ⟨μ, rfl⟩), oldTorusEquiv_flipBy s μ⟩
    · exact ⟨swapJ μ ν, Or.inr ⟨μ, ν, rfl⟩, oldTorusEquiv_swapJ μ ν⟩

omit [NeZero L] [NeZero N₁] in
/-- The old and new full level symmetry groups are conjugate. -/
theorem oldTorusEquiv_fullJSymGroup (j : ℕ) :
    Subgroup.map (oldTorusEquiv (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k)).permCongrHom
      (fullJSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L j) =
      fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L j := by
  exact oldTorusEquiv_symGroupBy (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k) (L ^ j)

omit [NeZero L] [NeZero N₁] in
/-- The old and new fixed-paving symmetry groups are conjugate. -/
theorem oldTorusEquiv_pavingSymGroup (m₀ j : ℕ) :
    Subgroup.map (oldTorusEquiv (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k)).permCongrHom
      (pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L m₀ j) =
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ j := by
  exact oldTorusEquiv_symGroupBy (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k) (cellSide L m₀ m₁ j)

end Balaban.Fluctuation
