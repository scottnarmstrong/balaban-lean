/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootPavingMap

/-!
# Non-vacuity of the root and paving map on a concrete torus

`d = 3`, `L = 2`, `N₁ = 2`, `m₀ = m₁ = 0`, `K = 1`: the fine torus has side `2 · 2^0 · 2 = 4`, the
cell side of level `1` is `2`, so the torus has `2` cells per direction.  There are a root `z`
and a cube set `T` containing the root cube, a paving symmetry `r` (the translation by one cell
side in direction `0`) with `sitesOf (r • T) ≠ sitesOf T`, and a coefficient family `e` with
exactly one non-zero value whose rooted sum is evaluated.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

theorem rootPaving_witness :
    ∃ (z : RootIdx 3 2 2 0 1)
      (T : Finset (CubeB (d := 3) (L := 2) (N₁ := 2) (m₁ := 0) (K := 1) 0 1 Set.univ))
      (r : Equiv.Perm (CTorus 3 2 2 0 1)),
      r ∈ pavingSymGroup (N₁ := 2) (m₁ := 0) (k := 1) (d := 3) 2 0 1 ∧
      rootCube (m₀ := 0) z ∈ T ∧ sitesOf (cubeAct r T) ≠ sitesOf T ∧
      ∃ e : RootIdx 3 2 2 0 1 →
          Finset (CubeB (d := 3) (L := 2) (N₁ := 2) (m₁ := 0) (K := 1) 0 1 Set.univ) → ℂ,
        (∀ z' T', e z' T' ≠ 0 → z' = z ∧ T' = T) ∧
          rootedSum e (rootSite z) (sitesOf T) = 1 := by
  classical
  have hN : (2 : ℕ) ^ 0 ∣ 2 := by norm_num
  let z : RootIdx 3 2 2 0 1 := 0
  let T : Finset (CubeB (d := 3) (L := 2) (N₁ := 2) (m₁ := 0) (K := 1) 0 1 Set.univ) :=
    {rootCube (m₀ := 0) z}
  let r : Equiv.Perm (CTorus 3 2 2 0 1) :=
    transBy (L := 2) (N₁ := 2) (m₁ := 0) (k := 1) (cellSide 2 0 0 1) 0
  have hr : r ∈ pavingSymGroup (N₁ := 2) (m₁ := 0) (k := 1) (d := 3) 2 0 1 :=
    Subgroup.subset_closure (Or.inl (Or.inl ⟨0, rfl⟩))
  refine ⟨z, T, r, hr, Finset.mem_singleton_self _, ?_,
    fun z' T' => if z' = z ∧ T' = T then 1 else 0, ?_, ?_⟩
  · intro h
    have hx : r (rootSite z) ∈ sitesOf (cubeAct r T) := by
      rw [sitesOf_cubeAct hN hr]
      refine ⟨rootSite z, ?_, rfl⟩
      exact (rootSite_mem_sitesOf_iff hN z T).2 (Finset.mem_singleton_self _)
    rw [h] at hx
    obtain ⟨b, hb, w, hw, hwe⟩ := mem_sitesOf.1 hx
    have hb' : b = rootCube (m₀ := 0) z := Finset.mem_singleton.1 hb
    subst hb'
    have h0 := congrFun hwe 0
    have hw0 : w 0 < 2 := by simpa [cellSide] using hw 0
    have e1 : rootSite z = 0 := by funext μ; simp [rootSite, z]
    have e2 : cbase (cellSide 2 0 0 1) (0 : CTorus 3 2 2 0 1) = 0 := by
      funext μ; simp [cbase]
    simp only [rootCube, r, transBy, e1, e2] at h0
    simp [natT, cellSide] at h0
    generalize w 0 = n at h0 hw0
    interval_cases n <;> revert h0 <;> decide
  · intro z' T' h
    by_contra hne
    exact h (by simp [hne])
  · rw [rootedSum_eq_of_pair hN _ (z := z) (T := T) rfl rfl]
    simp
