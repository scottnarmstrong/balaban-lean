/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseDefectWalks
import Mathlib.Tactic.Linarith

/-!
# Transport of the visited-set resolved walk sums

If `σ : ι → ι'` is injective on a set `B` and carries the entries of `D` on `B × B` to those of
`D'`, then for `x, y ∈ B` and `S ⊆ B` the walk sum of `D'` from `σ x` to `σ y` with visited set
`σ '' S` equals that of `D` from `x` to `y` with visited set `S` (`walkW_transport`).  Nothing is
assumed about `D'` off `σ '' B` or about `D` off `B`: a walk with visited set in `σ '' B` has all
its sites there.  The proof uses the closed recursion `walkW_succ`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Finset Matrix

section Transport

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **The recursion of `walkW` with the first site split off**: the visited set `S'` of the
remaining walk is `S` or `S.erase x`. -/
theorem walkW_succ (D : Matrix ι ι ℂ) (m : ℕ) (x y : ι) (S : Finset ι) :
    walkW D (m + 1) x y S = if x ∈ S then
      ∑ w, D x w * (walkW D m w y S + walkW D m w y (S.erase x)) else 0 := by
  simp only [walkW]
  have key : ∀ (a : Finset ι → ℂ), (∑ S', if S = insert x S' then a S' else 0) =
      if x ∈ S then a S + a (S.erase x) else 0 := by
    intro a
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceIte]
      have hne : S ≠ S.erase x := fun h => by
        have := Finset.notMem_erase x S
        rw [← h] at this; exact this hx
      have hset : (Finset.univ.filter fun S' => S = insert x S') = {S, S.erase x} := by
        ext S'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro h
          by_cases hx' : x ∈ S'
          · left
            rw [Finset.insert_eq_of_mem hx'] at h
            exact h.symm
          · right
            rw [h, Finset.erase_insert hx']
        · rintro (rfl | rfl)
          · exact (Finset.insert_eq_of_mem hx).symm
          · exact (Finset.insert_erase hx).symm
      rw [← Finset.sum_filter, hset, Finset.sum_pair hne]
    · simp only [hx, ↓reduceIte]
      refine Finset.sum_eq_zero fun S' _ => ?_
      have h : ¬ S = insert x S' := fun h => hx (h ▸ Finset.mem_insert_self _ _)
      simp only [h, ↓reduceIte]
  split_ifs with hx
  · refine Finset.sum_congr rfl fun w _ => ?_
    have := key (fun S' => D x w * walkW D m w y S')
    simp only [hx, ↓reduceIte] at this
    rw [this]; ring
  · refine Finset.sum_eq_zero fun w _ => ?_
    have := key (fun S' => D x w * walkW D m w y S')
    simp only [hx, ↓reduceIte] at this
    exact this

/-- A walk sum vanishes when its start is not in the visited set. -/
theorem walkW_eq_zero_of_notMem (D : Matrix ι ι ℂ) (m : ℕ) {x y : ι} {S : Finset ι}
    (h : x ∉ S) : walkW D m x y S = 0 := by
  by_contra h0
  exact h (walkW_ne_zero_imp D m x y S h0).1

/-- **Transport of the visited-set resolved walk sums.** -/
theorem walkW_transport (D : Matrix ι ι ℂ) (D' : Matrix ι' ι' ℂ) (σ : ι → ι') (B : Finset ι)
    (hinj : Set.InjOn σ B) (hDD : ∀ u ∈ B, ∀ v ∈ B, D' (σ u) (σ v) = D u v) (m : ℕ) :
    ∀ x y S, x ∈ B → y ∈ B → S ⊆ B →
      walkW D' m (σ x) (σ y) (S.image σ) = walkW D m x y S := by
  -- facts on images of subsets of `B`
  have himg_mem : ∀ {S : Finset ι}, S ⊆ B → ∀ {s}, s ∈ B → (σ s ∈ S.image σ ↔ s ∈ S) := by
    intro S hS s hs
    constructor
    · intro h
      obtain ⟨t, ht, hts⟩ := Finset.mem_image.1 h
      rw [hinj (hS ht) hs hts] at ht
      exact ht
    · intro h; exact Finset.mem_image_of_mem _ h
  have himg_erase : ∀ {S : Finset ι}, S ⊆ B → ∀ {x}, x ∈ B →
      (S.erase x).image σ = (S.image σ).erase (σ x) := by
    intro S hS x hx
    ext z
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨t, ⟨htx, htS⟩, rfl⟩
      exact ⟨fun h => htx (hinj (hS htS) hx h), t, htS, rfl⟩
    · rintro ⟨hzx, t, htS, rfl⟩
      exact ⟨t, ⟨fun h => hzx (h ▸ rfl), htS⟩, rfl⟩
  induction m with
  | zero =>
    intro x y S hx hy hS
    simp only [walkW]
    have hiff : (σ x = σ y ∧ S.image σ = {σ x}) ↔ (x = y ∧ S = {x}) := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨hinj hx hy h1, ?_⟩
        have hxS : x ∈ S := (himg_mem hS hx).1 (by rw [h2]; simp)
        ext s
        simp only [Finset.mem_singleton]
        constructor
        · intro hs
          have : σ s ∈ S.image σ := Finset.mem_image_of_mem _ hs
          rw [h2, Finset.mem_singleton] at this
          exact hinj (hS hs) hx this
        · rintro rfl; exact hxS
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, by simp⟩
    exact if_congr hiff rfl rfl
  | succ m ih =>
    intro x y S hx hy hS
    rw [walkW_succ, walkW_succ]
    by_cases hxS : x ∈ S
    · have hxS' : σ x ∈ S.image σ := (himg_mem hS hx).2 hxS
      simp only [hxS, hxS', ↓reduceIte]
      have hSe : S.erase x ⊆ B := (Finset.erase_subset _ _).trans hS
      -- restrict both sums to `B`
      have hL : ∑ w', D' (σ x) w' * (walkW D' m w' (σ y) (S.image σ) +
          walkW D' m w' (σ y) ((S.image σ).erase (σ x))) =
          ∑ w' ∈ B.image σ, D' (σ x) w' * (walkW D' m w' (σ y) (S.image σ) +
          walkW D' m w' (σ y) ((S.image σ).erase (σ x))) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun w' _ hw' => ?_
        have h1 : w' ∉ S.image σ := fun h => hw' (Finset.image_subset_image hS h)
        have h2 : w' ∉ (S.image σ).erase (σ x) := fun h => h1 (Finset.mem_of_mem_erase h)
        rw [walkW_eq_zero_of_notMem D' m h1, walkW_eq_zero_of_notMem D' m h2]
        simp
      have hR : ∑ w, D x w * (walkW D m w y S + walkW D m w y (S.erase x)) =
          ∑ w ∈ B, D x w * (walkW D m w y S + walkW D m w y (S.erase x)) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_
        have h1 : w ∉ S := fun h => hw (hS h)
        have h2 : w ∉ S.erase x := fun h => h1 (Finset.mem_of_mem_erase h)
        rw [walkW_eq_zero_of_notMem D m h1, walkW_eq_zero_of_notMem D m h2]
        simp
      rw [hL, hR, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hDD x hx w hw, ih w y S hw hy hS, ← himg_erase hS hx, ih w y (S.erase x) hw hy hSe]
    · have hxS' : σ x ∉ S.image σ := fun h => hxS ((himg_mem hS hx).1 h)
      simp [hxS, hxS']

/-- **The local term of a visited set is transported.** -/
theorem walkTerm_transport (D : Matrix ι ι ℂ) (D' : Matrix ι' ι' ℂ) (σ : ι → ι') (B : Finset ι)
    (hinj : Set.InjOn σ B) (hDD : ∀ u ∈ B, ∀ v ∈ B, D' (σ u) (σ v) = D u v) {x : ι}
    (hx : x ∈ B) (n : ℕ) {S : Finset ι} (hS : S ⊆ B) :
    walkTerm D' (σ x) n (S.image σ) = walkTerm D x n S := by
  unfold walkTerm
  rw [walkW_transport D D' σ B hinj hDD (n + 1) x x S hx hx hS]

end Transport

end Balaban.LargeField.Base
