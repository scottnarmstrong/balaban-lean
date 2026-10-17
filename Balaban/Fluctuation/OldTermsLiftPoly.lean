/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftGeom
public import Balaban.Localization.P6ActiveSeed

/-!
# Polymer geometry across the old and new descriptions of a physical torus

The one-scale polymer predicate uses the fine torus and the cell side.  Both are preserved
when the old side parameter is multiplied by `L` and the scale index increases by one.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6 Balaban.LargeField

variable {d L A B N₁ m₁ k K : ℕ}

private theorem nbr_cast {n n' : ℕ} (h : n = n') {x y : Torus d n}
    (hxy : Nbr x y) : Nbr (castT h x) (castT h y) := by
  rcases hxy with ⟨μ, hxy | hxy⟩
  · refine ⟨μ, Or.inl ?_⟩
    rw [hxy, castT_add, castT_single]
  · refine ⟨μ, Or.inr ?_⟩
    rw [hxy, castT_add, castT_single]

private theorem reach_cast {n n' : ℕ} (h : n = n') {X : Set (Torus d n)}
    {x y : Torus d n}
    (hxy : Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) x y) :
    Relation.ReflTransGen
      (fun a b => a ∈ castT h '' X ∧ b ∈ castT h '' X ∧ Nbr a b)
      (castT h x) (castT h y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨⟨_, hab.1, rfl⟩, ⟨_, hab.2.1, rfl⟩, nbr_cast h hab.2.2⟩

/-- A one-scale polymer remains a one-scale polymer after the physical-side cast. -/
theorem isPolyDom_cast
    (hside : (A * L ^ m₁) * L ^ k = (B * L ^ m₁) * L ^ K)
    {m₀ j : ℕ} {X : Set (CTorus d L A m₁ k)}
    (hX : IsPolyDom (L := L) (N₁ := A) (m₁ := m₁) (k := k) m₀ j X) :
    IsPolyDom (L := L) (N₁ := B) (m₁ := m₁) (k := K) m₀ j (castT hside '' X) := by
  rcases hX with ⟨hnonempty, ⟨𝒦, hchosen⟩, hconn⟩
  refine ⟨hnonempty.image _, ⟨castT hside '' 𝒦, ?_⟩, ?_⟩
  · constructor
    · rintro b ⟨b₀, hb₀, rfl⟩
      obtain ⟨hal, hbox⟩ := hchosen.1 b₀ hb₀
      refine ⟨castT_aligned hside _ hal, ?_⟩
      rw [← castT_image_box hside]
      exact Set.image_mono hbox
    · rintro z ⟨z₀, hz₀, rfl⟩
      obtain ⟨b₀, hb₀, hzb⟩ := hchosen.2 z₀ hz₀
      refine ⟨castT hside b₀, ⟨b₀, hb₀, rfl⟩, ?_⟩
      rw [← castT_image_box hside]
      exact ⟨z₀, hzb, rfl⟩
  · rintro x ⟨x₀, hx₀, rfl⟩ y ⟨y₀, hy₀, rfl⟩
    exact reach_cast hside (hconn x₀ hx₀ y₀ hy₀)

/-- The old and new polymer predicates agree under the physical torus equivalence. -/
theorem oldTorusEquiv_isPolyDom_iff [NeZero L] [NeZero N₁]
    {m₀ j : ℕ} {X : Set (CTorus d L (L * N₁) m₁ k)} :
    IsPolyDom (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) m₀ j X ↔
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) m₀ j
        (liftOldPoly X) := by
  have heq : (oldTorusEquiv : CTorus d L (L * N₁) m₁ k →
      CTorus d L N₁ m₁ (k + 1)) =
      castT (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) :=
    funext oldTorusEquiv_apply
  rw [liftOldPoly, heq]
  constructor
  · exact isPolyDom_cast (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
  · intro hX
    have hback := isPolyDom_cast
      (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)).symm hX
    simpa [Set.image_image, Function.comp_def, castT_castT] using hback

/-- The inherited generating sets cover their polymers and have no layers above `j`. -/
theorem liftOldTerms_gs_spec [NeZero L] [NeZero N₁] {N : ℕ} {ϱ : ℝ}
    {P : Consts} {Dom : Balaban.SmallField.Def6v2.FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : Balaban.SmallField.Def6v2.SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) :
    X ⊆ ↑(((liftOldTerms Tm).gs j X).Ω 1) ∧
      ∀ i, j < i → ((liftOldTerms Tm).gs j X).Ω i = ∅ := by
  have himg : liftOldPoly (oldTorusEquiv.symm '' X) = X := by
    simp [liftOldPoly, Set.image_image]
  have hXold : IsPolyDom (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
      P.m₀ j (oldTorusEquiv.symm '' X) := by
    apply (oldTorusEquiv_isPolyDom_iff (N₁ := N₁) (m₁ := m₁) (k := k)).2
    simpa [himg] using hX
  obtain ⟨hcover, habove⟩ := hcl.gs_spec j hj1 hjk _ hXold
  constructor
  · intro x hx
    have hxold : oldTorusEquiv.symm x ∈ oldTorusEquiv.symm '' X := ⟨x, hx, rfl⟩
    have hmem := hcover hxold
    change x ∈ (liftOldGS (Tm.gs j (oldTorusEquiv.symm '' X))).Ω 1
    rw [liftOldGS_Ω _ (hj1.trans hjk), mem_liftOldSites]
    exact hmem
  · intro i hji
    change (liftOldGS (Tm.gs j (oldTorusEquiv.symm '' X))).Ω i = ∅
    by_cases hik : i ≤ k
    · rw [liftOldGS_Ω _ hik, habove i hji]
      simp [liftOldSites]
    · simp [liftOldGS, hik]

end Balaban.Fluctuation
