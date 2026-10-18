/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelRho
public import Balaban.Fluctuation.OldTermsLiftPoly

/-!
# Geometry across the cast of the step torus (`LocalClassDensityLevelCastGeom`)

Let `N₁' L ^ m₁' = N₁ L ^ m₁` and let `m₀' + m₁' = m₀ + m₁`.  The tori
`CTorus d L N₁' m₁' K` and `CTorus d L N₁ m₁ K` have the same side, and the cell sides
`cellSide L m₀' m₁' j` and `cellSide L m₀ m₁ j` agree.  For an equivalence `e` of the two tori
induced by the equality of sides (`castT`), the polymers of `𝒟_j`, their sizes, the symmetry groups
of the level lattice and of the `M`-paving, the blocks and the alignment correspond.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField

section Side

variable {d L N₁ N₁' m₁ m₁' : ℕ}

theorem castSide_eq (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (K : ℕ) :
    N₁' * L ^ m₁' * L ^ K = N₁ * L ^ m₁ * L ^ K := by rw [hc]

/-- The equivalence of the two step tori at the equal sides, with its formula. -/
theorem exists_castEquiv (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (K : ℕ) :
    ∃ e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K,
      ∀ x, e x = castT (castSide_eq hc K) x :=
  ⟨Equiv.ofBijective _ ⟨castT_injective _, castT_surjective _⟩, fun _ => rfl⟩

theorem cellSide_eq_of_add {m₀ m₀' : ℕ} (hm : m₀' + m₁' = m₀ + m₁) (j : ℕ) :
    cellSide L m₀' m₁' j = cellSide L m₀ m₁ j := by
  unfold cellSide
  congr 1
  omega

end Side

section Poly

variable {d L A B m₁ m₁' k K m₀ m₀' j : ℕ}

private theorem nbr_cast' {n n' : ℕ} (h : n = n') {x y : Torus d n}
    (hxy : Nbr x y) : Nbr (castT h x) (castT h y) := by
  rcases hxy with ⟨μ, hxy | hxy⟩
  · refine ⟨μ, Or.inl ?_⟩
    rw [hxy, castT_add, castT_single]
  · refine ⟨μ, Or.inr ?_⟩
    rw [hxy, castT_add, castT_single]

private theorem reach_cast' {n n' : ℕ} (h : n = n') {X : Set (Torus d n)}
    {x y : Torus d n}
    (hxy : Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) x y) :
    Relation.ReflTransGen
      (fun a b => a ∈ castT h '' X ∧ b ∈ castT h '' X ∧ Nbr a b)
      (castT h x) (castT h y) := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨⟨_, hab.1, rfl⟩, ⟨_, hab.2.1, rfl⟩, nbr_cast' h hab.2.2⟩

/-- A one-scale polymer stays a one-scale polymer under the cast of the torus, when the cell sides
agree. -/
theorem isPolyDom_cast_cellSide
    (hside : (A * L ^ m₁') * L ^ k = (B * L ^ m₁) * L ^ K)
    (hcs : cellSide L m₀' m₁' j = cellSide L m₀ m₁ j)
    {X : Set (CTorus d L A m₁' k)}
    (hX : IsPolyDom (L := L) (N₁ := A) (m₁ := m₁') (k := k) m₀' j X) :
    IsPolyDom (L := L) (N₁ := B) (m₁ := m₁) (k := K) m₀ j (castT hside '' X) := by
  rcases hX with ⟨hnonempty, ⟨𝒦, hchosen⟩, hconn⟩
  unfold ChosenOne at hchosen
  rw [hcs] at hchosen
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
    exact reach_cast' hside (hconn x₀ hx₀ y₀ hy₀)

end Poly

section PolyEquiv

variable {d L N₁ N₁' m₁ m₁' K m₀ m₀' j : ℕ}

/-- The polymers of `𝒟_j` on the two tori correspond under the cast. -/
theorem isPolyDom_castEquiv_iff (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hm : m₀' + m₁' = m₀ + m₁)
    {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K} (he : ∀ x, e x = castT (castSide_eq hc K) x)
    (X : Set (CTorus d L N₁' m₁' K)) :
    IsPolyDom (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) m₀' j X ↔
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j (e '' X) := by
  have hcs := cellSide_eq_of_add (L := L) (m₁ := m₁) (m₁' := m₁') (m₀ := m₀) (m₀' := m₀') hm j
  have heq : (e : CTorus d L N₁' m₁' K → CTorus d L N₁ m₁ K) = castT (castSide_eq hc K) :=
    funext he
  rw [heq]
  constructor
  · exact isPolyDom_cast_cellSide (castSide_eq hc K) hcs
  · intro hX
    have hback := isPolyDom_cast_cellSide (castSide_eq hc K).symm hcs.symm hX
    simpa [Set.image_image, Function.comp_def, castT_castT] using hback

end PolyEquiv

section Size

variable {d L N₁ N₁' m₁ m₁' K m₀ m₀' j : ℕ}

/-- The size of a polymer is unchanged under the cast. -/
theorem sizeJ_castEquiv (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hm : m₀' + m₁' = m₀ + m₁)
    {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K} (he : ∀ x, e x = castT (castSide_eq hc K) x)
    (X : Set (CTorus d L N₁' m₁' K)) :
    sizeJ (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) m₀' j X =
      sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j (e '' X) := by
  have hcs := cellSide_eq_of_add (L := L) (m₁ := m₁) (m₁' := m₁') (m₀ := m₀) (m₀' := m₀') hm j
  have hsw : ∀ α : Type, (scaleW L m₀' m₁' j : α → α → ℝ) = scaleW L m₀ m₁ j := by
    intro α
    funext a b
    unfold scaleW
    congr 2
    omega
  let F : (n : ℕ) → Set (Torus d n) → ℝ := fun n Y =>
    sInf {c : ℝ | ∃ (𝒦 : Set (Torus d n)) (W : Finset (Torus d n))
        (E : Finset (Torus d n × Torus d n)),
      ((∀ b ∈ 𝒦, Aligned (cellSide L m₀ m₁ j) b ∧
          Localization.box b (L * cellSide L m₀ m₁ j) ⊆ Y) ∧
        ∀ z ∈ Y, ∃ b ∈ 𝒦, z ∈ Localization.box b (L * cellSide L m₀ m₁ j)) ∧
      ConnStruct W E ∧ (↑W ⊆ Y) ∧
      (∀ b ∈ 𝒦, ∃ x ∈ W, x ∈ Localization.box b (L * cellSide L m₀ m₁ j)) ∧
      c = bondCost (scaleW L m₀ m₁ j) E}
  have hF : ∀ {n n' : ℕ} (h : n = n') (Y : Set (Torus d n)),
      F n' (castT h '' Y) = F n Y := by
    intro n n' h Y
    cases h
    have hc : (castT (d := d) (rfl : n = n)) = (id : Torus d n → Torus d n) := rfl
    rw [hc, Set.image_id]
  have heq : (e : CTorus d L N₁' m₁' K → CTorus d L N₁ m₁ K) = castT (castSide_eq hc K) :=
    funext he
  rw [heq]
  have h1 : sizeJ (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) m₀' j X =
      F ((N₁' * L ^ m₁') * L ^ K) X := by
    unfold sizeJ treeLenCovOne ChosenOne MeetsOne
    simp only [hcs, hsw]
    rfl
  have h2 : sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j (castT (castSide_eq hc K) '' X) =
      F ((N₁ * L ^ m₁) * L ^ K) (castT (castSide_eq hc K) '' X) := rfl
  rw [h1, h2, hF]

end Size

end Balaban.Fluctuation
