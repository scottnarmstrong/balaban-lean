/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.CorrLift

/-!
# The hull of a set of cubes in the box

For a nonempty set of cubes of a torus whose sites lie in the box with a margin of one cube, the
set is small (`IsSmall`) and its side is the side `zside` of the lifted index set
(`isSmall_side`).  So `IsSmall` and `side`, which are defined by cyclic intervals of the torus,
agree for two tori at corresponding sets.
-/

@[expose] public section

open Balaban Balaban.LargeField

namespace Balaban.RootFSpine

section Hull

variable {d : ℕ}

/-- The extent `max - min + 1` of the `μ`-coordinates of a finite set of vectors of `ℤ^d`. -/
noncomputable def zspan (Λ : Finset (Fin d → ℤ)) (μ : Fin d) : ℕ :=
  if h : Λ.Nonempty then
    ((Λ.image fun u => u μ).max' (h.image _) - (Λ.image fun u => u μ).min' (h.image _) + 1).toNat
  else 0

/-- The side of a finite set of vectors of `ℤ^d`: the largest extent of a coordinate. -/
noncomputable def zside (Λ : Finset (Fin d → ℤ)) : ℕ := Finset.univ.sup (zspan Λ)

variable {P q ℓ m' : ℕ} [NeZero ℓ] [NeZero q] {cc : Fin d → ℤ}

theorem exists_extrema {A : Finset (Torus d q)} (hne : A.Nonempty) (μ : Fin d) :
    ∃ y₀ ∈ A, ∃ y₁ ∈ A, (∀ y ∈ A, clift P cc y₀ μ ≤ clift P cc y μ) ∧
      (∀ y ∈ A, clift P cc y μ ≤ clift P cc y₁ μ) := by
  obtain ⟨y₀, h0, hmin⟩ := Finset.exists_min_image A (fun y => clift P cc y μ) hne
  obtain ⟨y₁, h1, hmax⟩ := Finset.exists_max_image A (fun y => clift P cc y μ) hne
  exact ⟨y₀, h0, y₁, h1, hmin, hmax⟩

theorem zspan_cliftSet {A : Finset (Torus d q)} (hne : A.Nonempty) (μ : Fin d) {y₀ y₁ : Torus d q}
    (h0 : y₀ ∈ A) (h1 : y₁ ∈ A) (hmin : ∀ y ∈ A, clift P cc y₀ μ ≤ clift P cc y μ)
    (hmax : ∀ y ∈ A, clift P cc y μ ≤ clift P cc y₁ μ) :
    (zspan (cliftSet P cc A) μ : ℤ) = clift P cc y₁ μ - clift P cc y₀ μ + 1 := by
  have hΛ : (cliftSet P cc A).Nonempty := hne.image _
  unfold zspan
  simp only [hΛ, ↓reduceDIte]
  have e1 : ((cliftSet P cc A).image fun u => u μ).max' (hΛ.image _) = clift P cc y₁ μ := by
    apply le_antisymm
    · apply Finset.max'_le
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨y, hy, rfl⟩ := mem_cliftSet.1 hu
      exact hmax y hy
    · apply Finset.le_max'
      exact Finset.mem_image.2 ⟨_, mem_cliftSet.2 ⟨y₁, h1, rfl⟩, rfl⟩
  have e0 : ((cliftSet P cc A).image fun u => u μ).min' (hΛ.image _) = clift P cc y₀ μ := by
    apply le_antisymm
    · apply Finset.min'_le
      exact Finset.mem_image.2 ⟨_, mem_cliftSet.2 ⟨y₀, h0, rfl⟩, rfl⟩
    · apply Finset.le_min'
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨y, hy, rfl⟩ := mem_cliftSet.1 hu
      exact hmin y hy
  rw [e1, e0]
  have := hmax y₀ h0
  omega

/-- **The hull of a set of cubes in the box (with a margin).**  The set is small, and its side is
the side of the lifted index set. -/
theorem isSmall_side (hP : 2 ≤ P) (hℓ : ℓ = P * q) (hq : 4 ≤ q) {A : Finset (Torus d q)}
    (hA : GBoxK P P q ℓ m' cc A) (hne : A.Nonempty) :
    IsSmall (A : Set (Torus d q)) ∧ side (A : Set (Torus d q)) = zside (cliftSet P cc A) := by
  have hpair := fun {y y'} (hy : y ∈ A) (hy' : y' ∈ A) (μ : Fin d) =>
    GBoxK.pair hP hℓ hq hA hy hy' μ
  have hsmall : ∀ μ : Fin d, ∃ (a : ZMod q) (s : ℕ), 2 * s < q ∧
      ∀ x ∈ (A : Set (Torus d q)), x μ ∈ cycInt a s := by
    intro μ
    obtain ⟨y₀, h0, y₁, h1, hmin, hmax⟩ := exists_extrema (P := P) (cc := cc) hne μ
    have hspan := zspan_cliftSet hne μ h0 h1 hmin hmax
    set s := zspan (cliftSet P cc A) μ with hs
    have hb := hpair h1 h0 μ
    have hnn : 0 ≤ clift P cc y₁ μ - clift P cc y₀ μ := by have := hmin y₁ h1; omega
    rw [abs_of_nonneg (by omega)] at hb
    refine ⟨((clift P cc y₀ μ : ℤ) : ZMod q), s, by omega, ?_⟩
    intro x hx
    have hxA : x ∈ A := hx
    refine ⟨(clift P cc x μ - clift P cc y₀ μ).toNat, by have := hmin x hxA; have := hmax x hxA; omega, ?_⟩
    have h2 : (((clift P cc x μ - clift P cc y₀ μ).toNat : ℕ) : ℤ) =
        clift P cc x μ - clift P cc y₀ μ := by have := hmin x hxA; omega
    have h3 : x μ = ((clift P cc x μ : ℤ) : ZMod q) := by
      conv_lhs => rw [← zcast_clift P cc x]
      simp [zcast]
    rw [h3]
    have h4 : (((clift P cc x μ - clift P cc y₀ μ).toNat : ℕ) : ZMod q) =
        (((clift P cc x μ - clift P cc y₀ μ : ℤ)) : ZMod q) := by
      rw [← h2]; simp
    rw [h4]; push_cast; ring
  refine ⟨hsmall, ?_⟩
  unfold side zside
  refine Finset.sup_congr rfl fun μ _ => ?_
  obtain ⟨y₀, h0, y₁, h1, hmin, hmax⟩ := exists_extrema (P := P) (cc := cc) hne μ
  have hspan := zspan_cliftSet hne μ h0 h1 hmin hmax
  have hb := hpair h1 h0 μ
  have hnn : 0 ≤ clift P cc y₁ μ - clift P cc y₀ μ := by have := hmin y₁ h1; omega
  rw [abs_of_nonneg (by omega)] at hb
  set s := zspan (cliftSet P cc A) μ with hs
  have hX : IsSmall (A : Set (Torus d q)) := hsmall
  have hcov : ∀ x ∈ (A : Set (Torus d q)), x μ ∈ cycInt ((clift P cc y₀ μ : ℤ) : ZMod q) s := by
    intro x hx
    have hxA : x ∈ A := hx
    refine ⟨(clift P cc x μ - clift P cc y₀ μ).toNat, by have := hmin x hxA; have := hmax x hxA; omega, ?_⟩
    have h2 : (((clift P cc x μ - clift P cc y₀ μ).toNat : ℕ) : ℤ) =
        clift P cc x μ - clift P cc y₀ μ := by have := hmin x hxA; omega
    have h3 : x μ = ((clift P cc x μ : ℤ) : ZMod q) := by
      conv_lhs => rw [← zcast_clift P cc x]
      simp [zcast]
    rw [h3]
    have h4 : (((clift P cc x μ - clift P cc y₀ μ).toNat : ℕ) : ZMod q) =
        (((clift P cc x μ - clift P cc y₀ μ : ℤ)) : ZMod q) := by
      rw [← h2]; simp
    rw [h4]; push_cast; ring
  have huniq := hull_unique ⟨y₀, h0⟩ hX μ (b := ((clift P cc y₀ μ : ℤ) : ZMod q)) (t := s)
    (by omega) hcov (by
      intro a s' hs' hcov'
      have hq0 : s' ≤ q := by omega
      have p0 := (mem_cycInt_iff hq0).1 (hcov' y₀ h0)
      have p1 := (mem_cycInt_iff hq0).1 (hcov' y₁ h1)
      have e0 : y₀ μ = ((clift P cc y₀ μ : ℤ) : ZMod q) := by
        conv_lhs => rw [← zcast_clift P cc y₀]
        simp [zcast]
      have e1 : y₁ μ = ((clift P cc y₁ μ : ℤ) : ZMod q) := by
        conv_lhs => rw [← zcast_clift P cc y₁]
        simp [zcast]
      have hc : (((clift P cc y₁ μ - clift P cc y₀ μ : ℤ)) : ZMod q) =
          ((((pos a (y₁ μ) : ℤ) - (pos a (y₀ μ) : ℤ) : ℤ)) : ZMod q) := by
        push_cast
        rw [← e0, ← e1, natCast_pos, natCast_pos]; ring
      have := int_eq_of_cast_eq hc (by
        rw [abs_lt]; constructor <;> omega)
      omega)
  rw [← huniq, ncard_cycInt (by omega)]

end Hull

end Balaban.RootFSpine
