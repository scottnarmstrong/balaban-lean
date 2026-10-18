/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelCastDom

/-!
# Local sums of the terms across the cast (`LocalClassDensityLevelCastTerms`)

For terms `Tm'` on the torus `(N₁', m₁')` that are the cast of terms `Tm` on the torus `(N₁, m₁)`
(`Tm'.E j y' Y' Ψ h = Tm.E j (e y') (e '' Y') (Ψ ∘ e⁻¹) (h ∘ e⁻¹)`, likewise `M`), the sums over
the polymers of a site, the local sums `Eloc`, `Mloc` and the density `Edens` correspond.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField

section Local

variable {d L N₁ N₁' m₁ m₁' K N m₀ m₀' : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ : ℝ}
  (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₀' + m₁' = m₀ + m₁)
  {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K} (he : ∀ x, e x = castT (castSide_eq hc K) x)

include hc hm he

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem polysAt_castEquiv (j : ℕ) (y : CTorus d L N₁' m₁' K) :
    polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j (e y) =
      (fun Y => e '' Y) '' polysAt (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) m₀' j y := by
  ext Y
  constructor
  · rintro ⟨hY, hy⟩
    refine ⟨e ⁻¹' Y, ⟨?_, hy⟩, Set.image_preimage_eq _ e.surjective⟩
    rw [isPolyDom_castEquiv_iff hc hm he, Set.image_preimage_eq _ e.surjective]
    exact hY
  · rintro ⟨Y', ⟨hY', hy⟩, rfl⟩
    exact ⟨(isPolyDom_castEquiv_iff hc hm he Y').1 hY', ⟨y, hy, rfl⟩⟩

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem finsum_polysAt_castEquiv {M : Type*} [AddCommMonoid M] (j : ℕ)
    (y : CTorus d L N₁' m₁' K) (f : Set (CTorus d L N₁ m₁ K) → M) :
    ∑ᶠ Y ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j (e y), f Y =
      ∑ᶠ Y ∈ polysAt (L := L) (N₁ := N₁') (m₁ := m₁') (k := K) m₀' j y, f (e '' Y) := by
  rw [polysAt_castEquiv hc hm he]
  exact finsum_mem_image (g := fun Y => e '' Y) (f := f)
    (fun _ _ _ _ h => Set.image_injective.2 e.injective h)

variable {Tm : Terms d L N₁ m₁ K N ϱ} {Tm' : Terms d L N₁' m₁' K N ϱ}

/-- The local energy sum of the cast terms. -/
theorem Eloc_castEquiv
    (hE : ∀ j y Y Ψ h, Tm'.E j y Y Ψ h =
      Tm.E j (e y) (e '' Y) (fun x => Ψ (e.symm x)) (fun x => h (e.symm x)))
    (j : ℕ) (y : CTorus d L N₁' m₁' K) (Ψ h : Fld d L N₁' m₁' K N) :
    Eloc m₀' Tm' j y Ψ h =
      Eloc m₀ Tm j (e y) (fun x => Ψ (e.symm x)) (fun x => h (e.symm x)) := by
  unfold Eloc
  rw [finsum_polysAt_castEquiv hc hm he]
  exact finsum_mem_congr rfl fun Y _ => hE _ _ _ _ _

/-- The local observable sum of the cast terms. -/
theorem Mloc_castEquiv
    (hM : ∀ j x Y Ψ h g, Tm'.M j x Y Ψ h g =
      Tm.M j (e x) (e '' Y) (fun z => Ψ (e.symm z)) (fun z => h (e.symm z))
        (fun z => g (e.symm z)))
    (j : ℕ) (x : CTorus d L N₁' m₁' K) (Ψ h g : Fld d L N₁' m₁' K N) :
    Mloc m₀' Tm' j x Ψ h g =
      Mloc m₀ Tm j (e x) (fun z => Ψ (e.symm z)) (fun z => h (e.symm z))
        (fun z => g (e.symm z)) := by
  unfold Mloc
  rw [finsum_polysAt_castEquiv hc hm he]
  exact finsum_mem_congr rfl fun Y _ => hM _ _ _ _ _ _

/-- The density of the cast terms. -/
theorem Edens_castEquiv
    (hE : ∀ j y Y Ψ h, Tm'.E j y Y Ψ h =
      Tm.E j (e y) (e '' Y) (fun x => Ψ (e.symm x)) (fun x => h (e.symm x)))
    (j : ℕ) (Ψ h : Fld d L N₁' m₁' K N) :
    Edens m₀' Tm' j Ψ h =
      Edens m₀ Tm j (fun x => Ψ (e.symm x)) (fun x => h (e.symm x)) := by
  classical
  unfold Edens
  refine Finset.sum_equiv e (fun y => ?_) (fun y _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (castEquiv_aligned_iff hc he _ y).symm
  · exact Eloc_castEquiv hc hm he hE j y Ψ h

end Local

end Balaban.Fluctuation
