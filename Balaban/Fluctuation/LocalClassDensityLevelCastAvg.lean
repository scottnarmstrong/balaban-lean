/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelCastTerms

/-!
# Group averages across the cast (`LocalClassDensityLevelCastAvg`)

The cast `e` conjugates the symmetry group of the finer torus onto that of the torus `(N₁, m₁)`
(`castEquiv_pavingSymGroup`), intertwines the actions on fields and the rotations, so the averages
over the two groups of transported summands agree.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField

section Avg

variable {d L N₁ N₁' m₁ m₁' K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁']

variable {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K}

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem permCongrHom_apply' (s : Equiv.Perm (CTorus d L N₁' m₁' K)) (x : CTorus d L N₁' m₁' K) :
    (e.permCongrHom s) (e x) = e (s x) := by
  change e (s (e.symm (e x))) = e (s x)
  rw [Equiv.symm_apply_apply]

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem permCongrHom_symm_apply' (s : Equiv.Perm (CTorus d L N₁' m₁' K))
    (x : CTorus d L N₁ m₁ K) :
    (e.permCongrHom s).symm x = e (s.symm (e.symm x)) := rfl

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
/-- The action of a conjugated permutation on pushed-forward fields. -/
theorem actField_castEquiv (s : Equiv.Perm (CTorus d L N₁' m₁' K)) (Ψ : Fld d L N₁' m₁' K N) :
    actField (e.permCongrHom s) (fun x => Ψ (e.symm x)) =
      fun x => (actField s Ψ) (e.symm x) := by
  funext x
  change Ψ (e.symm ((e.permCongrHom s).symm x)) = Ψ (s.symm (e.symm x))
  rw [permCongrHom_symm_apply', Equiv.symm_apply_apply]

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
/-- Rotations commute with the cast of fields. -/
theorem rotField_castEquiv (R : Matrix (Fin N) (Fin N) ℂ) (Ψ : Fld d L N₁' m₁' K N) :
    rotField R (fun x => Ψ (e.symm x)) = fun x => (rotField R Ψ) (e.symm x) := rfl

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem permCongrHom_inv_apply (s : Equiv.Perm (CTorus d L N₁' m₁' K)) (x : CTorus d L N₁ m₁ K) :
    ((e.permCongrHom s)⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) x = e (s⁻¹ (e.symm x)) := rfl

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem permCongrHom_inv_apply_cast (s : Equiv.Perm (CTorus d L N₁' m₁' K))
    (y : CTorus d L N₁' m₁' K) :
    ((e.permCongrHom s)⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) (e y) =
      e ((s⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) y) := by
  rw [permCongrHom_inv_apply, Equiv.symm_apply_apply]

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
theorem permCongrHom_inv_image (s : Equiv.Perm (CTorus d L N₁' m₁' K))
    (Y : Set (CTorus d L N₁' m₁' K)) :
    ((e.permCongrHom s)⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' (e '' Y) = e '' ((s⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨s⁻¹ y, ⟨y, hy, rfl⟩, (permCongrHom_inv_apply_cast s y).symm⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, permCongrHom_inv_apply_cast s y⟩

omit [NeZero L] [NeZero N₁] [NeZero N₁'] in
/-- The average over a group of the transported summands is the average over the conjugated
group. -/
theorem avg_castEquiv {M : Type*} [AddCommGroup M] [Module ℂ M]
    {S' : Subgroup (Equiv.Perm (CTorus d L N₁' m₁' K))}
    {S : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))}
    (hS : Subgroup.map e.permCongrHom S' = S) [Fintype S'] [Fintype S]
    (F : Equiv.Perm (CTorus d L N₁ m₁ K) → M) :
    ((Fintype.card S : ℂ))⁻¹ • ∑ s : S, F s =
      ((Fintype.card S' : ℂ))⁻¹ • ∑ s : S', F (e.permCongrHom s) := by
  have hiff : ∀ s' : Equiv.Perm (CTorus d L N₁' m₁' K), e.permCongrHom s' ∈ S ↔ s' ∈ S' := by
    intro s'
    rw [← hS]
    exact Subgroup.mem_map_iff_mem e.permCongrHom.injective
  let Φ : S' ≃ S := (e.permCongrHom.toEquiv).subtypeEquiv (fun s' => (hiff s').symm)
  have hcard : Fintype.card S = Fintype.card S' := (Fintype.card_congr Φ).symm
  rw [hcard]
  congr 1
  exact (Fintype.sum_equiv Φ _ _ (fun s => rfl)).symm

end Avg

section Cpl

variable {d L N₁ N₁' m₁ m₁' K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁']
  (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
  {e : CTorus d L N₁' m₁' K ≃ CTorus d L N₁ m₁ K} (he : ∀ x, e x = castT (castSide_eq hc K) x)

include he

omit [NeZero N₁] in
theorem preimage_image_castEquiv (Y' : Set (CTorus d L N₁' m₁' K)) :
    {x' : CTorus d L N₁' m₁' K |
      (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ K) ∈ e '' Y'} = Y' := by
  ext x'
  simp only [Set.mem_ofPred_eq, torusCast_eq_equiv hc he]
  exact e.injective.mem_set_image

/-- The transported local projection is the local projection of the cast sets. -/
theorem cpl_castEquiv
    {cpl : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N}
    {cpl' : Set (CTorus d L N₁' m₁' K) → Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N →
      Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N}
    (hcpl : ∀ Y p, cpl Y p =
      (fun x => (cpl' {x' | (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ K) ∈ Y}
          (fun x' => p.1 (SmallField.GsSpec.torusCast x'),
            fun x' => p.2 (SmallField.GsSpec.torusCast x'))).1 (SmallField.GsSpec.torusCast x),
        fun x => (cpl' {x' | (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ K) ∈ Y}
          (fun x' => p.1 (SmallField.GsSpec.torusCast x'),
            fun x' => p.2 (SmallField.GsSpec.torusCast x'))).2 (SmallField.GsSpec.torusCast x)))
    (Y' : Set (CTorus d L N₁' m₁' K)) (q : Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N) :
    cpl (e '' Y') (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)) =
      (fun x => (cpl' Y' q).1 (e.symm x), fun x => (cpl' Y' q).2 (e.symm x)) := by
  rw [hcpl, preimage_image_castEquiv hc he]
  have hq : ((fun x' => (fun x => q.1 (e.symm x)) (SmallField.GsSpec.torusCast x' :
      CTorus d L N₁ m₁ K), fun x' => (fun x => q.2 (e.symm x))
        (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ K)) :
      Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N) = q := by
    refine Prod.ext (funext fun x' => ?_) (funext fun x' => ?_)
    · simp only [torusCast_eq_equiv hc he, Equiv.symm_apply_apply]
    · simp only [torusCast_eq_equiv hc he, Equiv.symm_apply_apply]
  rw [hq]
  simp only [torusCast_eq_equiv_symm hc he]

section Sums

variable {τι : Type*} (𝒯E : Finset τι)
  {cpl : Set (CTorus d L N₁ m₁ K) → Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N →
    Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N}
  {cpl' : Set (CTorus d L N₁' m₁' K) → Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N →
    Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N}
  (hcpl : ∀ Y p, cpl Y p =
      (fun x => (cpl' {x' | (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ K) ∈ Y}
          (fun x' => p.1 (SmallField.GsSpec.torusCast x'),
            fun x' => p.2 (SmallField.GsSpec.torusCast x'))).1 (SmallField.GsSpec.torusCast x),
        fun x => (cpl' {x' | (SmallField.GsSpec.torusCast x' : CTorus d L N₁ m₁ K) ∈ Y}
          (fun x' => p.1 (SmallField.GsSpec.torusCast x'),
            fun x' => p.2 (SmallField.GsSpec.torusCast x'))).2 (SmallField.GsSpec.torusCast x)))
  {S' : Subgroup (Equiv.Perm (CTorus d L N₁' m₁' K))}
  {S : Subgroup (Equiv.Perm (CTorus d L N₁ m₁ K))}
  (hS : Subgroup.map e.permCongrHom S' = S) [Fintype S'] [Fintype S]

include hcpl hS

/-- The group average of the energy terms is transported by the cast. -/
theorem AE_castEquiv
    {Tl : τι → CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ}
    {Tl' : τι → CTorus d L N₁' m₁' K → Set (CTorus d L N₁' m₁' K) →
      Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N → ℂ}
    (hTl' : ∀ τ z Y q, Tl' τ z Y q =
      Tl τ (e z) (e '' Y) (fun x => q.1 (e.symm x), fun x => q.2 (e.symm x)))
    {AE : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ}
    {AE' : CTorus d L N₁' m₁' K → Set (CTorus d L N₁' m₁' K) →
      Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N → ℂ}
    (hAE : ∀ z Y p, AE z Y p = ((Fintype.card S : ℂ))⁻¹ • ∑ s : S,
        ∑ τ ∈ 𝒯E, Tl τ (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ :
            Equiv.Perm (CTorus d L N₁ m₁ K)) z)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ p.2)))
    (hAE' : ∀ z Y p, AE' z Y p = ((Fintype.card S' : ℂ))⁻¹ • ∑ s : S',
        ∑ τ ∈ 𝒯E, Tl' τ (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ :
            Equiv.Perm (CTorus d L N₁' m₁' K)) z)
          (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y)
          (cpl' (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ :
              Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ p.1,
              actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ p.2)))
    (z : CTorus d L N₁' m₁' K) (Y : Set (CTorus d L N₁' m₁' K))
    (p : Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N) :
    AE (e z) (e '' Y) (fun x => p.1 (e.symm x), fun x => p.2 (e.symm x)) = AE' z Y p := by
  rw [hAE, hAE']
  refine (avg_castEquiv (M := ℂ) hS
    (fun σ : Equiv.Perm (CTorus d L N₁ m₁ K) => ∑ τ ∈ 𝒯E,
      Tl τ ((σ⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) (e z))
        ((σ⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' (e '' Y))
        (cpl ((σ⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' (e '' Y))
          (actField σ⁻¹ (fun x => p.1 (e.symm x)), actField σ⁻¹ (fun x => p.2 (e.symm x)))))).trans ?_
  congr 1
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [hTl', permCongrHom_inv_apply_cast, permCongrHom_inv_image, ← map_inv,
    actField_castEquiv, actField_castEquiv]
  have hh := cpl_castEquiv hc he hcpl
    (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y)
    (actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ p.1,
      actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ p.2)
  dsimp only at hh
  rw [hh]

/-- The group average of the source terms is transported by the cast. -/
theorem AM_castEquiv
    {TM : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × Fld d L N₁ m₁ K N → Fin N → ℂ}
    {TM' : CTorus d L N₁' m₁' K → Set (CTorus d L N₁' m₁' K) →
      (Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N) × Fld d L N₁' m₁' K N → Fin N → ℂ}
    (hTM' : ∀ x Y q, TM' x Y q = TM (e x) (e '' Y)
      ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z)))
    {AM : CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) →
      (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) × Fld d L N₁ m₁ K N → Fin N → ℂ}
    {AM' : CTorus d L N₁' m₁' K → Set (CTorus d L N₁' m₁' K) →
      (Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N) × Fld d L N₁' m₁' K N → Fin N → ℂ}
    (hAM : ∀ x Y q, AM x Y q = ((Fintype.card S : ℂ))⁻¹ • ∑ s : S,
        TM (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) x)
          (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
          (cpl (((s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁ m₁ K))⁻¹ q.2))
    (hAM' : ∀ x Y q, AM' x Y q = ((Fintype.card S' : ℂ))⁻¹ • ∑ s : S',
        TM' (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) x)
          (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y)
          (cpl' (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ :
              Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y)
            (actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ q.1.1,
              actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ q.1.2),
            actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ q.2))
    (x : CTorus d L N₁' m₁' K) (Y : Set (CTorus d L N₁' m₁' K))
    (q : (Fld d L N₁' m₁' K N × Fld d L N₁' m₁' K N) × Fld d L N₁' m₁' K N) :
    AM (e x) (e '' Y)
      ((fun z => q.1.1 (e.symm z), fun z => q.1.2 (e.symm z)), fun z => q.2 (e.symm z)) =
      AM' x Y q := by
  rw [hAM, hAM']
  refine (avg_castEquiv (M := Fin N → ℂ) hS
    (fun σ : Equiv.Perm (CTorus d L N₁ m₁ K) =>
      TM ((σ⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) (e x))
        ((σ⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' (e '' Y))
        (cpl ((σ⁻¹ : Equiv.Perm (CTorus d L N₁ m₁ K)) '' (e '' Y))
          (actField σ⁻¹ (fun z => q.1.1 (e.symm z)), actField σ⁻¹ (fun z => q.1.2 (e.symm z))),
          actField σ⁻¹ (fun z => q.2 (e.symm z))))).trans ?_
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hTM', permCongrHom_inv_apply_cast, permCongrHom_inv_image, ← map_inv,
    actField_castEquiv, actField_castEquiv, actField_castEquiv]
  have hh := cpl_castEquiv hc he hcpl
    (((s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ : Equiv.Perm (CTorus d L N₁' m₁' K)) '' Y)
    (actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ q.1.1,
      actField (s : Equiv.Perm (CTorus d L N₁' m₁' K))⁻¹ q.1.2)
  dsimp only at hh
  rw [hh]

end Sums

end Cpl

end Balaban.Fluctuation
