module

public import Balaban.LargeField.Region.SymmLevel
public import Balaban.LargeField.Region.Hull
import Mathlib.Tactic.Ring

/-!
# Covariance of components, hulls and the hull closure under lattice isometries

An affine lattice isometry `A` of the cube torus `Torus d n` maps cyclic intervals of every
coordinate to cyclic intervals (`cycInt_image`), hence hulls of small sets to hulls
(`AffIso.image_hull`), preserves the side (`AffIso.side_image`), and maps the components of a finite
set to the components of its image (`AffIso.comps_map`).  Consequently it commutes with the hull
round and the hull closure (`AffIso.image_hullRound`, `AffIso.image_hullClosure`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Coord

variable {n : ℕ}

/-- The affine map `y ↦ t + ε y` of `ZMod n`, `ε = ±1`. -/
def affCoord (n : ℕ) (b : Bool) (t : ZMod n) (y : ZMod n) : ZMod n := t + AffIso.sgn n b * y

theorem affCoord_injective (b : Bool) (t : ZMod n) : Function.Injective (affCoord n b t) := by
  intro y z h
  unfold affCoord at h
  have h1 : AffIso.sgn n b * y = AffIso.sgn n b * z := add_left_cancel h
  have := congrArg (AffIso.sgn n b * ·) h1
  simpa only [← mul_assoc, AffIso.sgn_mul_self, one_mul] using this

theorem affCoord_surjective (b : Bool) (t : ZMod n) : Function.Surjective (affCoord n b t) := by
  intro y
  refine ⟨AffIso.sgn n b * (y - t), ?_⟩
  unfold affCoord
  rw [← mul_assoc, AffIso.sgn_mul_self, one_mul]; ring

/-- The image of a cyclic interval under an affine map is a cyclic interval of the same length. -/
theorem affCoord_image_cycInt (b : Bool) (t a : ZMod n) (s : ℕ) :
    affCoord n b t '' cycInt a s =
      cycInt (affCoord n b t a - (if b then ((s - 1 : ℕ) : ZMod n) else 0)) s := by
  ext y
  constructor
  · rintro ⟨z, ⟨j, hj, rfl⟩, rfl⟩
    cases b
    · refine ⟨j, hj, ?_⟩
      simp [affCoord, AffIso.sgn]; ring
    · refine ⟨s - 1 - j, by omega, ?_⟩
      have h1 : ((s - 1 - j : ℕ) : ZMod n) = ((s - 1 : ℕ) : ZMod n) - (j : ZMod n) :=
        Nat.cast_sub (by omega)
      rw [h1]
      simp [affCoord, AffIso.sgn]; ring
  · rintro ⟨j, hj, rfl⟩
    cases b
    · refine ⟨a + j, ⟨j, hj, rfl⟩, ?_⟩
      simp [affCoord, AffIso.sgn]; ring
    · refine ⟨a + ((s - 1 - j : ℕ) : ZMod n), ⟨s - 1 - j, by omega, rfl⟩, ?_⟩
      have h1 : ((s - 1 - j : ℕ) : ZMod n) = ((s - 1 : ℕ) : ZMod n) - (j : ZMod n) :=
        Nat.cast_sub (by omega)
      rw [h1]
      simp [affCoord, AffIso.sgn]; ring

theorem affCoord_cycInt_exists (b : Bool) (t : ZMod n) (a' : ZMod n) (s : ℕ) :
    ∃ a, affCoord n b t '' cycInt a s = cycInt a' s := by
  refine ⟨AffIso.sgn n b * (a' + (if b then ((s - 1 : ℕ) : ZMod n) else 0) - t), ?_⟩
  rw [affCoord_image_cycInt]
  congr 1
  unfold affCoord
  rw [← mul_assoc, AffIso.sgn_mul_self, one_mul]; ring

/-- The hull of a set of residues: the intersection of the short cyclic intervals containing it. -/
def hullC (X : Set (ZMod n)) : Set (ZMod n) :=
  {y | ∀ (a : ZMod n) (s : ℕ), 2 * s < n → (∀ x ∈ X, x ∈ cycInt a s) → y ∈ cycInt a s}

theorem hullC_image (b : Bool) (t : ZMod n) (X : Set (ZMod n)) :
    hullC (affCoord n b t '' X) = affCoord n b t '' hullC X := by
  ext y
  obtain ⟨z, rfl⟩ := affCoord_surjective b t y
  rw [(affCoord_injective b t).mem_set_image]
  unfold hullC
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h a s hs hX
    obtain ⟨a', ha'⟩ := (⟨_, affCoord_image_cycInt b t a s⟩ : ∃ a', affCoord n b t '' cycInt a s = cycInt a' s)
    have := h a' s hs (by
      intro x hx
      obtain ⟨x0, hx0, rfl⟩ := hx
      rw [← ha']
      exact ⟨x0, hX x0 hx0, rfl⟩)
    rw [← ha'] at this
    exact (affCoord_injective b t).mem_set_image.1 this
  · intro h a' s hs hX
    obtain ⟨a, ha⟩ := affCoord_cycInt_exists b t a' s
    rw [← ha]
    refine ⟨z, h a s hs (fun x hx => ?_), rfl⟩
    have := hX (affCoord n b t x) ⟨x, hx, rfl⟩
    rw [← ha] at this
    exact (affCoord_injective b t).mem_set_image.1 this

end Coord


section Torus

variable {d n : ℕ}

theorem AffIso.toFun_apply (A : AffIso d n) (x : Torus d n) (i : Fin d) :
    A.toFun x i = affCoord n (A.flip (A.perm.symm i)) (A.shift i) (x (A.perm.symm i)) := rfl

theorem hullCoord_eq_hullC (X : Set (Torus d n)) (i : Fin d) :
    hullCoord X i = hullC ((fun x : Torus d n => x i) '' X) := by
  ext y
  simp only [hullCoord, hullC, Set.mem_ofPred_eq, Set.forall_mem_image]

theorem AffIso.hullCoord_image (A : AffIso d n) (X : Set (Torus d n)) (i : Fin d) :
    hullCoord (A.toFun '' X) i =
      affCoord n (A.flip (A.perm.symm i)) (A.shift i) '' hullCoord X (A.perm.symm i) := by
  rw [hullCoord_eq_hullC, hullCoord_eq_hullC, Set.image_image,
    ← hullC_image, Set.image_image]
  rfl

/-- A set of residues lying in a short cyclic interval. -/
def IsSmallC (Xs : Set (ZMod n)) : Prop := ∃ (a : ZMod n) (s : ℕ), 2 * s < n ∧ Xs ⊆ cycInt a s

theorem isSmallC_image (b : Bool) (t : ZMod n) (Xs : Set (ZMod n)) :
    IsSmallC (affCoord n b t '' Xs) ↔ IsSmallC Xs := by
  constructor
  · rintro ⟨a', s, hs, h⟩
    obtain ⟨a, ha⟩ := affCoord_cycInt_exists b t a' s
    refine ⟨a, s, hs, fun x hx => ?_⟩
    have := h ⟨x, hx, rfl⟩
    rw [← ha] at this
    exact (affCoord_injective b t).mem_set_image.1 this
  · rintro ⟨a, s, hs, h⟩
    refine ⟨affCoord n b t a - (if b then ((s - 1 : ℕ) : ZMod n) else 0), s, hs, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← affCoord_image_cycInt]
    exact ⟨x, h hx, rfl⟩

theorem isSmall_iff_proj (X : Set (Torus d n)) :
    IsSmall X ↔ ∀ i, IsSmallC ((fun x : Torus d n => x i) '' X) := by
  unfold IsSmall IsSmallC
  refine forall_congr' fun i => exists_congr fun a => exists_congr fun s => and_congr_right fun _ => ?_
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  · intro h x hx
    exact h ⟨x, hx, rfl⟩

theorem forall_fin_perm_iff {d : ℕ} (e : Equiv.Perm (Fin d)) (P : Fin d → Prop) :
    (∀ i, P i) ↔ ∀ μ, P (e μ) :=
  ⟨fun h μ => h _, fun h i => by simpa using h (e.symm i)⟩

theorem AffIso.isSmall_image (A : AffIso d n) (X : Set (Torus d n)) :
    IsSmall (A.toFun '' X) ↔ IsSmall X := by
  rw [isSmall_iff_proj, isSmall_iff_proj, forall_fin_perm_iff A.perm]
  refine forall_congr' fun μ => ?_
  have : (fun x : Torus d n => x (A.perm μ)) '' (A.toFun '' X) =
      affCoord n (A.flip μ) (A.shift (A.perm μ)) '' ((fun x : Torus d n => x μ) '' X) := by
    rw [Set.image_image, Set.image_image]
    refine Set.image_congr (fun x _ => ?_)
    simp only [AffIso.toFun_apply, Equiv.symm_apply_apply]
  rw [this]
  exact isSmallC_image _ _ _


theorem AffIso.side_image (A : AffIso d n) (X : Set (Torus d n)) :
    side (A.toFun '' X) = side X := by
  unfold side
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    rw [A.hullCoord_image, Set.ncard_image_of_injective _ (affCoord_injective _ _)]
    exact Finset.le_sup (f := fun i : Fin d => (hullCoord X i).ncard) (Finset.mem_univ _)
  · refine Finset.sup_le fun μ _ => ?_
    have : (hullCoord X μ).ncard = (hullCoord (A.toFun '' X) (A.perm μ)).ncard := by
      rw [A.hullCoord_image, Set.ncard_image_of_injective _ (affCoord_injective _ _),
        Equiv.symm_apply_apply]
    rw [this]
    exact Finset.le_sup (f := fun i : Fin d => (hullCoord (A.toFun '' X) i).ncard)
      (Finset.mem_univ _)

theorem AffIso.hull_image (A : AffIso d n) (X : Set (Torus d n)) :
    hull (A.toFun '' X) = A.toFun '' hull X := by
  ext y
  obtain ⟨z, rfl⟩ : ∃ z, A.toFun z = y := ⟨A.invFun y, A.toFun_invFun y⟩
  rw [A.toFun_injective.mem_set_image]
  unfold hull
  simp only [Set.mem_ofPred_eq]
  rw [forall_fin_perm_iff A.perm]
  refine forall_congr' fun μ => ?_
  rw [A.hullCoord_image, A.toFun_apply, Equiv.symm_apply_apply,
    (affCoord_injective _ _).mem_set_image]

end Torus

section Comps

variable {d n : ℕ} [NeZero n] (e : Equiv.Perm (Torus d n))
  (he : ∀ x y, supDist (e x) (e y) = supDist x y)
include he

theorem linked_map {ω : ℕ} (X : Set (Torus d n)) (x y : Torus d n) :
    Linked ω (e '' X) (e x) (e y) ↔ Linked ω X x y := by
  constructor
  · intro h
    have hsymm : ∀ u v, supDist (e.symm u) (e.symm v) = supDist u v := fun u v => by
      have := he (e.symm u) (e.symm v)
      simpa using this.symm
    have key := Relation.ReflTransGen.lift (r := fun a b => a ∈ e '' X ∧ b ∈ e '' X ∧ supDist a b < ω)
      (p := fun a b => a ∈ X ∧ b ∈ X ∧ supDist a b < ω) e.symm
      (fun a b ⟨ha, hb, hd⟩ =>
        ⟨by simpa using (show e.symm a ∈ e.symm '' (e '' X) from ⟨a, ha, rfl⟩),
         by simpa using (show e.symm b ∈ e.symm '' (e '' X) from ⟨b, hb, rfl⟩),
         by rw [hsymm]; exact hd⟩)
    have := key (e x) (e y) h
    simpa [Function.onFun, Linked] using this
  · intro h
    have key := Relation.ReflTransGen.lift (r := fun a b => a ∈ X ∧ b ∈ X ∧ supDist a b < ω)
      (p := fun a b => a ∈ e '' X ∧ b ∈ e '' X ∧ supDist a b < ω) e
      (fun a b ⟨ha, hb, hd⟩ => ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, by rw [he]; exact hd⟩)
    exact key _ _ h

theorem linkClass_map {ω : ℕ} (X : Finset (Torus d n)) (x : Torus d n) :
    linkClass ω (X.map e.toEmbedding) (e x) = (linkClass ω X x).map e.toEmbedding := by
  classical
  ext y
  obtain ⟨y0, rfl⟩ := e.surjective y
  rw [mem_linkClass, Finset.mem_map_equiv, Finset.mem_map_equiv, Equiv.symm_apply_apply,
    mem_linkClass, Finset.coe_map]
  simp only [Equiv.coe_toEmbedding]
  rw [linked_map e he]

theorem comps_map {ω : ℕ} (X : Finset (Torus d n)) :
    comps ω (X.map e.toEmbedding) = (comps ω X).image (Finset.map e.toEmbedding) := by
  classical
  ext Y
  simp only [comps, Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨linkClass ω X x, ⟨x, hx, rfl⟩, (linkClass_map e he X x).symm⟩
  · rintro ⟨Y0, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, linkClass_map e he X x⟩

end Comps


section Round

variable {d n : ℕ} [NeZero n]

theorem finOf_image (A : AffIso d n) (X : Set (Torus d n)) :
    finOf (A.toFun '' X) = (finOf X).map A.toEquiv.toEmbedding := by
  ext y
  obtain ⟨y0, rfl⟩ := A.toEquiv.surjective y
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_finOf, mem_finOf]
  exact A.toFun_injective.mem_set_image

theorem AffIso.image_hullRound (A : AffIso d n) (ω b : ℕ) (X : Set (Torus d n)) :
    A.toFun '' hullRound ω b X = hullRound ω b (A.toFun '' X) := by
  unfold hullRound
  rw [Set.image_union]
  congr 1
  rw [finOf_image, comps_map A.toEquiv A.supDist_eq]
  ext y
  constructor
  · rintro ⟨z, ⟨Y, hY, hs, hside, hz⟩, rfl⟩
    refine ⟨Y.map A.toEquiv.toEmbedding, Finset.mem_image_of_mem _ hY, ?_, ?_, ?_⟩
    · rw [Finset.coe_map]; exact (A.isSmall_image _).2 hs
    · rw [Finset.coe_map]; show side (A.toFun '' (Y : Set _)) ≤ b
      rw [A.side_image]; exact hside
    · rw [Finset.coe_map]; show A.toFun z ∈ hull (A.toFun '' (Y : Set _))
      rw [A.hull_image]; exact ⟨z, hz, rfl⟩
  · rintro ⟨Y', hY', hs, hside, hz⟩
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hY'
    rw [Finset.coe_map] at hs hside hz
    have hs' : IsSmall (A.toFun '' (Y : Set _)) := hs
    have hside' : side (A.toFun '' (Y : Set _)) ≤ b := hside
    have hz' : y ∈ hull (A.toFun '' (Y : Set _)) := hz
    rw [A.hull_image] at hz'
    obtain ⟨z, hz'', rfl⟩ := hz'
    exact ⟨z, ⟨Y, hY, (A.isSmall_image _).1 hs', by rwa [A.side_image] at hside', hz''⟩, rfl⟩

theorem AffIso.image_hullClosure (A : AffIso d n) (ω b : ℕ) (X : Set (Torus d n)) :
    A.toFun '' hullClosure ω b X = hullClosure ω b (A.toFun '' X) := by
  unfold hullClosure
  generalize Fintype.card (Torus d n) = m
  induction m generalizing X with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← A.image_hullRound, ih]

end Round

end Balaban.LargeField
