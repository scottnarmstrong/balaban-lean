module

public import Balaban.LargeField.Region.Step

/-!
# Lattice isometries of cube tori and the neighbourhood calculus

An *affine lattice isometry* of the torus `Torus d n` is a signed permutation of the coordinates
composed with a translation (`AffIso`): `x ↦ (shift_i + ε_i x_{π⁻¹ i})_i`, `ε_i = ±1`.  Such a map
preserves the index distance (`AffIso.supDist_eq`) and maps `L`-blocks to `L`-blocks
(`AffIso.image_lblock`), hence commutes with the neighbourhoods `nbhd`, `nbhdNeg`, `thick` and the
openings `opening`, `openingIn` of the region calculus (`image_nbhd`, `image_opening`,
`image_openingIn`).  A permutation of the torus is *affine* (`IsAff`) if it is of this form; a
nearest-neighbour symmetry (`NbrSymm`-type step relation) is affine (`isAff_of_step`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- An affine lattice isometry of `Torus d n`: a permutation of the coordinate directions, a choice
of orientation of each direction, and a translation. -/
structure AffIso (d n : ℕ) where
  /-- the permutation of the coordinate directions -/
  perm : Equiv.Perm (Fin d)
  /-- the directions whose orientation is reversed -/
  flip : Fin d → Bool
  /-- the translation -/
  shift : Torus d n

namespace AffIso

variable {d n : ℕ}

/-- The sign `±1` of an orientation. -/
def sgn (n : ℕ) (b : Bool) : ZMod n := if b then -1 else 1

theorem sgn_mul_self (b : Bool) : sgn n b * sgn n b = 1 := by
  cases b <;> simp [sgn]

/-- The action on the torus. -/
def toFun (A : AffIso d n) (x : Torus d n) : Torus d n :=
  fun i => A.shift i + sgn n (A.flip (A.perm.symm i)) * x (A.perm.symm i)

/-- The inverse action. -/
def invFun (A : AffIso d n) (y : Torus d n) : Torus d n :=
  fun μ => sgn n (A.flip μ) * (y (A.perm μ) - A.shift (A.perm μ))

theorem invFun_toFun (A : AffIso d n) (x : Torus d n) : A.invFun (A.toFun x) = x := by
  funext μ
  simp only [invFun, toFun, Equiv.symm_apply_apply, add_sub_cancel_left]
  rw [← mul_assoc, sgn_mul_self, one_mul]

theorem toFun_invFun (A : AffIso d n) (y : Torus d n) : A.toFun (A.invFun y) = y := by
  funext i
  simp only [invFun, toFun, Equiv.apply_symm_apply]
  rw [← mul_assoc, sgn_mul_self, one_mul]
  ring

/-- The action as a permutation of the torus. -/
def toEquiv (A : AffIso d n) : Equiv.Perm (Torus d n) where
  toFun := A.toFun
  invFun := A.invFun
  left_inv := A.invFun_toFun
  right_inv := A.toFun_invFun

@[simp] theorem toEquiv_apply (A : AffIso d n) (x : Torus d n) : A.toEquiv x = A.toFun x := rfl

theorem toFun_add_single (A : AffIso d n) (x : Torus d n) (μ : Fin d) :
    A.toFun (x + Pi.single μ 1) =
      if A.flip μ then A.toFun x - Pi.single (A.perm μ) 1 else A.toFun x + Pi.single (A.perm μ) 1 := by
  funext i
  by_cases hi : A.perm.symm i = μ
  · have hi' : i = A.perm μ := by rw [← hi]; simp
    subst hi'
    cases hf : A.flip μ <;> simp [toFun, sgn, hf, mul_add] <;> ring
  · have hi' : i ≠ A.perm μ := fun h => hi (by rw [h]; simp)
    cases hf : A.flip μ <;> simp [toFun, hi, hi']

end AffIso

/-- A permutation of the torus is an affine lattice isometry. -/
def IsAff {d n : ℕ} (e : Equiv.Perm (Torus d n)) : Prop :=
  ∃ A : AffIso d n, ∀ x, e x = A.toFun x

section Step

variable {d n : ℕ} [NeZero n]

/-- A permutation of the torus mapping the nearest-neighbour structure to itself (permuting the
directions by `π` and reversing the orientation of the directions `μ` with `fl μ`) is an affine
lattice isometry. -/
theorem isAff_of_step (e : Equiv.Perm (Torus d n)) (π : Equiv.Perm (Fin d)) (fl : Fin d → Bool)
    (hstep : ∀ x μ, e (x + Pi.single μ 1) =
      if fl μ then e x - Pi.single (π μ) 1 else e x + Pi.single (π μ) 1) : IsAff e := by
  let A : AffIso d n := ⟨π, fl, e 0⟩
  refine ⟨A, ?_⟩
  have key : ∀ s : ℕ, ∀ x : Torus d n, ∑ μ, (x μ).val = s → e x = A.toFun x := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro x hs
      by_cases hx : x = 0
      · subst hx
        have : A.toFun 0 = e 0 := by
          funext i; simp [AffIso.toFun, A]
        exact this.symm
      · obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ 0 := by
          by_contra h
          push Not at h
          exact hx (funext h)
        have hpos : 0 < (x μ).val := by
          rcases Nat.eq_zero_or_pos (x μ).val with h | h
          · exact absurd ((ZMod.val_eq_zero (x μ)).mp h) hμ
          · exact h
        let x' : Torus d n := x - Pi.single μ 1
        have hx' : x' + Pi.single μ 1 = x := sub_add_cancel _ _
        have hval : (x' μ).val + 1 = (x μ).val := by
          have h1 : x' μ = x μ - 1 := by simp [x']
          rw [h1]
          have hn : 1 ≤ (x μ).val := hpos
          have : ((x μ).val - 1 : ℕ) = ((x μ - 1 : ZMod n)).val := by
            have hlt := ZMod.val_lt (x μ)
            have e1 : ((x μ).val - 1 : ℕ) < n := by omega
            rw [← ZMod.val_natCast_of_lt e1]
            congr 1
            rw [Nat.cast_sub hn]
            simp
          omega
        have hsum : ∑ ν, (x' ν).val + 1 = s := by
          rw [← hs]
          have : ∀ ν, ν ≠ μ → (x' ν).val = (x ν).val := by
            intro ν hν; simp [x', hν]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ),
            ← Finset.add_sum_erase _ (fun ν => (x ν).val) (Finset.mem_univ μ)]
          rw [Finset.sum_congr rfl (fun ν hν => this ν (Finset.ne_of_mem_erase hν))]
          omega
        have ih' := ih (∑ ν, (x' ν).val) (by omega) x' rfl
        rw [← hx', hstep, ih', AffIso.toFun_add_single]
  exact fun x => key _ x rfl

end Step


section Metric

variable {d n : ℕ} [NeZero n]

theorem cycNorm_sgn_mul (b : Bool) (a : ZMod n) : cycNorm n (AffIso.sgn n b * a) = cycNorm n a := by
  cases b <;> simp [AffIso.sgn, cycNorm_neg]

theorem AffIso.sub_apply (A : AffIso d n) (x y : Torus d n) (i : Fin d) :
    A.toFun x i - A.toFun y i =
      sgn n (A.flip (A.perm.symm i)) * (x (A.perm.symm i) - y (A.perm.symm i)) := by
  simp only [toFun]; ring

/-- An affine lattice isometry preserves the index distance. -/
theorem AffIso.supDist_eq (A : AffIso d n) (x y : Torus d n) :
    supDist (A.toFun x) (A.toFun y) = supDist x y := by
  have key : ∀ m, supDist (A.toFun x) (A.toFun y) ≤ m ↔ supDist x y ≤ m := by
    intro m
    rw [supDist_le_iff, supDist_le_iff]
    constructor
    · intro h μ
      have := h (A.perm μ)
      rw [A.sub_apply, Equiv.symm_apply_apply, cycNorm_sgn_mul] at this
      exact this
    · intro h i
      rw [A.sub_apply, cycNorm_sgn_mul]
      exact h _
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

theorem IsAff.supDist_eq {e : Equiv.Perm (Torus d n)} (he : IsAff e) (x y : Torus d n) :
    supDist (e x) (e y) = supDist x y := by
  obtain ⟨A, hA⟩ := he
  rw [hA, hA]; exact A.supDist_eq x y

section Nbhd

variable {e : Equiv.Perm (Torus d n)} (he : ∀ x y, supDist (e x) (e y) = supDist x y)
include he

theorem image_nbhd (m : ℕ) (X : Set (Torus d n)) : e '' nbhd m X = nbhd m (e '' X) := by
  ext y'
  rw [mem_nbhd]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hd⟩ := mem_nbhd.1 hy
    exact ⟨e x, ⟨x, hx, rfl⟩, by rw [he]; exact hd⟩
  · rintro ⟨x', ⟨x, hx, rfl⟩, hd⟩
    refine ⟨e.symm y', mem_nbhd.2 ⟨x, hx, ?_⟩, by simp⟩
    have := he (e.symm y') x
    rw [← this]
    simpa using hd

theorem image_nbhdNeg (m : ℕ) (X : Set (Torus d n)) : e '' nbhdNeg m X = nbhdNeg m (e '' X) := by
  unfold nbhdNeg
  rw [Equiv.image_compl, image_nbhd he, Equiv.image_compl]

theorem image_thick (r : ℕ) (X : Set (Torus d n)) : e '' thick r X = thick r (e '' X) :=
  image_nbhd he _ X

end Nbhd

end Metric

section Blocks

variable {d n L : ℕ}

theorem cast_sub_aux (n : ℕ) {L v : ℕ} (h : v ≤ L - 1) :
    ((L - 1 - v : ℕ) : ZMod n) = ((L - 1 : ℕ) : ZMod n) - (v : ZMod n) := Nat.cast_sub h

theorem AffIso.toFun_add_cast (A : AffIso d n) (c : Torus d n) (v : Fin d → ℕ) (i : Fin d) :
    A.toFun (fun j => c j + (v j : ZMod n)) i =
      A.toFun c i + sgn n (A.flip (A.perm.symm i)) * (v (A.perm.symm i) : ZMod n) := by
  simp only [toFun]; ring

/-- The image of an `L`-block under an affine lattice isometry is an `L`-block. -/
theorem AffIso.image_lblock (A : AffIso d n) (hL : 0 < L) (c : Torus d n) :
    A.toFun '' lblock L c = lblock L (fun i => A.toFun c i -
      (if A.flip (A.perm.symm i) then ((L - 1 : ℕ) : ZMod n) else 0)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨fun i => if A.flip (A.perm.symm i) then L - 1 - v (A.perm.symm i) else v (A.perm.symm i),
      fun i => ?_, ?_⟩
    · have := hv (A.perm.symm i)
      dsimp only
      split_ifs <;> omega
    · funext i
      rw [A.toFun_add_cast]
      have := hv (A.perm.symm i)
      by_cases hf : A.flip (A.perm.symm i)
      · simp only [hf, ↓reduceIte, sgn]
        rw [cast_sub_aux n (by omega)]
        ring
      · simp [hf, sgn]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨fun μ => c μ + ((if A.flip μ then L - 1 - w (A.perm μ) else w (A.perm μ) : ℕ) : ZMod n),
      ⟨fun μ => if A.flip μ then L - 1 - w (A.perm μ) else w (A.perm μ), fun μ => ?_, rfl⟩, ?_⟩
    · have := hw (A.perm μ)
      dsimp only
      split_ifs <;> omega
    · funext i
      rw [A.toFun_add_cast]
      have := hw i
      by_cases hf : A.flip (A.perm.symm i)
      · simp only [hf, ↓reduceIte, sgn, Equiv.apply_symm_apply]
        rw [cast_sub_aux n (by omega)]
        ring
      · simp [hf, sgn]

theorem AffIso.exists_lblock_image (A : AffIso d n) (hL : 0 < L) (c' : Torus d n) :
    ∃ c, A.toFun '' lblock L c = lblock L c' := by
  refine ⟨A.invFun (fun i => c' i +
      (if A.flip (A.perm.symm i) then ((L - 1 : ℕ) : ZMod n) else 0)), ?_⟩
  rw [A.image_lblock hL, A.toFun_invFun]
  congr 1
  funext i
  ring

end Blocks

section Opening

variable {d n L : ℕ} [NeZero n] {e : Equiv.Perm (Torus d n)}
  (he : ∀ x y, supDist (e x) (e y) = supDist x y)
  (hW : ∀ c, ∃ c', e '' lblock L c = lblock L c') (hW' : ∀ c', ∃ c, e '' lblock L c = lblock L c')
include he hW hW'

theorem image_opening (m : ℕ) (F : Set (Torus d n)) :
    e '' opening L m F = opening L m (e '' F) := by
  ext y
  constructor
  · rintro ⟨z, ⟨c, hz, hd⟩, rfl⟩
    obtain ⟨c', hc'⟩ := hW c
    refine ⟨c', hc' ▸ ⟨z, hz, rfl⟩, ?_⟩
    rw [le_setDist_iff]
    rintro u hu _ ⟨v, hv, rfl⟩
    rw [← hc'] at hu
    obtain ⟨u0, hu0, rfl⟩ := hu
    rw [he]
    exact le_setDist_iff.1 hd u0 hu0 v hv
  · rintro ⟨c', hy, hd⟩
    obtain ⟨c, hc⟩ := hW' c'
    rw [← hc] at hy hd
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, ⟨c, hz, ?_⟩, rfl⟩
    rw [le_setDist_iff]
    intro u hu v hv
    have := le_setDist_iff.1 hd (e u) ⟨u, hu, rfl⟩ (e v) ⟨v, hv, rfl⟩
    rwa [he] at this

theorem image_openingIn (m : ℕ) (F Ω : Set (Torus d n)) :
    e '' openingIn L m F Ω = openingIn L m (e '' F) (e '' Ω) := by
  ext y
  constructor
  · rintro ⟨z, ⟨c, hz, hsub, hd⟩, rfl⟩
    obtain ⟨c', hc'⟩ := hW c
    refine ⟨c', hc' ▸ ⟨z, hz, rfl⟩, ?_, ?_⟩
    · rw [← hc']; exact Set.image_mono hsub
    · rw [le_setDist_iff]
      rintro u hu _ ⟨v, hv, rfl⟩
      rw [← hc'] at hu
      obtain ⟨u0, hu0, rfl⟩ := hu
      rw [he]
      exact le_setDist_iff.1 hd u0 hu0 v hv
  · rintro ⟨c', hy, hsub, hd⟩
    obtain ⟨c, hc⟩ := hW' c'
    rw [← hc] at hy hsub hd
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, ⟨c, hz, (Set.image_subset_image_iff e.injective).1 hsub, ?_⟩, rfl⟩
    rw [le_setDist_iff]
    intro u hu v hv
    have := le_setDist_iff.1 hd (e u) ⟨u, hu, rfl⟩ (e v) ⟨v, hv, rfl⟩
    rwa [he] at this

end Opening

end Balaban.LargeField
