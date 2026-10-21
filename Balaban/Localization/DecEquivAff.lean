/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivTranslate
public import Balaban.LargeField.Region.SymmLat

/-!
# Affine lattice isometries and the bumps of the cover (core of `CoverSymm.ofTranslate`)

An affine lattice isometry `A` of the torus `Torus d n` (`AffIso`: permutation of the directions,
reversal of some, translation) maps the cell of side `a` with base `y₀` onto the cell with base
`A y₀ - (a - 1) ·flip` (`AffIso.image_lblock`).  The periodized bumps are covariant under `A` with
the bases transported in this way (`bump_aff`, `cubeBump_aff`), and so are the boxes `InBox`
(`inBox_aff_iff`); translations are the instance `A = (id, 0, t)` (`cubeBump_translate`,
`inBox_add_iff`).
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Finset

/-! ### The spline is even -/

theorem tp_eq_abs (x : ℝ) : tp x = (x ^ 2 + x * |x|) / 2 := by
  unfold tp
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_right h, abs_of_nonpos h]; ring

theorem bsp_neg' (t : ℝ) : bsp (-t) = bsp t := by
  unfold bsp
  simp only [tp_eq_abs]
  have e1 : |-t + 3 / 2| = |t - 3 / 2| := by rw [← abs_neg]; ring_nf
  have e2 : |-t + 1 / 2| = |t - 1 / 2| := by rw [← abs_neg]; ring_nf
  have e3 : |-t - 1 / 2| = |t + 1 / 2| := by rw [← abs_neg]; ring_nf
  have e4 : |-t - 3 / 2| = |t + 3 / 2| := by rw [← abs_neg]; ring_nf
  rw [e1, e2, e3, e4]
  ring

theorem perN_neg' (r α : ℝ) : perN r (-α) = perN r α := by
  unfold perN
  rw [← finsum_comp_equiv (Equiv.neg ℤ) (f := fun p : ℤ => bsp (α + p * r))]
  refine finsum_congr fun p => ?_
  simp only [Equiv.neg_apply]
  rw [← bsp_neg']
  congr 1
  push_cast; ring

/-! ### Values of affine images -/

theorem exists_val_eq {n : ℕ} [NeZero n] (z : ZMod n) (c : ℤ) (h : z = (c : ZMod n)) :
    ∃ e : ℤ, (z.val : ℤ) = c + n * e := by
  have h1 : ((z.val : ℤ) : ZMod n) = ((c : ℤ) : ZMod n) := by
    rw [← h]; simp
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  exact ⟨-e, by linarith⟩

theorem perFac_core {n : ℕ} [NeZero n] (lam : ℕ) (hlam : 0 < lam) (s x y : ZMod n) (b : Bool) :
    perN ((n : ℝ) / lam)
        ((((s + AffIso.sgn n b * x).val : ℕ) -
          ((((s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0)).val : ℕ) : ℝ) +
            ((lam : ℝ) - 1) / 2)) / lam) =
      perN ((n : ℝ) / lam) ((((x.val : ℕ) : ℝ) - (((y.val : ℕ) : ℝ) + ((lam : ℝ) - 1) / 2)) / lam) := by
  have hl : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hl1 : 1 ≤ lam := hlam
  obtain ⟨e1, h1⟩ := exists_val_eq (s + AffIso.sgn n b * x)
    ((s.val : ℤ) + (if b then -1 else 1) * (x.val : ℤ)) (by
      cases b <;> simp [AffIso.sgn])
  obtain ⟨e2, h2⟩ := exists_val_eq (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0))
    ((s.val : ℤ) + (if b then -1 else 1) * (y.val : ℤ) - (if b then ((lam - 1 : ℕ) : ℤ) else 0)) (by
      cases b <;> simp [AffIso.sgn])
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h1 h2 ⊢
    have key : ((((s + AffIso.sgn n false * x).val : ℕ) : ℝ) -
        ((((s + AffIso.sgn n false * y - 0).val : ℕ) : ℝ) + ((lam : ℝ) - 1) / 2)) / lam =
        (((x.val : ℕ) : ℝ) - (((y.val : ℕ) : ℝ) + ((lam : ℝ) - 1) / 2)) / lam +
          (e1 - e2 : ℤ) * ((n : ℝ) / lam) := by
      have a1 : ((s + AffIso.sgn n false * x).val : ℝ) = (s.val : ℝ) + (x.val : ℝ) + n * e1 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) h1
        push_cast at this; linarith
      have a2 : ((s + AffIso.sgn n false * y - 0).val : ℝ) = (s.val : ℝ) + (y.val : ℝ) + n * e2 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) h2
        push_cast at this; linarith
      rw [a1, a2]; push_cast; field_simp; ring
    rw [key]
    exact perN_add_int_mul _ _ _
  · simp only [↓reduceIte] at h1 h2 ⊢
    have key : ((((s + AffIso.sgn n true * x).val : ℕ) : ℝ) -
        ((((s + AffIso.sgn n true * y - ((lam - 1 : ℕ) : ZMod n)).val : ℕ) : ℝ) +
          ((lam : ℝ) - 1) / 2)) / lam =
        -((((x.val : ℕ) : ℝ) - (((y.val : ℕ) : ℝ) + ((lam : ℝ) - 1) / 2)) / lam) +
          (e1 - e2 : ℤ) * ((n : ℝ) / lam) := by
      have a1 : ((s + AffIso.sgn n true * x).val : ℝ) = (s.val : ℝ) - (x.val : ℝ) + n * e1 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) h1
        push_cast at this; linarith
      have a2 : ((s + AffIso.sgn n true * y - ((lam - 1 : ℕ) : ZMod n)).val : ℝ) =
          (s.val : ℝ) - (y.val : ℝ) - ((lam : ℝ) - 1) + n * e2 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) h2
        have c1 : ((((lam - 1 : ℕ) : ℤ)) : ℝ) = (lam : ℝ) - 1 := by
          rw [Int.cast_natCast, Nat.cast_sub hl1]; simp
        simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_neg, Int.cast_one,
          Int.cast_sub, c1] at this
        linarith
      rw [a1, a2]; push_cast; field_simp; ring
    rw [key, perN_add_int_mul, perN_neg']

/-! ### The bump of the image cube -/

/-- **The base of the image of the cell with base `y`** (side `lam`): `A y - (lam - 1)` in the
reversed directions (`AffIso.image_lblock`). -/
def baseImg {d n : ℕ} (A : AffIso d n) (lam : ℕ) (y : Torus d n) : Torus d n := fun i =>
  A.toFun y i - (if A.flip (A.perm.symm i) then ((lam - 1 : ℕ) : ZMod n) else 0)

section Bump

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- **The periodized bump is covariant under an affine lattice isometry**, with the base of the
cube moved to the base of the image cube. -/
theorem bump_aff (A : AffIso d (N₀ * L ^ k)) (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) :
    bump m (baseImg A (L ^ m) y0) (A.toFun x) = bump m y0 x := by
  unfold bump
  rw [← Equiv.prod_comp A.perm (fun i => perFac m (baseImg A (L ^ m) y0) i (((A.toFun x) i).val : ℝ))]
  refine Finset.prod_congr rfl fun μ _ => ?_
  have hL : 0 < L ^ m := by have := NeZero.pos L; positivity
  have h := perFac_core (n := N₀ * L ^ k) (L ^ m) hL (A.shift (A.perm μ)) (x μ) (y0 μ)
    (A.flip μ)
  unfold perFac bumpCentre
  simp only [baseImg, AffIso.toFun, Equiv.symm_apply_apply]
  push_cast at h ⊢
  exact h

end Bump

section Cube

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

theorem cubeBump_aff (A : AffIso d ((N₁ * L ^ m₁) * L ^ K)) (j : ℕ) (y0 x : CTorus d L N₁ m₁ K) :
    cubeBump m₁ j (baseImg A (L ^ (j + m₁)) y0) (A.toFun x) = cubeBump m₁ j y0 x := by
  unfold cubeBump bump
  have hL : 0 < L ^ (j + m₁) := by have := NeZero.pos L; positivity
  rw [← Equiv.prod_comp A.perm (fun i => perFac (j + m₁) (tor m₁ (baseImg A (L ^ (j + m₁)) y0)) i
    ((((tor m₁ (A.toFun x)) i).val : ℕ) : ℝ))]
  refine Finset.prod_congr rfl fun μ _ => ?_
  have h := perFac_core (n := (N₁ * L ^ m₁) * L ^ K) (L ^ (j + m₁)) hL (A.shift (A.perm μ)) (x μ)
    (y0 μ) (A.flip μ)
  have hs : ((N₁ * L ^ (K + m₁) : ℕ) : ℝ) = (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) := by
    push_cast; ring
  unfold perFac bumpCentre
  simp only [tor_val, baseImg, AffIso.toFun, Equiv.symm_apply_apply, hs]
  push_cast at h ⊢
  exact h

end Cube

end Balaban.Localization.DecEquiv
