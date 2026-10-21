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

theorem exists_val_eq_int {n : ℕ} [NeZero n] (z : ZMod n) (c : ℤ) (h : z = (c : ZMod n)) :
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
  obtain ⟨e1, h1⟩ := exists_val_eq_int (s + AffIso.sgn n b * x)
    ((s.val : ℤ) + (if b then -1 else 1) * (x.val : ℤ)) (by
      cases b <;> simp [AffIso.sgn])
  obtain ⟨e2, h2⟩ := exists_val_eq_int (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0))
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

theorem val_img_core {n : ℕ} [NeZero n] (lam : ℕ) (hlam : 0 < lam) (s x y : ZMod n) (b : Bool) :
    ∃ e : ℤ, ((((s + AffIso.sgn n b * x).val : ℕ) : ℝ) -
        ((((s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0)).val : ℕ) : ℝ) +
          ((lam : ℝ) - 1) / 2)) =
      (if b then (-1 : ℝ) else 1) * (((x.val : ℕ) : ℝ) - (((y.val : ℕ) : ℝ) + ((lam : ℝ) - 1) / 2)) +
        (n : ℝ) * e := by
  have hl1 : 1 ≤ lam := hlam
  obtain ⟨e1, h1⟩ := exists_val_eq_int (s + AffIso.sgn n b * x)
    ((s.val : ℤ) + (if b then -1 else 1) * (x.val : ℤ)) (by
      cases b <;> simp [AffIso.sgn])
  obtain ⟨e2, h2⟩ := exists_val_eq_int (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0))
    ((s.val : ℤ) + (if b then -1 else 1) * (y.val : ℤ) - (if b then ((lam - 1 : ℕ) : ℤ) else 0)) (by
      cases b <;> simp [AffIso.sgn])
  refine ⟨e1 - e2, ?_⟩
  have c1 : ((((lam - 1 : ℕ) : ℤ)) : ℝ) = (lam : ℝ) - 1 := by
    rw [Int.cast_natCast, Nat.cast_sub hl1]; simp
  have a1 := congrArg (fun z : ℤ => (z : ℝ)) h1
  have a2 := congrArg (fun z : ℤ => (z : ℝ)) h2
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_sub, sub_zero, one_mul] at a1 a2 ⊢
    linarith
  · simp only [↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_neg,
      Int.cast_one, Int.cast_sub, c1] at a1 a2 ⊢
    linarith

theorem inBox_coord_aff (A : AffIso d ((N₁ * L ^ m₁) * L ^ K)) (j : ℕ) (y0 x : CTorus d L N₁ m₁ K)
    (R : ℝ) (μ : Fin d) :
    (∃ p : ℤ, |(((A.toFun x (A.perm μ)).val : ℕ) : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      ((((baseImg A (L ^ (j + m₁)) y0 (A.perm μ)).val : ℕ) : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < R) ↔
    ∃ p : ℤ, |(((x μ).val : ℕ) : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      ((((y0 μ).val : ℕ) : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < R := by
  have hL : 0 < L ^ (j + m₁) := by have := NeZero.pos L; positivity
  obtain ⟨e, he⟩ := val_img_core (n := (N₁ * L ^ m₁) * L ^ K) (L ^ (j + m₁)) hL
    (A.shift (A.perm μ)) (x μ) (y0 μ) (A.flip μ)
  have hx : (A.toFun x) (A.perm μ) = A.shift (A.perm μ) + AffIso.sgn _ (A.flip μ) * x μ := by
    simp [AffIso.toFun]
  have hy : baseImg A (L ^ (j + m₁)) y0 (A.perm μ) = A.shift (A.perm μ) + AffIso.sgn _ (A.flip μ) * y0 μ -
      (if A.flip μ then ((L ^ (j + m₁) - 1 : ℕ) : ZMod _) else 0) := by
    simp [baseImg, AffIso.toFun]
  rw [hx, hy]
  have hlam : ((L ^ (j + m₁) : ℕ) : ℝ) = (L : ℝ) ^ (j + m₁) := by push_cast; ring
  rw [hlam] at he
  generalize (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) = Nn at he ⊢
  cases hb : A.flip μ
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, one_mul] at he ⊢
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p + e, ?_⟩
      convert hp using 2
      push_cast; linarith
    · rintro ⟨p, hp⟩
      refine ⟨p - e, ?_⟩
      convert hp using 2
      push_cast; linarith
  · simp only [hb, ↓reduceIte] at he ⊢
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨-(p + e), ?_⟩
      rw [← abs_neg] at hp
      convert hp using 2
      push_cast; linarith
    · rintro ⟨p, hp⟩
      refine ⟨-(p + e), ?_⟩
      rw [← abs_neg]
      convert hp using 2
      push_cast; linarith

theorem inBox_aff_iff (A : AffIso d ((N₁ * L ^ m₁) * L ^ K)) (j : ℕ) (y0 x : CTorus d L N₁ m₁ K)
    (R : ℝ) :
    InBox m₁ j (baseImg A (L ^ (j + m₁)) y0) R (A.toFun x) ↔ InBox m₁ j y0 R x := by
  unfold InBox
  constructor
  · intro h μ
    exact (inBox_coord_aff A j y0 x R μ).1 (h (A.perm μ))
  · intro h i
    have := (inBox_coord_aff A j y0 x R (A.perm.symm i)).2 (h _)
    simpa using this

end Cube

/-! ### Cells and bases -/

section Cells

variable {d n : ℕ} [NeZero n]

theorem sameCell_iff_blockMap {a m : ℕ} (hm : n = a * m) (x y : Torus d n) :
    SameCell a x y ↔ blockMap a m x = blockMap a m y := by
  constructor
  · intro h
    funext μ
    simp only [blockMap_apply, blockCoord, h μ]
  · intro h μ
    have := congrArg (fun z : Torus d m => (z μ).val) h
    simpa only [blockMap_apply, blockCoord_val hm] using this

/-- **Cells are mapped onto cells**: an aligned affine lattice isometry preserves the relation of
lying in the same cell of side `lam`. -/
theorem sameCell_aff_iff (A : AffIso d n) {lam : ℕ} (hlam : 0 < lam) (hn : lam ∣ n)
    (hA : A.Aligned lam) (x y : Torus d n) :
    SameCell lam (A.toFun x) (A.toFun y) ↔ SameCell lam x y := by
  obtain ⟨m, hm⟩ := hn
  have hm0 : NeZero m := ⟨fun h => NeZero.ne n (by rw [hm, h, mul_zero])⟩
  rw [sameCell_iff_blockMap hm, sameCell_iff_blockMap hm, A.blockMap_toFun hm hlam hA,
    A.blockMap_toFun hm hlam hA]
  exact ⟨fun h => by simpa [AffIso.invFun_toFun] using congrArg (A.coarse lam m).invFun h,
    fun h => by rw [h]⟩

theorem baseCoord_dvd_iff {lam : ℕ} (hlam : 0 < lam) (hn : lam ∣ n) (s y : ZMod n) (b : Bool)
    (hs : lam ∣ s.val + (if b then 1 else 0)) :
    lam ∣ (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0)).val ↔
      lam ∣ y.val := by
  have hl1 : 1 ≤ lam := hlam
  obtain ⟨e, he⟩ := exists_val_eq_int (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0))
    ((s.val : ℤ) + (if b then -1 else 1) * (y.val : ℤ) - (if b then ((lam - 1 : ℕ) : ℤ) else 0)) (by
      cases b <;> simp [AffIso.sgn])
  have hnZ : (lam : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.2 hn
  have hsZ : (lam : ℤ) ∣ ((s.val : ℤ) + (if b then 1 else 0)) := by
    have := Int.natCast_dvd_natCast.2 hs
    cases b <;> simpa using this
  rw [← Int.natCast_dvd_natCast]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, sub_zero] at he hsZ ⊢
    rw [he]
    have hs' : (lam : ℤ) ∣ (s.val : ℤ) := by simpa using hsZ
    have h3 : (lam : ℤ) ∣ (n : ℤ) * e := dvd_mul_of_dvd_left hnZ e
    rw [add_assoc, Int.dvd_add_right hs', Int.dvd_add_left h3]
    exact Int.natCast_dvd_natCast
  · simp only [↓reduceIte] at he hsZ ⊢
    rw [he]
    have h3 : (lam : ℤ) ∣ (n : ℤ) * e := dvd_mul_of_dvd_left hnZ e
    have hc : ((lam - 1 : ℕ) : ℤ) = (lam : ℤ) - 1 := by push_cast [Nat.cast_sub hl1]; ring
    rw [hc]
    have e1 : (s.val : ℤ) + -1 * (y.val : ℤ) - ((lam : ℤ) - 1) + n * e =
        (((s.val : ℤ) + 1) - lam + n * e) + (-(y.val : ℤ)) := by ring
    rw [e1, Int.dvd_add_right (dvd_add (dvd_sub hsZ dvd_rfl) h3), dvd_neg]
    exact Int.natCast_dvd_natCast

theorem baseCoord_div {lam : ℕ} (hlam : 0 < lam) (hn : lam ∣ n) (s y : ZMod n) (b : Bool)
    (hs : lam ∣ s.val + (if b then 1 else 0)) (hy : lam ∣ y.val) :
    (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0)).val / lam =
      (s + AffIso.sgn n b * y).val / lam := by
  cases b
  · simp
  · simp only [↓reduceIte] at hs ⊢
    set w : ZMod n := s + AffIso.sgn n true * y with hw
    obtain ⟨e, he⟩ := exists_val_eq_int w ((s.val : ℤ) + -1 * (y.val : ℤ)) (by
      simp [hw, AffIso.sgn])
    have hnZ : (lam : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.2 hn
    have hdv : (lam : ℤ) ∣ ((w.val + 1 : ℕ) : ℤ) := by
      have h1 := Int.natCast_dvd_natCast.2 hs
      have h2 := Int.natCast_dvd_natCast.2 hy
      have h3 : (lam : ℤ) ∣ (n : ℤ) * e := dvd_mul_of_dvd_left hnZ e
      have e1 : ((w.val + 1 : ℕ) : ℤ) = (((s.val + 1 : ℕ) : ℤ) - (y.val : ℤ)) + n * e := by
        push_cast; linarith
      rw [e1]
      exact dvd_add (dvd_sub h1 h2) h3
    obtain ⟨c, hc⟩ := Int.natCast_dvd_natCast.1 hdv
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at hc; omega
      · exact h0
    have hlam1 : 1 ≤ lam := hlam
    have hwv : w.val = lam * (c - 1) + (lam - 1) := by
      have : lam * c = lam * (c - 1) + lam := by
        rw [← Nat.mul_succ]; congr 1; omega
      omega
    have hlt : lam - 1 < n := by
      have := Nat.le_of_dvd (NeZero.pos n) hn
      omega
    have hsub : (w - ((lam - 1 : ℕ) : ZMod n)).val = w.val - (lam - 1) := by
      rw [ZMod.val_sub (by rw [ZMod.val_natCast_of_lt hlt]; omega), ZMod.val_natCast_of_lt hlt]
    rw [hsub, hwv]
    have h1 : lam * (c - 1) + (lam - 1) - (lam - 1) = lam * (c - 1) := by omega
    rw [h1, Nat.mul_div_cancel_left _ hlam]
    rw [Nat.mul_add_div hlam, Nat.div_eq_of_lt (by omega)]
    simp

end Cells

section Torus

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
theorem baseImg_apply_perm (A : AffIso d n) (lam : ℕ) (y : Torus d n) (μ : Fin d) :
    baseImg A lam y (A.perm μ) = A.shift (A.perm μ) + AffIso.sgn n (A.flip μ) * y μ -
      (if A.flip μ then ((lam - 1 : ℕ) : ZMod n) else 0) := by
  simp [baseImg, AffIso.toFun]

omit [NeZero n] in
theorem toFun_apply_perm (A : AffIso d n) (y : Torus d n) (μ : Fin d) :
    A.toFun y (A.perm μ) = A.shift (A.perm μ) + AffIso.sgn n (A.flip μ) * y μ := by
  simp [AffIso.toFun]

/-- **The base of the image cell is a base iff the base of the cell is** (cells of side `lam`). -/
theorem baseImg_base_iff (A : AffIso d n) {lam : ℕ} (hlam : 0 < lam) (hn : lam ∣ n)
    (hA : A.Aligned lam) (y : Torus d n) :
    (∀ μ, (baseImg A lam y μ).val % lam = 0) ↔ ∀ μ, (y μ).val % lam = 0 := by
  constructor
  · intro h μ
    have := h (A.perm μ)
    rw [baseImg_apply_perm, ← Nat.dvd_iff_mod_eq_zero] at this
    rw [← Nat.dvd_iff_mod_eq_zero]
    exact (baseCoord_dvd_iff hlam hn _ _ _ (by simpa using hA (A.perm μ))).1 this
  · intro h i
    have hi := h (A.perm.symm i)
    obtain ⟨μ, rfl⟩ := A.perm.surjective i
    rw [Equiv.symm_apply_apply, ← Nat.dvd_iff_mod_eq_zero] at hi
    rw [baseImg_apply_perm, ← Nat.dvd_iff_mod_eq_zero]
    exact (baseCoord_dvd_iff hlam hn _ _ _ (by simpa using hA (A.perm μ))).2 hi

/-- **The base of the image cell lies in the image cell**: for a base `y`, `A y` and `baseImg A y`
are in the same cell. -/
theorem sameCell_baseImg (A : AffIso d n) {lam : ℕ} (hlam : 0 < lam) (hn : lam ∣ n)
    (hA : A.Aligned lam) (y : Torus d n) (hy : ∀ μ, (y μ).val % lam = 0) :
    SameCell lam (baseImg A lam y) (A.toFun y) := by
  intro i
  obtain ⟨μ, rfl⟩ := A.perm.surjective i
  rw [baseImg_apply_perm, toFun_apply_perm]
  exact baseCoord_div hlam hn _ _ _ (by simpa using hA (A.perm μ))
    (Nat.dvd_of_mod_eq_zero (hy μ))

end Torus

/-! ### Compatibility with the covers of two generating sets -/

section CoverAff

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The mask `(lam - 1)` in the reversed directions. -/
def baseMask {d n : ℕ} (A : AffIso d n) (lam : ℕ) : Torus d n := fun i =>
  if A.flip (A.perm.symm i) then ((lam - 1 : ℕ) : ZMod n) else 0

theorem baseImg_eq {d n : ℕ} (A : AffIso d n) (lam : ℕ) (y : Torus d n) :
    baseImg A lam y = A.toFun y - baseMask A lam := rfl

/-- **The action of `A` on the centres of cubes**: `(j, y₀) ↦ (j, base of the image cell)`. -/
def affCentres (A : AffIso d ((N₁ * L ^ m₁) * L ^ K)) (m₁' : ℕ) :
    Equiv.Perm (ℕ × Torus d ((N₁ * L ^ m₁) * L ^ K)) :=
  Equiv.prodShear (Equiv.refl ℕ) (fun j =>
    A.toEquiv.trans (Equiv.subRight (baseMask A (L ^ (j + m₁')))))

omit [NeZero N₁] [NeZero L] in
theorem affCentres_apply (A : AffIso d ((N₁ * L ^ m₁) * L ^ K)) (m₁' : ℕ)
    (q : ℕ × Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    affCentres (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) A m₁' q =
      (q.1, baseImg A (L ^ (q.1 + m₁')) q.2) := rfl

variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (A : AffIso d ((N₁ * L ^ m₁) * L ^ K))
  (hAl : A.Aligned (L ^ (K + m₁))) (hG : CubeAligned G m₁) (hG' : CubeAligned G' m₁)
  (hΩ : ∀ j x, A.toFun x ∈ G'.Ω j ↔ x ∈ G.Ω j)

omit [NeZero N₁] [NeZero L] in
include hAl in
theorem aligned_cube {j : ℕ} (hj : j ≤ K) : A.Aligned (L ^ (j + m₁)) :=
  fun i => dvd_trans (pow_dvd_pow L (by omega)) (hAl i)

include hΩ in
theorem layer_aff (j : ℕ) (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    A.toFun x ∈ G'.layer j ↔ x ∈ G.layer j := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, hΩ j, hΩ (j + 1)]

include hAl hG' hΩ in
theorem cover_idx_aff (q : ℕ × CTorus d L N₁ m₁ K) :
    affCentres (m₁ := m₁) A m₁ q ∈ (coverOf G').cubeIdx ↔ q ∈ (coverOf G).cubeIdx := by
  show (q.1, baseImg A (L ^ (q.1 + m₁)) q.2) ∈ cubeIdx G' ↔ q ∈ cubeIdx G
  rw [mem_cubeIdx, mem_cubeIdx]
  constructor
  · rintro ⟨hr, hl, hb⟩
    have hr' : 1 ≤ q.1 ∧ q.1 ≤ K := hr
    have hAj := aligned_cube A hAl hr'.2
    have hpos : 0 < L ^ (q.1 + m₁) := by have := NeZero.pos L; positivity
    have hb' : CubeBase m₁ q.1 q.2 :=
      (baseImg_base_iff A hpos (dvd_side hr'.2) hAj q.2).1 hb
    have hc := sameCell_baseImg A hpos (dvd_side hr'.2) hAj q.2 hb'
    refine ⟨hr', ?_, hb'⟩
    have hl' : baseImg A (L ^ (q.1 + m₁)) q.2 ∈ G'.layer q.1 := hl
    exact (layer_aff A hΩ q.1 q.2).1 ((hG'.mem_layer_iff hr'.1 hr'.2 hc).1 hl')
  · rintro ⟨hr, hl, hb⟩
    have hAj := aligned_cube A hAl hr.2
    have hpos : 0 < L ^ (q.1 + m₁) := by have := NeZero.pos L; positivity
    have hc := sameCell_baseImg A hpos (dvd_side hr.2) hAj q.2 hb
    refine ⟨hr, ?_, (baseImg_base_iff A hpos (dvd_side hr.2) hAj q.2).2 hb⟩
    exact (hG'.mem_layer_iff hr.1 hr.2 hc).2 ((layer_aff A hΩ q.1 q.2).2 hl)

include hAl hG' hΩ in
theorem coverDenom_aff (x : CTorus d L N₁ m₁ K) :
    coverDenom G' (A.toFun x) = coverDenom G x := by
  unfold coverDenom
  refine (Finset.sum_equiv (affCentres (m₁ := m₁) A m₁)
    (fun q => (cover_idx_aff A hAl hG' hΩ q).symm) fun q _ => ?_).symm
  rw [affCentres_apply]
  exact (cubeBump_aff A q.1 q.2 x).symm

include hAl hG' hΩ in
theorem cover_chi_aff (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) :
    (coverOf G').chi (affCentres (m₁ := m₁) A m₁ q) (A.toFun x) = (coverOf G).chi q x := by
  show chi G' (q.1, baseImg A (L ^ (q.1 + m₁)) q.2) (A.toFun x) = chi G q x
  unfold chi
  rw [coverDenom_aff A hAl hG' hΩ x]
  exact congrArg (· / coverDenom G x) (cubeBump_aff A q.1 q.2 x)

theorem cover_box_aff (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) :
    A.toFun x ∈ intBox (affCentres (m₁ := m₁) A m₁ q) ↔ x ∈ intBox q := by
  rw [mem_intBox, mem_intBox]
  exact inBox_aff_iff A q.1 q.2 x _

include hAl hG' hΩ in
theorem cover_qset_aff (q q' : ℕ × CTorus d L N₁ m₁ K) :
    affCentres (m₁ := m₁) A m₁ q' ∈ (coverOf G').Qset (affCentres (m₁ := m₁) A m₁ q) ↔
      q' ∈ (coverOf G).Qset q := by
  rw [DecCover.mem_Qset, DecCover.mem_Qset, cover_idx_aff A hAl hG' hΩ q']
  refine and_congr_right fun hq' => ?_
  have hr : 1 ≤ q'.1 ∧ q'.1 ≤ K := ((mem_cubeIdx G).1 hq').1
  obtain ⟨-, -, hb⟩ := (mem_cubeIdx G).1 hq'
  have hAj := aligned_cube A hAl hr.2
  have hpos : 0 < L ^ (q'.1 + m₁) := by have := NeZero.pos L; positivity
  have hc := sameCell_baseImg A hpos (dvd_side hr.2) hAj q'.2 hb
  show (∃ y, SameCell (L ^ (q'.1 + m₁)) y (baseImg A (L ^ (q'.1 + m₁)) q'.2) ∧
      InBox m₁ q.1 (baseImg A (L ^ (q.1 + m₁)) q.2) (hatRad L m₁ q.1) y) ↔
    ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧ InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨A.invFun y, ?_, ?_⟩
    · have h1' : SameCell (L ^ (q'.1 + m₁)) y (A.toFun q'.2) := h1.trans hc
      have := (sameCell_aff_iff A hpos (dvd_side hr.2) hAj (A.invFun y) q'.2).1
      exact this (by rwa [AffIso.toFun_invFun])
    · have := (inBox_aff_iff A q.1 q.2 (A.invFun y) (hatRad L m₁ q.1)).1
      exact this (by rwa [AffIso.toFun_invFun])
  · rintro ⟨y, h1, h2⟩
    refine ⟨A.toFun y, ?_, (inBox_aff_iff A q.1 q.2 y _).2 h2⟩
    exact ((sameCell_aff_iff A hpos (dvd_side hr.2) hAj y q'.2).2 h1).trans hc.symm

include hAl in
theorem cubeP_aff {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (x : CTorus d L N₁ m₁ K) :
    A.toFun x ∈ cubeP (affCentres (m₁ := m₁) A m₁ q) ↔ x ∈ cubeP q := by
  obtain ⟨hr, -, hb⟩ := (mem_cubeIdx G).1 hq
  have hAj := aligned_cube A hAl hr.2
  have hpos : 0 < L ^ (q.1 + m₁) := by have := NeZero.pos L; positivity
  have hc := sameCell_baseImg A hpos (dvd_side hr.2) hAj q.2 hb
  rw [mem_cubeP, mem_cubeP]
  show SameCell (L ^ (q.1 + m₁)) (A.toFun x) (baseImg A (L ^ (q.1 + m₁)) q.2) ↔ _
  exact ⟨fun h => (sameCell_aff_iff A hpos (dvd_side hr.2) hAj _ _).1 (h.trans hc),
    fun h => ((sameCell_aff_iff A hpos (dvd_side hr.2) hAj _ _).2 h).trans hc.symm⟩

/-! ### Compatibility with the blocks of two generating sets -/

include hAl hG' hΩ in
theorem block_idx_aff (q : ℕ × CTorus d L N₁ m₁ K) :
    (q.1, baseImg A (L ^ q.1) q.2) ∈ Background.blockIdx G' ↔ q ∈ Background.blockIdx G := by
  rw [Background.mem_blockIdx, Background.mem_blockIdx]
  have hAj : ∀ {j : ℕ}, j ≤ K → A.Aligned (L ^ j) := fun {j} hj i =>
    dvd_trans (pow_dvd_pow L (by omega)) (hAl i)
  have hdv : ∀ {j : ℕ}, j ≤ K → L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := fun {j} hj =>
    dvd_side' hj
  constructor
  · rintro ⟨hr, hl, hb⟩
    have hr' : 1 ≤ q.1 ∧ q.1 ≤ K := hr
    have hpos : 0 < L ^ q.1 := by have := NeZero.pos L; positivity
    have hb' : Background.IsBase q.1 q.2 :=
      (baseImg_base_iff A hpos (hdv hr'.2) (hAj hr'.2) q.2).1 hb
    have hc := sameCell_baseImg A hpos (hdv hr'.2) (hAj hr'.2) q.2 hb'
    refine ⟨hr', ?_, hb'⟩
    have hl' : baseImg A (L ^ q.1) q.2 ∈ G'.layer q.1 := hl
    have hc' : SameCell (L ^ (q.1 + m₁)) (baseImg A (L ^ q.1) q.2) (A.toFun q.2) :=
      hc.mono (pow_dvd_pow L (Nat.le_add_right _ _))
    exact (layer_aff A hΩ q.1 q.2).1 ((hG'.mem_layer_iff hr'.1 hr'.2 hc').1 hl')
  · rintro ⟨hr, hl, hb⟩
    have hpos : 0 < L ^ q.1 := by have := NeZero.pos L; positivity
    have hc := sameCell_baseImg A hpos (hdv hr.2) (hAj hr.2) q.2 hb
    have hc' : SameCell (L ^ (q.1 + m₁)) (baseImg A (L ^ q.1) q.2) (A.toFun q.2) :=
      hc.mono (pow_dvd_pow L (Nat.le_add_right _ _))
    refine ⟨hr, ?_, (baseImg_base_iff A hpos (hdv hr.2) (hAj hr.2) q.2).2 hb⟩
    exact (hG'.mem_layer_iff hr.1 hr.2 hc').2 ((layer_aff A hΩ q.1 q.2).2 hl)

theorem block_bump_aff (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) :
    Background.bump q.1 (baseImg A (L ^ q.1) q.2) (A.toFun x) = Background.bump q.1 q.2 x :=
  bump_aff A q.1 q.2 x

include hAl in
theorem block_base_aff (q : ℕ × CTorus d L N₁ m₁ K) (hr : 1 ≤ q.1 ∧ q.1 ≤ K)
    (hb : Background.IsBase q.1 q.2) :
    jBlock d L (N₁ * L ^ m₁) K q.1 (A.invFun (baseImg A (L ^ q.1) q.2)) =
      jBlock d L (N₁ * L ^ m₁) K q.1 q.2 := by
  have hAj : A.Aligned (L ^ q.1) := fun i => dvd_trans (pow_dvd_pow L (by omega)) (hAl i)
  have hdv : L ^ q.1 ∣ (N₁ * L ^ m₁) * L ^ K := dvd_side' hr.2
  have hpos : 0 < L ^ q.1 := by have := NeZero.pos L; positivity
  have hc := sameCell_baseImg A hpos hdv hAj q.2 hb
  have h1 : SameCell (L ^ q.1) (A.invFun (baseImg A (L ^ q.1) q.2)) q.2 := by
    refine (sameCell_aff_iff A hpos hdv hAj _ _).1 ?_
    rw [AffIso.toFun_invFun]; exact hc
  exact jBlock_eq_of_sameCell h1

/-- The action of `A` on the centres of blocks: `(j, y₀) ↦ (j, base of the image block)`. -/
def affBlocks (A : AffIso d ((N₁ * L ^ m₁) * L ^ K)) :
    Equiv.Perm (ℕ × Torus d ((N₁ * L ^ m₁) * L ^ K)) :=
  Equiv.prodShear (Equiv.refl ℕ) (fun j =>
    A.toEquiv.trans (Equiv.subRight (baseMask A (L ^ j))))

omit [NeZero N₁] [NeZero L] in
theorem affBlocks_apply (A : AffIso d ((N₁ * L ^ m₁) * L ^ K))
    (q : ℕ × Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    affBlocks (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) A q = (q.1, baseImg A (L ^ q.1) q.2) := rfl

include hAl in
/-- **`CoverSymm.ofTranslate` generalized**: an aligned affine lattice isometry preserving the
domains of a cube-aligned generating set is compatible with its cover. -/
def CoverSymm.ofAff {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : CubeAligned G m₁)
    (hΩ : ∀ j x, A.toFun x ∈ G.Ω j ↔ x ∈ G.Ω j) :
    CoverSymm (coverOf G) A.toEquiv where
  τ := affCentres (m₁ := m₁) A m₁
  idx := cover_idx_aff A hAl hG hΩ
  chi := cover_chi_aff A hAl hG hΩ
  box := cover_box_aff A
  qset := cover_qset_aff A hAl hG hΩ

/-- **`BlockSymm.ofTranslate` generalized.** -/
def BlockSymm.ofAff {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (hG : CubeAligned G m₁)
    (hΩ : ∀ j x, A.toFun x ∈ G.Ω j ↔ x ∈ G.Ω j) : BlockSymm G A.toEquiv where
  τ := affBlocks A
  idx := block_idx_aff A hAl hG hΩ
  layer := fun _ => rfl
  bump := block_bump_aff A
  base := fun q hq => by
    obtain ⟨hr, -, hb⟩ := (Background.mem_blockIdx G).1 hq
    exact block_base_aff A hAl q hr hb

end CoverAff

end Balaban.Localization.DecEquiv
