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

theorem val_img_core {n : ℕ} [NeZero n] (lam : ℕ) (hlam : 0 < lam) (s x y : ZMod n) (b : Bool) :
    ∃ e : ℤ, ((((s + AffIso.sgn n b * x).val : ℕ) : ℝ) -
        ((((s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0)).val : ℕ) : ℝ) +
          ((lam : ℝ) - 1) / 2)) =
      (if b then (-1 : ℝ) else 1) * (((x.val : ℕ) : ℝ) - (((y.val : ℕ) : ℝ) + ((lam : ℝ) - 1) / 2)) +
        (n : ℝ) * e := by
  have hl1 : 1 ≤ lam := hlam
  obtain ⟨e1, h1⟩ := exists_val_eq (s + AffIso.sgn n b * x)
    ((s.val : ℤ) + (if b then -1 else 1) * (x.val : ℤ)) (by
      cases b <;> simp [AffIso.sgn])
  obtain ⟨e2, h2⟩ := exists_val_eq (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0))
    ((s.val : ℤ) + (if b then -1 else 1) * (y.val : ℤ) - (if b then ((lam - 1 : ℕ) : ℤ) else 0)) (by
      cases b <;> simp [AffIso.sgn])
  refine ⟨e1 - e2, ?_⟩
  have c1 : ((((lam - 1 : ℕ) : ℤ)) : ℝ) = (lam : ℝ) - 1 := by
    rw [Int.cast_natCast, Nat.cast_sub hl1]; simp
  have a1 := congrArg (fun z : ℤ => (z : ℝ)) h1
  have a2 := congrArg (fun z : ℤ => (z : ℝ)) h2
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_one, Int.cast_sub, Int.cast_zero, sub_zero, one_mul] at a1 a2 ⊢
    push_cast at a1 a2 ⊢
    linarith
  · simp only [↓reduceIte, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_neg,
      Int.cast_one, Int.cast_sub, c1] at a1 a2 ⊢
    push_cast at a1 a2 ⊢
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
  obtain ⟨e, he⟩ := exists_val_eq (s + AffIso.sgn n b * y - (if b then ((lam - 1 : ℕ) : ZMod n) else 0))
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
    obtain ⟨e, he⟩ := exists_val_eq w ((s.val : ℤ) + -1 * (y.val : ℤ)) (by
      simp [hw, AffIso.sgn])
    have hnZ : (lam : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.2 hn
    have hdv : (lam : ℤ) ∣ ((w.val + 1 : ℕ) : ℤ) := by
      have h1 := Int.natCast_dvd_natCast.2 hs
      have h2 := Int.natCast_dvd_natCast.2 hy
      have h3 : (lam : ℤ) ∣ (n : ℤ) * e := dvd_mul_of_dvd_left hnZ e
      have e1 : ((w.val + 1 : ℕ) : ℤ) = (((s.val + 1 : ℕ) : ℤ) - (y.val : ℤ)) + n * e := by
        push_cast; push_cast at he; linarith
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

end Balaban.Localization.DecEquiv
