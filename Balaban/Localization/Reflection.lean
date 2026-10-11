/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Model.Torus
public import Balaban.Green.BallSums
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The coordinate fold of a cube (NC3, reflection construction)

A coordinate cube `□ = {c + t : 0 ≤ t < S}^d` of the torus `(ℤ/ℓℤ)^d` (with `S < ℓ`) is unfolded
to the doubled torus `(ℤ/2Sℤ)^d` by the reflection `r(t) = t` for `t < S`, `r(t) = 2S - 1 - t`
for `S ≤ t < 2S`.  This file contains the one-dimensional picture, which fixes the interfaces:

* `Balaban.Reflection.foldNat S`: the reflection `r`;
* `Balaban.Reflection.fold1 ℓ S c m`: the map `ZMod m → ZMod ℓ`, `a ↦ c + r(a.val)` (`m = 2S`);
* `Balaban.Reflection.InCube1`: membership in the interval `{c + t : t < S}` of `ZMod ℓ`;
* `Balaban.Reflection.fold1_nbr`: the neighbours of a folded point (the folded neighbours are the
  neighbours of the image that stay in the interval, or the image itself at a face).

Higher-dimensional statements are in `Balaban.Reflection.foldMap`.
-/

@[expose] public section

namespace Balaban.Reflection

open Balaban

/-- The reflection `r` of `[0, 2S)` onto `[0, S)`. -/
def foldNat (S t : ℕ) : ℕ := if t < S then t else 2 * S - 1 - t

theorem foldNat_lt {S t : ℕ} (ht : t < 2 * S) : foldNat S t < S := by
  unfold foldNat
  split_ifs with h <;> omega

theorem foldNat_reflect {S t : ℕ} (ht : t < 2 * S) : foldNat S (2 * S - 1 - t) = foldNat S t := by
  unfold foldNat
  split_ifs with h1 h2 h2 <;> omega

/-- An interval `{c + t : t < S}` of `ZMod ℓ`. -/
def InCube1 (ℓ S c : ℕ) (z : ZMod ℓ) : Prop := ∃ t, t < S ∧ z = ((c + t : ℕ) : ZMod ℓ)

/-- The fold `ZMod m → ZMod ℓ` (with `m = 2S`): `a ↦ c + r(a.val)`. -/
def fold1 (ℓ S c m : ℕ) (a : ZMod m) : ZMod ℓ := ((c + foldNat S a.val : ℕ) : ZMod ℓ)

section OneD

variable {ℓ S c m : ℕ}

theorem fold1_eq [NeZero m] (a : ZMod m) :
    fold1 ℓ S c m a = ((c + foldNat S a.val : ℕ) : ZMod ℓ) := rfl

theorem inCube1_cast_iff [NeZero ℓ] (hSℓ : S ≤ ℓ) (u : ℕ) :
    InCube1 ℓ S c ((c + u : ℕ) : ZMod ℓ) ↔ u % ℓ < S := by
  constructor
  · rintro ⟨t, ht, h⟩
    have h1 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
    have h2 : u % ℓ = t % ℓ :=
      (Nat.ModEq.add_left_cancel' c (show c + u ≡ c + t [MOD ℓ] from h1))
    rw [h2, Nat.mod_eq_of_lt (lt_of_lt_of_le ht hSℓ)]
    exact ht
  · intro h
    refine ⟨u % ℓ, h, ?_⟩
    rw [ZMod.natCast_eq_natCast_iff', Nat.add_mod_mod]

theorem inCube1_fold1 [NeZero m] (hm : m = 2 * S) (a : ZMod m) :
    InCube1 ℓ S c (fold1 ℓ S c m a) := by
  refine ⟨foldNat S a.val, foldNat_lt ?_, rfl⟩
  have := ZMod.val_lt a
  omega

theorem fold1_neg_one_sub [NeZero m] (hm : m = 2 * S) (hS : 0 < S) (a : ZMod m) :
    fold1 ℓ S c m (-1 - a) = fold1 ℓ S c m a := by
  have hv : (-1 - a : ZMod m).val = 2 * S - 1 - a.val := by
    have hlt := ZMod.val_lt a
    have e : (-1 - a : ZMod m) = ((2 * S - 1 - a.val : ℕ) : ZMod m) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      have : ((2 * S : ℕ) : ZMod m) = 0 := by rw [← hm]; exact ZMod.natCast_self m
      push_cast at this ⊢
      rw [this, ZMod.natCast_zmod_val]
      ring
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  unfold fold1
  rw [hv, foldNat_reflect (by have := ZMod.val_lt a; omega)]

theorem natCast_pred_zmod {n : ℕ} (hn : 1 ≤ n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn, ZMod.natCast_self]

theorem fold1_val_of_lt [NeZero m] {a : ZMod m} (ha : a.val < S) :
    fold1 ℓ S c m a = ((c + a.val : ℕ) : ZMod ℓ) := by
  unfold fold1 foldNat
  simp [ha]

open scoped Classical in
/-- The neighbour `y + 1` if it stays in the interval, else `y` (reflection at the upper face). -/
noncomputable def stepUp (ℓ S c : ℕ) (y : ZMod ℓ) : ZMod ℓ :=
  if InCube1 ℓ S c (y + 1) then y + 1 else y

open scoped Classical in
/-- The neighbour `y - 1` if it stays in the interval, else `y` (reflection at the lower face). -/
noncomputable def stepDn (ℓ S c : ℕ) (y : ZMod ℓ) : ZMod ℓ :=
  if InCube1 ℓ S c (y - 1) then y - 1 else y

open scoped Classical in
/-- Lower half: the neighbours of a folded point `a` with `a.val < S`. -/
theorem fold1_nbr_low [NeZero ℓ] [NeZero m] (hm : m = 2 * S) (hS : 0 < S) (hSℓ : S < ℓ)
    (a : ZMod m) (ha : a.val < S) :
    fold1 ℓ S c m (a + 1) = stepUp ℓ S c (fold1 ℓ S c m a) ∧
    fold1 ℓ S c m (a - 1) = stepDn ℓ S c (fold1 ℓ S c m a) := by
  unfold stepUp stepDn
  set t := a.val with ht
  have hat : a = (t : ZMod m) := (ZMod.natCast_zmod_val a).symm
  have hy : fold1 ℓ S c m a = ((c + t : ℕ) : ZMod ℓ) := fold1_val_of_lt ha
  have hmS : m = 2 * S := hm
  constructor
  · have e : a + 1 = ((t + 1 : ℕ) : ZMod m) := by rw [hat]; push_cast; rfl
    have hv : (a + 1).val = t + 1 := by
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hin : InCube1 ℓ S c (fold1 ℓ S c m a + 1) ↔ t + 1 < S := by
      have : fold1 ℓ S c m a + 1 = ((c + (t + 1) : ℕ) : ZMod ℓ) := by rw [hy]; push_cast; ring
      rw [this, inCube1_cast_iff hSℓ.le, Nat.mod_eq_of_lt (by omega)]
    by_cases h : t + 1 < S
    · simp only [hin.2 h, ↓reduceIte]
      rw [fold1_eq, hv]
      simp only [foldNat, h, ↓reduceIte]
      rw [hy]; push_cast; ring
    · simp only [show ¬ InCube1 ℓ S c (fold1 ℓ S c m a + 1) from fun h' => h (hin.1 h'), ↓reduceIte]
      rw [fold1_eq, hv, hy]
      simp only [foldNat, h, ↓reduceIte]
      have : t + 1 = S := by omega
      have e2 : 2 * S - 1 - (t + 1) = t := by omega
      rw [e2]
  · by_cases h0 : t = 0
    · have e : a - 1 = ((t + (m - 1) : ℕ) : ZMod m) := by
        rw [hat, Nat.cast_add, natCast_pred_zmod (by omega)]; ring
      have hv : (a - 1).val = 2 * S - 1 := by
        rw [e, ZMod.val_natCast, h0]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hin : ¬ InCube1 ℓ S c (fold1 ℓ S c m a - 1) := by
        have : fold1 ℓ S c m a - 1 = ((c + (ℓ - 1) : ℕ) : ZMod ℓ) := by
          rw [hy, h0, Nat.cast_add, Nat.cast_add, natCast_pred_zmod (by omega)]; push_cast; ring
        rw [this, inCube1_cast_iff hSℓ.le, Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [hin, ↓reduceIte]
      rw [fold1_eq, hv, hy]
      simp only [foldNat, show ¬ (2 * S - 1 < S) by omega, ↓reduceIte]
      have : 2 * S - 1 - (2 * S - 1) = 0 := by omega
      rw [this, h0]
    · have e : a - 1 = ((t - 1 : ℕ) : ZMod m) := by
        rw [hat, Nat.cast_sub (by omega)]; push_cast; rfl
      have hv : (a - 1).val = t - 1 := by
        rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      have hin : InCube1 ℓ S c (fold1 ℓ S c m a - 1) := by
        have : fold1 ℓ S c m a - 1 = ((c + (t - 1) : ℕ) : ZMod ℓ) := by
          rw [hy]; push_cast [Nat.cast_sub (show 1 ≤ t by omega)]; ring
        rw [this, inCube1_cast_iff hSℓ.le, Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [hin, ↓reduceIte]
      rw [fold1_eq, hv, hy]
      simp only [foldNat, show t - 1 < S by omega, ↓reduceIte]
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]; push_cast; ring

/-- **The neighbours of a folded point.** The two folded neighbours of `a` are the two
neighbours `stepUp`, `stepDn` of the image `fold1 a` (in one order or the other). -/
theorem fold1_nbr [NeZero ℓ] [NeZero m] (hm : m = 2 * S) (hS : 0 < S) (hSℓ : S < ℓ)
    (a : ZMod m) :
    (fold1 ℓ S c m (a + 1) = stepUp ℓ S c (fold1 ℓ S c m a) ∧
      fold1 ℓ S c m (a - 1) = stepDn ℓ S c (fold1 ℓ S c m a)) ∨
    (fold1 ℓ S c m (a + 1) = stepDn ℓ S c (fold1 ℓ S c m a) ∧
      fold1 ℓ S c m (a - 1) = stepUp ℓ S c (fold1 ℓ S c m a)) := by
  by_cases ha : a.val < S
  · exact Or.inl (fold1_nbr_low hm hS hSℓ a ha)
  · right
    set a' : ZMod m := -1 - a with ha'
    have hv : a'.val = 2 * S - 1 - a.val := by
      have hlt := ZMod.val_lt a
      have e : a' = ((2 * S - 1 - a.val : ℕ) : ZMod m) := by
        rw [ha', Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have : ((2 * S : ℕ) : ZMod m) = 0 := by rw [← hm]; exact ZMod.natCast_self m
        push_cast at this ⊢
        rw [this, ZMod.natCast_zmod_val]
        ring
      rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hlow : a'.val < S := by
      have := ZMod.val_lt a
      omega
    have hy : fold1 ℓ S c m a' = fold1 ℓ S c m a := fold1_neg_one_sub hm hS a
    obtain ⟨h1, h2⟩ := fold1_nbr_low hm hS hSℓ a' hlow
    rw [hy] at h1 h2
    have e1 : a + 1 = -1 - (a' - 1) := by rw [ha']; ring
    have e2 : a - 1 = -1 - (a' + 1) := by rw [ha']; ring
    rw [e1, e2, fold1_neg_one_sub hm hS, fold1_neg_one_sub hm hS]
    exact ⟨h2, h1⟩

/-! ### The fold is 1-Lipschitz for the cyclic distance -/

/-- The periodic reflection on `ℤ`. -/
def rI (S : ℕ) (n : ℤ) : ℤ := (foldNat S (n % (2 * S : ℤ)).toNat : ℤ)

theorem rI_succ_sub (S : ℕ) (hS : 0 < S) (n : ℤ) : |rI S (n + 1) - rI S n| ≤ 1 := by
  have hM : (0 : ℤ) < 2 * S := by omega
  have h0 := Int.emod_nonneg n hM.ne'
  have h1 := Int.emod_lt_of_pos n hM
  have hq : n % (2 * S : ℤ) + (2 * S : ℤ) * (n / (2 * S : ℤ)) = n := by
    have := Int.emod_add_mul_ediv n (2 * S)
    linarith [mul_comm ((2 * S : ℤ)) (n / (2 * S : ℤ))]
  have e : n + 1 = (n % (2 * S : ℤ) + 1) + (2 * S : ℤ) * (n / (2 * S : ℤ)) := by linarith
  have hn1 : (n + 1) % (2 * S : ℤ) =
      if n % (2 * S : ℤ) + 1 < 2 * S then n % (2 * S : ℤ) + 1 else 0 := by
    rw [e, Int.add_mul_emod_self_left]
    split_ifs with h
    · exact Int.emod_eq_of_lt (by omega) h
    · have : n % (2 * S : ℤ) + 1 = 2 * S := by omega
      rw [this, Int.emod_self]
  obtain ⟨t', ht'⟩ : ∃ t' : ℕ, n % (2 * S : ℤ) = t' := ⟨(n % (2 * S : ℤ)).toNat, (Int.toNat_of_nonneg h0).symm⟩
  unfold rI
  rw [hn1, ht']
  by_cases h : (t' : ℤ) + 1 < 2 * S
  · simp only [h, ↓reduceIte]
    have h' : t' + 1 < 2 * S := by omega
    have e1 : ((t' : ℤ) + 1).toNat = t' + 1 := by omega
    rw [e1, Int.toNat_natCast]
    unfold foldNat
    split_ifs <;> (rw [abs_le]; omega)
  · simp only [h, ↓reduceIte]
    have h' : t' + 1 = 2 * S := by omega
    rw [Int.toNat_zero, Int.toNat_natCast]
    unfold foldNat
    split_ifs <;> (rw [abs_le]; omega)

theorem rI_add_sub (S : ℕ) (hS : 0 < S) (n k : ℤ) : |rI S (n + k) - rI S n| ≤ |k| := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h1 := rI_succ_sub S hS (n + i)
      have e : n + ((i : ℤ) + 1) = n + i + 1 := by ring
      rw [e]
      calc |rI S (n + i + 1) - rI S n| ≤ |rI S (n + i + 1) - rI S (n + i)| +
            |rI S (n + i) - rI S n| := abs_sub_le _ _ _
        _ ≤ 1 + |(i : ℤ)| := add_le_add h1 ih
        _ = |((i : ℤ) + 1)| := by
            rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ i + 1), abs_of_nonneg (by positivity)]; ring
  | pred i ih =>
      have h1 := rI_succ_sub S hS (n + (-(i : ℤ) - 1))
      have e : n + (-(i : ℤ) - 1) + 1 = n + -(i : ℤ) := by ring
      rw [e] at h1
      calc |rI S (n + (-(i : ℤ) - 1)) - rI S n| ≤ |rI S (n + (-(i : ℤ) - 1)) - rI S (n + -(i : ℤ))| +
            |rI S (n + -(i : ℤ)) - rI S n| := abs_sub_le _ _ _
        _ ≤ 1 + |-(i : ℤ)| := add_le_add (by rw [abs_sub_comm]; exact h1) ih
        _ = |(-(i : ℤ) - 1)| := by
            rw [abs_neg, abs_of_nonpos (by omega : -(i : ℤ) - 1 ≤ 0), abs_of_nonneg (by positivity)]; ring

theorem fold1_eq_rI [NeZero m] (hm : m = 2 * S) (n : ℤ) :
    fold1 ℓ S c m ((n : ℤ) : ZMod m) = ((c + rI S n : ℤ) : ZMod ℓ) := by
  have hv : (((n : ZMod m)).val : ℤ) = n % (2 * S : ℤ) := by
    rw [ZMod.val_intCast, hm]; push_cast; rfl
  have hv' : ((n : ZMod m).val) = (n % (2 * S : ℤ)).toNat := by omega
  unfold fold1 rI
  rw [hv']
  push_cast
  rfl

theorem natAbs_cycRep_fold1_le [NeZero ℓ] [NeZero m] (hm : m = 2 * S) (hS : 0 < S)
    (a b : ZMod m) :
    (Green.cycRep (fold1 ℓ S c m a - fold1 ℓ S c m b)).natAbs ≤ (Green.cycRep (a - b)).natAbs := by
  set k := Green.cycRep (a - b) with hk
  have hkc : (k : ZMod m) = a - b := Green.cast_cycRep _
  have ha : a = (((b.val : ℤ) + k : ℤ) : ZMod m) := by
    push_cast; rw [ZMod.natCast_zmod_val, hkc]; ring
  have hb : b = (((b.val : ℤ) : ℤ) : ZMod m) := by simp
  have h1 := fold1_eq_rI (ℓ := ℓ) (S := S) (c := c) hm ((b.val : ℤ) + k)
  have h2 := fold1_eq_rI (ℓ := ℓ) (S := S) (c := c) hm (b.val : ℤ)
  rw [← ha] at h1
  rw [← hb] at h2
  have hz : fold1 ℓ S c m a - fold1 ℓ S c m b =
      ((rI S ((b.val : ℤ) + k) - rI S (b.val : ℤ) : ℤ) : ZMod ℓ) := by
    rw [h1, h2]; push_cast; ring
  refine (Green.natAbs_cycRep_le_of_cast _ _ hz.symm).trans ?_
  have := rI_add_sub S hS (b.val : ℤ) k
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-! ### Blocks -/

theorem foldNat_div {S A B t : ℕ} (hA : 0 < A) (hS : S = A * B) (ht : t < 2 * S) :
    foldNat S t / A = if t / A < B then t / A else 2 * B - (t / A + 1) := by
  have hlt : t < S ↔ t / A < B := by
    rw [Nat.div_lt_iff_lt_mul hA, hS, mul_comm B A]
  unfold foldNat
  by_cases h : t < S
  · simp [h, hlt.1 h]
  · have h2 : ¬ t / A < B := fun h' => h (hlt.2 h')
    simp only [h, h2, ↓reduceIte]
    have e : 2 * S - 1 - t = A * (2 * B) - (t + 1) := by rw [hS]; ring_nf; omega
    rw [e, Nat.mul_sub_div t A (2 * B) (by rw [hS] at ht; nlinarith)]

theorem fold1_val_div [NeZero ℓ] [NeZero m] {A B' C : ℕ} (hA : 0 < A) (hℓ : ℓ = A * B')
    (hc : c = A * C) (a : ZMod m) :
    (fold1 ℓ S c m a).val / A = (C + foldNat S a.val / A) % B' := by
  rw [fold1_eq, ZMod.val_natCast, hℓ, hc, Nat.mod_mul_right_div_self, Nat.mul_add_div hA]

/-- Two points of one block of side `A` (`A ∣ S`, `A ∣ c`, `A ∣ ℓ`) have images in one block. -/
theorem fold1_div_eq [NeZero ℓ] [NeZero m] {A B B' C : ℕ} (hm : m = 2 * S) (hA : 0 < A)
    (hS : S = A * B) (hℓ : ℓ = A * B') (hc : c = A * C) {a b : ZMod m}
    (h : a.val / A = b.val / A) : (fold1 ℓ S c m a).val / A = (fold1 ℓ S c m b).val / A := by
  rw [fold1_val_div hA hℓ hc, fold1_val_div hA hℓ hc, foldNat_div hA hS (by
    have := ZMod.val_lt a; omega), foldNat_div hA hS (by have := ZMod.val_lt b; omega), h]

/-- The fold is injective on a block of side `A` (`A ∣ S`). -/
theorem fold1_injOn_block [NeZero ℓ] [NeZero m] {A B : ℕ} (hm : m = 2 * S) (hA : 0 < A)
    (hS : S = A * B) (hSℓ : S < ℓ) {a b : ZMod m} (h : a.val / A = b.val / A)
    (hab : fold1 ℓ S c m a = fold1 ℓ S c m b) : a = b := by
  have hlt : ∀ t, t < S ↔ t / A < B := fun t => by
    rw [Nat.div_lt_iff_lt_mul hA, hS, mul_comm B A]
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have h1 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
  have h2 : foldNat S a.val % ℓ = foldNat S b.val % ℓ :=
    Nat.ModEq.add_left_cancel' c (show c + foldNat S a.val ≡ c + foldNat S b.val [MOD ℓ] from h1)
  rw [Nat.mod_eq_of_lt (lt_trans (foldNat_lt (by omega)) hSℓ),
    Nat.mod_eq_of_lt (lt_trans (foldNat_lt (by omega)) hSℓ)] at h2
  apply ZMod.val_injective
  have hq : (a.val < S ↔ b.val < S) := by rw [hlt, hlt, h]
  unfold foldNat at h2
  by_cases hs : a.val < S
  · have hs' := hq.1 hs
    simp only [hs, hs', ↓reduceIte] at h2
    exact h2
  · have hs' : ¬ b.val < S := fun h' => hs (hq.2 h')
    simp only [hs, hs', ↓reduceIte] at h2
    omega

end OneD

section Torus

variable {d : ℕ} {ℓ S m : ℕ} {c : Fin d → ℕ}

/-- The fold of the doubled torus `(ℤ/mℤ)^d` (`m = 2S`) onto the cube `{c + t : t < S}^d` of
`(ℤ/ℓℤ)^d`, coordinatewise. -/
def foldMap (ℓ S m : ℕ) (c : Fin d → ℕ) (p : Torus d m) : Torus d ℓ :=
  fun i => fold1 ℓ S (c i) m (p i)

open scoped Classical in
/-- The coordinate cube `{c + t : t < S}^d` of `(ℤ/ℓℤ)^d`. -/
noncomputable def cubeSet (ℓ S : ℕ) [NeZero ℓ] (c : Fin d → ℕ) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun x => ∀ i, InCube1 ℓ S (c i) (x i)

theorem mem_cubeSet [NeZero ℓ] {x : Torus d ℓ} :
    x ∈ cubeSet ℓ S c ↔ ∀ i, InCube1 ℓ S (c i) (x i) := by
  simp [cubeSet]

theorem foldMap_mem_cubeSet [NeZero ℓ] [NeZero m] (hm : m = 2 * S) (p : Torus d m) :
    foldMap ℓ S m c p ∈ cubeSet ℓ S c :=
  mem_cubeSet.2 fun i => inCube1_fold1 hm (p i)

theorem exists_foldMap_eq [NeZero ℓ] [NeZero m] (hm : m = 2 * S) {x : Torus d ℓ}
    (hx : x ∈ cubeSet ℓ S c) : ∃ p : Torus d m, foldMap ℓ S m c p = x := by
  classical
  have h := mem_cubeSet.1 hx
  choose t ht hxt using h
  refine ⟨fun i => ((t i : ℕ) : ZMod m), ?_⟩
  funext i
  have hv : (((t i : ℕ) : ZMod m)).val = t i := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ht i; omega)]
  show fold1 ℓ S (c i) m _ = x i
  rw [fold1_eq, hv, hxt i]
  simp [foldNat, ht i]

open scoped Classical in
/-- The neighbour `x + e_μ` if it stays in `Λ`, else `x`. -/
noncomputable def stepUpT [NeZero ℓ] (Λ : Finset (Torus d ℓ)) (x : Torus d ℓ) (μ : Fin d) :
    Torus d ℓ := if x + Pi.single μ 1 ∈ Λ then x + Pi.single μ 1 else x

open scoped Classical in
/-- The neighbour `x - e_μ` if it stays in `Λ`, else `x`. -/
noncomputable def stepDnT [NeZero ℓ] (Λ : Finset (Torus d ℓ)) (x : Torus d ℓ) (μ : Fin d) :
    Torus d ℓ := if x - Pi.single μ 1 ∈ Λ then x - Pi.single μ 1 else x

theorem add_single_eq_update {n : ℕ} (x : Torus d n) (μ : Fin d) :
    x + Pi.single μ 1 = Function.update x μ (x μ + 1) := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · simp [h, Function.update_of_ne]

theorem sub_single_eq_update {n : ℕ} (x : Torus d n) (μ : Fin d) :
    x - Pi.single μ 1 = Function.update x μ (x μ - 1) := by
  funext i
  by_cases h : i = μ
  · subst h; simp
  · simp [h, Function.update_of_ne]

theorem stepUpT_eq [NeZero ℓ] {x : Torus d ℓ} (hx : x ∈ cubeSet ℓ S c) (μ : Fin d) :
    stepUpT (cubeSet ℓ S c) x μ = Function.update x μ (stepUp ℓ S (c μ) (x μ)) := by
  classical
  have hiff : x + Pi.single μ 1 ∈ cubeSet ℓ S c ↔ InCube1 ℓ S (c μ) (x μ + 1) := by
    rw [mem_cubeSet, add_single_eq_update]
    constructor
    · intro h; simpa using h μ
    · intro h i
      by_cases hi : i = μ
      · subst hi; simpa using h
      · simpa [hi, Function.update_of_ne] using mem_cubeSet.1 hx i
  unfold stepUpT stepUp
  by_cases h : InCube1 ℓ S (c μ) (x μ + 1)
  · simp only [hiff.2 h, h, ↓reduceIte]
    exact add_single_eq_update x μ
  · have h' : ¬ x + Pi.single μ 1 ∈ cubeSet ℓ S c := fun h' => h (hiff.1 h')
    simp only [h', h, ↓reduceIte]
    exact (Function.update_eq_self μ x).symm

theorem stepDnT_eq [NeZero ℓ] {x : Torus d ℓ} (hx : x ∈ cubeSet ℓ S c) (μ : Fin d) :
    stepDnT (cubeSet ℓ S c) x μ = Function.update x μ (stepDn ℓ S (c μ) (x μ)) := by
  classical
  have hiff : x - Pi.single μ 1 ∈ cubeSet ℓ S c ↔ InCube1 ℓ S (c μ) (x μ - 1) := by
    rw [mem_cubeSet, sub_single_eq_update]
    constructor
    · intro h; simpa using h μ
    · intro h i
      by_cases hi : i = μ
      · subst hi; simpa using h
      · simpa [hi, Function.update_of_ne] using mem_cubeSet.1 hx i
  unfold stepDnT stepDn
  by_cases h : InCube1 ℓ S (c μ) (x μ - 1)
  · simp only [hiff.2 h, h, ↓reduceIte]
    exact sub_single_eq_update x μ
  · have h' : ¬ x - Pi.single μ 1 ∈ cubeSet ℓ S c := fun h' => h (hiff.1 h')
    simp only [h', h, ↓reduceIte]
    exact (Function.update_eq_self μ x).symm

/-- **Neighbours of a folded point (torus).** The two folded neighbours `F(p ± e_μ)` of `p` are
`x + e_μ`, `x - e_μ` (each replaced by `x` when it leaves the cube), in one order or the other,
where `x = F p`. -/
theorem foldMap_nbr [NeZero ℓ] [NeZero m] (hm : m = 2 * S) (hS : 0 < S) (hSℓ : S < ℓ)
    (p : Torus d m) (μ : Fin d) :
    (foldMap ℓ S m c (p + Pi.single μ 1) = stepUpT (cubeSet ℓ S c) (foldMap ℓ S m c p) μ ∧
      foldMap ℓ S m c (p - Pi.single μ 1) = stepDnT (cubeSet ℓ S c) (foldMap ℓ S m c p) μ) ∨
    (foldMap ℓ S m c (p + Pi.single μ 1) = stepDnT (cubeSet ℓ S c) (foldMap ℓ S m c p) μ ∧
      foldMap ℓ S m c (p - Pi.single μ 1) = stepUpT (cubeSet ℓ S c) (foldMap ℓ S m c p) μ) := by
  have hx := foldMap_mem_cubeSet (ℓ := ℓ) (c := c) hm p
  have e1 : foldMap ℓ S m c (p + Pi.single μ 1) =
      Function.update (foldMap ℓ S m c p) μ (fold1 ℓ S (c μ) m (p μ + 1)) := by
    rw [add_single_eq_update]
    funext i
    by_cases h : i = μ
    · subst h; simp [foldMap]
    · simp [foldMap, h, Function.update_of_ne]
  have e2 : foldMap ℓ S m c (p - Pi.single μ 1) =
      Function.update (foldMap ℓ S m c p) μ (fold1 ℓ S (c μ) m (p μ - 1)) := by
    rw [sub_single_eq_update]
    funext i
    by_cases h : i = μ
    · subst h; simp [foldMap]
    · simp [foldMap, h, Function.update_of_ne]
  rw [e1, e2, stepUpT_eq hx, stepDnT_eq hx]
  have hy : foldMap ℓ S m c p μ = fold1 ℓ S (c μ) m (p μ) := rfl
  rcases fold1_nbr (c := c μ) hm hS hSℓ (p μ) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [hy, h1, h2]; exact ⟨rfl, rfl⟩
  · right; rw [hy, h1, h2]; exact ⟨rfl, rfl⟩

/-- The fold is 1-Lipschitz for the `ℓ¹` torus distance. -/
theorem torusDist_foldMap_le [NeZero ℓ] [NeZero m] (hm : m = 2 * S) (hS : 0 < S)
    (p p' : Torus d m) :
    Green.torusDist d ℓ (foldMap ℓ S m c p) (foldMap ℓ S m c p') ≤ Green.torusDist d m p p' := by
  unfold Green.torusDist
  refine Finset.sum_le_sum fun i _ => ?_
  exact_mod_cast natAbs_cycRep_fold1_le hm hS (p i) (p' i)

/-- Points of one block of side `A` have images in one block of side `A`. -/
theorem foldMap_div_eq [NeZero ℓ] [NeZero m] {A B B' : ℕ} (hm : m = 2 * S) (hA : 0 < A)
    (hS : S = A * B) (hℓ : ℓ = A * B') (hc : ∀ i, ∃ C, c i = A * C) {p p' : Torus d m}
    (h : ∀ i, (p i).val / A = (p' i).val / A) (i : Fin d) :
    (foldMap ℓ S m c p i).val / A = (foldMap ℓ S m c p' i).val / A := by
  obtain ⟨C, hC⟩ := hc i
  exact fold1_div_eq hm hA hS hℓ hC (h i)

/-- The fold is injective on a block of side `A`. -/
theorem foldMap_injOn_block [NeZero ℓ] [NeZero m] {A B : ℕ} (hm : m = 2 * S) (hA : 0 < A)
    (hS : S = A * B) (hSℓ : S < ℓ) {p p' : Torus d m}
    (h : ∀ i, (p i).val / A = (p' i).val / A) (hF : foldMap ℓ S m c p = foldMap ℓ S m c p') :
    p = p' := by
  funext i
  exact fold1_injOn_block hm hA hS hSℓ (h i) (congrFun hF i)

end Torus

end Balaban.Reflection
