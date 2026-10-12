/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeInfDict

/-!
# Def-6: polymers of the tori and of the lattice `ℤ^d`

The torus of side `N₁ L^{m₁} L^k` and the lattice `ℤ^d` (fine sites), with the dictionary
`toTorus` (integer coordinates to a torus site) and `fineLift` (centred integer position of a torus
site): `toTorus (fineLift z) = z` and `fineLift (toTorus x) = x` on the small region.

* `PolyZ`: a polymer of `𝒟_j` in `ℤ^d` (nonempty union of `π'_j`-cubes, nearest-neighbour
  connected);
* `isPolyDom_of_polyZ`, `polyZ_of_isPolyDom`: for a shape `X'` that is small relative to the torus
  (`ZSmall`), the lift `Ypoly X'` is in `𝒟_j` iff `PolyZ` holds for the integer set `yhat X'`;
* `isPolyDom_transfer`: a small shape that is a polymer on one torus of the sequence is a polymer on
  every torus on which it is small (the tail lemma of CLASS-RULINGS Q-C uses this).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Localization

section Coord

variable {n p m : ℕ} [NeZero n]

theorem blockCoord_intCast (hn : n = p * m) (hp : 0 < p) (hm : 0 < m) (x : ℤ) :
    blockCoord p m ((x : ℤ) : ZMod n) = ((x / (p : ℤ) : ℤ) : ZMod m) := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  set q : ℤ := x / p with hq
  set r : ℤ := x % p with hr
  set q' : ℤ := q % m with hq'
  have hx1 : x = p * q + r := (Int.mul_ediv_add_emod x p).symm
  have hq1 : q = m * (q / m) + q' := (Int.mul_ediv_add_emod q m).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hpz.ne'
  have hr1 : r < p := Int.emod_lt_of_pos _ hpz
  have hq0 : 0 ≤ q' := Int.emod_nonneg _ hmz.ne'
  have hq2 : q' < m := Int.emod_lt_of_pos _ hmz
  set v : ℤ := p * q' + r with hv
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v < n := by
    rw [hn]; push_cast
    nlinarith
  have hxv : x = v + (n : ℤ) * (q / m) := by
    rw [hn]; push_cast; rw [hx1, hv]; nlinarith [hq1]
  have hval : ((x : ZMod n).val : ℤ) = v := by
    rw [ZMod.val_intCast, hxv, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hv0 hv1
  have hdiv : (x : ZMod n).val / p = q'.toNat := by
    have h1 : ((x : ZMod n).val : ℤ) / p = q' := by
      rw [hval, hv, Int.add_ediv_of_dvd_left (dvd_mul_right _ _)]
      rw [Int.mul_ediv_cancel_left _ hpz.ne', Int.ediv_eq_zero_of_lt hr0 hr1, add_zero]
    have h2 : (((x : ZMod n).val / p : ℕ) : ℤ) = q' := by
      rw [Int.natCast_ediv]; simpa using h1
    omega
  unfold blockCoord
  rw [hdiv]
  have : ((q'.toNat : ℕ) : ℤ) = q' := Int.toNat_of_nonneg hq0
  rw [← ZMod.intCast_mod q m, ← hq']
  rw [← this]; simp


/-- The centred integer position of a site of `ZMod n`: block position (centred) times `p` plus
the offset in the block. -/
noncomputable def flC (p m : ℕ) (a : ZMod n) : ℤ :=
  ZMod.valMinAbs (blockCoord p m a) * (p : ℤ) + ((a.val % p : ℕ) : ℤ)

theorem flC_cast (hn : n = p * m) (_hp : 0 < p) (_hm : 0 < m) [NeZero m] (a : ZMod n) :
    ((flC p m a : ℤ) : ZMod n) = a := by
  have hnz : (n : ℤ) = p * m := by exact_mod_cast hn
  set q : ℕ := a.val / p with hq
  have hba : blockCoord p m a = ((q : ℕ) : ZMod m) := rfl
  have h1 : ((ZMod.valMinAbs (blockCoord p m a) : ℤ) : ZMod m) = (((q : ℕ) : ℤ) : ZMod m) := by
    rw [ZMod.coe_valMinAbs, hba]; simp
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1.symm
  have h3 : ZMod.valMinAbs (blockCoord p m a) = (q : ℤ) + m * t := by linarith
  have hdm : (a.val : ℤ) = p * q + ((a.val % p : ℕ) : ℤ) := by
    have := Nat.div_add_mod a.val p
    exact_mod_cast this.symm
  have e : (q + m * t) * (p : ℤ) + ((a.val % p : ℕ) : ℤ) = (a.val : ℤ) + (n : ℤ) * t := by
    rw [hnz, hdm]; ring
  unfold flC
  rw [h3, e]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]

theorem flC_intCast (hn : n = p * m) (hp : 0 < p) (hm : 0 < m) [NeZero m] (x : ℤ)
    (hx : 2 * |x / (p : ℤ)| < m) : flC p m ((x : ℤ) : ZMod n) = x := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hb := blockCoord_intCast hn hp hm x
  have h1 : ZMod.valMinAbs (blockCoord p m ((x : ℤ) : ZMod n)) = x / (p : ℤ) := by
    rw [hb, ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    have := abs_lt.1 (show |x / (p : ℤ)| < (m : ℤ) from by
      have := abs_nonneg (x / (p : ℤ)); omega)
    rw [Set.mem_Ioc]
    have h2 := abs_lt.1 (show |x / (p : ℤ) * 2| < m by
      rw [abs_mul]; simp; omega)
    omega
  have h2 : (((x : ZMod n).val % p : ℕ) : ℤ) = x % (p : ℤ) := by
    have : ((x : ZMod n).val : ℤ) = x % (n : ℤ) := ZMod.val_intCast x
    have hpn : (p : ℤ) ∣ (n : ℤ) := by rw [hn]; push_cast; exact dvd_mul_right _ _
    rw [Int.natCast_mod, this, Int.emod_emod_of_dvd _ hpn]
  unfold flC
  rw [h1, h2]
  have := Int.mul_ediv_add_emod x (p : ℤ)
  linarith [mul_comm (x / (p : ℤ)) (p : ℤ)]


theorem valMinAbs_blockCoord_intCast (hn : n = p * m) (hp : 0 < p) (hm : 0 < m) [NeZero m] (x : ℤ)
    (hx : 2 * |x / (p : ℤ)| < m) :
    ZMod.valMinAbs (blockCoord p m ((x : ℤ) : ZMod n)) = x / (p : ℤ) := by
  have hb := blockCoord_intCast hn hp hm x
  rw [hb, ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  have h2 := abs_lt.1 (show |x / (p : ℤ) * 2| < m by
    rw [abs_mul]; simp; omega)
  rw [Set.mem_Ioc]
  omega

omit [NeZero n] in
theorem intCast_inj_of_small {x y : ℤ} (h : (x : ZMod n) = y) (hx : 2 * |x| < n)
    (hy : 2 * |y| < n) : x = y := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y n).1 h
  have : |y - x| < n := by
    calc |y - x| ≤ |y| + |x| := abs_sub _ _
      _ < n := by omega
  have := Int.eq_zero_of_abs_lt_dvd hd this
  omega

theorem aligned_val_iff {s : ℕ} (hs : s ∣ n) (x : ℤ) :
    ((x : ZMod n).val % s = 0) ↔ (s : ℤ) ∣ x := by
  have hsn : (s : ℤ) ∣ (n : ℤ) := by exact_mod_cast hs
  have hv : ((x : ZMod n).val : ℤ) = x % (n : ℤ) := ZMod.val_intCast x
  constructor
  · intro h
    have h1 : (s : ℤ) ∣ ((x : ZMod n).val : ℤ) := by
      have := Nat.dvd_of_mod_eq_zero h
      exact_mod_cast this
    rw [hv] at h1
    have h2 : (s : ℤ) ∣ x - x % (n : ℤ) := by
      have : x - x % (n : ℤ) = (n : ℤ) * (x / (n : ℤ)) := by
        have := Int.mul_ediv_add_emod x (n : ℤ); linarith
      rw [this]; exact Dvd.dvd.mul_right hsn _
    have := dvd_add h2 h1
    simpa using this
  · intro h
    apply Nat.mod_eq_zero_of_dvd
    have h1 : (s : ℤ) ∣ x % (n : ℤ) := by
      have : x % (n : ℤ) = x - (n : ℤ) * (x / (n : ℤ)) := by
        have := Int.mul_ediv_add_emod x (n : ℤ); linarith
      rw [this]
      exact dvd_sub h (Dvd.dvd.mul_right hsn _)
    rw [← hv] at h1
    exact_mod_cast h1

end Coord


section TorusLevel

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The point of the fine torus with integer coordinates `x`. -/
def toTorus (L N₁ m₁ k : ℕ) (x : Fin d → ℤ) : CTorus d L N₁ m₁ k :=
  fun μ => ((x μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ k))

omit [NeZero L] in
omit [NeZero N₁] in
theorem fineLift_apply (j : ℕ) (z : CTorus d L N₁ m₁ k) (μ : Fin d) :
    fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z μ =
      flC (L ^ j) (N₁ * L ^ m₁ * L ^ (k - j)) (z μ) := rfl

theorem toTorus_fineLift {j : ℕ} (hjk : j ≤ k) (z : CTorus d L N₁ m₁ k) :
    toTorus L N₁ m₁ k (fineLift j z) = z := by
  funext μ
  have hm : 0 < N₁ * L ^ m₁ * L ^ (k - j) := by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨hm.ne'⟩
  simp only [toTorus]
  rw [fineLift_apply]
  exact flC_cast (side_eq hjk) (pow_pos (NeZero.pos L) j) hm (z μ)

theorem unlift_toTorus {j : ℕ} (hjk : j ≤ k) (x : Fin d → ℤ)
    (hx : ∀ μ, 2 * |x μ / ((L ^ j : ℕ) : ℤ)| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (toTorus L N₁ m₁ k x) = blockOf L j x := by
  funext μ
  have hm : 0 < N₁ * L ^ m₁ * L ^ (k - j) := by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨hm.ne'⟩
  have := valMinAbs_blockCoord_intCast (n := (N₁ * L ^ m₁) * L ^ k) (side_eq hjk)
    (pow_pos (NeZero.pos L) j) hm (x μ) (by exact_mod_cast hx μ)
  simpa [unlift, jBlock, blockMap, toTorus, blockOf] using this

theorem fineLift_toTorus {j : ℕ} (hjk : j ≤ k) (x : Fin d → ℤ)
    (hx : ∀ μ, 2 * |x μ / ((L ^ j : ℕ) : ℤ)| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) :
    fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (toTorus L N₁ m₁ k x) = x := by
  funext μ
  have hm : 0 < N₁ * L ^ m₁ * L ^ (k - j) := by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨hm.ne'⟩
  rw [fineLift_apply]
  exact flC_intCast (side_eq hjk) (pow_pos (NeZero.pos L) j) hm (x μ) (by exact_mod_cast hx μ)


/-- The shape is small: all its centred block coordinates are well inside the block-level torus of
side `R`, with margin `Q + 1`. -/
def ZSmall (R Q : ℕ) (X' : Finset (Fin d → ℤ)) : Prop :=
  ∀ z ∈ X', ∀ μ, 2 * (|z μ| + (Q : ℤ) + 1) < (R : ℤ)

/-- The set of integer fine sites whose `j`-block lies in `X'`. -/
def yhat (L j : ℕ) (X' : Finset (Fin d → ℤ)) : Set (Fin d → ℤ) := {x | blockOf L j x ∈ X'}

omit [NeZero L] in
theorem blockOf_mem_small {R Q : ℕ} {X' : Finset (Fin d → ℤ)} (hs : ZSmall R Q X')
    {j : ℕ} {x : Fin d → ℤ} (hx : x ∈ yhat L j X') (μ : Fin d) :
    2 * (|x μ / ((L ^ j : ℕ) : ℤ)| + (Q : ℤ) + 1) < (R : ℤ) := hs _ hx μ

omit [NeZero L] in
omit [NeZero N₁] in
theorem toTorus_add (x y : Fin d → ℤ) :
    toTorus L N₁ m₁ k (x + y) = toTorus L N₁ m₁ k x + toTorus L N₁ m₁ k y := by
  funext μ; simp [toTorus]

omit [NeZero L] in
omit [NeZero N₁] in
theorem toTorus_natT (w : Fin d → ℕ) :
    toTorus L N₁ m₁ k (fun μ => (w μ : ℤ)) = natT w := by
  funext μ; simp [toTorus]

omit [NeZero L] in
omit [NeZero N₁] in
theorem toTorus_single (μ : Fin d) :
    toTorus L N₁ m₁ k (Pi.single μ (1 : ℤ)) = Pi.single μ 1 := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [toTorus]
  · simp [toTorus, Pi.single_eq_of_ne h]

/-- A fine site whose block is small has small fine coordinates. -/
theorem abs_le_of_ediv {p : ℕ} (hp : 0 < p) (x : ℤ) : |x| ≤ (p : ℤ) * (|x / (p : ℤ)| + 1) := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have h1 := Int.mul_ediv_add_emod x p
  have h2 : 0 ≤ x % (p : ℤ) := Int.emod_nonneg _ hpz.ne'
  have h3 : x % (p : ℤ) < p := Int.emod_lt_of_pos _ hpz
  rw [abs_le]
  have h4 := abs_nonneg (x / (p : ℤ))
  have h5 := le_abs_self (x / (p : ℤ))
  have h6 := neg_abs_le (x / (p : ℤ))
  constructor <;> nlinarith


theorem Ypoly_eq_image {j : ℕ} (hjk : j ≤ k) {X' : Finset (Fin d → ℤ)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X') :
    Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' =
      toTorus L N₁ m₁ k '' yhat L j X' := by
  ext z
  constructor
  · intro hz
    refine ⟨fineLift j z, ?_, toTorus_fineLift hjk z⟩
    show blockOf L j (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z) ∈ X'
    rw [blockOf_fineLift]; exact hz
  · rintro ⟨x, hx, rfl⟩
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (toTorus L N₁ m₁ k x) ∈ X'
    rw [unlift_toTorus hjk x (fun μ => by
      have h := hs _ hx μ
      change 2 * (|x μ / ((L ^ j : ℕ) : ℤ)| + ((0 : ℕ) : ℤ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) at h
      omega)]
    exact hx

omit [NeZero N₁] in
/-- Fine coordinates of a site with small block are small. -/
theorem fine_small {j Q : ℕ} (hQ : 1 ≤ Q) {X' : Finset (Fin d → ℤ)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) Q X') (hjk : j ≤ k) {x : Fin d → ℤ}
    (hx : x ∈ yhat L j X') (μ : Fin d) :
    2 * |x μ| + 2 < ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) := by
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have h1 := abs_le_of_ediv hp (x μ)
  have h2 : 2 * (|x μ / ((L ^ j : ℕ) : ℤ)| + (Q : ℤ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := hs _ hx μ
  have hQz : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hf : ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) = ((L ^ j : ℕ) : ℤ) * ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    exact_mod_cast side_eq hjk
  rw [hf]
  have hpz : (1 : ℤ) ≤ ((L ^ j : ℕ) : ℤ) := by exact_mod_cast hp
  have h3 : 2 * (|x μ / ((L ^ j : ℕ) : ℤ)| + 1) + 2 < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    linarith
  nlinarith


/-- Nearest neighbours in `ℤ^d`. -/
def NbrZ (a b : Fin d → ℤ) : Prop := ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1

/-- The box `b + [0, n)^d` of `ℤ^d`. -/
def boxZ (b : Fin d → ℤ) (n : ℕ) : Set (Fin d → ℤ) :=
  {x | ∃ w : Fin d → ℕ, (∀ μ, w μ < n) ∧ x = b + fun μ => (w μ : ℤ)}

/-- **A polymer of `𝒟_j` in `ℤ^d`** (fine sites): a nonempty union of `π'_j`-cubes (boxes of side
`L · cellSide` with base divisible by the cell side) that is nearest-neighbour connected. -/
def PolyZ (L m₀ m₁ j : ℕ) (Y : Set (Fin d → ℤ)) : Prop :=
  Y.Nonempty ∧ (∃ 𝒦 : Set (Fin d → ℤ),
      (∀ b ∈ 𝒦, (∀ μ, ((cellSide L m₀ m₁ j : ℕ) : ℤ) ∣ b μ) ∧
        boxZ b (L * cellSide L m₀ m₁ j) ⊆ Y) ∧
      ∀ x ∈ Y, ∃ b ∈ 𝒦, x ∈ boxZ b (L * cellSide L m₀ m₁ j)) ∧
    ∀ x ∈ Y, ∀ y ∈ Y, Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ NbrZ a b) x y

omit [NeZero L] in
omit [NeZero N₁] in
theorem nbr_toTorus {a b : Fin d → ℤ} (h : NbrZ a b) :
    Nbr (toTorus L N₁ m₁ k a) (toTorus L N₁ m₁ k b) := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inl (by rw [h, toTorus_add, toTorus_single])⟩
  · exact ⟨μ, Or.inr (by rw [h, toTorus_add, toTorus_single])⟩

theorem aligned_toTorus {s : ℕ} (hs : s ∣ N₁ * L ^ m₁ * L ^ k) {b : Fin d → ℤ}
    (hb : ∀ μ, (s : ℤ) ∣ b μ) : Aligned s (toTorus L N₁ m₁ k b) := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  intro μ
  exact (aligned_val_iff hs (b μ)).2 (hb μ)

theorem dvd_of_aligned {s : ℕ} (hs : s ∣ N₁ * L ^ m₁ * L ^ k) {j : ℕ} (hjk : j ≤ k)
    {b : CTorus d L N₁ m₁ k} (hb : Aligned s b) (μ : Fin d) :
    (s : ℤ) ∣ fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b μ := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  rw [← aligned_val_iff hs]
  have := congrFun (toTorus_fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk b) μ
  simp only [toTorus] at this
  rw [this]
  exact hb μ

/-- **A polymer of the lattice `ℤ^d` gives a polymer of the torus** whose shape is small. -/
theorem isPolyDom_of_polyZ {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁) {X' : Finset (Fin d → ℤ)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 X')
    (h : PolyZ L m₀ m₁ j (yhat L j X')) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  rw [Ypoly_eq_image hjk hs]
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hcon⟩ := h
  have hsd : cellSide L m₀ m₁ j ∣ N₁ * L ^ m₁ * L ^ k := cellSide_dvd hN hjk
  refine ⟨hne.image _, ⟨toTorus L N₁ m₁ k '' 𝒦, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨aligned_toTorus hsd (hK1 b hb).1, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨b + fun μ => (w μ : ℤ), (hK1 b hb).2 ⟨w, hw, rfl⟩, ?_⟩
    rw [toTorus_add, toTorus_natT]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, w, hw, rfl⟩ := hK2 x hx
    refine ⟨toTorus L N₁ m₁ k b, ⟨b, hb, rfl⟩, w, hw, ?_⟩
    rw [toTorus_add, toTorus_natT]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine (hcon x hx y hy).lift (toTorus L N₁ m₁ k) ?_
    rintro a b ⟨ha, hb, hab⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, nbr_toTorus hab⟩


theorem cellSide_eq_mul (L m₀ m₁ j : ℕ) :
    cellSide L m₀ m₁ j = L ^ j * L ^ (m₀ + m₁) := by
  unfold cellSide; rw [← pow_add]; congr 1; ring

theorem ediv_add_small {p Q : ℕ} (hp : 0 < p) {b w : ℤ} (hb : (p : ℤ) ∣ b) (hw0 : 0 ≤ w)
    (hw : w < (p : ℤ) * Q) : |(b + w) / (p : ℤ)| ≤ |b / (p : ℤ)| + Q := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  rw [Int.add_ediv_of_dvd_left hb]
  have h1 : 0 ≤ w / (p : ℤ) := Int.ediv_nonneg hw0 hpz.le
  have h2 : w / (p : ℤ) < Q := by
    rw [Int.ediv_lt_iff_lt_mul hpz]; linarith
  calc |b / (p : ℤ) + w / (p : ℤ)| ≤ |b / (p : ℤ)| + |w / (p : ℤ)| := abs_add_le _ _
    _ ≤ |b / (p : ℤ)| + Q := by rw [abs_of_nonneg h1]; linarith

/-- **A polymer of the torus whose shape is small gives a polymer of the lattice `ℤ^d`.** -/
theorem polyZ_of_isPolyDom {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁) {X' : Finset (Fin d → ℤ)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (m₀ + m₁)) X')
    (h : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    PolyZ L m₀ m₁ j (yhat L j X') := by
  classical
  set Rb := N₁ * L ^ m₁ * L ^ (k - j) with hRb
  set Q := L * L ^ (m₀ + m₁) with hQdef
  have hLp : 0 < L := NeZero.pos L
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hp : 0 < L ^ j := pow_pos hLp j
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by have := NeZero.pos N₁; positivity⟩
  have hs0 : ZSmall Rb 0 X' := fun z hz μ => by
    have := hs z hz μ; push_cast at this ⊢; omega
  have hY := Ypoly_eq_image (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk hs0
  have hsd : cellSide L m₀ m₁ j ∣ N₁ * L ^ m₁ * L ^ k := cellSide_dvd hN hjk
  have hspos : 0 < L * cellSide L m₀ m₁ j := Nat.mul_pos hLp (cellSide_pos m₀ m₁ j)
  have hLs : L * cellSide L m₀ m₁ j = L ^ j * Q := by
    rw [cellSide_eq_mul, hQdef]; ring
  have hpdvd : ((L ^ j : ℕ) : ℤ) ∣ ((cellSide L m₀ m₁ j : ℕ) : ℤ) := by
    rw [cellSide_eq_mul]; push_cast; exact dvd_mul_right _ _
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hcon⟩ := h
  -- the points of the lifted boxes
  have hbox : ∀ b ∈ 𝒦, ∀ w : Fin d → ℕ, (∀ μ, w μ < L * cellSide L m₀ m₁ j) →
      (∀ μ, 2 * (|(fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b +
          fun μ => (w μ : ℤ)) μ / ((L ^ j : ℕ) : ℤ)| + 1) < (Rb : ℤ)) ∧
      (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b + fun μ => (w μ : ℤ)) ∈ yhat L j X' := by
    intro b hb w hw
    have hbY : b ∈ box b (L * cellSide L m₀ m₁ j) := mem_box_self b hspos
    have hbY' : b ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := (hK1 b hb).2 hbY
    have hA : ∀ μ, 2 * (|(fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b +
          fun μ => (w μ : ℤ)) μ / ((L ^ j : ℕ) : ℤ)| + 1) < (Rb : ℤ) := by
      intro μ
      simp only [Pi.add_apply]
      have hz0 : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b ∈ X' := hbY'
      have hdv : ((L ^ j : ℕ) : ℤ) ∣ fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b μ :=
        hpdvd.trans (dvd_of_aligned hsd hjk (hK1 b hb).1 μ)
      have hw' : (w μ : ℤ) < ((L ^ j : ℕ) : ℤ) * (Q : ℤ) := by
        have := hw μ; rw [hLs] at this; exact_mod_cast this
      have h1 := ediv_add_small hp hdv (Int.natCast_nonneg _) hw'
      have h2 : fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b μ / ((L ^ j : ℕ) : ℤ) =
          unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b μ := by
        have := congrFun (blockOf_fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b) μ
        exact this
      rw [h2] at h1
      have h3 := hs _ hz0 μ
      omega
    refine ⟨hA, ?_⟩
    have hmem : toTorus L N₁ m₁ k (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b +
        fun μ => (w μ : ℤ)) ∈ box b (L * cellSide L m₀ m₁ j) := by
      refine ⟨w, hw, ?_⟩
      rw [toTorus_add, toTorus_fineLift hjk, toTorus_natT]
    have := (hK1 b hb).2 hmem
    change unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j _ ∈ X' at this
    rw [unlift_toTorus hjk _ (fun μ => by have := hA μ; omega)] at this
    exact this
  refine ⟨?_, ⟨fineLift j '' 𝒦, ?_, ?_⟩, ?_⟩
  · obtain ⟨z, hz⟩ := hne
    refine ⟨fineLift j z, ?_⟩
    show blockOf L j (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z) ∈ X'
    rw [blockOf_fineLift]; exact hz
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨fun μ => dvd_of_aligned hsd hjk (hK1 b hb).1 μ, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact (hbox b hb w hw).2
  · intro x hx
    have hxY : toTorus L N₁ m₁ k x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := by
      rw [hY]; exact ⟨x, hx, rfl⟩
    obtain ⟨b, hb, w, hw, hxw⟩ := hK2 _ hxY
    refine ⟨fineLift j b, ⟨b, hb, rfl⟩, w, hw, ?_⟩
    obtain ⟨hA, -⟩ := hbox b hb w hw
    funext μ
    have hf : toTorus L N₁ m₁ k (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b +
        fun μ => (w μ : ℤ)) = toTorus L N₁ m₁ k x := by
      rw [toTorus_add, toTorus_fineLift hjk, toTorus_natT, ← hxw]
    have hμ := congrFun hf μ
    simp only [toTorus] at hμ
    refine (intCast_inj_of_small hμ ?_ ?_).symm
    · have h1 := abs_le_of_ediv hp ((fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b +
        fun μ => (w μ : ℤ)) μ)
      have h2 := hA μ
      have hf' : ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) =
          ((L ^ j : ℕ) : ℤ) * (Rb : ℤ) := by exact_mod_cast side_eq hjk
      rw [hf']
      have hpz : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast hp
      simp only [Pi.add_apply] at h1 h2 ⊢
      nlinarith
    · have := fine_small hQ1 hs hjk hx μ
      omega
  · intro x hx y hy
    have hblk : ∀ z ∈ yhat L j X', ∀ μ, 2 * |z μ / ((L ^ j : ℕ) : ℤ)| < (Rb : ℤ) := by
      intro z hz μ
      have h : 2 * (|z μ / ((L ^ j : ℕ) : ℤ)| + ((Q : ℕ) : ℤ) + 1) < (Rb : ℤ) := hs _ hz μ
      have : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
      omega
    have hyh : ∀ q : CTorus d L N₁ m₁ k, q ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' →
        fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j q ∈ yhat L j X' := by
      intro q hq
      show blockOf L j (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j q) ∈ X'
      rw [blockOf_fineLift]; exact hq
    have hstep : ∀ b c : CTorus d L N₁ m₁ k, b ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' →
        c ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' → Nbr b c →
        NbrZ (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b)
          (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j c) := by
      have inj : ∀ (u v : Fin d → ℤ), toTorus L N₁ m₁ k u = toTorus L N₁ m₁ k v →
          (∀ μ, 2 * |u μ| < ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ)) →
          (∀ μ, 2 * |v μ| < ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ)) → u = v := by
        intro u v huv hu hv
        funext μ
        exact intCast_inj_of_small (congrFun huv μ) (hu μ) (hv μ)
      rintro b c hb hc ⟨μ, h | h⟩
      · refine ⟨μ, Or.inl ?_⟩
        refine (inj _ _ ?_ ?_ ?_).symm
        · rw [toTorus_add, toTorus_single, toTorus_fineLift hjk, toTorus_fineLift hjk, h]
        · intro ν
          have := fine_small hQ1 hs hjk (hyh b hb) ν
          simp only [Pi.add_apply]
          have h1 : |fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b ν + (Pi.single μ (1 : ℤ) : Fin d → ℤ) ν| ≤
              |fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j b ν| + 1 := by
            refine (abs_add_le _ _).trans ?_
            have : |(Pi.single μ (1 : ℤ) : Fin d → ℤ) ν| ≤ 1 := by
              by_cases hν : ν = μ
              · subst hν; simp
              · simp [Pi.single_eq_of_ne hν]
            linarith
          omega
        · intro ν
          have := fine_small hQ1 hs hjk (hyh c hc) ν
          omega
      · refine ⟨μ, Or.inr ?_⟩
        refine (inj _ _ ?_ ?_ ?_).symm
        · rw [toTorus_add, toTorus_single, toTorus_fineLift hjk, toTorus_fineLift hjk, h]
        · intro ν
          have := fine_small hQ1 hs hjk (hyh c hc) ν
          simp only [Pi.add_apply]
          have h1 : |fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j c ν + (Pi.single μ (1 : ℤ) : Fin d → ℤ) ν| ≤
              |fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j c ν| + 1 := by
            refine (abs_add_le _ _).trans ?_
            have : |(Pi.single μ (1 : ℤ) : Fin d → ℤ) ν| ≤ 1 := by
              by_cases hν : ν = μ
              · subst hν; simp
              · simp [Pi.single_eq_of_ne hν]
            linarith
          omega
        · intro ν
          have := fine_small hQ1 hs hjk (hyh b hb) ν
          omega
    have key : ∀ p q : CTorus d L N₁ m₁ k,
        Relation.ReflTransGen (fun a b => a ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ∧
          b ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ∧ Nbr a b) p q →
        Relation.ReflTransGen (fun a b => a ∈ yhat L j X' ∧ b ∈ yhat L j X' ∧ NbrZ a b)
          (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j p)
          (fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j q) := by
      intro p q hpq
      induction hpq with
      | refl => exact Relation.ReflTransGen.refl
      | tail hab hbc ih =>
        rename_i b c
        exact ih.tail ⟨hyh b hbc.1, hyh c hbc.2.1, hstep b c hbc.1 hbc.2.1 hbc.2.2⟩
    have hxY : toTorus L N₁ m₁ k x ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := by
      rw [hY]; exact ⟨x, hx, rfl⟩
    have hyY : toTorus L N₁ m₁ k y ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := by
      rw [hY]; exact ⟨y, hy, rfl⟩
    have := key _ _ (hcon _ hxY _ hyY)
    rwa [fineLift_toTorus hjk x (hblk x hx), fineLift_toTorus hjk y (hblk y hy)] at this

/-- **Transfer of polymers between tori**: a small shape that is the lift of a polymer of `𝒟_j` on
one torus of the sequence is the lift of a polymer on every torus on which it is small. -/
theorem isPolyDom_transfer {m₀ j : ℕ} (hjk : j ≤ k) {N₂ : ℕ} [NeZero N₂] (hN : L ^ m₀ ∣ N₁)
    (hN₂ : L ^ m₀ ∣ N₂) {X' : Finset (Fin d → ℤ)}
    (hs : ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) (L * L ^ (m₀ + m₁)) X')
    (hs₂ : ZSmall (N₂ * L ^ m₁ * L ^ (k - j)) 0 X')
    (h : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k) j X') :=
  isPolyDom_of_polyZ hjk hN₂ hs₂ (polyZ_of_isPolyDom hjk hN hs h)

end TorusLevel

end Balaban.SmallField.Def6
