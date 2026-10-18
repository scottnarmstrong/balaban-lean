/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfPoly
public import Balaban.SmallField.Def6InfTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Polymers in the quarter box of a torus

A finite set `A ⊂ ℤ^d` of fine sites in the quarter box `4|y_μ| < ℓ` of the torus
`𝕋_ℓ`, `ℓ = N₁ L^{m₁} L^k`, is sent injectively to `𝕋_ℓ` by `toTorus`, and the nearest-neighbour
steps and the boxes `b + [0, s)^d` of `𝕋_ℓ` that stay in the image of `A` come from those of
`ℤ^d` (`box_lift`, `nbrZ_of_nbr`). Consequently the image of `A` is a polymer of `𝒟_j`
(`IsPolyDom`) on `𝕋_ℓ` iff `A` is a polymer of `ℤ^d` (`PolyZ`), a condition that does not mention
the torus (`isPolyDom_toTorus_iff`). The set `A` is then a union of `j`-blocks, so that its image is
the lift `Ypoly j X'` of the set `X'` of its blocks (`Ypoly_eq_toTorus_image`), which does not
wind around the torus (`nonWind_blocks`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Localization Balaban.SmallField.Def6

section Integers

/-- The quarter box `4|y_μ| < ℓ` of the torus `𝕋_ℓ` in `ℤ^d`. -/
def QBox (d ℓ : ℕ) (y : Fin d → ℤ) : Prop := ∀ μ, 4 * |y μ| < (ℓ : ℤ)

theorem abs4_iff {x : ℤ} {n : ℕ} : 4 * |x| < (n : ℤ) ↔ -(n : ℤ) < 4 * x ∧ 4 * x < (n : ℤ) := by
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> omega

/-- Two integers of the quarter box that are congruent modulo `ℓ`, up to a shift of absolute value
`≤ 1`, are equal up to that shift. -/
theorem eq_of_cast_eq_small {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {x y e : ℤ} (hx : 4 * |x| < (ℓ : ℤ))
    (hy : 4 * |y| < (ℓ : ℤ)) (he : |e| ≤ 1)
    (h : ((x : ℤ) : ZMod ℓ) = ((y + e : ℤ) : ZMod ℓ)) : x = y + e := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
  rw [abs4_iff] at hx hy
  rw [abs_le] at he
  have h0 := Int.eq_zero_of_abs_lt_dvd hd (by
    rw [abs_lt]
    constructor <;> omega)
  omega

/-- Block coordinates of a point of the quarter box are small (the form of `ZSmall` with margin
`0`): `2(|⌊x/p⌋| + 1) < R` when `4|x| < p R` and `8 ≤ R`. -/
theorem ediv_small {p R x : ℤ} (hp : 0 < p) (hR : 8 ≤ R) (h : 4 * |x| < p * R) :
    2 * (|x / p| + 1) < R := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 : 0 ≤ x / p := Int.ediv_nonneg hx hp.le
    have h2 : p * (x / p) ≤ x := Int.mul_ediv_self_le hp.ne'
    rw [abs_of_nonneg hx] at h
    have h3 : p * (4 * (x / p)) < p * R := by nlinarith
    have h4 := lt_of_mul_lt_mul_left h3 hp.le
    rw [abs_of_nonneg h1]
    omega
  · have h1 : x / p < 0 := Int.ediv_neg_of_neg_of_pos hx hp
    have h2 : x < p * (x / p) + p := Int.lt_mul_ediv_self_add hp
    rw [abs_of_neg hx] at h
    have h3 : p * (4 * (-(x / p) - 1)) < p * R := by nlinarith
    have h4 := lt_of_mul_lt_mul_left h3 hp.le
    rw [abs_of_neg h1]
    omega

theorem valMinAbs_of_qbox {ℓ : ℕ} [NeZero ℓ] {x : ℤ} (hx : 4 * |x| < (ℓ : ℤ)) :
    ZMod.valMinAbs ((x : ℤ) : ZMod ℓ) = x := by
  have h0 := abs_nonneg x
  exact valMinAbs_intCast_of_small (by omega)

end Integers

section Torus

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
/-- On the quarter box the map `toTorus` is injective. -/
theorem toTorus_inj_of_qbox (hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k) {x y : Fin d → ℤ}
    (hx : QBox d (N₁ * L ^ m₁ * L ^ k) x) (hy : QBox d (N₁ * L ^ m₁ * L ^ k) y)
    (h : toTorus L N₁ m₁ k x = toTorus L N₁ m₁ k y) : x = y := by
  funext μ
  have := congrFun h μ
  simp only [toTorus] at this
  have := eq_of_cast_eq_small hℓ (hx μ) (hy μ) (e := 0) (by simp) (by simpa using this)
  simpa using this

omit [NeZero L] [NeZero N₁] in
/-- A point of the quarter box is recovered from its image by the centred representative. -/
theorem valMinAbs_toTorus (hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k) {y : Fin d → ℤ}
    (hy : QBox d (N₁ * L ^ m₁ * L ^ k) y) (μ : Fin d) :
    ZMod.valMinAbs (toTorus L N₁ m₁ k y μ) = y μ := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by omega⟩
  exact valMinAbs_of_qbox (hy μ)

omit [NeZero L] [NeZero N₁] in
/-- A unit step of the torus between two points of the quarter box comes from a unit step of
`ℤ^d`. -/
theorem eq_add_single_of_toTorus (hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k) {y z : Fin d → ℤ}
    (hy : QBox d (N₁ * L ^ m₁ * L ^ k) y) (hz : QBox d (N₁ * L ^ m₁ * L ^ k) z) {μ : Fin d}
    (h : toTorus L N₁ m₁ k z = toTorus L N₁ m₁ k y + Pi.single μ 1) :
    z = y + Pi.single μ 1 := by
  funext ν
  have h1 := congrFun h ν
  have h2 := congrFun (toTorus_single (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) μ) ν
  simp only [toTorus, Pi.add_apply] at h1 h2
  rw [← h2] at h1
  have := eq_of_cast_eq_small hℓ (hz ν) (hy ν) (e := (Pi.single μ (1 : ℤ) : Fin d → ℤ) ν)
    (by by_cases hν : ν = μ <;> simp [hν]) (by push_cast; exact h1)
  simpa using this

omit [NeZero L] [NeZero N₁] in
/-- **Boxes of the torus that stay in the image of a set of the quarter box lift to boxes of
`ℤ^d`**: if the points `b + w`, `0 ≤ w_μ < s`, of `𝕋_ℓ` are images of points of `A` for the image
`b` of `a ∈ A`, then `a + w ∈ A`. -/
theorem box_lift (hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y) {a : Fin d → ℤ} (ha : a ∈ A) {s : ℕ}
    (hbox : ∀ w : Fin d → ℕ, (∀ μ, w μ < s) →
      toTorus L N₁ m₁ k (a + fun μ => (w μ : ℤ)) ∈ toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ))) :
    ∀ w : Fin d → ℕ, (∀ μ, w μ < s) → (a + fun μ => (w μ : ℤ)) ∈ A := by
  suffices H : ∀ n : ℕ, ∀ w : Fin d → ℕ, ∑ μ, w μ = n → (∀ μ, w μ < s) →
      (a + fun μ => (w μ : ℤ)) ∈ A from fun w hw => H _ w rfl hw
  intro n
  induction n with
  | zero =>
    intro w hw0 _
    have : w = 0 := funext fun μ => by
      simpa using (Finset.sum_eq_zero_iff.1 hw0) μ (Finset.mem_univ μ)
    subst this
    have e : (a + fun μ => (((0 : Fin d → ℕ) μ : ℕ) : ℤ)) = a := by
      funext μ
      simp
    rw [e]
    exact ha
  | succ n ih =>
    intro w hw hlt
    obtain ⟨μ, hμ⟩ : ∃ μ, 0 < w μ := by
      by_contra hcon
      push Not at hcon
      have : ∑ ν, w ν = 0 := Finset.sum_eq_zero fun ν _ => Nat.le_zero.1 (hcon ν)
      omega
    set w' : Fin d → ℕ := Function.update w μ (w μ - 1) with hw'
    have hw'sum : ∑ ν, w' ν = n := by
      have h1 := Finset.add_sum_erase Finset.univ w' (Finset.mem_univ μ)
      have h2 := Finset.add_sum_erase Finset.univ w (Finset.mem_univ μ)
      have h3 : ∑ ν ∈ Finset.univ.erase μ, w' ν = ∑ ν ∈ Finset.univ.erase μ, w ν :=
        Finset.sum_congr rfl fun ν hν => by
          simp [hw', Function.update_of_ne (Finset.ne_of_mem_erase hν)]
      have h4 : w' μ = w μ - 1 := by simp [hw']
      omega
    have hlt' : ∀ ν, w' ν < s := fun ν => by
      by_cases hν : ν = μ
      · subst hν
        have := hlt ν
        simp only [hw', Function.update_self]
        omega
      · simpa [hw', Function.update_of_ne hν] using hlt ν
    have hx := ih w' hw'sum hlt'
    obtain ⟨a'', ha'', he⟩ := hbox w hlt
    have hcoord : ∀ ν, (a + fun μ => (w μ : ℤ)) ν =
        (a + fun μ => (w' μ : ℤ)) ν + (if ν = μ then 1 else 0) := by
      intro ν
      by_cases hν : ν = μ
      · subst hν
        simp only [Pi.add_apply, hw', Function.update_self, ite_true]
        omega
      · simp [hw', hν]
    have hfin : a'' = a + fun μ => (w μ : ℤ) := by
      funext ν
      have hc := congrFun he ν
      simp only [toTorus] at hc
      rw [hcoord ν] at hc
      have := eq_of_cast_eq_small hℓ (hA a'' ha'' ν) (hA _ hx ν)
        (e := if ν = μ then 1 else 0) (by split_ifs <;> simp) hc
      rw [this, hcoord ν]
    rw [← hfin]
    exact ha''

omit [NeZero N₁] in
/-- **A polymer of `𝒟_j` on `𝕋_ℓ` inside the image of the quarter box is a polymer of `ℤ^d`.** -/
theorem polyZ_of_isPolyDom_qbox {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    (hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y)
    (h : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)))) :
    PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ)) := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by omega⟩
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hcon⟩ := h
  have hsd : cellSide L m₀ m₁ j ∣ N₁ * L ^ m₁ * L ^ k := cellSide_dvd hN hjk
  have hspos : 0 < L * cellSide L m₀ m₁ j := Nat.mul_pos (NeZero.pos L) (cellSide_pos m₀ m₁ j)
  have hlift : ∀ b ∈ A, toTorus L N₁ m₁ k b ∈ 𝒦 → ∀ w : Fin d → ℕ,
      (∀ μ, w μ < L * cellSide L m₀ m₁ j) → (b + fun μ => (w μ : ℤ)) ∈ A := by
    intro b hb hb𝒦
    refine box_lift hℓ hA hb (fun w hw => ?_)
    have hmem : toTorus L N₁ m₁ k b + natT w ∈
        box (toTorus L N₁ m₁ k b) (L * cellSide L m₀ m₁ j) := ⟨w, hw, rfl⟩
    have := (hK1 _ hb𝒦).2 hmem
    rwa [← toTorus_natT (L := L) (N₁ := N₁) (m₁ := m₁) (k := k), ← toTorus_add] at this
  refine ⟨?_, ⟨{b | b ∈ A ∧ toTorus L N₁ m₁ k b ∈ 𝒦}, ?_, ?_⟩, ?_⟩
  · obtain ⟨_, a, ha, -⟩ := hne
    exact ⟨a, ha⟩
  · rintro b ⟨hb, hb𝒦⟩
    refine ⟨fun μ => (aligned_val_iff hsd (b μ)).1 ((hK1 _ hb𝒦).1 μ), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hlift b hb hb𝒦 w hw
  · intro x hx
    have hxX : toTorus L N₁ m₁ k x ∈ toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)) := ⟨x, hx, rfl⟩
    obtain ⟨b, hb𝒦, w, hw, hxw⟩ := hK2 _ hxX
    have hbX := (hK1 b hb𝒦).2 (mem_box_self b hspos)
    obtain ⟨b', hb'A, rfl⟩ := hbX
    refine ⟨b', ⟨hb'A, hb𝒦⟩, w, hw, ?_⟩
    have hmem := hlift b' hb'A hb𝒦 w hw
    refine toTorus_inj_of_qbox hℓ (hA x hx) (hA _ hmem) ?_
    rw [hxw, toTorus_add, toTorus_natT]
  · have key : ∀ p q : CTorus d L N₁ m₁ k, Relation.ReflTransGen (fun a b =>
        a ∈ toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)) ∧
        b ∈ toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)) ∧ Nbr a b) p q →
        ∀ x ∈ A, p = toTorus L N₁ m₁ k x → ∃ y ∈ A, q = toTorus L N₁ m₁ k y ∧
          Relation.ReflTransGen (fun a b => a ∈ (A : Set (Fin d → ℤ)) ∧
            b ∈ (A : Set (Fin d → ℤ)) ∧ NbrZ a b) x y := by
      intro p q hpq
      induction hpq with
      | refl => exact fun x hx hp => ⟨x, hx, hp, Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        intro x hx hp
        obtain ⟨y, hy, hqy, hrt⟩ := ih x hx hp
        obtain ⟨z, hz, hzc⟩ := hbc.2.1
        have hnb : NbrZ y z := by
          obtain ⟨μ, hμ | hμ⟩ := hbc.2.2
          · refine ⟨μ, Or.inl (eq_add_single_of_toTorus hℓ (hA y hy) (hA z hz) ?_)⟩
            rw [hzc, hμ, hqy]
          · refine ⟨μ, Or.inr (eq_add_single_of_toTorus hℓ (hA z hz) (hA y hy) ?_)⟩
            rw [hzc, ← hqy]
            exact hμ
        exact ⟨z, hz, hzc.symm, hrt.tail ⟨hy, hz, hnb⟩⟩
    intro x hx y hy
    obtain ⟨y', hy', hq, hrt⟩ := key _ _ (hcon _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩) x hx rfl
    have : y = y' := toTorus_inj_of_qbox hℓ (hA y hy) (hA y' hy') hq
    rwa [this]

end Torus

section Blocks

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- Two integers in the same block of side `p` as a point `b + w` of the box `b + [0, s)^d`
(`p ∣ b`, `p ∣ s`) lie in the box. -/
theorem sameBlock_box {p s a x b w : ℤ} (hp : 0 < p) (hb : p ∣ b) (hs : p ∣ s) (hw0 : 0 ≤ w)
    (hw : w < s) (ha : a = b + w) (hax : x / p = a / p) : 0 ≤ x - b ∧ x - b < s := by
  obtain ⟨qb, rfl⟩ := hb
  obtain ⟨S, rfl⟩ := hs
  have hx1 : x = p * (x / p) + x % p := (Int.mul_ediv_add_emod x p).symm
  have hx2 : 0 ≤ x % p := Int.emod_nonneg _ hp.ne'
  have hx3 : x % p < p := Int.emod_lt_of_pos _ hp
  have hq : x / p = w / p + qb := by
    rw [hax, ha, add_comm, Int.add_mul_ediv_left _ _ hp.ne']
  have hw1 : 0 ≤ w / p := Int.ediv_nonneg hw0 hp.le
  have hw2 : w / p < S := (Int.ediv_lt_iff_lt_mul hp).2 (by linarith)
  have hw3 : p * (w / p) ≤ p * (S - 1) := mul_le_mul_of_nonneg_left (by omega) hp.le
  have e : x - p * qb = p * (w / p) + x % p := by
    rw [hq] at hx1
    linarith
  constructor
  · nlinarith [mul_nonneg hp.le hw1]
  · nlinarith

/-- The set of `j`-blocks of a polymer of `ℤ^d` determines it: the polymer is a union of
`j`-blocks (its cubes have sides and bases divisible by `L^j`). -/
theorem yhat_image_blockOf {m₀ j : ℕ} {A : Finset (Fin d → ℤ)}
    (h : PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ))) :
    yhat L j (A.image (blockOf L j)) = (A : Set (Fin d → ℤ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.1 hx
    obtain ⟨-, ⟨𝒦, hK1, hK2⟩, -⟩ := h
    obtain ⟨b, hb, w, hw, haw⟩ := hK2 a (Finset.mem_coe.2 ha)
    have hp : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast pow_pos (NeZero.pos L) j
    have hcs : ((L ^ j : ℕ) : ℤ) ∣ ((cellSide L m₀ m₁ j : ℕ) : ℤ) := by
      unfold cellSide
      exact_mod_cast pow_dvd_pow L (by omega)
    have hbx : ∀ μ, 0 ≤ x μ - b μ ∧ x μ - b μ < ((L * cellSide L m₀ m₁ j : ℕ) : ℤ) := by
      intro μ
      refine sameBlock_box hp (hcs.trans ((hK1 b hb).1 μ)) ?_ (Int.natCast_nonneg _)
        (by exact_mod_cast hw μ) (congrFun haw μ) (congrFun hab μ).symm
      push_cast
      exact Dvd.dvd.mul_left hcs _
    refine (hK1 b hb).2 ⟨fun μ => (x μ - b μ).toNat, fun μ => ?_, ?_⟩
    · have := hbx μ
      show (x μ - b μ).toNat < L * cellSide L m₀ m₁ j
      omega
    · funext μ
      have := hbx μ
      simp only [Pi.add_apply]
      omega
  · intro hx
    exact Finset.mem_image.2 ⟨x, Finset.mem_coe.1 hx, rfl⟩

omit [NeZero L] [NeZero N₁] in
theorem ell_eq {j : ℕ} (hjk : j ≤ k) :
    N₁ * L ^ m₁ * L ^ k = L ^ j * (N₁ * L ^ m₁ * L ^ (k - j)) := by
  have : L ^ k = L ^ j * L ^ (k - j) := by rw [← pow_add]; congr 1; omega
  rw [this]
  ring

theorem eight_le_R {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hM8 : 8 ≤ L ^ (m₀ + m₁)) :
    8 ≤ N₁ * L ^ m₁ * L ^ (k - j) := by
  have h1 : L ^ m₀ ≤ N₁ := Nat.le_of_dvd (NeZero.pos N₁) hN
  have h2 : 1 ≤ L ^ (k - j) := Nat.one_le_pow _ _ (NeZero.pos L)
  calc 8 ≤ L ^ (m₀ + m₁) := hM8
    _ = L ^ m₀ * L ^ m₁ := pow_add _ _ _
    _ ≤ N₁ * L ^ m₁ := Nat.mul_le_mul_right _ h1
    _ ≤ N₁ * L ^ m₁ * L ^ (k - j) := Nat.le_mul_of_pos_right _ (by omega)

omit [NeZero N₁] in
/-- The set of blocks of a set of the quarter box is small in the block torus. -/
theorem zSmall_blocks {j : ℕ} (hjk : j ≤ k) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y) (hR : 8 ≤ N₁ * L ^ m₁ * L ^ (k - j)) :
    ZSmall (N₁ * L ^ m₁ * L ^ (k - j)) 0 (A.image (blockOf L j)) := by
  intro z hz μ
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hz
  have h := hA a ha μ
  rw [ell_eq hjk] at h
  have hp : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast pow_pos (NeZero.pos L) j
  have := ediv_small hp (R := ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) (by exact_mod_cast hR)
    (x := a μ) (by push_cast at h ⊢; exact h)
  simpa [blockOf] using this

/-- A set of the quarter box that is a polymer of `ℤ^d` has as image the lift `Ypoly` of the set
of its blocks. -/
theorem Ypoly_eq_toTorus_image {m₀ j : ℕ} (hjk : j ≤ k) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y) (hR : 8 ≤ N₁ * L ^ m₁ * L ^ (k - j))
    (h : PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ))) :
    Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (A.image (blockOf L j)) =
      toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ)) := by
  rw [Ypoly_eq_image hjk (zSmall_blocks hjk hA hR), yhat_image_blockOf h]

omit [NeZero N₁] in
/-- The set of blocks of a set of the quarter box does not wind around the torus. -/
theorem nonWind_blocks {j : ℕ} (hjk : j ≤ k) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y) (hR : 8 ≤ N₁ * L ^ m₁ * L ^ (k - j)) :
    NonWind L N₁ m₁ k j (A.image (blockOf L j)) := by
  intro z hz μ
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by omega⟩
  have h := zSmall_blocks hjk hA hR z hz μ
  have h0 := abs_nonneg (z μ)
  exact valMinAbs_intCast_of_small (by push_cast at h ⊢; omega)

/-- **A set of the quarter box of `𝕋_ℓ` is a polymer of `𝒟_j` iff it is a polymer of `ℤ^d`**, a
condition that does not mention the torus. -/
theorem isPolyDom_toTorus_iff {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    (hM8 : 8 ≤ L ^ (m₀ + m₁)) {A : Finset (Fin d → ℤ)}
    (hA : ∀ y ∈ A, QBox d (N₁ * L ^ m₁ * L ^ k) y) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
        (toTorus L N₁ m₁ k '' (A : Set (Fin d → ℤ))) ↔ PolyZ L m₀ m₁ j (A : Set (Fin d → ℤ)) := by
  have hR := eight_le_R (k := k) (j := j) hN hM8
  have hℓ : 2 ≤ N₁ * L ^ m₁ * L ^ k := by
    rw [ell_eq hjk]
    have := Nat.one_le_pow j L (NeZero.pos L)
    nlinarith
  refine ⟨polyZ_of_isPolyDom_qbox hjk hN hℓ hA, fun h => ?_⟩
  rw [← Ypoly_eq_toTorus_image hjk hA hR h]
  refine isPolyDom_of_polyZ hjk hN (zSmall_blocks hjk hA hR) ?_
  rw [yhat_image_blockOf h]
  exact h


end Blocks

end Balaban.RootFSpine
