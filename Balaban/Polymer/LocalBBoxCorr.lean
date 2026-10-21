/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GSIsoOfOmega
public import Balaban.SmallField.LocalGeneratorSource

/-!
# The local generating sets of corresponding polymers on two tori

`localB_omega_boxMap`: for a polymer `X` in the box of radius `ρ₀` of the step torus `N₁` and its
image `X' = boxMap '' X` on the torus `N₁'`, the domains `Ω_n` of the local generating sets
`𝔹_j(X)` and `𝔹_j(X')` correspond under `boxMap` on the box of radius `ρ₀ + 12 L^(j+m₁)`.  The
cube index `fineCubeIdx` of a site is the floor quotient of its centred coordinate by the cube
side (`fineCubeIdx_torusCast`), so the distances of cube indices that enter the recursion of
`𝔹_j(X)` are the integer distances of these quotients, the same on both tori.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
  Balaban.LargeField Balaban.SmallField.Def6

variable {d L N₁ m₁ q : ℕ} [NeZero N₁] [NeZero L]

/-- **The cube index of a site is the floor quotient of its centred coordinate.** -/
theorem fineCubeIdx_torusCast {n : ℕ} (hn : n ≤ q) (x : Torus d (N₁ * L ^ m₁ * L ^ q)) (μ : Fin d) :
    fineCubeIdx (L ^ m₁) N₁ L q n
        (GsSpec.torusCast x : Torus d (L ^ m₁ * N₁ * L ^ q)) μ =
      (((x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) : ℤ) : ZMod (N₁ * L ^ (q - n))) := by
  have hF : L ^ m₁ * N₁ * L ^ q = N₁ * L ^ m₁ * L ^ q := by ring
  have h1 : ((GsSpec.torusCast x : Torus d (L ^ m₁ * N₁ * L ^ q)) μ) =
      (((x μ).valMinAbs : ℤ) : ZMod (L ^ m₁ * N₁ * L ^ q)) := by
    show (((x μ).val : ℕ) : ZMod (L ^ m₁ * N₁ * L ^ q)) = _
    rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff, hF, ← ZMod.intCast_eq_intCast_iff,
      Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.coe_valMinAbs]
  unfold fineCubeIdx blockMap
  rw [h1]
  exact blockCoord_intCast (n := L ^ m₁ * N₁ * L ^ q) (a := L ^ n * L ^ m₁) (c := N₁ * L ^ (q - n))
    (fine_eq_cube hn)
    (Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))) _

/-- The floor quotient of a centred coordinate lies in the window `|2 q| ≤ c + 2`. -/
theorem abs_quot_window {s c : ℕ} (hs : 0 < s) {ξ : ℤ} (hξ1 : -((s * c : ℕ) : ℤ) < ξ * 2)
    (hξ2 : ξ * 2 ≤ ((s * c : ℕ) : ℤ)) : |2 * (ξ / (s : ℤ))| ≤ (c : ℤ) + 2 := by
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have h1 := Int.mul_ediv_self_le (x := ξ) (k := (s : ℤ)) hsz.ne'
  have h2 := Int.lt_mul_ediv_self_add (x := ξ) hsz
  push_cast at hξ1 hξ2
  rw [abs_le]
  constructor
  · by_contra hlt
    push Not at hlt
    have : (s : ℤ) * (2 * (ξ / (s : ℤ)) + 2 + c) ≤ 0 := by nlinarith
    nlinarith
  · by_contra hlt
    push Not at hlt
    have : (0 : ℤ) < (s : ℤ) * (2 * (ξ / (s : ℤ)) - c) := by
      exact mul_pos hsz (by linarith)
    nlinarith

/-- Two integers congruent modulo `c`, one in the window and the other small, are equal. -/
theorem eq_of_cast_eq_window {c : ℕ} [NeZero c] {u v : ℤ} {B : ℤ} (hu : |2 * u| ≤ (c : ℤ) + 2)
    (hv : |v| ≤ B) (hB : 2 * B + 2 < c) (h : ((u : ℤ) : ZMod c) = ((v : ℤ) : ZMod c)) : u = v := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have h2 : v - u = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    rw [abs_lt]
    rw [abs_le] at hu hv
    constructor <;> omega
  omega

/-- The side of the `𝒞_n`-cubes, the number of cubes, and the number of sites of the step torus. -/
theorem cube_card_eq {n : ℕ} (hn : n ≤ q) :
    N₁ * L ^ m₁ * L ^ q = (L ^ n * L ^ m₁) * (N₁ * L ^ (q - n)) := by
  have := fine_eq_cube (M1 := L ^ m₁) (N₁ := N₁) (L := L) (q := q) hn
  rw [← this]; ring

theorem valMinAbs_window {n : ℕ} (hn : n ≤ q) (x : Torus d (N₁ * L ^ m₁ * L ^ q)) (μ : Fin d) :
    |2 * ((x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ))| ≤ ((N₁ * L ^ (q - n) : ℕ) : ℤ) + 2 := by
  have hs : 0 < L ^ n * L ^ m₁ :=
    Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
  have hmem := ZMod.valMinAbs_mem_Ioc (x μ)
  have eA : ((N₁ * L ^ m₁ * L ^ q : ℕ) : ℤ) = (((L ^ n * L ^ m₁) * (N₁ * L ^ (q - n)) : ℕ) : ℤ) := by
    exact_mod_cast cube_card_eq (N₁ := N₁) (m₁ := m₁) hn
  rw [eA] at hmem
  exact abs_quot_window hs (by simpa using hmem.1) hmem.2

/-- **Two sites are in the same cube iff their floor quotients agree** (the quotient of the first
being small). -/
theorem fineCubeIdx_eq_iff {n : ℕ} (hn : n ≤ q) (x y : Torus d (N₁ * L ^ m₁ * L ^ q)) {r1 : ℤ}
    (hx : ∀ μ, |(x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ)| ≤ r1)
    (hc : 2 * r1 + 2 < ((N₁ * L ^ (q - n) : ℕ) : ℤ)) :
    fineCubeIdx (L ^ m₁) N₁ L q n (GsSpec.torusCast y : Torus d (L ^ m₁ * N₁ * L ^ q)) =
        fineCubeIdx (L ^ m₁) N₁ L q n (GsSpec.torusCast x : Torus d (L ^ m₁ * N₁ * L ^ q)) ↔
      ∀ μ, (y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) =
        (x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) := by
  constructor
  · intro h μ
    have := congrFun h μ
    rw [fineCubeIdx_torusCast hn, fineCubeIdx_torusCast hn] at this
    exact eq_of_cast_eq_window (valMinAbs_window (m₁ := m₁) hn y μ) (hx μ) hc this
  · intro h
    funext μ
    rw [fineCubeIdx_torusCast hn, fineCubeIdx_torusCast hn, h μ]

/-- **The distance of cube indices is the integer distance of the floor quotients** (the quotient of
the second site being small). -/
theorem supDist_fineCubeIdx_le_iff {n : ℕ} (hn : n ≤ q) (x y : Torus d (N₁ * L ^ m₁ * L ^ q))
    {r1 : ℤ} {m : ℕ}
    (hy : ∀ μ, |(y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ)| ≤ r1)
    (hc : 2 * (r1 + m) + 2 < ((N₁ * L ^ (q - n) : ℕ) : ℤ)) :
    supDist (fineCubeIdx (L ^ m₁) N₁ L q n (GsSpec.torusCast x : Torus d (L ^ m₁ * N₁ * L ^ q)))
        (fineCubeIdx (L ^ m₁) N₁ L q n (GsSpec.torusCast y : Torus d (L ^ m₁ * N₁ * L ^ q))) ≤ m ↔
      ∀ μ, |(x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) -
        (y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ)| ≤ m := by
  have : NeZero (N₁ * L ^ (q - n)) := ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ (NeZero.ne L))⟩
  rw [supDist_le_iff]
  refine forall_congr' fun μ => ?_
  rw [fineCubeIdx_torusCast hn, fineCubeIdx_torusCast hn, ← Int.cast_sub, cycNorm_le_iff]
  constructor
  · rintro ⟨t, ht, hte⟩
    have h1 : (((x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) : ℤ) : ZMod (N₁ * L ^ (q - n))) =
        ((t + (y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) : ℤ) : ZMod (N₁ * L ^ (q - n))) := by
      rw [Int.cast_add, hte, Int.cast_sub]; ring
    have h2 := eq_of_cast_eq_window (valMinAbs_window (m₁ := m₁) hn x μ)
      (v := t + (y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ)) (B := r1 + m)
      (by have := hy μ; rw [abs_le] at ht this ⊢; constructor <;> linarith)
      hc h1
    have : (x μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) -
        (y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ) = t := by omega
    rw [this]; exact_mod_cast ht
  · intro h
    exact ⟨_, by exact_mod_cast h, rfl⟩

/-- The floor quotient of a small integer is small. -/
theorem abs_ediv_le {ξ ρ s : ℤ} (hs : 0 < s) (h : |ξ| ≤ ρ) : |ξ / s| ≤ ρ / s + 1 := by
  rw [abs_le] at h ⊢
  have h1 : ρ / s * s ≤ ρ := Int.ediv_mul_le ρ hs.ne'
  have h2 : ρ < (ρ / s + 1) * s := Int.lt_ediv_add_one_mul_self ρ hs
  constructor
  · have : -(ρ / s + 1) ≤ ξ / s := by
      rw [Int.le_ediv_iff_mul_le hs]
      nlinarith
    linarith
  · have : ξ / s < ρ / s + 1 + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hs]
      nlinarith
    omega

/-- Two sites with the same floor quotient, or quotients at distance `≤ m`, are within `(m + 1) s`. -/
theorem abs_sub_le_of_quot {ξ ξ' s : ℤ} {m : ℕ} (hs : 0 < s) (h : |ξ / s - ξ' / s| ≤ m) :
    |ξ - ξ'| ≤ (m + 1) * s := by
  have a1 := Int.ediv_mul_le ξ hs.ne'
  have a2 := Int.lt_ediv_add_one_mul_self ξ hs
  have b1 := Int.ediv_mul_le ξ' hs.ne'
  have b2 := Int.lt_ediv_add_one_mul_self ξ' hs
  rw [abs_le] at h ⊢
  obtain ⟨h1, h2⟩ := h
  constructor <;> nlinarith

/-- The margin in the number of cubes from the margin in the number of sites. -/
theorem cube_margin {a s c ρ m : ℕ} (hsc : a = s * c) (hs : 0 < s)
    (h : 2 * (ρ + (m + 2) * s) < a) : 2 * ((ρ : ℤ) / (s : ℤ) + 1 + m) + 2 < (c : ℤ) := by
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have h1 : (ρ : ℤ) / s * s ≤ ρ := Int.ediv_mul_le ρ hsz.ne'
  have h2 : (2 * (ρ + (m + 2) * s) : ℤ) < (s : ℤ) * c := by
    have := (by exact_mod_cast h : (2 * (ρ + (m + 2) * s) : ℤ) < (a : ℤ))
    rw [hsc] at this; push_cast at this; linarith
  by_contra hlt
  push Not at hlt
  nlinarith

end Balaban.Polymer.TwoTorusStep

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
  Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.GsSpec

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₁' * L ^ m₁) * L ^ k)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ k) ((N₁ * L ^ m₁) * L ^ k)

/-- The cube-side bound used in the recursion: `(5 L + 1) s_n ≤ 6 L^(j+m₁)` for `n < j`. -/
theorem side_bound {n j : ℕ} (hn : n < j) (m₁ : ℕ) :
    (5 * L + 1) * (L ^ n * L ^ m₁) ≤ 6 * L ^ (j + m₁) := by
  have hpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have h1 : L ^ (n + 1) ≤ L ^ j := Nat.pow_le_pow_right hpos hn
  have e : L ^ (j + m₁) = L ^ j * L ^ m₁ := pow_add _ _ _
  have e2 : L ^ (n + 1) = L ^ n * L := pow_succ _ _
  rw [e]
  have h3 : L ^ n * L * L ^ m₁ ≤ L ^ j * L ^ m₁ := Nat.mul_le_mul_right _ (e2 ▸ h1)
  have h4 : 1 ≤ L ^ n * L ^ m₁ := Nat.one_le_iff_ne_zero.2
    (mul_ne_zero (pow_ne_zero _ hpos.ne') (pow_ne_zero _ hpos.ne'))
  nlinarith

/-- A site within integer quotient distance `m` of a site of the box lies in the enlarged box. -/
theorem inBox_of_near {N₀ : ℕ} {x y : Torus d N₀} {R b : ℕ} (hy : InBox d R N₀ y)
    (h : ∀ μ, |(x μ).valMinAbs - (y μ).valMinAbs| ≤ b) : InBox d (R + b) N₀ x := by
  intro μ
  have h1 := h μ
  have h2 := hy μ
  have h3 := abs_sub_abs_le_abs_sub (x μ).valMinAbs (y μ).valMinAbs
  rw [Nat.cast_add]
  linarith

/-- **One step of the support of the local generating set.** -/
theorem localB_support_step {j n : ℕ} (hj : j ≤ k) (hn : n < j) {X : Set (CTorus d L N₁ m₁ k)}
    {hsep : ϱ ≤ minSep L (L ^ m₁)} {R : ℕ}
    (sprev : ∀ x ∈ (localB j hj X hsep).Ω (n + 1), InBox d R ((N₁ * L ^ m₁) * L ^ k) x)
    (hm : 2 * (R + (5 * L + 2) * (L ^ n * L ^ m₁)) < N₁ * L ^ m₁ * L ^ k) :
    ∀ x ∈ (localB j hj X hsep).Ω n, InBox d (R + 6 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x := by
  intro x hx
  rw [mem_localB_Ω_succ hn] at hx
  obtain ⟨y, hy, hd⟩ := hx
  have hs0 : 0 < L ^ n * L ^ m₁ :=
    Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
  have hsz : (0 : ℤ) < ((L ^ n * L ^ m₁ : ℕ) : ℤ) := by exact_mod_cast hs0
  have hyb := sprev y hy
  have hQy : ∀ μ, |(y μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ)| ≤
      (R : ℤ) / ((L ^ n * L ^ m₁ : ℕ) : ℤ) + 1 := fun μ => abs_ediv_le hsz (hyb μ)
  have hc : 2 * ((R : ℤ) / ((L ^ n * L ^ m₁ : ℕ) : ℤ) + 1 + (5 * L : ℕ)) + 2 <
      ((N₁ * L ^ (k - n) : ℕ) : ℤ) :=
    cube_margin (a := N₁ * L ^ m₁ * L ^ k) (s := L ^ n * L ^ m₁) (c := N₁ * L ^ (k - n))
      (ρ := R) (m := 5 * L) (cube_card_eq (by omega)) hs0 hm
  have hQ := (supDist_fineCubeIdx_le_iff (by omega) x y hQy hc).1 hd
  have hnear : ∀ μ, |(x μ).valMinAbs - (y μ).valMinAbs| ≤ (((5 * L + 1) * (L ^ n * L ^ m₁) : ℕ) : ℤ) := by
    intro μ
    have := abs_sub_le_of_quot (ξ := (x μ).valMinAbs) (ξ' := (y μ).valMinAbs) (m := 5 * L) hsz
      (by exact_mod_cast hQ μ)
    push_cast at this ⊢
    exact this
  exact inBox_mono (Nat.add_le_add_left (side_bound (L := L) hn m₁) R) (inBox_of_near hyb hnear)

/-- **The domains of the local generating sets of corresponding polymers correspond.** -/
theorem localB_omega_boxMap {j : ℕ} (hj : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    {X' : Set (CTorus d L N₁' m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)} {hsep' : ϱ' ≤ minSep L (L ^ m₁)}
    {ρ0 : ℕ} (hX : ∀ x ∈ X, InBox d ρ0 ((N₁ * L ^ m₁) * L ^ k) x) (hXX : X' = bm '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁ * L ^ m₁ * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁' * L ^ m₁ * L ^ k) :
    ∀ t, t ≤ j → (∀ x ∈ (localB j hj X hsep).Ω (j - t),
        InBox d (ρ0 + 6 * t * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x) ∧
      (∀ x ∈ (localB j hj X' hsep').Ω (j - t),
        InBox d (ρ0 + 6 * t * L ^ (j + m₁)) ((N₁' * L ^ m₁) * L ^ k) x) ∧
      ∀ x : CTorus d L N₁ m₁ k, InBox d (ρ0 + 6 * t * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x →
        (bm x ∈ (localB j hj X' hsep').Ω (j - t) ↔ x ∈ (localB j hj X hsep).Ω (j - t)) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp only [Nat.sub_zero, mul_zero, zero_mul, add_zero]
    have hs0 : 0 < L ^ j * L ^ m₁ :=
      Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
    have hsz : (0 : ℤ) < ((L ^ j * L ^ m₁ : ℕ) : ℤ) := by exact_mod_cast hs0
    have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hmA' := hmA j le_rfl
    have hmB' := hmB j le_rfl
    have hmul : 2 * (L ^ j * L ^ m₁) ≤ (5 * L + 2) * (L ^ j * L ^ m₁) :=
      by nlinarith [Nat.zero_le (L ^ j * L ^ m₁)]
    have hcA : 2 * ((ρ0 : ℤ) / ((L ^ j * L ^ m₁ : ℕ) : ℤ) + 1) + 2 <
        ((N₁ * L ^ (k - j) : ℕ) : ℤ) := by
      have := cube_margin (a := N₁ * L ^ m₁ * L ^ k) (s := L ^ j * L ^ m₁) (c := N₁ * L ^ (k - j))
        (ρ := ρ0) (m := 0) (cube_card_eq hj) hs0 (by omega)
      simpa using this
    have hcB : 2 * ((ρ0 : ℤ) / ((L ^ j * L ^ m₁ : ℕ) : ℤ) + 1) + 2 <
        ((N₁' * L ^ (k - j) : ℕ) : ℤ) := by
      have := cube_margin (a := N₁' * L ^ m₁ * L ^ k) (s := L ^ j * L ^ m₁) (c := N₁' * L ^ (k - j))
        (ρ := ρ0) (m := 0) (cube_card_eq hj) hs0 (by omega)
      simpa using this
    have hsQ : (L ^ j * L ^ m₁ : ℕ) = (L ^ j * L ^ m₁ : ℕ) := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rw [mem_localB_Ω_top] at hx
      exact hX x (hx x rfl)
    · intro x hx
      rw [mem_localB_Ω_top] at hx
      have hx' := hx x rfl
      rw [hXX] at hx'
      obtain ⟨y, hy, rfl⟩ := hx'
      exact inBox_boxMap (by omega) (hX y hy)
    · intro x hx
      have hxQ : ∀ μ, |(x μ).valMinAbs / ((L ^ j * L ^ m₁ : ℕ) : ℤ)| ≤
          (ρ0 : ℤ) / ((L ^ j * L ^ m₁ : ℕ) : ℤ) + 1 := fun μ => abs_ediv_le hsz (hx μ)
      have hbx : InBox d ρ0 ((N₁' * L ^ m₁) * L ^ k) (bm x) := inBox_boxMap (by omega) hx
      have hxQ' : ∀ μ, |((bm x) μ).valMinAbs / ((L ^ j * L ^ m₁ : ℕ) : ℤ)| ≤
          (ρ0 : ℤ) / ((L ^ j * L ^ m₁ : ℕ) : ℤ) + 1 := fun μ => abs_ediv_le hsz (hbx μ)
      have hQx : ∀ μ, ((bm x) μ).valMinAbs = (x μ).valMinAbs := fun μ =>
        valMinAbs_boxMap (by omega) hx μ
      rw [mem_localB_Ω_top, mem_localB_Ω_top]
      constructor
      · intro hB y hy
        have hQy := (fineCubeIdx_eq_iff hj x y hxQ hcA).1 hy
        have hdy : ∀ μ, |(y μ).valMinAbs - (x μ).valMinAbs| ≤ ((L ^ j * L ^ m₁ : ℕ) : ℤ) := by
          intro μ
          have := abs_sub_le_of_quot (ξ := (y μ).valMinAbs) (ξ' := (x μ).valMinAbs) (m := 0) hsz
            (by rw [hQy μ]; simp)
          simpa using this
        have hyb : InBox d (ρ0 + L ^ j * L ^ m₁) ((N₁ * L ^ m₁) * L ^ k) y := by
          intro μ
          have h1 := hdy μ
          have h2 := hx μ
          have h3 := abs_sub_abs_le_abs_sub (y μ).valMinAbs (x μ).valMinAbs
          rw [Nat.cast_add]
          linarith
        have hbyb : InBox d (ρ0 + L ^ j * L ^ m₁) ((N₁' * L ^ m₁) * L ^ k) (bm y) :=
          inBox_boxMap (by omega) hyb
        have hcy : fineCubeIdx (L ^ m₁) N₁' L k j
            (GsSpec.torusCast (bm y) : Torus d (L ^ m₁ * N₁' * L ^ k)) =
            fineCubeIdx (L ^ m₁) N₁' L k j
              (GsSpec.torusCast (bm x) : Torus d (L ^ m₁ * N₁' * L ^ k)) := by
          refine (fineCubeIdx_eq_iff hj (bm x) (bm y) hxQ' hcB).2 fun μ => ?_
          rw [valMinAbs_boxMap (by omega) hyb μ, hQx μ]
          exact hQy μ
        have hyX' := hB (bm y) hcy
        rw [hXX] at hyX'
        obtain ⟨y0, hy0, hyy⟩ := hyX'
        have : y0 = y := boxMap_inj (hm' := (by omega : 2 * (ρ0 + L ^ j * L ^ m₁) + 1 <
          (N₁' * L ^ m₁) * L ^ k)) (inBox_mono (Nat.le_add_right _ _) (hX y0 hy0)) hyb hyy
        exact this ▸ hy0
      · intro hA y' hy'
        have hQy := (fineCubeIdx_eq_iff hj (bm x) y' hxQ' hcB).1 hy'
        have hdy : ∀ μ, |(y' μ).valMinAbs - ((bm x) μ).valMinAbs| ≤ ((L ^ j * L ^ m₁ : ℕ) : ℤ) := by
          intro μ
          have := abs_sub_le_of_quot (ξ := (y' μ).valMinAbs) (ξ' := ((bm x) μ).valMinAbs) (m := 0)
            hsz (by rw [hQy μ]; simp)
          simpa using this
        have hyb : InBox d (ρ0 + L ^ j * L ^ m₁) ((N₁' * L ^ m₁) * L ^ k) y' := by
          intro μ
          have h1 := hdy μ
          have h2 := hbx μ
          have h3 := abs_sub_abs_le_abs_sub (y' μ).valMinAbs ((bm x) μ).valMinAbs
          rw [Nat.cast_add]
          linarith
        have hya : InBox d (ρ0 + L ^ j * L ^ m₁) ((N₁ * L ^ m₁) * L ^ k) (bm' y') :=
          inBox_boxMap (by omega) hyb
        have hyy : bm (bm' y') = y' := boxMap_boxMap (by omega) hyb
        have hcy : fineCubeIdx (L ^ m₁) N₁ L k j
            (GsSpec.torusCast (bm' y') : Torus d (L ^ m₁ * N₁ * L ^ k)) =
            fineCubeIdx (L ^ m₁) N₁ L k j
              (GsSpec.torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) := by
          refine (fineCubeIdx_eq_iff hj x (bm' y') hxQ hcA).2 fun μ => ?_
          rw [valMinAbs_boxMap (by omega) hyb μ, ← hQx μ]
          exact hQy μ
        have := hA (bm' y') hcy
        rw [hXX]
        exact ⟨bm' y', this, hyy⟩
  | succ t ih =>
    intro ht1
    obtain ⟨sA, sB, eqv⟩ := ih (by omega)
    obtain ⟨n, hnn⟩ : ∃ n, j - (t + 1) = n := ⟨_, rfl⟩
    have hnt : j - t = n + 1 := by omega
    have hn : n < j := by omega
    have hnk : n ≤ k := by omega
    rw [hnt] at sA sB eqv
    rw [hnn]
    set P := L ^ (j + m₁) with hP
    have hR : ρ0 + 6 * (t + 1) * P = (ρ0 + 6 * t * P) + 6 * P := by ring
    rw [hR]
    set R := ρ0 + 6 * t * P with hRdef
    have hs0 : 0 < L ^ n * L ^ m₁ :=
      Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L)))
    have hsz : (0 : ℤ) < ((L ^ n * L ^ m₁ : ℕ) : ℤ) := by exact_mod_cast hs0
    have hsb := side_bound (L := L) hn m₁
    have hmA' := hmA n hn.le
    have hmB' := hmB n hn.le
    have hRle : R + 6 * P ≤ ρ0 + 6 * j * P := by
      have : 6 * (t + 1) * P ≤ 6 * j * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht1)
      nlinarith
    have hcA : 2 * ((R : ℤ) / ((L ^ n * L ^ m₁ : ℕ) : ℤ) + 1 + (5 * L : ℕ)) + 2 <
        ((N₁ * L ^ (k - n) : ℕ) : ℤ) := by
      refine cube_margin (a := N₁ * L ^ m₁ * L ^ k) (s := L ^ n * L ^ m₁) (c := N₁ * L ^ (k - n))
        (ρ := R) (m := 5 * L) (cube_card_eq hnk) hs0 ?_
      nlinarith
    have hcB : 2 * ((R : ℤ) / ((L ^ n * L ^ m₁ : ℕ) : ℤ) + 1 + (5 * L : ℕ)) + 2 <
        ((N₁' * L ^ (k - n) : ℕ) : ℤ) := by
      refine cube_margin (a := N₁' * L ^ m₁ * L ^ k) (s := L ^ n * L ^ m₁) (c := N₁' * L ^ (k - n))
        (ρ := R) (m := 5 * L) (cube_card_eq hnk) hs0 ?_
      nlinarith
    have hRρ : R ≤ ρ0 + 6 * j * P := le_trans (Nat.le_add_right _ _) hRle
    have hmA2 : 2 * (R + (5 * L + 2) * (L ^ n * L ^ m₁)) < N₁ * L ^ m₁ * L ^ k := by omega
    have hmB2 : 2 * (R + (5 * L + 2) * (L ^ n * L ^ m₁)) < N₁' * L ^ m₁ * L ^ k := by omega
    refine ⟨localB_support_step hj hn sA hmA2, localB_support_step hj hn sB hmB2, ?_⟩
    intro x hx
    have hmargA : 2 * (R + 6 * P) + 1 < N₁ * L ^ m₁ * L ^ k := by
      have : 6 * (t + 1) * P ≤ 6 * j * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht1)
      have h2 : L ^ n * L ^ m₁ ≤ (5 * L + 2) * (L ^ n * L ^ m₁) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hmargB : 2 * (R + 6 * P) + 1 < N₁' * L ^ m₁ * L ^ k := by
      have : 6 * (t + 1) * P ≤ 6 * j * P := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht1)
      have h2 : L ^ n * L ^ m₁ ≤ (5 * L + 2) * (L ^ n * L ^ m₁) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hQx : ∀ μ, ((bm x) μ).valMinAbs = (x μ).valMinAbs := fun μ =>
      valMinAbs_boxMap (by omega) hx μ
    have hQbound : ∀ {N₀ : ℕ} (z : Torus d N₀), InBox d R N₀ z → ∀ μ,
        |(z μ).valMinAbs / ((L ^ n * L ^ m₁ : ℕ) : ℤ)| ≤ (R : ℤ) / ((L ^ n * L ^ m₁ : ℕ) : ℤ) + 1 :=
      fun z hz μ => abs_ediv_le hsz (hz μ)
    rw [mem_localB_Ω_succ hn, mem_localB_Ω_succ hn]
    constructor
    · rintro ⟨y', hy', hd'⟩
      have hyb' := sB y' hy'
      have hya : InBox d R ((N₁ * L ^ m₁) * L ^ k) (bm' y') :=
        inBox_boxMap (by omega) hyb'
      have hyy : bm (bm' y') = y' := boxMap_boxMap (by omega) hyb'
      have hyΩ : bm' y' ∈ (localB j hj X hsep).Ω (n + 1) :=
        (eqv (bm' y') hya).1 (by rw [hyy]; exact hy')
      have hQ' := (supDist_fineCubeIdx_le_iff hnk (bm x) y' (hQbound y' hyb') hcB).1 hd'
      refine ⟨bm' y', hyΩ, (supDist_fineCubeIdx_le_iff hnk x (bm' y') (hQbound _ hya) hcA).2 ?_⟩
      intro μ
      have := hQ' μ
      rw [hQx μ] at this
      have e2 : ((bm' y') μ).valMinAbs = (y' μ).valMinAbs := valMinAbs_boxMap (by omega) hyb' μ
      rw [e2]
      exact this
    · rintro ⟨y, hy, hd⟩
      have hyb := sA y hy
      have hbyb : InBox d R ((N₁' * L ^ m₁) * L ^ k) (bm y) := inBox_boxMap (by omega) hyb
      have hyΩ : bm y ∈ (localB j hj X' hsep').Ω (n + 1) := (eqv y hyb).2 hy
      have hQ := (supDist_fineCubeIdx_le_iff hnk x y (hQbound y hyb) hcA).1 hd
      refine ⟨bm y, hyΩ, (supDist_fineCubeIdx_le_iff hnk (bm x) (bm y) (hQbound _ hbyb) hcB).2 ?_⟩
      intro μ
      have := hQ μ
      rw [hQx μ, valMinAbs_boxMap (by omega) hyb μ]
      exact this


/-- **The domains of the local generating sets of corresponding polymers correspond on the whole
box.** -/
theorem localB_omega_boxMap_all {j : ℕ} (hj : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    {X' : Set (CTorus d L N₁' m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)} {hsep' : ϱ' ≤ minSep L (L ^ m₁)}
    {ρ0 : ℕ} (hX : ∀ x ∈ X, InBox d ρ0 ((N₁ * L ^ m₁) * L ^ k) x) (hXX : X' = bm '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁ * L ^ m₁ * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁' * L ^ m₁ * L ^ k) :
    (∀ n, ∀ x ∈ (localB j hj X hsep).Ω n,
      InBox d (ρ0 + 6 * j * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x) ∧
    (∀ n, ∀ x ∈ (localB j hj X' hsep').Ω n,
      InBox d (ρ0 + 6 * j * L ^ (j + m₁)) ((N₁' * L ^ m₁) * L ^ k) x) ∧
    ∀ x : CTorus d L N₁ m₁ k, InBox d (ρ0 + 6 * j * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x →
      ∀ n, (bm x ∈ (localB j hj X' hsep').Ω n ↔ x ∈ (localB j hj X hsep).Ω n) := by
  have key := localB_omega_boxMap (hsep := hsep) (hsep' := hsep') hj hX hXX hmA hmB
  have hsupp : ∀ n, n ≤ j →
      (∀ x ∈ (localB j hj X hsep).Ω n, InBox d (ρ0 + 6 * (j - n) * L ^ (j + m₁))
        ((N₁ * L ^ m₁) * L ^ k) x) ∧
      (∀ x ∈ (localB j hj X' hsep').Ω n, InBox d (ρ0 + 6 * (j - n) * L ^ (j + m₁))
        ((N₁' * L ^ m₁) * L ^ k) x) ∧
      ∀ x : CTorus d L N₁ m₁ k, InBox d (ρ0 + 6 * (j - n) * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x →
        (bm x ∈ (localB j hj X' hsep').Ω n ↔ x ∈ (localB j hj X hsep).Ω n) := by
    intro n hn
    have := key (j - n) (by omega)
    have e : j - (j - n) = n := by omega
    rwa [e] at this
  have hbig : ∀ n, n ≤ j → 6 * (j - n) * L ^ (j + m₁) ≤ 6 * j * L ^ (j + m₁) := fun n _ =>
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  refine ⟨fun n x hx => ?_, fun n x hx => ?_, fun x hx n => ?_⟩
  · by_cases hn : n ≤ j
    · exact inBox_mono (Nat.add_le_add_left (hbig n hn) _) ((hsupp n hn).1 x hx)
    · rw [localB_Ω_of_gt (by omega)] at hx
      exact absurd hx (Finset.notMem_empty _)
  · by_cases hn : n ≤ j
    · exact inBox_mono (Nat.add_le_add_left (hbig n hn) _) ((hsupp n hn).2.1 x hx)
    · rw [localB_Ω_of_gt (by omega)] at hx
      exact absurd hx (Finset.notMem_empty _)
  · by_cases hn : n ≤ j
    · obtain ⟨sA, sB, eqv⟩ := hsupp n hn
      by_cases hxn : InBox d (ρ0 + 6 * (j - n) * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ k) x
      · exact eqv x hxn
      · have hmarg : 2 * (ρ0 + 6 * j * L ^ (j + m₁)) + 1 < N₁' * L ^ m₁ * L ^ k := by
          have := hmB n hn
          have h2 : 0 < (5 * L + 2) * (L ^ n * L ^ m₁) :=
            Nat.mul_pos (by omega) (Nat.pos_of_ne_zero
              (mul_ne_zero (pow_ne_zero _ (NeZero.ne L)) (pow_ne_zero _ (NeZero.ne L))))
          omega
        constructor
        · intro hB
          have hb := sB _ hB
          have hxx : ∀ μ, ((bm x) μ).valMinAbs = (x μ).valMinAbs := fun μ =>
            valMinAbs_boxMap (by omega) hx μ
          exact absurd (fun μ => by rw [← hxx μ]; exact hb μ) hxn
        · intro hA
          exact absurd (sA _ hA) hxn
    · rw [localB_Ω_of_gt (by omega), localB_Ω_of_gt (by omega)]
      simp


/-- **`GSIso` for the local generating sets of corresponding polymers.**  This discharges the
geometric premise `GSIso` of `evDec_oldTerm_twoTorus` for the generating sets `Gk = 𝔹_j(X)`. -/
theorem gsIso_localB {j : ℕ} (hj : j ≤ k) (hK : 1 ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    {X' : Set (CTorus d L N₁' m₁ k)} {hsep : ϱ ≤ minSep L (L ^ m₁)} {hsep' : ϱ' ≤ minSep L (L ^ m₁)}
    {ρ0 : ℕ} (hX : ∀ x ∈ X, InBox d ρ0 ((N₁ * L ^ m₁) * L ^ k) x) (hXX : X' = bm '' X)
    (hmA : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁ * L ^ m₁ * L ^ k)
    (hmB : ∀ n ≤ j, 2 * (ρ0 + 1 + 6 * j * L ^ (j + m₁) + (5 * L + 2) * (L ^ n * L ^ m₁)) <
      N₁' * L ^ m₁ * L ^ k)
    (hn : 2 * (ρ0 + 6 * j * L ^ (j + m₁) + 1) + 3 * L ^ k + 5 < (N₁ * L ^ m₁) * L ^ k)
    (hn' : 2 * (ρ0 + 6 * j * L ^ (j + m₁) + 1) + 3 * L ^ k + 5 < (N₁' * L ^ m₁) * L ^ k)
    (a : ℕ → ℝ) (ν : ℝ) :
    GSIso a ν (localB j hj X hsep) (localB j hj X' hsep') bm
      {z | InBox d (ρ0 + 6 * j * L ^ (j + m₁) + 1) ((N₁ * L ^ m₁) * L ^ k) z} := by
  obtain ⟨h1, h2, -⟩ := localB_omega_boxMap_all hj hX hXX
    (fun n hn => by have := hmA n hn; omega) (fun n hn => by have := hmB n hn; omega)
    (hsep := hsep) (hsep' := hsep')
  obtain ⟨-, -, h3⟩ := localB_omega_boxMap_all hj (ρ0 := ρ0 + 1)
    (fun x hx => inBox_mono (Nat.le_succ ρ0) (hX x hx)) hXX hmA hmB (hsep := hsep) (hsep' := hsep')
  exact gsIso_of_omega a ν hK hn hn' (fun x hx => h1 1 x hx) (fun x hx => h2 1 x hx)
    (fun x hx n _ _ => by
      refine h3 x ?_ n
      have : ρ0 + 1 + 6 * j * L ^ (j + m₁) = ρ0 + 6 * j * L ^ (j + m₁) + 1 := by ring
      rwa [this])

end Balaban.Polymer.TwoTorusStep
