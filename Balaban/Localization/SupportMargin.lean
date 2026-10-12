/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
public import Balaban.Localization.I5FluctLocal
public import Balaban.Fluctuation.CriticalPoint
public import Balaban.Fluctuation.HatEngineLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Support margin and whole unit blocks for the label sets (`notes/phase1/TRUE-LOCAL.md` §1–§2)

This file proves **geometry only**.  It says nothing about the physical terms of the fluctuation
expansion: the physical locality statement (`OPEN-PHYSICAL-FOOTPRINT-LOCAL` of the note) is open.

Notation: `a = cellSide L m₀ m₁ K` is the side of a `π_K`-cell, `b = L ^ (K + m₁)` the side of a
top-level parameter patch (`Pset`), `ℓ = L ^ K` the side of a level-`K` unit block; `ℓ ∣ b ∣ a`.

* `interval_margin` (one coordinate): an interval of length at most `a` together with one of its
  points' nearest neighbours lies in an aligned interval of length `L * a` (`L ≥ 2`).
* `box_cover_nbr`: the product version; `psiThick_subset_X1_of_layer`, `psiThick_subset_X1`:
  **old-support margin**, `psiThick X ⊆ X₁` for `X` covered by the chosen `π'_j`-cubes, `j < K`,
  when every aligned `L a`-cube lies in the top layer (for instance `IsLevel G K`).  The proof
  needs `L ≥ 2` only (the note states `L ≥ 3`).
* `IsCellUnion`: a set closed under `SameCell`.  `compY_isCellUnion`, `Ysites_isCellUnion`: the
  label sets are unions of complete cells; hence every level-`K` unit block is contained in or
  disjoint from them (`compY_unitBlock_dichotomy`, `Ysites_unitBlock_dichotomy`).
  This does **not** give `blockThick Y ⊆ Y`: `blockThick Y` contains the blocks of the neighbours
  of `Y` (`not_blockThick_subset`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Fluctuation Finset

/-! ### One coordinate -/

/-- **One-coordinate interval lemma.**  On `ZMod n` with `a ∣ n`, `L ≥ 2`: let `I = {p + r | r < s}`
be an interval of length `s ≤ a`, `p + t` one of its points and `ν` that point or one of its two
neighbours.  Then there is an aligned base `B` (`B.val` divisible by `a`) such that `I` and `ν`
both lie in the interval `{B + w | w < L * a}`. -/
theorem interval_margin {n a L s : ℕ} [NeZero n] (ha : 0 < a) (had : a ∣ n) (hL : 2 ≤ L)
    (hs : s ≤ a) (p : ZMod n) (t : ℕ) (ht : t < s) (ν : ZMod n)
    (hν : ν = p + t ∨ ν = p + t + 1 ∨ ν = p + t - 1) :
    ∃ B : ZMod n, B.val % a = 0 ∧ (∀ r < s, ∃ w < L * a, p + r = B + w) ∧
      ∃ w < L * a, ν = B + w := by
  have hna : a ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) had
  have h2a : 2 * a ≤ L * a := Nat.mul_le_mul_right a hL
  set P := p.val + n with hPdef
  have hp : p = (P : ZMod n) := by simp [hPdef]
  have hP1 : 1 ≤ P := by have := Nat.pos_of_ne_zero (NeZero.ne n); omega
  have key : ∀ k m : ℕ, a * k ≤ P → P ≤ a * k + a → a * k ≤ m → m < a * k + 2 * a →
      ν = (m : ZMod n) →
      ∃ B : ZMod n, B.val % a = 0 ∧ (∀ r < s, ∃ w < L * a, p + r = B + w) ∧
        ∃ w < L * a, ν = B + w := by
    intro k m h1 h2 h3 h4 hm
    refine ⟨((a * k : ℕ) : ZMod n), ?_, ?_, ⟨m - a * k, by omega, ?_⟩⟩
    · rw [ZMod.val_natCast, Nat.mod_mod_of_dvd _ had]; exact Nat.mul_mod_right a k
    · intro r hr
      refine ⟨P + r - a * k, by omega, ?_⟩
      have e : P + r = a * k + (P + r - a * k) := by omega
      rw [hp]; exact_mod_cast congrArg (Nat.cast : ℕ → ZMod n) e
    · have e : m = a * k + (m - a * k) := by omega
      rw [hm]; exact_mod_cast congrArg (Nat.cast : ℕ → ZMod n) e
  rcases hν with h | h | h
  · refine key (P / a) (P + t) ?_ ?_ ?_ ?_ (by rw [h, hp]; push_cast; rfl)
    · exact Nat.mul_div_le P a
    · have := Nat.lt_mul_div_succ P ha; rw [Nat.mul_succ] at this; omega
    · have := Nat.mul_div_le P a; omega
    · have := Nat.lt_mul_div_succ P ha; rw [Nat.mul_succ] at this; omega
  · refine key (P / a) (P + t + 1) ?_ ?_ ?_ ?_ (by rw [h, hp]; push_cast; rfl)
    · exact Nat.mul_div_le P a
    · have := Nat.lt_mul_div_succ P ha; rw [Nat.mul_succ] at this; omega
    · have := Nat.mul_div_le P a; omega
    · have := Nat.lt_mul_div_succ P ha; rw [Nat.mul_succ] at this; omega
  · have hk1 := Nat.mul_div_le (P - 1) a
    have hk2 := Nat.lt_mul_div_succ (P - 1) ha
    rw [Nat.mul_succ] at hk2
    refine key ((P - 1) / a) (P + t - 1) ?_ ?_ ?_ ?_ ?_
    · omega
    · omega
    · omega
    · omega
    · rw [h, hp, Nat.cast_sub (by omega)]; push_cast; rfl

/-- With `L = 1` the interval lemma fails: in `ZMod 4`, `a = 1`, no interval of length `1 * 1`
contains both `0` and its neighbour `1`.  (`interval_margin` needs `2 ≤ L`.) -/
theorem interval_margin_false_of_one :
    ¬ ∃ B : ZMod 4, (∃ w : ℕ, w < 1 * 1 ∧ (0 : ZMod 4) = B + w) ∧
      ∃ w : ℕ, w < 1 * 1 ∧ (1 : ZMod 4) = B + w := by
  rintro ⟨B, ⟨w, hw, h0⟩, ⟨w', hw', h1⟩⟩
  have e : w = 0 := by omega
  have e' : w' = 0 := by omega
  subst e e'
  simp at h0 h1
  rw [← h0] at h1
  exact absurd h1 (by decide)

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

/-- Product version: a box `box q s` with `s ≤ a`, and a site `y` equal or adjacent to a point of
it, lie in one aligned cube `box b (L * a)`, `L ≥ 2`. -/
theorem box_cover_nbr {a s : ℕ} (ha : 0 < a) (had : a ∣ (N₁ * L ^ m₁) * L ^ K) (hL : 2 ≤ L)
    (hs : s ≤ a) {q x y : CTorus d L N₁ m₁ K} (hx : x ∈ box q s) (hy : y = x ∨ Adj x y) :
    ∃ b : CTorus d L N₁ m₁ K, Aligned a b ∧ box q s ⊆ box b (L * a) ∧ y ∈ box b (L * a) := by
  obtain ⟨w0, hw0, rfl⟩ := hx
  have hν : ∀ ν, y ν = q ν + (w0 ν : ZMod _) ∨ y ν = q ν + (w0 ν : ZMod _) + 1 ∨
      y ν = q ν + (w0 ν : ZMod _) - 1 := by
    intro ν
    rcases hy with rfl | ⟨μ, h | h⟩
    · left; simp
    · by_cases hνμ : ν = μ
      · subst hνμ; right; left; simp [h]
      · left; simp [h, hνμ]
    · by_cases hνμ : ν = μ
      · subst hνμ
        have := congrFun h ν
        simp at this
        right; right; rw [this]; ring
      · have := congrFun h ν
        simp [hνμ] at this
        left; rw [← this]
  choose B hB1 hB2 hB3 using fun ν =>
    interval_margin (L := L) ha had hL hs (q ν) (w0 ν) (hw0 ν) (y ν) (hν ν)
  choose wy hwy1 hwy2 using hB3
  refine ⟨B, hB1, ?_, ⟨wy, hwy1, ?_⟩⟩
  · rintro x ⟨r, hr, rfl⟩
    choose wr hwr1 hwr2 using fun ν => hB2 ν (r ν) (hr ν)
    refine ⟨wr, hwr1, ?_⟩
    funext ν
    simp [hwr2 ν]
  · funext ν; simp [hwy2 ν]

omit [NeZero L] in
/-- The side `L * a_j` of a chosen `π'_j`-cube is at most `a_K` when `j < K`. -/
theorem cellSide_succ_le {j : ℕ} (hL : 1 ≤ L) (hj : j + 1 ≤ K) (m₀ m₁ : ℕ) :
    L * cellSide L m₀ m₁ j ≤ cellSide L m₀ m₁ K := by
  unfold cellSide
  calc L * L ^ (j + m₀ + m₁) = L ^ (j + 1 + m₀ + m₁) := by
        rw [show j + 1 + m₀ + m₁ = (j + m₀ + m₁) + 1 by ring, pow_succ]; ring
    _ ≤ L ^ (K + m₀ + m₁) := Nat.pow_le_pow_right hL (by omega)

/-- **Old-support margin (formula (1) of the note), weak form.**  Let `j < K`, `L ≥ 2`, and let
every aligned cube `box b (L * a_K)` lie in the top layer `G.layer K`.  If `X` is covered by the
chosen `π'_j`-cubes `box q (L * a_j)`, `q ∈ 𝒦X`, then `X` and its nearest neighbours lie in
`X₁ = X1 G m₀ j 𝒦X`. -/
theorem psiThick_subset_X1_of_layer {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hN : L ^ m₀ ∣ N₁) (hjK : j + 1 ≤ K) (hL : 2 ≤ L)
    (hlay : ∀ b : CTorus d L N₁ m₁ K, Aligned (cellSide L m₀ m₁ K) b →
      box b (L * cellSide L m₀ m₁ K) ⊆ (G.layer K : Set (CTorus d L N₁ m₁ K)))
    (hX : ∀ z ∈ X, ∃ q ∈ 𝒦X, z ∈ box q (L * cellSide L m₀ m₁ j)) :
    psiThick X ⊆ X1 G m₀ j 𝒦X := by
  intro y hy
  have hy' : ∃ x ∈ X, y = x ∨ Adj x y := by
    rcases hy with hy | ⟨x, hx, hxy⟩
    · exact ⟨y, hy, Or.inl rfl⟩
    · exact ⟨x, hx, Or.inr hxy⟩
  obtain ⟨x, hxX, hxy⟩ := hy'
  obtain ⟨q, hq, hxq⟩ := hX x hxX
  obtain ⟨b, hb, hsub, hyb⟩ := box_cover_nbr (L := L) (cellSide_pos m₀ m₁ K)
    (cellSide_dvd hN le_rfl) hL (cellSide_succ_le (by omega) hjK m₀ m₁) hxq hxy
  exact Set.mem_iUnion₂.2 ⟨b, ⟨hb, hlay b hb, q, hq, hsub⟩, hyb⟩

/-- **Old-support margin (formula (1) of the note).**  In the full-level case (`IsLevel G K`:
every site is in layer `K`), `j < K`, `L ≥ 2` (in particular `L ≥ 3`): `psiThick X ⊆ X₁` for every
`X` covered by the chosen `π'_j`-cubes.  No torus-size hypothesis is needed. -/
theorem psiThick_subset_X1 {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hN : L ^ m₀ ∣ N₁) (hjK : j + 1 ≤ K) (hL : 2 ≤ L) (hlev : IsLevel G K)
    (hX : ∀ z ∈ X, ∃ q ∈ 𝒦X, z ∈ box q (L * cellSide L m₀ m₁ j)) :
    psiThick X ⊆ X1 G m₀ j 𝒦X := by
  refine psiThick_subset_X1_of_layer hN hjK hL (fun b _ z _ => ?_) hX
  have := (G.layerIndex_spec (hlev z).1).2.2
  rw [(hlev z).2] at this
  exact_mod_cast this

/-- The same, from the `CovSetup` itself (`X ⊆ ⋃_{q ∈ 𝒦X} Q_q` is its field `chosen`). -/
theorem CovSetup.psiThick_subset_X1 {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hS : CovSetup G m₀ j X 𝒦X) (hL : 2 ≤ L) (hlev : IsLevel G K) :
    psiThick X ⊆ X1 G m₀ j 𝒦X :=
  Balaban.Localization.psiThick_subset_X1 hS.hN hS.hjK hL hlev hS.chosen.2

/-! ### Cell unions -/

end Geometry

section Cells

variable {d n : ℕ}

/-- `S` is a union of complete cells of side `a`: it is closed under `SameCell a`. -/
def IsCellUnion (a : ℕ) (S : Set (Torus d n)) : Prop :=
  ∀ x ∈ S, ∀ y, SameCell a y x → y ∈ S

theorem IsCellUnion.mono_dvd {a b : ℕ} {S : Set (Torus d n)} (hab : a ∣ b)
    (h : IsCellUnion b S) : IsCellUnion a S :=
  fun x hx y hy => h x hx y (SameCell.mono hab hy)

theorem IsCellUnion.union {a : ℕ} {S T : Set (Torus d n)} (hS : IsCellUnion a S)
    (hT : IsCellUnion a T) : IsCellUnion a (S ∪ T) := by
  rintro x (hx | hx) y hy
  · exact Or.inl (hS x hx y hy)
  · exact Or.inr (hT x hx y hy)

theorem isCellUnion_iUnion₂ {a : ℕ} {ι : Type*} {p : ι → Prop} {S : ι → Set (Torus d n)}
    (h : ∀ i, p i → IsCellUnion a (S i)) : IsCellUnion a (⋃ i, ⋃ _ : p i, S i) := by
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_iUnion₂.2 ⟨i, hi, h i hi x hxi y hy⟩

theorem sameCell_iff_cbase_eq [NeZero n] {a : ℕ} (ha : 0 < a) {x y : Torus d n} :
    SameCell a y x ↔ cbase a y = cbase a x := by
  have hv : ∀ z : Torus d n, ∀ μ, (cbase a z μ).val = a * ((z μ).val / a) := by
    intro z μ
    have hlt : a * ((z μ).val / a) < n :=
      lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
    simp only [cbase]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  constructor
  · intro h; funext μ; simp only [cbase, h μ]
  · intro h μ
    have := congrArg (fun z : Torus d n => (z μ).val) h
    simp only [hv] at this
    exact Nat.eq_of_mul_eq_mul_left ha this

end Cells

section CellsC

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

/-- An aligned cube `box b (L * a)` is a union of complete `a`-cells (`a ∣ N`). -/
theorem box_isCellUnion {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {b : CTorus d L N₁ m₁ K} (hb : Aligned a b) : IsCellUnion a (box b (L * a)) := by
  intro x hx y hy
  have hc : cbase a y = cbase a x := (sameCell_iff_cbase_eq ha0).1 hy
  have := cell_subset_cube ha ha0 hb hx
  exact this (hc ▸ mem_box_cbase ha0 y)

omit [NeZero N₁] [NeZero L] in
/-- `Pset` is a complete cell of side `L ^ (n + m₁)`. -/
theorem Pset_isCellUnion (q : ℕ × CTorus d L N₁ m₁ K) :
    IsCellUnion (L ^ (q.1 + m₁)) (Pset m₁ q) :=
  fun _ hx _ hy => SameCell.trans hy hx

theorem X1_isCellUnion {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ K)} (hN : L ^ m₀ ∣ N₁) :
    IsCellUnion (cellSide L m₀ m₁ K) (X1 G m₀ j 𝒦X) := by
  refine isCellUnion_iUnion₂ fun b hb => ?_
  exact box_isCellUnion (cellSide_dvd hN le_rfl) (cellSide_pos m₀ m₁ K) hb.1

theorem Dsites_isCellUnion (hN : L ^ m₀ ∣ N₁) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q.1 ≤ K) :
    IsCellUnion (cellSide L m₀ m₁ q.1) (Dsites G m₀ q) := by
  refine isCellUnion_iUnion₂ fun b hb => ?_
  exact box_isCellUnion (cellSide_dvd hN hq) (cellSide_pos m₀ m₁ q.1) hb.1

variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ K}

/-- **`Ysites` is a union of complete `a`-cells** (`a = cellSide K`), provided `X₁` is and every
marked patch is at the top level `K`. -/
theorem Ysites_isCellUnion (hN : L ^ m₀ ∣ N₁) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX₁ : IsCellUnion (cellSide L m₀ m₁ K) X₁) {C : Finset ι} (hC : ∀ i ∈ C, (c i).1 = K) :
    IsCellUnion (cellSide L m₀ m₁ K) (Ysites G m₀ c X₁ C) := by
  refine hX₁.union (isCellUnion_iUnion₂ fun i hi => ?_)
  have := Dsites_isCellUnion (G := G) hN (q := c i) (by rw [hC i hi])
  rwa [hC i hi] at this

/-- **`compY` is a union of complete `b`-cells** (`b = L ^ (K + m₁)`), provided `X₁` is and every
marked patch is at the top level `K`: a nearest-neighbour component of a union of complete cells
contains each cell it meets, since a cell is connected. -/
theorem compY_isCellUnion {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX₁ : IsCellUnion (L ^ (K + m₁)) X₁) {C : Finset ι} (hC : ∀ i ∈ C, (c i).1 = K) :
    IsCellUnion (L ^ (K + m₁)) (compY c X₁ C) := by
  have hdvd : L ^ (K + m₁) ∣ (N₁ * L ^ m₁) * L ^ K := by
    rw [show K + m₁ = m₁ + K by ring, pow_add]; exact Dvd.intro_left N₁ (by ring)
  have ha0 : 0 < L ^ (K + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hV : IsCellUnion (L ^ (K + m₁)) (patchUnion X₁ (fun i => Pset m₁ (c i)) C) := by
    refine hX₁.union (isCellUnion_iUnion₂ fun i hi => ?_)
    have := Pset_isCellUnion (c i)
    rwa [hC i hi] at this
  rintro x hx y hy
  obtain ⟨x0, hx0, hreach⟩ := hx
  have hxV : x ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h) ⟨x0, hx0, hreach⟩
  have hcb : cbase (L ^ (K + m₁)) y = cbase (L ^ (K + m₁)) x := (sameCell_iff_cbase_eq ha0).1 hy
  have hsub : box (cbase (L ^ (K + m₁)) x) (L ^ (K + m₁)) ⊆
      patchUnion X₁ (fun i => Pset m₁ (c i)) C := by
    intro z hz
    have : cbase (L ^ (K + m₁)) z = cbase (L ^ (K + m₁)) x :=
      cbase_eq_of_mem_box hdvd (aligned_cbase x) hz
    exact hV x hxV z ((sameCell_iff_cbase_eq ha0).2 this)
  have hpath := chain_in_box _ _ _ hsub (mem_box_cbase ha0 x) (hcb ▸ mem_box_cbase ha0 y)
  exact ⟨x0, hx0, hreach.trans hpath⟩

/-- In the full-level case every centre of `cubeIdx G` is at the top level `K`. -/
theorem level_eq_of_mem_cubeIdx (hlev : IsLevel G K) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : q.1 = K := by
  obtain ⟨⟨h1, h2⟩, hl, -⟩ := (mem_cubeIdx G).1 hq
  have := G.layerIndex_eq h1 h2 hl
  rw [(hlev q.2).2] at this
  exact this.symm

/-! ### Whole unit blocks -/

/-- A union of complete cells of side `L ^ K` contains or misses each level-`K` unit block. -/
theorem IsCellUnion.unitBlock_iff {S : Set (CTorus d L N₁ m₁ K)} (h : IsCellUnion (L ^ K) S)
    {x y : CTorus d L N₁ m₁ K}
    (hxy : jBlock d L (N₁ * L ^ m₁) K K x = jBlock d L (N₁ * L ^ m₁) K K y) :
    x ∈ S ↔ y ∈ S :=
  ⟨fun hx => h x hx y (sameCell_of_jBlock_eq le_rfl hxy).symm,
   fun hy => h y hy x (sameCell_of_jBlock_eq le_rfl hxy)⟩

/-- Dichotomy: the level-`K` unit block of a site `x` is contained in `S` or disjoint from `S`. -/
theorem IsCellUnion.unitBlock_dichotomy {S : Set (CTorus d L N₁ m₁ K)}
    (h : IsCellUnion (L ^ K) S) (x : CTorus d L N₁ m₁ K) :
    {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x} ⊆ S ∨
      Disjoint {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x} S := by
  by_cases hx : x ∈ S
  · exact Or.inl fun y hy => (h.unitBlock_iff hy).2 hx
  · refine Or.inr (Set.disjoint_left.2 fun y hy hyS => hx ((h.unitBlock_iff hy).1 hyS))

/-- `compY` contains or misses each level-`K` unit block (`X₁` a union of complete `L^(K+m₁)`-cells,
all marked patches at level `K`). -/
theorem compY_unitBlock_dichotomy {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX₁ : IsCellUnion (L ^ (K + m₁)) X₁) {C : Finset ι} (hC : ∀ i ∈ C, (c i).1 = K)
    (x : CTorus d L N₁ m₁ K) :
    {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x} ⊆ compY c X₁ C ∨
      Disjoint {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x}
        (compY c X₁ C) :=
  ((compY_isCellUnion hX₁ hC).mono_dvd (pow_dvd_pow L (by omega))).unitBlock_dichotomy x

/-- `Ysites` contains or misses each level-`K` unit block. -/
theorem Ysites_unitBlock_dichotomy (hN : L ^ m₀ ∣ N₁) {X₁ : Set (CTorus d L N₁ m₁ K)}
    (hX₁ : IsCellUnion (cellSide L m₀ m₁ K) X₁) {C : Finset ι} (hC : ∀ i ∈ C, (c i).1 = K)
    (x : CTorus d L N₁ m₁ K) :
    {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x} ⊆
        Ysites G m₀ c X₁ C ∨
      Disjoint {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x}
        (Ysites G m₀ c X₁ C) :=
  ((Ysites_isCellUnion hN hX₁ hC).mono_dvd
    (pow_dvd_pow L (by omega))).unitBlock_dichotomy x

/-- The full-level case of the note: for `X₁ = X1 G m₀ j 𝒦X`, `IsLevel G K` and centres of
`cubeIdx G`, both `compY` and `Ysites` contain or miss each level-`K` unit block. -/
theorem labels_unitBlock_dichotomy {j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ K)} (hN : L ^ m₀ ∣ N₁)
    (hlev : IsLevel G K) (hc : ∀ i, c i ∈ cubeIdx G) (C : Finset ι) (x : CTorus d L N₁ m₁ K) :
    ({y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x} ⊆
        compY c (X1 G m₀ j 𝒦X) C ∨
      Disjoint {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x}
        (compY c (X1 G m₀ j 𝒦X) C)) ∧
    ({y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x} ⊆
        Ysites G m₀ c (X1 G m₀ j 𝒦X) C ∨
      Disjoint {y | jBlock d L (N₁ * L ^ m₁) K K y = jBlock d L (N₁ * L ^ m₁) K K x}
        (Ysites G m₀ c (X1 G m₀ j 𝒦X) C)) := by
  have hC : ∀ i ∈ C, (c i).1 = K := fun i _ => level_eq_of_mem_cubeIdx hlev (hc i)
  have hX := X1_isCellUnion (G := G) (j := j) (𝒦X := 𝒦X) hN
  exact ⟨compY_unitBlock_dichotomy (hX.mono_dvd (pow_dvd_pow L (by omega))) hC x,
    Ysites_unitBlock_dichotomy hN hX hC x⟩

/-! ### No margin for `X₁` itself -/

/-- A nonempty proper subset of the torus has a site with a neighbour outside it. -/
theorem exists_adj_out {S : Set (CTorus d L N₁ m₁ K)} (hne : S.Nonempty) (hS : S ≠ Set.univ) :
    ∃ x ∈ S, ∃ y ∉ S, Adj x y := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨y0, hy0⟩ := (Set.ne_univ_iff_exists_notMem S).1 hS
  have hy : y0 = x0 + natT (fun μ => (y0 μ - x0 μ).val) := by
    funext μ; simp
  have hpath := reach_box x0 (fun μ => (y0 μ - x0 μ).val) Set.univ (fun _ _ => trivial)
  rw [← hy] at hpath
  have key : ∀ z, Relation.ReflTransGen (fun x y => (latGraph d ((N₁ * L ^ m₁) * L ^ K)).Adj x y ∧
      x ∈ (Set.univ : Set (CTorus d L N₁ m₁ K)) ∧ y ∈ (Set.univ : Set (CTorus d L N₁ m₁ K))) x0 z →
      z ∈ S ∨ ∃ x ∈ S, ∃ y ∉ S, Adj x y := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hx0
    | @tail b c _ hbc ih =>
      rcases ih with hb | h
      · by_cases hc : c ∈ S
        · exact Or.inl hc
        · exact Or.inr ⟨b, hb, c, hc, hbc.1.2⟩
      · exact Or.inr h
  rcases key y0 hpath with h | h
  · exact absurd h hy0
  · exact h

/-- **No margin for `X₁` itself:** if `X₁` is nonempty and not the whole torus, `psiThick X₁`
is not contained in `X₁`. -/
theorem not_psiThick_subset {S : Set (CTorus d L N₁ m₁ K)} (hne : S.Nonempty)
    (hS : S ≠ Set.univ) : ¬ psiThick S ⊆ S := by
  intro h
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_adj_out hne hS
  exact hy (h (Or.inr ⟨x, hx, hxy⟩))

end CellsC

section BlockThick

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L]

/-- The cell argument does **not** give `blockThick Y ⊆ Y`: `blockThick Y` contains `psiThick Y`
(the neighbours of `Y`), and a nonempty proper `Y` has a neighbour outside it.  In particular this
holds for every nonempty proper union of complete unit blocks. -/
theorem not_blockThick_subset {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hne : Y.Nonempty)
    (hY : Y ≠ Set.univ) : ¬ blockThick Y ⊆ Y :=
  fun h => not_psiThick_subset hne hY ((psiThick_subset_blockThick Y).trans h)

end BlockThick

end Balaban.Localization
