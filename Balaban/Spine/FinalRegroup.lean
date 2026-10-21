/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Geometry.IsPolymer
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Balaban.Lattice.Blocks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The hull of a polymer in coarser blocks

A6-3 (c): the regrouping `Y ↦ Ȳ` of polymers of scale `k` into polymers of scale `k + 1`. For a
block side `s'` the hull `hullT s' Y` of a finite set `Y` of sites of the torus is the union of the
`s'`-blocks meeting `Y`. This file proves that the hull of a connected set is connected
(`hull_isPolymer`), hence a polymer of block side `s'`.
-/

@[expose] public section

open Finset

namespace Balaban

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The nearest-neighbour step relation inside a set `X` (the one of `IsPolymer`). -/
def StepIn (X : Finset (Torus d ℓ)) (a b : Torus d ℓ) : Prop :=
  a ∈ X ∧ b ∈ X ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1

/-- The coordinate distance of two sites (sum over the directions of the distances of the
representatives). -/
def coordDist (x y : Torus d ℓ) : ℕ := ∑ μ, (((x μ).val : ℤ) - ((y μ).val : ℤ)).natAbs

theorem val_add_single_self (x : Torus d ℓ) (μ : Fin d) (h : (x μ).val + 1 < ℓ) :
    ((x + (Pi.single μ 1 : Torus d ℓ)) μ).val = (x μ).val + 1 := by
  simp only [Pi.add_apply, Pi.single_eq_same]
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < ℓ)]
  exact Nat.mod_eq_of_lt h

omit [NeZero ℓ] in
theorem val_add_single_ne (x : Torus d ℓ) {μ ν : Fin d} (h : ν ≠ μ) :
    ((x + (Pi.single μ 1 : Torus d ℓ)) ν).val = (x ν).val := by
  simp [Pi.single_eq_of_ne h]

theorem val_sub_single_self (x : Torus d ℓ) (μ : Fin d) (h : 1 ≤ (x μ).val) :
    ((x - (Pi.single μ 1 : Torus d ℓ)) μ).val = (x μ).val - 1 := by
  have hl : 1 < ℓ := by
    have := ZMod.val_lt (x μ); omega
  simp only [Pi.sub_apply, Pi.single_eq_same]
  rw [ZMod.val_sub (by rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl]; exact h),
    ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl]

omit [NeZero ℓ] in
theorem val_sub_single_ne (x : Torus d ℓ) {μ ν : Fin d} (h : ν ≠ μ) :
    ((x - (Pi.single μ 1 : Torus d ℓ)) ν).val = (x ν).val := by
  simp [Pi.single_eq_of_ne h]

/-- Two sites of the same `s'`-block are joined by a path of nearest-neighbour steps inside any set
containing the block. -/
theorem block_connected {s' : ℕ} (X : Finset (Torus d ℓ)) (c : Fin d → ℕ)
    (hX : ∀ z : Torus d ℓ, (∀ μ, (z μ).val / s' = c μ) → z ∈ X) :
    ∀ n : ℕ, ∀ x y : Torus d ℓ, coordDist x y = n → (∀ μ, (x μ).val / s' = c μ) →
      (∀ μ, (y μ).val / s' = c μ) → Relation.ReflTransGen (StepIn X) x y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x y hn hx hy
    by_cases hxy : x = y
    · subst hxy; exact Relation.ReflTransGen.refl
    · obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ y μ := by
        by_contra h; push Not at h; exact hxy (funext h)
      have hμv : (x μ).val ≠ (y μ).val := fun h => hμ (ZMod.val_injective ℓ h)
      have hxμ := hx μ
      have hyμ := hy μ
      have hlt := ZMod.val_lt (y μ)
      have hlt' := ZMod.val_lt (x μ)
      have hdist : ∀ x' : Torus d ℓ, (∀ ν, ν ≠ μ → (x' ν).val = (x ν).val) →
          (((x' μ).val : ℤ) - (y μ).val).natAbs < (((x μ).val : ℤ) - (y μ).val).natAbs →
          coordDist x' y < coordDist x y := by
        intro x' hne hlt2
        unfold coordDist
        refine Finset.sum_lt_sum (fun ν _ => ?_) ⟨μ, Finset.mem_univ _, hlt2⟩
        by_cases hν : ν = μ
        · subst hν; exact hlt2.le
        · rw [hne ν hν]
      rcases lt_or_gt_of_ne hμv with hlt2 | hgt2
      · -- step up
        have hv1 : (x μ).val + 1 < ℓ := by omega
        set x' : Torus d ℓ := x + (Pi.single μ 1 : Torus d ℓ) with hx'
        have hx'μ := val_add_single_self x μ hv1
        have hx'ν : ∀ ν, ν ≠ μ → (x' ν).val = (x ν).val := fun ν hν => val_add_single_ne x hν
        have hblk : ∀ ν, (x' ν).val / s' = c ν := by
          intro ν
          by_cases hν : ν = μ
          · subst hν
            rw [hx'μ]
            have h1 : ((x ν).val + 1) / s' ≤ (y ν).val / s' := Nat.div_le_div_right (by omega)
            have h2 : (x ν).val / s' ≤ ((x ν).val + 1) / s' := Nat.div_le_div_right (by omega)
            omega
          · rw [hx'ν ν hν]; exact hx ν
        have hstep : StepIn X x x' := ⟨hX x hx, hX x' hblk, μ, Or.inl rfl⟩
        have hd : coordDist x' y < coordDist x y := hdist x' hx'ν (by rw [hx'μ]; omega)
        exact Relation.ReflTransGen.head hstep (ih _ (hn ▸ hd) x' y rfl hblk hy)
      · -- step down
        have hv1 : 1 ≤ (x μ).val := by omega
        set x' : Torus d ℓ := x - (Pi.single μ 1 : Torus d ℓ) with hx'
        have hx'μ := val_sub_single_self x μ hv1
        have hx'ν : ∀ ν, ν ≠ μ → (x' ν).val = (x ν).val := fun ν hν => val_sub_single_ne x hν
        have hblk : ∀ ν, (x' ν).val / s' = c ν := by
          intro ν
          by_cases hν : ν = μ
          · subst hν
            rw [hx'μ]
            have h1 : ((x ν).val - 1) / s' ≤ (x ν).val / s' := Nat.div_le_div_right (by omega)
            have h2 : (y ν).val / s' ≤ ((x ν).val - 1) / s' := Nat.div_le_div_right (by omega)
            omega
          · rw [hx'ν ν hν]; exact hx ν
        have hstep : StepIn X x x' := ⟨hX x hx, hX x' hblk, μ, Or.inr (sub_add_cancel x _).symm⟩
        have hd : coordDist x' y < coordDist x y := hdist x' hx'ν (by rw [hx'μ]; omega)
        exact Relation.ReflTransGen.head hstep (ih _ (hn ▸ hd) x' y rfl hblk hy)

omit [NeZero ℓ] in
/-- Paths inside a subset are paths inside a larger set. -/
theorem stepIn_mono {Y X : Finset (Torus d ℓ)} (h : Y ⊆ X) {x y : Torus d ℓ}
    (hc : Relation.ReflTransGen (StepIn Y) x y) : Relation.ReflTransGen (StepIn X) x y := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih ⟨h hbc.1, h hbc.2.1, hbc.2.2⟩

/-- The hull of `Y` in `s'`-blocks: the union of the `s'`-blocks meeting `Y`. -/
def hullT (s' : ℕ) (Y : Finset (Torus d ℓ)) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun x => ∃ y ∈ Y, ∀ μ, (x μ).val / s' = (y μ).val / s'

theorem mem_hullT {s' : ℕ} {Y : Finset (Torus d ℓ)} {x : Torus d ℓ} :
    x ∈ hullT s' Y ↔ ∃ y ∈ Y, ∀ μ, (x μ).val / s' = (y μ).val / s' := by
  simp [hullT]

theorem subset_hullT (s' : ℕ) (Y : Finset (Torus d ℓ)) : Y ⊆ hullT s' Y :=
  fun y hy => mem_hullT.2 ⟨y, hy, fun _ => rfl⟩

theorem hullT_mono (s' : ℕ) {Y Y' : Finset (Torus d ℓ)} (h : Y ⊆ Y') : hullT s' Y ⊆ hullT s' Y' :=
  fun _ hx => by
    obtain ⟨y, hy, hxy⟩ := mem_hullT.1 hx
    exact mem_hullT.2 ⟨y, h hy, hxy⟩

/-- **The hull of a connected nonempty set is a polymer of the coarser blocks.** -/
theorem hullT_isPolymer {s s' : ℕ} {Y : Finset (Torus d ℓ)} (hY : IsPolymer d ℓ s Y) :
    IsPolymer d ℓ s' (hullT s' Y) := by
  obtain ⟨hne, -, hconn⟩ := hY
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hne
    exact ⟨y, subset_hullT s' Y hy⟩
  · intro x hx z hxz
    obtain ⟨y, hy, hxy⟩ := mem_hullT.1 hx
    exact mem_hullT.2 ⟨y, hy, fun μ => (hxz μ).symm.trans (hxy μ)⟩
  · intro x hx y hy
    obtain ⟨x0, hx0, hxx0⟩ := mem_hullT.1 hx
    obtain ⟨y0, hy0, hyy0⟩ := mem_hullT.1 hy
    have hblk : ∀ (z0 : Torus d ℓ), z0 ∈ Y → ∀ z : Torus d ℓ,
        (∀ μ, (z μ).val / s' = (z0 μ).val / s') → z ∈ hullT s' Y :=
      fun z0 hz0 z hz => mem_hullT.2 ⟨z0, hz0, hz⟩
    have p1 : Relation.ReflTransGen (StepIn (hullT s' Y)) x x0 :=
      block_connected (hullT s' Y) (fun μ => (x0 μ).val / s') (hblk x0 hx0) _ x x0 rfl
        hxx0 (fun _ => rfl)
    have p3 : Relation.ReflTransGen (StepIn (hullT s' Y)) y0 y :=
      block_connected (hullT s' Y) (fun μ => (y0 μ).val / s') (hblk y0 hy0) _ y0 y rfl
        (fun _ => rfl) hyy0
    have p2 : Relation.ReflTransGen (StepIn (hullT s' Y)) x0 y0 := by
      have hc := hconn x0 hx0 y0 hy0
      exact stepIn_mono (subset_hullT s' Y) hc
    exact (p1.trans p2).trans p3

section Count

variable {s m : ℕ}

theorem cell_eq_iff [NeZero m] (hℓ : ℓ = s * m) {x z : Torus d ℓ} :
    blockMap s m x = blockMap s m z ↔ ∀ μ, (x μ).val / s = (z μ).val / s := by
  constructor
  · intro h μ
    have := congrFun h μ
    simp only [blockMap_apply] at this
    rw [← blockCoord_val hℓ, ← blockCoord_val hℓ, this]
  · intro h
    funext μ
    simp only [blockMap_apply]
    apply ZMod.val_injective
    rw [blockCoord_val hℓ, blockCoord_val hℓ]
    exact h μ

/-- A block-closed set is the disjoint union of the blocks it contains. -/
theorem card_blockClosed [NeZero m] (hℓ : ℓ = s * m) (Y : Finset (Torus d ℓ))
    (hY : ∀ x ∈ Y, ∀ z : Torus d ℓ, (∀ μ, (x μ).val / s = (z μ).val / s) → z ∈ Y) :
    Y.card = s ^ d * (Y.image (blockMap s m)).card := by
  classical
  have h1 : Y = (Y.image (blockMap s m)).biUnion fun c => blockFibre s m c := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, mem_blockFibre]
    constructor
    · intro hx; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨c, ⟨y, hy, rfl⟩, hxc⟩
      exact hY y hy x ((cell_eq_iff hℓ).1 hxc.symm)
  conv_lhs => rw [h1]
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun c _ => card_blockFibre hℓ c]
    simp [mul_comm]
  · intro c _ c' _ hcc'
    refine Finset.disjoint_left.2 fun x hx hx' => hcc' ?_
    rw [mem_blockFibre] at hx hx'
    rw [← hx, ← hx']

/-- The cells of the hull are coarse cells of the cells of the set. -/
theorem hull_cells_card_le {L' m' : ℕ} [NeZero m'] [NeZero (L' * m')] (hℓ : ℓ = s * (L' * m'))
    (Y : Finset (Torus d ℓ)) :
    ((hullT (s * L') Y).image (blockMap (s * L') m')).card ≤
      (Y.image (blockMap s (L' * m'))).card := by
  classical
  have hℓ' : ℓ = (s * L') * m' := by rw [hℓ]; ring
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := Y.image (blockMap s (L' * m')))
    (f := blockMap L' m'))
  intro c hc
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨y, hy, hxy⟩ := mem_hullT.1 hx
  refine Finset.mem_image.2 ⟨blockMap s (L' * m') y, Finset.mem_image_of_mem _ hy, ?_⟩
  rw [blockMap_comp hℓ rfl]
  exact ((cell_eq_iff hℓ').2 hxy).symm

/-- The number of block-closed subsets of `X` is at most `2^{#cells of X}`. -/
theorem card_closedSubsets_le [NeZero m] (hℓ : ℓ = s * m) (X : Finset (Torus d ℓ)) :
    ((Finset.univ : Finset (Finset (Torus d ℓ))).filter fun Y => Y ⊆ X ∧
        ∀ x ∈ Y, ∀ z : Torus d ℓ, (∀ μ, (x μ).val / s = (z μ).val / s) → z ∈ Y).card ≤
      2 ^ (X.image (blockMap s m)).card := by
  classical
  rw [← Finset.card_powerset]
  refine Finset.card_le_card_of_injOn (fun Y => Y.image (blockMap s m)) ?_ ?_
  · intro Y hY
    have hY' := (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).2
    exact Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.image_subset_image hY'.1))
  · intro Y hY Y' hY' hYY'
    have hY := (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).2
    have hY' := (Finset.mem_filter.1 (Finset.mem_coe.1 hY')).2
    have key : ∀ A B : Finset (Torus d ℓ),
        (∀ x ∈ A, ∀ z : Torus d ℓ, (∀ μ, (x μ).val / s = (z μ).val / s) → z ∈ A) →
        (∀ x ∈ B, ∀ z : Torus d ℓ, (∀ μ, (x μ).val / s = (z μ).val / s) → z ∈ B) →
        A.image (blockMap s m) = B.image (blockMap s m) → A ⊆ B := by
      intro A B hA hB hAB x hx
      have : blockMap s m x ∈ B.image (blockMap s m) := hAB ▸ Finset.mem_image_of_mem _ hx
      obtain ⟨y', hy', hyx⟩ := Finset.mem_image.1 this
      exact hB y' hy' x ((cell_eq_iff hℓ).1 hyx)
    exact Finset.Subset.antisymm (key Y Y' hY.2 hY'.2 hYY') (key Y' Y hY'.2 hY.2 hYY'.symm)

open Classical in
/-- **The counting estimate of the regrouping.** The polymers `Y` of block side `s` with hull `X` in
blocks of side `s L'` carry the weights `exp(-κ' |Y|/s^d)`; their sum is at most
`exp(-(κ' - L'^d log 2) |X|/(s L')^d)`. -/
theorem regroup_sum_bound {L' m' : ℕ} [NeZero m'] [NeZero (L' * m')] (hℓ : ℓ = s * (L' * m'))
    (hs : 0 < s) (X : Finset (Torus d ℓ)) {κ' : ℝ} (hκ : 0 ≤ κ') :
    ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d ℓ))).filter
        (fun Y => hullT (s * L') Y = X ∧ IsPolymer d ℓ s Y),
      Real.exp (-κ' * (Y.card : ℝ) / (s : ℝ) ^ d) ≤
      Real.exp (-(κ' - (L' : ℝ) ^ d * Real.log 2) * (X.card : ℝ) / ((s * L' : ℕ) : ℝ) ^ d) := by
  classical
  set 𝒴 := (Finset.univ : Finset (Finset (Torus d ℓ))).filter
    (fun Y => hullT (s * L') Y = X ∧ IsPolymer d ℓ s Y) with h𝒴
  by_cases hempty : 𝒴 = ∅
  · rw [hempty]; simp only [Finset.sum_empty]; exact (Real.exp_pos _).le
  obtain ⟨Y0, hY0⟩ := Finset.nonempty_iff_ne_empty.2 hempty
  have hY0' := Finset.mem_filter.1 hY0
  have hℓ' : ℓ = (s * L') * m' := by rw [hℓ]; ring
  have hpoly := hullT_isPolymer (s' := s * L') hY0'.2.2
  rw [hY0'.2.1] at hpoly
  have hXcl := hpoly.2.1
  set r := (X.image (blockMap (s * L') m')).card with hr
  have hcardX : X.card = (s * L') ^ d * r := card_blockClosed hℓ' X hXcl
  have hXcl_s : ∀ x ∈ X, ∀ z : Torus d ℓ, (∀ μ, (x μ).val / s = (z μ).val / s) → z ∈ X := by
    intro x hx z hz
    refine hXcl x hx z fun μ => ?_
    rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hz μ]
  have hcardXs : X.card = s ^ d * (X.image (blockMap s (L' * m'))).card :=
    card_blockClosed hℓ X hXcl_s
  have hcs : (X.image (blockMap s (L' * m'))).card = L' ^ d * r := by
    have : s ^ d * (X.image (blockMap s (L' * m'))).card = s ^ d * (L' ^ d * r) := by
      rw [← hcardXs, hcardX, mul_pow]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hs d) this
  have hterm : ∀ Y ∈ 𝒴, Real.exp (-κ' * (Y.card : ℝ) / (s : ℝ) ^ d) ≤ Real.exp (-κ' * r) := by
    intro Y hY
    have hY' := Finset.mem_filter.1 hY
    have hYcard : Y.card = s ^ d * (Y.image (blockMap s (L' * m'))).card :=
      card_blockClosed hℓ Y hY'.2.2.2.1
    have hle : r ≤ (Y.image (blockMap s (L' * m'))).card := by
      have := hull_cells_card_le (s := s) (L' := L') (m' := m') hℓ Y
      rw [hY'.2.1] at this
      exact this
    refine Real.exp_le_exp.2 ?_
    have hsd : (0 : ℝ) < (s : ℝ) ^ d := by positivity
    rw [hYcard]
    push_cast
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hsd.ne']
    have : (r : ℝ) ≤ ((Y.image (blockMap s (L' * m'))).card : ℝ) := by exact_mod_cast hle
    nlinarith
  have hcount : 𝒴.card ≤ 2 ^ (L' ^ d * r) := by
    refine le_trans (Finset.card_le_card ?_) (hcs ▸ card_closedSubsets_le hℓ X)
    intro Y hY
    have hY' := Finset.mem_filter.1 hY
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hY'.2.2.2.1⟩
    rw [← hY'.2.1]
    exact subset_hullT _ Y
  calc ∑ Y ∈ 𝒴, Real.exp (-κ' * (Y.card : ℝ) / (s : ℝ) ^ d)
      ≤ ∑ Y ∈ 𝒴, Real.exp (-κ' * r) := Finset.sum_le_sum hterm
    _ = (𝒴.card : ℝ) * Real.exp (-κ' * r) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (L' ^ d * r) * Real.exp (-κ' * r) := by
        gcongr
        exact_mod_cast hcount
    _ = Real.exp (-(κ' - (L' : ℝ) ^ d * Real.log 2) * (X.card : ℝ) / ((s * L' : ℕ) : ℝ) ^ d) := by
        have h2 : (2 : ℝ) ^ (L' ^ d * r) = Real.exp (((L' ^ d * r : ℕ) : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        have hsd : (0 : ℝ) < ((s * L' : ℕ) : ℝ) ^ d := by
          have : 0 < s * L' := by
            rcases Nat.eq_zero_or_pos L' with h0 | h0
            · exfalso; subst h0; simp at hℓ; exact NeZero.ne ℓ hℓ
            · exact Nat.mul_pos hs h0
          positivity
        have hX' : (X.card : ℝ) = ((s * L' : ℕ) : ℝ) ^ d * r := by exact_mod_cast hcardX
        rw [h2, ← Real.exp_add, hX']
        congr 1
        generalize ((s * L' : ℕ) : ℝ) ^ d = P at hsd ⊢
        have e : -(κ' - (L' : ℝ) ^ d * Real.log 2) * (P * r) / P =
            -(κ' - (L' : ℝ) ^ d * Real.log 2) * r := by field_simp
        rw [e]
        push_cast
        ring

end Count

end Balaban
