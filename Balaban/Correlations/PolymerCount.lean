/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Geometry.IsPolymer
public import Balaban.Lattice.Blocks
public import Balaban.Polymer.BlockTorus
public import Balaban.Polymer.Animals
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# Counting polymers (CORRELATIONS.md, Lemma 1.1)

Conditional development of Root-C: geometry used by the consequences of the clauses of Root-F.
A polymer `X` of block side `s` on the torus `(ℤ/ℓ)^d`, `ℓ = s m`, is determined by its image
`X.image (blockMap s m)` in the block torus, a connected set of blocks (an animal of
`blockGraph d m`, of maximal degree `2 d`); `|X| = s^d * (number of blocks)`.  Consequently the
number of polymers through a point with `n` blocks is at most `(2 d)^(2 (n-1))`, and
`∑_{X ∋ x, n(X) ≥ n₀} r^{n(X)} ≤ 2 (1/2)^{n₀}` whenever `(2 d)^2 r ≤ 1/2`.
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Balaban.Correlations

open Balaban Balaban.Polymer Finset

variable {d ℓ s m : ℕ} [NeZero ℓ]

/-- The block number `|X| / s^d` of a set of sites. -/
def blockNumber (d s : ℕ) {α : Type*} (X : Finset α) : ℕ := X.card / s ^ d

theorem pos_of_eq_mul (hℓ : ℓ = s * m) : 0 < s :=
  Nat.pos_of_ne_zero fun h => NeZero.ne ℓ (by simp [hℓ, h])

theorem blockMap_eq_iff (hℓ : ℓ = s * m) [NeZero m] {x y : Torus d ℓ} :
    blockMap s m x = blockMap s m y ↔ ∀ μ, (x μ).val / s = (y μ).val / s := by
  simp only [funext_iff, blockMap_apply]
  refine forall_congr' fun μ => ?_
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [blockCoord_val hℓ, blockCoord_val hℓ] at this
  · intro h
    apply ZMod.val_injective
    rw [blockCoord_val hℓ, blockCoord_val hℓ]
    exact h

theorem polymer_eq_biUnion (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) :
    X = (X.image (blockMap s m)).biUnion (blockFibre s m) := by
  ext y
  simp only [mem_biUnion, mem_image, mem_blockFibre]
  constructor
  · intro hy
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨x, hx, rfl⟩, hyb⟩
    exact hX.2.1 x hx y ((blockMap_eq_iff hℓ).1 hyb.symm)

theorem polymer_card_eq (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) : X.card = (X.image (blockMap s m)).card * s ^ d := by
  conv_lhs => rw [polymer_eq_biUnion hℓ hX]
  rw [card_biUnion]
  · simp [card_blockFibre hℓ]
  · intro b _ b' _ hbb'
    rw [Function.onFun, Finset.disjoint_left]
    intro z hz hz'
    exact hbb' ((mem_blockFibre.1 hz).symm.trans (mem_blockFibre.1 hz'))

theorem polymer_blockNumber_eq (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) : blockNumber d s X = (X.image (blockMap s m)).card := by
  have hs : 0 < s := pos_of_eq_mul hℓ
  unfold blockNumber
  rw [polymer_card_eq hℓ hX, Nat.mul_div_cancel _ (pow_pos hs d)]

theorem polymer_card_eq_blockNumber (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) : X.card = blockNumber d s X * s ^ d := by
  rw [polymer_blockNumber_eq hℓ hX]
  exact polymer_card_eq hℓ hX

theorem blockCoord_add_one (hℓ : ℓ = s * m) [NeZero m] (z : ZMod ℓ) :
    blockCoord s m (z + 1) = blockCoord s m z ∨
      blockCoord s m (z + 1) = blockCoord s m z + 1 := by
  have hs : 0 < s := pos_of_eq_mul hℓ
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℕ, v < ℓ ∧ z = v :=
    ⟨z.val, ZMod.val_lt z, (ZMod.natCast_zmod_val z).symm⟩
  have h1 : ((v : ZMod ℓ) + 1) = ((v + 1 : ℕ) : ZMod ℓ) := by push_cast; rfl
  have hb : ∀ k : ℕ, blockCoord s m (k : ZMod ℓ) = (((k % ℓ) / s : ℕ) : ZMod m) := by
    intro k
    unfold blockCoord
    rw [ZMod.val_natCast]
  rw [h1, hb, hb, Nat.mod_eq_of_lt hv]
  by_cases hlt : v + 1 < ℓ
  · rw [Nat.mod_eq_of_lt hlt, Nat.succ_div]
    split_ifs
    · right; push_cast; rfl
    · left; simp
  · right
    have hvl : v + 1 = ℓ := by omega
    rw [hvl, Nat.mod_self, Nat.zero_div]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := NeZero.pos m; omega⟩
    have hd : v / s = m' := by
      apply Nat.div_eq_of_lt_le
      · nlinarith
      · nlinarith
    rw [hd]
    simp

theorem blockMap_step (hℓ : ℓ = s * m) [NeZero m] (a : Torus d ℓ) (μ : Fin d) :
    blockMap s m (a + Pi.single μ 1) = blockMap s m a ∨
      blockMap s m (a + Pi.single μ 1) = blockMap s m a + Pi.single μ 1 := by
  rcases blockCoord_add_one hℓ (a μ) with h | h
  · left
    funext i
    by_cases hi : i = μ
    · subst hi; simpa [blockMap_apply] using h
    · simp [blockMap_apply, Pi.single_eq_of_ne hi]
  · right
    funext i
    by_cases hi : i = μ
    · subst hi; simpa [blockMap_apply] using h
    · simp [blockMap_apply, Pi.single_eq_of_ne hi]

theorem polymer_image_connected (hℓ : ℓ = s * m) [NeZero m] {X : Finset (Torus d ℓ)}
    (hX : IsPolymer d ℓ s X) :
    ((X.image (blockMap s m)).card ≠ 0) ∧
      ((blockGraph d m).induce ((X.image (blockMap s m) : Finset (Torus d m)) :
        Set (Torus d m))).Connected := by
  set Y := X.image (blockMap s m) with hY
  obtain ⟨x0, hx0⟩ := hX.1
  have hmem : ∀ y ∈ X, blockMap s m y ∈ (Y : Set (Torus d m)) := fun y hy =>
    mem_coe.2 (mem_image_of_mem _ hy)
  refine ⟨?_, ?_⟩
  · exact (card_pos.2 ⟨_, mem_image_of_mem _ hx0⟩).ne'
  have key : ∀ x (hx : x ∈ X), ∀ y, Relation.ReflTransGen
      (fun a b => a ∈ X ∧ b ∈ X ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
      x y → ∃ hy : y ∈ X,
        ((blockGraph d m).induce (Y : Set (Torus d m))).Reachable
          ⟨blockMap s m x, hmem x hx⟩ ⟨blockMap s m y, hmem y hy⟩ := by
    intro x hx y hxy
    induction hxy with
    | refl => exact ⟨hx, SimpleGraph.Reachable.refl _⟩
    | @tail b c _ hstep ih =>
      obtain ⟨hb, hreach⟩ := ih
      obtain ⟨_, hc, μ, hμ⟩ := hstep
      refine ⟨hc, hreach.trans ?_⟩
      by_cases hbc : blockMap s m b = blockMap s m c
      · have : (⟨blockMap s m b, hmem b hb⟩ : (Y : Set (Torus d m))) =
            ⟨blockMap s m c, hmem c hc⟩ := Subtype.ext hbc
        rw [this]
      · refine SimpleGraph.Adj.reachable ?_
        show (blockGraph d m).Adj (blockMap s m b) (blockMap s m c)
        refine ⟨hbc, μ, ?_⟩
        rcases hμ with rfl | rfl
        · rcases blockMap_step hℓ b μ with h | h
          · exact absurd h.symm hbc
          · exact Or.inl h
        · rcases blockMap_step hℓ c μ with h | h
          · exact absurd h hbc
          · exact Or.inr h
  have : Nonempty (Y : Set (Torus d m)) := ⟨⟨blockMap s m x0, hmem x0 hx0⟩⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  obtain ⟨x, hx, rfl⟩ := mem_image.1 (mem_coe.1 hu)
  obtain ⟨y, hy, rfl⟩ := mem_image.1 (mem_coe.1 hv)
  obtain ⟨_, h⟩ := key x hx y (hX.2.2 x hx y hy)
  exact h

/-- The polymers (of block side `s`) containing the site `x`. -/
def polymersAt (d ℓ s : ℕ) [NeZero ℓ] (x : Torus d ℓ) : Finset (Finset (Torus d ℓ)) :=
  univ.filter fun X => IsPolymer d ℓ s X ∧ x ∈ X

theorem mem_polymersAt {x : Torus d ℓ} {X : Finset (Torus d ℓ)} :
    X ∈ polymersAt d ℓ s x ↔ IsPolymer d ℓ s X ∧ x ∈ X := by
  simp [polymersAt]

/-- Lemma 1.1 (counting): the polymers through `x` with `n` blocks number at most
`(2 d)^(2 (n-1))`. -/
theorem card_polymersAt_blockNumber_le (hℓ : ℓ = s * m) [NeZero m] (x : Torus d ℓ) (n : ℕ) :
    (((polymersAt d ℓ s x).filter fun X => blockNumber d s X = n)).card ≤
      (2 * d) ^ (2 * (n - 1)) := by
  have hs : 0 < s := pos_of_eq_mul hℓ
  refine le_trans (card_le_card_of_injOn (fun X => X.image (blockMap s m))
    (t := animals (blockGraph d m) (blockMap s m x) n) ?_ ?_)
    (card_animals_le (blockGraph d m) (blockGraph_degree_le d m) _ n)
  · intro X hX
    simp only [coe_filter, Set.mem_ofPred_eq, mem_polymersAt] at hX
    obtain ⟨⟨hXp, hxX⟩, hn⟩ := hX
    rw [mem_coe, mem_animals]
    refine ⟨mem_image_of_mem _ hxX, ?_, (polymer_image_connected hℓ hXp).2⟩
    rw [← polymer_blockNumber_eq hℓ hXp, hn]
  · intro X hX X' hX' h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_polymersAt] at hX hX'
    rw [polymer_eq_biUnion hℓ hX.1.1, polymer_eq_biUnion hℓ hX'.1.1]
    simp only at h
    rw [h]

theorem blockNumber_le_card (x : Finset (Torus d ℓ)) :
    blockNumber d s x ≤ Fintype.card (Torus d ℓ) :=
  (Nat.div_le_self _ _).trans (card_le_univ x)

/-- Lemma 1.1 (summation): `∑_{X ∋ x, n(X) ≥ n₀} r^{n(X)} ≤ 2 (1/2)^{n₀}` if `(2 d)^2 r ≤ 1/2`. -/
theorem sum_polymersAt_pow_le (hℓ : ℓ = s * m) [NeZero m] (hd : 1 ≤ d) (x : Torus d ℓ)
    (n0 : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : ((2 * d : ℕ) : ℝ) ^ 2 * r ≤ 1 / 2) :
    ∑ X ∈ (polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X),
        r ^ blockNumber d s X ≤ 2 * (1 / 2) ^ n0 := by
  set K := Fintype.card (Torus d ℓ)
  have hmaps : ∀ X ∈ (polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X),
      blockNumber d s X ∈ Ico n0 (K + 1) := by
    intro X hX
    rw [mem_filter] at hX
    exact mem_Ico.2 ⟨hX.2, Nat.lt_succ_of_le (blockNumber_le_card X)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hn : ∀ n ∈ Ico n0 (K + 1),
      ∑ X ∈ ((polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X)).filter
          (fun X => blockNumber d s X = n), r ^ blockNumber d s X ≤ (1 / 2 : ℝ) ^ n := by
    intro n _
    have h1 : ∑ X ∈ ((polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X)).filter
          (fun X => blockNumber d s X = n), r ^ blockNumber d s X =
        (((polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X)).filter
          (fun X => blockNumber d s X = n)).card • r ^ n := by
      rw [← sum_const]
      refine sum_congr rfl fun X hX => ?_
      rw [mem_filter] at hX
      rw [hX.2]
    rw [h1, nsmul_eq_mul]
    have hcard : ((((polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X)).filter
          (fun X => blockNumber d s X = n)).card : ℝ) ≤ ((2 * d : ℕ) : ℝ) ^ (2 * n) := by
      have h2 : (((polymersAt d ℓ s x).filter (fun X => n0 ≤ blockNumber d s X)).filter
          (fun X => blockNumber d s X = n)).card ≤ (2 * d) ^ (2 * n) := by
        refine le_trans (card_le_card ?_) ((card_polymersAt_blockNumber_le hℓ x n).trans
          (Nat.pow_le_pow_right (by omega) (by omega)))
        intro X hX
        simp only [mem_filter] at hX ⊢
        exact ⟨hX.1.1, hX.2⟩
      exact_mod_cast h2
    calc _ ≤ ((2 * d : ℕ) : ℝ) ^ (2 * n) * r ^ n :=
          mul_le_mul_of_nonneg_right hcard (pow_nonneg hr0 n)
      _ = (((2 * d : ℕ) : ℝ) ^ 2 * r) ^ n := by rw [mul_pow, pow_mul]
      _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by positivity) hr n
  calc _ ≤ ∑ n ∈ Ico n0 (K + 1), (1 / 2 : ℝ) ^ n := sum_le_sum hn
    _ ≤ (1 / 2) ^ n0 / (1 - 1 / 2) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ = _ := by ring

end Balaban.Correlations
