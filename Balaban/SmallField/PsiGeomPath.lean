/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.BlockCount
public import Balaban.SmallField.Def6Terms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# P1 (3.54): the path estimate on a polymer, in the landed carriers

A function `f` that is constant on the blocks of side `L ^ j` and varies by at most `δ` across every
bond of a connected structure `(W, E)` varies by at most `δ · #(blocks met by W)` on `W`
(`variation_le_card_image`; a discrete intermediate-value count in the style of
`Balaban.Localization.card_edges_ge`).  Together with the block count `card_cells_le`
(a connected structure with `|E|` bonds meets at most `3^d (|E| / L^j + 1)` blocks) and the
covering size `d_j(X)` this gives (3.54) (`psi_path_le`):
two points `y, z` of a polymer `X ∈ 𝒟_j` are joined inside `X` at a block distance
`≤ 3^d (M (4 d L + d_j(X)) + 1)`, `M = L^{m₀+m₁}`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6 Finset

section Variation

variable {α V F : Type*} [DecidableEq V] [SeminormedAddCommGroup F]

/-- **Variation along a connected structure.**  If `f` is constant on the fibres of `β`, varies by
at most `δ` across every bond of the connected structure `(W, E)`, then
`‖f y - f x‖ ≤ δ · #(β '' W)` for `x, y ∈ W`. -/
theorem variation_le_card_image (β : α → V) (f : α → F) (hfib : ∀ u v, β u = β v → f u = f v)
    (W : Finset α) (E : Finset (α × α))
    (hconn : ∀ x ∈ W, ∀ y ∈ W, Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x y)
    (hE : ∀ p ∈ E, p.1 ∈ W ∧ p.2 ∈ W) {δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ p ∈ E, ‖f p.1 - f p.2‖ ≤ δ) {x y : α} (hx : x ∈ W) (hy : y ∈ W) :
    ‖f y - f x‖ ≤ δ * (W.image β).card := by
  classical
  set g : α → ℕ := fun z => ⌊‖f z - f x‖ / δ⌋₊ with hg
  have hLip : ∀ p ∈ E, g p.1 ≤ g p.2 + 1 ∧ g p.2 ≤ g p.1 + 1 := by
    intro p hp
    have h1 := hstep p hp
    have t1 : ‖f p.1 - f x‖ ≤ ‖f p.2 - f x‖ + δ := by
      calc ‖f p.1 - f x‖ = ‖(f p.1 - f p.2) + (f p.2 - f x)‖ := by congr 1; abel
        _ ≤ ‖f p.1 - f p.2‖ + ‖f p.2 - f x‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have t2 : ‖f p.2 - f x‖ ≤ ‖f p.1 - f x‖ + δ := by
      calc ‖f p.2 - f x‖ = ‖(f p.2 - f p.1) + (f p.1 - f x)‖ := by congr 1; abel
        _ ≤ ‖f p.2 - f p.1‖ + ‖f p.1 - f x‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_sub_rev]; linarith
    have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ b + δ → ⌊a / δ⌋₊ ≤ ⌊b / δ⌋₊ + 1 := by
      intro a b ha hb hab
      have h2 : a / δ ≤ b / δ + 1 := by
        rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; exact hab
      calc ⌊a / δ⌋₊ ≤ ⌊b / δ + 1⌋₊ := Nat.floor_le_floor h2
        _ = ⌊b / δ⌋₊ + 1 := Nat.floor_add_one (by positivity)
    exact ⟨key _ _ (norm_nonneg _) (norm_nonneg _) t1, key _ _ (norm_nonneg _) (norm_nonneg _) t2⟩
  have hgx : g x = 0 := by simp [hg]
  have hcross := crossing_edge g W E hconn hLip hx hy hgx
  have hlevel : ∀ t ≤ g y, ∃ z ∈ W, g z = t := by
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | htp
    · exact ⟨x, hx, hgx⟩
    · obtain ⟨p, hp, hc⟩ := hcross (t - 1) (by omega)
      obtain ⟨hp1, hp2⟩ := hE p hp
      rcases hc with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact ⟨p.2, hp2, by omega⟩
      · exact ⟨p.1, hp1, by omega⟩
  have : Nonempty α := ⟨x⟩
  choose! z hzW hzg using hlevel
  have hinj : Set.InjOn (fun t => β (z t)) (↑(Finset.range (g y + 1)) : Set ℕ) := by
    intro t ht t' ht' h
    have h' := hfib _ _ h
    have e1 := hzg t (by simpa [Nat.lt_succ_iff] using ht)
    have e2 := hzg t' (by simpa [Nat.lt_succ_iff] using ht')
    have : g (z t) = g (z t') := by
      show ⌊‖f (z t) - f x‖ / δ⌋₊ = ⌊‖f (z t') - f x‖ / δ⌋₊
      rw [h']
    omega
  have hcard : g y + 1 ≤ (W.image β).card := by
    have := Finset.card_le_card_of_injOn (fun t => β (z t)) (s := Finset.range (g y + 1))
      (t := W.image β) (fun t ht => by
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨z t, hzW t ?_, rfl⟩)
        simpa [Nat.lt_succ_iff] using ht) hinj
    simpa using this
  have hlt : ‖f y - f x‖ / δ < g y + 1 := Nat.lt_floor_add_one _
  have : ‖f y - f x‖ < δ * (g y + 1) := by
    rw [div_lt_iff₀ hδ] at hlt; linarith
  calc ‖f y - f x‖ ≤ δ * (g y + 1) := this.le
    _ ≤ δ * (W.image β).card := by
      gcongr; exact_mod_cast hcard

end Variation

section Blocks

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {j m₀ : ℕ}

/-- The block count in the form used for `jBlock`: a connected structure with `|E|` bonds meets at
most `3^d (|E| / L^j + 1)` of the `j`-blocks. -/
theorem card_jBlock_image_le (hjk : j ≤ k) {W : Finset (CTorus d L N₁ m₁ k)}
    {E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k)} (hc : ConnStruct W E) :
    (L : ℝ) ^ j * ((W.image (jBlock d L (N₁ * L ^ m₁) k j)).card : ℝ) ≤
      3 ^ d * ((E.card : ℝ) + (L : ℝ) ^ j) := by
  have hLp : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hn : (N₁ * L ^ m₁) * L ^ k = L ^ j * ((N₁ * L ^ m₁) * L ^ (k - j)) := side_eq hjk
  have hm : NeZero ((N₁ * L ^ m₁) * L ^ (k - j)) := ⟨by
    have : (N₁ * L ^ m₁) * L ^ k ≠ 0 := NeZero.ne _
    rw [hn] at this
    exact right_ne_zero_of_mul this⟩
  have h := card_cells_le (d := d) (m := (N₁ * L ^ m₁) * L ^ (k - j)) (a := L ^ j) hn
    (pow_pos hLp j) hc
  exact_mod_cast h

/-- **Variation of a block-constant function along a connected structure.** -/
theorem variation_le_blocks {F : Type*} [SeminormedAddCommGroup F] (hjk : j ≤ k)
    {f : CTorus d L N₁ m₁ k → F}
    (hfib : ∀ u v, jBlock d L (N₁ * L ^ m₁) k j u = jBlock d L (N₁ * L ^ m₁) k j v → f u = f v)
    {W : Finset (CTorus d L N₁ m₁ k)} {E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k)}
    (hc : ConnStruct W E) {δ : ℝ} (hδ : 0 < δ) (hstep : ∀ p ∈ E, ‖f p.1 - f p.2‖ ≤ δ)
    {x y : CTorus d L N₁ m₁ k} (hx : x ∈ W) (hy : y ∈ W) :
    ‖f y - f x‖ ≤ δ * (3 ^ d * ((E.card : ℝ) / (L : ℝ) ^ j + 1)) := by
  have hLp : (0 : ℝ) < (L : ℝ) ^ j := by
    have : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h1 := variation_le_card_image (jBlock d L (N₁ * L ^ m₁) k j) f hfib W E hc.2.2
    (fun p hp => ⟨(hc.2.1 p hp).1, (hc.2.1 p hp).2.1⟩) hδ hstep hx hy
  have h2 := card_jBlock_image_le (j := j) (m₁ := m₁) hjk hc
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hδ.le)
  rw [← le_div_iff₀' hLp] at h2
  calc _ ≤ 3 ^ d * ((E.card : ℝ) + (L : ℝ) ^ j) / (L : ℝ) ^ j := h2
    _ = _ := by field_simp

/-- The structure `(X, all bonds of X)` is admissible for the covering size of a polymer
`X ∈ 𝒟_j`. -/
theorem exists_cover_struct {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X) :
    ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W := by
  classical
  obtain ⟨hne, ⟨𝒦, hch⟩, hconn⟩ := hX
  have hL : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  let W : Finset (CTorus d L N₁ m₁ k) := Finset.univ.filter (· ∈ X)
  let E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k) :=
    Finset.univ.filter fun p => p.1 ∈ X ∧ p.2 ∈ X ∧ Nbr p.1 p.2
  refine ⟨𝒦, W, E, hch, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [W, hx]⟩
  · intro p hp
    simpa [E, W] using (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    have hx' : x ∈ X := by simpa [W] using hx
    have hy' : y ∈ X := by simpa [W] using hy
    refine Relation.ReflTransGen.mono (fun u v huv => ?_) x y (hconn x hx' y hy')
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl huv
  · intro x hx; simpa [W] using hx
  · intro b hb
    refine ⟨b, ?_, mem_box_self b hL⟩
    simpa [W] using (hch.1 b hb).2 (mem_box_self b hL)

/-- **(3.54), the path estimate** (P1 p. 132, (3.54)-(3.55), in the landed carriers).  Let `X ∈ 𝒟_j`
and let `f` be a function on the fine torus that is constant on the `j`-blocks and varies by at most
`δ` across every bond of the lattice with both endpoints in `X`.  Then for `y, z ∈ X`
`‖f z - f y‖ ≤ δ · 3^d (M (4 d L + d_j(X)) + 1)`, `M = L^{m₀+m₁}`, `d_j = sizeJ`.

(P1 has `δ (2 d L M + d M d(X))`, from a path `Γ_{y,x}` of at most that many unit steps of the
`j`-lattice; the landed covering size `d_j` and the block count of `card_cells_le` give the constant
`3^d` in place of `d`, and `4 d L` in place of `2 d L`: the points `y`, `z` are joined to the tree
inside their cubes at cost `2 d L` each.) -/
theorem psi_path_le {F : Type*} [SeminormedAddCommGroup F] (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X) {f : CTorus d L N₁ m₁ k → F}
    (hfib : ∀ u v, jBlock d L (N₁ * L ^ m₁) k j u = jBlock d L (N₁ * L ^ m₁) k j v → f u = f v)
    {δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ p ∈ X, ∀ q ∈ X, Nbr p q → ‖f p - f q‖ ≤ δ) {y z : CTorus d L N₁ m₁ k}
    (hy : y ∈ X) (hz : z ∈ X) :
    ‖f z - f y‖ ≤ δ * (3 ^ d * ((L : ℝ) ^ (m₀ + m₁) * (4 * d * L + sizeJ m₀ j X) + 1)) := by
  classical
  obtain ⟨𝒦, W, E, hch, hc, hWX, hmeet, hcost⟩ :=
    treeLenCovOne_attained m₀ j X (exists_cover_struct hX)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLp : (0 : ℝ) < L := by linarith
  set a : ℝ := (L : ℝ) ^ (m₀ + m₁ + j) with ha
  have hapos : 0 < a := by positivity
  have hω : ∀ u v : CTorus d L N₁ m₁ k, 0 ≤ scaleW L m₀ m₁ j u v := fun u v => by
    unfold scaleW; positivity
  have hωc : ∀ u ∈ X, ∀ v ∈ X, scaleW L m₀ m₁ j u v ≤ a⁻¹ := fun u _ v _ => le_rfl
  -- attach a point of `X` to the tree, inside its cube
  have attach : ∀ w ∈ X, ∃ q ∈ W, Linked X (scaleW L m₀ m₁ j) (2 * d * L) w q := by
    intro w hw
    obtain ⟨b, hb, hwb⟩ := hch.2 w hw
    obtain ⟨q, hqW, hqb⟩ := hmeet b hb
    refine ⟨q, hqW, ?_⟩
    have hbox : box b (L * cellSide L m₀ m₁ j) ⊆ X := (hch.1 b hb).2
    have := linked_box_pair hω b (L * cellSide L m₀ m₁ j) hbox hωc hwb hqb
    refine Covers.mono_c this (le_of_eq ?_)
    have e : ((L * cellSide L m₀ m₁ j : ℕ) : ℝ) * a⁻¹ = L := by
      unfold cellSide
      rw [ha]; push_cast
      have : ((L : ℝ) ^ (j + m₀ + m₁)) = (L : ℝ) ^ (m₀ + m₁ + j) := by congr 1; ring
      rw [this]; field_simp
    calc 2 * ((d : ℝ) * ((L * cellSide L m₀ m₁ j : ℕ) : ℝ) * a⁻¹)
        = 2 * d * (((L * cellSide L m₀ m₁ j : ℕ) : ℝ) * a⁻¹) := by ring
      _ = 2 * d * L := by rw [e]
  obtain ⟨qy, hqy, hly⟩ := attach y hy
  obtain ⟨qz, hqz, hlz⟩ := attach z hz
  have htree : Linked X (scaleW L m₀ m₁ j) (sizeJ m₀ j X) qy qz :=
    ⟨W, E, hc, hWX, by intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
                       rcases hu with rfl | rfl <;> assumption, by rw [sizeJ, ← hcost]⟩
  have hall := (Linked.trans hω hly (Linked.trans hω htree hlz.symm))
  obtain ⟨W', E', hc', hW'X, hyz, hcost'⟩ := hall
  have hy' : y ∈ W' := hyz (by simp)
  have hz' : z ∈ W' := hyz (by simp)
  have hstep' : ∀ p ∈ E', ‖f p.1 - f p.2‖ ≤ δ := by
    intro p hp
    obtain ⟨h1, h2, hn⟩ := hc'.2.1 p hp
    exact hstep _ (hW'X h1) _ (hW'X h2) hn
  have hv := variation_le_blocks (m₁ := m₁) hjk hfib hc' hδ hstep' hy' hz'
  refine hv.trans (mul_le_mul_of_nonneg_left ?_ hδ.le)
  have hbc : bondCost (scaleW L m₀ m₁ j) E' = (E'.card : ℝ) * a⁻¹ := by
    unfold bondCost scaleW
    rw [Finset.sum_const, nsmul_eq_mul, ← ha]
  have hE' : (E'.card : ℝ) ≤ (2 * d * L + (sizeJ m₀ j X + 2 * d * L)) * a := by
    rw [hbc] at hcost'
    rw [← div_eq_mul_inv, div_le_iff₀ hapos] at hcost'
    exact hcost'
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have e : a / (L : ℝ) ^ j = (L : ℝ) ^ (m₀ + m₁) := by
    rw [ha, pow_add _ (m₀ + m₁) j]; field_simp
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc (E'.card : ℝ) / (L : ℝ) ^ j + 1
      ≤ (2 * d * L + (sizeJ m₀ j X + 2 * d * L)) * a / (L : ℝ) ^ j + 1 := by
        gcongr
    _ = (L : ℝ) ^ (m₀ + m₁) * (4 * d * L + sizeJ m₀ j X) + 1 := by
        rw [mul_div_assoc, e]; ring

end Blocks

end Balaban.SmallField
