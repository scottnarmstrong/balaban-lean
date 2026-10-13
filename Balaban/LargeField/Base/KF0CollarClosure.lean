/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Lattice.Blocks
public import Balaban.Polymer.BlockTorus
public import Balaban.Green.BallSums
public import Balaban.Green.BlockDistance
public import Balaban.LargeField.LF1.BlockArith
import Mathlib.Tactic.Linarith

/-!
# Collars of bad blocks and the closure graph (KF0-LINK, "closure definition")

Source: `notes/phase1/KF0-LINK.md` §1, paragraphs "PROVED (closure definition)" and "PROVED
(termination and compatibility)".

Setting: the torus of side `ℓ = s * m`, the `s`-blocks indexed by the torus `Torus d m`
(`Balaban.blockMap s m`), and the `ℓ¹` distance `Green.torusDist`.  A radius function
`R : Torus d m → ℕ` on blocks is an arbitrary argument; it is fixed in advance and never changes
when collars merge.

* `kf0Collar ℓ s m R Q` : the set of `s`-blocks that meet the site neighbourhood of radius `R Q`
  of the block `Q`.  It contains `Q`, is connected in the sense of the landed block polymers
  (`Polymer.IsAnimal (Polymer.blockGraph d m)`: nonempty and connected for the nearest-neighbour
  graph of blocks) and has at most `(2 ⌈R Q / s⌉ + 1) ^ d` blocks.
* `BlockNear X Y` : the block sets `X`, `Y` meet or touch (share a block, or contain two blocks
  adjacent in `Polymer.blockGraph d m`).
* `kf0Closure` : the graph on a bad set `B`, `Q ~ Q'` iff `kf0Collar Q` and `kf0Collar Q'` are
  near.  `kf0Components` is the set of its connected components (as a `Finset (Finset _)`) and
  `kf0Support` is the union `S_I` of the collars of a component `I`.

Proved: every bad block lies in exactly one component; the components partition `B`; distinct
supports are disjoint and not near; each support is connected; `⋃ S_I = ⋃ C_Q`;
`∑_I |S_I| ≤ ∑_Q |C_Q|`; the components depend only on `B` and the values of `R` on `B`; the empty
and one-block cases; the locality of the closure; a small instance with two components and with
one.

Combinatorics only.  The integrated collar potential, the linked expansion and the one-scale
theorem are NOT proved here.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Finset

open scoped Classical

set_option linter.unusedSectionVars false

section Defs

variable {d : ℕ} (ℓ s m : ℕ) [NeZero ℓ] [NeZero m]

/-- The collar `C_Q` of the block `Q`: the `s`-blocks `Q'` that contain a site at `ℓ¹` distance at
most `R Q` from a site of `Q`. -/
noncomputable def kf0Collar (R : Torus d m → ℕ) (Q : Torus d m) : Finset (Torus d m) :=
  Finset.univ.filter fun Q' => ∃ x y : Torus d ℓ, blockMap s m x = Q ∧ blockMap s m y = Q' ∧
    Green.torusDist d ℓ x y ≤ (R Q : ℝ)

end Defs

/-- Two sets of blocks meet or touch: they share a block, or contain two blocks adjacent in the
nearest-neighbour graph of blocks. -/
def BlockNear {d m : ℕ} (X Y : Finset (Torus d m)) : Prop :=
  ∃ a ∈ X, ∃ b ∈ Y, a = b ∨ (Polymer.blockGraph d m).Adj a b

/-- The step relation of a block set `X`: adjacent blocks of `X`. -/
def BlockRel {d m : ℕ} (X : Finset (Torus d m)) (a b : Torus d m) : Prop :=
  a ∈ X ∧ b ∈ X ∧ (Polymer.blockGraph d m).Adj a b

/-- Every two blocks of `X` are joined by a chain of adjacent blocks inside `X`. -/
def ChainConn {d m : ℕ} (X : Finset (Torus d m)) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, Relation.ReflTransGen (BlockRel X) a b

section Defs2

variable {d : ℕ} (ℓ s m : ℕ) [NeZero ℓ] [NeZero m]

/-- The closure graph on the bad set `B`: `Q ~ Q'` iff both lie in `B` and their collars meet or
touch. -/
def kf0Closure (R : Torus d m → ℕ) (B : Finset (Torus d m)) (Q Q' : Torus d m) : Prop :=
  Q ∈ B ∧ Q' ∈ B ∧ BlockNear (kf0Collar ℓ s m R Q) (kf0Collar ℓ s m R Q')

/-- The component of the bad block `Q` in the closure graph. -/
noncomputable def kf0Component (R : Torus d m → ℕ) (B : Finset (Torus d m)) (Q : Torus d m) :
    Finset (Torus d m) :=
  B.filter fun Q' => Relation.ReflTransGen (kf0Closure ℓ s m R B) Q Q'

/-- The dressed components of the bad set `B`: the connected components of the closure graph. -/
noncomputable def kf0Components (R : Torus d m → ℕ) (B : Finset (Torus d m)) :
    Finset (Finset (Torus d m)) :=
  B.image (kf0Component ℓ s m R B)

/-- The support `S_I = ⋃_{Q ∈ I} C_Q` of a set `I` of bad blocks. -/
noncomputable def kf0Support (R : Torus d m → ℕ) (I : Finset (Torus d m)) :
    Finset (Torus d m) :=
  I.biUnion (kf0Collar ℓ s m R)

end Defs2

/-! ### Connectivity in the landed sense -/

section Conn

variable {d m : ℕ} [NeZero m]

theorem reach_of_chain {X : Finset (Torus d m)} {a b : Torus d m} (haX : a ∈ X)
    (h : Relation.ReflTransGen (BlockRel X) a b) (hb : b ∈ X) :
    ((Polymer.blockGraph d m).induce (X : Set (Torus d m))).Reachable ⟨a, haX⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hs ih => exact (ih hs.1).trans (SimpleGraph.Adj.reachable hs.2.2)

/-- A nonempty set of blocks any two of which are joined by a chain of adjacent blocks inside it
is a landed block polymer. -/
theorem isAnimal_of_chainConn {X : Finset (Torus d m)} (hne : X.Nonempty) (h : ChainConn X) :
    Polymer.IsAnimal (Polymer.blockGraph d m) X := by
  refine ⟨hne, ?_⟩
  obtain ⟨a, ha⟩ := hne
  have : Nonempty (X : Set (Torus d m)) := ⟨⟨a, ha⟩⟩
  refine SimpleGraph.Connected.mk (fun u v => ?_)
  exact reach_of_chain u.2 (h u.1 u.2 v.1 v.2) v.2

theorem BlockRel.mono {X Y : Finset (Torus d m)} (h : X ⊆ Y) {a b : Torus d m}
    (hab : BlockRel X a b) : BlockRel Y a b := ⟨h hab.1, h hab.2.1, hab.2.2⟩

theorem chain_mono {X Y : Finset (Torus d m)} (h : X ⊆ Y) {a b : Torus d m}
    (hab : Relation.ReflTransGen (BlockRel X) a b) :
    Relation.ReflTransGen (BlockRel Y) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hs.mono h)

theorem chain_symm {X : Finset (Torus d m)} {a b : Torus d m}
    (hab : Relation.ReflTransGen (BlockRel X) a b) :
    Relation.ReflTransGen (BlockRel X) b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    exact Relation.ReflTransGen.head ⟨hs.2.1, hs.1, hs.2.2.symm⟩ ih

theorem ChainConn.of_root {X : Finset (Torus d m)} {q : Torus d m}
    (h : ∀ b ∈ X, Relation.ReflTransGen (BlockRel X) q b) : ChainConn X := by
  intro a ha b hb
  exact (chain_symm (h a ha)).trans (h b hb)

theorem BlockNear.mono {X X' Y Y' : Finset (Torus d m)} (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : BlockNear X Y) : BlockNear X' Y' := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, hX ha, b, hY hb, hab⟩

theorem BlockNear.symm {X Y : Finset (Torus d m)} (h : BlockNear X Y) : BlockNear Y X := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨b, hb, a, ha, hab.imp Eq.symm SimpleGraph.Adj.symm⟩

theorem blockNear_of_not_disjoint {X Y : Finset (Torus d m)} (h : ¬ Disjoint X Y) :
    BlockNear X Y := by
  obtain ⟨a, ha⟩ := Finset.not_disjoint_iff.1 h
  exact ⟨a, ha.1, a, ha.2, Or.inl rfl⟩

theorem BlockNear.not_disjoint_or {X Y : Finset (Torus d m)} (h : ¬ BlockNear X Y) :
    Disjoint X Y :=
  Finset.disjoint_left.2 fun a ha hb => h ⟨a, ha, a, hb, Or.inl rfl⟩

end Conn

/-! ### The union of near connected sets along a chain -/

section Union

variable {d m : ℕ} [NeZero m]

/-- Union of connected sets along a chain of near sets: let `X : ι → Finset` be a family of
chain-connected nonempty sets, all contained in `S`; if `q ∈ X i₀` and `i₀` reaches `i` through
near steps, then every block of `X i` is joined to `q` by a chain inside `S`. -/
theorem chain_along {ι : Type*} (X : ι → Finset (Torus d m)) (S : Finset (Torus d m))
    (rel : ι → ι → Prop) (hrel : ∀ i j, rel i j → BlockNear (X i) (X j))
    (hconn : ∀ i, ChainConn (X i)) {i₀ i : ι} (hi : Relation.ReflTransGen rel i₀ i)
    (hS : ∀ j, Relation.ReflTransGen rel i₀ j → X j ⊆ S) {q : Torus d m} (hq : q ∈ X i₀) :
    ∀ b ∈ X i, Relation.ReflTransGen (BlockRel S) q b := by
  induction hi with
  | refl =>
    intro b hb
    exact chain_mono (hS _ Relation.ReflTransGen.refl) (hconn _ q hq b hb)
  | @tail j k hj hjk ih =>
    intro b hb
    obtain ⟨a, ha, a', ha', haa⟩ := hrel j k hjk
    have h1 := ih a ha
    have hSk : X k ⊆ S := hS k (hj.tail hjk)
    have hSj' : X j ⊆ S := hS j hj
    have h2 : Relation.ReflTransGen (BlockRel S) a a' := by
      rcases haa with rfl | hadj
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨hSj' ha, hSk ha', hadj⟩
    have h3 := chain_mono hSk (hconn k a' ha' b hb)
    exact (h1.trans h2).trans h3

end Union

/-! ### Site arithmetic -/

section Sites

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The `ℓ¹` distance of two sites as a natural number. -/
def siteL1 (x y : Torus d ℓ) : ℕ := ∑ i, (Green.cycRep (x i - y i)).natAbs

theorem torusDist_eq_siteL1 (x y : Torus d ℓ) :
    Green.torusDist d ℓ x y = (siteL1 x y : ℝ) := by
  unfold Green.torusDist siteL1
  push_cast
  rfl

theorem eq_of_siteL1_eq_zero {x y : Torus d ℓ} (h : siteL1 x y = 0) : x = y := by
  funext i
  have h1 : (Green.cycRep (x i - y i)).natAbs = 0 :=
    (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ i)
  have h2 : Green.cycRep (x i - y i) = 0 := Int.natAbs_eq_zero.1 h1
  have h3 := Green.cast_cycRep (x i - y i)
  rw [h2] at h3
  simpa [sub_eq_zero] using h3.symm

theorem siteL1_self (x : Torus d ℓ) : siteL1 x x = 0 := by
  simp [siteL1, Green.natAbs_cycRep_zero]

/-- A coordinate at nonzero cyclic distance can be moved one step closer. -/
theorem exists_step_coord (c : ZMod ℓ) (hc : (Green.cycRep c).natAbs ≠ 0) :
    ∃ σ : ZMod ℓ, (σ = 1 ∨ σ = -1) ∧ (Green.cycRep (c - σ)).natAbs < (Green.cycRep c).natAbs := by
  set k := Green.cycRep c with hk
  have hkc : ((k : ℤ) : ZMod ℓ) = c := Green.cast_cycRep c
  rcases lt_or_gt_of_ne (show k ≠ 0 by omega) with hneg | hpos
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have := Green.natAbs_cycRep_le_of_cast (c - -1) (k + 1) (by push_cast; rw [hkc]; ring)
    omega
  · refine ⟨1, Or.inl rfl, ?_⟩
    have := Green.natAbs_cycRep_le_of_cast (c - 1) (k - 1) (by push_cast; rw [hkc])
    omega

/-- If `x ≠ y` some site next to `y` is strictly closer to `x`. -/
theorem exists_step_site (x y : Torus d ℓ) (h : siteL1 x y ≠ 0) :
    ∃ (i : Fin d) (σ : ZMod ℓ), (σ = 1 ∨ σ = -1) ∧
      siteL1 x (y + Pi.single i σ) < siteL1 x y := by
  have : ∃ i, (Green.cycRep (x i - y i)).natAbs ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h (Finset.sum_eq_zero fun i _ => hall i)
  obtain ⟨i, hi⟩ := this
  obtain ⟨σ, hσ, hlt⟩ := exists_step_coord (x i - y i) hi
  refine ⟨i, σ, hσ, ?_⟩
  unfold siteL1
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.single_eq_same]
      have : x j - (y j + σ) = x j - y j - σ := by ring
      rw [this]; exact hlt.le
    · simp [Pi.single_eq_of_ne hj]
  · simp only [Pi.add_apply, Pi.single_eq_same]
    have : x i - (y i + σ) = x i - y i - σ := by ring
    rw [this]; exact hlt

end Sites

/-! ### Blocks of neighbouring sites -/

section Steps

variable {d ℓ s m : ℕ} [NeZero ℓ] [NeZero m]

/-- A unit step between sites leads to the same or to an adjacent block. -/
theorem blockMap_step (hℓ : ℓ = s * m) (y : Torus d ℓ) (i : Fin d) {σ : ZMod ℓ}
    (hσ : σ = 1 ∨ σ = -1) :
    blockMap s m (y + Pi.single i σ) = blockMap s m y ∨
      (Polymer.blockGraph d m).Adj (blockMap s m y) (blockMap s m (y + Pi.single i σ)) := by
  have hs := pos_left_of_eq hℓ
  have key : ∀ z : Torus d ℓ, blockMap s m (z + Pi.single i 1) = blockMap s m z ∨
      (Polymer.blockGraph d m).Adj (blockMap s m z) (blockMap s m (z + Pi.single i 1)) := by
    intro z
    have h1 := blockMap_add_single_cases hℓ z i (t := 1) hs
    simp only [Nat.cast_one] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · by_cases heq : blockMap s m (z + Pi.single i 1) = blockMap s m z
      · exact Or.inl heq
      · exact Or.inr ⟨fun h => heq h.symm, i, Or.inl h1⟩
  rcases hσ with rfl | rfl
  · exact key y
  · have hy : y + Pi.single i (-1 : ZMod ℓ) + Pi.single i 1 = y := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    rcases key (y + Pi.single i (-1 : ZMod ℓ)) with h | h
    · left; rw [hy] at h; exact h.symm
    · right; rw [hy] at h; exact h.symm

end Steps

/-! ### T1: the collar -/

section Collar

variable {d ℓ s m : ℕ} [NeZero ℓ] [NeZero m]

theorem mem_kf0Collar {R : Torus d m → ℕ} {Q Q' : Torus d m} :
    Q' ∈ kf0Collar ℓ s m R Q ↔ ∃ x y : Torus d ℓ, blockMap s m x = Q ∧ blockMap s m y = Q' ∧
      siteL1 x y ≤ R Q := by
  unfold kf0Collar
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, torusDist_eq_siteL1]
  exact exists_congr fun x => exists_congr fun y => by
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by exact_mod_cast h3⟩

/-- The block `Q` lies in its own collar. -/
theorem self_mem_kf0Collar (hℓ : ℓ = s * m) (R : Torus d m → ℕ) (Q : Torus d m) :
    Q ∈ kf0Collar ℓ s m R Q := by
  obtain ⟨z, hz⟩ := exists_blockMap_eq hℓ (pos_left_of_eq hℓ) Q
  exact mem_kf0Collar.2 ⟨z, z, hz, hz, by simp [siteL1_self]⟩

theorem kf0Collar_nonempty (hℓ : ℓ = s * m) (R : Torus d m → ℕ) (Q : Torus d m) :
    (kf0Collar ℓ s m R Q).Nonempty :=
  ⟨Q, self_mem_kf0Collar hℓ R Q⟩

/-- Along a chain of sites, each step of the chain is a step between adjacent or equal blocks. -/
theorem chain_blocks_aux (hℓ : ℓ = s * m) (x : Torus d ℓ) (R : ℕ) :
    ∀ k : ℕ, ∀ y : Torus d ℓ, siteL1 x y ≤ k → k ≤ R →
      Relation.ReflTransGen
        (BlockRel (Finset.univ.filter fun b : Torus d m =>
          ∃ z : Torus d ℓ, blockMap s m z = b ∧ siteL1 x z ≤ R))
        (blockMap s m x) (blockMap s m y) := by
  intro k
  induction k with
  | zero =>
    intro y hy _
    have : x = y := eq_of_siteL1_eq_zero (Nat.le_zero.1 hy)
    subst this
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    intro y hy hk
    by_cases hle : siteL1 x y ≤ k
    · exact ih y hle (by omega)
    · have hne : siteL1 x y ≠ 0 := by omega
      obtain ⟨i, σ, hσ, hlt⟩ := exists_step_site x y hne
      have hlt' : siteL1 x (y + Pi.single i σ) ≤ k := by omega
      have h1 := ih _ hlt' (by omega)
      rcases blockMap_step (s := s) (m := m) hℓ y i hσ with heq | hadj
      · rw [← heq]; exact h1
      · refine h1.tail ⟨?_, ?_, hadj.symm⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨_, rfl, by omega⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨y, rfl, by omega⟩

/-- The collar is connected: every block of the collar of `Q` is joined to `Q` by a chain of
adjacent blocks inside the collar. -/
theorem chain_kf0Collar (hℓ : ℓ = s * m) (R : Torus d m → ℕ) (Q : Torus d m) :
    ∀ b ∈ kf0Collar ℓ s m R Q, Relation.ReflTransGen (BlockRel (kf0Collar ℓ s m R Q)) Q b := by
  intro b hb
  obtain ⟨x, y, hx, hy, hxy⟩ := mem_kf0Collar.1 hb
  subst hx; subst hy
  have h := chain_blocks_aux (s := s) (m := m) hℓ x (R (blockMap s m x)) _ y le_rfl hxy
  refine chain_mono ?_ h
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  obtain ⟨z, hz, hzx⟩ := hb
  exact mem_kf0Collar.2 ⟨x, z, rfl, hz, hzx⟩

theorem chainConn_kf0Collar (hℓ : ℓ = s * m) (R : Torus d m → ℕ) (Q : Torus d m) :
    ChainConn (kf0Collar ℓ s m R Q) :=
  ChainConn.of_root (chain_kf0Collar hℓ R Q)

/-- The collar of a block is a block polymer in the landed sense (nonempty, connected for the
nearest-neighbour graph of blocks). -/
theorem isAnimal_kf0Collar (hℓ : ℓ = s * m) (R : Torus d m → ℕ) (Q : Torus d m) :
    Polymer.IsAnimal (Polymer.blockGraph d m) (kf0Collar ℓ s m R Q) :=
  isAnimal_of_chainConn (kf0Collar_nonempty hℓ R Q) (chainConn_kf0Collar hℓ R Q)

/-! ### T1: cardinality of the collar -/

/-- One coordinate: a displacement of cyclic size at most `R` moves the block coordinate by at
most `⌈R / s⌉`. -/
theorem blockCoord_shift (hℓ : ℓ = s * m) (a b : ZMod ℓ) (R : ℕ)
    (h : (Green.cycRep (b - a)).natAbs ≤ R) :
    ∃ t : ℤ, -(⌈(R : ℝ) / s⌉₊ : ℤ) ≤ t ∧ t ≤ (⌈(R : ℝ) / s⌉₊ : ℤ) ∧
      blockCoord s m b = blockCoord s m a + (t : ZMod m) := by
  have hs := pos_left_of_eq hℓ
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  set k : ℕ := ⌈(R : ℝ) / s⌉₊ with hk
  have hRk : (R : ℤ) ≤ k * s := by
    have h1 : (R : ℝ) / s ≤ k := Nat.le_ceil _
    rw [div_le_iff₀ (by exact_mod_cast hs)] at h1
    exact_mod_cast h1
  set δ : ℤ := Green.cycRep (b - a) with hδ
  have hδc : ((δ : ℤ) : ZMod ℓ) = b - a := Green.cast_cycRep _
  have hδR : -(R : ℤ) ≤ δ ∧ δ ≤ R := ⟨by omega, by omega⟩
  have hdvd : (ℓ : ℤ) ∣ (b.val : ℤ) - ((a.val : ℤ) + δ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hδc, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  obtain ⟨j, hj⟩ := hdvd
  have hbv : (b.val : ℤ) = ((a.val : ℤ) + δ) + (s : ℤ) * ((m : ℤ) * j) := by
    have : (ℓ : ℤ) = s * m := by exact_mod_cast hℓ
    rw [this] at hj
    linarith
  have hdiv : ((b.val / s : ℕ) : ℤ) = ((a.val : ℤ) + δ) / s + (m : ℤ) * j := by
    rw [Int.natCast_div, hbv, Int.add_mul_ediv_left _ _ hsz.ne']
  set A : ℤ := (a.val : ℤ) with hA
  have hAdecomp : A = s * (A / s) + A % s := (Int.mul_ediv_add_emod A s).symm
  have hr0 : 0 ≤ A % s := Int.emod_nonneg _ hsz.ne'
  have hr1 : A % s < s := Int.emod_lt_of_pos _ hsz
  have hsplit : (A + δ) / s = A / s + (A % s + δ) / s := by
    have : A + δ = (A % s + δ) + s * (A / s) := by linarith
    rw [this, Int.add_mul_ediv_left _ _ hsz.ne']; ring
  refine ⟨(A % s + δ) / s, ?_, ?_, ?_⟩
  · rw [Int.le_ediv_iff_mul_le hsz]; nlinarith
  · have : (A % s + δ) / s < k + 1 := by
      rw [Int.ediv_lt_iff_lt_mul hsz]; nlinarith
    omega
  · unfold blockCoord
    have e1 : (((b.val / s : ℕ) : ℤ) : ZMod m) = ((b.val / s : ℕ) : ZMod m) :=
      Int.cast_natCast _
    have e2 : (((a.val / s : ℕ) : ℤ) : ZMod m) = ((a.val / s : ℕ) : ZMod m) :=
      Int.cast_natCast _
    rw [← e1, ← e2, hdiv, Int.natCast_div, hsplit]
    push_cast
    simp [hA]

/-- The cardinality bound: `|C_Q| ≤ (2 ⌈R_Q / s⌉ + 1) ^ d` (hence `≤ (2 ⌈R_Q / s⌉ + 3) ^ d`). -/
theorem card_kf0Collar_le (hℓ : ℓ = s * m) (R : Torus d m → ℕ) (Q : Torus d m) :
    (kf0Collar ℓ s m R Q).card ≤ (2 * ⌈(R Q : ℝ) / s⌉₊ + 1) ^ d := by
  set k : ℕ := ⌈(R Q : ℝ) / s⌉₊ with hk
  let T : ZMod m → Finset (ZMod m) := fun q =>
    (Finset.Icc (-(k : ℤ)) k).image fun t : ℤ => q + (t : ZMod m)
  have hT : ∀ q, (T q).card ≤ 2 * k + 1 := by
    intro q
    refine Finset.card_image_le.trans ?_
    rw [Int.card_Icc]; omega
  have hsub : kf0Collar ℓ s m R Q ⊆ Fintype.piFinset fun i : Fin d => T (Q i) := by
    intro Q' hQ'
    obtain ⟨x, y, hx, hy, hxy⟩ := mem_kf0Collar.1 hQ'
    rw [Fintype.mem_piFinset]
    intro i
    have h1 : (Green.cycRep (x i - y i)).natAbs ≤ siteL1 x y :=
      Finset.single_le_sum (f := fun i => (Green.cycRep (x i - y i)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (Green.cycRep (y i - x i)).natAbs ≤ R Q := by
      rw [← neg_sub, Green.natAbs_cycRep_neg]; exact h1.trans hxy
    obtain ⟨t, ht1, ht2, ht3⟩ := blockCoord_shift hℓ (x i) (y i) (R Q) h2
    refine Finset.mem_image.2 ⟨t, Finset.mem_Icc.2 ⟨ht1, ht2⟩, ?_⟩
    have : Q' i = blockMap s m y i := by rw [← hy]
    have h3 : Q i = blockMap s m x i := by rw [← hx]
    rw [this, h3]
    simp only [blockMap_apply]
    exact ht3.symm
  calc (kf0Collar ℓ s m R Q).card ≤ (Fintype.piFinset fun i : Fin d => T (Q i)).card :=
        Finset.card_le_card hsub
    _ = ∏ i : Fin d, (T (Q i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * k + 1) := Finset.prod_le_prod fun i _ => hT _
    _ = (2 * k + 1) ^ d := by simp

end Collar

/-! ### T2: the closure graph and its components -/

section Closure

variable {d ℓ s m : ℕ} [NeZero ℓ] [NeZero m] (R : Torus d m → ℕ) (B : Finset (Torus d m))

theorem kf0Closure_symm {Q Q' : Torus d m} (h : kf0Closure ℓ s m R B Q Q') :
    kf0Closure ℓ s m R B Q' Q := ⟨h.2.1, h.1, h.2.2.symm⟩

theorem closure_chain_symm {Q Q' : Torus d m}
    (h : Relation.ReflTransGen (kf0Closure ℓ s m R B) Q Q') :
    Relation.ReflTransGen (kf0Closure ℓ s m R B) Q' Q := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head (kf0Closure_symm R B hs) ih

theorem mem_kf0Component {Q Q' : Torus d m} :
    Q' ∈ kf0Component ℓ s m R B Q ↔
      Q' ∈ B ∧ Relation.ReflTransGen (kf0Closure ℓ s m R B) Q Q' := by
  simp [kf0Component]

variable {R B}

theorem self_mem_kf0Component {Q : Torus d m} (hQ : Q ∈ B) :
    Q ∈ kf0Component ℓ s m R B Q :=
  (mem_kf0Component R B).2 ⟨hQ, Relation.ReflTransGen.refl⟩

theorem kf0Component_eq_of_mem {Q Q' : Torus d m} (h : Q' ∈ kf0Component ℓ s m R B Q) :
    kf0Component ℓ s m R B Q' = kf0Component ℓ s m R B Q := by
  obtain ⟨hQ'B, hQQ'⟩ := (mem_kf0Component R B).1 h
  ext Q''
  rw [mem_kf0Component, mem_kf0Component]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, hQQ'.trans h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (closure_chain_symm R B hQQ').trans h2⟩

theorem mem_kf0Components {I : Finset (Torus d m)} :
    I ∈ kf0Components ℓ s m R B ↔ ∃ Q ∈ B, kf0Component ℓ s m R B Q = I := by
  simp [kf0Components]

theorem kf0Component_subset (Q : Torus d m) : kf0Component ℓ s m R B Q ⊆ B :=
  fun _ h => ((mem_kf0Component R B).1 h).1

theorem subset_of_mem_kf0Components {I : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) : I ⊆ B := by
  obtain ⟨Q, _, rfl⟩ := mem_kf0Components.1 hI
  exact kf0Component_subset Q

theorem nonempty_of_mem_kf0Components {I : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) : I.Nonempty := by
  obtain ⟨Q, hQ, rfl⟩ := mem_kf0Components.1 hI
  exact ⟨Q, self_mem_kf0Component hQ⟩

/-- Every bad block lies in exactly one component. -/
theorem existsUnique_component {Q : Torus d m} (hQ : Q ∈ B) :
    ∃! I, I ∈ kf0Components ℓ s m R B ∧ Q ∈ I := by
  refine ⟨kf0Component ℓ s m R B Q, ⟨mem_kf0Components.2 ⟨Q, hQ, rfl⟩,
    self_mem_kf0Component hQ⟩, ?_⟩
  rintro I ⟨hI, hQI⟩
  obtain ⟨Q0, _, rfl⟩ := mem_kf0Components.1 hI
  exact (kf0Component_eq_of_mem hQI).symm

/-- Distinct components are disjoint. -/
theorem disjoint_of_mem_kf0Components {I I' : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) (hI' : I' ∈ kf0Components ℓ s m R B) (hne : I ≠ I') :
    Disjoint I I' := by
  rw [Finset.disjoint_left]
  intro Q hQ hQ'
  obtain ⟨Q1, _, rfl⟩ := mem_kf0Components.1 hI
  obtain ⟨Q2, _, rfl⟩ := mem_kf0Components.1 hI'
  exact hne ((kf0Component_eq_of_mem hQ).symm.trans (kf0Component_eq_of_mem hQ'))

/-- The components cover the bad set. -/
theorem biUnion_kf0Components : (kf0Components ℓ s m R B).biUnion id = B := by
  ext Q
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨I, hI, hQ⟩; exact subset_of_mem_kf0Components hI hQ
  · intro hQ
    exact ⟨_, mem_kf0Components.2 ⟨Q, hQ, rfl⟩, self_mem_kf0Component hQ⟩

/-- Two blocks of `B` whose collars meet or touch lie in the same component. -/
theorem mem_component_of_near {Q Q' : Torus d m} (hQ : Q ∈ B) (hQ' : Q' ∈ B)
    (h : BlockNear (kf0Collar ℓ s m R Q) (kf0Collar ℓ s m R Q')) :
    Q' ∈ kf0Component ℓ s m R B Q :=
  (mem_kf0Component R B).2 ⟨hQ', Relation.ReflTransGen.single ⟨hQ, hQ', h⟩⟩

/-! ### T3: supports -/

theorem mem_kf0Support {I : Finset (Torus d m)} {b : Torus d m} :
    b ∈ kf0Support ℓ s m R I ↔ ∃ Q ∈ I, b ∈ kf0Collar ℓ s m R Q := by
  simp [kf0Support]

/-- The supports of distinct components neither meet nor touch. -/
theorem not_blockNear_support {I I' : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) (hI' : I' ∈ kf0Components ℓ s m R B) (hne : I ≠ I') :
    ¬ BlockNear (kf0Support ℓ s m R I) (kf0Support ℓ s m R I') := by
  rintro ⟨a, ha, b, hb, hab⟩
  obtain ⟨Q, hQI, haQ⟩ := mem_kf0Support.1 ha
  obtain ⟨Q', hQ'I', hbQ'⟩ := mem_kf0Support.1 hb
  have hnear : BlockNear (kf0Collar ℓ s m R Q) (kf0Collar ℓ s m R Q') := ⟨a, haQ, b, hbQ', hab⟩
  have h1 := mem_component_of_near (subset_of_mem_kf0Components hI hQI)
    (subset_of_mem_kf0Components hI' hQ'I') hnear
  obtain ⟨Q0, _, rfl⟩ := mem_kf0Components.1 hI
  obtain ⟨Q1, _, rfl⟩ := mem_kf0Components.1 hI'
  have e1 := kf0Component_eq_of_mem hQI
  have e2 := kf0Component_eq_of_mem hQ'I'
  have e3 := kf0Component_eq_of_mem h1
  exact hne (e1.symm.trans (e3.symm.trans e2))

/-- The supports of distinct components are disjoint. -/
theorem disjoint_support {I I' : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) (hI' : I' ∈ kf0Components ℓ s m R B) (hne : I ≠ I') :
    Disjoint (kf0Support ℓ s m R I) (kf0Support ℓ s m R I') :=
  BlockNear.not_disjoint_or (not_blockNear_support hI hI' hne)

/-- Each support is connected: a landed block polymer. -/
theorem isAnimal_support (hℓ : ℓ = s * m) {I : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) :
    Polymer.IsAnimal (Polymer.blockGraph d m) (kf0Support ℓ s m R I) := by
  obtain ⟨Q0, hQ0, rfl⟩ := mem_kf0Components.1 hI
  set I := kf0Component ℓ s m R B Q0 with hIdef
  have hQ0I : Q0 ∈ I := self_mem_kf0Component hQ0
  have hq : Q0 ∈ kf0Collar ℓ s m R Q0 := self_mem_kf0Collar hℓ R Q0
  have hqS : Q0 ∈ kf0Support ℓ s m R I := mem_kf0Support.2 ⟨Q0, hQ0I, hq⟩
  refine isAnimal_of_chainConn ⟨Q0, hqS⟩ (ChainConn.of_root (q := Q0) fun b hb => ?_)
  obtain ⟨Q, hQI, hbQ⟩ := mem_kf0Support.1 hb
  have hreach : Relation.ReflTransGen (kf0Closure ℓ s m R B) Q0 Q :=
    ((mem_kf0Component R B).1 hQI).2
  refine chain_along (fun Q => kf0Collar ℓ s m R Q) (kf0Support ℓ s m R I)
    (kf0Closure ℓ s m R B) (fun i j h => h.2.2) (chainConn_kf0Collar hℓ R) hreach ?_ hq b hbQ
  intro j hj
  have hjB : j ∈ B := by
    rcases Relation.ReflTransGen.cases_tail hj with rfl | ⟨c, _, hc⟩
    · exact hQ0
    · exact hc.2.1
  have hjI : j ∈ I := (mem_kf0Component R B).2 ⟨hjB, hj⟩
  intro a ha
  exact mem_kf0Support.2 ⟨j, hjI, ha⟩

/-- The union of the supports is the union of the collars of the bad blocks. -/
theorem biUnion_support :
    (kf0Components ℓ s m R B).biUnion (kf0Support ℓ s m R) = B.biUnion (kf0Collar ℓ s m R) := by
  ext b
  simp only [Finset.mem_biUnion, mem_kf0Support]
  constructor
  · rintro ⟨I, hI, Q, hQ, hb⟩
    exact ⟨Q, subset_of_mem_kf0Components hI hQ, hb⟩
  · rintro ⟨Q, hQ, hb⟩
    exact ⟨_, mem_kf0Components.2 ⟨Q, hQ, rfl⟩, Q, self_mem_kf0Component hQ, hb⟩

/-- Size bound: `∑_I |S_I| ≤ ∑_{Q ∈ B} |C_Q|`. -/
theorem sum_card_support_le :
    ∑ I ∈ kf0Components ℓ s m R B, (kf0Support ℓ s m R I).card ≤
      ∑ Q ∈ B, (kf0Collar ℓ s m R Q).card := by
  rw [← Finset.card_biUnion fun I hI I' hI' hne => disjoint_support hI hI' hne,
    biUnion_support]
  exact Finset.card_biUnion_le

/-! ### T4: determinacy and locality -/

theorem kf0Collar_congr {R R' : Torus d m → ℕ} {Q : Torus d m} (h : R Q = R' Q) :
    kf0Collar ℓ s m R Q = kf0Collar ℓ s m R' Q := by
  ext b
  rw [mem_kf0Collar, mem_kf0Collar, h]

/-- The components depend only on `B` and the values of the radius function on `B`. -/
theorem kf0Components_congr {R R' : Torus d m → ℕ} (h : ∀ Q ∈ B, R Q = R' Q) :
    kf0Components ℓ s m R B = kf0Components ℓ s m R' B := by
  have hrel : kf0Closure ℓ s m R B = kf0Closure ℓ s m R' B := by
    funext Q Q'
    apply propext
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rwa [kf0Collar_congr (h Q h1), kf0Collar_congr (h Q' h2)] at h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rwa [← kf0Collar_congr (h Q h1), ← kf0Collar_congr (h Q' h2)] at h3⟩
  unfold kf0Components
  congr 1
  funext Q
  unfold kf0Component
  rw [hrel]

theorem kf0Support_congr {R R' : Torus d m → ℕ} {I : Finset (Torus d m)}
    (h : ∀ Q ∈ I, R Q = R' Q) : kf0Support ℓ s m R I = kf0Support ℓ s m R' I :=
  Finset.biUnion_congr rfl fun Q hQ => kf0Collar_congr (h Q hQ)

theorem kf0Components_empty : kf0Components ℓ s m R (∅ : Finset (Torus d m)) = ∅ := by
  simp [kf0Components]

theorem kf0Component_singleton (Q : Torus d m) :
    kf0Component ℓ s m R {Q} Q = {Q} := by
  ext Q'
  rw [mem_kf0Component]
  constructor
  · rintro ⟨h1, _⟩; exact h1
  · intro h
    have : Q' = Q := Finset.mem_singleton.1 h
    subst this
    exact ⟨h, Relation.ReflTransGen.refl⟩

/-- For `B = {Q}` the family is `{({Q}, C_Q)}`. -/
theorem kf0Components_singleton (Q : Torus d m) :
    kf0Components ℓ s m R {Q} = {{Q}} := by
  simp [kf0Components, kf0Component_singleton]

theorem kf0Support_singleton (Q : Torus d m) :
    kf0Support ℓ s m R {Q} = kf0Collar ℓ s m R Q := by
  simp [kf0Support]

/-- Locality of the closure.  Let `I` be a component of `(B, R)`, contained in a second bad set
`B'` with a second radius function `R'` that agrees with `R` on `I`.  If no block of `B' \ I` has
its `R'`-collar meeting or touching the support `S_I`, then `I` is also a component of `(B', R')`,
with the same support. -/
theorem component_local {R' : Torus d m → ℕ} {B' I : Finset (Torus d m)}
    (hI : I ∈ kf0Components ℓ s m R B) (hIB' : I ⊆ B') (hR : ∀ Q ∈ I, R Q = R' Q)
    (hfar : ∀ Q' ∈ B' \ I, ¬ BlockNear (kf0Support ℓ s m R I) (kf0Collar ℓ s m R' Q')) :
    I ∈ kf0Components ℓ s m R' B' ∧ kf0Support ℓ s m R' I = kf0Support ℓ s m R I := by
  refine ⟨?_, (kf0Support_congr hR).symm⟩
  obtain ⟨Q0, hQ0, rfl⟩ := mem_kf0Components.1 hI
  set I := kf0Component ℓ s m R B Q0 with hIdef
  have hQ0I : Q0 ∈ I := self_mem_kf0Component hQ0
  refine mem_kf0Components.2 ⟨Q0, hIB' hQ0I, ?_⟩
  ext Q
  rw [mem_kf0Component]
  constructor
  · rintro ⟨hQB', hQ⟩
    have : ∀ c, Relation.ReflTransGen (kf0Closure ℓ s m R' B') Q0 c → c ∈ I := by
      intro c hc
      induction hc with
      | refl => exact hQ0I
      | @tail b c _ hbc ih =>
        by_contra hcI
        refine hfar c (Finset.mem_sdiff.2 ⟨hbc.2.1, hcI⟩) ?_
        obtain ⟨a, ha, a', ha', haa⟩ := hbc.2.2
        refine ⟨a, ?_, a', ha', haa⟩
        rw [← kf0Collar_congr (hR b ih)] at ha
        exact mem_kf0Support.2 ⟨b, ih, ha⟩
    exact this Q hQ
  · intro hQI
    have hreach := ((mem_kf0Component R B).1 hQI).2
    refine ⟨hIB' hQI, ?_⟩
    have : ∀ c, Relation.ReflTransGen (kf0Closure ℓ s m R B) Q0 c →
        c ∈ I ∧ Relation.ReflTransGen (kf0Closure ℓ s m R' B') Q0 c := by
      intro c hc
      induction hc with
      | refl => exact ⟨hQ0I, Relation.ReflTransGen.refl⟩
      | @tail b c hb hbc ih =>
        have hcI : c ∈ I :=
          (mem_kf0Component R B).2 ⟨hbc.2.1, hb.trans (Relation.ReflTransGen.single hbc)⟩
        refine ⟨hcI, ih.2.tail ⟨hIB' ih.1, hIB' hcI, ?_⟩⟩
        have h3 := hbc.2.2
        rwa [kf0Collar_congr (hR b ih.1), kf0Collar_congr (hR c hcI)] at h3
    exact (this Q hreach).2

end Closure

/-! ### T6: a small instance -/

section Instance

/-- With radius `0` the collar of a block is the block itself. -/
theorem kf0Collar_zero {d ℓ s m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = s * m) (Q : Torus d m) :
    kf0Collar ℓ s m (fun _ => 0) Q = {Q} := by
  ext Q'
  rw [Finset.mem_singleton]
  constructor
  · intro h
    obtain ⟨x, y, hx, hy, hxy⟩ := mem_kf0Collar.1 h
    have := eq_of_siteL1_eq_zero (Nat.le_zero.1 hxy)
    subst this
    exact hy.symm.trans hx
  · rintro rfl
    exact self_mem_kf0Collar hℓ _ _

theorem blockMap_one_self {d m : ℕ} [NeZero m] (x : Torus d m) : blockMap (ℓ := m) 1 m x = x := by
  funext i
  simp [blockMap, blockCoord]

/-- The two bad blocks `0` and `5` on the block torus `ℤ/10ℤ` (`d = 1`, `s = 1`). -/
def instB : Finset (Torus 1 10) := {0, 5}

theorem mem_instB (Q : Torus 1 10) : Q ∈ instB ↔ Q = 0 ∨ Q = 5 := by
  simp [instB]

theorem inst_not_near : ¬ BlockNear ({0} : Finset (Torus 1 10)) {5} := by
  rintro ⟨a, ha, b, hb, h⟩
  rw [Finset.mem_singleton] at ha hb
  subst ha; subst hb
  rcases h with h | ⟨_, μ, hμ | hμ⟩
  · have := congrFun h 0
    revert this
    decide
  · obtain rfl : μ = 0 := Subsingleton.elim _ _
    have := congrFun hμ 0
    simp only [Pi.add_apply, Pi.single_eq_same] at this
    revert this
    decide
  · obtain rfl : μ = 0 := Subsingleton.elim _ _
    have := congrFun hμ 0
    simp only [Pi.add_apply, Pi.single_eq_same] at this
    revert this
    decide

theorem inst_component_zero :
    kf0Component 10 1 10 (fun _ => 0) instB 0 = {0} := by
  ext Q
  rw [mem_kf0Component, Finset.mem_singleton]
  constructor
  · rintro ⟨hQ, h⟩
    have key : ∀ c, Relation.ReflTransGen (kf0Closure 10 1 10 (fun _ => 0) instB) 0 c → c = 0 := by
      intro c hc
      induction hc with
      | refl => rfl
      | @tail b c _ hbc ih =>
        subst ih
        obtain ⟨_, hcB, hn⟩ := hbc
        rw [kf0Collar_zero (by norm_num), kf0Collar_zero (by norm_num)] at hn
        rw [mem_instB] at hcB
        rcases hcB with rfl | rfl
        · rfl
        · exact absurd hn inst_not_near
    exact key Q h
  · rintro rfl
    exact ⟨by simp [instB], Relation.ReflTransGen.refl⟩

theorem inst_component_five :
    kf0Component 10 1 10 (fun _ => 0) instB 5 = {5} := by
  ext Q
  rw [mem_kf0Component, Finset.mem_singleton]
  constructor
  · rintro ⟨hQ, h⟩
    have key : ∀ c, Relation.ReflTransGen (kf0Closure 10 1 10 (fun _ => 0) instB) 5 c → c = 5 := by
      intro c hc
      induction hc with
      | refl => rfl
      | @tail b c _ hbc ih =>
        subst ih
        obtain ⟨_, hcB, hn⟩ := hbc
        rw [kf0Collar_zero (by norm_num), kf0Collar_zero (by norm_num)] at hn
        rw [mem_instB] at hcB
        rcases hcB with rfl | rfl
        · exact absurd hn.symm inst_not_near
        · rfl
    exact key Q h
  · rintro rfl
    exact ⟨by simp [instB], Relation.ReflTransGen.refl⟩

/-- Radius `0`: the two bad blocks form two components. -/
theorem inst_two_components :
    kf0Components 10 1 10 (fun _ => 0) instB = {{0}, {5}} := by
  ext I
  rw [mem_kf0Components]
  simp only [mem_instB, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨Q, rfl | rfl, rfl⟩
    · rw [inst_component_zero]; simp
    · rw [inst_component_five]; simp
  · rintro (rfl | rfl)
    · exact ⟨0, Or.inl rfl, inst_component_zero⟩
    · exact ⟨5, Or.inr rfl, inst_component_five⟩

theorem inst_two_components_card :
    (kf0Components 10 1 10 (fun _ => 0) instB).card = 2 := by
  rw [inst_two_components]
  have : ({0} : Finset (Torus 1 10)) ≠ {5} := by
    intro h
    have := Finset.singleton_inj.1 h
    revert this
    decide +kernel
  exact Finset.card_pair this

theorem inst_two_supports :
    kf0Support 10 1 10 (fun _ => 0) ({0} : Finset (Torus 1 10)) = {0} ∧
      kf0Support 10 1 10 (fun _ => 0) ({5} : Finset (Torus 1 10)) = {5} := by
  rw [kf0Support_singleton, kf0Support_singleton, kf0Collar_zero (by norm_num),
    kf0Collar_zero (by norm_num)]
  exact ⟨rfl, rfl⟩

theorem inst_near_two : BlockNear (kf0Collar 10 1 10 (fun _ => 3) 0)
    (kf0Collar 10 1 10 (fun _ => 3) (5 : Torus 1 10)) := by
  have h0 : (2 : Torus 1 10) ∈ kf0Collar 10 1 10 (fun _ => 3) 0 := by
    refine mem_kf0Collar.2 ⟨0, 2, blockMap_one_self _, blockMap_one_self _, ?_⟩
    decide +kernel
  have h5 : (2 : Torus 1 10) ∈ kf0Collar 10 1 10 (fun _ => 3) 5 := by
    refine mem_kf0Collar.2 ⟨5, 2, blockMap_one_self _, blockMap_one_self _, ?_⟩
    decide +kernel
  exact ⟨2, h0, 2, h5, Or.inl rfl⟩

/-- Radius `3`: the same two bad blocks merge into a single component. -/
theorem inst_one_component :
    kf0Components 10 1 10 (fun _ => 3) instB = {instB} := by
  have h5 : (5 : Torus 1 10) ∈ kf0Component 10 1 10 (fun _ => 3) instB 0 :=
    mem_component_of_near (by simp [instB]) (by simp [instB]) inst_near_two
  have hc : kf0Component 10 1 10 (fun _ => 3) instB 0 = instB := by
    ext Q
    constructor
    · intro h; exact kf0Component_subset _ h
    · intro h
      rw [mem_instB] at h
      rcases h with rfl | rfl
      · exact self_mem_kf0Component (by simp [instB])
      · exact h5
  ext I
  rw [mem_kf0Components, Finset.mem_singleton]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact (kf0Component_eq_of_mem (Q := 0) (Q' := Q) (by rw [hc]; exact hQ)).trans hc
  · rintro rfl
    exact ⟨0, by simp [instB], hc⟩

theorem inst_one_component_card :
    (kf0Components 10 1 10 (fun _ => 3) instB).card = 1 := by
  rw [inst_one_component]; simp

theorem inst_one_support :
    kf0Support 10 1 10 (fun _ => 3) instB =
      kf0Collar 10 1 10 (fun _ => 3) 0 ∪ kf0Collar 10 1 10 (fun _ => 3) 5 := by
  simp [kf0Support, instB]

end Instance

end Balaban.LargeField
