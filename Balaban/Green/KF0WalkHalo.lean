/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkOrdinary
public import Balaban.Green.KF0WalkTorus
public import Balaban.Lattice.Blocks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0WalkHalo`: walk-indexed terms, their halo, and the block count (F.10)

Part of Theorem F.1 of `notes/phase1/LF-BASE-KF0.md`.  The landed file `KF0WalkOrdinary` indexes the
terms of the expansion of a monomial in `u = β^{-1/2} C ψ` by (length, endpoint).  Here the index is
refined to the step sequences themselves.

* `KF0Walk d`: a walk, `⟨n, w⟩` with `w : Fin n → Fin d × Bool` (the steps `±e_μ`).
* `kf0WalkTerm`: `∏_i β^{-1/2} w_{n_i} ℓ_i(ψ(x_i + Σ steps))`; the sum over the walks with given
  lengths and endpoints is the landed `kf0Term` (`kf0Term_eq_sum_walks`); the sum over all
  tuples of walks is the monomial (`kf0WalkTerm_hasSum`), absolutely convergent, with
  `∑ e^{γ n_tot} sup |term| ≤ (p A_γ / √β)^r` (`kf0WalkBound_summable`).
* `walkHalo x ω`: the finite set of sites visited by the walks `ω i` started at `x i`, together
  with `U = {x i}`.  It is connected for the nearest-neighbour adjacency of the torus
  (`walkHalo_nnConnected`; `NNConnected` is the third clause of the frozen `IsPolymer`) when any
  two sites of `U` are equal or adjacent (a single site or a bond), and the term depends on `ψ`
  only on it (`kf0WalkTerm_congr`).
* Block count: for the block map `blockMap s m'` of the torus of side `m = s m'`, the number
  `k_s(H)` of `s`-blocks meeting the halo satisfies
  `k_s(H) ≤ 3^d (r + n_tot / s)` (`kf0BlockCount_walkHalo_le_real`), hence (F.10)
  `k_s(H) ≤ 2 + 3^d r + (8·3^d/s) n_tot`.
* Weighted bound: `∑_ω e^{κ k_s(H)} sup |term| ≤ (e^{κ 3^d} p A_γ/√β)^r` when `γ ≥ κ 3^d/s`
  (`kf0WalkTerm_weighted_summable`), and the power-series form.

NOT proved here: the regrouping of the terms with the same halo into `F_H`, the concrete
functions (F.11)–(F.13) and their Taylor majorants (F.12), the heavy sector, and the one-scale
theorem.
-/

@[expose] public section

namespace Balaban.Green

open Finset Matrix Filter Topology Balaban.LargeField

variable {d m : ℕ}

/-! ### Walks and their paths -/

/-- A walk in `ℤ^d`: a length `n` and `n` steps `±e_μ`. -/
abbrev KF0Walk (d : ℕ) : Type := Σ n : ℕ, (Fin n → Fin d × Bool)

/-- The `i`-th step of `w`, as a vector in `ℤ^d`; zero for `i ≥ n`. -/
def walkStep (d : ℕ) {n : ℕ} (w : Fin n → Fin d × Bool) (i : ℕ) : Fin d → ℤ :=
  if h : i < n then stepVec d (w ⟨i, h⟩) else 0

/-- The position after `k` steps of the walk `w` started at `x`. -/
def pathPt (x : Torus d m) (w : KF0Walk d) (k : ℕ) : Torus d m :=
  x + intToTorus d m (∑ i ∈ range k, walkStep d w.2 i)

/-- The endpoint of the walk `w` started at `x`. -/
def walkEnd (x : Torus d m) (w : KF0Walk d) : Torus d m := x + intToTorus d m (stepSum w.2)

theorem pathPt_zero (x : Torus d m) (w : KF0Walk d) : pathPt x w 0 = x := by
  simp [pathPt]

theorem pathPt_length (x : Torus d m) (w : KF0Walk d) : pathPt x w w.1 = walkEnd x w := by
  unfold pathPt walkEnd stepSum
  congr 2
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [walkStep]

theorem abs_walkStep_le {n : ℕ} (w : Fin n → Fin d × Bool) (i : ℕ) (μ : Fin d) :
    |walkStep d w i μ| ≤ 1 := by
  unfold walkStep
  split_ifs
  · exact abs_stepVec_le _ _
  · simp

theorem abs_sum_walkStep_le {n : ℕ} (w : Fin n → Fin d × Bool) (a b : ℕ) (μ : Fin d) :
    |(∑ i ∈ Ico a b, walkStep d w i) μ| ≤ ((b - a : ℕ) : ℤ) := by
  rw [Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Ico a b, |walkStep d w i μ| ≤ ∑ _i ∈ Ico a b, (1 : ℤ) :=
        Finset.sum_le_sum fun i _ => abs_walkStep_le w i μ
    _ = ((b - a : ℕ) : ℤ) := by simp

theorem intToTorus_stepVec (s : Fin d × Bool) :
    ∃ μ : Fin d, intToTorus d m (stepVec d s) = Pi.single μ 1 ∨
      intToTorus d m (stepVec d s) = -Pi.single μ 1 := by
  refine ⟨s.1, ?_⟩
  by_cases h : s.2
  · left
    ext ν; by_cases h' : ν = s.1 <;> simp [stepVec, intToTorus_apply, h, h']
  · right
    ext ν; by_cases h' : ν = s.1 <;> simp [stepVec, intToTorus_apply, h, h']

/-- The nearest-neighbour adjacency of the torus, as in the frozen `IsPolymer`, inside `X`. -/
def NNAdjIn (X : Finset (Torus d m)) (a b : Torus d m) : Prop :=
  a ∈ X ∧ b ∈ X ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1

/-- `X` is connected for the nearest-neighbour adjacency of the torus (the third clause of the
frozen `Balaban.IsPolymer`). -/
def NNConnected (X : Finset (Torus d m)) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, Relation.ReflTransGen (NNAdjIn X) a b

theorem pathPt_succ_adj (x : Torus d m) (w : KF0Walk d) {k : ℕ} (hk : k < w.1) :
    ∃ μ : Fin d, pathPt x w (k + 1) = pathPt x w k + Pi.single μ 1 ∨
      pathPt x w k = pathPt x w (k + 1) + Pi.single μ 1 := by
  obtain ⟨μ, h⟩ := intToTorus_stepVec (d := d) (m := m) (w.2 ⟨k, hk⟩)
  have e : pathPt x w (k + 1) = pathPt x w k + intToTorus d m (stepVec d (w.2 ⟨k, hk⟩)) := by
    unfold pathPt
    rw [Finset.sum_range_succ, map_add, add_assoc]
    simp [walkStep, hk]
  refine ⟨μ, ?_⟩
  rcases h with h | h
  · left; rw [e, h]
  · right; rw [e, h]; abel

/-! ### The halo -/

/-- The sites visited by the walk `w` started at `x`. -/
def walkSites (x : Torus d m) (w : KF0Walk d) : Finset (Torus d m) :=
  (range (w.1 + 1)).image (pathPt x w)

/-- The halo of the tuple of walks `ω i` started at `x i`: the sites visited by the walks together
with the anchor `U = {x i}`. -/
def walkHalo {ι : Type} [Fintype ι] (x : ι → Torus d m) (ω : ι → KF0Walk d) : Finset (Torus d m) :=
  univ.image x ∪ univ.biUnion fun i => walkSites (x i) (ω i)

theorem mem_walkSites {x a : Torus d m} {w : KF0Walk d} :
    a ∈ walkSites x w ↔ ∃ k ≤ w.1, pathPt x w k = a := by
  simp only [walkSites, mem_image, mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩

variable {ι : Type} [Fintype ι]

theorem mem_walkHalo {x : ι → Torus d m} {ω : ι → KF0Walk d} {a : Torus d m} :
    a ∈ walkHalo x ω ↔ ∃ i, ∃ k ≤ (ω i).1, pathPt (x i) (ω i) k = a := by
  simp only [walkHalo, mem_union, mem_image, mem_univ, true_and, mem_biUnion, mem_walkSites]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, k, hk, h⟩)
    · exact ⟨i, 0, Nat.zero_le _, pathPt_zero _ _⟩
    · exact ⟨i, k, hk, h⟩
  · rintro ⟨i, k, hk, h⟩; exact Or.inr ⟨i, k, hk, h⟩

theorem pathPt_mem_walkHalo (x : ι → Torus d m) (ω : ι → KF0Walk d) (i : ι) {k : ℕ}
    (hk : k ≤ (ω i).1) : pathPt (x i) (ω i) k ∈ walkHalo x ω :=
  mem_walkHalo.2 ⟨i, k, hk, rfl⟩

theorem anchor_mem_walkHalo (x : ι → Torus d m) (ω : ι → KF0Walk d) (i : ι) :
    x i ∈ walkHalo x ω := by
  simpa [pathPt_zero] using pathPt_mem_walkHalo x ω i (Nat.zero_le (ω i).1)

theorem walkEnd_mem_walkHalo (x : ι → Torus d m) (ω : ι → KF0Walk d) (i : ι) :
    walkEnd (x i) (ω i) ∈ walkHalo x ω := by
  simpa [pathPt_length] using pathPt_mem_walkHalo x ω i (le_refl (ω i).1)

theorem nnAdjIn_symm (X : Finset (Torus d m)) {a b : Torus d m} (h : NNAdjIn X a b) :
    NNAdjIn X b a := by
  obtain ⟨ha, hb, μ, h⟩ := h
  exact ⟨hb, ha, μ, h.symm⟩

theorem reflTransGen_walk (x : ι → Torus d m) (ω : ι → KF0Walk d) (i : ι) :
    ∀ k ≤ (ω i).1, Relation.ReflTransGen (NNAdjIn (walkHalo x ω)) (x i) (pathPt (x i) (ω i) k) := by
  intro k
  induction k with
  | zero => intro _; rw [pathPt_zero]
  | succ k ih =>
    intro hk
    refine (ih (by omega)).tail ?_
    obtain ⟨μ, h⟩ := pathPt_succ_adj (x i) (ω i) (k := k) (by omega)
    exact ⟨pathPt_mem_walkHalo x ω i (by omega), pathPt_mem_walkHalo x ω i hk, μ, h⟩

/-- **Connectivity of the halo.**  If any two sites of the anchor `U = {x i}` are equal or
nearest-neighbour adjacent (`U` is a single site or a bond), the halo is connected for the
nearest-neighbour adjacency of the torus. -/
theorem walkHalo_nnConnected (x : ι → Torus d m) (ω : ι → KF0Walk d)
    (hU : ∀ i j, x i = x j ∨ ∃ μ : Fin d, x j = x i + Pi.single μ 1 ∨ x i = x j + Pi.single μ 1) :
    NNConnected (walkHalo x ω) := by
  have key : ∀ i j, Relation.ReflTransGen (NNAdjIn (walkHalo x ω)) (x i) (x j) := by
    intro i j
    rcases hU i j with h | ⟨μ, h⟩
    · rw [h]
    · exact Relation.ReflTransGen.single ⟨anchor_mem_walkHalo x ω i, anchor_mem_walkHalo x ω j,
        μ, h⟩
  have symm : ∀ {a b}, Relation.ReflTransGen (NNAdjIn (walkHalo x ω)) a b →
      Relation.ReflTransGen (NNAdjIn (walkHalo x ω)) b a := fun h =>
    by
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact (Relation.ReflTransGen.single (nnAdjIn_symm _ hbc)).trans ih
  intro a ha b hb
  obtain ⟨i, k, hk, rfl⟩ := mem_walkHalo.1 ha
  obtain ⟨j, l, hl, rfl⟩ := mem_walkHalo.1 hb
  exact ((symm (reflTransGen_walk x ω i k hk)).trans (key i j)).trans (reflTransGen_walk x ω j l hl)

/-! ### Block count -/

section Blocks

/-- The number of `s`-blocks (of the torus of side `m = s m'`) meeting a set of sites. -/
def kf0BlockCount [NeZero m] (s m' : ℕ) [NeZero m'] (H : Finset (Torus d m)) : ℕ :=
  (H.image (Balaban.blockMap (d := d) (ℓ := m) s m')).card

variable {s m' : ℕ}

/-- A step of at most `s` in one coordinate moves the block index by `-1, 0` or `1` (modulo `m'`),
on the torus of side `m = s m'`. -/
theorem blockCoord_add_int [NeZero m] [NeZero m'] (hs : 0 < s) (hm : m = s * m') (a : ZMod m)
    (v : ℤ) (hv : |v| ≤ s) :
    ∃ c : ℤ, -1 ≤ c ∧ c ≤ 1 ∧
      Balaban.blockCoord s m' (a + (v : ZMod m)) = Balaban.blockCoord s m' a + (c : ZMod m') := by
  have hs0 : (s : ℤ) ≠ 0 := by exact_mod_cast hs.ne'
  set A : ℤ := (a.val : ℤ) with hA
  have hat : a + (v : ZMod m) = ((A + v : ℤ) : ZMod m) := by simp [A]
  have hval : ((a + (v : ZMod m)).val : ℤ) = (A + v) % (m : ℤ) := by
    rw [hat, ZMod.val_intCast]
  set j : ℤ := (A + v) / (m : ℤ) with hj
  have h1 : ((a + (v : ZMod m)).val : ℤ) = (A + v) + (-((m' : ℤ) * j)) * s := by
    rw [hval, Int.emod_def, ← hj, hm]; push_cast; ring
  have h2 : (((a + (v : ZMod m)).val / s : ℕ) : ℤ) = (A + v) / s - (m' : ℤ) * j := by
    rw [Int.natCast_div, h1, Int.add_mul_ediv_right _ _ hs0]; ring
  have h3 : (((a.val / s : ℕ) : ℤ)) = A / s := by rw [Int.natCast_div]
  refine ⟨(A + v) / s - A / s, ?_, ?_, ?_⟩
  · have hv' := (abs_le.1 hv).1
    have : (A - s) / s ≤ (A + v) / s := Int.ediv_le_ediv (by exact_mod_cast hs) (by linarith)
    have e : (A - s) / s = A / s - 1 := by
      have := Int.add_mul_ediv_right A (-1) hs0
      rw [show A + (-1) * (s : ℤ) = A - s by ring] at this
      rw [this]; ring
    linarith
  · have hv' := (abs_le.1 hv).2
    have : (A + v) / s ≤ (A + s) / s := Int.ediv_le_ediv (by exact_mod_cast hs) (by linarith)
    have e : (A + s) / s = A / s + 1 := by
      have := Int.add_mul_ediv_right A 1 hs0
      rw [show A + 1 * (s : ℤ) = A + s by ring] at this
      rw [this]
    linarith
  · unfold Balaban.blockCoord
    have e1 : (((a + (v : ZMod m)).val / s : ℕ) : ZMod m') =
        ((((a + (v : ZMod m)).val / s : ℕ) : ℤ) : ZMod m') := (Int.cast_natCast _).symm
    have e2 : (((a.val / s : ℕ) : ZMod m')) = ((((a.val / s : ℕ) : ℤ)) : ZMod m') := (Int.cast_natCast _).symm
    rw [e1, e2, h2, h3]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, sub_zero]
    ring

/-- The `3^d` blocks around `b` (indices differing by `-1, 0, 1` in each coordinate). -/
def blockNbrs [NeZero m'] (b : Torus d m') : Finset (Torus d m') :=
  univ.image fun e : Fin d → Fin 3 => b + fun μ => (((e μ : ℕ) : ZMod m') - 1)

theorem card_blockNbrs_le [NeZero m'] (b : Torus d m') : (blockNbrs b).card ≤ 3 ^ d := by
  refine (card_image_le).trans ?_
  simp

theorem mem_blockNbrs [NeZero m'] {b b' : Torus d m'}
    (h : ∀ μ, ∃ c : ℤ, -1 ≤ c ∧ c ≤ 1 ∧ b' μ = b μ + (c : ZMod m')) : b' ∈ blockNbrs b := by
  choose c hc1 hc2 hc using h
  simp only [blockNbrs, mem_image, mem_univ, true_and]
  refine ⟨fun μ => ⟨(c μ + 1).toNat, by have := hc1 μ; have := hc2 μ; omega⟩, ?_⟩
  funext μ
  simp only [Pi.add_apply]
  rw [hc μ]
  have : (((c μ + 1).toNat : ℕ) : ℤ) = c μ + 1 := Int.toNat_of_nonneg (by have := hc1 μ; omega)
  have h2 : (((c μ + 1).toNat : ℕ) : ZMod m') = ((c μ : ℤ) : ZMod m') + 1 := by
    rw [← Int.cast_natCast, this]; push_cast; rfl
  rw [h2]; ring

/-- A displacement of at most `s` in each coordinate moves a site to a site in a neighbouring block
(the `3^d` blocks around the block of the original site). -/
theorem blockMap_add_mem_blockNbrs [NeZero m] [NeZero m'] (hs : 0 < s) (hm : m = s * m')
    (a : Torus d m) (v : Fin d → ℤ) (hv : ∀ μ, |v μ| ≤ s) :
    Balaban.blockMap s m' (a + intToTorus d m v) ∈ blockNbrs (Balaban.blockMap s m' a) := by
  refine mem_blockNbrs fun μ => ?_
  simpa [Balaban.blockMap, intToTorus_apply] using blockCoord_add_int hs hm (a μ) (v μ) (hv μ)

theorem pathPt_add_disp (x : Torus d m) (w : KF0Walk d) {a k : ℕ} (hak : a ≤ k) :
    pathPt x w k = pathPt x w a + intToTorus d m (∑ i ∈ Ico a k, walkStep d w.2 i) := by
  unfold pathPt
  rw [add_assoc, ← map_add, Finset.sum_range_add_sum_Ico _ hak]

variable [NeZero m] [NeZero m']

/-- The blocks met by one walk: at most `3^d (n/s + 1)`. -/
theorem blockMap_pathPt_mem (hs : 0 < s) (hm : m = s * m') (x : Torus d m) (w : KF0Walk d)
    {k : ℕ} (hk : k ≤ w.1) :
    Balaban.blockMap s m' (pathPt x w k) ∈
      (range (w.1 / s + 1)).biUnion fun j =>
        blockNbrs (Balaban.blockMap s m' (pathPt x w (j * s))) := by
  rw [mem_biUnion]
  refine ⟨k / s, mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right hk)), ?_⟩
  have h1 : k / s * s ≤ k := Nat.div_mul_le_self k s
  have h2 : k - k / s * s ≤ s := by
    have := Nat.mod_lt k hs
    have e : k % s = k - k / s * s := by
      have := Nat.div_add_mod k s
      rw [mul_comm] at this
      omega
    omega
  rw [pathPt_add_disp x w h1]
  refine blockMap_add_mem_blockNbrs hs hm _ _ fun μ => ?_
  refine (abs_sum_walkStep_le w.2 _ _ μ).trans ?_
  exact_mod_cast h2

theorem kf0BlockCount_walkHalo_subset (hs : 0 < s) (hm : m = s * m') (x : ι → Torus d m)
    (ω : ι → KF0Walk d) :
    (walkHalo x ω).image (Balaban.blockMap (d := d) (ℓ := m) s m') ⊆
      univ.biUnion fun i => (range ((ω i).1 / s + 1)).biUnion fun j =>
        blockNbrs (Balaban.blockMap s m' (pathPt (x i) (ω i) (j * s))) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
  obtain ⟨i, k, hk, rfl⟩ := mem_walkHalo.1 ha
  exact mem_biUnion.2 ⟨i, mem_univ _, blockMap_pathPt_mem hs hm _ _ hk⟩

/-- **The block count of the halo.**  The number of `s`-blocks meeting the halo is at most
`∑_i 3^d (⌊n_i / s⌋ + 1)`. -/
theorem kf0BlockCount_walkHalo_le (hs : 0 < s) (hm : m = s * m') (x : ι → Torus d m)
    (ω : ι → KF0Walk d) :
    kf0BlockCount s m' (walkHalo x ω) ≤ ∑ i, ((ω i).1 / s + 1) * 3 ^ d := by
  refine (card_le_card (kf0BlockCount_walkHalo_subset hs hm x ω)).trans ?_
  refine card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ?_)
  refine card_biUnion_le.trans ?_
  calc ∑ j ∈ range ((ω i).1 / s + 1), (blockNbrs
        (Balaban.blockMap s m' (pathPt (x i) (ω i) (j * s)))).card
      ≤ ∑ _j ∈ range ((ω i).1 / s + 1), 3 ^ d :=
        Finset.sum_le_sum fun j _ => card_blockNbrs_le _
    _ = _ := by simp

/-- The block count in real form, linear in the total length:
`k_s(H) ≤ 3^d (r + n_tot / s)`. -/
theorem kf0BlockCount_walkHalo_le_real (hs : 0 < s) (hm : m = s * m') (x : ι → Torus d m)
    (ω : ι → KF0Walk d) :
    (kf0BlockCount s m' (walkHalo x ω) : ℝ) ≤
      3 ^ d * ((Fintype.card ι : ℝ) + (∑ i, ((ω i).1 : ℝ)) / s) := by
  have h := kf0BlockCount_walkHalo_le hs hm x ω
  have h' : (kf0BlockCount s m' (walkHalo x ω) : ℝ) ≤ ∑ i, ((((ω i).1 / s + 1) * 3 ^ d : ℕ) : ℝ) := by
    exact_mod_cast h
  refine h'.trans ?_
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have : ∀ i, ((((ω i).1 / s + 1) * 3 ^ d : ℕ) : ℝ) ≤ 3 ^ d * (1 + ((ω i).1 : ℝ) / s) := by
    intro i
    have h1 : (((ω i).1 / s : ℕ) : ℝ) ≤ ((ω i).1 : ℝ) / s := Nat.cast_div_le
    push_cast
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) d]
  calc _ ≤ ∑ i, (3 ^ d * (1 + ((ω i).1 : ℝ) / s) : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        ← Finset.sum_div, nsmul_eq_mul, mul_one]

/-- **(F.10)** in the form of the note: for an anchor of at most two sites, `r ≥ |U|/2`... the
count `k_s(H) ≤ 2 + 3^d r + (8·3^d/s) n_tot` follows. -/
theorem kf0BlockCount_walkHalo_le_F10 (hs : 0 < s) (hm : m = s * m') (x : ι → Torus d m)
    (ω : ι → KF0Walk d) :
    (kf0BlockCount s m' (walkHalo x ω) : ℝ) ≤
      2 + 3 ^ d * (Fintype.card ι : ℝ) + (8 * 3 ^ d / s) * ∑ i, ((ω i).1 : ℝ) := by
  have h := kf0BlockCount_walkHalo_le_real hs hm x ω
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
  have hn : (0 : ℝ) ≤ ∑ i, ((ω i).1 : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have e : (3 : ℝ) ^ d * ((Fintype.card ι : ℝ) + (∑ i, ((ω i).1 : ℝ)) / s) =
      3 ^ d * (Fintype.card ι : ℝ) + (3 ^ d / s) * ∑ i, ((ω i).1 : ℝ) := by ring
  rw [e] at h
  have : (3 ^ d / s : ℝ) * ∑ i, ((ω i).1 : ℝ) ≤ (8 * 3 ^ d / s) * ∑ i, ((ω i).1 : ℝ) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by nlinarith) hs'.le) hn
  linarith

end Blocks

/-! ### Walk-indexed terms -/

section Terms

variable [NeZero m] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {𝕜 : Type} [RCLike 𝕜]
  {ι : Type} [Fintype ι]

/-- The weight `β^{-1/2} w_n` of one walk of length `n` (no adjacency factor: each walk is
counted once). -/
noncomputable def kf0WalkWt (d : ℕ) (ν β : ℝ) (n : ℕ) : ℝ := (Real.sqrt β)⁻¹ * walkWeight d ν n

theorem kf0WalkWt_nonneg {ν : ℝ} (hν : 0 < ν) (β : ℝ) (n : ℕ) : 0 ≤ kf0WalkWt d ν β n :=
  mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (walkWeight_pos hν n).le

/-- The term of the product expansion of `∏_i ℓ_i(u_{x_i})` indexed by the tuple of walks `ω`:
`∏_i β^{-1/2} w_{n_i} ℓ_i(ψ(endpoint of ω i from x i))`. -/
noncomputable def kf0WalkTerm (d m : ℕ) [NeZero m] (ν β : ℝ) (x : ι → Torus d m)
    (ℓ : ι → W →L[ℝ] 𝕜) (ω : ι → KF0Walk d) (ψ : Torus d m → W) : 𝕜 :=
  ∏ i, ((kf0WalkWt d ν β (ω i).1 : ℝ) : 𝕜) * ℓ i (ψ (walkEnd (x i) (ω i)))

/-- The majorant `∏_i e^{γ n_i} β^{-1/2} w_{n_i} p` of `e^{γ n_tot} ‖kf0WalkTerm‖` on the event
`sup ‖ψ‖ ≤ p`. -/
noncomputable def kf0WalkBound (d : ℕ) (ν β γ p : ℝ) (ω : ι → KF0Walk d) : ℝ :=
  ∏ i, (Real.exp (γ * (ω i).1) * (kf0WalkWt d ν β (ω i).1 * p))

/-- **Dependence on the halo.**  The term depends on `ψ` only on the halo (indeed only at the
endpoints, which lie in the halo). -/
theorem kf0WalkTerm_congr (ν β : ℝ) (x : ι → Torus d m) (ℓ : ι → W →L[ℝ] 𝕜)
    (ω : ι → KF0Walk d) {ψ ψ' : Torus d m → W} (h : ∀ a ∈ walkHalo x ω, ψ a = ψ' a) :
    kf0WalkTerm d m ν β x ℓ ω ψ = kf0WalkTerm d m ν β x ℓ ω ψ' := by
  unfold kf0WalkTerm
  exact Finset.prod_congr rfl fun i _ => by rw [h _ (walkEnd_mem_walkHalo x ω i)]

theorem kf0WalkTerm_congr_end (ν β : ℝ) (x : ι → Torus d m) (ℓ : ι → W →L[ℝ] 𝕜)
    (ω : ι → KF0Walk d) {ψ ψ' : Torus d m → W}
    (h : ∀ i, ψ (walkEnd (x i) (ω i)) = ψ' (walkEnd (x i) (ω i))) :
    kf0WalkTerm d m ν β x ℓ ω ψ = kf0WalkTerm d m ν β x ℓ ω ψ' := by
  unfold kf0WalkTerm
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

/-- One landed coefficient is the sum of the walk weights over the walks of length `n` from `x`
to `y`. -/
theorem kf0WalkCoeff_mul_eq_sum (ν β : ℝ) (n : ℕ) (x y : Torus d m) (z : 𝕜) :
    ((kf0WalkCoeff d m ν β n x y : ℝ) : 𝕜) * z =
      ∑ c : Fin n → Fin d × Bool,
        if walkEnd x ⟨n, c⟩ = y then ((kf0WalkWt d ν β n : ℝ) : 𝕜) * z else 0 := by
  have h : kf0WalkCoeff d m ν β n x y = kf0WalkWt d ν β n *
      ∑ c : Fin n → Fin d × Bool, if walkEnd x ⟨n, c⟩ = y then (1 : ℝ) else 0 := by
    unfold kf0WalkCoeff kf0WalkWt
    rw [kf0Adj_pow_eq_count]
    simp only [walkEnd]
    rw [mul_assoc]
    congr!
  rw [h]
  push_cast
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- **The refinement.**  The landed term `kf0Term` for the data `τ i = (n_i, y_i)` is the sum of
the walk terms over the tuples of walks of lengths `n_i` ending at `y_i`. -/
theorem kf0Term_eq_sum_walks [DecidableEq ι] (ν β : ℝ) (x : ι → Torus d m)
    (ℓ : ι → W →L[ℝ] 𝕜) (τ : ι → ℕ × Torus d m) (ψ : Torus d m → W) :
    kf0Term d m ν β x ℓ τ ψ =
      ∑ w : (∀ i, Fin (τ i).1 → Fin d × Bool),
        if ∀ i, walkEnd (x i) ⟨(τ i).1, w i⟩ = (τ i).2 then
          kf0WalkTerm d m ν β x ℓ (fun i => ⟨(τ i).1, w i⟩) ψ else 0 := by
  unfold kf0Term
  have h1 : ∀ i, ((kf0WalkCoeff d m ν β (τ i).1 (x i) (τ i).2 : ℝ) : 𝕜) * ℓ i (ψ (τ i).2) =
      ∑ c : Fin (τ i).1 → Fin d × Bool,
        if walkEnd (x i) ⟨(τ i).1, c⟩ = (τ i).2 then
          ((kf0WalkWt d ν β (τ i).1 : ℝ) : 𝕜) * ℓ i (ψ (walkEnd (x i) ⟨(τ i).1, c⟩)) else 0 := by
    intro i
    rw [kf0WalkCoeff_mul_eq_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with h
    · rw [h]
    · rfl
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.prod_ite_zero]
  simp only [mem_univ, forall_true_left]
  rfl

/-! ### Weighted sums -/

/-- The weighted sum of the walk weights of one factor: `∑_w e^{γ n} β^{-1/2} w_n p ≤ p A_γ/√β`. -/
theorem kf0_walk_weighted_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p) :
    Summable (fun w : KF0Walk d => Real.exp (γ * w.1) * (kf0WalkWt d ν β w.1 * p)) ∧
      ∑' w : KF0Walk d, Real.exp (γ * w.1) * (kf0WalkWt d ν β w.1 * p) ≤
        p * kf0WalkA d g γ / Real.sqrt β := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  set G : ℕ → ℝ := fun n => Real.exp (γ * n) * (kf0WalkWt d ν β n * p) with hG
  have hGnn : ∀ n, 0 ≤ G n := fun n =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (kf0WalkWt_nonneg (d := d) hν β n) hp0)
  have hcard : ∀ n : ℕ, (Fintype.card (Fin n → Fin d × Bool) : ℝ) = (2 * d : ℝ) ^ n := by
    intro n
    simp [mul_comm]
  have hfib : ∀ n : ℕ, ∑' _c : Fin n → Fin d × Bool, G n = (2 * d : ℝ) ^ n * G n := by
    intro n
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hrow : ∀ n : ℕ, (2 * d : ℝ) ^ n * G n =
      p * (Real.sqrt β)⁻¹ * (Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n)) := by
    intro n; simp only [hG, kf0WalkWt]; ring
  obtain ⟨h1, h2⟩ := kf0_weighted_walk_summable (d := d) (ν := ν) hg hgν hq
  have hS : Summable (fun n : ℕ => (2 * d : ℝ) ^ n * G n) := by
    simp only [hrow]; exact h1.mul_left _
  have hnn : ∀ w : KF0Walk d, 0 ≤ G w.1 := fun w => hGnn _
  have hsum : Summable (fun w : KF0Walk d => G w.1) := by
    refine (summable_sigma_of_nonneg hnn).2 ⟨fun n => Summable.of_finite, ?_⟩
    simpa only [hfib] using hS
  refine ⟨hsum, ?_⟩
  rw [hsum.tsum_sigma' fun n => Summable.of_finite]
  simp only [hfib]
  simp only [hrow]
  rw [tsum_mul_left]
  calc p * (Real.sqrt β)⁻¹ * ∑' n : ℕ, Real.exp (γ * n) * (walkWeight d ν n * (2 * d : ℝ) ^ n)
      ≤ p * (Real.sqrt β)⁻¹ * kf0WalkA d g γ :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hp0 (inv_nonneg.2 (Real.sqrt_nonneg _)))
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- Pointwise bound: `e^{γ n_tot} ‖kf0WalkTerm‖ ≤ kf0WalkBound` on `sup ‖ψ‖ ≤ p`. -/
theorem kf0WalkTerm_weighted_le_basic {ν : ℝ} (hν : 0 < ν) (β γ p : ℝ) (x : ι → Torus d m)
    (ℓ : ι → W →L[ℝ] 𝕜) (hℓ : ∀ i, ‖ℓ i‖ ≤ 1) (ω : ι → KF0Walk d)
    (ψ : Torus d m → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Real.exp (γ * ∑ i, ((ω i).1 : ℝ)) * ‖kf0WalkTerm d m ν β x ℓ ω ψ‖ ≤
      kf0WalkBound d ν β γ p ω := by
  unfold kf0WalkTerm kf0WalkBound
  rw [norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (kf0WalkWt_nonneg (d := d) hν β _)]
  have h1 : ‖ℓ i (ψ (walkEnd (x i) (ω i)))‖ ≤ p :=
    ((ℓ i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hℓ i) (norm_nonneg _)).trans
      (by simpa using hp _))
  have h2 := mul_le_mul_of_nonneg_left h1 (kf0WalkWt_nonneg (d := d) hν β (ω i).1)
  calc Real.exp (γ * (ω i).1) * (kf0WalkWt d ν β (ω i).1 * ‖ℓ i (ψ (walkEnd (x i) (ω i)))‖)
      ≤ Real.exp (γ * (ω i).1) * (kf0WalkWt d ν β (ω i).1 * p) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := rfl

theorem kf0WalkBound_nonneg {ν : ℝ} (hν : 0 < ν) (β γ : ℝ) {p : ℝ} (hp0 : 0 ≤ p)
    (ω : ι → KF0Walk d) : 0 ≤ kf0WalkBound d ν β γ p ω :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (kf0WalkWt_nonneg (d := d) hν β _) hp0)

/-- **Total sup-norm over tuples of walks**: summable, with total at most `(p A_γ/√β)^r`. -/
theorem kf0WalkBound_summable {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p) :
    Summable (kf0WalkBound (ι := ι) d ν β γ p) ∧
      ∑' ω, kf0WalkBound (ι := ι) d ν β γ p ω ≤
        (p * kf0WalkA d g γ / Real.sqrt β) ^ Fintype.card ι := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  obtain ⟨h1, h2⟩ := kf0_walk_weighted_summable (d := d) hg hgν hq β hp0
  let f : ι → KF0Walk d → ℝ := fun _ w => Real.exp (γ * w.1) * (kf0WalkWt d ν β w.1 * p)
  have hnn : ∀ i w, 0 ≤ f i w := fun i w =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (kf0WalkWt_nonneg (d := d) hν β _) hp0)
  have hsum : ∀ i, Summable fun w => ‖f i w‖ := fun i =>
    h1.congr fun w => by simp only [Real.norm_of_nonneg (hnn i w)]; rfl
  obtain ⟨_, h3⟩ := pi_prod_summable_hasSum (𝕜 := ℝ) ι f hsum
  have e : kf0WalkBound (ι := ι) d ν β γ p = fun ω => ∏ i, f i (ω i) := rfl
  rw [e]
  refine ⟨h3.summable, ?_⟩
  rw [h3.tsum_eq]
  calc ∏ i, ∑' w, f i w ≤ ∏ _i : ι, p * kf0WalkA d g γ / Real.sqrt β :=
        Finset.prod_le_prod₀ (fun i _ => tsum_nonneg (hnn i)) fun i _ => h2
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- **One factor.**  Summing the walks of one factor gives `ℓ(u_x)`, `u = β^{-1/2} C ψ`. -/
theorem kf0_walk_factor_hasSum {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p)
    (x : Torus d m) (ℓ : W →L[ℝ] 𝕜) (hℓ : ‖ℓ‖ ≤ 1) (ψ : Torus d m → W)
    (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun w : KF0Walk d => ‖((kf0WalkWt d ν β w.1 : ℝ) : 𝕜) * ℓ (ψ (walkEnd x w))‖) ∧
    HasSum (fun w : KF0Walk d => ((kf0WalkWt d ν β w.1 : ℝ) : 𝕜) * ℓ (ψ (walkEnd x w)))
      (ℓ ((Real.sqrt β)⁻¹ • matAct (kf0C d m ν) ψ x)) := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  set f : KF0Walk d → 𝕜 := fun w => ((kf0WalkWt d ν β w.1 : ℝ) : 𝕜) * ℓ (ψ (walkEnd x w)) with hf
  have hbd : ∀ w, ‖f w‖ ≤ Real.exp (γ * w.1) * (kf0WalkWt d ν β w.1 * p) := by
    intro w
    have h1 : ‖ℓ (ψ (walkEnd x w))‖ ≤ p :=
      (ℓ.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)).trans
        (by simpa using hp _))
    have h2 := mul_le_mul_of_nonneg_left h1 (kf0WalkWt_nonneg (d := d) hν β w.1)
    have h3 : 1 ≤ Real.exp (γ * w.1) := Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
    simp only [hf, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (kf0WalkWt_nonneg (d := d) hν β _)]
    nlinarith [mul_nonneg (kf0WalkWt_nonneg (d := d) hν β w.1) hp0]
  have hsn : Summable (fun w => ‖f w‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd
      (kf0_walk_weighted_summable (d := d) hg hgν hq β hp0).1
  refine ⟨hsn, ?_⟩
  have hsub := ℓ.hasSum (kf0_substitution_hasSum (d := d) (m := m) hν β ψ x)
  have hfib := hsub.prod_fiberwise
    (g := fun n : ℕ => ∑ y : Torus d m, ℓ (kf0WalkCoeff d m ν β n x y • ψ y))
    fun n => hasSum_fintype _
  refine HasSum.sigma_of_hasSum (f := f) hfib (fun n => ?_) hsn.of_norm
  have hy : ∀ y : Torus d m, ℓ (kf0WalkCoeff d m ν β n x y • ψ y) =
      ∑ c : Fin n → Fin d × Bool, if walkEnd x ⟨n, c⟩ = y then
        ((kf0WalkWt d ν β n : ℝ) : 𝕜) * ℓ (ψ y) else 0 := by
    intro y
    rw [map_smul, RCLike.real_smul_eq_coe_mul, kf0WalkCoeff_mul_eq_sum]
  have hsum_eq : ∑ y : Torus d m, ℓ (kf0WalkCoeff d m ν β n x y • ψ y) =
      ∑ c : Fin n → Fin d × Bool, f ⟨n, c⟩ := by
    simp_rw [hy]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hf, Finset.sum_ite_eq]
  rw [hsum_eq]
  exact hasSum_fintype _

end Terms

end Balaban.Green
