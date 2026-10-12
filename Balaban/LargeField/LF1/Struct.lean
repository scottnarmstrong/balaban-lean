/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.Setup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Structure of the block hierarchy (helper for LF-1)

Basic facts on `fib`, `tBlocks`, `lam` (the layers `Λ_n`, `n = 0, …, q`), the coarsening of blocks
(`bavgL_succ`: `Q_{n+1} φ = L^{-d} ∑ Q_n φ`), and the geometry of the cross pairs
(`cross_geometry`: for the separation `ϱ ≥ 2dL`, `b₊ ⊂ Λ_{n+1}` and `b₋ ⊂ Λ_n`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Basic

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem mem_fib {n : ℕ} {y : Blk d L N₀ q n} {x : Site d L N₀ q} :
    x ∈ fib d L N₀ q n y ↔ blkMap d L N₀ q n x = y := by
  simp [fib]

theorem fib_eq_blockFibre (n : ℕ) (y : Blk d L N₀ q n) :
    fib d L N₀ q n y = blockFibre (L ^ n) (N₀ * L ^ (q - n)) y := by
  ext x
  rw [mem_fib, mem_blockFibre]; rfl

omit [NeZero N₀] [NeZero L] in
theorem sideEq {n : ℕ} (hn : n ≤ q) : N₀ * L ^ q = L ^ n * (N₀ * L ^ (q - n)) :=
  side_eq hn

theorem card_fib {n : ℕ} (hn : n ≤ q) (y : Blk d L N₀ q n) :
    (fib d L N₀ q n y).card = (L ^ n) ^ d := by
  rw [fib_eq_blockFibre]
  exact card_blockFibre (sideEq hn) y

theorem fib_nonempty {n : ℕ} (hn : n ≤ q) (y : Blk d L N₀ q n) : (fib d L N₀ q n y).Nonempty := by
  rw [← Finset.card_pos, card_fib hn]
  exact pow_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) _

omit [NeZero N₀] [NeZero L] in
theorem mem_tBlocks {n : ℕ} {S : Finset (Site d L N₀ q)} {y : Blk d L N₀ q n} :
    y ∈ tBlocks d L N₀ q n S ↔ ∃ x ∈ S, blkMap d L N₀ q n x = y := by
  simp [tBlocks]

omit [NeZero N₀] [NeZero L] in
theorem blkMap_mem_tBlocks {n : ℕ} {S : Finset (Site d L N₀ q)} {x : Site d L N₀ q} (hx : x ∈ S) :
    blkMap d L N₀ q n x ∈ tBlocks d L N₀ q n S :=
  mem_tBlocks.2 ⟨x, hx, rfl⟩

/-- The `n`-blocks of a union of `n`-blocks lie inside it. -/
theorem fib_subset_of_mem_tBlocks {n : ℕ} {S : Finset (Site d L N₀ q)}
    (hS : IsBlockUnion L N₀ q n S) {y : Blk d L N₀ q n} (hy : y ∈ tBlocks d L N₀ q n S) :
    fib d L N₀ q n y ⊆ S := by
  obtain ⟨x, hx, rfl⟩ := mem_tBlocks.1 hy
  intro x' hx'
  rw [mem_fib] at hx'
  exact (hS x' x hx').2 hx

theorem mem_tBlocks_iff_fib_subset {n : ℕ} {S : Finset (Site d L N₀ q)}
    (hS : IsBlockUnion L N₀ q n S) {y : Blk d L N₀ q n} (hn : n ≤ q) :
    y ∈ tBlocks d L N₀ q n S ↔ fib d L N₀ q n y ⊆ S := by
  refine ⟨fib_subset_of_mem_tBlocks hS, fun h => ?_⟩
  obtain ⟨x, hx⟩ := fib_nonempty hn y
  exact mem_tBlocks.2 ⟨x, h hx, mem_fib.1 hx⟩

theorem bavgL_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (φ : Site d L N₀ q → E) (y : Blk d L N₀ q n) :
    bavgL d L N₀ q n φ y = bavg (L ^ n) (N₀ * L ^ (q - n)) φ y := rfl

theorem blkMap_zero (x : Site d L N₀ q) : blkMap d L N₀ q 0 x = x := by
  funext i
  show blockCoord (L ^ 0) (N₀ * L ^ (q - 0)) (x i) = x i
  unfold blockCoord
  simp only [pow_zero, Nat.div_one]
  exact ZMod.natCast_zmod_val (x i)

theorem fib_zero (y : Blk d L N₀ q 0) : fib d L N₀ q 0 y = {y} := by
  ext x
  rw [mem_fib, blkMap_zero]
  simp only [Finset.mem_singleton]

/-- At scale `0` the block average is the field itself. -/
theorem bavgL_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Site d L N₀ q → E) (y : Blk d L N₀ q 0) : bavgL d L N₀ q 0 φ y = φ y := by
  unfold bavgL bavg
  rw [← fib_eq_blockFibre, fib_zero]
  simp

theorem psiFull_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Site d L N₀ q → E) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (y : Blk d L N₀ q 0) :
    psiFull φ ψ 0 y = bavgL d L N₀ q 0 φ y := by
  rw [bavgL_zero]; rfl

end Basic

section Layers

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ)

theorem layerIndex_eq_zero_iff (x : Site d L N₀ q) : G.layerIndex x = 0 ↔ x ∉ G.Ω 1 := by
  constructor
  · intro h hx
    have := (G.layerIndex_spec hx).1
    omega
  · intro hx
    unfold GeneratingSet.layerIndex
    have : ¬ ∃ j, 1 ≤ j ∧ j ≤ q ∧ x ∈ G.layer j := by
      rintro ⟨j, hj, hjq, hxj⟩
      exact hx (G.layer_subset hj hjq hxj)
    simp [this]

theorem layerIndex_le (x : Site d L N₀ q) : G.layerIndex x ≤ q := by
  by_cases hx : x ∈ G.Ω 1
  · exact (G.layerIndex_spec hx).2.1
  · rw [(layerIndex_eq_zero_iff G x).2 hx]; exact Nat.zero_le _

theorem mem_lam_iff {n : ℕ} (hn : n ≤ q) (x : Site d L N₀ q) :
    x ∈ lam G n ↔ G.layerIndex x = n := by
  unfold lam
  by_cases h0 : n = 0
  · subst h0
    simp [layerIndex_eq_zero_iff]
  · simp only [h0, ↓reduceIte]
    constructor
    · intro hx
      exact G.layerIndex_eq (Nat.one_le_iff_ne_zero.2 h0) hn hx
    · intro h
      have hx1 : x ∈ G.Ω 1 := by
        by_contra hx
        have := (layerIndex_eq_zero_iff G x).2 hx
        omega
      have := (G.layerIndex_spec hx1).2.2
      rwa [h] at this

theorem lam_disjoint {n n' : ℕ} (hn : n ≤ q) (hn' : n' ≤ q) (hne : n ≠ n') {x : Site d L N₀ q}
    (hx : x ∈ lam G n) : x ∉ lam G n' := by
  rw [mem_lam_iff G hn] at hx
  rw [mem_lam_iff G hn']
  omega

theorem mem_lam_layerIndex (x : Site d L N₀ q) : x ∈ lam G (G.layerIndex x) :=
  (mem_lam_iff G (layerIndex_le G x) x).2 rfl

theorem isBlockUnion_zero (S : Finset (Site d L N₀ q)) : IsBlockUnion L N₀ q 0 S := by
  intro x x' h
  have : x = x' := by
    have h1 : blkMap d L N₀ q 0 x = blkMap d L N₀ q 0 x' := h
    rwa [blkMap_zero, blkMap_zero] at h1
  rw [this]

/-- `Λ_n ∩ X` is a union of `n`-blocks (the hypothesis of LF-1, for `1 ≤ n ≤ q`). -/
theorem isBlockUnion_lam {X : Finset (Site d L N₀ q)}
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n)) {n : ℕ} (hn : n ≤ q) :
    IsBlockUnion L N₀ q n (lam G n ∩ X) := by
  by_cases h0 : n = 0
  · subst h0; exact isBlockUnion_zero _
  · have := hX n (Nat.one_le_iff_ne_zero.2 h0) hn
    simp only [lam, h0, ↓reduceIte]
    rwa [Finset.inter_comm]

end Layers

section Hierarchy

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L]

theorem coarse_blkMap {n : ℕ} (hn : n < q) (x : Site d L N₀ q) :
    coarse d L N₀ q n (blkMap d L N₀ q n x) = blkMap d L N₀ q (n + 1) x := by
  have hm : N₀ * L ^ (q - n) = L * (N₀ * L ^ (q - (n + 1))) := by
    have : q - n = (q - (n + 1)) + 1 := by omega
    rw [this, pow_succ]; ring
  have := blockMap_comp (sideEq (L := L) (N₀ := N₀) hn.le) hm x
  unfold coarse blkMap
  rw [this, pow_succ]

theorem card_coarse_fibre {n : ℕ} (hn : n < q) (b : Blk d L N₀ q (n + 1)) :
    (Finset.univ.filter fun s : Blk d L N₀ q n => coarse d L N₀ q n s = b).card = L ^ d := by
  have hm : N₀ * L ^ (q - n) = L * (N₀ * L ^ (q - (n + 1))) := by
    have : q - n = (q - (n + 1)) + 1 := by omega
    rw [this, pow_succ]; ring
  exact card_blockFibre hm b

/-- Summing over an `(n+1)`-block is summing over its `n`-blocks and then over their sites. -/
theorem sum_fib_succ {E : Type*} [AddCommMonoid E] {n : ℕ} (hn : n < q)
    (b : Blk d L N₀ q (n + 1)) (f : Site d L N₀ q → E) :
    ∑ x ∈ fib d L N₀ q (n + 1) b, f x =
      ∑ s ∈ Finset.univ.filter (fun s : Blk d L N₀ q n => coarse d L N₀ q n s = b),
        ∑ x ∈ fib d L N₀ q n s, f x := by
  classical
  have hmaps : ∀ x ∈ fib d L N₀ q (n + 1) b, blkMap d L N₀ q n x ∈
      Finset.univ.filter (fun s : Blk d L N₀ q n => coarse d L N₀ q n s = b) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [coarse_blkMap hn, ← mem_fib.1 hx]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter, mem_fib, Finset.mem_univ, true_and] at hs ⊢
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [← coarse_blkMap hn, h, hs]

/-- `Q_{n+1} φ = L^{-d} ∑_{s ⊂ b} Q_n φ (s)`. -/
theorem bavgL_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} (hn : n < q)
    (φ : Site d L N₀ q → E) (b : Blk d L N₀ q (n + 1)) :
    bavgL d L N₀ q (n + 1) φ b = qCoarse d L N₀ q n (bavgL d L N₀ q n φ) b := by
  classical
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold bavgL qCoarse
  unfold bavg
  rw [← fib_eq_blockFibre, sum_fib_succ hn]
  have : ∀ s : Blk d L N₀ q n, ∑ x ∈ fib d L N₀ q n s, φ x =
      (((L ^ n : ℕ) : ℝ) ^ d) • bavg (L ^ n) (N₀ * L ^ (q - n)) φ s := by
    intro s
    rw [fib_eq_blockFibre]
    exact sum_blockFibre_eq_smul_bavg (sideEq (by omega)) φ s
  rw [Finset.sum_congr rfl fun s _ => this s, ← Finset.smul_sum, smul_smul]
  congr 1
  push_cast
  field_simp
  rw [← mul_pow, ← pow_succ]

end Hierarchy

section Geometry

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem adjE_symm {d m : ℕ} {y y' : Torus d m}
    (h : ∃ μ : Fin d, y' = y + Pi.single μ 1 ∨ y = y' + Pi.single μ 1) :
    ∃ μ : Fin d, y = y' + Pi.single μ 1 ∨ y' = y + Pi.single μ 1 := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

/-- Sites of nearest-neighbour blocks are at `ℓ¹` distance `≤ 2 d L^n`. -/
theorem dist_le_of_adj {n : ℕ} (hn : n ≤ q) {b b' : Blk d L N₀ q n}
    (hb : ∃ μ : Fin d, b' = b + Pi.single μ 1 ∨ b = b' + Pi.single μ 1)
    {x z : Site d L N₀ q} (hx : x ∈ fib d L N₀ q n b) (hz : z ∈ fib d L N₀ q n b') :
    Green.torusDist d (N₀ * L ^ q) x z ≤ 2 * d * (L : ℝ) ^ n := by
  have hx' := mem_fib.1 hx
  have hz' := mem_fib.1 hz
  have key := torusDist_le_of_blocks (sideEq (L := L) (N₀ := N₀) hn) (x := x) (z := z)
  have hcast : ((L ^ n : ℕ) : ℝ) = (L : ℝ) ^ n := by push_cast; ring
  rw [hcast] at key
  refine key fun i => ?_
  unfold blkMap at hx' hz'
  obtain ⟨μ, h | h⟩ := hb
  · have := coord_cases_of_single b μ (σ := (1 : ZMod _)) (Or.inl rfl) i
    rw [← h] at this
    rw [hx', hz']
    rcases this with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · have := coord_cases_of_single b' μ (σ := (1 : ZMod _)) (Or.inl rfl) i
    rw [← h] at this
    rw [hx', hz']
    rcases this with h1 | h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h1)

/-- **Geometry of a cross pair** (separation `ϱ ≥ 2 d L`): if `b₊ ⊂ Ω_{n+1}` and `b₋ ∩ Ω_{n+1} = ∅`
are nearest-neighbour `(n+1)`-blocks, then `b₊ ∩ Ω_{n+2} = ∅` and, for `n ≥ 1`, `b₋ ⊂ Ω_n`. -/
theorem cross_geometry (G : GeneratingSet d L N₀ q ϱ) {n : ℕ} (hn : n < q)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {bp bm : Blk d L N₀ q (n + 1)}
    (hadj : ∃ μ : Fin d, bm = bp + Pi.single μ 1 ∨ bp = bm + Pi.single μ 1)
    (hp : fib d L N₀ q (n + 1) bp ⊆ G.Ω (n + 1))
    (hm : Disjoint (fib d L N₀ q (n + 1) bm) (G.Ω (n + 1))) :
    (∀ x ∈ fib d L N₀ q (n + 1) bp, x ∉ G.Ω (n + 2)) ∧
      (1 ≤ n → ∀ z ∈ fib d L N₀ q (n + 1) bm, z ∈ G.Ω n) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLn : (0 : ℝ) < (L : ℝ) ^ n := by positivity
  obtain ⟨z0, hz0⟩ := fib_nonempty (d := d) (L := L) (N₀ := N₀) (q := q) (n := n + 1) (by omega) bm
  obtain ⟨x0, hx0⟩ := fib_nonempty (d := d) (L := L) (N₀ := N₀) (q := q) (n := n + 1) (by omega) bp
  refine ⟨fun x hx hx2 => ?_, fun hn1 z hz => ?_⟩
  · -- (G1)
    by_cases hq : n + 2 = q + 1
    · rw [hq, G.top] at hx2; exact absurd hx2 (Finset.notMem_empty _)
    · have hj : n + 1 < q := by omega
      have hsep := G.separation (n + 1) (by omega) hj z0
        (fun h => Finset.disjoint_left.1 hm hz0 h) x hx2
      have hd := dist_le_of_adj (by omega : n + 1 ≤ q) (adjE_symm hadj) hz0 hx
      have hLp : (0 : ℝ) < (L : ℝ) ^ (n + 1) := by positivity
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      have h2d : 2 * (d : ℝ) ≤ ϱ := by nlinarith
      have h3 : 2 * (d : ℝ) * (L : ℝ) ^ (n + 1) ≤ ϱ * (L : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right h2d hLp.le
      linarith
  · by_contra hzn
    have hsep := G.separation n hn1 hn z hzn x0 (hp hx0)
    have hd := dist_le_of_adj (by omega : n + 1 ≤ q) (adjE_symm hadj) hz hx0
    have hpow : (L : ℝ) ^ (n + 1) = (L : ℝ) ^ n * L := pow_succ _ _
    have h3 : 2 * (d : ℝ) * L * (L : ℝ) ^ n ≤ ϱ * (L : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hϱ hLn.le
    nlinarith

/-- The sites of the `n`-blocks `s` inside the `(n+1)`-block `bm` lie in `bm`. -/
theorem fib_subset_of_coarse {n : ℕ} (hn : n < q) {s : Blk d L N₀ q n} {bm : Blk d L N₀ q (n + 1)}
    (h : coarse d L N₀ q n s = bm) : fib d L N₀ q n s ⊆ fib d L N₀ q (n + 1) bm := by
  intro x hx
  rw [mem_fib] at hx ⊢
  rw [← coarse_blkMap hn, hx, h]

/-- **Fibre containments of a cross pair**: `b₊ ⊂ Λ_{n+1} ∩ X` and `b₋ ⊂ Λ_n ∩ X`. -/
theorem cross_fib_subsets (G : GeneratingSet d L N₀ q ϱ) {n : ℕ} (hn : n < q)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {X : Finset (Site d L N₀ q)} {bp bm : Blk d L N₀ q (n + 1)}
    (hadj : ∃ μ : Fin d, bm = bp + Pi.single μ 1 ∨ bp = bm + Pi.single μ 1)
    (hp : fib d L N₀ q (n + 1) bp ⊆ X ∩ G.Ω (n + 1)) (hm1 : fib d L N₀ q (n + 1) bm ⊆ X)
    (hm2 : Disjoint (fib d L N₀ q (n + 1) bm) (G.Ω (n + 1))) :
    fib d L N₀ q (n + 1) bp ⊆ lam G (n + 1) ∩ X ∧ fib d L N₀ q (n + 1) bm ⊆ lam G n ∩ X := by
  obtain ⟨g1, g2⟩ := cross_geometry G hn hϱ hadj (fun x hx => (Finset.mem_inter.1 (hp hx)).2) hm2
  constructor
  · intro x hx
    have hx' := Finset.mem_inter.1 (hp hx)
    refine Finset.mem_inter.2 ⟨?_, hx'.1⟩
    simp only [lam, Nat.succ_ne_zero, ↓reduceIte]
    exact G.mem_layer.2 ⟨hx'.2, g1 x hx⟩
  · intro z hz
    refine Finset.mem_inter.2 ⟨?_, hm1 hz⟩
    have hz2 : z ∉ G.Ω (n + 1) := fun h => Finset.disjoint_left.1 hm2 hz h
    by_cases h0 : n = 0
    · subst h0
      simp only [lam, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact hz2
    · simp only [lam, h0, ↓reduceIte]
      exact G.mem_layer.2 ⟨g2 (Nat.one_le_iff_ne_zero.2 h0) z hz, hz2⟩

end Geometry

end Balaban.LargeField
