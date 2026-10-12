/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroData
public import Balaban.LargeField.R.ZeroDomainRef
public import Balaban.LargeField.LF1.BlockArith
public import Balaban.Correlations.PolymerCount
public import Balaban.Green.BlockDistance
public import Balaban.Background.CompositionSystem

/-!
# Interface pairs of `k`-blocks (geometry for Lemma III.3.3)

Neighbouring fine sites lie in the same or in neighbouring `k`-blocks (`jBlock_adj`, `blocks_of_interface`), and
neighbouring `k`-blocks inside `Ω_k(G)` carry an interface pair of fine sites (`exists_interface_pair`), so that the
conditions (R1) of the tube `Ψ̃(𝔹_k; δ)` apply to every pair of neighbouring blocks of `Ω_k`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Geom

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

theorem fine_eq_block (L N₀ k : ℕ) : N₀ * L ^ k = L ^ k * (N₀ * L ^ (k - k)) := by
  simp [mul_comm]

/-- Neighbouring fine sites lie in the same `k`-block or in neighbouring `k`-blocks. -/
theorem jBlock_adj {x y : Torus d (N₀ * L ^ k)} (h : Adj x y) :
    jBlock d L N₀ k k x = jBlock d L N₀ k k y ∨ torusAdj (jBlock d L N₀ k k x) (jBlock d L N₀ k k y) := by
  obtain ⟨μ, h | h⟩ := h
  · rcases Balaban.Correlations.blockMap_step (fine_eq_block L N₀ k) x μ with e | e
    · left; unfold jBlock; rw [h]; exact e.symm
    · right; exact ⟨μ, Or.inl (by unfold jBlock; rw [h]; exact e)⟩
  · rcases Balaban.Correlations.blockMap_step (fine_eq_block L N₀ k) y μ with e | e
    · left; unfold jBlock; rw [h]; exact e
    · right; exact ⟨μ, Or.inr (by unfold jBlock; rw [h]; exact e)⟩

/-- Sites of a block of `x` lie in the `k`-block of `x`. -/
theorem jBlock_of_mem_blockSet {x y : Torus d (N₀ * L ^ k)} (h : y ∈ blockSet G x) :
    jBlock d L N₀ k k y = jBlock d L N₀ k k x := by
  classical
  unfold blockSet at h
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte] at h
    exact jBlock_eq_of_le (layerIndex_le_k G x) le_rfl (GeneratingSet.mem_blk.1 h)
  · simp only [hx, ↓reduceIte] at h
    simp at h
    rw [h]

/-- An interface pair of fine sites lies in the same `k`-block or in neighbouring `k`-blocks. -/
theorem blocks_of_interface {x x' : Torus d (N₀ * L ^ k)} (h : IsInterfacePair G x x') :
    jBlock d L N₀ k k x = jBlock d L N₀ k k x' ∨ torusAdj (jBlock d L N₀ k k x) (jBlock d L N₀ k k x') := by
  obtain ⟨-, -, -, y, hy, y', hy', hadj⟩ := h
  rw [← jBlock_of_mem_blockSet G hy, ← jBlock_of_mem_blockSet G hy']
  exact jBlock_adj hadj

/-- Two neighbouring `k`-blocks `A`, `A + e_μ` contain neighbouring fine sites. -/
theorem exists_adj_sites (A : Torus d (N₀ * L ^ (k - k))) (μ : Fin d) :
    ∃ p q : Torus d (N₀ * L ^ k), Adj p q ∧ jBlock d L N₀ k k p = A ∧
      jBlock d L N₀ k k q = A + Pi.single μ 1 := by
  have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  obtain ⟨x0, hx0⟩ := Balaban.exists_blockMap_eq (fine_eq_block L N₀ k) hN A
  set r := (x0 μ).val % L ^ k with hr
  have hrN : r < L ^ k := Nat.mod_lt _ hN
  set t := L ^ k - 1 - r with ht
  have hrt : r + t = L ^ k - 1 := by omega
  refine ⟨x0 + Pi.single μ (t : ZMod (N₀ * L ^ k)), x0 + Pi.single μ ((t + 1 : ℕ) : ZMod (N₀ * L ^ k)),
    ⟨μ, Or.inl ?_⟩, ?_, ?_⟩
  · rw [add_assoc, ← Pi.single_add]; push_cast; rfl
  · unfold jBlock
    rw [blockMap_add_single_natCast (fine_eq_block L N₀ k), ← hr, hrt, Nat.div_eq_of_lt (by omega)]
    simpa using hx0
  · unfold jBlock
    rw [blockMap_add_single_natCast (fine_eq_block L N₀ k), ← hr]
    have : (r + (t + 1)) / L ^ k = 1 := by
      rw [show r + (t + 1) = L ^ k by omega]; exact Nat.div_self hN
    rw [this]
    simp [hx0]

/-- Adjacent fine sites of `Ω_k` form an interface pair. -/
theorem isInterfacePair_of_mem_top (hk : 1 ≤ k) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k)
    (hx' : x' ∈ G.Ω k) (hadj : Adj x x') : IsInterfacePair G x x' := by
  classical
  have h1 : ∀ y, y ∈ G.Ω k → y ∈ G.Ω 1 := fun y hy => G.Ω_antitone le_rfl hk (by omega) hy
  have hli : ∀ y, y ∈ G.Ω k → G.layerIndex y = k := fun y hy =>
    G.layerIndex_eq hk le_rfl (G.mem_layer.2 ⟨hy, by rw [G.top]; simp⟩)
  have hds : ∀ y, y ∈ G.Ω k → y ∈ dataSites G := fun y hy => (mem_dataSites G).2 (Or.inl (h1 y hy))
  have hbs : ∀ y, y ∈ G.Ω k → y ∈ blockSet G y := fun y hy => by
    unfold blockSet
    simp only [h1 y hy, ↓reduceIte]
    exact GeneratingSet.mem_blk.2 rfl
  exact ⟨hds x hx, hds x' hx', Or.inl ((hli x' hx').trans (hli x hx).symm), x, hbs x hx, x', hbs x' hx', hadj⟩

/-- Neighbouring `k`-blocks inside `Ω_k` carry an interface pair of fine sites. -/
theorem exists_interface_pair (hk : 1 ≤ k) {z z' : Torus d (N₀ * L ^ (k - k))} (hadj : torusAdj z z')
    (hΩ : ∀ x, jBlock d L N₀ k k x = z ∨ jBlock d L N₀ k k x = z' → x ∈ G.Ω k) :
    ∃ x x', IsInterfacePair G x x' ∧ jBlock d L N₀ k k x = z ∧ jBlock d L N₀ k k x' = z' := by
  obtain ⟨μ, h | h⟩ := hadj
  · obtain ⟨p, q, hpq, hp, hq⟩ := exists_adj_sites (L := L) (N₀ := N₀) (k := k) z μ
    rw [← h] at hq
    exact ⟨p, q, isInterfacePair_of_mem_top G hk (hΩ p (Or.inl hp)) (hΩ q (Or.inr hq)) hpq, hp, hq⟩
  · obtain ⟨p, q, hpq, hp, hq⟩ := exists_adj_sites (L := L) (N₀ := N₀) (k := k) z' μ
    rw [← h] at hq
    exact ⟨q, p, isInterfacePair_of_mem_top G hk (hΩ q (Or.inl hq)) (hΩ p (Or.inr hp)) hpq.symm, hq, hp⟩

end Geom

end Balaban.LargeField
