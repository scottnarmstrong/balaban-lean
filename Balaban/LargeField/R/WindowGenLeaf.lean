module

public import Balaban.LargeField.LF1.Struct
public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Leaves of a generating set (Lemma III.2.3, preparation)

For a generating set `G` at level `q` and a site `s ∈ Ω₁` the *leaf* of `s` is the `n_s`-block of `s`,
`n_s = G.layerIndex s`.  If `X ∩ Λ_n` is a union of `n`-blocks for every `n`, then the leaves of the
sites of `X ∩ Ω₁` partition `X ∩ Ω₁` (`leaf_closed`), and sums over sites can be regrouped as sums
over leaves (`sum_partition_avg`, `sum_blkMap`).  The leaves are the "leaves `x ⊂ z`" of the block
tree in the proof of Lemma III.2.3.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Partition

variable {α : Type*} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If the family `leaf` of finite sets partitions `S` (each `s ∈ S` lies in `leaf s`, and the
members of `leaf s` lie in `S` and have the same leaf), then averaging a function over the leaf of
`s` and summing over `s ∈ S` is the same as summing the function over `S`. -/
theorem sum_partition_avg (S : Finset α) (leaf : α → Finset α) (ha : ∀ s ∈ S, s ∈ leaf s)
    (hb : ∀ s ∈ S, ∀ s' ∈ leaf s, s' ∈ S ∧ leaf s' = leaf s) (f : α → E) :
    ∑ s ∈ S, ((leaf s).card : ℝ)⁻¹ • ∑ s' ∈ leaf s, f s' = ∑ s ∈ S, f s := by
  have h1 : ∀ s ∈ S, ((leaf s).card : ℝ)⁻¹ • ∑ s' ∈ leaf s, f s' =
      ∑ s' ∈ leaf s, ((leaf s).card : ℝ)⁻¹ • f s' := fun s _ => by rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := S) (s' := fun s' => leaf s')]
  · refine Finset.sum_congr rfl fun s' hs' => ?_
    have hc : ∀ s ∈ leaf s', ((leaf s).card : ℝ)⁻¹ • f s' = ((leaf s').card : ℝ)⁻¹ • f s' := by
      intro s hs
      have := (hb s' hs' s hs).2
      rw [this]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    have hne : ((leaf s').card : ℝ) ≠ 0 := by
      have : 0 < (leaf s').card := Finset.card_pos.2 ⟨s', ha s' hs'⟩
      exact_mod_cast this.ne'
    rw [mul_inv_cancel₀ hne, one_smul]
  · intro s s'
    constructor
    · rintro ⟨hs, hs'⟩
      obtain ⟨h1, h2⟩ := hb s hs s' hs'
      exact ⟨by rw [h2]; exact ha s hs, h1⟩
    · rintro ⟨hs, hs'⟩
      obtain ⟨h1, h2⟩ := hb s' hs' s hs
      exact ⟨h1, by rw [h2]; exact ha s' hs'⟩

end Partition

section Blocks

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Summing a function of the `n`-block over a union of `n`-blocks: each block is counted
`(L^n)^d` times. -/
theorem sum_blkMap {n : ℕ} (hn : n ≤ q) {S : Finset (Site d L N₀ q)}
    (hS : IsBlockUnion L N₀ q n S) (g : Blk d L N₀ q n → E) :
    ∑ s ∈ S, g (blkMap d L N₀ q n s) =
      (((L ^ n : ℕ) : ℝ) ^ d) • ∑ y ∈ tBlocks d L N₀ q n S, g y := by
  classical
  have hmaps : ∀ s ∈ S, blkMap d L N₀ q n s ∈ tBlocks d L N₀ q n S := fun s hs =>
    blkMap_mem_tBlocks hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hfib : S.filter (fun s => blkMap d L N₀ q n s = y) = fib d L N₀ q n y := by
    ext s
    simp only [Finset.mem_filter, mem_fib]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fib_subset_of_mem_tBlocks hS hy (mem_fib.2 h), h⟩
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.1 hs).2]), Finset.sum_const,
    hfib, card_fib hn, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  rfl

/-- The leaf of a site `s`: its `n_s`-block, `n_s` the layer index of `s`. -/
noncomputable def leaf (G : GeneratingSet d L N₀ q ϱ) (s : Site d L N₀ q) : Finset (Site d L N₀ q) :=
  fib d L N₀ q (G.layerIndex s) (blkMap d L N₀ q (G.layerIndex s) s)

theorem mem_leaf_self (G : GeneratingSet d L N₀ q ϱ) (s : Site d L N₀ q) : s ∈ leaf G s :=
  mem_fib.2 rfl

theorem card_leaf (G : GeneratingSet d L N₀ q ϱ) (s : Site d L N₀ q) :
    (leaf G s).card = (L ^ G.layerIndex s) ^ d :=
  card_fib (layerIndex_le G s) _

/-- The leaves of the sites of `X ∩ Ω₁` partition `X ∩ Ω₁`, provided `X ∩ Λ_n` is a union of
`n`-blocks for every `1 ≤ n ≤ q`. -/
theorem leaf_closed (G : GeneratingSet d L N₀ q ϱ) {X : Finset (Site d L N₀ q)}
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    {s : Site d L N₀ q} (hs : s ∈ X) (hs1 : s ∈ G.Ω 1) {s' : Site d L N₀ q}
    (hs' : s' ∈ leaf G s) :
    s' ∈ X ∧ s' ∈ G.Ω 1 ∧ G.layerIndex s' = G.layerIndex s ∧ leaf G s' = leaf G s := by
  obtain ⟨hn1, hnq, hsl⟩ := G.layerIndex_spec hs1
  set n := G.layerIndex s with hn
  have hblk : blkMap d L N₀ q n s' = blkMap d L N₀ q n s := mem_fib.1 hs'
  have hjb : jBlock d L N₀ q n s' = jBlock d L N₀ q n s := hblk
  have hmem : s' ∈ X ∩ G.layer n := (hX n hn1 hnq s' s hjb).2 (Finset.mem_inter.2 ⟨hs, hsl⟩)
  obtain ⟨hs'X, hs'l⟩ := Finset.mem_inter.1 hmem
  have hl : G.layerIndex s' = n := G.layerIndex_eq hn1 hnq hs'l
  refine ⟨hs'X, G.layer_subset hn1 hnq hs'l, hl, ?_⟩
  unfold leaf
  rw [hl, ← hn, hblk]

omit [Module ℝ E] in
/-- Splitting a sum over a union of `n`-blocks into the sums over the blocks. -/
theorem sum_eq_sum_fib {n : ℕ} {S : Finset (Site d L N₀ q)} (hS : IsBlockUnion L N₀ q n S)
    (f : Site d L N₀ q → E) :
    ∑ s ∈ S, f s = ∑ y ∈ tBlocks d L N₀ q n S, ∑ s ∈ fib d L N₀ q n y, f s := by
  classical
  have hmaps : ∀ s ∈ S, blkMap d L N₀ q n s ∈ tBlocks d L N₀ q n S := fun s hs =>
    blkMap_mem_tBlocks hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hfib : S.filter (fun s => blkMap d L N₀ q n s = y) = fib d L N₀ q n y := by
    ext s
    simp only [Finset.mem_filter, mem_fib]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fib_subset_of_mem_tBlocks hS hy (mem_fib.2 h), h⟩
  rw [hfib]

/-- Nesting: the leaf of `s` lies in the `k`-block of `s` for every `k ≥ n_s`. -/
theorem blkMap_of_mem_leaf (G : GeneratingSet d L N₀ q ϱ) {s : Site d L N₀ q} {j : ℕ} (hj : G.layerIndex s ≤ j)
    (hjq : j ≤ q) {s' : Site d L N₀ q} (hs' : s' ∈ leaf G s) :
    blkMap d L N₀ q j s' = blkMap d L N₀ q j s :=
  Background.jBlock_eq_of_le hj hjq (mem_fib.1 hs')

end Blocks

end Balaban.LargeField
