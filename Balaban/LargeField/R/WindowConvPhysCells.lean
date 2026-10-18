/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvWindow
public import Balaban.Background.BlockGeometry
public import Balaban.Background.Composition

/-!
# Positive block-cell decomposition of a regional action

The regions of a generating set split canonically into their nonempty layer blocks.
Each block has weight one.  The crossing bonds split by the block on the inside,
coordinate direction, and orientation, with at most `2 d` slots per block.  For an
actual quiet piece, `WindowRegionGeom` identifies the two possible layers as `j`
and `j+1`.  The identification of this cell count with the P6 (2.31) mixed count
and the refinement of each slot to the `M`-cube walls of P6 p. 11 remain separate
geometric statements.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ K ϱ}

/-- A layer block containing a site of a region is the same layer block at each
of its sites. -/
theorem Region.layerBlock_eq_of_mem (X : Region G) {x y : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) (hy : y ∈ G.blk (G.layerIndex x) x) :
    G.layerIndex y = G.layerIndex x ∧
      G.blk (G.layerIndex y) y = G.blk (G.layerIndex x) x := by
  obtain ⟨h1, hK, hxl⟩ := G.layerIndex_spec (X.sub_Ω hx)
  have hyl := mem_layer_of_mem_blk G h1 hK hxl hy
  have heq := G.layerIndex_eq h1 hK hyl
  exact ⟨heq, by rw [heq]; exact blk_eq_of_mem hy⟩

/-- Every regional block cell has strictly positive weight one, and its crossing
bonds admit at most `2 d` oriented face slots.  The total is the number of
distinct layer blocks meeting `X`. -/
theorem Region.exists_stepDecomp_positive_blocks_cells (X : Region G) :
    ∃ Dc : StepDecomp X,
      (∀ i, 0 < Dc.wt i) ∧
      Dc.inc = 2 * d ∧
      Dc.total = ((X.sites.image fun x => G.blk (G.layerIndex x) x).card : ℝ) ∧
      (∀ q, Dc.wall q ⊆ (Dc.cube (Dc.wallCube q)).crossing) ∧
      (∀ i, Dc.wt i = 1) ∧
      (∀ i, ∃ x ∈ X.sites, (Dc.cube i).sites = G.blk (G.layerIndex x) x) := by
  classical
  let cells : Finset (Finset (Torus d (N₀ * L ^ K))) :=
    X.sites.image fun x => G.blk (G.layerIndex x) x
  let ι := {B : Finset (Torus d (N₀ * L ^ K)) // B ∈ cells}
  let cell : ι → Region G := fun B =>
    { sites := B.1
      sub_Ω := by
        obtain ⟨x, hx, hBx⟩ := Finset.mem_image.mp B.2
        intro y hy
        rw [← hBx] at hy
        exact X.sub_Ω (X.blockClosed x hx y hy)
      blockClosed := by
        obtain ⟨x, hx, hBx⟩ := Finset.mem_image.mp B.2
        intro y hy z hz
        have hy' : y ∈ G.blk (G.layerIndex x) x := by simpa only [hBx] using hy
        have hcell := (X.layerBlock_eq_of_mem hx hy').2
        rw [hcell] at hz
        simpa only [hBx] using hz }
  have hsub : ∀ B : ι, (cell B).sites ⊆ X.sites := by
    intro B
    obtain ⟨x, hx, hBx⟩ := Finset.mem_image.mp B.2
    intro y hy
    change y ∈ B.1 at hy
    rw [← hBx] at hy
    exact X.blockClosed x hx y hy
  have hpair : Pairwise fun B B' : ι => Disjoint (cell B).sites (cell B').sites := by
    intro B B' hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x, hx, hBx⟩ := Finset.mem_image.mp B.2
    obtain ⟨x', hx', hBx'⟩ := Finset.mem_image.mp B'.2
    have hBy : B.1 = G.blk (G.layerIndex y) y := by
      have hmem : y ∈ G.blk (G.layerIndex x) x := by simpa only [hBx] using hy
      exact hBx ▸ (X.layerBlock_eq_of_mem hx hmem).2.symm
    have hBy' : B'.1 = G.blk (G.layerIndex y) y := by
      have hmem : y ∈ G.blk (G.layerIndex x') x' := by simpa only [hBx'] using hy'
      exact hBx' ▸ (X.layerBlock_eq_of_mem hx' hmem).2.symm
    exact hne (Subtype.ext (hBy.trans hBy'.symm))
  have hunion : X.sites = Finset.univ.biUnion fun B : ι => (cell B).sites := by
    ext y
    rw [Finset.mem_biUnion]
    constructor
    · intro hy
      refine ⟨⟨G.blk (G.layerIndex y) y, Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩,
        Finset.mem_univ _, ?_⟩
      exact G.mem_blk.mpr rfl
    · rintro ⟨B, -, hy⟩
      exact hsub B hy
  let inside : (Torus d (N₀ * L ^ K) × Fin d) → Torus d (N₀ * L ^ K) :=
    fun b => if b.1 ∈ X.sites then b.1 else b.1 + Pi.single b.2 1
  let κ := ι × (Fin d × Bool)
  let wall : κ → Finset (Torus d (N₀ * L ^ K) × Fin d) := fun q =>
    X.crossing.filter fun b => b.2 = q.2.1 ∧
      decide (b.1 ∈ X.sites) = q.2.2 ∧ inside b ∈ (cell q.1).sites
  have hins : ∀ b ∈ X.crossing, inside b ∈ X.sites := by
    intro b hb
    have hb' : ¬ (b.1 ∈ X.sites ↔ b.1 + Pi.single b.2 1 ∈ X.sites) := by
      simpa only [Region.crossing, Finset.mem_filter, Finset.mem_univ, true_and] using hb
    by_cases h : b.1 ∈ X.sites
    · simp [inside, h]
    · have h' : b.1 + Pi.single b.2 1 ∈ X.sites := by tauto
      simpa [inside, h] using h'
  have hwallUnion : X.crossing = Finset.univ.biUnion wall := by
    ext b
    rw [Finset.mem_biUnion]
    constructor
    · intro hb
      have hi := hins b hb
      rw [hunion, Finset.mem_biUnion] at hi
      obtain ⟨B, -, hB⟩ := hi
      refine ⟨(B, (b.2, decide (b.1 ∈ X.sites))), Finset.mem_univ _, ?_⟩
      simp only [wall, Finset.mem_filter, hb, true_and, inside]
      exact hB
    · rintro ⟨q, -, hq⟩
      exact (Finset.mem_filter.mp hq).1
  have hwallDisj : Pairwise fun q q' : κ => Disjoint (wall q) (wall q') := by
    intro q q' hne
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    obtain ⟨-, hdir, hsign, hB⟩ := (Finset.mem_filter.mp hb)
    obtain ⟨-, hdir', hsign', hB'⟩ := (Finset.mem_filter.mp hb')
    have hq : q.1 = q'.1 := by
      by_contra h
      exact Finset.disjoint_left.mp (hpair h) hB hB'
    have hd : q.2.1 = q'.2.1 := hdir.symm.trans hdir'
    have hs : q.2.2 = q'.2.2 := hsign.symm.trans hsign'
    exact hne (Prod.ext hq (Prod.ext hd hs))
  have hwallSub : ∀ q : κ, wall q ⊆ (cell q.1).crossing := by
    intro q b hb
    obtain ⟨hbX, _, _, hbB⟩ := Finset.mem_filter.mp hb
    have hcross : ¬ (b.1 ∈ X.sites ↔ b.1 + Pi.single b.2 1 ∈ X.sites) := by
      simpa only [Region.crossing, Finset.mem_filter, Finset.mem_univ, true_and] using hbX
    simp only [Region.crossing, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : b.1 ∈ X.sites
    · have hfirst : b.1 ∈ (cell q.1).sites := by simpa [inside, h] using hbB
      have hsecond : b.1 + Pi.single b.2 1 ∉ X.sites := by tauto
      intro heq
      exact hsecond (hsub q.1 (heq.mp hfirst))
    · have hsecond : b.1 + Pi.single b.2 1 ∈ (cell q.1).sites := by
        simpa [inside, h] using hbB
      have hfirst : b.1 ∉ (cell q.1).sites := fun hb' => h (hsub q.1 hb')
      intro heq
      exact hfirst (heq.mpr hsecond)
  let Dc : StepDecomp X :=
    { ι := ι
      κ := κ
      cube := cell
      wt := fun _ => 1
      wt_nonneg := by intro _; norm_num
      cube_disj := hpair
      cube_union := hunion
      wall := wall
      wall_disj := hwallDisj
      wall_union := hwallUnion
      wallCube := Prod.fst
      inc := 2 * d
      inc_le := by
        intro B
        have heq : (Finset.univ.filter fun q : κ => q.1 = B) =
            ({B} : Finset ι).product (Finset.univ : Finset (Fin d × Bool)) := by
          ext q
          constructor
          · intro h
            exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr
              ((Finset.mem_filter.mp h).2), Finset.mem_univ _⟩
          · intro h
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.mem_singleton.mp (Finset.mem_product.mp h).1⟩
        rw [heq]
        simp [Fintype.card_prod, Nat.mul_comm]
    }
  refine ⟨Dc, ?_, rfl, ?_, ?_, fun _ => rfl, ?_⟩
  · intro i
    norm_num [Dc]
  · change (∑ _ : ι, (1 : ℝ)) = (cells.card : ℝ)
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    exact_mod_cast Fintype.card_coe cells
  · exact hwallSub
  · intro B
    obtain ⟨x, hx, hBx⟩ := Finset.mem_image.mp B.2
    exact ⟨x, hx, hBx.symm⟩

/-- Every regional block cell has strictly positive weight one, and its crossing
bonds admit at most `2 d` oriented face slots.  The total is the number of
distinct layer blocks meeting `X`. -/
theorem Region.exists_stepDecomp_positive_blocks (X : Region G) :
    ∃ Dc : StepDecomp X,
      (∀ i, 0 < Dc.wt i) ∧
      Dc.inc = 2 * d ∧
      Dc.total = ((X.sites.image fun x => G.blk (G.layerIndex x) x).card : ℝ) ∧
      (∀ q, Dc.wall q ⊆ (Dc.cube (Dc.wallCube q)).crossing) := by
  obtain ⟨Dc, h1, h2, h3, h4, -, -⟩ := X.exists_stepDecomp_positive_blocks_cells
  exact ⟨Dc, h1, h2, h3, h4⟩

/-- When a region meets only layers `j` and `j+1`, its canonical cell count
is the sum of the numbers of distinct blocks at those two scales. -/
theorem Region.layerBlock_count_two (X : Region G) (j : ℕ)
    (htwo : ∀ x ∈ X.sites, G.layerIndex x = j ∨ G.layerIndex x = j + 1) :
    (X.sites.image fun x => G.blk (G.layerIndex x) x).card =
      ((X.sites.filter fun x => G.layerIndex x = j).image fun x => G.blk j x).card +
      ((X.sites.filter fun x => G.layerIndex x = j + 1).image fun x => G.blk (j + 1) x).card := by
  classical
  let A := (X.sites.filter fun x => G.layerIndex x = j).image fun x => G.blk j x
  let B := (X.sites.filter fun x => G.layerIndex x = j + 1).image fun x => G.blk (j + 1) x
  have hU : (X.sites.image fun x => G.blk (G.layerIndex x) x) = A ∪ B := by
    ext C
    constructor
    · intro h
      obtain ⟨x, hx, hC⟩ := Finset.mem_image.mp h
      rcases htwo x hx with hj | hj
      · apply Finset.mem_union.mpr (Or.inl _)
        apply Finset.mem_image.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, hj⟩, by simpa [hj] using hC⟩
      · apply Finset.mem_union.mpr (Or.inr _)
        apply Finset.mem_image.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, hj⟩, by simpa [hj] using hC⟩
    · intro h
      rcases Finset.mem_union.mp h with hA | hB
      · obtain ⟨x, hx, hC⟩ := Finset.mem_image.mp hA
        obtain ⟨hxX, hj⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_image.mpr ⟨x, hxX, by simpa [hj] using hC⟩
      · obtain ⟨x, hx, hC⟩ := Finset.mem_image.mp hB
        obtain ⟨hxX, hj⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_image.mpr ⟨x, hxX, by simpa [hj] using hC⟩
  have hD : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro C hA hB
    obtain ⟨x, hxA, hxC⟩ := Finset.mem_image.mp hA
    obtain ⟨y, hyB, hyC⟩ := Finset.mem_image.mp hB
    obtain ⟨hxX, hxj⟩ := Finset.mem_filter.mp hxA
    obtain ⟨hyX, hyj⟩ := Finset.mem_filter.mp hyB
    have hxy : x ∈ G.blk (G.layerIndex y) y := by
      rw [hyj, hyC, ← hxC]
      exact G.mem_blk.mpr rfl
    have heq := (X.layerBlock_eq_of_mem hyX hxy).1
    omega
  rw [hU, Finset.card_union_of_disjoint hD]

end Balaban.LargeField.ActionConv
