/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootMarkGeom
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Localization.I5FluctLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Root support of the marked terms: the bridge to a rooted domain (MARKCUBIC.md §4, package 3)

The marks of the first-order term at the root `z` come from a marked difference of the block
expansion.  A term of that expansion is indexed by a pair `(b, Y)`: a block `b` and a domain `Y`
of the landed expansion.  By the locality clause of the expansion (`vblock_expansion_scaled`), the
term `(b, Y)` reads the tangent only on `psiThick Y`, the set `Y` together with its nearest
neighbours.  The marked tangent differs from the unmarked one only on the block `B(z)`
(`fineBlock z`).  So a term can be non-zero only if `psiThick Y` meets `fineBlock z`, and this does
**not** put the root cube among the cubes of `Y`.

This file is pure geometry and combinatorics.  No mark is constructed and no analytic statement
is proved.

* `markedIdx reads dom z`: the pairs `(b, Y)`, `Y ∈ dom b`, such that the sites `reads b` read by
  the block `b` meet `fineBlock z` and `psiThick Y` meets `fineBlock z`.  Dropping the other
  blocks changes no sum over `Y`, since the sum over `Y` of the terms of a block is the block
  energy, which reads only `reads b`.
* `bridge m₀ z Y`: `Y` itself if the root cube is a cube of `Y`; otherwise `Y` together with
  every aligned `π′`-cube that contains the root cube and shares a cube with `Y`.
* `bridge_isDj`, `subset_bridge`, `treeLenCovOne_bridge_le`: `bridge z Y` is a domain of the
  class `𝒟_K` that contains `Y`, with `d^cov(bridge z Y) ≤ d^cov(Y) + cBr d L`,
  `cBr d L = L^d · 2 d L`; this is the landed union bound (G3) applied once per added cube, at most
  `L^d` of them.
* `rootCube_mem_blocksOf_bridge`: if `psiThick Y` meets `fineBlock z`, the root cube is a cube of
  `bridge z Y` (for `L ≥ 2`).
* `card_fibre_bridge_le`, `fibre_weighted_le`: at most `nFibre d L = 2 ^ (L^d · L^d)` domains of a
  finite family are sent to the same `Y′`, and the weighted form
  `∑_{bridge Y = Y′} e^{-a d(Y)} ≤ nFibre · e^{a cBr} e^{-a d(Y′)}`.
* `bridgeFamily`: the finite family `𝒴_z` of the bridges of the contributing pairs; every member
  is in `𝒟_K` and contains the root cube (`bridgeFamily_spec`), the prefactor sum over it is at most
  `F K₀` (`bridgeFamily_entropy`), and marks labelled by it have the root cube among their cubes
  (`anchor_of_bridgeFamily`).

## Scope

Hypotheses are typing data (`L ^ m₀ ∣ N₁`, `2 ≤ L`, that the domains are in `𝒟_K`).  The marks
and the activities are not constructed here.  Nothing depends on a choice of generating set for
the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory

section Bridge

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (m₀ : ℕ)

open Classical in
/-- **The aligned `π′`-cubes containing the root cube**: the aligned `p` of the paving with the
base of `rootCube z` in `box p (L · cellSide)`. -/
noncomputable def rootCubes (z : RootIdx d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun p => Aligned (cellSide L m₀ m₁ K) p ∧
    (rootCube (m₀ := m₀) z).1 ∈ box p (L * cellSide L m₀ m₁ K)

open Classical in
/-- Those aligned `π′`-cubes containing the root cube that share a cube with `Y`. -/
noncomputable def joinCubes (z : RootIdx d L N₁ m₁ K) (Y : Set (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  (rootCubes m₀ z).filter fun p => ∃ t, Aligned (cellSide L m₀ m₁ K) t ∧
    box t (cellSide L m₀ m₁ K) ⊆ Y ∩ box p (L * cellSide L m₀ m₁ K)

open Classical in
/-- **The bridge of `Y` to the root** (`ROOT-BRIDGE`).  If the root cube is a cube of `Y`, it is
`Y`.  Otherwise it is `Y` together with all aligned `π′`-cubes `box p (L a)` that contain the root
cube and share a cube with `Y`. -/
noncomputable def bridge (z : RootIdx d L N₁ m₁ K) (Y : Set (CTorus d L N₁ m₁ K)) :
    Set (CTorus d L N₁ m₁ K) :=
  if rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y then Y
  else Y ∪ ⋃ p ∈ joinCubes m₀ z Y, box p (L * cellSide L m₀ m₁ K)

/-- The bridge cost: `L^d` added cubes, each of cost `c_G = 2 d L`. -/
noncomputable def cBr (d L : ℕ) : ℝ := (L : ℝ) ^ d * cG d L

/-- The fibre bound: the cells met by the `π′`-cubes through the root cube number at most
`L^d · L^d`, and a domain of the fibre is determined by its cells among them. -/
def nFibre (d L : ℕ) : ℕ := 2 ^ (L ^ d * L ^ d)

variable {m₀}

theorem mem_rootCubes {z : RootIdx d L N₁ m₁ K} {p : CTorus d L N₁ m₁ K} :
    p ∈ rootCubes m₀ z ↔ Aligned (cellSide L m₀ m₁ K) p ∧
      (rootCube (m₀ := m₀) z).1 ∈ box p (L * cellSide L m₀ m₁ K) := by
  classical
  simp [rootCubes]

theorem card_rootCubes_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K) :
    (rootCubes m₀ z).card ≤ L ^ d := by
  classical
  exact card_cubes_containing (cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K))
    (cellSide_pos (L := L) m₀ m₁ K) (rootCube (m₀ := m₀) z).2.1

omit [NeZero L] in
theorem cBr_nonneg : 0 ≤ cBr d L := by
  unfold cBr cG; positivity

theorem bridge_of_mem {z : RootIdx d L N₁ m₁ K} {Y : Set (CTorus d L N₁ m₁ K)}
    (h : rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y) : bridge m₀ z Y = Y := by
  simp [bridge, h]

theorem subset_bridge (z : RootIdx d L N₁ m₁ K) (Y : Set (CTorus d L N₁ m₁ K)) :
    Y ⊆ bridge m₀ z Y := by
  unfold bridge
  split_ifs
  · exact subset_rfl
  · exact Set.subset_union_left

/-- The cell of a site of a union of `π′`-cubes lies in the union. -/
theorem box_cbase_subset_of_mem (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hj : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPiPrimeUnion (m₁ := m₁) m₀ j Y) {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ Y) : box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) ⊆ Y := by
  obtain ⟨b, hb1, hb2, hb3⟩ := hY y hy
  exact (cell_subset_cube (cellSide_dvd (K := K) (m₁ := m₁) hN hj)
    (cellSide_pos (L := L) m₀ m₁ j) hb1 hb2).trans hb3

/-- **`ROOT-BRIDGE`, domain and size.**  For `Y ∈ 𝒟_K`, `bridge z Y ∈ 𝒟_K`, and
`d^cov(bridge z Y) ≤ d^cov(Y) + cBr d L`. -/
theorem bridge_isDj_and_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y) :
    IsDj m₀ K (bridge m₀ z Y) ∧
      treeLenCovOne m₀ K (bridge m₀ z Y) ≤ treeLenCovOne m₀ K Y + cBr d L := by
  classical
  unfold bridge
  split_ifs with h
  · exact ⟨hY, le_add_of_nonneg_right cBr_nonneg⟩
  · have hP : ∀ p ∈ joinCubes m₀ z Y, Aligned (cellSide L m₀ m₁ K) p ∧ ∃ t,
        Aligned (cellSide L m₀ m₁ K) t ∧
          box t (cellSide L m₀ m₁ K) ⊆ Y ∩ box p (L * cellSide L m₀ m₁ K) := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp)
      exact ⟨(mem_rootCubes.1 hp'.1).1, hp'.2⟩
    obtain ⟨h1, h2⟩ := thick_union hY (joinCubes m₀ z Y) hP
    refine ⟨h1, h2.trans ?_⟩
    have hc : ((joinCubes m₀ z Y).card : ℝ) ≤ (L : ℝ) ^ d := by
      have : (joinCubes m₀ z Y).card ≤ L ^ d :=
        (Finset.card_filter_le _ _).trans (card_rootCubes_le hN z)
      exact_mod_cast this
    have hg : 0 ≤ cG d L := by unfold cG; positivity
    unfold cBr
    nlinarith [mul_le_mul_of_nonneg_right hc hg]

theorem bridge_isDj (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y) : IsDj m₀ K (bridge m₀ z Y) :=
  (bridge_isDj_and_le hN z hY).1

theorem treeLenCovOne_bridge_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y) :
    treeLenCovOne m₀ K (bridge m₀ z Y) ≤ treeLenCovOne m₀ K Y + cBr d L :=
  (bridge_isDj_and_le hN z hY).2

/-- A site of `Y` and a site of the block `B(z)` that are equal or adjacent put the root cube
into the bridge of `Y`. -/
theorem rootCube_mem_blocksOf_bridge (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ K) {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y)
    (hmeet : (psiThick Y ∩ fineBlock z).Nonempty) :
    rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ (bridge m₀ z Y) := by
  classical
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  by_cases h : rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y
  · rw [bridge_of_mem h]; exact h
  · obtain ⟨y, hyT, hyz⟩ := hmeet
    obtain ⟨x, hxY, hnear⟩ : ∃ x ∈ Y, Near 1 (cellSide L m₀ m₁ K)
        (cbase (cellSide L m₀ m₁ K) x) (cbase (cellSide L m₀ m₁ K) y) := by
      rcases hyT with hy | ⟨x, hx, hxy⟩
      · exact ⟨y, hy, ⟨0, by simp, by funext μ; simp⟩⟩
      · exact ⟨x, hx, near_cbase_of_nbr ha ha0 (show Nbr x y from hxy)⟩
    rw [cbase_eq_rootCube (m₀ := m₀) hyz] at hnear
    obtain ⟨o, h1, h2⟩ := exists_pBase_near hL ha ha0 hnear
    have hcell := box_cbase_subset_of_mem hN (le_refl K) hY.2.1 hxY
    have hp : pBase (cellSide L m₀ m₁ K) (cbase (cellSide L m₀ m₁ K) x) o ∈ joinCubes m₀ z Y := by
      refine Finset.mem_filter.2 ⟨mem_rootCubes.2 ⟨pBase_aligned ha (aligned_cbase x) o, ?_⟩,
        cbase (cellSide L m₀ m₁ K) x, aligned_cbase x, fun w hw => ⟨hcell hw, h1 hw⟩⟩
      · have := h2 (mem_box_self (rootCube (m₀ := m₀) z).1 ha0)
        exact this
    rw [mem_blocksOf]
    unfold bridge
    simp only [h, ↓reduceIte]
    refine h2.trans fun w hw => Or.inr ?_
    exact Set.mem_iUnion₂.2 ⟨_, hp, hw⟩

end Bridge

section Fibre

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- The cells met by the `π′`-cubes through the root cube. -/
noncomputable def nearCells (m₀ : ℕ) (z : RootIdx d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun c => Aligned (cellSide L m₀ m₁ K) c ∧
    ∃ p ∈ rootCubes m₀ z, c ∈ box p (L * cellSide L m₀ m₁ K)

theorem card_nearCells_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K) :
    (nearCells m₀ z).card ≤ L ^ d * L ^ d := by
  classical
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have hsub : nearCells m₀ z ⊆ (rootCubes m₀ z).biUnion fun p =>
      Finset.univ.filter fun c : CTorus d L N₁ m₁ K =>
        Aligned (cellSide L m₀ m₁ K) c ∧ c ∈ box p (L * cellSide L m₀ m₁ K) := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := (Finset.mem_filter.1 hc).2
    obtain ⟨p, hp, hcp⟩ := hc2
    exact Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc1, hcp⟩⟩
  calc (nearCells m₀ z).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ rootCubes m₀ z, (Finset.univ.filter fun c : CTorus d L N₁ m₁ K =>
        Aligned (cellSide L m₀ m₁ K) c ∧ c ∈ box p (L * cellSide L m₀ m₁ K)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ rootCubes m₀ z, L ^ d :=
      Finset.sum_le_sum fun p hp =>
        card_aligned_in_cube ha ha0 (mem_rootCubes.1 hp).1
    _ = (rootCubes m₀ z).card * L ^ d := by simp
    _ ≤ L ^ d * L ^ d := Nat.mul_le_mul_right _ (card_rootCubes_le hN z)

open Classical in
/-- Outside the `π′`-cubes through the root cube, the bridge of `Y` is `Y`. -/
theorem mem_of_mem_bridge_of_notMem {z : RootIdx d L N₁ m₁ K} {Y : Set (CTorus d L N₁ m₁ K)}
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ bridge m₀ z Y)
    (hxn : ∀ p ∈ rootCubes m₀ z, x ∉ box p (L * cellSide L m₀ m₁ K)) : x ∈ Y := by
  unfold bridge at hx
  split_ifs at hx with h
  · exact hx
  · rcases hx with hx | hx
    · exact hx
    · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 hx
      exact absurd hxp (hxn p (Finset.mem_filter.1 hp).1)

open Classical in
/-- **A domain of the fibre is determined by its bridge and by which of the cells near the root it
contains.** -/
theorem eq_of_bridge_eq (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    {Y₁ Y₂ : Set (CTorus d L N₁ m₁ K)} (h₁ : IsDj m₀ K Y₁) (h₂ : IsDj m₀ K Y₂)
    (hb : bridge m₀ z Y₁ = bridge m₀ z Y₂)
    (hc : (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y₁) =
      (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y₂)) : Y₁ = Y₂ := by
  have ha := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have key : ∀ {Y Y' : Set (CTorus d L N₁ m₁ K)}, IsDj m₀ K Y → IsDj m₀ K Y' →
      bridge m₀ z Y = bridge m₀ z Y' →
      (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y) =
        (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y') → Y ⊆ Y' := by
    intro Y Y' hY hY' hbb hcc x hx
    by_cases hxu : ∀ p ∈ rootCubes m₀ z, x ∉ box p (L * cellSide L m₀ m₁ K)
    · exact mem_of_mem_bridge_of_notMem (hbb ▸ subset_bridge z Y hx) hxu
    · push Not at hxu
      obtain ⟨p, hp, hxp⟩ := hxu
      have hcp := cell_subset_cube ha ha0 (mem_rootCubes.1 hp).1 hxp
      have hcell := box_cbase_subset_of_mem hN (le_refl K) hY.2.1 hx
      have hmem : cbase (cellSide L m₀ m₁ K) x ∈ (nearCells m₀ z).filter
          (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y) :=
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, aligned_cbase x,
          p, hp, hcp (mem_box_self _ ha0)⟩, hcell⟩
      rw [hcc] at hmem
      exact (Finset.mem_filter.1 hmem).2 (mem_box_cbase ha0 x)
  exact Set.Subset.antisymm (key h₁ h₂ hb hc) (key h₂ h₁ hb.symm hc.symm)

open Classical in
/-- **`ROOT-FIBRE`, count.**  At most `nFibre d L = 2 ^ (L^d · L^d)` domains of a finite family of
`𝒟_K` are sent to the same rooted domain `Y′`. -/
theorem card_fibre_bridge_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ K))) (h𝒴 : ∀ Y ∈ 𝒴, IsDj m₀ K Y)
    (Y' : Set (CTorus d L N₁ m₁ K)) :
    (𝒴.filter fun Y => bridge m₀ z Y = Y').card ≤ nFibre d L := by
  have hinj : ∀ Y₁ ∈ 𝒴.filter (fun Y => bridge m₀ z Y = Y'),
      ∀ Y₂ ∈ 𝒴.filter (fun Y => bridge m₀ z Y = Y'),
      (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y₁) =
        (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y₂) → Y₁ = Y₂ := by
    intro Y₁ h1 Y₂ h2 hc
    obtain ⟨h1a, h1b⟩ := Finset.mem_filter.1 h1
    obtain ⟨h2a, h2b⟩ := Finset.mem_filter.1 h2
    exact eq_of_bridge_eq hN z (h𝒴 _ h1a) (h𝒴 _ h2a) (h1b.trans h2b.symm) hc
  calc (𝒴.filter fun Y => bridge m₀ z Y = Y').card
      ≤ (nearCells m₀ z).powerset.card := by
        refine Finset.card_le_card_of_injOn
          (fun Y => (nearCells m₀ z).filter (fun c => box c (cellSide L m₀ m₁ K) ⊆ Y))
          (fun Y _ => Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)))
          (fun Y₁ h1 Y₂ h2 hc => hinj Y₁ h1 Y₂ h2 hc)
    _ = 2 ^ (nearCells m₀ z).card := Finset.card_powerset _
    _ ≤ nFibre d L := Nat.pow_le_pow_right (by norm_num) (card_nearCells_le hN z)

open Classical in
/-- **`ROOT-FIBRE`, weighted form** (8): for `a ≥ 0`, the terms sent to `Y′` have total weight at
most `nFibre d L · e^{a cBr} · e^{-a d^cov(Y′)}`. -/
theorem fibre_weighted_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    (𝒴 : Finset (Set (CTorus d L N₁ m₁ K))) (h𝒴 : ∀ Y ∈ 𝒴, IsDj m₀ K Y)
    (Y' : Set (CTorus d L N₁ m₁ K)) {a : ℝ} (ha : 0 ≤ a) :
    ∑ Y ∈ 𝒴.filter (fun Y => bridge m₀ z Y = Y'), Real.exp (-a * treeLenCovOne m₀ K Y) ≤
      (nFibre d L : ℝ) * (Real.exp (a * cBr d L) * Real.exp (-a * treeLenCovOne m₀ K Y')) := by
  have hterm : ∀ Y ∈ 𝒴.filter (fun Y => bridge m₀ z Y = Y'),
      Real.exp (-a * treeLenCovOne m₀ K Y) ≤
        Real.exp (a * cBr d L) * Real.exp (-a * treeLenCovOne m₀ K Y') := by
    intro Y hY
    obtain ⟨hY1, hY2⟩ := Finset.mem_filter.1 hY
    have h := treeLenCovOne_bridge_le hN z (h𝒴 Y hY1)
    rw [hY2] at h
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc _ ≤ ∑ _Y ∈ 𝒴.filter (fun Y => bridge m₀ z Y = Y'),
        (Real.exp (a * cBr d L) * Real.exp (-a * treeLenCovOne m₀ K Y')) :=
      Finset.sum_le_sum hterm
    _ = (𝒴.filter fun Y => bridge m₀ z Y = Y').card •
        (Real.exp (a * cBr d L) * Real.exp (-a * treeLenCovOne m₀ K Y')) := by simp
    _ ≤ _ := by
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast card_fibre_bridge_le hN z 𝒴 h𝒴 Y'

end Fibre

section Marked

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}
  {β : Type*} [Fintype β]

open Classical in
/-- **The pairs `(b, Y)` that can contribute to the marks at the root `z`.**  Here `reads b` is the
set of sites read by the block `b` (for the landed block energy, `readSites Hm n b`) and `dom b`
the finite family of domains of its expansion.  A pair is kept when `reads b` meets the block
`B(z)` (otherwise the block energy does not see the marked tangent) and `psiThick Y`, the set `Y`
with its nearest neighbours, meets `B(z)` (the locality clause of the expansion). -/
noncomputable def markedIdx (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K) :
    Finset (β × Set (CTorus d L N₁ m₁ K)) :=
  ((Finset.univ : Finset β).biUnion fun b => (dom b).image fun Y => (b, Y)).filter fun q =>
    (reads q.1 ∩ fineBlock z).Nonempty ∧ (psiThick q.2 ∩ fineBlock z).Nonempty

omit [NeZero N₁] [NeZero L] in
theorem mem_markedIdx {reads : β → Set (CTorus d L N₁ m₁ K)}
    {dom : β → Finset (Set (CTorus d L N₁ m₁ K))} {z : RootIdx d L N₁ m₁ K}
    {b : β} {Y : Set (CTorus d L N₁ m₁ K)} :
    (b, Y) ∈ markedIdx reads dom z ↔ Y ∈ dom b ∧ (reads b ∩ fineBlock z).Nonempty ∧
      (psiThick Y ∩ fineBlock z).Nonempty := by
  classical
  simp only [markedIdx, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨b', Y', hY', rfl, rfl⟩, h⟩
    exact ⟨hY', h⟩
  · rintro ⟨hY, h⟩
    exact ⟨⟨b, Y, hY, rfl, rfl⟩, h⟩

omit [NeZero N₁] [NeZero L] in
/-- **T1.** A contributing pair has a domain whose nearest-neighbour thickening meets `B(z)`. -/
theorem psiThick_meets_of_mem_markedIdx {reads : β → Set (CTorus d L N₁ m₁ K)}
    {dom : β → Finset (Set (CTorus d L N₁ m₁ K))} {z : RootIdx d L N₁ m₁ K}
    {q : β × Set (CTorus d L N₁ m₁ K)} (h : q ∈ markedIdx reads dom z) :
    (psiThick q.2 ∩ fineBlock z).Nonempty := by
  obtain ⟨b, Y⟩ := q
  exact (mem_markedIdx.1 h).2.2

/-- **T1.** If the domain of a contributing pair itself meets `B(z)`, the root cube is one of its
cubes and the bridge is the domain itself: no enlargement is needed. -/
theorem rootCube_mem_of_meets (hN : L ^ m₀ ∣ N₁) {z : RootIdx d L N₁ m₁ K}
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y) (hm : (Y ∩ fineBlock z).Nonempty) :
    rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y ∧ bridge m₀ z Y = Y := by
  have h := rootCube_mem_blocksOf_of_isDj hN hY hm
  exact ⟨h, bridge_of_mem h⟩

/-- **T4.  The label family `𝒴_z`**: the bridges of the domains of the contributing pairs. -/
noncomputable def bridgeFamily (m₀ : ℕ) (reads : β → Set (CTorus d L N₁ m₁ K))
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (z : RootIdx d L N₁ m₁ K) :
    Finset (Set (CTorus d L N₁ m₁ K)) := by
  classical
  exact (markedIdx reads dom z).image fun q => bridge m₀ z q.2

theorem mem_bridgeFamily {reads : β → Set (CTorus d L N₁ m₁ K)}
    {dom : β → Finset (Set (CTorus d L N₁ m₁ K))} {z : RootIdx d L N₁ m₁ K}
    {Y' : Set (CTorus d L N₁ m₁ K)} :
    Y' ∈ bridgeFamily m₀ reads dom z ↔
      ∃ b, ∃ Y ∈ dom b, (reads b ∩ fineBlock z).Nonempty ∧
        (psiThick Y ∩ fineBlock z).Nonempty ∧ bridge m₀ z Y = Y' := by
  classical
  unfold bridgeFamily
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨b, Y⟩, hq, rfl⟩
    obtain ⟨h1, h2, h3⟩ := mem_markedIdx.1 hq
    exact ⟨b, Y, h1, h2, h3, rfl⟩
  · rintro ⟨b, Y, h1, h2, h3, rfl⟩
    exact ⟨(b, Y), mem_markedIdx.2 ⟨h1, h2, h3⟩, rfl⟩

/-- **T4.**  Every member of `𝒴_z` is a domain of `𝒟_K` that contains the root cube, and contains
a domain of a contributing pair; the family is the image of the contributing pairs. -/
theorem bridgeFamily_spec (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K)
    {Y' : Set (CTorus d L N₁ m₁ K)} (hY' : Y' ∈ bridgeFamily m₀ reads dom z) :
    IsDj m₀ K Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y' ∧
      ∃ b, ∃ Y ∈ dom b, Y ⊆ Y' ∧ treeLenCovOne m₀ K Y' ≤ treeLenCovOne m₀ K Y + cBr d L := by
  obtain ⟨b, Y, hY, -, hm, rfl⟩ := mem_bridgeFamily.1 hY'
  exact ⟨bridge_isDj hN z (hdom b Y hY), rootCube_mem_blocksOf_bridge hN hL z (hdom b Y hY) hm,
    b, Y, hY, subset_bridge z Y, treeLenCovOne_bridge_le hN z (hdom b Y hY)⟩

theorem bridgeFamily_isDj (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) :
    ∀ Y' ∈ bridgeFamily m₀ reads dom z, IsDj m₀ K Y' :=
  fun _ h => (bridgeFamily_spec hN hL hdom z h).1

open Classical in
/-- **T4, prefactor sum.**  For `κ₀ ≥ a_ent + 1` and `F ≥ 0`, the sum over `𝒴_z` of
`F e^{-κ₀ d^cov}` is at most `F · K₀`, with `K₀ = K0 d L κ₀` independent of the root, the scale and
the torus. -/
theorem bridgeFamily_entropy (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y) (z : RootIdx d L N₁ m₁ K) {κ0 : ℝ}
    (hκ0 : aEnt d L + 1 ≤ κ0) {F : ℝ} (hF : 0 ≤ F) :
    ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ reads dom z},
        F * Real.exp (-κ0 * treeLenCovOne m₀ K Y'.1) ≤ F * K0 d L κ0 := by
  have h := rootAnchored_entropy_thick hN (bridgeFamily m₀ reads dom z)
    (bridgeFamily_isDj hN hL hdom z) hκ0 z hF
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun Y' _ => ?_)) h
  simp only [(bridgeFamily_spec hN hL hdom z Y'.2).2.1, ↓reduceIte]

section Anchor

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {BS : ProdSplit ν d L N₁ m₁ K m₀}
  {W : ℝ → Ω → ℂ} {f : RootIdx d L N₁ m₁ K → ℝ → Ω → ℂ}

/-- **T4, anchor.**  If every mark label of `I z` is a member of the family `𝒴_z`, a non-zero
coefficient of `I z` has the root cube of `z` in `T`: the hypothesis of
`anchor_of_labels` holds for marks labelled by `𝒴_z`. -/
theorem anchor_of_bridgeFamily (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    {reads : β → Set (CTorus d L N₁ m₁ K)} {dom : β → Finset (Set (CTorus d L N₁ m₁ K))}
    (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y)
    (I : ∀ z : RootIdx d L N₁ m₁ K, InterpMarks ν BS W (f z))
    (hlab : ∀ (z : RootIdx d L N₁ m₁ K) i,
      (I z).Lab.ysite ((I z).y0 i) ∈ bridgeFamily m₀ reads dom z)
    (z : RootIdx d L N₁ m₁ K) {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) m₀ K Set.univ)} (h : interpCoeff (I z) T ≠ 0) : rootCube z ∈ T :=
  anchor_of_labels I (fun z i => (bridgeFamily_spec hN hL hdom z (hlab z i)).2.1) z h

end Anchor

end Marked

end Balaban.Fluctuation
