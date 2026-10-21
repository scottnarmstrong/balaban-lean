/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgLiftC
public import Balaban.SmallField.Def6AvgDens

/-!
# Limits of sums over shapes: the class-free part

The thermodynamic limit of a whole-torus coefficient (P1 p. 147 (3.110)) is a limit of a sum over
the shapes `X' ∋ y` that are good on the `n`-th torus of the sequence `torusSeq L m₀ n`.  This file
contains the two statements of that argument that do not read the class:

* `finsum_polysAt_eq_shAt`: for `n` so large that the block corner of `y` is centred, a sum over
  the polymers of `𝒟_j` through the block corner of `y` on the `n`-th torus is the sum over the
  shapes `ShAt` of the values at the lifts `Ypoly j X'` (every polymer of the torus is such a
  lift);
* `exists_tendsto_shapeSum`: if the shape values `cN n X'` agree on any two good tori (torus
  independence of the terms) and obey the bound `C e^{-κ d_j}` of the size on the `n`-th torus
  with `κ > a_ent + 1`, then the sums over the shapes converge.  The limit is the sum over the
  polymers of `T∞` of the common values; the limit function is built by choice from the agreement,
  so neither the infinite-volume terms nor the cut-off `GE` are used.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter

section Shapes

variable {d L m₁ k : ℕ} [NeZero L]

/-- **A sum over the polymers of the torus through a block corner is the sum over the good shapes.**
For `y` with `unlift (blockPt y) = y` on the `n`-th torus, every polymer of `𝒟_j` through the
block corner of `y` is `Ypoly j X'` for exactly one shape `X' ∋ y` that is good on the torus. -/
theorem finsum_polysAt_eq_shAt {m₀ j : ℕ} (hjk : j ≤ k) (y : Site d) (n : ℕ)
    (hyu : unlift (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j (blockPt j y) = y)
    (f : Set (CTorus d L (torusSeq L m₀ n) m₁ k) → ℂ) :
    (haveI : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
      ∑ᶠ X ∈ polysAt m₀ j (blockPt j y), f X) =
      ∑ᶠ X' ∈ ShAt (d := d) L m₁ k m₀ j y n,
        f (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X') := by
  classical
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  rw [polysAt_eq_image hjk (torusSeq_dvd m₀ n) (blockPt j y)]
  rw [finsum_mem_image (g := fun X' => Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁)
    (k := k) j X') (f := f)
    (fun A hA B hB h => ypoly_injOn_nonWind hjk hA.2.1 hB.2.1 h)]
  rw [hyu]
  have hset : {X' : Finset (Site d) | y ∈ X' ∧
      NonWind L (torusSeq L m₀ n) m₁ k j X' ∧
      IsPolyDom (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) m₀ j
        (Ypoly (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j X')} =
      ShAt (d := d) L m₁ k m₀ j y n := by
    ext X'
    simp only [Set.mem_ofPred_eq, ShAt, GoodAt]
  rw [hset]

/-- **The limit of a sum over shapes exists.**  Let `cN n X'` be a value attached to the shape `X'`
on the `n`-th torus, with (i) `cN n X' = cN n' X'` whenever `X' ∋ y` is good on both tori and
(ii) `‖cN n X'‖ ≤ C e^{-κ d_j(X')}` (the covering size on the `n`-th torus) for `X' ∋ y` good on the
`n`-th torus, `κ > a_ent + 1`.  Then the sums over the good shapes through `y` converge. -/
theorem exists_tendsto_shapeSum {m₀ j : ℕ} (hjk : j ≤ k) {κ : ℝ} (hκ : aEnt d L + 1 < κ)
    (y : Site d) (cN : ℕ → Finset (Site d) → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hagree : ∀ n n' X', y ∈ X' → GoodAt L m₁ k m₀ j X' n → GoodAt L m₁ k m₀ j X' n' →
      cN n X' = cN n' X')
    (hbound : ∀ n X', y ∈ X' → GoodAt L m₁ k m₀ j X' n →
      ‖cN n X'‖ ≤ C * Real.exp (-κ * sizeSeq L m₁ k m₀ j X' n)) :
    ∃ ℓ : ℂ, Tendsto (fun n => ∑ᶠ X' ∈ ShAt (d := d) L m₁ k m₀ j y n, cN n X') atTop (nhds ℓ) := by
  classical
  have hκ0 : 0 ≤ κ := by linarith [aEnt_nonneg d L]
  set ainf : Finset (Site d) → ℂ := fun X' =>
    if h : y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' then
      cN (Classical.choose (exists_goodAt (L := L) (m₁ := m₁) (k := k) h.2)) X' else 0 with hainf
  have hval : ∀ X', y ∈ X' → InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' → ∀ n,
      GoodAt L m₁ k m₀ j X' n → ainf X' = cN n X' := by
    intro X' hy hX n hn
    have hc : y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' := ⟨hy, hX⟩
    simp only [hainf, hc, and_self, dite_true]
    exact hagree _ _ X' hy (Classical.choose_spec (exists_goodAt (L := L) (m₁ := m₁) (k := k) hX))
      hn
  refine ⟨∑' X', ainf X', tendsto_shapeSum (m₀ := m₀) (m₁ := m₁) (j := j) hjk (κ := κ) hκ y cN
    ainf hC ?_ hbound ?_ ?_⟩
  · intro n X' hy hgood hsz
    exact (hval X' hy (infPoly_of_small hjk hy hgood hsz) n hgood).symm
  · intro X' hy hX
    obtain ⟨n₀, hn₀⟩ := exists_goodAt (L := L) (m₁ := m₁) (k := k) hX
    rw [hval X' hy hX n₀ hn₀]
    refine bound_dInf hn₀ (norm_nonneg _) hκ0 fun n hgood => ?_
    rw [hagree n₀ n X' hy hn₀ hgood]
    exact hbound n X' hy hgood
  · intro X' h
    simp only [hainf, h, dite_false]

end Shapes

end Balaban.SmallField.Def6
