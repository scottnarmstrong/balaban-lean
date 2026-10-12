/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33Level
public import Balaban.Fluctuation.TraceEntropy
public import Balaban.Fluctuation.SizeModG1
public import Balaban.Fluctuation.Interaction

/-!
# Counting sites and blocks in a polymer domain (FLUCTUATION Lemma 1.2 (G1) for `Y[𝒞]`)

The polymer domains `Y[𝒞]` of the localization expansion of a level generating set are
multiscale polymer domains (`polymerDomain_isMultiDom`); for a generating set of level `lev` they
are domains `𝒟_{lev}` of the single scale, so (G1) bounds their number of sites and of
`(n+1)`-blocks by `1 + d^cov`:

* `ncard_polyDom_le`: `|Y| ≤ c₁ (L^{lev})^d M^d (1 + d^cov_{lev}(Y))`, `M = L^{m₀ + m₁}`;
* `card_blocks_polyDom_le`: the number of blocks `B_{n+1}(z) ⊆ Y` is at most
  `c₁ M^d (1 + d^cov_{n+1}(Y))`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ lev : ℕ}

/-- A multiscale polymer domain of a level generating set is a domain `𝒟_{lev}`. -/
theorem isDj_of_isMultiDom (hG : IsLevel G lev) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsMultiDom G m₀ Y) : IsDj m₀ lev Y := by
  obtain ⟨h1, hK⟩ := hG.bounds
  obtain ⟨-, hconn, 𝒦, W, E, hch, hc, hWY, -⟩ := hY
  refine ⟨?_, fun z hz => ?_, hconn⟩
  · obtain ⟨w, hw⟩ := hc.1
    exact ⟨w, hWY hw⟩
  · obtain ⟨b, hb, hzb⟩ := (hch lev h1 hK).2 z hz (Finset.mem_coe.2 (hG.mem_layer z))
    exact ⟨b, (hch lev h1 hK).1 b hb |>.1, hzb, (hch lev h1 hK).1 b hb |>.2.1⟩

/-- **(G1) for a polymer domain of a level generating set**: with `M = L^{m₀+m₁}`,
`|Y| ≤ c₁ (L^{lev})^d M^d (1 + d^cov_{lev}(Y))`. -/
theorem ncard_le_of_isMultiDom (hG : IsLevel G lev) (hN : L ^ m₀ ∣ N₁)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsMultiDom G m₀ Y) :
    (Y.ncard : ℝ) ≤ c1 d L * ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      (1 + treeLenCov G m₀ Y) := by
  have h := G1_card hN hG.bounds.2 (isDj_of_isMultiDom hG hY)
  rw [← treeLenCov_eq_treeLenCovOne hG] at h
  have hc : ((cellSide L m₀ m₁ lev : ℕ) : ℝ) ^ d =
      ((L : ℝ) ^ lev) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by
    unfold cellSide
    push_cast
    rw [← mul_pow, ← pow_add]
    congr 2
    ring
  rw [hc] at h
  linarith

end Count

section Blocks

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- Every block `B_{n+1}(z)` has exactly `(L^{n+1})^d` sites. -/
theorem card_blockSites_eq {n : ℕ} (hp : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    (blockSites d L N₁ m₁ K n z).card = (L ^ (n + 1)) ^ d := by
  have h := card_blockFibre (d := d) (N := L ^ (n + 1)) (m := N₁ * L ^ m₁ * L ^ (K - (n + 1)))
    (ℓ := N₁ * L ^ m₁ * L ^ K) (side_eq hp) z
  rw [← h]
  rfl

/-- The number of blocks contained in a set is at most `|Y| / (L^{n+1})^d`. -/
theorem card_blocks_mul_le {n : ℕ} (hp : n + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (S : Finset (Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))))
    (hS : ∀ z ∈ S, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ Y) :
    S.card * (L ^ (n + 1)) ^ d ≤ Y.ncard := by
  classical
  have hdisj : (↑S : Set _).PairwiseDisjoint (blockSites d L N₁ m₁ K n) := by
    intro z hz z' hz' hne
    refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
    have e1 := (Finset.mem_filter.1 hx).2
    have e2 := (Finset.mem_filter.1 hx').2
    rw [← e1, ← e2]
  have hcard : (S.biUnion (blockSites d L N₁ m₁ K n)).card = S.card * (L ^ (n + 1)) ^ d := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl fun z _ => card_blockSites_eq hp z]
    simp
  rw [← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => by
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
    exact hS z hz hxz) (Set.toFinite _)

end Blocks

end Balaban.Fluctuation
