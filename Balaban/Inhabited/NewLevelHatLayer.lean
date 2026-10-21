/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelHatLocal
public import Balaban.Fluctuation.OldTermsLiftHat
public import Balaban.Inhabited.ClassHatWitness
public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSpec

/-!
# The layer of a class generating set near its polymer

For a class generating set `G = Tm.gs j X` with the hat specification (`HatSpec`, the cast local
set `𝔹_j(X̂)`), every site within sup-distance `2 L^{j+m₁+s}` of `X` lies in the top layer
`Ω_j(G)` (`hatSpec_mem_Ω_of_near`, through `HatSpec.eq_castLocalB` and `hatLocal_margin_at`), and,
when no layer of `G` is above `j`, in the layer `j` (`hatSpec_mem_layer_of_near`).  These give the
region of the pullback of the composed data of a label: the forward stars of the sites of `X` at
the block scale `L^j` lie in the layer `j` of `Tm.gs j X`.  `gsSpecStrong_hatGSOf`: the generating
set `hatGSOf m₀ (k+1) X` of the new level (ruling R13) has the strong specification of `X`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Balaban.LargeField

/-- A site of the top layer `Ω_j` of a generating set without layers above `j` lies in the layer
`j`. -/
theorem mem_layer_of_mem_Ω_of_le {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} {j : ℕ} (hj1 : 1 ≤ j) (hjK : j ≤ K)
    (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) {y : Torus d (N₀ * L ^ K)} (hy : y ∈ G.Ω j) :
    y ∈ G.layer j := by
  refine G.mem_layer.2 ⟨hy, fun hy1 => ?_⟩
  have hy0 : y ∈ G.Ω 1 := G.Ω_antitone le_rfl hj1 (by omega) hy
  obtain ⟨-, -, hl⟩ := G.layerIndex_spec hy0
  have hm := hnj y hy0
  have := G.Ω_antitone (by omega) (by omega : G.layerIndex y + 1 ≤ j + 1) (by omega) hy1
  exact (G.mem_layer.1 hl).2 this

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The top layer of a class generating set near its polymer**: with the hat specification at the
cube exponent `s = hatScale L m₁ ϱ < m₀` and `L ≥ 3`, every site within sup-distance
`2 L^{j+m₁+s}` of a site of `X` lies in `Ω_j(G)`. -/
theorem hatSpec_mem_Ω_of_near {m₀ j : ℕ} (hL : 3 ≤ L) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (h : HatSpec m₀ j X G)
    (hlt : hatScale L m₁ ϱ < m₀) (hs : ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)))
    (hj : j ≤ k + 1) {N₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁)
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ X)
    (hxy : supDist x y ≤ 2 * L ^ (j + (m₁ + hatScale L m₁ ϱ))) : y ∈ G.Ω j := by
  rw [Fluctuation.HatSpec.eq_castLocalB h hlt hs hj hc]
  exact hatLocal_margin_at hlt hL hc hs hj (subset_refl X) x hx y hxy

/-- **The layer `j` of a class generating set near its polymer**: under the hypotheses of
`hatSpec_mem_Ω_of_near`, when no layer of `G` is above `j`, every site within sup-distance
`2 L^{j+m₁+s}` of a site of `X` lies in the layer `j` of `G`. -/
theorem hatSpec_mem_layer_of_near {m₀ j : ℕ} (hL : 3 ≤ L) {X : Set (CTorus d L N₁ m₁ (k + 1))}
    {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (h : HatSpec m₀ j X G)
    (hlt : hatScale L m₁ ϱ < m₀) (hs : ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)))
    (hj1 : 1 ≤ j) (hj : j ≤ k + 1) (hnj : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) {N₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁)
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ X)
    (hxy : supDist x y ≤ 2 * L ^ (j + (m₁ + hatScale L m₁ ϱ))) : y ∈ G.layer j :=
  mem_layer_of_mem_Ω_of_le hj1 hj hnj (hatSpec_mem_Ω_of_near hL h hlt hs hj hc hx hxy)

/-- **The strong specification of the cast local set `𝔹_{k+1}(X̂)`** (top level of the torus): `X`
lies in the top layer (`hatLocal_margin`), no layer above `k + 1`. -/
theorem gsSpecStrong_castG_hat {m₀ s : ℕ} (hs : s < m₀) (hL : 3 ≤ L) {N₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ (m₁ + s) = N₁ * L ^ m₁) (hsep : ϱ ≤ LargeField.minSep L (L ^ (m₁ + s)))
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    GsSpecStrong (k + 1) le_rfl X (castG hc (localB (k + 1) (le_refl (k + 1))
      {x' : CTorus d L N₁' (m₁ + s) (k + 1) |
        (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ hatSet m₀ (k + 1) X} hsep)) := by
  set G := castG hc (localB (k + 1) (le_refl (k + 1))
      {x' : CTorus d L N₁' (m₁ + s) (k + 1) |
        (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ hatSet m₀ (k + 1) X} hsep) with hG
  have hlay : ∀ z ∈ X, z ∈ G.layer (k + 1) := fun z hz => by
    refine G.mem_layer.2 ⟨?_, by rw [G.top]; exact Finset.notMem_empty _⟩
    exact hatLocal_margin hs hL hc hsep (subset_refl X) z hz z (by rw [supDist_self]; omega)
  exact GsSpecCore.toStrong (by omega) le_rfl
    { subset := fun z hz => G.layer_subset (by omega) le_rfl (hlay z hz)
      noAbove := castG_noAbove hc (fun i hi => localB_Ω_of_gt hi)
      topLayer := hlay }

/-- **The generating set of the new level has the strong specification** (`gs_strong` of the
assembly of A4-1b): `hatGSOf m₀ (k+1) X` is `𝔹_{k+1}(X̂)` (`gsSpecStrong_castG_hat`) or the
whole-level set (`levelGS_strong`). -/
theorem gsSpecStrong_hatGSOf {m₀ : ℕ} (hL : 3 ≤ L) (hlt : hatScale L m₁ ϱ < m₀)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    GsSpecStrong (k + 1) le_rfl X (hatGSOf (ϱ := ϱ) m₀ (k + 1) le_rfl X) := by
  unfold hatGSOf
  split_ifs with h
  · haveI := (exists_finer_torusG (L := L) m₁ _ h.1).choose_spec.choose
    exact gsSpecStrong_castG_hat hlt hL _ h.2 X
  · exact levelGS_strong (by omega) le_rfl X

end Balaban.Inhabited
