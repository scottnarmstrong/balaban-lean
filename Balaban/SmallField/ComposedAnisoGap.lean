/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomXiC
public import Balaban.SmallField.Def6InfExpand

/-!
# What the anisotropic data hypothesis at the composed data still needs (A4-1b (ii), P-2)

The bound of the irrelevant parts at the data the step reads (P1 (3.128); the composed charts
`composedChart`) is available, for the labels `X ≠ □(y)` and for the cell label through
`norm_filed_le_power`, under the anisotropic data hypothesis `DataHypAniso` of the datum pulled back
at the centre `y` (`σ = C₀ s`, `ε = ε_k`).  The landed producer of that hypothesis,
`xiC_dataHypAniso_of_levelGS`, composes the data of a chart into the **whole-level** set `𝔹_j`
(`levelGS j`), from a chart at the level of the torus.  Two of its hypotheses fail for the data
composed into the local generating sets of the class (ruling R13), and this file proves that they
fail:

* `not_forall_pullback_mem`: the pullback `x ↦ y + ibase j x` covers every `L^j`-aligned site of
  the torus, so the hypothesis of `ScaledPsiC.dataHypAniso_of_pullback` that every pulled-back site
  lies in `Ω₁` (in the top layer `j`) of the target generating set fails as soon as one aligned
  site lies outside `Ω₁` — for the local set `Tm.gs j X` of a polymer on a large torus.  The
  bounds that consume the hypothesis (`irrelTorus_bound_of_dataHyp_of_threshold`,
  `norm_filed_le_power`) ask it on the whole pullback as well, while the irrelevant part reads the
  field only on `X ∪ st₊(y)` (`irrelTorus_congr`);
* `not_scaleGap_of_lower_source`: the sharp composition estimate behind the producer
  (`xiC_scaledComposition_square_sharp`, `HypS`) ties the scale ratio to the level of the torus,
  `L^j = θ L^K`; with a source generating set whose top layer at the site is `K - 1` (the local
  level-`k` sets `Gk` of the step, on the torus of level `K = k + 1`) the scale gap
  `ℓ_{Gj} ≤ θ ℓ_G` fails, so the estimate does not apply to the composed charts of the step (it
  applies with the source `𝔹_{k+1}` itself, at `θ = L^{j-k-1}`).
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6

section Pullback

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The pullback at `y` reaches every aligned site**: if an `L^j`-aligned site `z` (with
`z - y` aligned) lies outside `Ω₁` of a generating set `G`, then not every pulled-back site
`y + ibase j x` lies in `Ω₁(G)`.  The hypothesis `hsite` of `ScaledPsiC.dataHypAniso_of_pullback`
therefore holds only for targets whose `Ω₁` contains every aligned site (the whole-level sets). -/
theorem not_forall_pullback_mem {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ} (hjk : j ≤ k)
    {y z : CTorus d L N₁ m₁ k} (hzy : Aligned (L ^ j) (z - y)) (hz : z ∉ G.Ω 1) :
    ¬ ∀ x : Site d, y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ G.Ω 1 := by
  intro h
  have h1 := h (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y))
  rw [ibase_unlift hjk hzy, add_sub_cancel] at h1
  exact hz h1

end Pullback

section Gap

variable {d L N₀ K : ℕ} [NeZero L] [NeZero N₀] {ϱ ϱ' : ℝ}

/-- **The scale gap fails for a source one level below the torus**: if `L ≥ 2`,
`L^j = θ L^{k+1}` (the scale ratio of `HypS` on the torus of level `k + 1`) and a site `x` of
`Ω₁(Gj)` lies in the layer `j` of the target `Gj` and in the layer `k` of the source `G`, then
`ScaleGap Gj G θ` (`ℓ_{Gj}(x) ≤ θ ℓ_G(x)`) fails: `L^j ≤ θ L^k = L^j / L`. -/
theorem not_scaleGap_of_lower_source {Gj : GeneratingSet d L N₀ K ϱ}
    {G : GeneratingSet d L N₀ K ϱ'} (hL : 2 ≤ L) {j k : ℕ} {θ : ℝ}
    (hjθ : (L : ℝ) ^ j = θ * (L : ℝ) ^ (k + 1)) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ Gj.Ω 1)
    (hxj : Gj.layerIndex x = j) (hxk : G.layerIndex x = k) : ¬ ScaleGap Gj G θ := by
  intro h
  have h1 := h x hx
  unfold GeneratingSet.spacing at h1
  rw [hxj, hxk] at h1
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hpos : 0 < (L : ℝ) ^ j := by positivity
  have hθk : 0 < θ * (L : ℝ) ^ k := by
    have e : θ * (L : ℝ) ^ (k + 1) = θ * (L : ℝ) ^ k * L := by rw [pow_succ]; ring
    rw [e] at hjθ
    nlinarith
  have e : θ * (L : ℝ) ^ (k + 1) = θ * (L : ℝ) ^ k * L := by rw [pow_succ]; ring
  rw [hjθ, e] at h1
  nlinarith

end Gap

end Balaban.SmallField
