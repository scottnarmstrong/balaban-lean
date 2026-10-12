/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Terms
public import Balaban.Background.Data
public import Balaban.Localization.Cover

/-!
# The definitions `GsSpecCore`, `GsSpecStrong` of the specification of the local generating set

Early file (imported by `Def6v2`): the specification of the generating set `G_{j,X}` attached to a
polymer, and the whole-level set `levelGS j` satisfying it (`levelGS_strong`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

section Core

variable {d L N₀ k : ℕ} [NeZero L] [NeZero N₀] {ϱ : ℝ}

/-- **The core of the strong specification of the local set `𝔹_j(X)`** on an arbitrary torus
(P5 (2.10)-(2.11), LOC (4.4)-(4.8)): `X ⊆ Ω₁(G)`, `G` has no layer above `j`, and `X` lies in the
top layer `j` of `G`. -/
structure GsSpecCore (j : ℕ) (X : Set (Torus d (N₀ * L ^ k))) (G : GeneratingSet d L N₀ k ϱ) :
    Prop where
  subset : X ⊆ (G.Ω 1 : Set (Torus d (N₀ * L ^ k)))
  noAbove : ∀ i, j < i → G.Ω i = ∅
  topLayer : ∀ z ∈ X, z ∈ G.layer j

theorem GsSpecCore.layerIndex_eq {j : ℕ} {X : Set (Torus d (N₀ * L ^ k))}
    {G : GeneratingSet d L N₀ k ϱ} (h : GsSpecCore j X G) (hj1 : 1 ≤ j) (hjk : j ≤ k) {z}
    (hz : z ∈ X) : G.layerIndex z = j :=
  G.layerIndex_eq hj1 hjk (h.topLayer z hz)

theorem GsSpecCore.layerIndex_le {j : ℕ} {X : Set (Torus d (N₀ * L ^ k))}
    {G : GeneratingSet d L N₀ k ϱ} (h : GsSpecCore j X G) {z} (hz : z ∈ G.Ω 1) :
    G.layerIndex z ≤ j := by
  obtain ⟨-, -, hl⟩ := G.layerIndex_spec hz
  by_contra hlt
  push Not at hlt
  have := (G.mem_layer.1 hl).1
  rw [h.noAbove _ hlt] at this
  exact absurd this (Finset.notMem_empty _)

end Core

section Strong

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The strong specification `GsSpecStrong` of the generating set `G = G_{j,X}`** of a level-`j`
polymer `X` on the fine torus of index `k`: the two fields of `Def6.IsSF.gs_spec`
(`X ⊆ Ω₁(G)`, no layer above `j`), `X` lies in the top layer `j` of `G`, and the layer indices and
`j`-blocks of `G` on `X` are those of the whole-level set `levelGS j`.  (Blocks do not depend on the
generating set, so the last field is automatic; on the neighbours of `X` the layers of `G` are
`≤ j`, `GsSpecStrong.layerIndex_le`, and the sites of `Ω₁(G)` adjacent to `X` or its collar form
the data sites of `G`, `GsSpecStrong.adj_dataSites`.) -/
structure GsSpecStrong (j : ℕ) (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k))
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) : Prop extends GsSpecCore j X G where
  layerEq : ∀ z ∈ X, G.layerIndex z =
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk).layerIndex z
  blkEq : ∀ z ∈ X, G.blk j z =
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk).blk j z

theorem levelGS_layerIndex' {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) :
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk).layerIndex x = j :=
  GeneratingSet.layerIndex_eq _ hj1 hjk
    ((GeneratingSet.mem_layer _).2 ⟨by simp [levelGS], by simp [levelGS]⟩)

/-- The core specification implies the strong one on the fine torus. -/
theorem GsSpecCore.toStrong {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {X : Set (CTorus d L N₁ m₁ k)}
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (h : GsSpecCore j X G) :
    GsSpecStrong j hjk X G where
  toGsSpecCore := h
  layerEq := fun z hz => by rw [h.layerIndex_eq hj1 hjk hz, levelGS_layerIndex' hj1 hjk]
  blkEq := fun _ _ => rfl

/-- The whole-level set satisfies the strong specification for every `X`. -/
theorem levelGS_strong {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    GsSpecStrong j hjk X
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk) :=
  GsSpecCore.toStrong hj1 hjk
    { subset := fun x _ => by simp [levelGS, hj1]
      noAbove := fun i hi => by
        have : ¬ i ≤ j := by omega
        simp [levelGS, this]
      topLayer := fun z _ =>
        (GeneratingSet.mem_layer _).2 ⟨by simp [levelGS], by simp [levelGS]⟩ }

end Strong

end Balaban.SmallField.GsSpec
