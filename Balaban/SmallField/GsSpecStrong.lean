/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.GsSpecDef
public import Balaban.SmallField.Def6v2Inhabited
public import Balaban.LargeField.Background.MinimalGenSet

/-!
# The strong specification `GsSpecStrong` of the local generating set `G_{j,X}`

`GsSpecCore` (on any torus) and `GsSpecStrong` (on the fine torus, with the agreement with
`levelGS j`), the whole-level set and P3's minimal generating set `minimalGenSet` satisfy it
(`levelGS_strong`, `minimalGenSet_core`, `minimalGenSet_top`), with a non-trivial witness
(`gsSpecStrong_minimal_witness`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

section Strong

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {j : ℕ} {hjk : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}

theorem GsSpecStrong.layerIndex_le (h : GsSpecStrong j hjk X G) {z} (hz : z ∈ G.Ω 1) :
    G.layerIndex z ≤ j := h.toGsSpecCore.layerIndex_le hz

/-- The neighbours of `X` are data sites of `G`. -/
theorem GsSpecStrong.adj_dataSites (h : GsSpecStrong j hjk X G) {z w : CTorus d L N₁ m₁ k}
    (hz : z ∈ X) (hzw : Adj z w) : w ∈ dataSites G := by
  rw [mem_dataSites]
  by_cases hw : w ∈ G.Ω 1
  · exact Or.inl hw
  · exact Or.inr (mem_collar_of_adj G (h.subset hz) hw hzw)

/-- The local set `G` (no layer above `j ≤ k'`) precedes the top level-`k'` set. -/
theorem precedes_levelGS (h : GsSpecStrong j hjk X G) {k' : ℕ} (hjk' : j ≤ k') (hk : k' ≤ k) :
    Precedes G
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) k' hk) :=
  fun i _ _ x hx => by
    by_cases hi : i ≤ k'
    · simp [levelGS, hi]
    · rw [h.noAbove i (by omega)] at hx
      simp at hx

end Strong


section Minimal

open Balaban.LargeField

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- **The minimal generating set `𝔹_j(X)` of P3 (4.4)-(4.6) satisfies the core specification**:
for a set `X` of sites that is a union of `𝒞_j`-cubes (a polymer is one, P3 (4.4)) and
`1 ≤ j ≤ q`, `X ⊆ Ω₁(𝔹_j(X))`, `Ω_i(𝔹_j(X)) = ∅` for `i > j`, and `X = Ω_j(𝔹_j(X))` lies in the
top layer `j`. -/
theorem minimalGenSet_core {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ q)
    (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    (hX : ∀ x ∈ X, ∀ y, fineCubeIdx M1 N₁ L q j y = fineCubeIdx M1 N₁ L q j x → y ∈ X) :
    GsSpecCore j (X : Set (Torus d (M1 * N₁ * L ^ q))) (minimalGenSet hj X) where
  subset := fun z hz => by
    have h1 : z ∈ (minimalGenSet hj X).Ω j := by
      rw [minimalGenSet_Ω, minLayer_self, mem_cubeInterior]
      intro y hy
      exact hX z hz y hy
    exact (minimalGenSet hj X).Ω_antitone le_rfl hj1 (by omega) h1
  noAbove := fun i hi => by
    rw [minimalGenSet_Ω]
    exact minLayer_of_gt X hi
  topLayer := fun z hz => by
    refine ((minimalGenSet hj X).mem_layer).2 ⟨?_, ?_⟩
    · rw [minimalGenSet_Ω, minLayer_self, mem_cubeInterior]
      intro y hy
      exact hX z hz y hy
    · rw [minimalGenSet_Ω, minLayer_of_gt X (Nat.lt_succ_self j)]
      simp

/-- The top layer of the minimal set is exactly `X`: `Ω_j(𝔹_j(X)) = X`. -/
theorem minimalGenSet_top {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q)))
    (hX : ∀ x ∈ X, ∀ y, fineCubeIdx M1 N₁ L q j y = fineCubeIdx M1 N₁ L q j x → y ∈ X) :
    (minimalGenSet hj X).Ω j = X := by
  rw [minimalGenSet_Ω, minLayer_self]
  refine Finset.Subset.antisymm (cubeInterior_subset X) fun z hz => ?_
  rw [mem_cubeInterior]
  exact fun y hy => hX z hz y hy

end Minimal

section Witness

open Balaban.LargeField

/-- **A non-trivial `GsSpecStrong` witness for the minimal generating set** (`d = 1`, `L = 2`,
fine torus `ℤ/4` of the class with `N₁ = 1`, `m₁ = 0`, `k = 2`, `j = 1`): `X` is the `𝒞₁`-cube
of `0` (two of the four sites; nonempty and not the whole torus), and `G = 𝔹₁(X)` is its minimal
generating set, whose `Ω₁` is `X` itself (not the whole-level set `levelGS 1`). -/
theorem gsSpecStrong_minimal_witness :
    ∃ (X : Set (CTorus 1 2 1 0 2)) (G : GeneratingSet 1 2 (1 * 2 ^ 0) 2 (minSep 2 1)),
      X.Nonempty ∧ X ≠ Set.univ ∧ G.Ω 1 ≠ Finset.univ ∧
        GsSpecStrong (d := 1) (L := 2) (N₁ := 1) (m₁ := 0) (k := 2) (ϱ := minSep 2 1)
          1 (by norm_num) X G := by
  classical
  let X0 : Finset (Torus 1 (1 * 1 * 2 ^ 2)) :=
    Finset.univ.filter fun x => fineCubeIdx 1 1 2 2 1 x = fineCubeIdx 1 1 2 2 1 0
  have hX : ∀ x ∈ X0, ∀ y, fineCubeIdx 1 1 2 2 1 y = fineCubeIdx 1 1 2 2 1 x → y ∈ X0 := by
    intro x hx y hy
    simp only [X0, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hy, hx]
  have hcore := minimalGenSet_core (d := 1) (M1 := 1) (N₁ := 1) (L := 2) (q := 2)
    (j := 1) le_rfl (by norm_num) X0 hX
  have h0 : (0 : Torus 1 (1 * 1 * 2 ^ 2)) ∈ X0 := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have h2 : (fun _ => (2 : ZMod 4) : Torus 1 (1 * 1 * 2 ^ 2)) ∉ X0 := by
    simp only [X0, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold fineCubeIdx
    decide
  refine ⟨(X0 : Set (Torus 1 (1 * 1 * 2 ^ 2))), minimalGenSet (by norm_num) X0, ⟨0, h0⟩, ?_, ?_,
    hcore.toStrong le_rfl (by norm_num)⟩
  · intro h
    exact h2 (by simpa using (h ▸ Set.mem_univ _ : _ ∈ (X0 : Set (Torus 1 (1 * 1 * 2 ^ 2)))))
  · intro h
    have e := minimalGenSet_top (d := 1) (M1 := 1) (N₁ := 1) (L := 2) (q := 2) (j := 1)
      (by norm_num) X0 hX
    exact h2 (e ▸ h ▸ Finset.mem_univ _)

end Witness

end Balaban.SmallField.GsSpec
