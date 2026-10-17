/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidDataZ
public import Balaban.Background.BlockGeometry

/-!
# The multiscale data `Ψ` of a window from a field on the blocks (W944)

`notes/phase1/LF4R-PLAN.md` §8.5.  `exists_bgData_of_field`: for a generating set `G` at level `m' + 1` and a
field `fldv s y` on the blocks of the history, the field `Ψ x = fldv n (block_n x)` (`n = layerIndex x`) on `Ω₁(G)` and `0`
elsewhere, with `h = 0`, is a real datum `BgData G N` (`Ψ` is constant on the blocks of every layer).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Bg

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {m' : ℕ}

open Classical in
theorem exists_bgData_of_field (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) {N : ℕ} {ϱ : ℝ}
    (G : GeneratingSet S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (fldv : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N)) :
    ∃ D : BgData G N, D.IsReal ∧ ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i =
      ((fldv (G.layerIndex x) (jBlock S.d S.L (M * n K) K (G.layerIndex x)
        (torusCast (fine_eq_top hnn hmK).symm x)) i : ℝ) : ℂ) := by
  let Ψ : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) → Fin N → ℂ := fun x i =>
    if x ∈ G.Ω 1 then ((fldv (G.layerIndex x) (jBlock S.d S.L (M * n K) K (G.layerIndex x)
      (torusCast (fine_eq_top hnn hmK).symm x)) i : ℝ) : ℂ) else 0
  have hlc : IsLayerConstant G Ψ := by
    intro q hq1 hqk x hx x' hx'
    have hx'l : x' ∈ G.layer q := mem_layer_of_mem_blk G hq1 hqk hx hx'
    have hb : jBlock S.d S.L (M * n (m' + 1)) (m' + 1) q x' = jBlock S.d S.L (M * n (m' + 1)) (m' + 1) q x :=
      GeneratingSet.mem_blk.1 hx'
    have hb' := jBlock_torusCast (d := S.d) (L := S.L) (N₀ := M * n (m' + 1)) (N₀' := M * n K)
      (k := m' + 1) (K := K) (j := q) hqk (by omega) (fine_eq_top hnn hmK).symm
      (blk_eq_top hnn hmK hqk) x'
    have hb'' := jBlock_torusCast (d := S.d) (L := S.L) (N₀ := M * n (m' + 1)) (N₀' := M * n K)
      (k := m' + 1) (K := K) (j := q) hqk (by omega) (fine_eq_top hnn hmK).symm
      (blk_eq_top hnn hmK hqk) x
    have hbK : jBlock S.d S.L (M * n K) K q (torusCast (fine_eq_top hnn hmK).symm x') =
        jBlock S.d S.L (M * n K) K q (torusCast (fine_eq_top hnn hmK).symm x) := by
      rw [hb', hb'', hb]
    have hi1 : x ∈ G.Ω 1 := G.layer_subset hq1 hqk hx
    have hi1' : x' ∈ G.Ω 1 := G.layer_subset hq1 hqk hx'l
    funext i
    simp only [Ψ, hi1, hi1', ↓reduceIte]
    rw [G.layerIndex_eq hq1 hqk hx, G.layerIndex_eq hq1 hqk hx'l, hbK]
  refine ⟨⟨Ψ, fun _ _ => 0, hlc, fun _ _ _ _ _ _ _ => rfl, ?_, fun _ _ => rfl⟩, ?_, ?_⟩
  · intro x hx
    funext i
    have : x ∉ G.Ω 1 := fun h => hx (by rw [dataSites]; exact Finset.mem_union_left _ h)
    simp [Ψ, this]
  · intro x i
    refine ⟨?_, by simp⟩
    by_cases hx : x ∈ G.Ω 1 <;> simp [Ψ, hx]
  · intro x hx i
    simp [Ψ, hx]

end Bg

end Balaban.LargeField
