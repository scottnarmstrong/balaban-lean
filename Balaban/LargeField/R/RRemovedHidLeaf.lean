/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidMean
public import Balaban.LargeField.R.ChainSetting
public import Balaban.LargeField.Operators.DomainGeom
public import Balaban.LargeField.Operators.CompBound
public import Balaban.LargeField.R.WindowGenGlue

/-!
# The Gaussian blocks of the ancestors are the blocks outside the layers of the window (W941)

`notes/phase1/LF4R-PLAN.md` §8.5.  `gaussBlocks_iff_locStep`: a block `y` of scale `j + 1` is a Gaussian block of
the localized history of an ancestor `c` of `Z` at scale `j + 1` iff its cube lies in `c` and not in the
`Ω_{j+1}` of the localized history of `Z` (`((H.locRH (m'+1) Z).step j).Omega`).  This is the comparison of
`a.Z (j+1) ∖ a.Omega j` (`gaussBlocks`) with the layers of `full = H.locGen Z M …` of the window
(`mem_locGen`: `x ∈ Ω_{j+1}(full) ↔ cubeMap (j+1) x ∈ ((H.locRH (m'+1) Z).step j).Omega`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Leaf

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

theorem gaussBlocks_iff_locStep {m' j : ℕ} (hK : j + 1 ≤ K) (hmK : m' + 1 ≤ K) (hj : j < m' + 1)
    {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    (y : BlockAt S n M K (j + 1)) :
    y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j ↔
      blockCube S n M K (j + 1) y ∈ (c.1 : Set (Torus S.d (n (j + 1)))) ∧
        blockCube S n M K (j + 1) y ∉ ((H.locRH (m' + 1) Z).step j).Omega := by
  rw [gaussBlocks_iff hK c y]
  set e := blockCube S n M K (j + 1) y with he
  have h1 := mem_locOmega_iff' hK c (Nat.lt_succ_self j) e
  have h2 := mem_locOmega_iff' hmK Z hj e
  rw [lin_self] at h1
  have hcl : e ∈ (c.1 : Set (Torus S.d (n (j + 1)))) →
      e ∈ ((H.lin (j + 1) (m' + 1) Z : Finset (Torus S.d (n (j + 1)))) : Set _) := fun h =>
    Finset.mem_coe.mpr (mem_lin.mpr ⟨c, mem_ancFin.mp hc, h⟩)
  rw [h1, h2]
  constructor
  · rintro ⟨h3, h4⟩
    refine ⟨h3, ?_⟩
    rintro (h5 | h5)
    · exact h4 (Or.inl h5)
    · exact h5 (hcl h3)
  · rintro ⟨h3, h4⟩
    refine ⟨h3, ?_⟩
    rintro (h5 | h5)
    · exact h4 (Or.inl h5)
    · exact h5 h3


theorem gaussBlocks_iff_locGen {m' j : ℕ} (hK : j + 1 ≤ K) (hmK : m' + 1 ≤ K) (hj : j < m' + 1)
    (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    (y : BlockAt S n M K (j + 1)) (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)))
    (hxy : cubeMap n S.L M (m' + 1) (j + 1) x = blockCube S n M K (j + 1) y) :
    y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j ↔
      blockCube S n M K (j + 1) y ∈ (c.1 : Set (Torus S.d (n (j + 1)))) ∧
        x ∉ (H.locGen Z M hmK hL hR).Ω (j + 1) := by
  rw [gaussBlocks_iff_locStep hK hmK hj hc y, mem_locGen, hxy]
  refine and_congr Iff.rfl (not_congr ?_)
  exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩

end Leaf


section Window

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **On `Z ∖ Z_{k₁}` the layers of the window generating set are those of `full`** (`windowGenSet_Ω`: the
three pieces have disjoint regions). -/
theorem windowGenSet_mem_iff_full (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ W.Z \ W.Zk1) (hxU : x ∈ W.Z) (j : ℕ) :
    x ∈ (W.windowGenSet h).Ω j ↔ x ∈ W.full.Ω j := by
  rw [WindowPieces.windowGenSet_Ω]
  have h1 : x ∉ W.Zk1 := (Finset.mem_sdiff.mp hx).2
  have h2 : x ∉ W.Unb \ W.Z := fun h' => (Finset.mem_sdiff.mp h').2 hxU
  simp only [Finset.mem_union, Finset.mem_inter, h1, h2, and_false, or_false, hx, and_true, false_or]

/-- The layer index of the window generating set at a site of `Z ∖ Z_{k₁}` is that of `full`. -/
theorem windowGenSet_layerIndex_eq_full (W : WindowPieces d L N₀ k ϱ) (h : W.Hyp)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ W.Z \ W.Zk1) :
    (W.windowGenSet h).layerIndex x = W.full.layerIndex x := by
  classical
  have hxZ : x ∈ W.Z := (Finset.mem_sdiff.mp hx).1
  have hlay : ∀ j, x ∈ (W.windowGenSet h).layer j ↔ x ∈ W.full.layer j := fun j => by
    rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, windowGenSet_mem_iff_full W h hx hxZ,
      windowGenSet_mem_iff_full W h hx hxZ]
  by_cases hex : ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ (W.windowGenSet h).layer j
  · obtain ⟨j, hj1, hjk, hjl⟩ := hex
    rw [(W.windowGenSet h).layerIndex_eq hj1 hjk hjl, W.full.layerIndex_eq hj1 hjk ((hlay j).mp hjl)]
  · have hex' : ¬ ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ W.full.layer j := by
      rintro ⟨j, hj1, hjk, hjl⟩
      exact hex ⟨j, hj1, hjk, (hlay j).mpr hjl⟩
    unfold GeneratingSet.layerIndex
    rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex')]

end Window

end Balaban.LargeField
