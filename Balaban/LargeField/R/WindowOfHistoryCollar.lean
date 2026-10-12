module

public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.WindowCollarGeom

/-!
# The collar lemmas at the actual window of a ripe component

The geometric premises of `window_parent_refines`, `outer_collar_outside_reference`,
`outer_collar_parent_layer_top` and `inner_collar_parent_layer` (COLLAR-FIX §§1-2) are discharged for
`W = windowOfHistory H Z g hkK hW` by the theorems `windowOfHistory_h…` of `WindowOfHistory`, with the
hypothesis `W.Hyp` supplied by `windowOfHistory_hyp`.

Not instantiated here (missing premises, none of which is a property of the window pieces alone):
`deltaPsiColl_eq_zero_outer` (the reference-field identity P7 (2.44) `hoff`, the typing `hprec`
of `windowData`, and the data `ψ ψ0 h`), `inner_collar_in_regular_T`, `inner_collar_shell_bound`,
`inner_collar_data_change_*`, `dataChangeBound'_window_of_coreTop` (the regularity-path premises
`hcT`, `hwT`, `hcoreTop`, `hreach`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Finset

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) {k : ℕ} (Z : H.Comp k) {M : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M) (hkK : k ≤ K) (hW : H.RipeWindow k Z)

/-- `window_parent_refines` at the actual window: the parent `𝔹_k` refines the window generating
set. -/
theorem windowOfHistory_parentRefines :
    ParentRefines ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).full :=
  window_parent_refines _ _ (windowOfHistory_hcore (g := g) hkK hW)
    (windowOfHistory_hbdry (g := g) hkK hW)

/-- `outer_collar_outside_reference` at the actual window. -/
theorem windowOfHistory_outer_collar_outside_reference
    {c : Torus S.d (M * n k * S.L ^ k)}
    (hc : c ∈ collarOut (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    c ∉ (windowOfHistory H Z g hkK hW).Z ∧ c ∉ (windowOfHistory H Z g hkK hW).bdry.Ω 1 :=
  outer_collar_outside_reference _ _
    (windowOfHistory_hOmK1 (g := g) hkK hW)
    (windowOfHistory_hsupp (g := g) hkK hW) hc

/-- `outer_collar_parent_layer_top` at the actual window. -/
theorem windowOfHistory_outer_collar_parent_layer_top (hk : 1 ≤ k)
    {c : Torus S.d (M * n k * S.L ^ k)}
    (hc : c ∈ collarOut (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    c ∈ (windowOfHistory H Z g hkK hW).full.layer k ∧
      (windowOfHistory H Z g hkK hW).full.layerIndex c = k ∧
      parentBlock (windowOfHistory H Z g hkK hW).full c = blockOf S.d S.L (M * n k) k k c :=
  outer_collar_parent_layer_top _ _ hk (windowOfHistory_hOmK1 (g := g) hkK hW)
    (windowOfHistory_hsupp (g := g) hkK hW) (windowOfHistory_hOmK (g := g) hkK hW hk) hc

/-- `inner_collar_parent_layer` at the actual window (`k₁ = S.k1 k`). -/
theorem windowOfHistory_inner_collar_parent_layer
    {c : Torus S.d (M * n k * S.L ^ k)}
    (hc : c ∈ collarIn (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)) :
    c ∈ (windowOfHistory H Z g hkK hW).full.layer (S.k1 k) ∧
      (windowOfHistory H Z g hkK hW).full.layerIndex c = S.k1 k ∧
      parentBlock (windowOfHistory H Z g hkK hW).full c = blockOf S.d S.L (M * n k) k (S.k1 k) c :=
  inner_collar_parent_layer _ _ (hW.k1_pos hkK) (k1_le hW) (windowOfHistory_hmargin (g := g) hkK hW)
    (windowOfHistory_hZk1top (g := g) hkK hW) hc

end RegionHistory

end Balaban.LargeField
