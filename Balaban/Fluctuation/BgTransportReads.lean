/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.BgTransport

/-!
# The canonical transport reads every datum of the step (`BgTransportReads`)

For the step's expansion set `Gp` (a level set of the top level `k + 1`) and any background
generating set `Gb` on the same torus, the datum `clipRaw Gb (rawOf D)` read by a term recomputed on
`Gb` from a datum `D` of the step is a datum of `Gb`: the fields of `D` are constant on the blocks
of side `L ^ (k + 1)`, hence on every smaller block, and the cut-off to the data sites of `Gb` does
not cut a block of a layer of `Gb`, because such a block lies in `Ω₁(Gb)`.  No margin condition on
`Gb` is needed.

* `isLayerConstant_of_isLevel`: a field constant on the blocks of the level set `Gp` is constant on
  the blocks of every layer of any generating set `Gb`;
* `layerSub_of_isLevel`, `BgTransport.reads_canon`: `(BgTransport.canon Gp Gb N).Reads`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.LargeField Balaban.Multiscale Balaban.Fluctuation Balaban.Background
  Balaban.SmallField Finset

section Reads

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} {N : ℕ}

/-- **Fields constant on the blocks of a level set are constant on the blocks of every layer of
every generating set**: the `n`-block, `n ≤ k + 1`, lies in the `(k + 1)`-block of its sites. -/
theorem isLayerConstant_of_isLevel (hG' : IsLevel Gp (k + 1)) {β : Type*}
    {Ψ : CTorus d L N₁ m₁ (k + 1) → β} (h : IsLayerConstant Gp Ψ) :
    IsLayerConstant Gb Ψ := by
  intro n hn hnk x _ x' hx'
  have hsc : SameCell (L ^ n) x' x :=
    sameCell_of_jBlock_eq (N₀ := N₁ * L ^ m₁) hnk (GeneratingSet.mem_blk.1 hx')
  refine h (k + 1) le_add_self le_rfl x (hG'.mem_layer x) x' ?_
  rw [GeneratingSet.mem_blk]
  exact jBlock_eq_of_sameCell (hsc.mono (pow_dvd_pow L hnk))

/-- **The raw data of a datum of the step are layer constant for every `Gb`.** -/
theorem layerSub_of_isLevel (hG' : IsLevel Gp (k + 1)) (D : BgData Gp N) :
    (D.Ψ, D.h) ∈ layerSub Gb :=
  ⟨isLayerConstant_of_isLevel hG' D.Ψ_layerConst, isLayerConstant_of_isLevel hG' D.h_layerConst⟩

/-- **The canonical transport reads every datum of the step** (the open point of W1139): for a
level set `Gp` and any `Gb` on the same torus, the datum `clipRaw Gb (rawOf D)` is a datum of `Gb`. -/
theorem BgTransport.reads_canon (hG' : IsLevel Gp (k + 1)) :
    (BgTransport.canon Gp Gb N).Reads := fun D => by
  show clipRaw Gb (D.Ψ, D.h) ∈ rawSub N Gb
  exact clipRaw_mem_rawSub Gb (layerSub_of_isLevel hG' D)

end Reads

end Balaban.Localization
