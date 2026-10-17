/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidMean
public import Balaban.LargeField.R.RRemovedChainForest

/-!
# From a map of sites to leaves of a forest to the leaf map of a block tree (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `forest_leaf_map`: given the numbering `e`, `el` of the nodes and leaves of the
tree of a root `r` of a forest (`hsc`, `hleaf` as in `forest_trees`) and a map `ls` of sites to leaves of that
tree with `m^{n}` sites over every leaf of scale `n`, the composite `lf = el ∘ ls` is a leaf map of the block tree
(`hcard`) and reads the leaf scales (`hscale`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

section LeafMap

variable {m k1 : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι)

open Classical in
theorem forest_leaf_map (r : {r : ι // pa r = r}) (B : BlockTree m k1 (sc r.1))
    (e : {i : ι // pa^[Fintype.card ι] i = r.1} ≃ Fin (B.n + 1))
    (el : {l : Lf // pa^[Fintype.card ι] (lp l) = r.1} ≃ Fin B.nLeaf)
    (hsc : ∀ i, B.scale (e i) = sc i.1)
    (hleaf : ∀ l, B.leafPar (el l) = e ⟨lp l.1, l.2⟩)
    {X : Type*} [Fintype X] (ls : X → Lf) (hroot : ∀ s, pa^[Fintype.card ι] (lp (ls s)) = r.1)
    (hcardL : ∀ l : Lf, pa^[Fintype.card ι] (lp l) = r.1 →
      (Finset.univ.filter fun s : X => ls s = l).card = m ^ (sc (lp l) - 1)) :
    ∃ lf : X → Fin B.nLeaf,
      (∀ x, (Finset.univ.filter fun s : X => lf s = x).card = m ^ B.leafScale x) ∧
      (∀ s, B.leafScale (lf s) = sc (lp (ls s)) - 1) ∧ ∀ s, (el.symm (lf s)).1 = ls s := by
  have hls : ∀ l : {l : Lf // pa^[Fintype.card ι] (lp l) = r.1},
      B.leafScale (el l) = sc (lp l.1) - 1 := by
    intro l
    unfold BlockTree.leafScale
    rw [hleaf l, hsc]
  refine ⟨fun s => el ⟨ls s, hroot s⟩, fun x => ?_, fun s => hls ⟨ls s, hroot s⟩,
    fun s => by simp⟩
  obtain ⟨l, rfl⟩ := el.surjective x
  rw [hls l, ← hcardL l.1 l.2]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact congrArg Subtype.val (el.injective h)
  · intro h
    exact congrArg el (Subtype.ext h)

end LeafMap

end Balaban.LargeField
