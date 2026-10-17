/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupSplit
public import Balaban.LargeField.R.RRemovedChainPiSplit

/-!
# The regrouping exposing the Gaussian node coordinates: the outputs (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (2).  The outputs `ψ_m↾Z` are regrouped into
`ψ_m↾Z₀`, the tree group `(V₂, P₂)`, the outputs at the blocks of a set `G₃` (top Gaussian blocks outside
the window groups) and the remaining outputs (`exists_out_nodes`); the inner outputs `ψ'_m↾Z₀` into those
at the blocks of `G₀ ⊆ Z₀` and the remaining ones (`exists_inner_nodes`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Out

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (m : ℕ) (Z0 : Set (BlockAt S n M K m))
  (V2 : Set (BlockAt S n M K m)) (P2 : BlockAt S n M K m → Prop) (G3 : Set (BlockAt S n M K m))

/-- **The outputs `ψ_m↾Z` regrouped with the node outputs exposed**: into `ψ_m↾Z₀`, the tree group, the
outputs at the blocks of `G₃` (inside `Z`, outside `Z₀` and the tree group) and the remaining outputs
`RO`; the value of each part at a block is the output at that block. -/
theorem exists_out_nodes
    (hZ0 : ∀ y ∈ Vblk R a m, y ∈ Z0 → ZBlk a m y)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R a m ∧ ZBlk a m y ∧ y ∉ Z0)
    (hG3 : ∀ y ∈ G3, y ∈ Vblk R a m ∧ ZBlk a m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y)) :
    ∃ (RO : Type) (_ : MeasurableSpace RO) (μRO : Measure RO) (_ : SFinite μRO)
      (Ψ : OutZ N R a m ≃ᵐ OutZero N R a m Z0 × (OutPart N V2 P2 ×
        (OutPart N (Vblk R a m) (· ∈ G3) × RO))),
      MeasurePreserving Ψ (outPartMeasure N (Vblk R a m) (ZBlk a m))
        ((outPartMeasure N (Vblk R a m) (· ∈ Z0)).prod ((outPartMeasure N V2 P2).prod
          ((outPartMeasure N (Vblk R a m) (· ∈ G3)).prod μRO))) ∧
      (∀ o (y : {y // y ∈ Vblk R a m ∧ y ∈ Z0}),
        (Ψ o).1 y = o ⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩) ∧
      (∀ o (y : {y // y ∈ V2 ∧ P2 y}),
        (Ψ o).2.1 y = o ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩) ∧
      (∀ o (y : {y // y ∈ Vblk R a m ∧ y ∈ G3}),
        (Ψ o).2.2.1 y = o ⟨y.1, y.2.1, (hG3 y.1 y.2.2).2.1⟩) := by
  classical
  have h12o : ∀ i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y},
      (i.1 ∈ V2 ∧ P2 i.1) → ¬ i.1 ∈ Z0 := fun i hi => (hV2 i.1 hi.1 hi.2).2.2
  have h13o : ∀ i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y},
      i.1 ∈ G3 → ¬ i.1 ∈ Z0 := fun i hi => (hG3 i.1 hi).2.2.1
  have h23o : ∀ i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y},
      i.1 ∈ G3 → ¬ (i.1 ∈ V2 ∧ P2 i.1) := fun i hi => (hG3 i.1 hi).2.2.2
  let e1o : {y // y ∈ Vblk R a m ∧ y ∈ Z0} ≃
      {i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y} // i.1 ∈ Z0} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩, y.2.2⟩
      invFun := fun i => ⟨i.1.1, i.1.2.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2o : {y // y ∈ V2 ∧ P2 y} ≃
      {i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y} // i.1 ∈ V2 ∧ P2 i.1} :=
    { toFun := fun y => ⟨⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩, y.2⟩
      invFun := fun i => ⟨i.1.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e3o : {y // y ∈ Vblk R a m ∧ y ∈ G3} ≃
      {i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y} // i.1 ∈ G3} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1, (hG3 y.1 y.2.2).2.1⟩, y.2.2⟩
      invFun := fun i => ⟨i.1.1, i.1.2.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨Ψ, hΨ, c1, c2, c3, c4⟩ := exists_split_three
    (α := fun _ : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y} =>
      EuclideanSpace ℝ (Fin N)) (fun _ => volume)
    (fun i => i.1 ∈ Z0) (fun i => i.1 ∈ V2 ∧ P2 i.1) (fun i => i.1 ∈ G3) h12o h13o h23o e1o e2o e3o
  exact ⟨_, _, _, inferInstance, Ψ, hΨ, c1, c2, c3⟩

/-- **The inner outputs `ψ'_m↾Z₀`** regrouped into those at the blocks of `G₀ ⊆ Z₀` and the remaining
ones. -/
theorem exists_inner_nodes (G0 : Set (BlockAt S n M K m)) (hG0 : ∀ y ∈ G0, y ∈ Z0) :
    ∃ (RW : Type) (_ : MeasurableSpace RW) (μRW : Measure RW) (_ : SFinite μRW)
      (Ψ : OutZero N R a m Z0 ≃ᵐ OutPart N (Vblk R a m) (· ∈ G0) × RW),
      MeasurePreserving Ψ (outPartMeasure N (Vblk R a m) (· ∈ Z0))
        ((outPartMeasure N (Vblk R a m) (· ∈ G0)).prod μRW) ∧
      (∀ w (y : {y // y ∈ Vblk R a m ∧ y ∈ G0}),
        (Ψ w).1 y = w ⟨y.1, y.2.1, hG0 y.1 y.2.2⟩) := by
  classical
  let e0w : {y // y ∈ Vblk R a m ∧ y ∈ G0} ≃
      {i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ y ∈ Z0} // i.1 ∈ G0} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1, hG0 y.1 y.2.2⟩, y.2.2⟩
      invFun := fun i => ⟨i.1.1, i.1.2.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨Ψ, hΨ, c1, c2⟩ := exists_split1
    (α := fun _ : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ y ∈ Z0} =>
      EuclideanSpace ℝ (Fin N)) (fun _ => volume) (fun i => i.1 ∈ G0) e0w
  exact ⟨_, _, _, inferInstance, Ψ, hΨ, c1⟩

end Out

end Balaban.LargeField
