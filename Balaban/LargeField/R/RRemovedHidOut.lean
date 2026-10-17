/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupSplit
public import Balaban.LargeField.R.RRemovedChainPiSplit

/-!
# The regrouping of the window integral with the shell variables exposed: the outputs (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  As `exists_out_nodes` (W923), but the
outputs outside the window groups and outside the Gaussian set `G₃` are not hidden: they are the explicit
variables `RO` (an `OutPart`), so that the shell indicators of the new outputs can be integrated.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Out

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (m : ℕ) (Z0 : Set (BlockAt S n M K m))
  (V2 : Set (BlockAt S n M K m)) (P2 : BlockAt S n M K m → Prop) (G3 : Set (BlockAt S n M K m))

/-- **The outputs `ψ_m↾Z` regrouped with the node and the shell outputs exposed**: into `ψ_m↾Z₀`, the tree
group, the outputs at the blocks of `G₃` and the outputs at the remaining blocks of `V ∩ Z` (the shell
outputs `RO`, an `OutPart`); the value of each part at a block is the output at that block. -/
theorem exists_out_shell
    (hZ0 : ∀ y ∈ Vblk R a m, y ∈ Z0 → ZBlk a m y)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R a m ∧ ZBlk a m y ∧ y ∉ Z0)
    (hG3 : ∀ y ∈ G3, y ∈ Vblk R a m ∧ ZBlk a m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y)) :
    ∃ Ψ : OutZ N R a m ≃ᵐ OutZero N R a m Z0 × (OutPart N V2 P2 ×
        (OutPart N (Vblk R a m) (· ∈ G3) ×
          OutPart N (Vblk R a m) (fun y => ZBlk a m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))),
      MeasurePreserving Ψ (outPartMeasure N (Vblk R a m) (ZBlk a m))
        ((outPartMeasure N (Vblk R a m) (· ∈ Z0)).prod ((outPartMeasure N V2 P2).prod
          ((outPartMeasure N (Vblk R a m) (· ∈ G3)).prod
            (outPartMeasure N (Vblk R a m)
              (fun y => ZBlk a m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))))) ∧
      (∀ o (y : {y // y ∈ Vblk R a m ∧ y ∈ Z0}),
        (Ψ o).1 y = o ⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩) ∧
      (∀ o (y : {y // y ∈ V2 ∧ P2 y}),
        (Ψ o).2.1 y = o ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩) ∧
      (∀ o (y : {y // y ∈ Vblk R a m ∧ y ∈ G3}),
        (Ψ o).2.2.1 y = o ⟨y.1, y.2.1, (hG3 y.1 y.2.2).2.1⟩) ∧
      (∀ o (y : {y // y ∈ Vblk R a m ∧
          (ZBlk a m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)}),
        (Ψ o).2.2.2 y = o ⟨y.1, y.2.1, y.2.2.1⟩) := by
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
  let e4o : {y // y ∈ Vblk R a m ∧
      (ZBlk a m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)} ≃
      {t : {t : {i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y} // ¬ i.1 ∈ Z0} //
        ¬ (fun i : {y : BlockAt S n M K m // y ∈ Vblk R a m ∧ ZBlk a m y} =>
          i.1 ∈ V2 ∧ P2 i.1) t.1} // ¬ (fun i : {y : BlockAt S n M K m //
            y ∈ Vblk R a m ∧ ZBlk a m y} => i.1 ∈ G3) t.1.1} :=
    { toFun := fun y => ⟨⟨⟨⟨y.1, y.2.1, y.2.2.1⟩, y.2.2.2.1⟩, y.2.2.2.2.1⟩, y.2.2.2.2.2⟩
      invFun := fun t => ⟨t.1.1.1.1, t.1.1.1.2.1, t.1.1.1.2.2, t.1.1.2, t.1.2, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨Ψ4, h4, d4⟩ := exists_reindex_equiv e4o (β := fun _ => EuclideanSpace ℝ (Fin N))
    (γ := fun _ => EuclideanSpace ℝ (Fin N)) (fun _ => volume) (fun _ => volume)
    (fun _ => MeasurableEquiv.refl _) (fun _ => MeasurePreserving.id _)
  refine ⟨Ψ.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) Ψ4))), ?_, ?_, ?_, ?_, ?_⟩
  · have h7 := (MeasurePreserving.id (outPartMeasure N (Vblk R a m) (· ∈ Z0))).prod
      ((MeasurePreserving.id (outPartMeasure N V2 P2)).prod
        ((MeasurePreserving.id (outPartMeasure N (Vblk R a m) (· ∈ G3))).prod h4))
    have h8 := h7.comp (f := Ψ) (by convert hΨ using 3 <;> first | rfl | congr!)
    exact h8
  · exact c1
  · exact c2
  · exact c3
  · intro o y
    exact (d4 _ y).trans (c4 o _)

end Out

end Balaban.LargeField
