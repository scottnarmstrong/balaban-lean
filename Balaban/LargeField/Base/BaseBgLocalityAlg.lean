/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepPointLocal
public import Balaban.Fluctuation.PhysicalReadsFNu
public import Balaban.Green.FinalBoxLocCore

/-!
# The rooted component of a family of cells and the active closure (Lemma AE through the decoupled
background, combinatorics)

For a decoupling cover `C` with centres `C.cubeIdx` (the parameter cells, `ι = ↥C.cubeIdx`), the
patch of a cell `i` is the union, over the centres `q` whose footprint `𝒬(q)` contains `i`, of the
`D`-neighbourhoods of the interaction boxes `□_q` (`cellPatch`).  Two cells of one footprint have
patches that meet (in the box of `q`), two active centres whose boxes are within `D` have cells with
patches that meet.  Hence for parameters `s` vanishing off a family `Cs` of cells, **the footprint of
every centre of the active closure of a seed lies in the rooted component of `Cs`** at the seed
(`footprint_subset_rootComp`), and the decoupling factors of `s` and of `cutTo (rootComp …) s`
agree on the closure (`sProd_cutTo_eq_of_mem_actComp`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Fluctuation Balaban.Green

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] (C : DecCover d L N₁ m₁ (k + 1))

/-- The `D`-neighbourhood of the interaction box of a centre. -/
def boxNbhd (D : ℕ) (q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
  {y | ∃ x ∈ intBox q, supDist x y ≤ D}

/-- The patch of a parameter cell: the union of the `D`-neighbourhoods of the boxes of the centres
whose footprint contains it. -/
def cellPatch (D : ℕ) (i : ↥C.cubeIdx) : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
  {y | ∃ q ∈ C.cubeIdx, i.1 ∈ C.Qset q ∧ y ∈ boxNbhd D q}

variable {C}

theorem box_subset_boxNbhd (D : ℕ) (q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox q) : x ∈ boxNbhd D q := ⟨x, hx, by rw [supDist_self]; exact Nat.zero_le _⟩

theorem mem_cellPatch_of_box {D : ℕ} {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) {i : ↥C.cubeIdx} (hi : i.1 ∈ C.Qset q)
    {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ boxNbhd D q) :
    y ∈ cellPatch C D i := ⟨q, hq, hi, hy⟩

theorem mem_cellPatch_self {D : ℕ} {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ boxNbhd D q) : y ∈ cellPatch C D (⟨q, hq⟩ : ↥C.cubeIdx) :=
  ⟨q, hq, Balaban.Localization.self_mem_Qset_cover _ hq, hy⟩

theorem mem_cellPatch_foot {D : ℕ} {q i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (hi : i ∈ C.Qset q) (hiC : i ∈ C.cubeIdx)
    {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ boxNbhd D q) : y ∈ cellPatch C D (⟨i, hiC⟩ : ↥C.cubeIdx) :=
  ⟨q, hq, hi, hy⟩

open Classical in
/-- The cells of the footprint of an active centre lie in the family `Cs` that carries `s`. -/
theorem footprint_subset_of_active {Cs : Finset ↥C.cubeIdx} {s : Dec2.DecParams C}
    (hs : s ∈ supportedOn Cs) {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : ActC C (Dec2.extS C s) q) {i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hi : i ∈ C.Qset q) : ∃ h : i ∈ C.cubeIdx, (⟨i, h⟩ : ↥C.cubeIdx) ∈ Cs := by
  have hiC : i ∈ C.cubeIdx := ((C.mem_Qset).1 hi).1
  refine ⟨hiC, ?_⟩
  by_contra hn
  have h0 : s ⟨i, hiC⟩ = 0 := hs _ hn
  have : C.sProd (Dec2.extS C s) q = 0 := by
    unfold DecCover.sProd
    exact Finset.prod_eq_zero hi (by simp [Dec2.extS, hiC, h0])
  exact hq.2 this

open Classical in
theorem cell_rooted_of_adj {D : ℕ} {Cs : Finset ↥C.cubeIdx} {s : Dec2.DecParams C}
    (hs : s ∈ supportedOn Cs) {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {b c : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hadj : ActAdj C D (Dec2.extS C s) b c)
    (hb : (⟨b, hadj.1.1⟩ : ↥C.cubeIdx) ∈ rootComp (cellPatch C D) (seed : Set _) Cs) :
    (⟨c, hadj.2.1.1⟩ : ↥C.cubeIdx) ∈ rootComp (cellPatch C D) (seed : Set _) Cs := by
  obtain ⟨_, hcCs⟩ := footprint_subset_of_active hs hadj.2.1 (Balaban.Localization.self_mem_Qset_cover _ hadj.2.1.1)
  obtain ⟨x, hx, x', hx', hxx'⟩ := hadj.2.2
  refine mem_rootComp_of_adj hb hcCs ⟨x', ?_, ?_⟩
  · exact mem_cellPatch_self hadj.1.1 ⟨x, hx, hxx'⟩
  · exact mem_cellPatch_self hadj.2.1.1 (box_subset_boxNbhd D c hx')

open Classical in
/-- **The footprint of every centre of the active closure lies in the rooted component.** -/
theorem footprint_subset_rootComp {D : ℕ} {Cs : Finset ↥C.cubeIdx} {s : Dec2.DecParams C}
    (hs : s ∈ supportedOn Cs) {seed : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ actComp C D (Dec2.extS C s) seed) {i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hi : i ∈ C.Qset q) (hiC : i ∈ C.cubeIdx) :
    (⟨i, hiC⟩ : ↥C.cubeIdx) ∈ rootComp (cellPatch C D) (seed : Set _) Cs := by
  obtain ⟨hqC, q₀, h₀, hseed, hch⟩ := mem_actComp.1 hq
  -- all cells of the footprint of `q'` are rooted once the cell `q'` is
  have spread : ∀ q' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
      ActC C (Dec2.extS C s) q' →
      (∀ h : q' ∈ C.cubeIdx, (⟨q', h⟩ : ↥C.cubeIdx) ∈ rootComp (cellPatch C D) (seed : Set _) Cs) →
      ∀ j (hj : j ∈ C.Qset q') (hjC : j ∈ C.cubeIdx),
        (⟨j, hjC⟩ : ↥C.cubeIdx) ∈ rootComp (cellPatch C D) (seed : Set _) Cs := by
    intro q' hq' hroot j hj hjC
    obtain ⟨_, hjCs⟩ := footprint_subset_of_active hs hq' hj
    refine mem_rootComp_of_adj (hroot hq'.1) hjCs ⟨q'.2, ?_, ?_⟩
    · exact mem_cellPatch_self hq'.1 (box_subset_boxNbhd D q' (Localization.base_mem_intBox q'))
    · exact mem_cellPatch_foot hq'.1 hj hjC (box_subset_boxNbhd D q' (Localization.base_mem_intBox q'))
  have key : ∀ q' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1),
      Relation.ReflTransGen (ActAdj C D (Dec2.extS C s)) q₀ q' →
      ActC C (Dec2.extS C s) q' ∧
      ∀ h : q' ∈ C.cubeIdx, (⟨q', h⟩ : ↥C.cubeIdx) ∈ rootComp (cellPatch C D) (seed : Set _) Cs := by
    intro q' hq'
    induction hq' with
    | refl =>
      refine ⟨h₀, fun h => ?_⟩
      obtain ⟨_, hCs⟩ := footprint_subset_of_active hs h₀ (Balaban.Localization.self_mem_Qset_cover _ h₀.1)
      obtain ⟨x, hx, y, hy, hxy⟩ := hseed
      exact mem_rootComp_of_meets hCs ⟨y, mem_cellPatch_self h₀.1 ⟨x, hx, hxy⟩, hy⟩
    | tail _ hab ih =>
      rename_i b c
      exact ⟨hab.2.1, fun hc => cell_rooted_of_adj hs hab (ih.2 hab.1.1)⟩
  obtain ⟨hqact, hqroot⟩ := key q hch
  exact spread q hqact hqroot i hi hiC

theorem extS_cutTo_apply (A : Finset ↥C.cubeIdx) (s : Dec2.DecParams C)
    {P : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ C.cubeIdx) :
    Dec2.extS C (cutTo A s) P = if (⟨P, hP⟩ : ↥C.cubeIdx) ∈ A then Dec2.extS C s P else 0 := by
  classical
  simp [Dec2.extS, hP, cutTo]

open Classical in
/-- **The factors of `s` and of `cutTo A s` agree on every centre whose footprint lies in `A`.** -/
theorem sProd_cutTo_eq_of_footprint (A : Finset ↥C.cubeIdx) (s : Dec2.DecParams C)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (h : ∀ i ∈ C.Qset q, ∀ hi : i ∈ C.cubeIdx, (⟨i, hi⟩ : ↥C.cubeIdx) ∈ A) :
    C.sProd (Dec2.extS C (cutTo A s)) q = C.sProd (Dec2.extS C s) q := by
  unfold DecCover.sProd
  refine Finset.prod_congr rfl fun i hi => ?_
  have hiC : i ∈ C.cubeIdx := ((C.mem_Qset).1 hi).1
  rw [extS_cutTo_apply A s hiC]
  simp [h i hi hiC]

open Classical in
/-- **A centre active for `cutTo A s` is active for `s`, with the same factor.** -/
theorem sProd_cutTo_eq_of_active (A : Finset ↥C.cubeIdx) (s : Dec2.DecParams C)
    {q : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (h : C.sProd (Dec2.extS C (cutTo A s)) q ≠ 0) :
    C.sProd (Dec2.extS C (cutTo A s)) q = C.sProd (Dec2.extS C s) q := by
  refine sProd_cutTo_eq_of_footprint A s fun i hi hiC => ?_
  by_contra hn
  have h0 : Dec2.extS C (cutTo A s) i = 0 := by
    rw [extS_cutTo_apply A s hiC]
    simp [hn]
  exact h (Finset.prod_eq_zero hi h0)

end Balaban.LargeField.Base
