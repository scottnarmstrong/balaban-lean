/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootMarkedBound
public import Balaban.Fluctuation.RootPavingMap
public import Balaban.Fluctuation.HatLabelsAct
public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Fluctuation.StepObjects
public import Balaban.SmallField.Def6BridgeGeom
import Mathlib.Tactic.Positivity

/-!
# Geometry of the root block and of the rooted domains (MARKS.md §4, package 1)

The block `B(z)` of a root `z` of the next-scale torus is a block of side `L^K` of the fine torus
`CTorus d L N₁ m₁ K`; it lies in the level-`K` cube `rootCube z` of side `cellSide`.  This file
proves the pure geometry that a marked expansion rooted at `z` needs.

* `fineBlock z`: the fine sites of `B(z)`, `{x | blockIndex x = z}`; for `K = k + 1` it is the set
  of fine sites whose unit block has `unitBlock1` equal to `z` (`mem_fineBlock_iff_unitBlock1`),
  i.e. the whole fibre over `z`.
* **Block in the root cube** (`fineBlock_subset_box_rootCube`, `cbase_eq_rootCube`), and for
  unit points of the step: `b ∈ S.blockU z → S.cellOf m₀ b = rootCube z`
  (`cellOf_eq_rootCube`), `unitRep b ∈ fineBlock z` (`unitRep_mem_fineBlock`).
* **A domain meeting the block contains the root cube** (`rootCube_mem_blocksOf_of_mem_fineBlock`
  and its forms for `IsDj`, `IsPolyDom`): a union of `π′_K` cubes that contains a site of `B(z)`
  contains the box of `rootCube z`; the corollary `anchor_of_meets` feeds `anchor_of_labels`.
* **Extension of a label system by zero** (`labelActExtend`, `gsumCoeff_extend`,
  `thickActExtend`, `gsumCoeff_thick_extend`): adjoining domains with zero activity does not
  change the coefficients, and the entropy bound `K0 d L κ₀` of `entropy_thick` is the same for
  the larger family.
* **Root-anchored prefactor bound** (`rootAnchored_entropy_thick`, `rootAnchored_mark_sum`):
  the weighted number of domains containing `rootCube z` is at most the constant `K0 d L κ₀`,
  independent of `z`, of the scale and of the torus.

## Scope

This is geometry only.  No mark is constructed and no analytic estimate is proved here; the
marked expansion is a separate package.  Nothing depends on a choice of generating set for the
class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 MeasureTheory

section Block

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The fine sites of the block `B(z)`** of the root `z`: the sites `x` of the fine torus whose
block of side `L^K` has coarse index `z`. -/
def fineBlock (z : RootIdx d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  {x | blockIndex x = z}

omit [NeZero N₁] [NeZero L] in
theorem mem_fineBlock {z : RootIdx d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} :
    x ∈ fineBlock z ↔ blockIndex x = z := Iff.rfl

theorem rootSite_mem_fineBlock (z : RootIdx d L N₁ m₁ K) : rootSite z ∈ fineBlock z :=
  blockIndex_rootSite z

/-- Sites of one block of side `L^K` determine the same level-`K` cell. -/
theorem cbase_cellSide_eq_of_blockBase_eq (w x : CTorus d L N₁ m₁ K)
    (hw : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K x) :
    cbase (cellSide L m₀ m₁ K) w = cbase (cellSide L m₀ m₁ K) x := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨c, hc⟩ := (pow_dvd_cellSide (L := L) (K := K) (m₀ := m₀) (m₁ := m₁))
  funext μ
  have hμ := congrArg (fun t : CTorus d L N₁ m₁ K => (t μ).val) hw
  simp only [blockBase, cbase_val] at hμ
  have hq : (w μ).val / L ^ K = (x μ).val / L ^ K := Nat.eq_of_mul_eq_mul_left hL hμ
  simp only [cbase]
  rw [hc, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hq]

/-- **The cell of a site of `B(z)` is the root cube.** -/
theorem cbase_eq_rootCube {z : RootIdx d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ fineBlock z) :
    cbase (cellSide L m₀ m₁ K) x = (rootCube (m₀ := m₀) z).1 := by
  have h1 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K x = rootSite z := by
    rw [← rootSite_blockIndex, hx]
  have h2 := blockBase_rootSite (N₁ := N₁) (m₁ := m₁) (K := K) (d := d) (L := L) z
  exact cbase_cellSide_eq_of_blockBase_eq (m₀ := m₀) x (rootSite z) (h1.trans h2.symm)

/-- **T1.** Every site of the block `B(z)` lies in the level-`K` cube `rootCube z`. -/
theorem fineBlock_subset_box_rootCube (z : RootIdx d L N₁ m₁ K) :
    fineBlock z ⊆ box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K) := by
  intro x hx
  rw [← cbase_eq_rootCube (m₀ := m₀) hx]
  exact mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) x

/-- **T2.** A union of `π′_K` cubes containing a site of the block `B(z)` contains the root
cube among its cubes. -/
theorem rootCube_mem_blocksOf_of_mem_fineBlock (hN : L ^ m₀ ∣ N₁) {z : RootIdx d L N₁ m₁ K}
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPiPrimeUnion (m₁ := m₁) m₀ K Y)
    {x : CTorus d L N₁ m₁ K} (hxY : x ∈ Y) (hxz : x ∈ fineBlock z) :
    rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  obtain ⟨b, hb1, hb2, hb3⟩ := hY x hxY
  have hcell := (cell_subset_cube hdvd ha0 hb1 hb2).trans hb3
  rw [cbase_eq_rootCube (m₀ := m₀) hxz] at hcell
  exact mem_blocksOf.2 hcell

/-- **T2 for `IsDj`.** -/
theorem rootCube_mem_blocksOf_of_isDj (hN : L ^ m₀ ∣ N₁) {z : RootIdx d L N₁ m₁ K}
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y) (hmeet : (Y ∩ fineBlock z).Nonempty) :
    rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y := by
  obtain ⟨x, hxY, hxz⟩ := hmeet
  exact rootCube_mem_blocksOf_of_mem_fineBlock hN hY.2.1 hxY hxz

/-- **T2 for `IsPolyDom`.** -/
theorem rootCube_mem_blocksOf_of_isPolyDom (hN : L ^ m₀ ∣ N₁) {z : RootIdx d L N₁ m₁ K}
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsPolyDom m₀ K Y)
    (hmeet : (Y ∩ fineBlock z).Nonempty) :
    rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y :=
  rootCube_mem_blocksOf_of_isDj hN (isDj_of_isPolyDom hY) hmeet

section Anchor

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {BS : ProdSplit ν d L N₁ m₁ K m₀}
  {W : ℝ → Ω → ℂ} {f : RootIdx d L N₁ m₁ K → ℝ → Ω → ℂ}

/-- **T2, corollary.**  If every mark label of `I z` is a domain meeting the block `B(z)`, then
every mark label contains the root cube, so a non-zero coefficient of `I z` has the root cube of
`z` in `T`. -/
theorem anchor_of_meets (hN : L ^ m₀ ∣ N₁)
    (I : ∀ z : RootIdx d L N₁ m₁ K, InterpMarks ν BS W (f z))
    (hmeet : ∀ (z : RootIdx d L N₁ m₁ K) i,
      ((I z).Lab.ysite ((I z).y0 i) ∩ fineBlock z).Nonempty)
    (z : RootIdx d L N₁ m₁ K) {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) m₀ K Set.univ)} (h : interpCoeff (I z) T ≠ 0) : rootCube z ∈ T :=
  anchor_of_labels I (fun z i => rootCube_mem_blocksOf_of_isDj hN ((I z).Lab.isDj _) (hmeet z i))
    z h

/-- **T2, corollary.**  Under the same hypothesis the root site lies in the polymer of every
non-zero marked term. -/
theorem y_mem_of_markedTerm_ne_zero_of_meets (hN : L ^ m₀ ∣ N₁)
    (I : ∀ z : RootIdx d L N₁ m₁ K, InterpMarks ν BS W (f z))
    (hmeet : ∀ (z : RootIdx d L N₁ m₁ K) i,
      ((I z).Lab.ysite ((I z).y0 i) ∩ fineBlock z).Nonempty)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (h : markedTerm I y X ≠ 0) :
    y ∈ X :=
  y_mem_of_markedTerm_ne_zero_of_anchor I hN (fun z _ => anchor_of_meets hN I hmeet z) h

end Anchor

end Block

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}

/-- For `K = k + 1`, the block `B(z)` is the fibre `unitBlock1 (unitBlock x) = z` over the root:
one block of side `L^{k+1}`, i.e. the fibre of `unitBlock1` over a unit block, pulled back to the
fine torus. -/
theorem mem_fineBlock_iff_unitBlock1 {z : RootIdx d L N₁ m₁ (k + 1)}
    {x : CTorus d L N₁ m₁ (k + 1)} :
    x ∈ fineBlock z ↔ unitBlock1 (unitBlock x) = z := by
  rw [unitBlock1_unitBlock]
  exact Iff.rfl

/-- **T1 (unit points).**  A unit point of the block `blockU z` lies in the cube `rootCube z`:
`cellOf b = rootCube z`. -/
theorem cellOf_eq_rootCube {z : RootIdx d L N₁ m₁ (k + 1)} {b : S.U} (hb : b ∈ S.blockU z) :
    S.cellOf m₀ b = rootCube (m₀ := m₀) z := by
  have hbz : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = z := by
    simpa [StepSetting.blockU] using hb
  have hx := (Classical.choose_spec ((mem_unitPts S.G').1 b.2)).2
  have hmem : Classical.choose ((mem_unitPts S.G').1 b.2) ∈ fineBlock z :=
    mem_fineBlock_iff_unitBlock1.2 (by rw [hx]; exact hbz)
  exact Subtype.ext (cbase_eq_rootCube (m₀ := m₀) hmem)

/-- **T1 (representatives).**  The fine representative of a unit point of `blockU z` lies in the
block `B(z)`, hence in the box of `rootCube z`. -/
theorem unitRep_mem_fineBlock {z : RootIdx d L N₁ m₁ (k + 1)} {b : S.U}
    (hb : b ∈ S.blockU z) : unitRep b ∈ fineBlock z := by
  have hbz : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = z := by
    simpa [StepSetting.blockU] using hb
  exact mem_fineBlock_iff_unitBlock1.2 (by rw [unitBlock_unitRep]; exact hbz)

theorem unitRep_mem_box_rootCube {z : RootIdx d L N₁ m₁ (k + 1)} {b : S.U}
    (hb : b ∈ S.blockU z) :
    unitRep b ∈ box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ (k + 1)) :=
  fineBlock_subset_box_rootCube z (unitRep_mem_fineBlock hb)

end Step

end Balaban.Fluctuation
