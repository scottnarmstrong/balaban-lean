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

section Extend

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
  (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb)
  (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb')

/-- **Extension by zero** of a family `H` of functions indexed by the labels `Lb` along an
injection `e : Lb → Lb'` of label types: the value at `e y` is `H y` and the value off the range
of `e` is `0`. -/
noncomputable def extendByZero {Φ : Type*} (e : Lb → Lb') (H : Lb → Φ → ℂ) : Lb' → Φ → ℂ :=
  Function.extend e H 0

omit [Fintype Lb] [Fintype Lb'] in
theorem extendByZero_apply {Φ : Type*} {e : Lb → Lb'} (he : Function.Injective e)
    (H : Lb → Φ → ℂ) (y : Lb) : extendByZero e H (e y) = H y :=
  he.extend_apply H 0 y

omit [Fintype Lb] [Fintype Lb'] in
theorem extendByZero_apply_of_not_mem_range {Φ : Type*} {e : Lb → Lb'} (H : Lb → Φ → ℂ)
    {y' : Lb'} (hy' : ∀ y, e y ≠ y') : extendByZero e H y' = 0 :=
  Function.extend_apply' H (0 : Lb' → Φ → ℂ) y' (fun ⟨y, hy⟩ => hy' y hy)

open Classical in
/-- The pre-summed term of the extended activities is the pre-summed term of the original ones
(`presum` of `extendByZero`), when the extension is compatible with the label sites. -/
theorem presum_extendByZero {e : Lb → Lb'} (he : Function.Injective e)
    (hsite : ∀ y, Lab'.ysite (e y) = Lab.ysite y) {Ωb : CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) m₀ j Ω → Type*} (H : Lb → (∀ b, Ωb b) → ℂ)
    (S : NePoly (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    (Φ : ∀ b, Ωb b) :
    presum Lab' (extendByZero e H) S Φ = presum Lab H S Φ := by
  unfold presum
  have h1 : ∑ y ∈ Finset.univ.filter (fun y => blocksOf m₀ j Ω (Lab.ysite y) = S.1), H y Φ =
      ∑ y' ∈ (Finset.univ.filter (fun y => blocksOf m₀ j Ω (Lab.ysite y) = S.1)).image e,
        extendByZero e H y' Φ := by
    rw [Finset.sum_image (fun a _ b _ h => he h)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [extendByZero_apply he]
  rw [h1]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro y' hy'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rwa [hsite]
  · intro y' hy' hn
    by_cases hr : ∃ y, e y = y'
    · obtain ⟨y, rfl⟩ := hr
      exfalso
      refine hn (Finset.mem_image.2 ⟨y, ?_, rfl⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy' ⊢
      rwa [hsite] at hy'
    · rw [extendByZero_apply_of_not_mem_range H (fun y hy => hr ⟨y, hy⟩)]
      rfl

open Classical in
/-- **The activities extended by zero.**  Given activities `A` of the label system `Lab`, the
activity of a label of `Lab'` is `A.H y` at `e y` and `0` elsewhere.  The constants
`ε_H, κ_H, κ₀` are those of `A`; the entropy constant `Kc'` is that of the bigger label system
(`hent`). -/
noncomputable def labelActExtend {e : Lb → Lb'} (he : Function.Injective e)
    (hsite : ∀ y, Lab'.ysite (e y) = Lab.ysite y) (hdl : ∀ y, Lab'.dl (e y) = Lab.dl y)
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc Kc' : ℝ} (hε : 0 ≤ εH)
    (hent : ∀ b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω,
      ∑ y : Lb', (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab'.ysite y then
        Real.exp (-κ0 * Lab'.dl y) else 0) ≤ Kc')
    (A : LabelAct Lab Ωb εH κH κ0 Kc) : LabelAct Lab' Ωb εH κH κ0 Kc' where
  H := extendByZero e A.H
  meas y' := by
    by_cases hr : ∃ y, e y = y'
    · obtain ⟨y, rfl⟩ := hr
      rw [extendByZero_apply he]; exact A.meas y
    · rw [extendByZero_apply_of_not_mem_range A.H (fun y hy => hr ⟨y, hy⟩)]
      exact measurable_const
  dep y' := by
    by_cases hr : ∃ y, e y = y'
    · obtain ⟨y, rfl⟩ := hr
      rw [extendByZero_apply he, hsite]; exact A.dep y
    · rw [extendByZero_apply_of_not_mem_range A.H (fun y hy => hr ⟨y, hy⟩)]
      intro Φ Φ' _; rfl
  bound y' Φ := by
    by_cases hr : ∃ y, e y = y'
    · obtain ⟨y, rfl⟩ := hr
      rw [extendByZero_apply he, hdl]; exact A.bound y Φ
    · rw [extendByZero_apply_of_not_mem_range A.H (fun y hy => hr ⟨y, hy⟩)]
      simpa using mul_nonneg hε (Real.exp_pos _).le
  entropy := hent

open Classical in
/-- The local term `G*` only sees the activities through their pre-sums, so it is unchanged by
the extension by zero. -/
theorem Gst_extendByZero {e : Lb → Lb'} (he : Function.Injective e)
    (hsite : ∀ y, Lab'.ysite (e y) = Lab.ysite y)
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (H : Lb → (∀ b, Ωb b) → ℂ)
    (S₀ : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω))
    (G : (∀ b, Ωb b) → ℂ) (S : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) m₀ j Ω)) :
    Gst μ Lab' (extendByZero e H) S₀ G S = Gst μ Lab H S₀ G S := by
  unfold Gst
  have : presum Lab' (extendByZero e H) = presum Lab H := by
    funext T Φ
    exact presum_extendByZero Lab Lab' he hsite H T Φ
  rw [this]

open Classical in
/-- **T3 (generic form).**  The coefficient `gsumCoeff` of the marks `G` with labels `y0` and
activities `A` equals the coefficient of the marks with labels `e ∘ y0` and the activities
extended by zero, in the larger label system. -/
theorem gsumCoeff_extend {e : Lb → Lb'} (he : Function.Injective e)
    (hsite : ∀ y, Lab'.ysite (e y) = Lab.ysite y) (hdl : ∀ y, Lab'.dl (e y) = Lab.dl y)
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {εH κH κ0 Kc Kc' : ℝ} (hε : 0 ≤ εH)
    (hent : ∀ b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω,
      ∑ y : Lb', (if box b.1 (cellSide L m₀ m₁ j) ⊆ Lab'.ysite y then
        Real.exp (-κ0 * Lab'.dl y) else 0) ≤ Kc')
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) {ι : Type*} [Fintype ι] (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) m₀ j Ω)) :
    gsumCoeff μ Lab' (fun s => labelActExtend Lab Lab' he hsite hdl hε hent (A s))
        (fun i => e (y0 i)) G T = gsumCoeff μ Lab A y0 G T := by
  unfold gsumCoeff
  refine intervalIntegral.integral_congr fun s _ => ?_
  unfold Gsum
  refine Finset.sum_congr rfl fun i _ => ?_
  have hb : blocksOf m₀ j Ω (Lab'.ysite (e (y0 i))) = blocksOf m₀ j Ω (Lab.ysite (y0 i)) := by
    rw [hsite]
  simp only [hb]
  exact Gst_extendByZero Lab Lab' he hsite μ (A (s : ℂ)).H _ _ _

end Extend

section Thick

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

/-- The inclusion of the labels of a subfamily of domains into the labels of a larger family. -/
def thickIncl {𝒴 𝒵 : Finset (Set (CTorus d L N₁ m₁ K))} (h𝒴𝒵 : 𝒴 ⊆ 𝒵) :
    {Y // Y ∈ 𝒴} → {Z // Z ∈ 𝒵} := fun Y => ⟨Y.1, h𝒴𝒵 Y.2⟩

omit [NeZero L] [NeZero N₁] in
theorem thickIncl_injective {𝒴 𝒵 : Finset (Set (CTorus d L N₁ m₁ K))} (h𝒴𝒵 : 𝒴 ⊆ 𝒵) :
    Function.Injective (thickIncl h𝒴𝒵) := fun _ _ h => by
  have := congrArg Subtype.val h
  exact Subtype.ext this

open Classical in
/-- **T3.**  The activities of the labels `thickLabels 𝒴`, extended by zero to the labels
`thickLabels 𝒵` of a larger finite family of domains.  The constants `ε_H, κ_H, κ₀` are those of
the original activities; the entropy constant is `K0 d L κ₀`, the constant of `entropy_thick`,
which does not depend on the family (so the same as for `𝒴`), provided `a_ent + 1 ≤ κ₀`. -/
noncomputable def thickActExtend (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {𝒴 𝒵 : Finset (Set (CTorus d L N₁ m₁ K))} (h𝒴 : ∀ Y ∈ 𝒴, IsDj m₀ j Y)
    (h𝒵 : ∀ Z ∈ 𝒵, IsDj m₀ j Z) (h𝒴𝒵 : 𝒴 ⊆ 𝒵)
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)] {εH κH κ0 Kc : ℝ} (hε : 0 ≤ εH) (hκ0 : aEnt d L + 1 ≤ κ0)
    (A : LabelAct (thickLabels 𝒴 h𝒴) Ωb εH κH κ0 Kc) :
    LabelAct (thickLabels 𝒵 h𝒵) Ωb εH κH κ0 (K0 d L κ0) :=
  labelActExtend (thickLabels 𝒴 h𝒴) (thickLabels 𝒵 h𝒵) (thickIncl_injective h𝒴𝒵)
    (fun _ => rfl) (fun _ => rfl) hε (fun b => entropy_thick hN hj 𝒵 h𝒵 hκ0 b) A

open Classical in
/-- **T3 (the step's label system).**  For finite families of domains `𝒴 ⊆ 𝒵`, the coefficient of
marks with labels in `thickLabels 𝒴` and activities `A` is unchanged when the labels are viewed in
`thickLabels 𝒵` and the activities are extended by zero on `𝒵 ∖ 𝒴`.  The entropy hypothesis
`hent` of the landed theorems holds in `thickLabels 𝒵` with the constant `K0 d L κ₀` of
`entropy_thick` (the same constant as for `𝒴`); no other constant changes. -/
theorem gsumCoeff_thick_extend (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K)
    {𝒴 𝒵 : Finset (Set (CTorus d L N₁ m₁ K))} (h𝒴 : ∀ Y ∈ 𝒴, IsDj m₀ j Y)
    (h𝒵 : ∀ Z ∈ 𝒵, IsDj m₀ j Z) (h𝒴𝒵 : 𝒴 ⊆ 𝒵)
    {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {εH κH κ0 Kc : ℝ} (hε : 0 ≤ εH) (hκ0 : aEnt d L + 1 ≤ κ0)
    (A : ℂ → LabelAct (thickLabels 𝒴 h𝒴) Ωb εH κH κ0 Kc) {ι : Type*} [Fintype ι]
    (y0 : ι → {Y // Y ∈ 𝒴}) (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ)) :
    gsumCoeff μ (thickLabels 𝒵 h𝒵) (fun s => thickActExtend hN hj h𝒴 h𝒵 h𝒴𝒵 hε hκ0 (A s))
        (fun i => thickIncl h𝒴𝒵 (y0 i)) G T =
      gsumCoeff μ (thickLabels 𝒴 h𝒴) A y0 G T :=
  gsumCoeff_extend (thickLabels 𝒴 h𝒴) (thickLabels 𝒵 h𝒵) (thickIncl_injective h𝒴𝒵)
    (fun _ => rfl) (fun _ => rfl) μ hε (fun b => entropy_thick hN hj 𝒵 h𝒵 hκ0 b) A y0 G T

end Thick

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ : ℕ}

open Classical in
/-- **T4.**  Root-anchored prefactor bound for the domains of a finite family: the sum, over the
domains `Z` containing the root cube, of `F e^{-κ₀ d^cov_K(Z)}` is at most `F · K0 d L κ₀`.  The
constant depends only on `d, L` (the bound `K0 d L κ₀` of `G2_X` via `entropy_thick`), not on
`z`, on the scale or on the torus size. -/
theorem rootAnchored_entropy_thick (hN : L ^ m₀ ∣ N₁) (𝒵 : Finset (Set (CTorus d L N₁ m₁ K)))
    (h𝒵 : ∀ Z ∈ 𝒵, IsDj m₀ K Z) {κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    (z : RootIdx d L N₁ m₁ K) {F : ℝ} (hF : 0 ≤ F) :
    ∑ Z : {Z // Z ∈ 𝒵}, (if rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Z.1 then
        F * Real.exp (-κ0 * treeLenCovOne m₀ K Z.1) else 0) ≤ F * K0 d L κ0 := by
  have h := entropy_thick hN (le_refl K) 𝒵 h𝒵 hκ0 (rootCube (m₀ := m₀) z)
  calc _ = F * ∑ Z : {Z // Z ∈ 𝒵}, (if box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K) ⊆ Z.1
          then Real.exp (-κ0 * treeLenCovOne m₀ K Z.1) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        by_cases hZ : box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K) ⊆ Z.1
        · simp [mem_blocksOf.2 hZ, hZ]
        · have : rootCube (m₀ := m₀) z ∉ blocksOf m₀ K Set.univ Z.1 := fun hh =>
            hZ (mem_blocksOf.1 hh)
          simp [this, hZ]
    _ ≤ F * K0 d L κ0 := mul_le_mul_of_nonneg_left h hF

open Classical in
/-- **T4 (marks).**  For a family of marks indexed by `ι` whose labels `y0 i` are distinct labels
of a label system `Lab` obeying the entropy hypothesis with constant `Kc`, and all contain the
root cube, with `F₀ i ≤ F`: `∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(y₀ᵢ)} ≤ F · Kc`. -/
theorem rootAnchored_mark_sum {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb)
    {κ0 Kc F : ℝ} (hF : 0 ≤ F)
    (hent : ∀ b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ,
      ∑ y : Lb, (if box b.1 (cellSide L m₀ m₁ K) ⊆ Lab.ysite y then
        Real.exp (-κ0 * Lab.dl y) else 0) ≤ Kc)
    (z : RootIdx d L N₁ m₁ K) (y0 : ι → Lb) (hinj : Function.Injective y0) (F0 : ι → ℝ)
    (hF0 : ∀ i, F0 i ≤ F)
    (hroot : ∀ i, rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) :
    ∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i)) ≤ F * Kc := by
  have h1 : ∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i)) ≤
      ∑ i, F * Real.exp (-κ0 * Lab.dl (y0 i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hF0 i) (Real.exp_pos _).le
  have h2 : ∑ i, Real.exp (-κ0 * Lab.dl (y0 i)) ≤ Kc := by
    refine le_trans ?_ (hent (rootCube (m₀ := m₀) z))
    calc ∑ i, Real.exp (-κ0 * Lab.dl (y0 i))
        = ∑ i, (if box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K) ⊆ Lab.ysite (y0 i) then
            Real.exp (-κ0 * Lab.dl (y0 i)) else 0) :=
          Finset.sum_congr rfl fun i _ => by simp [mem_blocksOf.1 (hroot i)]
      _ = ∑ y ∈ Finset.univ.image y0, (if box (rootCube (m₀ := m₀) z).1
            (cellSide L m₀ m₁ K) ⊆ Lab.ysite y then Real.exp (-κ0 * Lab.dl y) else 0) :=
          by rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ => by
          split_ifs
          · exact (Real.exp_pos _).le
          · exact le_rfl)
  calc _ ≤ ∑ i, F * Real.exp (-κ0 * Lab.dl (y0 i)) := h1
    _ = F * ∑ i, Real.exp (-κ0 * Lab.dl (y0 i)) := by rw [Finset.mul_sum]
    _ ≤ F * Kc := mul_le_mul_of_nonneg_left h2 hF

end Count

end Balaban.Fluctuation
