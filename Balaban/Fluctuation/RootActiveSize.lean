/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31CoeffA
public import Balaban.Fluctuation.SizeModCore
public import Balaban.Fluctuation.SizeModG1
public import Balaban.Fluctuation.SizeModEntropy
public import Balaban.SmallField.Def6Terms
public import Balaban.Localization.TreeLengthPaper
public import Balaban.Polymer.MarkedCubesLocal
public import Balaban.Polymer.MarkedCubesVanish
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Active cube sets: the two sizes agree

The canonical coefficients of Theorem 3.1 (`gsumCoeff`, `interpCoeff`) are indexed by finite sets
`T` of level-`K` cubes and are bounded by `exp(-κ' dExt T)`; the terms of the inductive class are
indexed by polymers `X` and bounded by `exp(-κ sizeJ X)`.  This file shows that on the cube sets
where a coefficient can be non-zero the two sizes are equal, with no constants lost, and that the
coefficients vanish elsewhere.  Everything is at `Ω = univ` (the whole-lattice step) and at the
level `K` of the cubes.

* `isPolyDom_and_dExt_eq_sizeJ`: for non-empty `T` with `dOmega m₀ K univ (sitesOf T) ≠ ⊤`, the
  set `sitesOf T` is a polymer (`IsPolyDom`) and `dExt T = sizeJ m₀ K (sitesOf T)`.
* `isPolyDom_iff_dOmega_ne_top`: the converse, so for every `T`
  `IsPolyDom m₀ K (sitesOf T) ↔ T.Nonempty ∧ dOmega m₀ K univ (sitesOf T) ≠ ⊤`.
* `dOmega_empty`: for `T = ∅` the size `dOmega` is `⊤` (a connected structure is non-empty, so no
  admissible pair exists inside the empty set); hence `gsumCoeff … ∅ = 0` and `interpCoeff I ∅ = 0`,
  while `e1Coeff I D ∅ = D.term ∅`.
* `gsumCoeff_eq_zero_of_dOmega_top`, `interpCoeff_eq_zero_of_dOmega_top`: vanishing at `dOmega = ⊤`.
* `exists_blocksOf_subset_of_interpCoeff_ne_zero`: a non-zero interpolation coefficient has a mark
  label whose blocks lie in `T`.
* `interpCoeff_ne_zero_active`, `norm_interpCoeff_le_sizeJ`: the statement used downstream, with the
  bound in class form `exp(-κ' sizeJ)`.
* `sizeJ_le_treeLenAll_le`: the papers' size `treeLenAll` is bounded by an affine function of
  `dExt T`; the class bound uses `sizeJ`, so the comparison needed there is with constants `1`
  and `0`, which is the equality above.

## Scope

This file does not prove that the marks contain the root cube of the energy term (the
ROOT-MARK-ANCHOR of `notes/phase1/ROOT.md`), and it proves nothing about the determinant term
`D.term`.  Nothing here depends on a choice of generating set for the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

section Sizes

omit [NeZero N₁] [NeZero L] in
/-- At `Ω = univ` the hat of a set is the set itself. -/
theorem Yhat_univ (S : Set (CTorus d L N₁ m₁ K)) : Yhat Set.univ S = S := by
  ext y
  simp [Yhat]

omit [NeZero N₁] [NeZero L] in
/-- For a connected set the whole-lattice size `dOmega` is the extended covering cost. -/
theorem dOmega_univ_of_siteConnected {S : Set (CTorus d L N₁ m₁ K)} (h : SiteConnected S) :
    dOmega m₀ K Set.univ S = dcovModE m₀ K Set.univ S := by
  classical
  unfold dOmega
  rw [Yhat_univ]
  simp [h]

omit [NeZero N₁] [NeZero L] in
/-- If `dOmega` is finite then the set is site-connected and the covering cost is finite. -/
theorem siteConnected_of_dOmega_ne_top {S : Set (CTorus d L N₁ m₁ K)}
    (h : dOmega m₀ K Set.univ S ≠ ⊤) :
    SiteConnected S ∧ dOmega m₀ K Set.univ S = dcovModE m₀ K Set.univ S := by
  classical
  have hc : SiteConnected S := by
    by_contra hc
    apply h
    unfold dOmega
    rw [Yhat_univ]
    simp [hc]
  exact ⟨hc, dOmega_univ_of_siteConnected hc⟩

/-- **Size lemma (R1).**  For non-empty `T` with finite `dOmega`, the set `sitesOf T` is a polymer
and `dExt T` equals `sizeJ` of it. -/
theorem isPolyDom_and_dExt_eq_sizeJ {T : Finset 𝔅} (hT : T.Nonempty)
    (h : dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤) :
    IsPolyDom m₀ K (sitesOf T) ∧ dExt T = sizeJ m₀ K (sitesOf T) := by
  obtain ⟨hc, hE⟩ := siteConnected_of_dOmega_ne_top h
  have hfin : dcovModE m₀ K Set.univ (sitesOf T) ≠ ⊤ := hE ▸ h
  obtain ⟨𝒦, W, E, hadm⟩ := exists_admissible_of_ne_top hfin
  obtain ⟨hch, -, -, -⟩ := (modAdmissible_iff_chosen (Set.subset_univ (sitesOf T))).1 hadm
  have hne : (sitesOf T).Nonempty := by
    obtain ⟨b, hb⟩ := hT
    exact ⟨b.1, mem_sitesOf.2 ⟨b, hb, mem_box_self _ (cellSide_pos (L := L) m₀ m₁ K)⟩⟩
  refine ⟨⟨hne, ⟨𝒦, hch⟩, hc⟩, ?_⟩
  rw [dExt_eq_toReal h, hE]
  exact dcovMod_of_subset (Set.subset_univ _)

/-- A polymer has finite whole-lattice size. -/
theorem dOmega_ne_top_of_isPolyDom {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ K X) :
    dOmega m₀ K Set.univ X ≠ ⊤ := by
  obtain ⟨hne, ⟨𝒦, hch, hcov⟩, hc⟩ := hX
  have hDj : IsDj m₀ K X := by
    refine ⟨hne, fun z hz => ?_, hc⟩
    obtain ⟨b, hb, hzb⟩ := hcov z hz
    exact ⟨b, (hch b hb).1, hzb, (hch b hb).2⟩
  rw [dOmega_univ_of_siteConnected hDj.2.2]
  exact dcovModE_ne_top_of_IsDj hDj

/-- **The converse of the size lemma.**  A set of cubes is a polymer exactly when it is non-empty
and has finite whole-lattice size. -/
theorem isPolyDom_iff_dOmega_ne_top {T : Finset 𝔅} :
    IsPolyDom m₀ K (sitesOf T) ↔ T.Nonempty ∧ dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤ := by
  constructor
  · intro hX
    refine ⟨?_, dOmega_ne_top_of_isPolyDom hX⟩
    obtain ⟨z, hz⟩ := hX.1
    obtain ⟨b, hb, -⟩ := mem_sitesOf.1 hz
    exact ⟨b, hb⟩
  · rintro ⟨hT, h⟩
    exact (isPolyDom_and_dExt_eq_sizeJ hT h).1

/-- (R1) in the converse direction: for a polymer `sitesOf T`, `dExt T = sizeJ`. -/
theorem dExt_eq_sizeJ_of_isPolyDom {T : Finset 𝔅} (hX : IsPolyDom m₀ K (sitesOf T)) :
    dExt T = sizeJ m₀ K (sitesOf T) :=
  (isPolyDom_and_dExt_eq_sizeJ (isPolyDom_iff_dOmega_ne_top.1 hX).1
    (isPolyDom_iff_dOmega_ne_top.1 hX).2).2

omit [NeZero N₁] [NeZero L] in
theorem sitesOf_empty : sitesOf (∅ : Finset 𝔅) = ∅ := by
  ext z
  simp [mem_sitesOf]

omit [NeZero N₁] [NeZero L] in
/-- **The empty set of cubes.**  `dOmega` of `sitesOf ∅` is `⊤`: a connected structure is
non-empty, so no admissible pair lies inside the empty set. -/
theorem dOmega_empty : dOmega m₀ K Set.univ (sitesOf (∅ : Finset 𝔅)) = ⊤ := by
  by_contra h
  obtain ⟨-, hE⟩ := siteConnected_of_dOmega_ne_top h
  obtain ⟨𝒦, W, E, hadm⟩ := exists_admissible_of_ne_top (hE ▸ h)
  obtain ⟨-, ⟨⟨w, hw⟩, -⟩, hWX, -⟩ :=
    (modAdmissible_iff_chosen (Set.subset_univ (sitesOf (∅ : Finset 𝔅)))).1 hadm
  have := hWX hw
  rw [sitesOf_empty] at this
  exact this

theorem dExt_empty : dExt (∅ : Finset 𝔅) = Mbig d L N₁ m₁ K :=
  dExt_eq_Mbig dOmega_empty

/-- **The papers' size.**  For a non-empty `T` with finite `dOmega`,
`sizeJ ≤ treeLenAll ≤ A * dExt T + B` with `A = 1 + 2 d L c₁(d,L)`, `B = 2 d L c₁(d,L)`.
The class bound uses `sizeJ` itself, for which the comparison with `dExt` has constants `1`
and `0` (`isPolyDom_and_dExt_eq_sizeJ`). -/
theorem sizeJ_le_treeLenAll_le (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅} (hT : T.Nonempty)
    (h : dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤) :
    sizeJ m₀ K (sitesOf T) ≤ treeLenAll m₀ K (sitesOf T) ∧
    treeLenAll m₀ K (sitesOf T) ≤
      (1 + 2 * d * L * c1 d L) * dExt T + 2 * d * L * c1 d L := by
  obtain ⟨hX, hd⟩ := isPolyDom_and_dExt_eq_sizeJ hT h
  have hDj : IsDj m₀ K (sitesOf T) := by
    obtain ⟨hne, ⟨𝒦, hch, hcov⟩, hc⟩ := hX
    refine ⟨hne, fun z hz => ?_, hc⟩
    obtain ⟨b, hb, hzb⟩ := hcov z hz
    exact ⟨b, (hch b hb).1, hzb, (hch b hb).2⟩
  refine ⟨treeLenCovOne_le_treeLenAll hDj, ?_⟩
  rw [hd]
  exact treeLenAll_le hN le_rfl hDj

end Sizes

section Vanishing

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

theorem isPiUnion_univ_K : IsPiUnion m₀ K (Set.univ : Set (CTorus d L N₁ m₁ K)) :=
  fun z _ => ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z,
    mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) z, Set.subset_univ _⟩

/-- **Vanishing of the interpolation integral** at `dOmega = ⊤`. -/
theorem gsumCoeff_eq_zero_of_dOmega_top (hN : L ^ m₀ ∣ N₁)
    {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ K Set.univ Lb)
    {εH κH κ0 Kc : ℝ} (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) {T : Finset 𝔅}
    (hT : dOmega m₀ K Set.univ (sitesOf T) = ⊤) : gsumCoeff μ Lab A y0 G T = 0 := by
  classical
  unfold gsumCoeff Gsum
  have : (fun s : ℝ => ∑ i, Gst μ Lab (A (s : ℂ)).H (blocksOf m₀ K Set.univ (Lab.ysite (y0 i)))
      (G i (s : ℂ)) T) = fun _ => 0 :=
    funext fun s => Finset.sum_eq_zero fun i _ =>
      Gst_eq_zero_of_dOmega_top μ hN le_rfl isPiUnion_univ_K Lab _ (y0 i) _ T hT
  simp only [this]
  simp

section Interp

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {BS : ProdSplit ν d L N₁ m₁ K m₀}
  {W f : ℝ → X → ℂ}

/-- **Vanishing of `interpCoeff`** at `dOmega = ⊤`. -/
theorem interpCoeff_eq_zero_of_dOmega_top (I : InterpMarks ν BS W f) {T : Finset 𝔅}
    (hT : dOmega m₀ K Set.univ (sitesOf T) = ⊤) : interpCoeff I T = 0 :=
  gsumCoeff_eq_zero_of_dOmega_top I.hN _ _ _ _ _ hT

/-- `interpCoeff I ∅ = 0`. -/
theorem interpCoeff_empty (I : InterpMarks ν BS W f) : interpCoeff I (∅ : Finset 𝔅) = 0 :=
  interpCoeff_eq_zero_of_dOmega_top I dOmega_empty

/-- **Support.**  If `interpCoeff I T ≠ 0` then the blocks of some mark label lie in `T`. -/
theorem exists_blocksOf_subset_of_interpCoeff_ne_zero (I : InterpMarks ν BS W f) {T : Finset 𝔅}
    (h : interpCoeff I T ≠ 0) :
    ∃ i, blocksOf m₀ K Set.univ (I.Lab.ysite (I.y0 i)) ⊆ T := by
  classical
  by_contra hno
  push Not at hno
  apply h
  unfold interpCoeff gsumCoeff Gsum
  have : (fun s : ℝ => ∑ i, Gst BS.μ I.Lab (I.A (s : ℂ)).H
      (blocksOf m₀ K Set.univ (I.Lab.ysite (I.y0 i))) (I.G i (s : ℂ)) T) = fun _ => 0 :=
    funext fun s => Finset.sum_eq_zero fun i _ =>
      (marked_cubes_explicit BS.μ I.hN le_rfl isPiUnion_univ_K (I.A (s : ℂ)) (I.y0 i)
        (I.G i (s : ℂ)) (I.meas i _) (I.dep i _) (I.bound i _) I.hκ0 I.hKc I.hεpos (I.hF0 i)
        I.hκ' I.hκG I.hκ I.hε).2.2.2.1 T (hno i)
  simp only [this]
  simp

/-- **Active sets.**  A non-zero interpolation coefficient has `T` non-empty, `sitesOf T` a polymer
and `dExt T = sizeJ`. -/
theorem interpCoeff_ne_zero_active (I : InterpMarks ν BS W f) {T : Finset 𝔅}
    (h : interpCoeff I T ≠ 0) :
    T.Nonempty ∧ IsPolyDom m₀ K (sitesOf T) ∧ dExt T = sizeJ m₀ K (sitesOf T) := by
  classical
  obtain ⟨i, hi⟩ := exists_blocksOf_subset_of_interpCoeff_ne_zero I h
  have hne : T.Nonempty :=
    (I.Lab.blocksOf_nonempty I.hN le_rfl isPiUnion_univ_K (I.y0 i)).mono hi
  have htop : dOmega m₀ K Set.univ (sitesOf T) ≠ ⊤ := fun ht =>
    h (interpCoeff_eq_zero_of_dOmega_top I ht)
  exact ⟨hne, (isPolyDom_and_dExt_eq_sizeJ hne htop).1, (isPolyDom_and_dExt_eq_sizeJ hne htop).2⟩

open Classical in
/-- **The bound in class form.**  For every `T`,
`‖interpCoeff I T‖ ≤ C_PE (∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) exp(-κ' sizeJ m₀ K (sitesOf T))` (the same
prefactor as `interpCoeff_spec`); for `T` where the coefficient is non-zero this is the bound of
`interpCoeff_spec` with `dExt T` replaced by `sizeJ`, and elsewhere the left side is `0`. -/
theorem norm_interpCoeff_le_sizeJ (I : InterpMarks ν BS W f) (T : Finset 𝔅) :
    ‖interpCoeff I T‖ ≤ CPE d L I.Kc I.κH I.κ0 I.κ' *
        (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) *
        Real.exp (-I.κ' * sizeJ m₀ K (sitesOf T)) := by
  by_cases h : interpCoeff I T = 0
  · rw [h, norm_zero]
    have hc : 0 ≤ CPE d L I.Kc I.κH I.κ0 I.κ' := by unfold CPE c1; positivity
    have hs : 0 ≤ ∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (I.hF0 i).le (Real.exp_pos _).le
    positivity
  · have := (interpCoeff_spec I).2 T
    rwa [(interpCoeff_ne_zero_active I h).2.2] at this

end Interp

section E1

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀} {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))}

/-- At `T = ∅` the term of Theorem 3.1 (a) is the determinant term alone (this file says nothing
else about that term). -/
theorem e1Coeff_empty (I : E1Marks S C BS z) {κ'' cdet : ℝ}
    (D : DetExpansion S m₀ z κ'' cdet) : e1Coeff I D ∅ = D.term ∅ := by
  unfold e1Coeff
  rw [interpCoeff_empty, add_zero]

end E1

end Vanishing

end Balaban.Fluctuation
