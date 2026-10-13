/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.RootPavingMap
public import Balaban.Fluctuation.Thm31Witness
import Mathlib.Tactic.Positivity

/-!
# The marked part of the new energy terms, rooted (ROOT.md §4, formula (R7), marked part)

For a family `I z` of interpolation marks (one `InterpMarks` for each root `z` of the next-scale
torus, all over the same block split) the marked part of the energy term rooted at `y` and living
on the polymer `X` is the rooted sum of the canonical coefficients
`markedTerm I y X = ∑_{z : rootSite z = y} ∑_{T : sitesOf T = X} interpCoeff (I z) T`.

* `markedTerm_ne_zero_imp`, `markedTerm_rootSite_sitesOf`: support; the term vanishes unless `X`
  is a polymer of `𝒟_K` and `y` is the root site of some `z`, and at `(rootSite z, sitesOf T)` it
  is `interpCoeff (I z) T`.
* `norm_markedTerm_le`: the class bound `‖markedTerm I y X‖ ≤ B exp(-κ' sizeJ X)` from a uniform
  bound `B` on the prefactors and a common rate `κ'`.  No hypothesis on sizes remains: the
  identity `dExt T = sizeJ (sitesOf T)` on the support comes from `interpCoeff_ne_zero_active`.
* `y_mem_of_markedTerm_ne_zero_of_anchor`: conditionally on the anchor premise
  (a non-zero coefficient has the root cube in `T`), `markedTerm I y X ≠ 0 → y ∈ X`;
  `anchor_of_labels` derives the anchor from the condition that every mark label of `I z`
  contains the root cube of `z`.
* `sum_markedTerm`: the sum of all marked terms over roots and polymers is the sum of all the
  coefficients; `sum_markedTerm_e1` is its form for `E1Marks`: it equals `∑_z E1loc(z)`.
* `markedTerm_covariant`: conditional covariance, from an explicit covariance premise.
* `markedTerm_nonvacuous`: an instance on the actual step datum of `Thm31Witness`.

## Scope

Nothing here constructs a `Terms` structure, a generating set of terms or a field domain.  Not
proved here: the determinant part of the new terms, the anchor of the physical marks at the root
cube, the dependence of the terms on the datum (analyticity and locality in the fields) and the
covariance of the coefficients.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 MeasureTheory

section Marked

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {BS : ProdSplit ν d L N₁ m₁ K m₀}
  {W : ℝ → Ω → ℂ} {f : RootIdx d L N₁ m₁ K → ℝ → Ω → ℂ}

/-- **The marked part of the new energy term**, rooted at the site `y` and living on the set `X`:
the rooted sum, over the roots `z` and the finite sets `T` of level-`K` cubes with
`rootSite z = y` and `sitesOf T = X`, of the interpolation coefficients `interpCoeff (I z) T`. -/
noncomputable def markedTerm (I : ∀ z : RootIdx d L N₁ m₁ K, InterpMarks ν BS W (f z))
    (y : CTorus d L N₁ m₁ K) (X : Set (CTorus d L N₁ m₁ K)) : ℂ :=
  rootedSum (fun z T => interpCoeff (I z) T) y X

variable (I : ∀ z : RootIdx d L N₁ m₁ K, InterpMarks ν BS W (f z))

/-- If the marked term is non-zero, some pair `(z, T)` over `(y, X)` has a non-zero
coefficient. -/
theorem exists_pair_of_markedTerm_ne_zero (hN : L ^ m₀ ∣ N₁) {y : CTorus d L N₁ m₁ K}
    {X : Set (CTorus d L N₁ m₁ K)} (h : markedTerm I y X ≠ 0) :
    ∃ (z : RootIdx d L N₁ m₁ K) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) m₀ K Set.univ)), rootSite z = y ∧ sitesOf T = X ∧ interpCoeff (I z) T ≠ 0 := by
  by_contra hno
  apply h
  by_cases hex : ∃ (z : RootIdx d L N₁ m₁ K) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) m₀ K Set.univ)), rootSite z = y ∧ sitesOf T = X
  · obtain ⟨z, T, hz, hT⟩ := hex
    unfold markedTerm
    rw [rootedSum_eq_of_pair hN _ hz hT]
    by_contra hc
    exact hno ⟨z, T, hz, hT, hc⟩
  · exact rootedSum_eq_zero _ hex

/-- **Support.**  The marked term is non-zero only on a polymer of `𝒟_K` and at the root site of
some `z`. -/
theorem markedTerm_ne_zero_imp (hN : L ^ m₀ ∣ N₁) {y : CTorus d L N₁ m₁ K}
    {X : Set (CTorus d L N₁ m₁ K)} (h : markedTerm I y X ≠ 0) :
    IsPolyDom m₀ K X ∧ ∃ z : RootIdx d L N₁ m₁ K, y = rootSite z := by
  obtain ⟨z, T, hz, hT, hc⟩ := exists_pair_of_markedTerm_ne_zero I hN h
  exact ⟨hT ▸ (interpCoeff_ne_zero_active (I z) hc).2.1, z, hz.symm⟩

/-- At `(rootSite z, sitesOf T)` the marked term is the coefficient `interpCoeff (I z) T`. -/
theorem markedTerm_rootSite_sitesOf (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    markedTerm I (rootSite z) (sitesOf T) = interpCoeff (I z) T :=
  rootedSum_rootSite_sitesOf hN (fun z T => interpCoeff (I z) T) z T

open Classical in
/-- **The class bound for the marked part ((R7), marked coefficients).**  If the prefactors
`C_PE ∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}` of the marks are bounded by `B` for all roots and all marks have the
rate `κ'`, then `‖markedTerm I y X‖ ≤ B exp(-κ' sizeJ X)` for all `y` and `X`. -/
theorem norm_markedTerm_le (hN : L ^ m₀ ∣ N₁) {B κ' : ℝ}
    (hB : ∀ z, CPE d L (I z).Kc (I z).κH (I z).κ0 (I z).κ' *
      (∑ i, (I z).F0 i * Real.exp (-(I z).κ0 * (I z).Lab.dl ((I z).y0 i))) ≤ B)
    (hκ : ∀ z, (I z).κ' = κ') (y : CTorus d L N₁ m₁ K) (X : Set (CTorus d L N₁ m₁ K)) :
    ‖markedTerm I y X‖ ≤ B * Real.exp (-κ' * sizeJ m₀ K X) := by
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (hB 0)
    have hc : 0 ≤ CPE d L (I 0).Kc (I 0).κH (I 0).κ0 (I 0).κ' := by unfold CPE c1; positivity
    have hs : 0 ≤ ∑ i, (I 0).F0 i * Real.exp (-(I 0).κ0 * (I 0).Lab.dl ((I 0).y0 i)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg ((I 0).hF0 i).le (Real.exp_pos _).le
    positivity
  refine rootedSum_norm_le_of_activeSize hN hB0 (fun z T => ?_)
    (fun z T h => (interpCoeff_ne_zero_active (I z) h).2.2) y X
  have h1 := (interpCoeff_spec (I z)).2 T
  calc ‖interpCoeff (I z) T‖
      ≤ CPE d L (I z).Kc (I z).κH (I z).κ0 (I z).κ' *
        (∑ i, (I z).F0 i * Real.exp (-(I z).κ0 * (I z).Lab.dl ((I z).y0 i))) *
        Real.exp (-(I z).κ' * dExt T) := h1
    _ ≤ B * Real.exp (-(I z).κ' * dExt T) :=
        mul_le_mul_of_nonneg_right (hB z) (Real.exp_pos _).le
    _ = B * Real.exp (-κ' * dExt T) := by rw [hκ z]

/-- **Root in the polymer, conditional on the anchor** (ROOT-MARK-ANCHOR, not proved here): if a
non-zero coefficient `interpCoeff (I z) T` has the root cube of `z` in `T`, then a non-zero marked
term has its root in the polymer. -/
theorem y_mem_of_markedTerm_ne_zero_of_anchor (hN : L ^ m₀ ∣ N₁)
    (hanchor : ∀ (z : RootIdx d L N₁ m₁ K) (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) m₀ K Set.univ)), interpCoeff (I z) T ≠ 0 → rootCube z ∈ T)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (h : markedTerm I y X ≠ 0) :
    y ∈ X := by
  obtain ⟨z, T, hz, hT, hc⟩ := exists_pair_of_markedTerm_ne_zero I hN h
  rw [← hz, ← hT]
  exact (rootSite_mem_sitesOf_iff hN z T).2 (hanchor z T hc)

/-- **What the landed support theorem gives without the anchor**: a non-zero coefficient has the
cubes of some mark label inside `T`. -/
theorem exists_label_blocks_subset (z : RootIdx d L N₁ m₁ K)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (h : interpCoeff (I z) T ≠ 0) :
    ∃ i, blocksOf m₀ K Set.univ ((I z).Lab.ysite ((I z).y0 i)) ⊆ T :=
  exists_blocksOf_subset_of_interpCoeff_ne_zero (I z) h

/-- **The anchor from the labels.**  If every mark label of `I z` contains the root cube of `z`
among its cubes, then a non-zero coefficient of `I z` has the root cube of `z` in `T`. -/
theorem anchor_of_labels
    (hlab : ∀ (z : RootIdx d L N₁ m₁ K) i,
      rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ ((I z).Lab.ysite ((I z).y0 i)))
    (z : RootIdx d L N₁ m₁ K) {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) m₀ K Set.univ)} (h : interpCoeff (I z) T ≠ 0) : rootCube z ∈ T := by
  obtain ⟨i, hi⟩ := exists_label_blocks_subset I z h
  exact hi (hlab z i)

open Classical in
/-- **Sum over roots.**  Summing the marked terms over all roots `y` and all polymers `X` (the
values of `sitesOf`) gives the sum of all the coefficients over `z` and `T`. -/
theorem sum_markedTerm (hN : L ^ m₀ ∣ N₁) :
    ∑ y : CTorus d L N₁ m₁ K, ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L)
        (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ))).image sitesOf, markedTerm I y X =
      ∑ z : RootIdx d L N₁ m₁ K, ∑ T, interpCoeff (I z) T := by
  have hN' := hN
  unfold markedTerm rootedSum
  have e1 : ∀ y : CTorus d L N₁ m₁ K,
      ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := K) m₀ K Set.univ))).image sitesOf,
        ∑ z ∈ Finset.univ.filter (fun z => rootSite z = y),
          ∑ T ∈ Finset.univ.filter (fun T => sitesOf T = X), interpCoeff (I z) T =
      ∑ z ∈ Finset.univ.filter (fun z => rootSite z = y), ∑ T, interpCoeff (I z) T := by
    intro y
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image sitesOf)
      (g := sitesOf) (fun T _ => Finset.mem_image_of_mem _ (Finset.mem_univ T))
      (fun T => interpCoeff (I z) T)
  rw [Finset.sum_congr rfl fun y _ => e1 y]
  exact Finset.sum_fiberwise (Finset.univ : Finset (RootIdx d L N₁ m₁ K)) rootSite
    (fun z => ∑ T, interpCoeff (I z) T)

open Classical in
/-- **Covariance, conditional** (ROOT-COEFF-COV): if the coefficient families of `I` and `I'` are
related by `interpCoeff (I' (rootAct r z)) (r • T) = interpCoeff (I z) T` for a paving symmetry
`r`, then `markedTerm I'` at the aligned root transformed by `r` and the transformed polymer
agrees with `markedTerm I` at `(y, X)`. -/
theorem markedTerm_covariant (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (I' : ∀ z : RootIdx d L N₁ m₁ K, InterpMarks ν BS W (f z))
    (hcov : ∀ z T, interpCoeff (I' (rootAct r z)) (cubeAct r T) = interpCoeff (I z) T)
    {y : CTorus d L N₁ m₁ K}
    (hy : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K y = y)
    (X : Set (CTorus d L N₁ m₁ K)) :
    markedTerm I' (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y)) (r '' X) =
      markedTerm I y X :=
  rootedSum_covariant hN hr (e := fun z T => interpCoeff (I z) T)
    (e' := fun z T => interpCoeff (I' z) T) hcov hy X

end Marked

section E1

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {BS : BlockSplit S m₀}

open Classical in
/-- **The marked terms reproduce the first-order energy terms.**  For a family of `E1Marks`, one
for each root `z`, the sum of all marked terms is `∑_z E1loc(z)`. -/
theorem sum_markedTerm_e1 (hN : L ^ m₀ ∣ N₁) {κ'' cdet : ℝ}
    (I : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), E1Marks S C BS z)
    (D : ∀ z, DetExpansion S m₀ z κ'' cdet) (hκ'' : ∀ z, (I z).κ' ≤ κ'') :
    ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d)
        (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))).image sitesOf,
        markedTerm (f := fun z s x =>
          (fderiv ℝ (S.Phi1 C) (s • S.shiftU x)) (S.maskU z (S.shiftU x))) I y X =
      ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E1loc C z := by
  rw [sum_markedTerm I hN]
  exact Finset.sum_congr rfl fun z _ => ((thm31a_coeff (I z) (hκ'' z) (D z)).1).symm

end E1

section Witness

open Balaban.Localization.I5Inhabited

/-- **Non-vacuity.**  On the actual step datum of `exists_e1Marks_datum` (`d = L = 3`, `N₁ = 6`,
`k = 1`), the constant family of the landed marks (the marks of the root `0`, used for every root)
has prefactors bounded by `B` by `Bf β`, with a common rate; so the hypotheses of
`norm_markedTerm_le` are satisfied and its conclusion holds.  (The landed marks carry one whole-torus label,
so the marked term is non-zero only at `X` the set of all sites.) -/
theorem markedTerm_nonvacuous (Bf : ℝ → ℝ) (hBf : ∀ β, 0 < β → 0 < Bf β) :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0)
      (I : ∀ _z : RootIdx 3 3 6 m₁ 2, InterpMarks S.nuFl BS
        (S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (fun s x =>
          (fderiv ℝ (S.Phi1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (s • S.shiftU x))
            (S.maskU (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (S.shiftU x)))),
      (∀ z, CPE 3 3 (I z).Kc (I z).κH (I z).κ0 (I z).κ' *
        (∑ i, (I z).F0 i * Real.exp (-(I z).κ0 * (I z).Lab.dl ((I z).y0 i))) ≤ Bf S.β) ∧
      (∀ _z, (I _z).κ' = (I 0).κ') ∧
      ∀ (y : CTorus 3 3 6 m₁ 2) (X : Set (CTorus 3 3 6 m₁ 2)),
        ‖markedTerm (f := fun _ s x =>
          (fderiv ℝ (S.Phi1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (s • S.shiftU x))
            (S.maskU (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (S.shiftU x))) I y X‖ ≤
          Bf S.β * Real.exp (-(I 0).κ' * sizeJ 0 2 X) := by
  obtain ⟨m₁, S, BS, -, -, -, -, I, hI⟩ := exists_e1Marks_datum Bf hBf
  exact ⟨m₁, S, BS, fun _ => I, fun _ => hI, fun _ => rfl,
    norm_markedTerm_le (fun _ => I) (by norm_num) (fun _ => hI) (fun _ => rfl)⟩

end Witness

end Balaban.Fluctuation
