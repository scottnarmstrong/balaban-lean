/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoCover
public import Balaban.Localization.Decoupled2Solve
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the exact transport of the decoupled Green's operator

The decoupled Green's operator `G_s(A) = G*_s(A) (1 - 𝒦_s(A))⁻¹` of a pair (cover `C = coverOf Gc`,
operator set `H`) is built from the cube operators of `H` at the centres of `Gc`, the partition of
unity of `Gc` and the cut weights.  When `Gc` and `H` are carried by the box map onto `Hc` and `H'`
(`OmegaIso`), all these matrices on `Ω₁(H)` are the reindexings of those on `Ω₁(H')`, for
potentials and parameters corresponding under the bijections `e` of the sites and `cubeEquiv` of
the centres.

* `chiD_submatrix`, `Kz_submatrix`, `Gstar_submatrix`, `Kcal_submatrix`, `Gs_submatrix`;
* `extS_eq`, `decG_submatrix`: the Green family `α ↦ G_s(α)` of the decoupled problem at
  corresponding parameters.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' ϱc ϱc' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "cm" => (Prod.map id bm : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁' m₁ K)

/-- The submatrix of a sum over a finite set. -/
theorem submatrix_finset_sum {ι α β R : Type*} [AddCommMonoid R] (s : Finset ι)
    (f : ι → Matrix α α R) (e : β → α) :
    (∑ i ∈ s, f i).submatrix e e = ∑ i ∈ s, (f i).submatrix e e := by
  ext x y
  simp [Matrix.sum_apply]

/-- The submatrix of a difference (pointwise form of `Matrix.submatrix_sub`). -/
theorem submatrix_sub_apply {α β R : Type*} [Sub R] (A B : Matrix α α R) (e : β → α) :
    (A - B).submatrix e e = A.submatrix e e - B.submatrix e e := rfl

/-- The submatrix of a scalar multiple (pointwise form of `Matrix.submatrix_smul`). -/
theorem submatrix_smul_apply {α β R S : Type*} [SMul S R] (r : S) (A : Matrix α α R)
    (e : β → α) : (r • A).submatrix e e = r • A.submatrix e e := rfl

/-- The cut weights of the cover of a generating set are those of the set. -/
theorem decCover_sProd_coverOf (Gc : GeneratingSet d L (N₁ * L ^ m₁) K ϱc)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    (coverOf Gc).sProd s q = sProd Gc s q := rfl

namespace OmegaIso

section Pair

variable {Gc : GeneratingSet d L (N₁ * L ^ m₁) K ϱc} {Hc : GeneratingSet d L (N₁' * L ^ m₁) K ϱc'}
  {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ} (hC : OmegaIso Gc Hc ρ) (hH : OmegaIso H H' ρ)

include hC hH

/-- **The partition weights as multipliers on `Ω₁(H)`.** -/
theorem chiD_submatrix {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx Gc) :
    (Dec2.chiD (coverOf Gc) H q).submatrix hH.e.symm hH.e.symm =
      Dec2.chiD (coverOf Hc) H' (cm q) := by
  unfold Dec2.chiD
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x'
  obtain ⟨x, rfl⟩ := hH.e.surjective x'
  simp only [Function.comp_apply, Equiv.symm_apply_apply, OmegaIso.coe_e]
  show ((chi Gc q x : ℝ) : ℂ) = ((chi Hc (cm q) (bm x) : ℝ) : ℂ)
  rw [hC.chi_eq hq (hH.boxG x x.2)]

omit hC in
/-- The Dirichlet operator at the zero potential. -/
theorem dirichletOperator_zero_submatrix (a : ℕ → ℝ) (ν : ℝ) :
    (dirichletOperator H a ν 0).submatrix hH.e.symm hH.e.symm = dirichletOperator H' a ν 0 :=
  hH.dirichletOperator_submatrix a ν (fun _ => rfl)

/-- **The commutators `K_z`.** -/
theorem Kz_submatrix (a : ℕ → ℝ) (ν : ℝ) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx Gc) :
    (Dec2.Kz (coverOf Gc) H a ν q).submatrix hH.e.symm hH.e.symm =
      Dec2.Kz (coverOf Hc) H' a ν (cm q) := by
  unfold Dec2.Kz
  rw [submatrix_sub_apply, ← Matrix.submatrix_mul_equiv _ _ _ hH.e.symm,
    ← Matrix.submatrix_mul_equiv _ _ _ hH.e.symm, hC.chiD_submatrix hH hq,
    hH.dirichletOperator_zero_submatrix a ν]

/-- The cube resolvent of a centre of the cover. -/
theorem cubeG_cover_submatrix (a : ℕ → ℝ) (ν : ℝ) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx Gc) {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hα : ∀ x, α' (hH.e x) = α x) :
    (cubeG H a ν α q).submatrix hH.e.symm hH.e.symm = cubeG H' a ν α' (cm q) := by
  obtain ⟨⟨-, hj⟩, -, -⟩ := (mem_cubeIdx Gc).1 hq
  obtain ⟨j, y0⟩ := q
  exact hH.cubeG_submatrix a ν hj (hC.base_inBox hq) hα

/-- **`G*_s(A)`** at potentials and cut parameters corresponding on the centres. -/
theorem Gstar_submatrix (a : ℕ → ℝ) (ν : ℝ) {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    (hα : ∀ x, α' (hH.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ K → ℂ} (hs : ∀ P ∈ cubeIdx Gc, s' (cm P) = s P) :
    (Dec2.Gstar (coverOf Gc) H a ν α s).submatrix hH.e.symm hH.e.symm =
      Dec2.Gstar (coverOf Hc) H' a ν α' s' := by
  unfold Dec2.Gstar
  rw [submatrix_finset_sum]
  show _ = ∑ q ∈ cubeIdx Hc, _
  rw [← hC.cubeIdx_image, Finset.sum_image hC.cm_injOn]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [submatrix_smul_apply, ← Matrix.submatrix_mul_equiv _ _ _ hH.e.symm,
    hC.chiD_submatrix hH hq, hC.cubeG_cover_submatrix hH a ν hq hα, decCover_sProd_coverOf,
    decCover_sProd_coverOf, hC.sProd_eq hq hs]

/-- **`𝒦_s(A)`** at potentials and cut parameters corresponding on the centres. -/
theorem Kcal_submatrix (a : ℕ → ℝ) (ν : ℝ) {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    (hα : ∀ x, α' (hH.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ K → ℂ} (hs : ∀ P ∈ cubeIdx Gc, s' (cm P) = s P) :
    (Dec2.Kcal (coverOf Gc) H a ν α s).submatrix hH.e.symm hH.e.symm =
      Dec2.Kcal (coverOf Hc) H' a ν α' s' := by
  unfold Dec2.Kcal
  rw [submatrix_finset_sum]
  show _ = ∑ q ∈ cubeIdx Hc, _
  rw [← hC.cubeIdx_image, Finset.sum_image hC.cm_injOn]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [submatrix_smul_apply, ← Matrix.submatrix_mul_equiv _ _ _ hH.e.symm,
    hC.Kz_submatrix hH a ν hq, hC.cubeG_cover_submatrix hH a ν hq hα, decCover_sProd_coverOf,
    decCover_sProd_coverOf, hC.sProd_eq hq hs]

/-- **The decoupled Green's operator `G_s(A)`** at potentials and cut parameters corresponding on
the centres. -/
theorem Gs_submatrix (a : ℕ → ℝ) (ν : ℝ) {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    (hα : ∀ x, α' (hH.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ K → ℂ} (hs : ∀ P ∈ cubeIdx Gc, s' (cm P) = s P) :
    (Dec2.Gs (coverOf Gc) H a ν α s).submatrix hH.e.symm hH.e.symm =
      Dec2.Gs (coverOf Hc) H' a ν α' s' := by
  unfold Dec2.Gs
  rw [← Matrix.submatrix_mul_equiv _ _ _ hH.e.symm, ← Matrix.inv_submatrix_equiv,
    submatrix_sub_apply, Matrix.submatrix_one_equiv, hC.Gstar_submatrix hH a ν hα hs,
    hC.Kcal_submatrix hH a ν hα hs]

omit hH in
/-- The extension by `1` of corresponding parameters of the centres. -/
theorem extS_eq {s : Dec2.DecParams (coverOf Gc)} {s' : Dec2.DecParams (coverOf Hc)}
    (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx Gc) : Dec2.extS (coverOf Hc) s' (cm P) = Dec2.extS (coverOf Gc) s P := by
  have hP' : cm P ∈ cubeIdx Hc := hC.mem_cubeIdx_map hP
  unfold Dec2.extS
  simp only [show cm P ∈ (coverOf Hc).cubeIdx from hP', show P ∈ (coverOf Gc).cubeIdx from hP,
    ↓reduceDIte]
  exact hs ⟨P, hP⟩

/-- **The Green family of the decoupled problem** at corresponding parameters of the centres and
corresponding potentials. -/
theorem decG_submatrix (a : ℕ → ℝ) (ν : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hα : ∀ x, α' (hH.e x) = α x) :
    (Dec2.decG (coverOf Gc) H a ν s α).submatrix hH.e.symm hH.e.symm =
      Dec2.decG (coverOf Hc) H' a ν s' α' :=
  hC.Gs_submatrix hH a ν hα fun _ hP => hC.extS_eq hs hP

end Pair

end OmegaIso

end Balaban.Polymer.LocalIso
