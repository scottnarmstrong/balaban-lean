/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecCover
public import Balaban.Localization.DecoupledMain

/-!
# The decoupled Green's operator for a cover `C` and an operator generating set `H`

The definitions of `Decoupled.lean` with the cover (`cubeIdx`, `χ`, `𝒬`, `s_z`) read from a
`DecCover C` and the operator (`cutOperator`, `Ω₁`, `ℓ`) from a generating set `H`:
`Kz C H`, `Gstar C H`, `Kcal C H`, `Gs C H`.

`CoverBase C H a ν Kc Cx` collects the properties of the pair `(C, H)` that the proofs of
(DG1)--(DG4) use; it is the interface that the cut-operator estimates (NC), the partition of unity
and the overlap counts of the cover have to provide.  For `C = H` (`coverOf H`) all of them are
landed theorems (`coverBase_self`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-! ### Definitions -/

section Defs

variable (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)

/-- The multiplication by `χ_z`, on the domain `Ω₁` of the operator. -/
noncomputable def chiD (q : ℕ × CTorus d L N₁ m₁ K) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  Matrix.diagonal fun x => ((C.chi q x : ℝ) : ℂ)

/-- The commutator `K_z = χ_z H_D - H_D χ_z`. -/
noncomputable def Kz (a : ℕ → ℝ) (ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  chiD C H q * dirichletOperator H a ν 0 - dirichletOperator H a ν 0 * chiD C H q

/-- `G*_s(A) = ∑_z s_z χ_z G^{(z)}(A) c_z`. -/
noncomputable def Gstar (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  ∑ q ∈ C.cubeIdx, C.sProd s q • (chiD C H q * cubeG H a ν α q)

/-- `𝒦_s(A) = ∑_z s_z K_z G^{(z)}(A) c_z`. -/
noncomputable def Kcal (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  ∑ q ∈ C.cubeIdx, C.sProd s q • (Kz C H a ν q * cubeG H a ν α q)

/-- **The decoupled Green's operator** `G_s(A) = G*_s(A) (1 - 𝒦_s(A))⁻¹` of the cover `C` and the
operator `H`. -/
noncomputable def Gs (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  Gstar C H a ν α s * (1 - Kcal C H a ν α s)⁻¹

end Defs

section Algebra

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}


theorem Kz_eq (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Kz C H a ν q = chiD C H q * dirichletOperator H a ν α - dirichletOperator H a ν α * chiD C H q := by
  have hc : chiD C H q * Matrix.diagonal α = Matrix.diagonal α * chiD C H q := by
    unfold chiD
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; exact mul_comm _ _
  unfold Kz
  rw [dirichletOperator_eq_add a ν α, mul_add, add_mul, hc]
  abel

/-- **The parametrix identity, algebraic form.** If `χ_z H_D G_z = χ_z` for all centres and the
`χ_z` add up to the identity then `H_D G*_1 = 1 - 𝒦_1`. -/
theorem parametrix_algebra (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ)
    (hχG : ∀ q ∈ C.cubeIdx, chiD C H q * dirichletOperator H a ν α * cubeG H a ν α q = chiD C H q)
    (hsum : ∑ q ∈ C.cubeIdx, chiD C H q = 1) :
    dirichletOperator H a ν α * Gstar C H a ν α (fun _ => 1) = 1 - Kcal C H a ν α (fun _ => 1) := by
  have h1 : ∀ q ∈ C.cubeIdx, dirichletOperator H a ν α * (chiD C H q * cubeG H a ν α q) =
      chiD C H q - Kz C H a ν q * cubeG H a ν α q := by
    intro q hq
    have e : Kz C H a ν q * cubeG H a ν α q = chiD C H q * dirichletOperator H a ν α *
        cubeG H a ν α q - dirichletOperator H a ν α * (chiD C H q * cubeG H a ν α q) := by
      rw [Kz_eq a ν α q]; noncomm_ring
    rw [e, hχG q hq]; abel
  unfold Gstar Kcal
  simp only [DecCover.sProd, Finset.prod_const_one, one_smul]
  rw [Finset.mul_sum, Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hsum]

end Algebra

/-! ### The pair `(C, H)` -/

section Pair

variable (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
  (Kc Cx : ℝ)

/-- **The hypotheses on the operator `H` alone**: `d ≥ 3`, `L ≥ 3`, mass regime, admissible weights
and the separation `ϱ ≥ R₀` of the Green's function bounds (the operator part of `DGSetting`). -/
structure OpSetting (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ) : Prop where
  hd : 3 ≤ d
  hL : 3 ≤ L
  mass : 0 ≤ ν
  massLe : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1
  weights : IsAdmissibleWeights K a
  sep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)

open Classical in
/-- **The properties of the pair (cover `C`, operator `H`) that do not involve the cut-operator
estimate (NC3)**: the operator side `OpSetting H a ν`, and, on the pair side, `blockAligned`
(every cover cube `□_z` is a union of `H`-blocks, so its cut is a valid cut of `H`), `chi_unit`,
`sum_chi` (partition of unity on `Ω₁(H)`), `chi_smooth` (the `H`-scaled derivative bounds on
`χ_z`, with the constant `Cx`), `inner_near` (`supp χ_z` and the stencil: the interior of the
cube), `card_box` (at most `3 · 5^d` cubes meet a point), `card_qset` (`|𝒬(z)| ≤ N₀`). -/
structure CoverGeom : Prop extends OpSetting H a ν where
  blockAligned : ∀ q ∈ C.cubeIdx, BlockAligned H (intBox q)
  chi_unit : ∀ q ∈ C.cubeIdx, ∀ {x z : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 →
    (z = x ∨ ∃ μ : Fin d, z = x + Pi.single μ 1 ∨ z = x - Pi.single μ 1) →
    0 ≤ C.chi q z ∧ C.chi q z ≤ 1
  sum_chi : ∀ x ∈ H.Ω 1, ∑ q ∈ C.cubeIdx, C.chi q x = 1
  chi_smooth : ∀ q ∈ C.cubeIdx, IsSmoothField H (Cx / (L : ℝ) ^ m₁) (C.chiField q)
  inner_near : ∀ q ∈ C.cubeIdx, ∀ {x : CTorus d L N₁ m₁ K}, x ∈ H.Ω 1 → ∀ {y : CTorus d L N₁ m₁ K},
    C.chi q y ≠ 0 → ((∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) ∨
      SameCell (L ^ H.layerIndex x) x y) → Inner q x
  card_box : ∀ x ∈ H.Ω 1, (C.cubeIdx.filter fun q => x ∈ intBox q).card ≤ 3 * 5 ^ d
  card_qset : ∀ q ∈ C.cubeIdx, (C.Qset q).card ≤ N0 d L

/-- **The properties of the pair used by (DG1)--(DG4)**: `CoverGeom`, and `nc`, the block bounds
(NC3) of the cut operator `H_z(A)⁻¹` of every cover cube, with the constant `Kc`. -/
structure CoverBase : Prop extends CoverGeom C H a ν Cx where
  nc : ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ q ∈ C.cubeIdx, CubeBlockBounds H a ν α q Kc

end Pair

section Alg

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

theorem chiD_mulVec (q : ℕ × CTorus d L N₁ m₁ K) (f : H.Ω 1 → ℂ) (x : H.Ω 1) :
    (chiD C H q *ᵥ f) x = ((C.chi q x : ℝ) : ℂ) * f x := by
  unfold chiD
  rw [Matrix.mulVec_diagonal]


/-- The interior points contain the support of `χ_z`. -/
theorem inner_of_chi_ne_zero (S : CoverBase C H a ν Kc Cx) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (h : C.chi q x ≠ 0) :
    Inner q x := by
  exact S.inner_near q hq hx h (Or.inr (SameCell.refl _ _))

/-! ### The cube operator -/

theorem cubeH_isUnit (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) : IsUnit (cubeH H a ν α q) :=
  cutOperator_isUnit H (cubeCut_aligned H (S.blockAligned q hq))
    (by have := S.hd; omega) S.mass S.weights α hα

theorem cubeG_mulVec (q : ℕ × CTorus d L N₁ m₁ K) (f : H.Ω 1 → ℂ) :
    cubeG H a ν α q *ᵥ f = (cubeH H a ν α q)⁻¹ *ᵥ (cD H q *ᵥ f) := by
  unfold cubeG
  rw [Matrix.mulVec_mulVec]

/-- **`G^{(z)}(A) c_z f` is supported in the interaction cube.** -/
theorem cubeG_supp (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) (f : H.Ω 1 → ℂ) (z : H.Ω 1) (hz : (z : CTorus d L N₁ m₁ K) ∉ intBox q) :
    (cubeG H a ν α q *ᵥ f) z = 0 := by
  have hU := cubeH_isUnit S hα hq
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hH : cubeH H a ν α q *ᵥ (cubeG H a ν α q *ᵥ f) = cD H q *ᵥ f := by
    rw [cubeG_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  exact cutOperator_inv_supported H (S.blockAligned q hq) α hU
    (f := cD H q *ᵥ f) (fun w hw => by rw [cD_mulVec]; simp [hw]) hH z hz

theorem cubeH_cubeG (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) (f : H.Ω 1 → ℂ) :
    cubeH H a ν α q *ᵥ (cubeG H a ν α q *ᵥ f) = cD H q *ᵥ f := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (cubeH_isUnit S hα hq)
  rw [cubeG_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **`χ_z H_D G^{(z)} c_z = χ_z`.** -/
theorem chiD_dirichlet_cubeG (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ C.cubeIdx) :
    chiD C H q * dirichletOperator H a ν α * cubeG H a ν α q = chiD C H q := by
  refine matrix_ext_mulVec fun f => ?_
  funext x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, chiD_mulVec, chiD_mulVec]
  by_cases h0 : C.chi q x = 0
  · simp [h0]
  · have hin := inner_of_chi_ne_zero S hq x.2 h0
    have hrow := dirichlet_row_eq_cut_row a ν α (cut := cubeCut H (intBox q)) hin.noCut
      (cubeG H a ν α q *ᵥ f)
    have h1 := cubeH_cubeG S hα hq f
    have h2 := congrFun h1 x
    simp only [cD_mulVec, hin.self, ite_true] at h2
    change ((C.chi q x : ℝ) : ℂ) * (dirichletOperator H a ν α *ᵥ (cubeG H a ν α q *ᵥ f)) x = _
    rw [hrow]
    unfold cubeH at h2
    rw [h2]

theorem sum_chiD (S : CoverBase C H a ν Kc Cx) : ∑ q ∈ C.cubeIdx, chiD C H q = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  unfold chiD
  simp only [Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true, Matrix.one_apply_eq]
    rw [← Complex.ofReal_sum, S.sum_chi x x.2, Complex.ofReal_one]
  · simp [hxy]

/-- **The parametrix identity** `H_D(A) G*_1(A) = 1 - 𝒦_1(A)` (LOCALIZATION.md §1.3). -/
theorem parametrix (S : CoverBase C H a ν Kc Cx) (hα : AdmPot H α) :
    dirichletOperator H a ν α * Gstar C H a ν α (fun _ => 1) = 1 - Kcal C H a ν α (fun _ => 1) :=
  parametrix_algebra a ν α (fun _ hq => chiD_dirichlet_cubeG S hα hq)
    (sum_chiD S)

end Alg

end Balaban.Localization.Dec2
