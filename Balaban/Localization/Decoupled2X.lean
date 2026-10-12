/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Local
public import Balaban.Localization.DecoupledX

/-!
# The x-variant decoupled Green's operator for a cover `C` and an operator `H` (DG7)

`Kzx C H`, `Gstarx C H`, `Kcalx C H`, `Gsx C H` are the commutators and the parametrix operators
of the x-variant `H_{k,x}` of GREEN.md (1.7) with the cover read from `C`; the cube operators
`cubeHx H`, `cubeGx H` only involve `H`.  `XCover C H a aT ν Cx` is `CoverGeom` for the generating
set of level `k + 1` together with `1 ≤ k` and `a_{k+1} = aT ∈ [1/2, 2]`; no estimate (NC) for the
cut operators is assumed: the weighted `L²` bounds of the x-variant are the energy inequalities
`x_agmon_energy_cut`, which only need that the cube is a union of blocks of `H`
(`CoverGeom.blockAligned`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Defs

variable (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- The commutator `K^x_z = χ_z H_{k,x} - H_{k,x} χ_z` (independent of the potential). -/
noncomputable def Kzx (a : ℕ → ℝ) (aT x ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  chiD C H q * xDirichletOperator H a aT x ν 0 - xDirichletOperator H a aT x ν 0 * chiD C H q

/-- `G*_{x,s}(A) = ∑_z s_z χ_z G^{(z)}_x(A) c_z`. -/
noncomputable def Gstarx (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  ∑ q ∈ C.cubeIdx, C.sProd s q • (chiD C H q * cubeGx H a aT x ν α q)

/-- `𝒦_{x,s}(A) = ∑_z s_z K^x_z G^{(z)}_x(A) c_z`. -/
noncomputable def Kcalx (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  ∑ q ∈ C.cubeIdx, C.sProd s q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α q)

/-- **The x-variant decoupled Green's operator** `G_{k,x,s}(A) = G*_{x,s}(A) (1 - 𝒦_{x,s}(A))⁻¹`. -/
noncomputable def Gsx (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  Gstarx C H a aT x ν α s * (1 - Kcalx C H a aT x ν α s)⁻¹

end Defs

section Setting

variable (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (a : ℕ → ℝ) (aT ν Cx : ℝ)

/-- **The standing hypotheses of DG7 for the pair `(C, H)`**: `CoverGeom` for the generating set
of level `k + 1`, `k ≥ 1` and the coefficient `a_{k+1} = aT ∈ [1/2, 2]` of the top layer. -/
structure XCover : Prop extends CoverGeom C H a ν Cx where
  hk : 1 ≤ k
  haT1 : 1 / 2 ≤ aT
  haT2 : aT ≤ 2

end Setting

variable {C : DecCover d L N₁ m₁ (k + 1)} {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT x ν Cx : ℝ} {α : H.Ω 1 → ℂ}

theorem XCover.ha (S : XCover C H a aT ν Cx) : IsAdmissibleWeights k a :=
  fun j h1 h2 => S.weights j h1 (by omega)

theorem AdmPot.le_eighth' (hd : 3 ≤ d) (hα : AdmPot H α) (y : H.Ω 1) :
    ‖α y‖ ≤ (1 / 8) / (H.spacing y) ^ 2 := by
  refine (hα y).trans ?_
  have hd : 0 < d := by omega
  have hp := poincareConst_le_half d
  have hs : 0 < (H.spacing (y : CTorus d L N₁ m₁ (k + 1))) ^ 2 := by
    have := spacing_pos H (x := (y : CTorus d L N₁ m₁ (k + 1))); positivity
  have : coerciveConst d ≤ 1 / 4 := by unfold coerciveConst; linarith
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith

theorem cubeHx_isUnit (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) :
    IsUnit (cubeHx H a aT x ν α q) :=
  cutXOperator_isUnit H (cubeCut_aligned H (S.blockAligned q hq)) S.hL S.hk S.mass S.ha S.haT1
    S.haT2 hx α (AdmPot.le_eighth' S.hd hα)


theorem cubeHx_cubeGx (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (f : H.Ω 1 → ℂ) :
    cubeHx H a aT x ν α q *ᵥ (cubeGx H a aT x ν α q *ᵥ f) = cD H q *ᵥ f := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 (cubeHx_isUnit S hα hx hq)
  rw [cubeGx_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- **`H^{(z)}_x(A) c_z f` is supported in the interaction cube.** -/
theorem cubeGx_supp (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (f : H.Ω 1 → ℂ) (z : H.Ω 1)
    (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q) :
    (cubeGx H a aT x ν α q *ᵥ f) z = 0 :=
  cutXOperator_inv_supported (S.blockAligned q hq) (cubeHx_isUnit S hα hx hq)
    (f := cD H q *ᵥ f) (fun w hw => by rw [cD_mulVec]; simp [hw])
    (cubeHx_cubeGx S hα hx hq f) z hz

/-- **`χ_z H_{k,x} G^{(z)}_x c_z = χ_z`.** -/
theorem chiD_xDirichlet_cubeGx (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) :
    chiD C H q * xDirichletOperator H a aT x ν α * cubeGx H a aT x ν α q = chiD C H q := by
  refine matrix_ext_mulVec fun f => ?_
  funext y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, chiD_mulVec, chiD_mulVec]
  by_cases h0 : C.chi q y = 0
  · simp [h0]
  · have hin := S.inner_near q hq y.2 h0 (Or.inr (SameCell.refl _ _))
    have hrow := xDirichlet_row_eq_cutX_row (G := H) (a := a) (aT := aT) (x := x) (ν := ν)
      (α := α) (cut := cubeCut H (intBox q)) (y := y) hin.noCut (cubeGx H a aT x ν α q *ᵥ f)
    have h1 := cubeHx_cubeGx S hα hx hq f
    have h2 := congrFun h1 y
    simp only [cD_mulVec, hin.self, ite_true] at h2
    change ((C.chi q y : ℝ) : ℂ) *
      (xDirichletOperator H a aT x ν α *ᵥ (cubeGx H a aT x ν α q *ᵥ f)) y = _
    rw [hrow]
    unfold cubeHx at h2
    rw [h2]


theorem Kzx_eq (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Kzx C H a aT x ν q = chiD C H q * xDirichletOperator H a aT x ν α -
      xDirichletOperator H a aT x ν α * chiD C H q := by
  have hdec : xDirichletOperator H a aT x ν α = xDirichletOperator H a aT x ν 0 +
      Matrix.diagonal α := by
    unfold xDirichletOperator
    simp
  have hc : chiD C H q * Matrix.diagonal α = Matrix.diagonal α * chiD C H q := by
    unfold chiD
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext z; exact mul_comm _ _
  unfold Kzx
  rw [hdec, mul_add, add_mul, hc]
  abel

theorem Kzx_apply (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1))
    (y y' : H.Ω 1) :
    Kzx C H a aT x ν q y y' = xDirichletOperator H a aT x ν α y y' *
      (((C.chi q y : ℝ) : ℂ) - ((C.chi q y' : ℝ) : ℂ)) := by
  rw [Kzx_eq a aT x ν α q]
  unfold chiD
  rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

theorem Kzx_mulVec_eq_commK (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (u : H.Ω 1 → ℂ) (y : H.Ω 1) :
    (Kzx C H a aT x ν q *ᵥ u) y =
      (commK (xDirichletOperator H a aT x ν α) (restrictField H (C.chiField q)) *ᵥ
        (fun p : H.Ω 1 × Fin 1 => u p.1)) y := by
  rw [commK_mulVec]
  simp only [Matrix.mulVec, dotProduct, Kzx_apply a aT x ν α q, Finset.univ_unique,
    Finset.sum_singleton]
  refine Finset.sum_congr rfl fun y' _ => ?_
  simp [restrictField, DecCover.chiField]


/-- **Support of the commutator.** If `K^x_z u (y) ≠ 0` then `y` is an interior point of `□_z`. -/
theorem inner_of_Kzx_ne_zero (S : XCover C H a aT ν Cx) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ C.cubeIdx) (u : H.Ω 1 → ℂ) (y : H.Ω 1)
    (h : (Kzx C H a aT x ν q *ᵥ u) y ≠ 0) : Inner q y := by
  by_contra hI
  obtain ⟨-, hnK, -⟩ := H.layerIndex_spec y.2
  set n := H.layerIndex (y : CTorus d L N₁ m₁ (k + 1)) with hn
  have hz : ∀ z : CTorus d L N₁ m₁ (k + 1),
      ((∃ μ : Fin d, z = (y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1 ∨
        z = (y : CTorus d L N₁ m₁ (k + 1)) - Pi.single μ 1) ∨
        SameCell (L ^ n) (y : CTorus d L N₁ m₁ (k + 1)) z) → C.chi q z = 0 := by
    intro z hnear
    by_contra hne
    exact hI (S.inner_near q hq y.2 hne hnear)
  have hx0 : C.chi q (y : CTorus d L N₁ m₁ (k + 1)) = 0 := hz _ (Or.inr (SameCell.refl _ _))
  have e : ∀ z : CTorus d L N₁ m₁ (k + 1), C.chi q z = 0 → C.chiField q z = fun _ => 0 := by
    intro z hz0; funext i; unfold DecCover.chiField; rw [hz0]; simp
  apply h
  rw [Kzx_mulVec_eq_commK a aT x ν (0 : H.Ω 1 → ℂ) q u y]
  refine commKx_apply_eq_zero a aT x ν 0 _ y (fun μ => ?_) (fun z hz' => ?_)
  · have h1 := hz _ (Or.inl ⟨μ, Or.inl rfl⟩)
    have h2 := hz _ (Or.inl ⟨μ, Or.inr rfl⟩)
    rw [e _ h1, e _ h2, e _ hx0]; exact ⟨rfl, rfl⟩
  · have hy' := GeneratingSet.mem_blk.1 hz'
    have h1 := hz z (Or.inr (sameCell_of_jBlock_eq hnK hy'.symm))
    rw [e _ h1, e _ hx0]

/-! ### The parametrix identity -/

theorem parametrix_algebra_x (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ)
    (hχG : ∀ q ∈ C.cubeIdx, chiD C H q * xDirichletOperator H a aT x ν α *
      cubeGx H a aT x ν α q = chiD C H q) (hsum : ∑ q ∈ C.cubeIdx, chiD C H q = 1) :
    xDirichletOperator H a aT x ν α * Gstarx C H a aT x ν α (fun _ => 1) =
      1 - Kcalx C H a aT x ν α (fun _ => 1) := by
  have h1 : ∀ q ∈ C.cubeIdx, xDirichletOperator H a aT x ν α *
      (chiD C H q * cubeGx H a aT x ν α q) =
      chiD C H q - Kzx C H a aT x ν q * cubeGx H a aT x ν α q := by
    intro q hq
    have e : Kzx C H a aT x ν q * cubeGx H a aT x ν α q = chiD C H q *
        xDirichletOperator H a aT x ν α * cubeGx H a aT x ν α q -
        xDirichletOperator H a aT x ν α * (chiD C H q * cubeGx H a aT x ν α q) := by
      rw [Kzx_eq a aT x ν α q]; noncomm_ring
    rw [e, hχG q hq]; abel
  unfold Gstarx Kcalx
  simp only [DecCover.sProd, Finset.prod_const_one, one_smul]
  rw [Finset.mul_sum, Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hsum]

/-- **The parametrix identity** `H_{k,x}(A) G*_{x,1}(A) = 1 - 𝒦_{x,1}(A)`. -/
theorem parametrix_x (S : XCover C H a aT ν Cx) (hα : AdmPot H α) (hx : 0 ≤ x) :
    xDirichletOperator H a aT x ν α * Gstarx C H a aT x ν α (fun _ => 1) =
      1 - Kcalx C H a aT x ν α (fun _ => 1) :=
  parametrix_algebra_x a aT x ν α (fun _ hq => chiD_xDirichlet_cubeGx S hα hx hq)
    (sum_chiD S.toCoverGeom)

end Balaban.Localization.Dec2
