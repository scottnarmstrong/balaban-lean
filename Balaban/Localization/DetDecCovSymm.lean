/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DetUnitIncidenceSymm
public import Balaban.Localization.XCutOperator
public import Balaban.Localization.DecoupledCovBound
public import Balaban.Localization.DecoupledSqrt
public import Balaban.Localization.Decoupled2Self

/-!
# Covariance of the x-shifted decoupled Green's operator and of `decM`, `decN`, `decPi`, `decCov`,
`decLog` under a lattice symmetry

Let `S : LatSymm G G σ` with `hU : UnitBlockPres σ`, `CS : CoverSymm (coverOf G) σ`, and let `u`
be the permutation `unitAct G S hU` of the unit points.  Write `rm e M = M.submatrix e.symm e.symm`
(`DecEquiv.rm`), so `(rm e M) (e p) (e q) = M p q`.  All identities below are between the objects
at the transported data (`S.mul α`, `CS.par s`, `symSite σ φ`) and the original objects:

* the x-variant averaging form and the cut operators `cutXOperator`, `xDirichletOperator`
  (`rm S.Ω1Equiv`);
* `Gsx` (`Gsx_rm`);
* `decM` (`rm S.Ω1Equiv`), `decN` and the field multiplication (rectangular `submatrix`), `decPi`
  (`rm` for `S.Ω1Equiv` lifted by the identity of `Fin N`);
* `decCov` and `decLog` on the unit points, with `unitQ`, `unitP` (`rm` for `u` lifted by the
  identity of `Fin N`).

Inverses are the nonsingular inverse `Matrix.inv`, so no invertibility is assumed; transposes are
plain transposes (the real matrices `unitQ` are not conjugated).

Covariance of the CLASS terms (after the collar regrouping, on the class domain) is NOT proved
here.  The statements are not chart-sensitive and independent of the choice of generator.
-/

@[expose] public section

namespace Balaban.Localization.DetDecCov

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Finset Matrix

/-! ### The x-variant averaging form -/

section XAvg

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ K ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ K))}

theorem layerBlock_sym (j m : ℕ) (hl : ∀ x, σ x ∈ G.layer j ↔ x ∈ G.layer j)
    (hb : ∀ x y, x ∈ G.layer j → y ∈ G.layer j →
      (blockMap (L ^ m) (N₀ * L ^ (K - m)) (σ x) = blockMap (L ^ m) (N₀ * L ^ (K - m)) (σ y) ↔
        blockMap (L ^ m) (N₀ * L ^ (K - m)) x = blockMap (L ^ m) (N₀ * L ^ (K - m)) y))
    (x y : Torus d (N₀ * L ^ K)) :
    layerBlockMatrix G j m (σ x) (σ y) = layerBlockMatrix G j m x y := by
  by_cases hxy : x ∈ G.layer j ∧ y ∈ G.layer j
  · have := hb x y hxy.1 hxy.2
    simp only [layerBlockMatrix, blockProjMatrix, hl, hxy, and_self, ite_true, this]
  · simp [layerBlockMatrix, hl, hxy]

end XAvg

section XSym

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ) (hU : UnitBlockPres σ)

include S hU in
theorem xAvg_sym (a : ℕ → ℝ) (s₁ s₂ : ℝ) (x y : CTorus d L N₁ m₁ (k + 1)) :
    xAvgMatrix G a s₁ s₂ (σ x) (σ y) = xAvgMatrix G a s₁ s₂ x y := by
  have hLow : ∀ j, 1 ≤ j → j ≤ k → ∀ x y,
      layerBlockMatrix G j j (σ x) (σ y) = layerBlockMatrix G j j x y := fun j h1 hj x y =>
    layerBlock_sym j j (S.mem_layer h1 (by omega)) (fun x y hx _ =>
      S.block j h1 (by omega) ⟨x, hx⟩ x y) x y
  have hK : ∀ x y, layerBlockMatrix G (k + 1) k (σ x) (σ y) = layerBlockMatrix G (k + 1) k x y :=
    fun x y => layerBlock_sym (k + 1) k (S.mem_layer (by omega) le_rfl) (fun x y _ _ => hU x y) x y
  have hT : ∀ x y, layerBlockMatrix G (k + 1) (k + 1) (σ x) (σ y) =
      layerBlockMatrix G (k + 1) (k + 1) x y := fun x y =>
    layerBlock_sym (k + 1) (k + 1) (S.mem_layer (by omega) le_rfl) (fun x y hx _ =>
      S.block (k + 1) (by omega) le_rfl ⟨x, hx⟩ x y) x y
  simp only [xAvgMatrix, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hK, hT]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨h1, hk⟩ := Finset.mem_Icc.1 hj
  rw [hLow j h1 hk]

include S hU in
theorem cutXOperator_rm (a : ℕ → ℝ) (aT x ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    cutXOperator G a aT x ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α) =
      rm S.Ω1Equiv (cutXOperator G a aT x ν cut α) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply]
  simp only [cutXOperator, Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.map_apply, LatSymm.coe_Ω1Equiv, cutXFullMatrix,
    Matrix.add_apply, cutLaplacian_sym S, xAvg_sym S hU, LatSymm.mul_apply,
    Equiv.apply_eq_iff_eq]

include S hU in
theorem xDirichletOperator_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) :
    xDirichletOperator G a aT x ν (S.mul α) = rm S.Ω1Equiv (xDirichletOperator G a aT x ν α) := by
  have := cutXOperator_rm S hU a aT x ν ∅ α
  simpa using this

end XSym

/-! ### `Gsx` -/

section GsxSym

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ) (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf G) σ)

theorem rm_chiD' (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    rm S.Ω1Equiv (chiD G q) = chiD G (CS.τ q) := rm_chiD S CS q

include S hU CS in
theorem cubeHx_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    cubeHx G a aT x ν (S.mul α) (CS.τ q) = rm S.Ω1Equiv (cubeHx G a aT x ν α q) := by
  unfold cubeHx
  rw [CS.intBox_eq, cubeCut_siteImage S, cutXOperator_rm S hU]

include S hU CS in
theorem cubeGx_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    cubeGx G a aT x ν (S.mul α) (CS.τ q) = rm S.Ω1Equiv (cubeGx G a aT x ν α q) := by
  unfold cubeGx
  rw [rm_mul, rm_inv, ← cubeHx_rm S hU CS, rm_cD S CS]

include S hU CS in
theorem Kzx_rm (a : ℕ → ℝ) (aT x ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Kzx G a aT x ν (CS.τ q) = rm S.Ω1Equiv (Kzx G a aT x ν q) := by
  have h0 : S.mul (0 : G.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  unfold Kzx
  rw [rm_sub, rm_mul, rm_mul, rm_chiD' S CS, ← xDirichletOperator_rm S hU, h0]

include S hU CS in
theorem Gstarx_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G)) :
    Gstarx G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) =
      rm S.Ω1Equiv (Gstarx G a aT x ν α (Dec2.extS (coverOf G) s)) := by
  unfold Gstarx
  rw [rm_sum]
  refine (Finset.sum_equiv CS.τ (fun q => (CS.idx q).symm) fun q _ => ?_).symm
  have hs : sProd G (Dec2.extS (coverOf G) (CS.par s)) (CS.τ q) =
      sProd G (Dec2.extS (coverOf G) s) q := CS.sProd_par s q
  rw [hs, rm_smul, rm_mul, rm_chiD' S CS, cubeGx_rm S hU CS]

include S hU CS in
theorem Kcalx_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G)) :
    Kcalx G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) =
      rm S.Ω1Equiv (Kcalx G a aT x ν α (Dec2.extS (coverOf G) s)) := by
  unfold Kcalx
  rw [rm_sum]
  refine (Finset.sum_equiv CS.τ (fun q => (CS.idx q).symm) fun q _ => ?_).symm
  have hs : sProd G (Dec2.extS (coverOf G) (CS.par s)) (CS.τ q) =
      sProd G (Dec2.extS (coverOf G) s) q := CS.sProd_par s q
  rw [hs, rm_smul, rm_mul, Kzx_rm S hU CS, cubeGx_rm S hU CS]

include S hU CS in
/-- **T1. Covariance of `Gsx`**: `G_{k,x,s∘τ⁻¹}(σα) = rm σ (G_{k,x,s}(α))`, i.e.
`Gsx' (σ y) (σ y') = Gsx y y'`. -/
theorem Gsx_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G)) :
    Gsx G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) =
      rm S.Ω1Equiv (Gsx G a aT x ν α (Dec2.extS (coverOf G) s)) := by
  unfold Gsx
  rw [rm_mul, rm_inv, rm_sub, rm_one, Gstarx_rm S hU CS, Kcalx_rm S hU CS]

end GsxSym

/-! ### Lifts to `N`-vector fields and transport of rectangular matrices -/

section Lift

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ}

theorem submatrix_sub' {m n o p : Type*} (A B : Matrix m n ℂ) (f : o → m) (g : p → n) :
    (A - B).submatrix f g = A.submatrix f g - B.submatrix f g := by
  ext; simp

theorem liftOp_rm (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    liftOp N (rm e A) = rm (e.prodCongr (Equiv.refl (Fin N))) (liftOp N A) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [liftOp, rm]

theorem liftRect_submatrix {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : κ' ≃ κ) (f : ι ≃ ι)
    (Q : Matrix κ ι ℂ) :
    liftRect N (Q.submatrix e f) =
      (liftRect N Q).submatrix (e.prodCongr (Equiv.refl (Fin N))) (f.prodCongr (Equiv.refl (Fin N))) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [liftRect]

theorem covA_rm (e : ι ≃ κ) (c b x : ℝ) (P : Matrix ι ι ℂ) :
    covA c b x (rm e P) = rm e (covA c b x P) := by
  unfold covA
  rw [rm_add, rm_smul, rm_smul, rm_sub, rm_one]

theorem intMat_rm (e : ι ≃ κ) (μ : MeasureTheory.Measure ℝ) (F : ℝ → Matrix ι ι ℂ) :
    intMat μ (fun x => rm e (F x)) = rm e (intMat μ F) := rfl

/-- The algebra of the conjugation in `decCov`. -/
theorem conj_alg {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (u : U ≃ U) (w : W ≃ W) (A : Matrix U U ℂ) (X : Matrix U W ℂ) (Gl Pi : Matrix W W ℂ)
    (hA : rm u A = A) (hX : X.submatrix u.symm w.symm = X) :
    A * X * (rm w Gl - rm w Pi) * Xᵀ * A = rm u (A * X * (Gl - Pi) * Xᵀ * A) := by
  conv_lhs => rw [← hA, ← hX]
  rw [← rm_sub]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

end Lift

/-! ### `decM`, `decN`, `decPi` -/

section DecSym

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ)

theorem fieldMul_restrict_symSite (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    fieldMul (restrictField G (symSite σ φ)) =
      (fieldMul (restrictField G φ)).submatrix (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm
        S.Ω1Equiv.symm := by
  ext ⟨x', i⟩ y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  simp [fieldMul, restrictField, symSite]

theorem commK_rm (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    commK (rm S.Ω1Equiv H) (restrictField G (symSite σ φ)) =
      (commK H (restrictField G φ)).submatrix S.Ω1Equiv.symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm := by
  unfold commK
  rw [fieldMul_restrict_symSite S, liftOp_rm, Matrix.transpose_submatrix, rm, rm,
    submatrix_sub']
  simp only [Matrix.submatrix_mul_equiv]

theorem constraintM_rm (H Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    constraintM (rm S.Ω1Equiv H) (rm S.Ω1Equiv Gm) (restrictField G (symSite σ φ)) =
      rm S.Ω1Equiv (constraintM H Gm (restrictField G φ)) := by
  unfold constraintM
  rw [fieldMul_restrict_symSite S, commK_rm S, liftOp_rm, rm_sub]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

theorem constraintN_rm (H Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    constraintN (rm S.Ω1Equiv H) (rm S.Ω1Equiv Gm) (restrictField G (symSite σ φ)) =
      (constraintN H Gm (restrictField G φ)).submatrix S.Ω1Equiv.symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm := by
  unfold constraintN
  rw [fieldMul_restrict_symSite S, commK_rm S, liftOp_rm]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, submatrix_sub']

variable (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf G) σ)

include S hU CS in
/-- **T2. Covariance of `M_{x,s}`**: `M' = rm σ M`. -/
theorem decM_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decM G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) (symSite σ φ) =
      rm S.Ω1Equiv (decM G a aT x ν α (Dec2.extS (coverOf G) s) φ) := by
  unfold decM
  rw [xDirichletOperator_rm S hU, Gsx_rm S hU CS, constraintM_rm S]

include S hU CS in
/-- **T2. Covariance of `N_{x,s}`**: `N' = N` with rows relabelled by `σ` on `Ω₁` and columns
by `σ × 1` on `Ω₁ × Fin N`. -/
theorem decN_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decN G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) (symSite σ φ) =
      (decN G a aT x ν α (Dec2.extS (coverOf G) s) φ).submatrix S.Ω1Equiv.symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm := by
  unfold decN
  rw [xDirichletOperator_rm S hU, Gsx_rm S hU CS, constraintN_rm S]

include S hU CS in
/-- **T2. Covariance of `Π_{x,s}`**: `Π' = rm (σ × 1) Π`. -/
theorem decPi_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decPi G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) (symSite σ φ) =
      rm (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N)))
        (decPi G a aT x ν α (Dec2.extS (coverOf G) s) φ) := by
  unfold decPi
  rw [decM_rm S hU CS, decN_rm S hU CS, Gsx_rm S hU CS, liftOp_rm, fieldMul_restrict_symSite S,
    ← rm_inv]
  simp only [rm, Matrix.submatrix_mul_equiv]

end DecSym

/-! ### `decCov` and `decLog` on the unit points -/

section CovSym

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ) (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf G) σ)

include S hU in
theorem liftRect_unitQ_invariant :
    (liftRect N (unitQ G)).submatrix ((unitAct G S hU).prodCongr (Equiv.refl (Fin N))).symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm = liftRect N (unitQ G) := by
  have h := liftRect_submatrix (N := N) (unitAct G S hU).symm S.Ω1Equiv.symm (unitQ G)
  rw [unitQ_submatrix_symm G S hU] at h
  simpa using h.symm

include S hU in
theorem liftOp_unitP_invariant :
    rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N))) (liftOp N (unitP G)) =
      liftOp N (unitP G) := by
  have h := liftOp_rm (N := N) (unitAct G S hU) (unitP G)
  have e : rm (unitAct G S hU) (unitP G) = unitP G := unitP_submatrix_symm G S hU
  rw [e] at h
  exact h.symm

include S hU CS in
/-- **T2. Covariance of `C_x(s)`** on the unit points (with the same `unitQ G`, `unitP G` on both
sides): `C_x' = rm (u × 1) C_x`, where `u = unitAct G S hU`. -/
theorem decCov_rm (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decCov G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) (symSite σ φ)
        (unitQ G) (unitP G) =
      rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (decCov G a aT x ν α (Dec2.extS (coverOf G) s) φ (unitQ G) (unitP G)) := by
  unfold decCov
  rw [Gsx_rm S hU CS, decPi_rm S hU CS, liftOp_rm, rm_add, rm_smul]
  have hA : rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) =
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)) := by
    rw [← covA_rm, liftOp_unitP_invariant S hU]
  have key := conj_alg ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
    (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N)))
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) (liftRect N (unitQ G))
    (liftOp N (Gsx G a aT x ν α (Dec2.extS (coverOf G) s)))
    (decPi G a aT x ν α (Dec2.extS (coverOf G) s) φ) hA (liftRect_unitQ_invariant S hU)
  rw [hA, ← key]

include S hU in
theorem covA_unitP_invariant (c b x : ℝ) :
    rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
      (covA c b x (liftOp N (unitP G))) = covA c b x (liftOp N (unitP G)) := by
  rw [← covA_rm, liftOp_unitP_invariant S hU]

include S hU CS in
/-- **T3. Covariance of the logarithm `𝕃(s)`** (`decLog`) on the unit points:
`𝕃' = rm (u × 1) 𝕃`; the integral over `x` is entrywise, so it commutes with the relabelling. -/
theorem decLog_rm (a : ℕ → ℝ) (aT ν : ℝ) (α : G.Ω 1 → ℂ) (s : Dec2.DecParams (coverOf G))
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decLog G a aT ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s)) (symSite σ φ)
        (unitQ G) (unitP G) =
      rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (decLog G a aT ν α (Dec2.extS (coverOf G) s) φ (unitQ G) (unitP G)) := by
  have hdiff : (fun x => decCov G a aT x ν (S.mul α) (Dec2.extS (coverOf G) (CS.par s))
        (symSite σ φ) (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) =
      fun x => rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (decCov G a aT x ν α (Dec2.extS (coverOf G) s) φ (unitQ G) (unitP G) -
          covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) := by
    funext x
    rw [decCov_rm S hU CS, rm_sub, covA_unitP_invariant S hU]
  unfold decLog
  rw [hdiff, intMat_rm, rm_sub, rm_add, rm_smul, rm_smul, rm_sub, rm_one,
    liftOp_unitP_invariant S hU]

end CovSym

end Balaban.Localization.DetDecCov
