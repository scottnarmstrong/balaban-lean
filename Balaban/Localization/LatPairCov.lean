/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LatPairBg
public import Balaban.Localization.DetDecCovSymm

/-!
# Lattice symmetries between two generating sets: the decoupled covariance and its square root

The two-set form of `DetDecCovSymm.lean`.  For a lattice symmetry `S : LatSymm G G' σ` between two
generating sets of level `k + 1`, preserving the unit blocks (`UnitBlockPres σ`), a permutation `τ`
of the centres between the covers `coverOf G`, `coverOf G'` (`hidx`, `hchi`, `hbox`, `hqset`), and a
bijection `u` of the unit points of `G` onto those of `G'` matching the unit blocks (`hu`):

* `Gsx_rm_pair`: the x-variant decoupled Green's operator;
* `decM_rm_pair`, `decN_rm_pair`, `decPi_rm_pair`;
* `unitQ_pair`, `unitP_pair`: the unit-lattice matrices;
* `decCov_rm_pair`: `C'_x(s') = rm (u × 1) C_x(s)`;
* `decCovSqrt_rm_pair`: the same for the square root `C^{1/2}(s)`;
* `exists_unitAct_pair`: the bijection `u` exists.
The parameters are related by `s' ∘ τ = s`.
-/

@[expose] public section

namespace Balaban.Localization.DetDecCov

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.DecEquiv Balaban.Localization.DetUnitIncidence Finset Matrix

section XAvgPair

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G G' : GeneratingSet d L N₀ K ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ K))}

theorem layerBlock_sym_pair (j m : ℕ) (hl : ∀ x, σ x ∈ G'.layer j ↔ x ∈ G.layer j)
    (hb : ∀ x y, x ∈ G.layer j → y ∈ G.layer j →
      (blockMap (L ^ m) (N₀ * L ^ (K - m)) (σ x) = blockMap (L ^ m) (N₀ * L ^ (K - m)) (σ y) ↔
        blockMap (L ^ m) (N₀ * L ^ (K - m)) x = blockMap (L ^ m) (N₀ * L ^ (K - m)) y))
    (x y : Torus d (N₀ * L ^ K)) :
    layerBlockMatrix G' j m (σ x) (σ y) = layerBlockMatrix G j m x y := by
  by_cases hxy : x ∈ G.layer j ∧ y ∈ G.layer j
  · have := hb x y hxy.1 hxy.2
    simp only [layerBlockMatrix, blockProjMatrix, hl, hxy, and_self, ite_true, this]
  · simp [layerBlockMatrix, hl, hxy]

end XAvgPair

section XSymPair

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G' σ) (hU : UnitBlockPres σ)

include S hU in
theorem xAvg_sym_pair (a : ℕ → ℝ) (s₁ s₂ : ℝ) (x y : CTorus d L N₁ m₁ (k + 1)) :
    xAvgMatrix G' a s₁ s₂ (σ x) (σ y) = xAvgMatrix G a s₁ s₂ x y := by
  have hLow : ∀ j, 1 ≤ j → j ≤ k → ∀ x y,
      layerBlockMatrix G' j j (σ x) (σ y) = layerBlockMatrix G j j x y := fun j h1 hj x y =>
    layerBlock_sym_pair j j (S.mem_layer h1 (by omega)) (fun x y hx _ =>
      S.block j h1 (by omega) ⟨x, hx⟩ x y) x y
  have hK : ∀ x y, layerBlockMatrix G' (k + 1) k (σ x) (σ y) = layerBlockMatrix G (k + 1) k x y :=
    fun x y => layerBlock_sym_pair (k + 1) k (S.mem_layer (by omega) le_rfl)
      (fun x y _ _ => hU x y) x y
  have hT : ∀ x y, layerBlockMatrix G' (k + 1) (k + 1) (σ x) (σ y) =
      layerBlockMatrix G (k + 1) (k + 1) x y := fun x y =>
    layerBlock_sym_pair (k + 1) (k + 1) (S.mem_layer (by omega) le_rfl) (fun x y hx _ =>
      S.block (k + 1) (by omega) le_rfl ⟨x, hx⟩ x y) x y
  simp only [xAvgMatrix, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hK, hT]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨h1, hk⟩ := Finset.mem_Icc.1 hj
  rw [hLow j h1 hk]

include S hU in
theorem cutXOperator_rm_pair (a : ℕ → ℝ) (aT x ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    cutXOperator G' a aT x ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α) =
      rm S.Ω1Equiv (cutXOperator G a aT x ν cut α) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply]
  simp only [cutXOperator, Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.map_apply, LatSymm.coe_Ω1Equiv, cutXFullMatrix,
    Matrix.add_apply, cutLaplacian_sym_pair S, xAvg_sym_pair S hU, LatSymm.mul_apply,
    Equiv.apply_eq_iff_eq]

include S hU in
theorem xDirichletOperator_rm_pair (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) :
    xDirichletOperator G' a aT x ν (S.mul α) = rm S.Ω1Equiv (xDirichletOperator G a aT x ν α) := by
  have := cutXOperator_rm_pair S hU a aT x ν ∅ α
  simpa using this

end XSymPair

section GsxPair

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G' σ) (hU : UnitBlockPres σ)
  {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}

theorem rm_chiD_pair' (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    rm S.Ω1Equiv (chiD G q) = chiD G' (τ q) := by
  unfold chiD
  rw [rm_diagonal]
  congr 1
  funext z
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective z
  simp [hchi]

include S hU in
theorem cubeHx_rm_pair (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q) (a : ℕ → ℝ)
    (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    cubeHx G' a aT x ν (S.mul α) (τ q) = rm S.Ω1Equiv (cubeHx G a aT x ν α q) := by
  unfold cubeHx
  rw [intBox_eq_pair hbox, cubeCut_siteImage_pair S, cutXOperator_rm_pair S hU]

include S hU in
theorem cubeGx_rm_pair (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q) (a : ℕ → ℝ)
    (aT x ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    cubeGx G' a aT x ν (S.mul α) (τ q) = rm S.Ω1Equiv (cubeGx G a aT x ν α q) := by
  unfold cubeGx
  rw [rm_mul, rm_inv, ← cubeHx_rm_pair S hU hbox, rm_cD_pair S hbox]

include S hU in
theorem Kzx_rm_pair (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x) (a : ℕ → ℝ)
    (aT x ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Kzx G' a aT x ν (τ q) = rm S.Ω1Equiv (Kzx G a aT x ν q) := by
  have h0 : S.mul (0 : G.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  unfold Kzx
  rw [rm_sub, rm_mul, rm_mul, rm_chiD_pair' S hchi, ← xDirichletOperator_rm_pair S hU, h0]

theorem sProd_pair' (hqset : ∀ q q', τ q' ∈ Qset G' (τ q) ↔ q' ∈ Qset G q)
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) : sProd G' s' (τ q) = sProd G s q := by
  unfold sProd
  refine (Finset.prod_equiv τ (fun P => (hqset q P).symm) fun P _ => ?_).symm
  rw [hs]

include S hU in
theorem Gstarx_rm_pair (hidx : ∀ q, τ q ∈ cubeIdx G' ↔ q ∈ cubeIdx G)
    (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ Qset G' (τ q) ↔ q' ∈ Qset G q)
    (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hs : ∀ P, s' (τ P) = s P) :
    Gstarx G' a aT x ν (S.mul α) s' = rm S.Ω1Equiv (Gstarx G a aT x ν α s) := by
  unfold Gstarx
  rw [rm_sum]
  refine (Finset.sum_equiv τ (fun q => (hidx q).symm) fun q _ => ?_).symm
  rw [sProd_pair' hqset hs, rm_smul, rm_mul, rm_chiD_pair' S hchi, cubeGx_rm_pair S hU hbox]

include S hU in
theorem Kcalx_rm_pair (hidx : ∀ q, τ q ∈ cubeIdx G' ↔ q ∈ cubeIdx G)
    (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ Qset G' (τ q) ↔ q' ∈ Qset G q)
    (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hs : ∀ P, s' (τ P) = s P) :
    Kcalx G' a aT x ν (S.mul α) s' = rm S.Ω1Equiv (Kcalx G a aT x ν α s) := by
  unfold Kcalx
  rw [rm_sum]
  refine (Finset.sum_equiv τ (fun q => (hidx q).symm) fun q _ => ?_).symm
  rw [sProd_pair' hqset hs, rm_smul, rm_mul, Kzx_rm_pair S hU hchi, cubeGx_rm_pair S hU hbox]

include S hU in
/-- **Covariance of `Gsx` between two generating sets.** -/
theorem Gsx_rm_pair (hidx : ∀ q, τ q ∈ cubeIdx G' ↔ q ∈ cubeIdx G)
    (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ Qset G' (τ q) ↔ q' ∈ Qset G q)
    (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ) {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hs : ∀ P, s' (τ P) = s P) :
    Gsx G' a aT x ν (S.mul α) s' = rm S.Ω1Equiv (Gsx G a aT x ν α s) := by
  unfold Gsx
  rw [rm_mul, rm_inv, rm_sub, rm_one, Gstarx_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs,
    Kcalx_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs]

end GsxPair

section DecPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G' σ)

theorem fieldMul_restrict_symSite_pair (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    fieldMul (restrictField G' (symSite σ φ)) =
      (fieldMul (restrictField G φ)).submatrix (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm
        S.Ω1Equiv.symm := by
  ext ⟨x', i⟩ y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  simp [fieldMul, restrictField, symSite]

theorem commK_rm_pair (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    commK (rm S.Ω1Equiv H) (restrictField G' (symSite σ φ)) =
      (commK H (restrictField G φ)).submatrix S.Ω1Equiv.symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm := by
  unfold commK
  rw [fieldMul_restrict_symSite_pair S, liftOp_rm, Matrix.transpose_submatrix, rm, rm,
    submatrix_sub']
  simp only [Matrix.submatrix_mul_equiv]

theorem constraintM_rm_pair (H Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    constraintM (rm S.Ω1Equiv H) (rm S.Ω1Equiv Gm) (restrictField G' (symSite σ φ)) =
      rm S.Ω1Equiv (constraintM H Gm (restrictField G φ)) := by
  unfold constraintM
  rw [fieldMul_restrict_symSite_pair S, commK_rm_pair S, liftOp_rm, rm_sub]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

theorem constraintN_rm_pair (H Gm : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    constraintN (rm S.Ω1Equiv H) (rm S.Ω1Equiv Gm) (restrictField G' (symSite σ φ)) =
      (constraintN H Gm (restrictField G φ)).submatrix S.Ω1Equiv.symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm := by
  unfold constraintN
  rw [fieldMul_restrict_symSite_pair S, commK_rm_pair S, liftOp_rm]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, submatrix_sub']

variable (hU : UnitBlockPres σ) {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}
  (hidx : ∀ q, τ q ∈ cubeIdx G' ↔ q ∈ cubeIdx G)
  (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x)
  (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
  (hqset : ∀ q q', τ q' ∈ Qset G' (τ q) ↔ q' ∈ Qset G q)

include S hU hidx hchi hbox hqset in
/-- **Covariance of `M_{x,s}` between two generating sets.** -/
theorem decM_rm_pair (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decM G' a aT x ν (S.mul α) s' (symSite σ φ) = rm S.Ω1Equiv (decM G a aT x ν α s φ) := by
  unfold decM
  rw [xDirichletOperator_rm_pair S hU, Gsx_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs,
    constraintM_rm_pair S]

include S hU hidx hchi hbox hqset in
/-- **Covariance of `N_{x,s}` between two generating sets.** -/
theorem decN_rm_pair (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decN G' a aT x ν (S.mul α) s' (symSite σ φ) =
      (decN G a aT x ν α s φ).submatrix S.Ω1Equiv.symm
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))).symm := by
  unfold decN
  rw [xDirichletOperator_rm_pair S hU, Gsx_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs,
    constraintN_rm_pair S]

include S hU hidx hchi hbox hqset in
/-- **Covariance of `Π_{x,s}` between two generating sets**: `Π' = rm (σ × 1) Π`. -/
theorem decPi_rm_pair (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decPi G' a aT x ν (S.mul α) s' (symSite σ φ) =
      rm (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))) (decPi G a aT x ν α s φ) := by
  unfold decPi
  rw [decM_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs,
    decN_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs,
    Gsx_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs, liftOp_rm,
    fieldMul_restrict_symSite_pair S, ← rm_inv]
  simp only [rm, Matrix.submatrix_mul_equiv]

end DecPair

section UnitPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G' σ)

include S in
/-- **The unit points of two generating sets related by a lattice symmetry** (preserving the unit
blocks) correspond: there is a bijection `u` with `unitBlock (σ x) = u y ↔ unitBlock x = y`. -/
theorem exists_unitAct_pair (hU : UnitBlockPres σ) :
    ∃ u : unitPts G ≃ unitPts G', ∀ (y : unitPts G) (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k) := by
  classical
  have hl : ∀ x, σ x ∈ G'.layer (k + 1) ↔ x ∈ G.layer (k + 1) :=
    fun x => S.mem_layer (by omega) le_rfl x
  have hl' : ∀ x, σ.symm x ∈ G.layer (k + 1) ↔ x ∈ G'.layer (k + 1) := fun x => by
    have := hl (σ.symm x)
    simpa using this.symm
  let f : unitPts G → unitPts G' := fun y =>
    ⟨unitBlock (σ (Classical.choose ((mem_unitPts G).1 y.2))),
      (mem_unitPts G').2 ⟨_, (hl _).2 (Classical.choose_spec ((mem_unitPts G).1 y.2)).1, rfl⟩⟩
  let g : unitPts G' → unitPts G := fun y =>
    ⟨unitBlock (σ.symm (Classical.choose ((mem_unitPts G').1 y.2))),
      (mem_unitPts G).2 ⟨_, (hl' _).2 (Classical.choose_spec ((mem_unitPts G').1 y.2)).1, rfl⟩⟩
  have hf : ∀ (y : unitPts G) (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock x = (y : UnitTorus d L N₁ m₁ k) →
        unitBlock (σ x) = ((f y : unitPts G') : UnitTorus d L N₁ m₁ k) := by
    intro y x hx
    have h0 := (Classical.choose_spec ((mem_unitPts G).1 y.2)).2
    exact (hU _ _).2 (hx.trans h0.symm)
  have hg : ∀ (y : unitPts G') (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock x = (y : UnitTorus d L N₁ m₁ k) →
        unitBlock (σ.symm x) = ((g y : unitPts G) : UnitTorus d L N₁ m₁ k) := by
    intro y x hx
    have h0 := (Classical.choose_spec ((mem_unitPts G').1 y.2)).2
    exact (hU.symm _ _).2 (hx.trans h0.symm)
  refine ⟨{ toFun := f, invFun := g, left_inv := fun y => ?_, right_inv := fun y => ?_ },
    fun y x => ?_⟩
  · apply Subtype.ext
    obtain ⟨x, -, hx⟩ := (mem_unitPts G).1 y.2
    have h1 := hf y x hx
    have h2 := hg (f y) (σ x) h1
    simpa [hx] using h2.symm
  · apply Subtype.ext
    obtain ⟨x, -, hx⟩ := (mem_unitPts G').1 y.2
    have h1 := hg y x hx
    have h2 := hf (g y) (σ.symm x) h1
    simpa [hx] using h2.symm
  · obtain ⟨x₀, -, hx₀⟩ := (mem_unitPts G).1 y.2
    have h1 : unitBlock (σ x₀) = ((f y : unitPts G') : UnitTorus d L N₁ m₁ k) := hf y x₀ hx₀
    show unitBlock (σ x) = ((f y : unitPts G') : UnitTorus d L N₁ m₁ k) ↔ _
    rw [← h1, ← hx₀]
    exact hU x x₀

variable {u : unitPts G ≃ unitPts G'}
  (hu : ∀ (y : unitPts G) (x : CTorus d L N₁ m₁ (k + 1)),
    unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k))

include hu in
theorem unitQ_pair (y : unitPts G) (x : G.Ω 1) :
    unitQ G' (u y) (S.Ω1Equiv x) = unitQ G y x := by
  unfold unitQ
  simp only [LatSymm.coe_Ω1Equiv]
  by_cases h : unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = y
  · have h' := (hu y x).2 h
    simp [h, h']
  · have h' : ¬ unitBlock (σ (x : CTorus d L N₁ m₁ (k + 1))) = (u y : UnitTorus d L N₁ m₁ k) :=
      fun h' => h ((hu y x).1 h')
    simp [h, h']

include S hu in
theorem unitBlock1_pair_iff (y y' : unitPts G) :
    unitBlock1 (u y : UnitTorus d L N₁ m₁ k) = unitBlock1 (u y' : UnitTorus d L N₁ m₁ k) ↔
      unitBlock1 (y : UnitTorus d L N₁ m₁ k) = unitBlock1 (y' : UnitTorus d L N₁ m₁ k) := by
  obtain ⟨x, hxl, hx⟩ := (mem_unitPts G).1 y.2
  obtain ⟨x', -, hx'⟩ := (mem_unitPts G).1 y'.2
  have e1 := (hu y x).2 hx
  have e2 := (hu y' x').2 hx'
  rw [← e1, ← e2, ← hx, ← hx', unitBlock1_unitBlock, unitBlock1_unitBlock,
    unitBlock1_unitBlock, unitBlock1_unitBlock]
  exact S.block (k + 1) (by omega) le_rfl ⟨x, hxl⟩ x x'

include S hu in
theorem unitP_pair (y y' : unitPts G) : unitP G' (u y) (u y') = unitP G y y' := by
  unfold unitP
  simp only [unitBlock1_pair_iff S hu y y']

include S hu in
theorem liftRect_unitQ_pair :
    (liftRect N (unitQ G')).submatrix (u.prodCongr (Equiv.refl (Fin N)))
        (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N))) = liftRect N (unitQ G) := by
  ext ⟨y, i⟩ ⟨x, j⟩
  simp [liftRect, unitQ_pair S hu]

include S hu in
theorem liftOp_unitP_pair :
    rm (u.prodCongr (Equiv.refl (Fin N))) (liftOp N (unitP G)) = liftOp N (unitP G') := by
  ext ⟨y', i⟩ ⟨z', j⟩
  obtain ⟨y, rfl⟩ := u.surjective y'
  obtain ⟨z, rfl⟩ := u.surjective z'
  simp [rm, liftOp, unitP_pair S hu]

end UnitPair

section CovPair

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G' σ) (hU : UnitBlockPres σ) {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}
  (hidx : ∀ q, τ q ∈ cubeIdx G' ↔ q ∈ cubeIdx G)
  (hchi : ∀ q x, chi G' (τ q) (σ x) = chi G q x)
  (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
  (hqset : ∀ q q', τ q' ∈ Qset G' (τ q) ↔ q' ∈ Qset G q)
  {u : unitPts G ≃ unitPts G'}
  (hu : ∀ (y : unitPts G) (x : CTorus d L N₁ m₁ (k + 1)),
    unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k))

/-- The algebra of the conjugation in `decCov`, between two index sets. -/
theorem conj_alg_pair {U U' W W' : Type*} [Fintype U] [DecidableEq U] [Fintype U']
    [DecidableEq U'] [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']
    (e : U ≃ U') (f : W ≃ W') (A : Matrix U U ℂ) (A' : Matrix U' U' ℂ) (X : Matrix U W ℂ)
    (X' : Matrix U' W' ℂ) (Gl Pi : Matrix W W ℂ)
    (hA : rm e A = A') (hX : X'.submatrix e f = X) :
    A' * X' * (rm f Gl - rm f Pi) * X'ᵀ * A' = rm e (A * X * (Gl - Pi) * Xᵀ * A) := by
  have hX' : X' = X.submatrix e.symm f.symm := by
    rw [← hX]; ext; simp
  rw [← hA, hX', ← rm_sub]
  simp only [rm, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]

include S hU hidx hchi hbox hqset hu in
/-- **Covariance of `C_x(s)` between two generating sets** on the unit points: `C'_x(s') =
rm (u × 1) C_x(s)`. -/
theorem decCov_rm_pair (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decCov G' a aT x ν (S.mul α) s' (symSite σ φ) (unitQ G') (unitP G') =
      rm (u.prodCongr (Equiv.refl (Fin N)))
        (decCov G a aT x ν α s φ (unitQ G) (unitP G)) := by
  unfold decCov
  rw [Gsx_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs,
    decPi_rm_pair S hU hidx hchi hbox hqset a aT x ν α hs, liftOp_rm, rm_add, rm_smul]
  have hA : rm (u.prodCongr (Equiv.refl (Fin N)))
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) =
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G')) := by
    rw [← covA_rm, liftOp_unitP_pair S hu]
  have key := conj_alg_pair (u.prodCongr (Equiv.refl (Fin N)))
    (S.Ω1Equiv.prodCongr (Equiv.refl (Fin N)))
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)))
    (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G'))) (liftRect N (unitQ G))
    (liftRect N (unitQ G'))
    (liftOp N (Gsx G a aT x ν α s)) (decPi G a aT x ν α s φ) hA (liftRect_unitQ_pair S hu)
  rw [hA, ← key]

include S hU hidx hchi hbox hqset hu in
/-- **Covariance of the square root `C^{1/2}(s)` between two generating sets.** -/
theorem decCovSqrt_rm_pair (a : ℕ → ℝ) (aT ν : ℝ) (α : G.Ω 1 → ℂ)
    {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :
    decCovSqrt G' a aT ν (S.mul α) s' (symSite σ φ) (unitQ G') (unitP G') =
      rm (u.prodCongr (Equiv.refl (Fin N)))
        (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G)) := by
  have hint : decSqrtInt G' a aT ν (S.mul α) s' (symSite σ φ) (unitQ G') (unitP G') =
      fun x => rm (u.prodCongr (Equiv.refl (Fin N)))
        (decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x) := by
    funext x
    unfold decSqrtInt
    rw [decCov_rm_pair S hU hidx hchi hbox hqset hu a aT x ν α hs φ, rm_smul]
  unfold decCovSqrt
  rw [hint, intMat_rm, rm_smul]

end CovPair

end Balaban.Localization.DetDecCov
