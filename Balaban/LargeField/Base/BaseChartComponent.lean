/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartGaussianNormalization
public import Balaban.LargeField.Base.BaseChartGaussian

/-!
# Coordinates of the physical first-step chart operator

The real chart form of P4 (2.44) and the complex base operator of
BASE-KERNEL-3 (1.3) use the same tangent and normal projections.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- In Euclidean coordinates, the normal projection is the matrix with
entries `eₓᵢ eₓⱼ` at each site. -/
theorem normalProj_toMatrix (e : Config ι N) :
    LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (normalProj e) =
    (fun p q : (Σ _ : ι, Fin N) => if p.1 = q.1 then
      (e p.1 p.2 : ℝ) * (e p.1 q.2 : ℝ) else 0) := by
  classical
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [LinearMap.toMatrix_apply, Pi.basis_apply]
  simp [normalProj, EuclideanSpace.inner_eq_star_dotProduct,
    Pi.single_apply, dotProduct]
  by_cases hxy : x = y
  · subst y
    simp [mul_comm]
  · simp [hxy]

/-- Coordinate matrix of `Q H Q + P`, with `P` the normal projection.
This is the real matrix form of BASE-KERNEL-3 (1.3). -/
theorem gaussForm_toMatrix (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N) :
    let B := Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
    let P := LinearMap.toMatrix B B (normalProj e)
    let M := LinearMap.toMatrix B B H
    LinearMap.toMatrix B B (gaussForm e H) = (1 - P) * M * (1 - P) + P := by
  let B := Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  change LinearMap.toMatrix B B (gaussForm e H) =
    (1 - LinearMap.toMatrix B B (normalProj e)) *
      LinearMap.toMatrix B B H *
      (1 - LinearMap.toMatrix B B (normalProj e)) +
      LinearMap.toMatrix B B (normalProj e)
  rw [gaussForm, map_add]
  rw [LinearMap.toMatrix_comp B B B, LinearMap.toMatrix_comp B B B]
  simp only [tangentOp, map_sub, LinearMap.toMatrix_id]
  rw [Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- A symmetric scalar Hessian gives a symmetric chart form. -/
theorem gaussForm_cinner_symmetric (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N)
    (hH : ∀ u v, cinner u (H v) = cinner (H u) v)
    (u v : Config ι N) :
    cinner u (gaussForm e H v) = cinner (gaussForm e H u) v := by
  simp only [gaussForm, LinearMap.add_apply, LinearMap.comp_apply]
  rw [cinner_add_right, cinner_add_left,
    cinner_tangentOp_comm e, hH,
    cinner_tangentOp_comm e, cinner_normalProj_comm e]

/-- Symmetry in the configuration inner product becomes matrix symmetry in
the standard Euclidean coordinate basis. -/
theorem toMatrix_isSymm_of_cinner
    (T : Config ι N →ₗ[ℝ] Config ι N)
    (hT : ∀ u v, cinner u (T v) = cinner (T u) v) :
    (LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)) T).IsSymm := by
  classical
  let B := Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  have hcoord (u v : Config ι N) :
      cinner u v = (B.repr u) ⬝ᵥ (B.repr v) := by
    simp [cinner, B, dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
      Finset.sum_sigma', mul_comm]
  have hentry (p q : Σ _ : ι, Fin N) :
      LinearMap.toMatrix B B T p q = cinner (B p) (T (B q)) := by
    rw [LinearMap.toMatrix_apply]
    rw [hcoord]
    simp [dotProduct, Finsupp.single_apply]
  apply Matrix.IsSymm.ext
  intro p q
  rw [hentry, hentry]
  calc
    cinner (B q) (T (B p)) = cinner (T (B q)) (B p) := hT _ _
    _ = cinner (B p) (T (B q)) := cinner_comm _ _

/-- Coordinates of a scalar site matrix acting on every spin coordinate. -/
theorem componentwise_toMatrix (H : Config ι N →ₗ[ℝ] Config ι N)
    (A : Matrix ι ι ℝ)
    (hH : ∀ u x i, (H u x i : ℝ) = ∑ y, A x y * (u y i : ℝ)) :
    LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)) H =
    (fun p q : (Σ _ : ι, Fin N) => if p.2 = q.2 then A p.1 q.1 else 0) := by
  classical
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [LinearMap.toMatrix_apply, Pi.basis_apply, hH,
    EuclideanSpace.basisFun_apply, Pi.single_apply,
    EuclideanSpace.single, eq_comm]
  rw [Finset.sum_eq_single y]
  · simp [PiLp.single_apply]
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

/-- The coordinate chart form is the real transport of the complex base operator
for a componentwise scalar Hessian (BASE-KERNEL-3 (1.3)). -/
theorem gaussForm_toMatrix_baseOp (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N) (A : Matrix ι ι ℝ)
    (hH : ∀ u x i, (H u x i : ℝ) = ∑ y, A x y * (u y i : ℝ)) :
    let B := Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
    let σ := Equiv.sigmaEquivProd ι (Fin N)
    ((Matrix.reindex σ σ
      (LinearMap.toMatrix B B (gaussForm e H))).map (algebraMap ℝ ℂ)) =
      baseOp N (fun x i => ((e x i : ℝ) : ℂ))
        (A.map (algebraMap ℝ ℂ)) := by
  classical
  let B := Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  let σ := Equiv.sigmaEquivProd ι (Fin N)
  let F := Matrix.reindexRingEquiv ℝ σ
  let K := LinearMap.toMatrix B B (gaussForm e H)
  let P := LinearMap.toMatrix B B (normalProj e)
  let M := LinearMap.toMatrix B B H
  have hP : (F P).map (algebraMap ℝ ℂ) =
      basePart (fun x i => ((e x i : ℝ) : ℂ)) := by
    have hP0 := normalProj_toMatrix e
    change P = (fun p q : (Σ _ : ι, Fin N) =>
      if p.1 = q.1 then (e p.1 p.2 : ℝ) * (e p.1 q.2 : ℝ) else 0) at hP0
    rw [hP0]
    ext p q
    rw [basePart_real, unitProj_apply]
    change ((if p.1 = q.1 then
      (e p.1 p.2 : ℝ) * (e p.1 q.2 : ℝ) else 0 : ℝ) : ℂ) = _
    split_ifs <;> simp
  have hM : (F M).map (algebraMap ℝ ℂ) =
      liftOp N (A.map (algebraMap ℝ ℂ)) := by
    have hM0 := componentwise_toMatrix H A hH
    change M = (fun p q : (Σ _ : ι, Fin N) =>
      if p.2 = q.2 then A p.1 q.1 else 0) at hM0
    rw [hM0]
    ext p q
    change ((if p.2 = q.2 then A p.1 q.1 else 0 : ℝ) : ℂ) = _
    split_ifs with h <;> simp [liftOp, h]
  change (F K).map (algebraMap ℝ ℂ) = _
  rw [show K = (1 - P) * M * (1 - P) + P from gaussForm_toMatrix e H]
  simp only [map_add, map_sub, map_mul, map_one]
  rw [Matrix.map_add (algebraMap ℝ ℂ) (map_add (algebraMap ℝ ℂ))]
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.map_sub (algebraMap ℝ ℂ) (map_sub (algebraMap ℝ ℂ)), Matrix.map_one]
  rw [hP, hM]
  rfl
  all_goals simp

/-- A symmetric real matrix whose complexification has a positive coercivity
constant is positive definite. -/
theorem real_posDef_of_complex_coercive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : Matrix κ κ ℝ) (hKs : K.IsSymm) (γ : ℝ) (hγ : 0 < γ)
    (hK : Balaban.Green.IsCoercive (K.map (algebraMap ℝ ℂ)) γ) : K.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_iff_isSymm.mpr hKs)
  intro v hv
  have hnorm : Balaban.Green.sqNorm (fun i => (v i : ℂ)) = v ⬝ᵥ v := by
    simp [Balaban.Green.sqNorm, dotProduct, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [pow_two]
  have hquad : Balaban.Green.reQuad (K.map (algebraMap ℝ ℂ))
      (fun i => (v i : ℂ)) = v ⬝ᵥ K *ᵥ v := by
    rw [Balaban.reQuad_map_ofReal]
    simp [dotProduct]
  have hc := hK (fun i => (v i : ℂ))
  rw [hnorm, hquad] at hc
  have hvpos : 0 < v ⬝ᵥ v := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (funext hn)
    change 0 < ∑ i, v i * v i
    have hs : 0 < ∑ i, v i ^ 2 :=
      Finset.sum_pos' (fun i _ => sq_nonneg (v i))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    simpa only [pow_two] using hs
  exact lt_of_lt_of_le (mul_pos hγ hvpos) hc

/-- Coercivity is invariant under a bijective change of matrix indices. -/
theorem isCoercive_reindex {κ τ : Type*} [Fintype κ] [Fintype τ]
    [DecidableEq κ] [DecidableEq τ] (A : Matrix κ κ ℂ) (γ : ℝ)
    (hA : Balaban.Green.IsCoercive A γ) (e : κ ≃ τ) :
    Balaban.Green.IsCoercive (Matrix.reindex e e A) γ := by
  intro v
  let w : κ → ℂ := v ∘ e
  have hn : Balaban.Green.sqNorm v = Balaban.Green.sqNorm w := by
    unfold Balaban.Green.sqNorm
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
  have hm : (Matrix.reindex e e A) *ᵥ v = (A *ᵥ w) ∘ e.symm := by
    exact Matrix.submatrix_mulVec_equiv A v e.symm e.symm
  have hq : Balaban.Green.reQuad (Matrix.reindex e e A) v =
      Balaban.Green.reQuad A w := by
    unfold Balaban.Green.reQuad
    rw [hm]
    congr 1
    exact (Fintype.sum_equiv e
      (fun j : κ => star (w j) * (A *ᵥ w) j)
      (fun i : τ => star (v i) * (A *ᵥ w) (e.symm i))
      (by intro j; simp [w])).symm
  rw [hn, hq]
  exact hA w

/-- The real-background base operator commutes with relabelling sites. -/
theorem baseOp_reindex_real {κ τ : Type*} [Fintype κ] [Fintype τ]
    [DecidableEq κ] [DecidableEq τ] (t : κ ≃ τ)
    (e : κ → Fin N → ℝ) (H : Matrix κ κ ℂ) :
    let ρ := Equiv.prodCongr t (Equiv.refl (Fin N))
    Matrix.reindex ρ ρ (baseOp N (fun x i => (e x i : ℂ)) H) =
      baseOp N (fun x i => (e (t.symm x) i : ℂ))
        (Matrix.reindex t t H) := by
  classical
  let ρ := Equiv.prodCongr t (Equiv.refl (Fin N))
  let F := Matrix.reindexRingEquiv ℂ ρ
  have hP : F (basePart (fun x i => (e x i : ℂ))) =
      basePart (fun x i => (e (t.symm x) i : ℂ)) := by
    rw [basePart_real, basePart_real]
    ext p q
    change unitProj e (ρ.symm p) (ρ.symm q) =
      unitProj (fun x i => e (t.symm x) i) p q
    rw [unitProj_apply, unitProj_apply]
    change (if t.symm p.1 = t.symm q.1 then
      (e (t.symm p.1) p.2 : ℂ) * (e (t.symm p.1) q.2 : ℂ) else 0) = _
    simp only [t.symm_apply_eq]
    by_cases h : p.1 = q.1 <;> simp [h]
  have hL : F (liftOp N H) = liftOp N (Matrix.reindex t t H) := by
    ext p q
    change (if p.2 = q.2 then H (t.symm p.1) (t.symm q.1) else 0) = _
    simp [liftOp]
  change F (baseOp N (fun x i => (e x i : ℂ)) H) = _
  rw [baseOp, baseOp]
  simp only [map_add, map_mul, map_sub, map_one, hP, hL]

variable {d L n : ℕ} [NeZero L] [NeZero n]

/-- The physical P4 (2.44) Hessian acts by the lifted real scalar matrix
in Euclidean coordinates. -/
theorem baseSectorHessian_toMatrix (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let site : Torus d (L * n) → G.Ω 1 := fun x =>
      ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
    let A : Matrix (Torus d (L * n)) (Torus d (L * n)) ℝ :=
      fun x y => fullMatrix G aw μ (site x : Torus d (1 * n * L ^ 1))
        (site y : Torus d (1 * n * L ^ 1)) +
        if x = y then α (site x) else 0
    LinearMap.toMatrix
      (Pi.basis (fun _ : Torus d (L * n) =>
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : Torus d (L * n) =>
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (baseSectorHessian ϱ aw μ α) =
    (fun p q : (Σ _ : Torus d (L * n), Fin N) =>
      if p.2 = q.2 then A p.1 q.1 else 0) := by
  dsimp only
  let A : Matrix (Torus d (L * n)) (Torus d (L * n)) ℝ :=
    fun x y => fullMatrix (GeneratingSet.single ϱ) aw μ
      ((baseSector_side L n).symm ▸ x) ((baseSector_side L n).symm ▸ y) +
      if x = y then α ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩ else 0
  have hH := componentwise_toMatrix (baseSectorHessian (N := N) ϱ aw μ α) A (by
    intro u x i
    simpa only [A] using baseSectorHessian_apply ϱ aw μ α u x i)
  simpa only [A] using hH

/-- The full physical chart matrix is the complex base operator transported
to physical torus sites, with the real multiplier of P4 (2.44). -/
theorem baseSector_gaussForm_toMatrix_baseOp (ϱ : ℝ) (aw : ℕ → ℝ) (μ : ℝ)
    (α : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 → ℝ)
    (e : Config (Torus d (L * n)) N) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let site : Torus d (L * n) → G.Ω 1 := fun x =>
      ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
    let B := Pi.basis (fun _ : Torus d (L * n) =>
      (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
    let σ := Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N)
    (Matrix.reindex σ σ (LinearMap.toMatrix B B
      (gaussForm e (baseSectorHessian ϱ aw μ α)))).map (algebraMap ℝ ℂ) =
      baseOp N (fun x i => ((e x i : ℝ) : ℂ))
        (fun x y => dirichletOperator G aw μ (fun z => (α z : ℂ))
          (site x) (site y)) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let site : Torus d (L * n) → G.Ω 1 := fun x =>
    ⟨(baseSector_side L n).symm ▸ x,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
  let A : Matrix (Torus d (L * n)) (Torus d (L * n)) ℝ :=
    fun x y => fullMatrix G aw μ (site x : Torus d (1 * n * L ^ 1))
      (site y : Torus d (1 * n * L ^ 1)) +
      if x = y then α (site x) else 0
  have hH (u : Config (Torus d (L * n)) N) (x : Torus d (L * n)) (i : Fin N) :
      (baseSectorHessian ϱ aw μ α u x i : ℝ) =
        ∑ y, A x y * (u y i : ℝ) := by
    simpa only [A, site] using baseSectorHessian_apply ϱ aw μ α u x i
  have hK := gaussForm_toMatrix_baseOp e (baseSectorHessian ϱ aw μ α) A hH
  have hA : A.map (algebraMap ℝ ℂ) =
      (fun x y => dirichletOperator G aw μ (fun z => (α z : ℂ))
        (site x) (site y)) := by
    ext x y
    exact (baseSectorHessian_coeff_eq ϱ aw μ α x y).symm
  rw [hA] at hK
  exact hK

/-- On nonzero first-sector support, the physical P4 (2.44) chart matrix is
positive definite. The estimate comes from the uncut BASE-KERNEL-3 (1.5)
base-operator coercivity after transport of the fine sites. -/
theorem baseSector_gaussForm_posDef_of_product_ne_zero
    (ϱ : ℝ) (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ)
    (hδ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let Hα := baseSectorHessian ϱ aw (if regimeB then ν else 0)
      (fun z => (α z).re)
    (LinearMap.toMatrix
      (Pi.basis (fun _ : Torus d (L * n) =>
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : Torus d (L * n) =>
        (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm e Hα)).PosDef := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
  let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
  let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
    baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
  let B := Pi.basis (fun _ : Torus d (L * n) =>
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  let K := LinearMap.toMatrix B B (gaussForm e Hα)
  let site : Torus d (L * n) → G.Ω 1 := fun x =>
    ⟨(baseSector_side L n).symm ▸ x,
      baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
  have castF {a b : ℕ} (h : a = b) (x : Torus d b) :
      h ▸ (h.symm ▸ x) = x := by
    cases h
    rfl
  have castR {a b : ℕ} (h : a = b) (x : Torus d a) :
      h.symm ▸ (h ▸ x) = x := by
    cases h
    rfl
  have hcastF (x : Torus d (L * n)) :
      baseSector_side L n ▸ ((baseSector_side L n).symm ▸ x) = x := by
    exact castF (baseSector_side L n) x
  have hcastR (x : Torus d (1 * n * L ^ 1)) :
      (baseSector_side L n).symm ▸ (baseSector_side L n ▸ x) = x := by
    exact castR (baseSector_side L n) x
  let t : G.Ω 1 ≃ Torus d (L * n) :=
    { toFun := fun z => baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))
      invFun := site
      left_inv := by intro z; apply Subtype.ext; exact hcastR z.1
      right_inv := hcastF }
  let ρ := Equiv.prodCongr t (Equiv.refl (Fin N))
  let σ := Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N)
  let a : G.Ω 1 → Fin N → ℝ := fun z i => (e (t z) i : ℝ)
  let D := dirichletOperator G aw (if regimeB then ν else 0)
    (fun z => ((α z).re : ℂ))
  let A := baseOp N (fun z i => (a z i : ℂ)) D
  let Aphys := baseOp N (fun x i => (e x i : ℂ))
    (fun x y => D (site x) (site y))
  have hα (z : G.Ω 1) : α z = ((α z).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using baseSector_bgMult_real_of_product_ne_zero
        ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp z
  have hD : baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1) = D := by
    rw [baseHamiltonian_one]
    congr 1
    funext z
    exact hα z
  have hnat : Balaban.Green.IsCoercive A (baseCoercivity L) := by
    have hc := baseSector_baseOp_coercive_of_product_ne_zero
      ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
    change Balaban.Green.IsCoercive
      (baseOp N (fun z i => (a z i : ℂ))
        (baseHamiltonian G aw (if regimeB then ν else 0) α (fun _ => 1)))
      (baseCoercivity L) at hc
    rw [hD] at hc
    exact hc
  have htrans : Matrix.reindex ρ ρ A = Aphys := by
    have hr := baseOp_reindex_real t a D
    change Matrix.reindex ρ ρ A =
      baseOp N (fun x i => (a (t.symm x) i : ℂ))
        (Matrix.reindex t t D) at hr
    rw [hr]
    unfold Aphys
    congr 1
    · funext x i
      simp [a]
  have hphys : Balaban.Green.IsCoercive Aphys (baseCoercivity L) := by
    rw [← htrans]
    exact isCoercive_reindex A (baseCoercivity L) hnat ρ
  have hK : (Matrix.reindex σ σ K).map (algebraMap ℝ ℂ) = Aphys := by
    have hk := baseSector_gaussForm_toMatrix_baseOp ϱ aw
      (if regimeB then ν else 0) (fun z => (α z).re) e
    simpa only [K, B, σ, Aphys, D, site] using hk
  have hKC : K.map (algebraMap ℝ ℂ) =
      Matrix.reindex σ.symm σ.symm Aphys := by
    ext p q
    have hpq := congrArg (fun M : Matrix (Torus d (L * n) × Fin N)
      (Torus d (L * n) × Fin N) ℂ => M (σ p) (σ q)) hK
    simpa [Matrix.reindex_apply] using hpq
  have hcoerK : Balaban.Green.IsCoercive (K.map (algebraMap ℝ ℂ))
      (baseCoercivity L) := by
    rw [hKC]
    exact isCoercive_reindex Aphys (baseCoercivity L) hphys σ.symm
  have hsym : K.IsSymm :=
    toMatrix_isSymm_of_cinner (gaussForm e Hα)
      (gaussForm_cinner_symmetric e Hα
        (baseSectorHessian_symmetric ϱ aw (if regimeB then ν else 0)
          (fun z => (α z).re)))
  exact real_posDef_of_complex_coercive K hsym (baseCoercivity L)
    (baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L))) hcoerK

variable [NeZero N]

/-- At a crossing-bond cut, the principal logarithmic Gaussian normalization
of BASE-KERNEL-3 (1.3) factors between a first-block component and its
complement. At the physical parameter `s = 1`, the uncut chart Hessian is
recovered; this factorization uses `CrossZero` and therefore belongs to the
cut family. -/
theorem baseSector_component_exp_normalization_factorization
    (ϱ : ℝ) (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ)
    (hδ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (U : Set (Torus d (1 * n * L ^ 1)))
    (hU : IsFirstBlockUnion (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U)
    (hU0 : ∃ z : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
      (z : Torus d (1 * n * L ^ 1)) ∈ U)
    (hUc : ∃ z : (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1,
      (z : Torus d (1 * n * L ^ 1)) ∉ U)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d))
    (s : FineBond d L (1 * n) → ℂ)
    (hs : s ∈ baseParamNbhd (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) η)
    (hz : CrossZero (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) U s) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let P : G.Ω 1 × Fin N → Prop := fun p =>
      (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let J := {p : G.Ω 1 × Fin N // ¬ P p}
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    let A_V : Matrix J J ℂ := A.submatrix Subtype.val Subtype.val
    Complex.exp (-(1 / 2) * (Balaban.Localization.logMat A).trace) =
      Complex.exp (-(1 / 2) * (Balaban.Localization.logMat A_U).trace) *
        Complex.exp (-(1 / 2) * (Balaban.Localization.logMat A_V).trace) := by
  dsimp only
  have ht := (baseSector_component_logDet_factorization
    ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
    U hU hU0 hUc hη0 hη s hs hz).1
  rw [ht]
  rw [← Complex.exp_add]
  ring_nf

end Balaban.LargeField
