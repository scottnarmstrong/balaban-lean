/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutFamily
public import Balaban.LargeField.Base.BaseChartComponentGauss

/-!
# The cut chart integral at a real selected cut as a normalized Gaussian integral

At a real cut parameter the cut quadratic form of BASE-KERNEL-3 (1.2) is the
quadratic form of a real componentwise Hessian whose chart matrix is the
real matrix of the cut operator `A(s)` of (1.3). The tangent Gaussian integral
of the cut chart then carries the normalization `det (pdSqrtInv K)` of P4
(2.47)–(2.54).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green Matrix MeasureTheory SphereChart
  Classical
open Balaban.LargeField.Base Balaban.Localization

section Generic

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] {N : ℕ}

omit [DecidableEq ι] in
/-- A real componentwise Hessian on `Config ι N` with the prescribed scalar matrix. -/
theorem exists_componentwise_hessian (A : Matrix ι ι ℝ) :
    ∃ Hs : Config ι N →ₗ[ℝ] Config ι N,
      ∀ u x i, (Hs u x i : ℝ) = ∑ y, A x y * (u y i : ℝ) := by
  refine ⟨
    { toFun := fun u x => WithLp.toLp 2 (fun i : Fin N =>
        ∑ y : ι, A x y * ((u y) i : ℝ))
      map_add' := by
        intro u v
        funext x
        ext i
        change (∑ y, A x y * (((u + v) y i) : ℝ)) =
          (∑ y, A x y * (u y i : ℝ)) + (∑ y, A x y * (v y i : ℝ))
        simp only [Pi.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c u
        funext x
        ext i
        change (∑ y, A x y * (((c • u) y i) : ℝ)) =
          c * ∑ y, A x y * (u y i : ℝ)
        simp only [Pi.smul_apply, PiLp.smul_apply,
          smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring }, ?_⟩
  intro u x i
  rfl

omit [Fintype τ] [DecidableEq τ] in
/-- For a complex matrix with real entries, the componentwise Hessian of
its real part (transported along `t`) has chart matrix the real matrix of the
base operator, up to the relabelling of indices. -/
theorem exists_hessian_chart_of_real_baseOp (t : τ ≃ ι) (e : Config ι N)
    (H : Matrix τ τ ℂ) (hH : ∀ x y, (H x y).im = 0) :
    ∃ Hs : Config ι N →ₗ[ℝ] Config ι N,
      (∀ u x i, (Hs u x i : ℝ) =
        ∑ y, (H (t.symm x) (t.symm y)).re * (u y i : ℝ)) ∧
      (Matrix.reindex (Equiv.sigmaEquivProd ι (Fin N))
        (Equiv.sigmaEquivProd ι (Fin N))
        (LinearMap.toMatrix
          (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
          (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
          (gaussForm e Hs))).map (algebraMap ℝ ℂ) =
        baseOp N (fun x i => (e x i : ℂ)) (fun x y => H (t.symm x) (t.symm y)) := by
  obtain ⟨Hs, hHs⟩ := exists_componentwise_hessian (N := N)
    (fun x y => (H (t.symm x) (t.symm y)).re)
  refine ⟨Hs, hHs, ?_⟩
  have hk := gaussForm_toMatrix_baseOp e Hs
    (fun x y => (H (t.symm x) (t.symm y)).re) hHs
  dsimp only at hk
  rw [hk]
  congr 1
  ext x y
  apply Complex.ext
  · exact Complex.ofReal_re _
  · exact (Complex.ofReal_im _).trans (hH _ _).symm

omit [DecidableEq ι] [DecidableEq τ] in
/-- The quadratic form of the lifted complex matrix with real entries is the real
chart quadratic form of the componentwise Hessian of its real part. -/
theorem pair_liftOp_eq_cinner (t : τ ≃ ι) (H : Matrix τ τ ℂ)
    (hH : ∀ x y, (H x y).im = 0) (Hs : Config ι N →ₗ[ℝ] Config ι N)
    (hHs : ∀ u x i, (Hs u x i : ℝ) =
      ∑ y, (H (t.symm x) (t.symm y)).re * (u y i : ℝ)) (w : Config ι N) :
    (∑ p : τ × Fin N, ((w (t p.1) p.2 : ℝ) : ℂ) *
      (liftOp N H *ᵥ fun p : τ × Fin N => ((w (t p.1) p.2 : ℝ) : ℂ)) p) =
      ((cinner w (Hs w) : ℝ) : ℂ) := by
  have hre (x y : τ) : H x y = (((H x y).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simpa using hH x y)
  have hrhs : cinner w (Hs w) = ∑ z : τ, ∑ i : Fin N, (w (t z) i : ℝ) *
      ∑ z' : τ, (H z z').re * (w (t z') i : ℝ) := by
    unfold cinner
    rw [← Equiv.sum_comp t]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
    congr 1
    rw [hHs, ← Equiv.sum_comp t]
    simp
  rw [hrhs]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, liftOp, Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul]
  simp
  exact Finset.sum_congr rfl fun x _ => by rw [← hre z x]

end Generic

section Physical

variable {d N L n : ℕ} [NeZero L] [NeZero n]

attribute [local fun_prop] measurable_chartMapPi

/-- At a real selected cut `s` in the coercive neighbourhood, the cut chart integral
of the first physical sphere chart is the Gaussian prefactor
`(2π)^((N-1)|D|/2) * det (pdSqrtInv K)` times the standard Gaussian integral of the
transported remainder, where `K` is the real coordinate matrix of the cut operator
`A(s)` of BASE-KERNEL-3 (1.3). The remainder keeps the missing crossing-bond form
`q 1 - q s`, the hard-spin normal-coordinate terms, the P5 cutoff, Jacobian and source.
The real cut Hessian `Hs` has chart matrix the transport of `A(s)` to physical sites. -/
theorem baseSectorChartIntegral_eq_cut_normalized
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0)
    {η : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d))
    (s : FineBond d L (1 * n) → ℂ)
    (hs : s ∈ baseParamNbhd (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) η)
    (hsr : ∀ b ∈ baseCutBonds (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ), (s b).im = 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let eG : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let A := baseOp N (fun z i => (eG z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let K := A.map Complex.re
    let site : Torus d (L * n) → G.Ω 1 := fun x =>
      ⟨(baseSector_side L n).symm ▸ x,
        baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩
    let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
      let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
      let z := chartShift β e w
      let W : G.Ω 1 × Fin N → ℂ := fun p =>
        (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
      let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
        (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
          (if regimeB then ν else 0) α t) *ᵥ W)
      let M := β * (ν - (if regimeB then ν else 0)) / 2 *
        ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
      ((chartJac β w : ℝ) : ℂ) *
        ((χ φ : ℂ) *
          ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (
            -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
              (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
            (∑ x : Torus d (L * n), ∑ i : Fin N,
              g x i * (((e x) i : ℝ) : ℂ)) +
            (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              (∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((w x + z x) i : ℝ) : ℂ)) -
            (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
              (q (fun _ => 1) - q s))))
    K.PosDef ∧
    ∃ Hs : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N,
      (∀ u x i, (Hs u x i : ℝ) =
        ∑ y, (baseHamiltonian G aw (if regimeB then ν else 0) α s
          (site x) (site y)).re * (u y i : ℝ)) ∧
      (Matrix.reindex (Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N))
        (Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N))
        (LinearMap.toMatrix
          (Pi.basis (fun _ : Torus d (L * n) =>
            (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
          (Pi.basis (fun _ : Torus d (L * n) =>
            (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
          (gaussForm e Hs))).map (algebraMap ℝ ℂ) =
        baseOp N (fun x i => ((e x i : ℝ) : ℂ))
          (fun x y => baseHamiltonian G aw (if regimeB then ν else 0) α s
            (site x) (site y)) ∧
      ∃ R : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N,
        (∀ w, gaussForm e Hs (R (R w)) = w) ∧
        (∀ u v, cinner (R u) v = cinner u (R v)) ∧
        LinearMap.det (R : Config (Torus d (L * n)) N →ₗ[ℝ]
          Config (Torus d (L * n)) N) = (pdSqrtInv K).det ∧
        baseChartIntegral d N L n β a₀ ν h g θ χ e he =
          ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
            ((((2 * Real.pi) ^ (((N : ℝ) - 1) *
              Fintype.card (Torus d (L * n)) / 2) * (pdSqrtInv K).det : ℝ) : ℂ) *
              ∫ ψ, F (tangentProj e he (R ψ)) ∂(stdGaussian (Torus d (L * n)) N)) := by
  intro G α e he ec Hα χ eG A K site F
  have hα : ∀ z, (α z).im = 0 :=
    baseSector_bgMult_real_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
  have hHim := baseHamiltonian_im_eq_zero G aw (if regimeB then ν else 0) α s hα hsr
  have hKpd : K.PosDef :=
    (baseSector_selected_cut_component_posDef ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
      ∅ hη0 hη s hs hsr).1
  have castF {a b : ℕ} (h : a = b) (x : Torus d b) :
      h ▸ (h.symm ▸ x) = x := by
    cases h
    rfl
  have castR {a b : ℕ} (h : a = b) (x : Torus d a) :
      h.symm ▸ (h ▸ x) = x := by
    cases h
    rfl
  let t : G.Ω 1 ≃ Torus d (L * n) :=
    { toFun := fun z => baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))
      invFun := site
      left_inv := by intro z; apply Subtype.ext; exact castR (baseSector_side L n) z.1
      right_inv := fun x => castF (baseSector_side L n) x }
  obtain ⟨Hs, hHs, hmat⟩ := exists_hessian_chart_of_real_baseOp t e
    (baseHamiltonian G aw (if regimeB then ν else 0) α s) hHim
  let B := Pi.basis (fun _ : Torus d (L * n) =>
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  let ρ := Equiv.prodCongr t (Equiv.refl (Fin N))
  let σ := Equiv.sigmaEquivProd (Torus d (L * n)) (Fin N)
  have hAK : K.map (algebraMap ℝ ℂ) = A :=
    (baseSector_selected_cut_real_matrix ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp s hsr).2
  have hrei : Matrix.reindex ρ ρ A = baseOp N (fun x i => ((e x i : ℝ) : ℂ))
      (fun x y => baseHamiltonian G aw (if regimeB then ν else 0) α s
        (site x) (site y)) := by
    have hr := baseOp_reindex_real t eG
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    dsimp only at hr
    change Matrix.reindex ρ ρ A = _ at hr
    rw [hr]
    congr 1
    funext x i
    change (((e (t (t.symm x)) i : ℝ)) : ℂ) = ((e x i : ℝ) : ℂ)
    rw [Equiv.apply_symm_apply]
  have hKmat : Matrix.reindex σ σ (LinearMap.toMatrix B B (gaussForm e Hs)) =
      Matrix.reindex ρ ρ K := by
    apply Matrix.map_injective (algebraMap ℝ ℂ).injective
    refine hmat.trans (hrei.symm.trans ?_)
    rw [← hAK]
    ext p q
    simp [Matrix.reindex_apply]
  have hKphys : (LinearMap.toMatrix B B (gaussForm e Hs)).PosDef := by
    have h1 : (Matrix.reindex ρ ρ K).PosDef := hKpd.submatrix ρ.symm.injective
    have h2 : LinearMap.toMatrix B B (gaussForm e Hs) =
        (Matrix.reindex σ σ (LinearMap.toMatrix B B (gaussForm e Hs))).submatrix σ σ := by
      ext p q
      simp [Matrix.reindex_apply]
    rw [h2, hKmat]
    exact h1.submatrix σ.injective
  have hdet : LinearMap.det (gaussForm e Hs) = K.det := by
    rw [← LinearMap.det_toMatrix B, ← Matrix.det_reindex_self σ, hKmat,
      Matrix.det_reindex_self]
  have hsq : Real.sqrt (LinearMap.det (gaussForm e Hs))⁻¹ = (pdSqrtInv K).det := by
    rw [hdet, ← pdSqrtInv_det_sq hKpd, Real.sqrt_sq (pdSqrtInv_det_pos hKpd).le]
  have hcoord (x : Torus d (L * n)) (i : Fin N) :
      Measurable (fun v : (x : Torus d (L * n)) → perp (e x) =>
        (((v x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) := by
    fun_prop
  have hq (Hm : Matrix (G.Ω 1) (G.Ω 1) ℂ) :
      Measurable (fun v : (x : Torus d (L * n)) → perp (e x) =>
        (1 / 2 : ℂ) * pair G (fun p : G.Ω 1 × Fin N =>
          (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
            (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
          (liftOp N Hm *ᵥ fun p : G.Ω 1 × Fin N =>
            (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
              (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))) := by
    refine Measurable.const_mul ?_ _
    unfold pair
    refine Finset.measurable_sum _ fun p _ => (hcoord _ _).mul ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun p' _ => measurable_const.mul (hcoord _ _)
  have hF : Measurable F := by
    let V := (x : Torus d (L * n)) → perp (e x)
    let W : V → Config (Torus d (L * n)) N := fun v x => (v x : EuclideanSpace ℝ (Fin N))
    let Φ : V → CfgT d N L n := fun v => chartMapPi e he ((Real.sqrt β)⁻¹ • v)
    let Z : V → Config (Torus d (L * n)) N := fun v => chartShift β e (W v)
    let Mass : V → ℝ := fun v => β * (ν - (if regimeB then ν else 0)) / 2 *
      ∑ x : Torus d (L * n), ‖(Φ v x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
    let Source : V → ℂ := fun v => ∑ x : Torus d (L * n), ∑ i : Fin N,
      g x i * (((W v x + Z v x) i : ℝ) : ℂ)
    let Cross : V → ℝ := fun v => cinner (W v) (Hα (Z v))
    let Zquad : V → ℝ := fun v => cinner (Z v) (Hα (Z v))
    have hχ : Measurable χ := measurable_baseSectorCubeProduct regimeB ν δ₀ h θ
    have hHα : Measurable Hα :=
      (LinearMap.continuous_of_finiteDimensional Hα).measurable
    have hW : Measurable W := by
      refine measurable_pi_iff.mpr fun x => ?_
      fun_prop
    have hΦ : Measurable Φ := by
      dsimp only [Φ]
      fun_prop
    have hZ : Measurable Z := (measurable_chartShift β e).comp hW
    have hMass : Measurable Mass := by
      dsimp only [Mass]
      fun_prop
    have hSource : Measurable Source := by
      dsimp only [Source]
      fun_prop
    have hCross : Measurable Cross := by
      dsimp only [Cross, cinner]
      fun_prop
    have hZquad : Measurable Zquad := by
      dsimp only [Zquad, cinner]
      fun_prop
    let Qt : (FineBond d L (1 * n) → ℂ) → V → ℂ := fun t v =>
      (1 / 2 : ℂ) * pair G (fun p : G.Ω 1 × Fin N =>
        (((W v) (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
        (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α t) *ᵥ
          fun p : G.Ω 1 × Fin N =>
            (((W v) (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
    have hQt (t : FineBond d L (1 * n) → ℂ) : Measurable (Qt t) := hq _
    change Measurable (fun v : V =>
      ((chartJac β (W v) : ℝ) : ℂ) *
        ((χ (Φ v) : ℂ) * ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) * Complex.exp (
          -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((e x) i : ℝ) : ℂ)) +
          (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Source v -
          (((Cross v + (1 / 2) * Zquad v + Mass v : ℝ) : ℂ) +
            (Qt (fun _ => 1) v - Qt s v)))))
    refine (Complex.measurable_ofReal.comp ((measurable_chartJac β).comp hW)).mul ?_
    refine ((Complex.measurable_ofReal.comp (hχ.comp hΦ)).mul measurable_const).mul ?_
    apply Complex.measurable_exp.comp
    refine Measurable.sub ((measurable_const.add measurable_const).add
      (measurable_const.mul hSource)) ?_
    exact (Complex.measurable_ofReal.comp ((hCross.add (hZquad.const_mul _)).add hMass)).add
      ((hQt _).sub (hQt _))
  obtain ⟨R, hRR, hRs, hdetR, hnorm⟩ :=
    integral_tangent_gaussian_of_posDef e he Hs hKphys F hF
  refine ⟨hKpd, Hs, hHs, hmat, R, hRR, hRs, hdetR.trans hsq, ?_⟩
  rw [baseSectorChartIntegral_eq_cut_gaussian hβ a₀ ν δ₀ ϱ aw ha regimeB hδ
    h hh H hΛ1 g θ s]
  apply congrArg (fun z : ℂ =>
    ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) • z)
  rw [hsq] at hnorm
  rw [← hnorm]
  apply integral_congr_ae
  filter_upwards [] with v
  dsimp only [F]
  rw [Complex.ofReal_exp]
  have hqs : (1 / 2 : ℂ) * pair G (fun p : G.Ω 1 × Fin N =>
      (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
        (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
      (liftOp N (baseHamiltonian G aw (if regimeB then ν else 0) α s) *ᵥ
        fun p : G.Ω 1 × Fin N =>
          (((fun x => (v x : EuclideanSpace ℝ (Fin N))) (baseSector_side L n ▸
            (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * ((cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (Hs (fun x => (v x : EuclideanSpace ℝ (Fin N)))) : ℝ) : ℂ) := by
    congr 1
    exact pair_liftOp_eq_cinner t (baseHamiltonian G aw (if regimeB then ν else 0) α s)
      hHim Hs hHs (fun x => (v x : EuclideanSpace ℝ (Fin N)))
  have hexp : ∀ b c s0 s1 R : ℂ, Complex.exp (b - c + s0 + s1 - R) =
      Complex.exp (-c) * Complex.exp (b + s0 + s1 - R) := by
    intro b c s0 s1 R
    rw [← Complex.exp_add]
    congr 1
    ring
  have hc : Complex.exp (((-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
      (Hs (fun x => (v x : EuclideanSpace ℝ (Fin N)))) : ℝ)) : ℂ) =
      Complex.exp (-((1 / 2 : ℂ) * ((cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (Hs (fun x => (v x : EuclideanSpace ℝ (Fin N)))) : ℝ) : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hqs, hexp, hc]
  ring


variable [NeZero N]

/-- Combination of the normalized cut chart integral with the factorization of the
Gaussian normalization over a first-block component and its complement. -/
theorem baseSectorChartIntegral_eq_cut_normalized_factorization
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0)
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
      (N₀ := 1 * n) (k := 1) ϱ) U s)
    (hsr : ∀ b ∈ baseCutBonds (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ), (s b).im = 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let eG : G.Ω 1 → Fin N → ℝ := fun z i =>
      (baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (z : Torus d (1 * n * L ^ 1))) i : ℝ)
    let A := baseOp N (fun z i => (eG z i : ℂ))
      (baseHamiltonian G aw (if regimeB then ν else 0) α s)
    let K := A.map Complex.re
    let P : G.Ω 1 × Fin N → Prop := fun p =>
      (p.1 : Torus d (1 * n * L ^ 1)) ∈ U
    let I := {p : G.Ω 1 × Fin N // P p}
    let J := {p : G.Ω 1 × Fin N // ¬ P p}
    let A_U : Matrix I I ℂ := A.submatrix Subtype.val Subtype.val
    let A_V : Matrix J J ℂ := A.submatrix Subtype.val Subtype.val
    let K_U := A_U.map Complex.re
    let K_V := A_V.map Complex.re
    let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
      let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
      let z := chartShift β e w
      let W : G.Ω 1 × Fin N → ℂ := fun p =>
        (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
      let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
        (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
          (if regimeB then ν else 0) α t) *ᵥ W)
      let M := β * (ν - (if regimeB then ν else 0)) / 2 *
        ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
      ((chartJac β w : ℝ) : ℂ) *
        ((χ φ : ℂ) *
          ((∏ _y : Torus d n,
            ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
              ((N : ℝ) / 2) : ℝ) : ℂ) *
          Complex.exp (
            -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
              (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
            (∑ x : Torus d (L * n), ∑ i : Fin N,
              g x i * (((e x) i : ℝ) : ℂ)) +
            (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              (∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((w x + z x) i : ℝ) : ℂ)) -
            (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
              (q (fun _ => 1) - q s))))
    (pdSqrtInv K).det = (pdSqrtInv K_U).det * (pdSqrtInv K_V).det ∧
    Complex.exp (-(1 / 2) * (logMat A).trace) = (((pdSqrtInv K).det : ℝ) : ℂ) ∧
    ∃ R : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N,
      baseChartIntegral d N L n β a₀ ν h g θ χ e he =
        ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) *
            Fintype.card (Torus d (L * n)) / 2) *
            ((pdSqrtInv K_U).det * (pdSqrtInv K_V).det) : ℝ) : ℂ) *
            ∫ ψ, F (tangentProj e he (R ψ)) ∂(stdGaussian (Torus d (L * n)) N)) := by
  intro G α e he ec Hα χ eG A K P I J A_U A_V K_U K_V F
  have h1 := baseSectorChartIntegral_eq_cut_normalized hβ a₀ ν δ₀ ϱ aw ha regimeB hδ
    h hh H hΛ1 g θ φ₀ hp hη0 hη s hs hsr
  have h2 := baseSector_selected_cut_gaussian_factorization ϱ aw regimeB ν δ₀ hδ h hh H
    hΛ1 θ φ₀ hp U hU hU0 hUc hη0 hη s hs hz hsr
  dsimp only at h1 h2
  obtain ⟨-, -, hd, hexpA, -, -⟩ := h2
  obtain ⟨-, Hs, -, -, R, -, -, -, hint⟩ := h1
  refine ⟨hd, hexpA, R, ?_⟩
  rw [hd] at hint
  exact hint

end Physical

end Balaban.LargeField
