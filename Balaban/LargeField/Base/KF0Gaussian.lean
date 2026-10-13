/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0SqrtReal
public import Balaban.LargeField.Base.BaseChartMeasure
public import Balaban.LargeField.Base.PiLintegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Linarith

/-!
# The Gaussian form of the all-good sector of the one-scale problem (package K2b `KF0ProductCutoff`)

This is the all-good (plus-sheet, product-cutoff) sector only.  Bad blocks, the minus sheet, the
finite-walk expansion, the large-field complement and Root-F are NOT treated here.

On the unit torus `(ℤ/ℓ)^d` let `K_ν = -Δ + ν` (`latticeLaplacian d ℓ ν`), `S = kf0SqrtR d ℓ ν`
its real symmetric positive definite inverse square root (`KF0SqrtReal.lean`; `S * S = K_ν⁻¹`,
entries `≥ 0`, row sums `ν^{-1/2}`), `h` a unit vector of `ℝ^N`, and tangent fields
`ψ : Torus d ℓ → h^⊥`.  `matAct S ψ` is `S` applied to the site index, `(Sψ)_x = ∑_y S(x,y) ψ_y`.

* `lintegral_tangent_gaussian_change`: for every `F ≥ 0` on tangent fields,
  `∫ F(v) exp(-½⟨v,K_ν v⟩) dv = (2π)^{n/2} det(K_ν)^{-(N-1)/2} ∫ F(Sψ) dγ(ψ)`, `n = |Λ|(N-1)`,
  `dv` the Lebesgue measure on `∏_x h^⊥` (`tangentVol`) and `γ = tangentGaussian` the standard
  Gaussian measure `(2π)^{-n/2} exp(-½ ∑_x ‖ψ_x‖²) dψ` on the same space (a probability measure,
  `tangentGaussian_univ`).  The normalizer is `kf0GaussNorm`.  The proof is the linear change of
  variables for Lebesgue measure (`det (matAct S) = det(S)^{N-1}`, `det S = det(K_ν)^{-1/2}`) and
  the identity `⟨Sψ, K_ν Sψ⟩ = ‖ψ‖²` (`tangentQuad_matAct`).
* `lintegral_restrictedIntegrand_gaussian`: applied to the landed chart integrand
  (`lintegral_restrictedIntegrand`): the partition integral restricted to the event that all spins
  lie in the open hemisphere around `h` equals `β^{-n/2} (2π)^{n/2} det(K_ν)^{-(N-1)/2}` times the
  Gaussian expectation of `J_β(Sψ) exp(-R_β(Sψ) + source terms at Sψ)` (`chartInteractionExponent`).
* `kf0_cutoff_spins`, `kf0_cutoff_good_sites` (F.6): if `‖ψ_y‖ ≤ p` for all `y` then
  `‖(Sψ)_x‖ ≤ p ν^{-1/2}` (nonnegative entries and row sums `ν^{-1/2}`); if moreover `2p ≤ √(βν)`
  every spin of the chart configuration of `β^{-1/2} Sψ` lies in the open hemisphere and
  `‖φ_x - h‖ ≤ √2 p/√(βν)`; with `p = b log(βa)`, `r_β = A log(βa)/√β`, `A > √2 b`, `βa > 1`,
  one gets `‖φ_x - h‖ < r_β/√ν` for every site `x`.
* `kf0Gaussian_instance`: `d = 3`, torus `(ℤ/3)^3`, `N = 2`, `ν = 1/8`.

Source: `notes/phase1/KF0.md` (finite-volume Gaussian change of variables), `notes/phase1/
LF-BASE-KF0.md` §F ((F.1)-(F.6), plus sheet).
-/

@[expose] public section

open Matrix MeasureTheory Kronecker

namespace Balaban.LargeField

section MatAct

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup W] [Module ℝ W]

noncomputable def matAct (S : Matrix ι ι ℝ) (ψ : ι → W) : ι → W := fun x => ∑ y, S x y • ψ y

noncomputable def matActL (S : Matrix ι ι ℝ) : (ι → W) →ₗ[ℝ] (ι → W) where
  toFun := matAct S
  map_add' ψ φ := by
    funext x
    simp [matAct, smul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    funext x
    simp [matAct, Finset.smul_sum, smul_comm c]

omit [DecidableEq ι] in
theorem matActL_apply (S : Matrix ι ι ℝ) (ψ : ι → W) : matActL S ψ = matAct S ψ := rfl

omit [DecidableEq ι] in
theorem matAct_mul (A B : Matrix ι ι ℝ) (ψ : ι → W) :
    matAct A (matAct B ψ) = matAct (A * B) ψ := by
  funext x
  simp only [matAct, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem matAct_one (ψ : ι → W) : matAct (1 : Matrix ι ι ℝ) ψ = ψ := by
  funext x
  simp [matAct, Matrix.one_apply]

variable [Module.Free ℝ W] [Module.Finite ℝ W]

theorem det_matActL (S : Matrix ι ι ℝ) :
    LinearMap.det (matActL S : (ι → W) →ₗ[ℝ] (ι → W)) = S.det ^ Module.finrank ℝ W := by
  classical
  let b := Module.finBasis ℝ W
  let B := Pi.basis (fun _ : ι => b)
  rw [← LinearMap.det_toMatrix B]
  have hM : LinearMap.toMatrix B B (matActL S : (ι → W) →ₗ[ℝ] (ι → W)) =
      Matrix.reindex (Equiv.sigmaEquivProd ι (Fin (Module.finrank ℝ W))).symm
        (Equiv.sigmaEquivProd ι (Fin (Module.finrank ℝ W))).symm
        (S ⊗ₖ (1 : Matrix (Fin (Module.finrank ℝ W)) (Fin (Module.finrank ℝ W)) ℝ)) := by
    ext ⟨x, i⟩ ⟨y, j⟩
    simp [LinearMap.toMatrix_apply, B, Pi.basis_apply, matActL_apply, matAct, Matrix.one_apply,
      Matrix.kroneckerMap_apply]
    rw [Finset.sum_eq_single y]
    · simp [Finsupp.single_apply, eq_comm]
    · intro z _ hz
      simp [hz]
    · simp
  rw [hM, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one,
    Fintype.card_fin]


/-- `matAct S` as a linear equivalence, for invertible `S`. -/
noncomputable def matActEquiv (S : Matrix ι ι ℝ) (hS : IsUnit S.det) : (ι → W) ≃ₗ[ℝ] (ι → W) :=
  LinearEquiv.ofLinearMap (matActL S) (matActL S⁻¹)
    (LinearMap.ext fun ψ => by
      rw [LinearMap.comp_apply, matActL_apply, matActL_apply, matAct_mul,
        Matrix.mul_nonsing_inv _ hS, matAct_one]; rfl)
    (LinearMap.ext fun ψ => by
      rw [LinearMap.comp_apply, matActL_apply, matActL_apply, matAct_mul,
        Matrix.nonsing_inv_mul _ hS, matAct_one]; rfl)

omit [Module.Free ℝ W] [Module.Finite ℝ W] in
theorem matActEquiv_apply (S : Matrix ι ι ℝ) (hS : IsUnit S.det) (ψ : ι → W) :
    matActEquiv S hS ψ = matAct S ψ := rfl

theorem det_matActEquiv (S : Matrix ι ι ℝ) (hS : IsUnit S.det) :
    LinearMap.det ((matActEquiv S hS : (ι → W) ≃ₗ[ℝ] (ι → W)) : (ι → W) →ₗ[ℝ] (ι → W)) =
      S.det ^ Module.finrank ℝ W :=
  det_matActL S

end MatAct

/-! ### Tangent fields -/

open SphereChart

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- The Lebesgue measure on the tangent fields `∏_x h^⊥`. -/
noncomputable abbrev tangentVol (d ℓ : ℕ) [NeZero ℓ] (h : EuclideanSpace ℝ (Fin N)) :
    Measure (Torus d ℓ → perp h) :=
  Measure.pi fun _ => (volume : Measure (perp h))

theorem lintegral_matAct {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    (S : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) (hS : IsUnit S.det)
    (f : (Torus d ℓ → perp h) → ENNReal) :
    ∫⁻ v, f v ∂(tangentVol d ℓ h) =
      ENNReal.ofReal |S.det ^ (N - 1)| * ∫⁻ ψ, f (matAct S ψ) ∂(tangentVol d ℓ h) := by
  have := lintegral_eq_ofReal_abs_det_mul (tangentVol d ℓ h) (matActEquiv S hS) f
  rw [det_matActEquiv] at this
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  rw [hr] at this
  exact this


theorem coord_matAct {h : EuclideanSpace ℝ (Fin N)} (S : Matrix (Torus d ℓ) (Torus d ℓ) ℝ)
    (ψ : Torus d ℓ → perp h) (x : Torus d ℓ) (i : Fin N) :
    ((matAct S ψ x : perp h) : EuclideanSpace ℝ (Fin N)) i =
      (S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) x := by
  simp [matAct, Matrix.mulVec, dotProduct]

/-- **The Gaussian quadratic form in the new variables**: if `S` is symmetric with
`S K_ν S = 1` then `⟨Sψ, K_ν Sψ⟩ = ‖ψ‖²` for tangent fields `ψ`. -/
theorem tangentQuad_matAct {h : EuclideanSpace ℝ (Fin N)} {ν : ℝ}
    {S : Matrix (Torus d ℓ) (Torus d ℓ) ℝ} (hSt : Sᵀ = S)
    (hSKS : S * latticeLaplacian d ℓ ν * S = 1) (ψ : Torus d ℓ → perp h) :
    tangentQuad ν (matAct S ψ) = ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2 := by
  have hn : ∀ u : perp h, ‖u‖ ^ 2 = ∑ i : Fin N, ((u : EuclideanSpace ℝ (Fin N)) i) ^ 2 := by
    intro u
    rw [← norm_coe_perp, EuclideanSpace.norm_sq_eq]
    simp
  unfold tangentQuad
  have hcoord : ∀ i : Fin N, (fun x => ((matAct S ψ x : perp h) : EuclideanSpace ℝ (Fin N)) i) =
      S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i := fun i => by
    funext x; exact coord_matAct S ψ x i
  have hq : ∀ i : Fin N, (S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) ⬝ᵥ
      latticeLaplacian d ℓ ν *ᵥ (S *ᵥ fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) =
      ∑ y, (((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i) ^ 2 := by
    intro i
    set w : Torus d ℓ → ℝ := fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i with hw
    have e1 : (S *ᵥ w) ⬝ᵥ latticeLaplacian d ℓ ν *ᵥ (S *ᵥ w) = w ⬝ᵥ (Sᵀ * latticeLaplacian d ℓ ν * S) *ᵥ w := by
      have hT : ∀ u : Torus d ℓ → ℝ, (S *ᵥ w) ⬝ᵥ u = w ⬝ᵥ (Sᵀ *ᵥ u) := fun u => by
        rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
      rw [hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [e1, hSt, hSKS, Matrix.one_mulVec]
    simp [dotProduct, sq, hw]
  simp only [hcoord, hq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => (hn (ψ x)).symm


/-! ### The standard Gaussian on the tangent fields -/

/-- The exponent `n = |Λ| (N - 1)`, the dimension of the tangent fields. -/
abbrev tangentDim (d ℓ N : ℕ) [NeZero ℓ] : ℕ := Fintype.card (Torus d ℓ) * (N - 1)

/-- **The standard Gaussian measure on the tangent fields** `∏_x h^⊥`: the probability measure
`(2π)^{-n/2} exp(-½ ∑_x ‖ψ_x‖²) dψ`, `n = |Λ| (N - 1)`, `dψ` the Lebesgue measure
(`tangentVol`).  It is the product over the sites of the standard Gaussian of `h^⊥`
(`tangentGaussian_univ`: total mass `1`). -/
noncomputable def tangentGaussian (d ℓ : ℕ) [NeZero ℓ] (h : EuclideanSpace ℝ (Fin N)) :
    Measure (Torus d ℓ → perp h) :=
  (tangentVol d ℓ h).withDensity fun ψ =>
    ENNReal.ofReal ((2 * Real.pi) ^ (-(tangentDim d ℓ N : ℝ) / 2) *
      Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2))

theorem lintegral_gauss_perp {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) :
    ∫⁻ u : perp h, ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (((N - 1 : ℕ) : ℝ) / 2)) := by
  have hr : Module.finrank ℝ (perp h) = N - 1 := by
    have := finrank_perp h hh; omega
  have hI := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := perp h) (b := (1 / 2 : ℝ)) (by norm_num)
  rw [hr] at hI
  have hpos : (Real.pi / (1 / 2 : ℝ)) ^ (((N - 1 : ℕ) : ℝ) / 2) = (2 * Real.pi) ^ (((N - 1 : ℕ) : ℝ) / 2) := by
    congr 1; ring
  rw [hpos] at hI
  have hint : Integrable (fun u : perp h => Real.exp (-(1 / 2 : ℝ) * ‖u‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [hI]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun u => (Real.exp_pos _).le), hI]


theorem lintegral_gauss_tangent {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) :
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2))
        ∂(tangentVol d ℓ h) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((tangentDim d ℓ N : ℝ) / 2)) := by
  have e1 : ∀ ψ : Torus d ℓ → perp h,
      ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2)) =
        ∏ x : Torus d ℓ, ENNReal.ofReal (Real.exp (-(1 / 2) * ‖ψ x‖ ^ 2)) := by
    intro ψ
    rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le)]
  simp_rw [e1]
  have hmeas : Measurable fun u : perp h => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
  rw [PiTools.lintegral_fintype_prod_eq_prod (Torus d ℓ)
    (fun _ u => ENNReal.ofReal (Real.exp (-(1 / 2) * ‖u‖ ^ 2))) (fun _ => hmeas)]
  rw [Finset.prod_const, lintegral_gauss_perp hh, Finset.card_univ, ← ENNReal.ofReal_pow
    (Real.rpow_nonneg (by positivity) _), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast
  ring

/-- **The tangent Gaussian is a probability measure.** -/
theorem tangentGaussian_univ {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) :
    tangentGaussian d ℓ h Set.univ = 1 := by
  unfold tangentGaussian
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hc : ∀ ψ : Torus d ℓ → perp h,
      ENNReal.ofReal ((2 * Real.pi) ^ (-(tangentDim d ℓ N : ℝ) / 2) *
        Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(tangentDim d ℓ N : ℝ) / 2)) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2)) := fun ψ =>
    ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gauss_tangent hh,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), ← Real.rpow_add (by positivity)]
  have : -(tangentDim d ℓ N : ℝ) / 2 + (tangentDim d ℓ N : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, ENNReal.ofReal_one]

/-! ### The linear change of variables `v = K_ν^{-1/2} ψ` -/

open Balaban.Green

theorem kf0SqrtR_mul_mul {ν : ℝ} (hν : 0 < ν) :
    kf0SqrtR d ℓ ν * latticeLaplacian d ℓ ν * kf0SqrtR d ℓ ν = 1 := by
  set S := kf0SqrtR d ℓ ν
  set K := latticeLaplacian d ℓ ν
  have hKu : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 (latticeLaplacian_posDef hν).isUnit
  have h1 : S * (S * K) = 1 := by
    rw [← Matrix.mul_assoc, kf0SqrtR_mul_self hν]
    exact Matrix.nonsing_inv_mul K hKu
  have h2 : (S * K) * S = 1 := mul_eq_one_comm.1 h1
  exact h2

theorem det_kf0SqrtR_pow {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    (kf0SqrtR d ℓ ν).det ^ k = (latticeLaplacian d ℓ ν).det ^ (-(k : ℝ) / 2) := by
  have hKpos : 0 < (latticeLaplacian d ℓ ν).det := (latticeLaplacian_posDef hν).det_pos
  have hSpos : 0 < (kf0SqrtR d ℓ ν).det := (kf0SqrtR_posDef hν).det_pos
  have hsq : (kf0SqrtR d ℓ ν).det ^ 2 = ((latticeLaplacian d ℓ ν).det)⁻¹ := by
    have := congrArg Matrix.det (kf0SqrtR_mul_self (d := d) (m := ℓ) hν)
    rw [Matrix.det_mul, Matrix.det_nonsing_inv] at this
    rw [sq, this]
    exact Ring.inverse_eq_inv _
  have h1 : (kf0SqrtR d ℓ ν).det = (latticeLaplacian d ℓ ν).det ^ (-(1 / 2 : ℝ)) := by
    have h2 : ((latticeLaplacian d ℓ ν).det ^ (-(1 / 2 : ℝ))) ^ 2 = ((latticeLaplacian d ℓ ν).det)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
      norm_num
      exact Real.rpow_neg_one _
    have h3 : 0 < (latticeLaplacian d ℓ ν).det ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hKpos _
    nlinarith [sq_nonneg ((kf0SqrtR d ℓ ν).det - (latticeLaplacian d ℓ ν).det ^ (-(1 / 2 : ℝ))),
      sq_nonneg ((kf0SqrtR d ℓ ν).det + (latticeLaplacian d ℓ ν).det ^ (-(1 / 2 : ℝ)))]
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]
  congr 1
  ring


/-- The normalizer of the Gaussian change of variables:
`(2π)^{n/2} det(K_ν)^{-(N-1)/2}`, `n = |Λ|(N-1)`. -/
noncomputable def kf0GaussNorm (d ℓ N : ℕ) [NeZero ℓ] (ν : ℝ) : ℝ :=
  (2 * Real.pi) ^ ((tangentDim d ℓ N : ℝ) / 2) *
    (latticeLaplacian d ℓ ν).det ^ (-((N - 1 : ℕ) : ℝ) / 2)

theorem kf0GaussNorm_pos {ν : ℝ} (hν : 0 < ν) : 0 < kf0GaussNorm d ℓ N ν :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (latticeLaplacian_posDef hν).det_pos _)

/-- **The Gaussian change of variables** `v = K_ν^{-1/2} ψ` (T4).  For `ν > 0`, `|h| = 1` and every
`F ≥ 0` on tangent fields (no measurability needed),
`∫ F(v) exp(-½⟨v, K_ν v⟩) dv = (2π)^{n/2} det(K_ν)^{-(N-1)/2} ∫ F(K_ν^{-1/2} ψ) dγ(ψ)`,
`n = |Λ|(N-1)`, `dv` the Lebesgue measure on `∏_x h^⊥` and `γ = tangentGaussian` the standard
Gaussian on the same space.  `K_ν^{-1/2}` acts on the site index of the tangent field. -/
theorem lintegral_tangent_gaussian_change {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    {ν : ℝ} (hν : 0 < ν) (F : (Torus d ℓ → perp h) → ENNReal) :
    ∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * tangentQuad ν v)) ∂(tangentVol d ℓ h) =
      ENNReal.ofReal (kf0GaussNorm d ℓ N ν) *
        ∫⁻ ψ, F (matAct (kf0SqrtR d ℓ ν) ψ) ∂(tangentGaussian d ℓ h) := by
  set S := kf0SqrtR d ℓ ν with hS
  have hSpos : 0 < S.det := (kf0SqrtR_posDef hν).det_pos
  have hSu : IsUnit S.det := hSpos.ne'.isUnit
  rw [lintegral_matAct hh S hSu]
  have hq : ∀ ψ : Torus d ℓ → perp h,
      F (matAct S ψ) * ENNReal.ofReal (Real.exp (-(1 / 2) * tangentQuad ν (matAct S ψ))) =
      F (matAct S ψ) * ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2)) := by
    intro ψ
    rw [tangentQuad_matAct (kf0SqrtR_transpose ν) (kf0SqrtR_mul_mul hν)]
  simp_rw [hq]
  set c₀ : ℝ := (2 * Real.pi) ^ (-(tangentDim d ℓ N : ℝ) / 2) with hc₀
  have hc₀pos : 0 < c₀ := Real.rpow_pos_of_pos (by positivity) _
  have hγ : ∫⁻ ψ, F (matAct S ψ) ∂(tangentGaussian d ℓ h) =
      ENNReal.ofReal c₀ * ∫⁻ ψ, F (matAct S ψ) *
        ENNReal.ofReal (Real.exp (-(1 / 2) * ∑ x : Torus d ℓ, ‖ψ x‖ ^ 2)) ∂(tangentVol d ℓ h) := by
    unfold tangentGaussian
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ψ => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul hc₀pos.le]
      ring
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact ae_of_all _ fun ψ => ENNReal.ofReal_lt_top
  rw [hγ, ← mul_assoc, ← ENNReal.ofReal_mul (kf0GaussNorm_pos hν).le]
  congr 2
  have h2 : (2 * Real.pi) ^ ((tangentDim d ℓ N : ℝ) / 2) * c₀ = 1 := by
    rw [hc₀, ← Real.rpow_add (by positivity)]
    have : (tangentDim d ℓ N : ℝ) / 2 + -(tangentDim d ℓ N : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [abs_of_pos (pow_pos hSpos _), det_kf0SqrtR_pow hν, kf0GaussNorm, mul_right_comm, h2, one_mul]

/-! ### The chart integrand as a Gaussian expectation -/

/-- The exponent of the chart integrand without the Gaussian part:
`-R_β(v) + ⟨g,h⟩ + β^{-1/2}⟨g,v⟩ + β^{-1/2} ∑_x (g_x·h) w_x`. -/
noncomputable def chartInteractionExponent (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (v : Torus d ℓ → perp h) : ℝ :=
  -chartRemainder β ν v + sourceConst g h + (Real.sqrt β)⁻¹ * sourceTangent g v +
    (Real.sqrt β)⁻¹ * sourceNormal g h β v

theorem chartActionExponent_eq (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) (v : Torus d ℓ → perp h) :
    chartActionExponent β ν h g v =
      -(1 / 2) * tangentQuad ν v + chartInteractionExponent β ν h g v := by
  unfold chartActionExponent chartInteractionExponent
  rw [tangentEnergy_eq]
  ring

/-- **The restricted partition integral as a Gaussian expectation** (T4).  For `β > 0`, `ν > 0`,
`|h| = 1` and a real source `g`:
`∫ 1_{E_h} exp(-βH₀ + ⟨g,φ⟩) d(aprioriMeasure) =
  β^{-n/2} · (2π)^{n/2} det(K_ν)^{-(N-1)/2} · E_γ[ J_β(Sψ) exp(-R_β(Sψ) + source terms at Sψ) ]`,
where `n = |Λ|(N-1)`, `S = K_ν^{-1/2}` (`kf0SqrtR`), `γ = tangentGaussian` and `J_β = chartJac`.
This is the all-good sector only: the event `E_h` that all spins lie in the open hemisphere around
`h`; no estimate of the complement, no expansion. -/
theorem lintegral_restrictedIntegrand_gaussian {β : ℝ} (hβ : 0 < β) {ν : ℝ} (hν : 0 < ν)
    {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (g : Torus d ℓ → Fin N → ℝ) :
    ∫⁻ φ, restrictedIntegrand β ν h g φ ∂(aprioriMeasure d N ℓ) =
      ENNReal.ofReal (((Real.sqrt β)⁻¹) ^ (Fintype.card (Torus d ℓ) * (N - 1))) *
        ENNReal.ofReal (kf0GaussNorm d ℓ N ν) *
        ∫⁻ ψ, ENNReal.ofReal (chartJac β (fun x => ((matAct (kf0SqrtR d ℓ ν) ψ x : perp h) :
              EuclideanSpace ℝ (Fin N)))) *
            ENNReal.ofReal (Real.exp (chartInteractionExponent β ν h g
              (matAct (kf0SqrtR d ℓ ν) ψ))) ∂(tangentGaussian d ℓ h) := by
  rw [lintegral_restrictedIntegrand hβ ν hh g, mul_assoc]
  congr 1
  have hF := lintegral_tangent_gaussian_change (d := d) (ℓ := ℓ) hh hν
    (fun v => ENNReal.ofReal (chartJac β (fun x => ((v x : perp h) : EuclideanSpace ℝ (Fin N)))) *
      ENNReal.ofReal (Real.exp (chartInteractionExponent β ν h g v)))
  rw [← hF]
  refine lintegral_congr fun v => ?_
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, chartActionExponent_eq]
  congr 3
  ring

/-! ### The product cutoff controls every spin -/

/-- `‖hemiE ξ - h‖² = 2 (1 - √(1 - ‖ξ‖²)) ≤ 2 ‖ξ‖²` for `‖ξ‖ ≤ 1`, `|h| = 1`. -/
theorem norm_sq_hemiE_sub_le {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (ξ : perp h)
    (hξ : ‖ξ‖ ≤ 1) :
    ‖hemiE h ξ - h‖ ^ 2 = 2 * (1 - Real.sqrt (1 - ‖ξ‖ ^ 2)) ∧
      ‖hemiE h ξ - h‖ ^ 2 ≤ 2 * ‖ξ‖ ^ 2 := by
  have e : hemiE h ξ - h = (Real.sqrt (1 - ‖ξ‖ ^ 2) - 1) • h + (ξ : EuclideanSpace ℝ (Fin N)) := by
    unfold hemiE; module
  have hs : Real.sqrt (1 - ‖ξ‖ ^ 2) ^ 2 = 1 - ‖ξ‖ ^ 2 :=
    Real.sq_sqrt (by nlinarith [norm_nonneg ξ])
  have h1 : ‖hemiE h ξ - h‖ ^ 2 = 2 * (1 - Real.sqrt (1 - ‖ξ‖ ^ 2)) := by
    rw [e, norm_sq_smul_add_perp hh]
    nlinarith
  refine ⟨h1, ?_⟩
  rw [h1]
  have := one_sub_sqrt_le (s := ‖ξ‖ ^ 2) (by positivity) (by nlinarith [norm_nonneg ξ])
  linarith

omit [NeZero ℓ] in
/-- **Site estimate.**  If `‖v x‖ < √β`, the spin of the chart configuration of `ξ = β^{-1/2} v`
at `x` lies in the open hemisphere and `‖φ_x - h‖ ≤ √2 ‖v x‖ / √β`. -/
theorem chartCfg_site_bound {β : ℝ} (hβ : 0 < β) {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1)
    (v : Torus d ℓ → perp h) (x : Torus d ℓ) (hx : ‖v x‖ < Real.sqrt β) :
    0 < inner ℝ h ((chartCfg h hh ((Real.sqrt β)⁻¹ • v) x :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : EuclideanSpace ℝ (Fin N)) ∧
      ‖((chartCfg h hh ((Real.sqrt β)⁻¹ • v) x :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : EuclideanSpace ℝ (Fin N)) - h‖ ≤
        Real.sqrt 2 * ‖v x‖ / Real.sqrt β := by
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hlt : ‖((Real.sqrt β)⁻¹ • v) x‖ < 1 := by
    rw [Pi.smul_apply]; exact (norm_inv_sqrt_smul_lt_one_iff hβ (v x)).2 hx
  refine ⟨inner_hemiPt_pos h hh hlt, ?_⟩
  unfold chartCfg
  rw [coe_hemiPt_of_lt h hh hlt]
  have h2 := (norm_sq_hemiE_sub_le hh (((Real.sqrt β)⁻¹ • v) x) hlt.le).2
  have hn : ‖((Real.sqrt β)⁻¹ • v) x‖ = ‖v x‖ / Real.sqrt β := by
    rw [Pi.smul_apply, norm_smul, norm_inv, Real.norm_of_nonneg hsβ.le]; ring
  rw [hn] at h2
  have hr : 0 ≤ Real.sqrt 2 * ‖v x‖ / Real.sqrt β := by positivity
  refine le_of_sq_le_sq ?_ hr
  calc ‖hemiE h (((Real.sqrt β)⁻¹ • v) x) - h‖ ^ 2 ≤ 2 * (‖v x‖ / Real.sqrt β) ^ 2 := h2
    _ = (Real.sqrt 2 * ‖v x‖ / Real.sqrt β) ^ 2 := by
        rw [mul_div_assoc, mul_pow, Real.sq_sqrt (by norm_num)]

/-- A tangent field of the form `K_ν^{-1/2} ψ` with `‖ψ_y‖ ≤ p` for all `y` has `‖v_x‖ ≤ p ν^{-1/2}`
(row sum of the nonnegative matrix `K_ν^{-1/2}`; (F.6)). -/
theorem norm_matAct_kf0SqrtR_le {h : EuclideanSpace ℝ (Fin N)} {ν : ℝ} (hν : 0 < ν) {p : ℝ}
    (ψ : Torus d ℓ → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ p) (x : Torus d ℓ) :
    ‖matAct (kf0SqrtR d ℓ ν) ψ x‖ ≤ p * (Real.sqrt ν)⁻¹ := by
  unfold matAct
  calc ‖∑ y, kf0SqrtR d ℓ ν x y • ψ y‖ ≤ ∑ y, ‖kf0SqrtR d ℓ ν x y • ψ y‖ := norm_sum_le _ _
    _ ≤ ∑ y, kf0SqrtR d ℓ ν x y * p := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (kf0SqrtR_nonneg hν x y)]
        exact mul_le_mul_of_nonneg_left (hψ y) (kf0SqrtR_nonneg hν x y)
    _ = p * (Real.sqrt ν)⁻¹ := by
        rw [← Finset.sum_mul, kf0SqrtR_row_sum hν x, mul_comm]

/-- **The product cutoff on the Gaussian variables controls every spin** (T3, (F.6)).  Let
`ν, β > 0`, `|h| = 1`, `p` with `2p ≤ √(βν)`, and `ψ` a tangent field with `‖ψ_y‖ ≤ p` for all
`y`.  Then for `v = K_ν^{-1/2} ψ`: `‖v_x‖ ≤ p ν^{-1/2} ≤ √β / 2` (so `v` is in the chart domain),
every spin of the chart configuration of `β^{-1/2} v` lies in the open hemisphere and
`‖φ_x - h‖ ≤ √2 p / √(βν)`. -/
theorem kf0_cutoff_spins {β ν p : ℝ} (hβ : 0 < β) (hν : 0 < ν) {h : EuclideanSpace ℝ (Fin N)}
    (hh : ‖h‖ = 1) (hp : 2 * p ≤ Real.sqrt (β * ν)) (ψ : Torus d ℓ → perp h)
    (hψ : ∀ y, ‖ψ y‖ ≤ p) :
    (∀ x, ‖matAct (kf0SqrtR d ℓ ν) ψ x‖ ≤ p * (Real.sqrt ν)⁻¹) ∧
      (∀ x, ‖matAct (kf0SqrtR d ℓ ν) ψ x‖ < Real.sqrt β) ∧
      ∀ x, 0 < inner ℝ h ((chartCfg h hh ((Real.sqrt β)⁻¹ • matAct (kf0SqrtR d ℓ ν) ψ) x :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : EuclideanSpace ℝ (Fin N)) ∧
        ‖((chartCfg h hh ((Real.sqrt β)⁻¹ • matAct (kf0SqrtR d ℓ ν) ψ) x :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : EuclideanSpace ℝ (Fin N)) - h‖ ≤
          Real.sqrt 2 * p / Real.sqrt (β * ν) := by
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsm : Real.sqrt (β * ν) = Real.sqrt β * Real.sqrt ν := Real.sqrt_mul hβ.le ν
  have hv := norm_matAct_kf0SqrtR_le (d := d) (ℓ := ℓ) hν ψ hψ
  have hlt : ∀ x, ‖matAct (kf0SqrtR d ℓ ν) ψ x‖ < Real.sqrt β := by
    intro x
    refine lt_of_le_of_lt (hv x) ?_
    rw [hsm] at hp
    rw [← div_eq_mul_inv, div_lt_iff₀ hsν]
    nlinarith
  refine ⟨hv, hlt, fun x => ⟨(chartCfg_site_bound hβ hh _ x (hlt x)).1, ?_⟩⟩
  refine (chartCfg_site_bound hβ hh _ x (hlt x)).2.trans ?_
  rw [hsm]
  calc Real.sqrt 2 * ‖matAct (kf0SqrtR d ℓ ν) ψ x‖ / Real.sqrt β
      ≤ Real.sqrt 2 * (p * (Real.sqrt ν)⁻¹) / Real.sqrt β := by gcongr; exact hv x
    _ = Real.sqrt 2 * p / (Real.sqrt β * Real.sqrt ν) := by field_simp

/-- **The cutoff `|ψ_y| ≤ b log(βa)` makes every site good** (T3, (F.6)).  With
`p_β = b log(βa)`, `r_β = A log(βa)/√β`, `A > √2 b`, `βa > 1`, and `2 p_β ≤ √(βν)`: every spin of
the chart configuration of `β^{-1/2} K_ν^{-1/2} ψ` satisfies `‖φ_x - h‖ < r_β/√ν`. -/
theorem kf0_cutoff_good_sites {β ν a b A : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) (hβa : 1 < β * a)
    (hA : Real.sqrt 2 * b < A) (hreg : 2 * (b * Real.log (β * a)) ≤ Real.sqrt (β * ν))
    (ψ : Torus d ℓ → perp h) (hψ : ∀ y, ‖ψ y‖ ≤ b * Real.log (β * a)) (x : Torus d ℓ) :
    ‖((chartCfg h hh ((Real.sqrt β)⁻¹ • matAct (kf0SqrtR d ℓ ν) ψ) x :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : EuclideanSpace ℝ (Fin N)) - h‖ <
      (A * Real.log (β * a) / Real.sqrt β) / Real.sqrt ν := by
  have hL : 0 < Real.log (β * a) := Real.log_pos hβa
  have h1 := ((kf0_cutoff_spins (d := d) (ℓ := ℓ) hβ hν hh hreg ψ hψ).2.2 x).2
  refine lt_of_le_of_lt h1 ?_
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  rw [Real.sqrt_mul hβ.le ν, div_div]
  exact div_lt_div_of_pos_right (by nlinarith) (by positivity)

/-- **The Gaussian normalization** (T4 with `F ≡ 1`): `∫ exp(-½⟨v,K_ν v⟩) dv =
(2π)^{n/2} det(K_ν)^{-(N-1)/2}`. -/
theorem lintegral_exp_tangentQuad {h : EuclideanSpace ℝ (Fin N)} (hh : ‖h‖ = 1) {ν : ℝ}
    (hν : 0 < ν) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (-(1 / 2) * tangentQuad ν v)) ∂(tangentVol d ℓ h) =
      ENNReal.ofReal (kf0GaussNorm d ℓ N ν) := by
  have := lintegral_tangent_gaussian_change (d := d) (ℓ := ℓ) hh hν (fun _ => 1)
  simp only [one_mul, lintegral_const, one_mul] at this
  rw [this, tangentGaussian_univ hh, mul_one]

/-! ### Non-vacuity -/

/-- **Instance** (`d = 3`, torus `(ℤ/3)^3`, `N = 2`, `h = e₀` so one tangent direction per site,
`ν = 1/8`): the Gaussian normalization identity holds with a positive explicit normalizer;
the tangent Gaussian is a probability measure; and, with `β = 32`, `a = 1/16` (so `βa = 2`),
`b = 1`, `A = 2 > √2 b`, the regime condition `2 b log(βa) ≤ √(βν) = 2` holds, so every Gaussian
field `ψ` with `‖ψ_y‖ ≤ log 2` for all `y` (for instance `ψ = 0`) gives a configuration all of whose
spins satisfy `‖φ_x - h‖ < r_β/√ν`, `r_β = 2 log 2/√32`. -/
theorem kf0Gaussian_instance :
    let h : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    ∃ hh : ‖h‖ = 1,
      0 < kf0GaussNorm 3 3 2 (1 / 8 : ℝ) ∧
      tangentGaussian 3 3 h Set.univ = 1 ∧
      ∫⁻ v, ENNReal.ofReal (Real.exp (-(1 / 2) * tangentQuad (1 / 8 : ℝ) v))
          ∂(tangentVol 3 3 h) = ENNReal.ofReal (kf0GaussNorm 3 3 2 (1 / 8 : ℝ)) ∧
      ∀ ψ : Torus 3 3 → perp h, (∀ y, ‖ψ y‖ ≤ 1 * Real.log (32 * (1 / 16))) →
        ∀ x, ‖((chartCfg h hh ((Real.sqrt 32)⁻¹ • matAct (kf0SqrtR 3 3 (1 / 8 : ℝ)) ψ) x :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) : EuclideanSpace ℝ (Fin 2)) - h‖ <
          (2 * Real.log (32 * (1 / 16)) / Real.sqrt 32) / Real.sqrt (1 / 8) := by
  intro h
  have hh : ‖h‖ = 1 := by simp [h]
  have hν : (0 : ℝ) < 1 / 8 := by norm_num
  refine ⟨hh, kf0GaussNorm_pos hν, tangentGaussian_univ hh, lintegral_exp_tangentQuad hh hν,
    fun ψ hψ x => ?_⟩
  have hβa : 1 < (32 : ℝ) * (1 / 16) := by norm_num
  have hlog : Real.log (32 * (1 / 16) : ℝ) < 1 := by
    have : (32 * (1 / 16) : ℝ) = 2 := by norm_num
    rw [this]
    have := Real.log_two_lt_d9
    linarith
  have hsq : Real.sqrt ((32 : ℝ) * (1 / 8)) = 2 := by
    rw [show (32 : ℝ) * (1 / 8) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine kf0_cutoff_good_sites (d := 3) (ℓ := 3) (by norm_num) hν hh hβa
    (a := 1 / 16) (b := 1) (A := 2) ?_ ?_ ψ hψ x
  · have : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    linarith
  · rw [hsq]; linarith

end Balaban.LargeField
