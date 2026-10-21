/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCore
public import Balaban.LargeField.Base.BaseFirstCutPositive
public import Balaban.LargeField.Base.ChordQuadratic
public import Balaban.Background.BgFieldTwoTorusEquiv

/-!
# The chart Gaussian integral over the sites of a generating set

For a generating set `G` at the first step, data `D` supported on a record (the spin support
`BaseSpinSupport`), the background `e = Re bgField` is a unit field, the multiplier `α` is real, and
the action of `G` has the exact chord expansion about `e` with the real Hessian of the Dirichlet
operator `H₀ + diag α`.  The Gaussian form is positive definite.  The chart Gaussian core
`chartGaussian_core` therefore applies to the spins on `G.Ω 1` (the record's good region), with all
other spins entering through the data `D`:

* `compHess`: the componentwise real Hessian of a real matrix on `G.Ω 1`;
* `pair_liftOp_eq_cinner`: the complex bilinear Dirichlet form of real fields is the real pairing;
* `baseNative_chartGaussian`: the chart Gaussian integral for the action of `G`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

noncomputable section

section Hessian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The componentwise real Hessian** of a real matrix `A` on `ι`:
`(H u)_x = ∑_y A x y u_y` in each of the `N` components. -/
def compHess (A : Matrix ι ι ℝ) : Config ι N →ₗ[ℝ] Config ι N where
  toFun u := fun x => WithLp.toLp 2 (fun i : Fin N => ∑ y, A x y * (u y i : ℝ))
  map_add' u v := by
    funext x
    ext i
    simp only [Pi.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    funext x
    ext i
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring

omit [DecidableEq ι] in
theorem compHess_apply (A : Matrix ι ι ℝ) (u : Config ι N) (x : ι) (i : Fin N) :
    (compHess A u x i : ℝ) = ∑ y, A x y * (u y i : ℝ) := rfl

omit [DecidableEq ι] in
/-- The componentwise Hessian of a symmetric matrix is symmetric. -/
theorem compHess_symmetric {A : Matrix ι ι ℝ} (hA : A.IsSymm) (u v : Config ι N) :
    cinner u (compHess A v) = cinner (compHess A u) v := by
  rw [cinner_components, cinner_components]
  simp only [compHess_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ x, ∑ y, ∑ i : Fin N, (u x i : ℝ) * (A x y * (v y i : ℝ)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ y, ∑ x, ∑ i : Fin N, (u x i : ℝ) * (A x y * (v y i : ℝ)) := Finset.sum_comm
    _ = ∑ y, ∑ i : Fin N, ∑ x, (A y x * (u x i : ℝ)) * (v y i : ℝ) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
        rw [← hA.apply y x]
        ring
    _ = _ := rfl

end Hessian

section Generating

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)

/-- A real multiplier gives a real Dirichlet operator. -/
theorem dirichletOperator_im_eq_zero (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, (α x).im = 0) (x y : G.Ω 1) : (dirichletOperator G a ν α x y).im = 0 := by
  simp only [dirichletOperator, Matrix.add_apply, Green.restrictOp,
    Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hα]

/-- **The complex bilinear form of real fields is the real pairing**: for a matrix on `G.Ω 1`
with real entries the pairing of `pair` is the real pairing against the componentwise Hessian. -/
theorem pair_liftOp_eq_cinner (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (hA : ∀ x y, (A x y).im = 0)
    (u v : Config (G.Ω 1) N) :
    pair G (fun p : G.Ω 1 × Fin N => (((u p.1 p.2 : ℝ)) : ℂ))
      (liftOp N A *ᵥ fun p : G.Ω 1 × Fin N => (((v p.1 p.2 : ℝ)) : ℂ)) =
      ((cinner u (compHess (A.map Complex.re) v) : ℝ) : ℂ) := by
  unfold pair
  rw [Fintype.sum_prod_type, cinner_components]
  push_cast
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [liftOp_mulVec_apply, compHess_apply]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have : A x y = (((A x y).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hA x y)
  rw [Matrix.map_apply, ← this]

/-- A point of the product of spheres is a real unit field of the action. -/
theorem isRealUnitField_of_sphere (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    IsRealUnitField G (fun p : G.Ω 1 × Fin N =>
      (((ψ p.1 : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) := by
  intro x
  refine ⟨fun i => by simp, ?_⟩
  have hn : ‖(ψ x : EuclideanSpace ℝ (Fin N))‖ = 1 := mem_sphere_zero_iff_norm.mp (ψ x).property
  have hs := EuclideanSpace.norm_sq_eq (ψ x : EuclideanSpace ℝ (Fin N))
  simp only [Real.norm_eq_abs, sq_abs] at hs
  calc _ = ∑ i, ((ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ‖(ψ x : EuclideanSpace ℝ (Fin N))‖ ^ 2 := hs.symm
    _ = 1 := by rw [hn]; norm_num

/-- The action is continuous in the field. -/
theorem continuous_action (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) :
    Continuous (fun φ : G.Ω 1 × Fin N → ℂ => action G a ν D φ) := by
  have hsv : ∀ y i, Continuous fun φ : G.Ω 1 × Fin N → ℂ => svec G φ y i := by
    intro y i
    unfold svec zeroExt
    split_ifs <;> fun_prop
  have hba : ∀ x i, Continuous fun φ : G.Ω 1 × Fin N → ℂ => blockAvg G φ x i := by
    intro x i
    unfold blockAvg
    exact continuous_const.mul (continuous_finsetSum _ fun y _ => hsv y i)
  have hbar : ∀ x i, Continuous fun φ : G.Ω 1 × Fin N → ℂ => barField G D.Ψ φ x i := by
    intro x i
    unfold barField
    by_cases hx : x ∈ G.Ω 1
    · simp only [hx, dite_true]; fun_prop
    · simp only [hx, dite_false]; fun_prop
  unfold action
  refine ((continuous_const.mul (continuous_finsetSum _ fun x _ => continuous_const.mul
    (continuous_finsetSum _ fun i _ => ?_))).add
    (continuous_const.mul (continuous_finsetSum _ fun x _ =>
      continuous_finsetSum _ fun μ _ => ?_))).add
    (continuous_const.mul (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ => ?_))
  · exact ((continuous_const.sub (hba x i)).norm).pow 2
  · by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      exact continuous_finsetSum _ fun i _ =>
        (((hbar _ i).sub (hbar x i)).norm).pow 2
    · simp only [hc, ↓reduceIte]; exact continuous_const
  · have : Continuous fun φ : G.Ω 1 × Fin N → ℂ => φ (x, i) := continuous_apply _
    exact ((this.sub continuous_const).norm).pow 2

variable {a : ℕ → ℝ} {ν δ₀ : ℝ}

/-- **The facts about the background of record-supported data**: the data are real, the background
is a real unit field solving the Euler–Lagrange system with the multiplier `bgMult`, and the
multiplier is real. -/
theorem bgData_facts {φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ} {h : Fin N → ℝ} {D : BgData G N}
    (H : BgHyp d L 1 ϱ a ν) (S : BaseSpinSupport G ν δ₀ φ h D)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N) :
    D.IsReal ∧ IsRealUnitField G (bgField G a ν D) ∧
      IsEL G a ν D (bgField G a ν D) (bgMult G a ν D) ∧ ∀ x, (bgMult G a ν D x).im = 0 := by
  have hU := baseFirstCut_inUnionDomain G a φ h D H S hΛ1
  obtain ⟨δ, hδ0, hδc, hDδ⟩ := hU
  have hth := theorem71 (G := G) H ⟨δ, hδ0, hδc, hDδ⟩
  exact ⟨isReal_of_inDomainR hDδ, hth.2.1, hth.2.2.1.1,
    baseFirstCut_multiplier_real G a φ h D H S hΛ1⟩

variable (a ν) in
/-- **The background centre** `e = Re bgField` as a configuration on `G.Ω 1`. -/
def bgCenter (D : BgData G N) : Config (G.Ω 1) N :=
  fun x => WithLp.toLp 2 (fun i : Fin N => (bgField G a ν D (x, i)).re)

variable (a ν) in
/-- **The real Hessian** of the chord expansion: the real part of the Dirichlet operator with the
background multiplier, acting componentwise. -/
def bgHess (D : BgData G N) : Config (G.Ω 1) N →ₗ[ℝ] Config (G.Ω 1) N :=
  compHess ((dirichletOperator G a ν (bgMult G a ν D)).map Complex.re)

/-- The real Hessian is symmetric. -/
theorem bgHess_symmetric (D : BgData G N) (u v : Config (G.Ω 1) N) :
    cinner u (bgHess G a ν D v) = cinner (bgHess G a ν D u) v := by
  refine compHess_symmetric ?_ u v
  ext x y
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [← baseHamiltonian_one G a ν (bgMult G a ν D)]
  rw [baseHamiltonian_symm G a ν (bgMult G a ν D) (fun _ => 1) y x]

/-- The background centre is a field of unit vectors. -/
theorem bgCenter_unit (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ) (D : BgData G N)
    (S : BaseSpinSupport G ν δ₀ φ h D) (H : BgHyp d L 1 ϱ a ν)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4) (x : G.Ω 1) :
    ‖bgCenter G a ν D x‖ = 1 := by
  have hs := (spins_near_background (G := G) H S hΛ1 hΛ2 x).1
  have hn : ‖bgCenter G a ν D x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs, sq_abs, bgCenter] using hs
  nlinarith [norm_nonneg (bgCenter G a ν D x)]

/-- **The chord expansion of the action about the background centre**: for every field of unit
spins `ψ` on `G.Ω 1`, `A(ψ) - A(e) = ½ ⟨ψ - e, H (ψ - e)⟩` with the real Hessian `H`. -/
theorem action_sub_eq_bgHess (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    (D : BgData G N) (S : BaseSpinSupport G ν δ₀ φ h D) (H : BgHyp d L 1 ϱ a ν)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (he : ∀ x, ‖bgCenter G a ν D x‖ = 1)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    action G a ν D (fun p : G.Ω 1 × Fin N => (((ψ p.1 : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) -
      action G a ν D (fun p : G.Ω 1 × Fin N =>
        ((((⟨bgCenter G a ν D p.1, mem_sphere_zero_iff_norm.mpr (he p.1)⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : EuclideanSpace ℝ (Fin N)) p.2 :
            ℝ) : ℂ)) =
    (1 / 2) * cinner (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - bgCenter G a ν D x)
      (bgHess G a ν D (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - bgCenter G a ν D x)) := by
  obtain ⟨hreal, hunit, hEL, hαre⟩ := bgData_facts G H S hΛ1
  have hbg : bgField G a ν D = fun p : G.Ω 1 × Fin N => ((bgCenter G a ν D p.1 p.2 : ℝ) : ℂ) := by
    funext p
    exact Complex.ext rfl (by simpa using (hunit p.1).1 p.2)
  have hch := action_sub_eq_chord_quadratic (a := a) (ν := ν) D hreal hEL hunit
    (isRealUnitField_of_sphere G ψ)
  rw [hbg] at hch
  have hdiff : (fun p : G.Ω 1 × Fin N => (((ψ p.1 : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) -
      (fun p : G.Ω 1 × Fin N => ((bgCenter G a ν D p.1 p.2 : ℝ) : ℂ)) =
      fun p : G.Ω 1 × Fin N => ((((fun x => (ψ x : EuclideanSpace ℝ (Fin N)) -
        bgCenter G a ν D x) p.1 p.2 : ℝ)) : ℂ) := by
    funext p
    simp
  rw [hdiff, pair_liftOp_eq_cinner G _ (dirichletOperator_im_eq_zero G a ν _ hαre)
    (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - bgCenter G a ν D x)
    (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - bgCenter G a ν D x)] at hch
  have : ((action G a ν D (fun p : G.Ω 1 × Fin N =>
      (((ψ p.1 : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) -
      action G a ν D (fun p : G.Ω 1 × Fin N => ((bgCenter G a ν D p.1 p.2 : ℝ) : ℂ)) : ℝ) : ℂ) =
      (((1 / 2) * cinner (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - bgCenter G a ν D x)
        (bgHess G a ν D (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - bgCenter G a ν D x)) : ℝ) :
          ℂ) := by
    rw [hch]; push_cast; rfl
  exact_mod_cast this

/-- **The Gaussian form of the record-supported background is positive definite.** -/
theorem bgHess_gaussForm_posDef (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    (D : BgData G N) (S : BaseSpinSupport G ν δ₀ φ h D) (H : BgHyp d L 1 ϱ a ν)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4) :
    (LinearMap.toMatrix
      (Pi.basis (fun _ : G.Ω 1 => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : G.Ω 1 => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm (bgCenter G a ν D) (bgHess G a ν D))).PosDef := by
  obtain ⟨hreal, hunit, hEL, hαre⟩ := bgData_facts G H S hΛ1
  have hs : (fun _ : FineBond d L N₀ => (1 : ℂ)) ∈ baseParamNbhd G 0 := fun b _ =>
    ⟨1, zero_le_one, le_rfl, by simp⟩
  have hsr : ∀ b ∈ baseCutBonds G, ((fun _ : FineBond d L N₀ => (1 : ℂ)) b).im = 0 :=
    fun _ _ => by simp
  have hpd := (baseFirstCut_posDef_of_spinSupport G a φ h D H S hΛ1 hΛ2 _ hs hsr
    (fun _ => True)).1
  dsimp only at hpd
  let B := Pi.basis (fun _ : G.Ω 1 => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis)
  let σ := Equiv.sigmaEquivProd (G.Ω 1) (Fin N)
  have hk := gaussForm_toMatrix_baseOp (bgCenter G a ν D) (bgHess G a ν D)
    ((dirichletOperator G a ν (bgMult G a ν D)).map Complex.re) (fun u x i => compHess_apply _ u x i)
  have hD : ((dirichletOperator G a ν (bgMult G a ν D)).map Complex.re).map
      (algebraMap ℝ ℂ) = dirichletOperator G a ν (bgMult G a ν D) := by
    ext x y
    simp only [Matrix.map_apply]
    exact (Complex.ext (by simp) (by simpa using dirichletOperator_im_eq_zero G a ν _ hαre x y)).symm
  rw [hD, ← baseHamiltonian_one G a ν (bgMult G a ν D)] at hk
  set K := LinearMap.toMatrix B B (gaussForm (bgCenter G a ν D) (bgHess G a ν D)) with hKdef
  have hreK : Matrix.reindex σ σ K = (baseOp N (fun z i => ((bgCenter G a ν D z i : ℝ) : ℂ))
      (baseHamiltonian G a ν (bgMult G a ν D) (fun _ => 1))).map Complex.re := by
    have hmap : ∀ M : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℝ,
        (M.map (algebraMap ℝ ℂ)).map Complex.re = M := fun M => by ext p q; simp
    rw [← hmap (Matrix.reindex σ σ K), hk]
  have hpd' : (Matrix.reindex σ σ K).PosDef := by
    rw [hreK]
    exact hpd
  have := hpd'.submatrix σ.injective
  simpa [Matrix.reindex_apply, Matrix.submatrix_submatrix] using this

/-- **The spin field of a point of the product of spheres**, as a field on `G.Ω 1 × Fin N`. -/
def spinField (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    G.Ω 1 × Fin N → ℂ := fun p => (((ψ p.1 : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)

theorem continuous_action_spinField (D : BgData G N) :
    Continuous (fun ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 =>
      action G a ν D (spinField G ψ)) := by
  refine (continuous_action G a ν D).comp ?_
  refine continuous_pi fun p => ?_
  have : Continuous fun ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 =>
      ((ψ p.1 : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) := by fun_prop
  exact Complex.continuous_ofReal.comp this

/-- **The chart Gaussian integral over the sites of a generating set.**  For record-supported data
`D` of `G` (the spin support `S`), a cutoff `χ` supported in the hemispheres around the background
centre, a constant `K0`, a regime-A mass coefficient `m` and a complex source `g`, the integral of
`χ K0 exp(-β A_G(ψ) - m ∑ ‖ψ_x - h‖² + ⟨g, ψ⟩)` over the spins of `G.Ω 1` is the Gaussian
prefactor times the standard Gaussian integral of the remainder `chartGaussRem`. -/
theorem baseNative_chartGaussian {β : ℝ} (hβ : 0 < β) (m : ℝ)
    (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ) (D : BgData G N)
    (S : BaseSpinSupport G ν δ₀ φ h D) (H : BgHyp d L 1 ϱ a ν)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (g : G.Ω 1 → Fin N → ℂ) (K0 : ℂ)
    (χ : (G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℝ) (hχ : Measurable χ)
    (hχ1 : ∀ ψ, |χ ψ| ≤ 1)
    (hχs : ∀ ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∃ x, ¬ 0 < inner ℝ (bgCenter G a ν D x) (ψ x : EuclideanSpace ℝ (Fin N))) → χ ψ = 0) :
    ∃ R : Config (G.Ω 1) N ≃ₗ[ℝ] Config (G.Ω 1) N,
      (∀ w, gaussForm (bgCenter G a ν D) (bgHess G a ν D) (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config (G.Ω 1) N →ₗ[ℝ] Config (G.Ω 1) N) =
        Real.sqrt (LinearMap.det (gaussForm (bgCenter G a ν D) (bgHess G a ν D)))⁻¹ ∧
      ∫ ψ, chartGaussDensity β m (WithLp.toLp 2 h) g K0 χ
          (fun ψ => action G a ν D (spinField G ψ)) ψ
          ∂(Measure.pi fun _ : G.Ω 1 => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
        ((Real.sqrt β)⁻¹ ^ (Fintype.card (G.Ω 1) * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card (G.Ω 1) / 2) *
            Real.sqrt (LinearMap.det (gaussForm (bgCenter G a ν D) (bgHess G a ν D)))⁻¹ : ℝ) : ℂ) *
            ∫ ψ, chartGaussRem β m (bgCenter G a ν D) (bgCenter_unit G φ h D S H hΛ1 hΛ2)
              (bgHess G a ν D) (WithLp.toLp 2 h) g K0 χ
              (action G a ν D (fun p : G.Ω 1 × Fin N => ((bgCenter G a ν D p.1 p.2 : ℝ) : ℂ)))
              (tangentProj (bgCenter G a ν D) (bgCenter_unit G φ h D S H hΛ1 hΛ2) (R ψ))
              ∂(stdGaussian (G.Ω 1) N)) := by
  have he := bgCenter_unit G φ h D S H hΛ1 hΛ2
  exact chartGaussian_core hβ m (bgCenter G a ν D) he (bgHess G a ν D)
    (bgHess_symmetric G D) (bgHess_gaussForm_posDef G φ h D S H hΛ1 hΛ2) (WithLp.toLp 2 h) g K0
    χ hχ hχ1 hχs (fun ψ => action G a ν D (spinField G ψ)) (continuous_action_spinField G D)
    (fun x => ⟨bgCenter G a ν D x, mem_sphere_zero_iff_norm.mpr (he x)⟩)
    (fun ψ => action_sub_eq_bgHess G φ h D S H hΛ1 he ψ)

end Generating


end

end Balaban.LargeField
