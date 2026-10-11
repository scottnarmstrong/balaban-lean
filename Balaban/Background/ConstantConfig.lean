/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ConstantConfigReal
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Constant configurations at `λ = ∞`: complex data
-/

@[expose] public section

open Matrix

namespace Balaban.Background

variable {ι : Type*} [Fintype ι]

/-- Complex blend `w = aψ + νh`. -/
noncomputable def cBlend (a ν : ℝ) (ψ h : ι → ℂ) : ι → ℂ := (a : ℂ) • ψ + (ν : ℂ) • h

/-- Principal square root of the bilinear square `x ⬝ᵥ x`. -/
noncomputable def sqrtDot (x : ι → ℂ) : ℂ := (x ⬝ᵥ x) ^ ((2 : ℂ)⁻¹)

noncomputable def cMinimizer (a ν : ℝ) (ψ h : ι → ℂ) : ι → ℂ :=
  (sqrtDot (cBlend a ν ψ h))⁻¹ • cBlend a ν ψ h

noncomputable def cMultiplier (a ν : ℝ) (ψ h : ι → ℂ) : ℂ :=
  sqrtDot (cBlend a ν ψ h) - a - ν

theorem sqrtDot_sq (x : ι → ℂ) : sqrtDot x ^ 2 = x ⬝ᵥ x := by
  simp [sqrtDot]

theorem re_cpow_half_nonneg (z : ℂ) : 0 ≤ (z ^ ((2 : ℂ)⁻¹)).re := by
  by_cases hz : z = 0
  · subst hz; simp
  · rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
    apply mul_nonneg (Real.exp_pos _).le
    have h1 : (Complex.log z * (2 : ℂ)⁻¹).im = z.arg / 2 := by
      simp [Complex.log_im, div_eq_mul_inv]
    rw [h1]
    apply Real.cos_nonneg_of_mem_Icc
    have := Complex.neg_pi_lt_arg z
    have := Complex.arg_le_pi z
    constructor <;> linarith

theorem re_sqrtDot_nonneg (x : ι → ℂ) : 0 ≤ (sqrtDot x).re := re_cpow_half_nonneg _

/-- Euclidean (`ℓ²`) norm on `ι → ℂ`. -/
noncomputable def cNorm (x : ι → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖

theorem cNorm_sq (x : ι → ℂ) : cNorm x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold cNorm
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem cNorm_nonneg (x : ι → ℂ) : 0 ≤ cNorm x := norm_nonneg _

theorem cNorm_add_le (x y : ι → ℂ) : cNorm (x + y) ≤ cNorm x + cNorm y :=
  norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)

theorem cNorm_sub_le (x y : ι → ℂ) : cNorm (x - y) ≤ cNorm x + cNorm y :=
  norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℂ ι) (WithLp.toLp 2 y)

theorem cNorm_smul (c : ℂ) (x : ι → ℂ) : cNorm (c • x) = ‖c‖ * cNorm x :=
  norm_smul c (WithLp.toLp 2 x : EuclideanSpace ℂ ι)

theorem norm_dotProduct_le (x y : ι → ℂ) : ‖x ⬝ᵥ y‖ ≤ cNorm x * cNorm y := by
  have h1 : ‖x ⬝ᵥ y‖ ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans ?_
    simp
  have h2 : (∑ i, ‖x i‖ * ‖y i‖) ^ 2 ≤ (cNorm x * cNorm y) ^ 2 := by
    rw [mul_pow, cNorm_sq, cNorm_sq]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  exact h1.trans (le_of_sq_le_sq h2 (mul_nonneg (cNorm_nonneg _) (cNorm_nonneg _)))

/-- Complexification of a real vector. -/
def cplx (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

theorem cNorm_cplx_sq (x : ι → ℝ) : cNorm (cplx x) ^ 2 = x ⬝ᵥ x := by
  rw [cNorm_sq]
  simp [cplx, dotProduct, sq]

/-! ### The explicit solution -/

theorem sqrtDot_ne_zero_of_re {x : ι → ℂ} (hx : 0 < (x ⬝ᵥ x).re) : sqrtDot x ≠ 0 := by
  intro h0
  have := sqrtDot_sq x
  rw [h0] at this
  have h2 : (x ⬝ᵥ x).re = 0 := by rw [← this]; simp
  linarith

theorem cMinimizer_dot {a ν : ℝ} {ψ h : ι → ℂ} (hx : cBlend a ν ψ h ⬝ᵥ cBlend a ν ψ h ≠ 0) :
    cMinimizer a ν ψ h ⬝ᵥ cMinimizer a ν ψ h = 1 := by
  have hr : sqrtDot (cBlend a ν ψ h) ≠ 0 := by
    intro h0
    apply hx
    rw [← sqrtDot_sq, h0]; simp
  unfold cMinimizer
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← sqrtDot_sq]
  field_simp

/-- The complex Euler–Lagrange equation. -/
def IsCEL (a ν : ℝ) (ψ h φ : ι → ℂ) (α : ℂ) : Prop :=
  (a : ℂ) • (φ - ψ) + (ν : ℂ) • (φ - h) + α • φ = 0

omit [Fintype ι] in
theorem isCEL_iff {a ν : ℝ} {ψ h φ : ι → ℂ} {α : ℂ} :
    IsCEL a ν ψ h φ α ↔ ((a : ℂ) + ν + α) • φ = cBlend a ν ψ h := by
  unfold IsCEL cBlend
  constructor <;> intro H <;> funext i <;> have := congrFun H i <;>
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at this ⊢ <;>
    linear_combination this

theorem cMultiplier_add (a ν : ℝ) (ψ h : ι → ℂ) :
    (a : ℂ) + ν + cMultiplier a ν ψ h = sqrtDot (cBlend a ν ψ h) := by
  unfold cMultiplier; ring

theorem cMinimizer_isCEL {a ν : ℝ} {ψ h : ι → ℂ} (hx : cBlend a ν ψ h ⬝ᵥ cBlend a ν ψ h ≠ 0) :
    IsCEL a ν ψ h (cMinimizer a ν ψ h) (cMultiplier a ν ψ h) := by
  have hr : sqrtDot (cBlend a ν ψ h) ≠ 0 := by
    intro h0
    apply hx
    rw [← sqrtDot_sq, h0]; simp
  rw [isCEL_iff, cMultiplier_add]
  unfold cMinimizer
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul]

/-- **Uniqueness (complex data).**  A solution `(φ, α)` of the Euler–Lagrange system with
`φ ⬝ᵥ φ = 1` and `‖α‖ < a + ν` is `(φ*, α*)`; no condition on the data is needed. -/
theorem eq_of_isCEL {a ν : ℝ} {ψ h φ : ι → ℂ} {α : ℂ} (hφ : φ ⬝ᵥ φ = 1)
    (hEL : IsCEL a ν ψ h φ α) (hα : ‖α‖ < a + ν) :
    φ = cMinimizer a ν ψ h ∧ α = cMultiplier a ν ψ h := by
  rw [isCEL_iff] at hEL
  set s : ℂ := (a : ℂ) + ν + α with hs
  have hres : 0 < s.re := by
    have h1 : |α.re| ≤ ‖α‖ := Complex.abs_re_le_norm α
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 hα)
    simp [hs]; linarith
  have hww : cBlend a ν ψ h ⬝ᵥ cBlend a ν ψ h = s ^ 2 := by
    rw [← hEL, smul_dotProduct, dotProduct_smul, hφ]; simp [sq]
  have hsne : s ≠ 0 := fun h0 => by simp [h0] at hres
  have hsq : s ^ 2 = sqrtDot (cBlend a ν ψ h) ^ 2 := by rw [sqrtDot_sq, hww]
  have hpm : s = sqrtDot (cBlend a ν ψ h) ∨ s = -sqrtDot (cBlend a ν ψ h) :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have hr : s = sqrtDot (cBlend a ν ψ h) := by
    rcases hpm with hp | hp
    · exact hp
    · exfalso
      have := re_sqrtDot_nonneg (cBlend a ν ψ h)
      have h3 : s.re = -(sqrtDot (cBlend a ν ψ h)).re := by rw [hp]; simp
      linarith
  refine ⟨?_, ?_⟩
  · unfold cMinimizer
    rw [← hr, ← hEL, smul_smul, inv_mul_cancel₀ hsne, one_smul]
  · unfold cMultiplier; rw [← hr, hs]; ring

/-! ### Analyticity -/

/-- The open domain `Re (w ⬝ᵥ w) > 0` of the complex solution. -/
def cDomain (a ν : ℝ) : Set ((ι → ℂ) × (ι → ℂ)) :=
  {p | 0 < (cBlend a ν p.1 p.2 ⬝ᵥ cBlend a ν p.1 p.2).re}

theorem analyticAt_coord (i : ι) (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => q.1 i) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).comp
    (ContinuousLinearMap.fst ℂ (ι → ℂ) (ι → ℂ))).analyticAt p

theorem analyticAt_coord' (i : ι) (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => q.2 i) p :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).comp
    (ContinuousLinearMap.snd ℂ (ι → ℂ) (ι → ℂ))).analyticAt p

theorem analyticAt_cBlend_coord (a ν : ℝ) (i : ι) (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => cBlend a ν q.1 q.2 i) p := by
  have h1 := analyticAt_coord i p
  have h2 := analyticAt_coord' i p
  simp only [cBlend, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ((analyticAt_const (v := (a : ℂ))).fun_mul h1).fun_add
    ((analyticAt_const (v := (ν : ℂ))).fun_mul h2)

theorem analyticAt_cBlend_dot (a ν : ℝ) (p : (ι → ℂ) × (ι → ℂ)) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) =>
      cBlend a ν q.1 q.2 ⬝ᵥ cBlend a ν q.1 q.2) p := by
  unfold dotProduct
  exact Finset.analyticAt_fun_sum _ (fun i _ =>
    (analyticAt_cBlend_coord a ν i p).mul (analyticAt_cBlend_coord a ν i p))

theorem isOpen_cDomain (a ν : ℝ) : IsOpen (cDomain (ι := ι) a ν) := by
  have hc : Continuous fun q : (ι → ℂ) × (ι → ℂ) =>
      (cBlend a ν q.1 q.2 ⬝ᵥ cBlend a ν q.1 q.2).re :=
    Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun p =>
      (analyticAt_cBlend_dot a ν p).continuousAt)
  exact isOpen_lt continuous_const hc

theorem analyticAt_sqrtDot_blend (a ν : ℝ) {p : (ι → ℂ) × (ι → ℂ)} (hp : p ∈ cDomain a ν) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × (ι → ℂ) => sqrtDot (cBlend a ν q.1 q.2)) p := by
  have hs : cBlend a ν p.1 p.2 ⬝ᵥ cBlend a ν p.1 p.2 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hp)
  exact (analyticAt_cBlend_dot a ν p).cpow analyticAt_const hs

theorem analyticOnNhd_cMultiplier (a ν : ℝ) :
    AnalyticOnNhd ℂ (fun q : (ι → ℂ) × (ι → ℂ) => cMultiplier a ν q.1 q.2) (cDomain a ν) := by
  intro p hp
  unfold cMultiplier
  exact ((analyticAt_sqrtDot_blend a ν hp).sub analyticAt_const).sub analyticAt_const

theorem analyticOnNhd_cMinimizer_coord (a ν : ℝ) (i : ι) :
    AnalyticOnNhd ℂ (fun q : (ι → ℂ) × (ι → ℂ) => cMinimizer a ν q.1 q.2 i) (cDomain a ν) := by
  intro p hp
  have hne : sqrtDot (cBlend a ν p.1 p.2) ≠ 0 := sqrtDot_ne_zero_of_re hp
  simp only [cMinimizer, Pi.smul_apply, smul_eq_mul]
  exact ((analyticAt_sqrtDot_blend a ν hp).inv hne).mul (analyticAt_cBlend_coord a ν i p)

theorem analyticOnNhd_cMinimizer (a ν : ℝ) :
    AnalyticOnNhd ℂ (fun q : (ι → ℂ) × (ι → ℂ) => cMinimizer a ν q.1 q.2) (cDomain a ν) :=
  analyticOnNhd_pi_iff.mpr (analyticOnNhd_cMinimizer_coord a ν)

/-! ### Compatibility with the real solution -/

omit [Fintype ι] in
theorem cBlend_cplx (a ν : ℝ) (ψ h : ι → ℝ) :
    cBlend a ν (cplx ψ) (cplx h) = cplx (blendVec a ν ψ h) := by
  funext i; simp [cBlend, cplx, blendVec]

theorem cplx_dot (x y : ι → ℝ) : cplx x ⬝ᵥ cplx y = ((x ⬝ᵥ y : ℝ) : ℂ) := by
  simp [cplx, dotProduct]

theorem sqrtDot_cplx (x : ι → ℝ) : sqrtDot (cplx x) = ((Real.sqrt (x ⬝ᵥ x) : ℝ) : ℂ) := by
  have hx : 0 ≤ x ⬝ᵥ x := dotSelf_nonneg x
  rw [sqrtDot, cplx_dot, Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]
  norm_num

/-- For real data the complex solution is the real one. -/
theorem cMinimizer_cplx (a ν : ℝ) (ψ h : ι → ℝ) :
    cMinimizer a ν (cplx ψ) (cplx h) = cplx (constMinimizer a ν ψ h) := by
  funext i
  simp [cMinimizer, cBlend_cplx, sqrtDot_cplx, constMinimizer, cplx]

theorem cMultiplier_cplx (a ν : ℝ) (ψ h : ι → ℝ) :
    cMultiplier a ν (cplx ψ) (cplx h) = ((constMultiplier a ν ψ h : ℝ) : ℂ) := by
  simp [cMultiplier, cBlend_cplx, sqrtDot_cplx, constMultiplier]

/-! ### Covariance -/

section Covariance

variable [DecidableEq ι]

theorem cMulVec_dotProduct_mulVec (M : Matrix ι ι ℂ) (hM : Mᵀ * M = 1) (x y : ι → ℂ) :
    (M *ᵥ x) ⬝ᵥ (M *ᵥ y) = x ⬝ᵥ y := by
  rw [← vecMul_transpose, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_one]

omit [DecidableEq ι] in
theorem cBlend_mulVec (a ν : ℝ) (M : Matrix ι ι ℂ) (ψ h : ι → ℂ) :
    cBlend a ν (M *ᵥ ψ) (M *ᵥ h) = M *ᵥ cBlend a ν ψ h := by
  unfold cBlend
  rw [mulVec_add, mulVec_smul, mulVec_smul]

theorem sqrtDot_mulVec (M : Matrix ι ι ℂ) (hM : Mᵀ * M = 1) (x : ι → ℂ) :
    sqrtDot (M *ᵥ x) = sqrtDot x := by
  unfold sqrtDot; rw [cMulVec_dotProduct_mulVec M hM]

/-- **`O(N, ℂ)` covariance** (in particular for real orthogonal matrices, see
`cMinimizer_mulVec_ofReal`): `φ*(Mψ, Mh) = M φ*(ψ, h)` for `Mᵀ M = 1`. -/
theorem cMinimizer_mulVec (a ν : ℝ) (M : Matrix ι ι ℂ) (hM : Mᵀ * M = 1) (ψ h : ι → ℂ) :
    cMinimizer a ν (M *ᵥ ψ) (M *ᵥ h) = M *ᵥ cMinimizer a ν ψ h := by
  unfold cMinimizer
  rw [cBlend_mulVec, sqrtDot_mulVec M hM, mulVec_smul]

theorem cMultiplier_mulVec (a ν : ℝ) (M : Matrix ι ι ℂ) (hM : Mᵀ * M = 1) (ψ h : ι → ℂ) :
    cMultiplier a ν (M *ᵥ ψ) (M *ᵥ h) = cMultiplier a ν ψ h := by
  unfold cMultiplier
  rw [cBlend_mulVec, sqrtDot_mulVec M hM]

/-- A real orthogonal matrix is a complex orthogonal matrix. -/
theorem map_ofReal_transpose_mul (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1) :
    (R.map ((↑) : ℝ → ℂ))ᵀ * R.map (↑) = 1 := by
  ext i j
  have h0 := congrFun (congrFun hR i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h0
  have h1 := congrArg (fun x : ℝ => (x : ℂ)) h0
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply]
  push_cast at h1
  rw [h1]
  split_ifs <;> simp

/-- Covariance under a real orthogonal matrix acting on complex data. -/
theorem cMinimizer_mulVec_ofReal (a ν : ℝ) (R : Matrix ι ι ℝ) (hR : Rᵀ * R = 1)
    (ψ h : ι → ℂ) :
    cMinimizer a ν (R.map (↑) *ᵥ ψ) (R.map (↑) *ᵥ h) = R.map (↑) *ᵥ cMinimizer a ν ψ h := by
  exact cMinimizer_mulVec a ν _ (map_ofReal_transpose_mul R hR) ψ h

end Covariance

/-! ### The invariants `U, V, W²` of P2 (2.6) and the bounds -/

/-- `U = √(ψ ⬝ᵥ ψ)`. -/
noncomputable def invU (ψ : ι → ℂ) : ℂ := sqrtDot ψ

/-- `V = ψ ⬝ᵥ h / U` (`= ψ₀ ⬝ᵥ h`). -/
noncomputable def invV (ψ h : ι → ℂ) : ℂ := (ψ ⬝ᵥ h) / sqrtDot ψ

/-- `W² = h ⬝ᵥ h - V²`. -/
noncomputable def invW2 (ψ h : ι → ℂ) : ℂ := h ⬝ᵥ h - invV ψ h ^ 2

/-- `z = a (U - 1) + ν (V - 1)`. -/
noncomputable def invZ (a ν : ℝ) (ψ h : ι → ℂ) : ℂ :=
  a * (invU ψ - 1) + ν * (invV ψ h - 1)

/-- `w ⬝ᵥ w = (a + ν + z)² + ν² W²`: the scalar equation (2.9) of P2 at `λ = ∞`. -/
theorem cBlend_dot_eq (a ν : ℝ) {ψ h : ι → ℂ} (hU : sqrtDot ψ ≠ 0) :
    cBlend a ν ψ h ⬝ᵥ cBlend a ν ψ h =
      ((a : ℂ) + ν + invZ a ν ψ h) ^ 2 + (ν : ℂ) ^ 2 * invW2 ψ h := by
  have h1 : ψ ⬝ᵥ ψ = sqrtDot ψ ^ 2 := (sqrtDot_sq ψ).symm
  have h2 : ψ ⬝ᵥ h = sqrtDot ψ * invV ψ h := by unfold invV; field_simp
  simp only [cBlend, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [dotProduct_comm h ψ, h1, h2]
  unfold invZ invW2 invU
  ring

theorem norm_cMultiplier_le {a ν : ℝ} {ψ h : ι → ℂ} (hav : 1 / 2 < a + ν)
    (hU : sqrtDot ψ ≠ 0) (hz : ‖invZ a ν ψ h‖ ≤ 1 / 4) :
    ‖cMultiplier a ν ψ h‖ ≤ ‖invZ a ν ψ h‖ + 4 * ‖(ν : ℂ) ^ 2 * invW2 ψ h‖ := by
  set z := invZ a ν ψ h with hzdef
  set t : ℂ := (ν : ℂ) ^ 2 * invW2 ψ h with htdef
  set r := sqrtDot (cBlend a ν ψ h) with hr
  set s : ℂ := (a : ℂ) + ν + z with hs
  have hr2 : r ^ 2 = s ^ 2 + t := by rw [hr, sqrtDot_sq, cBlend_dot_eq a ν hU]
  have hfac : (r - s) * (r + s) = t := by linear_combination hr2
  have hrre : 0 ≤ r.re := re_sqrtDot_nonneg _
  have hzre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hsre : 1 / 4 < s.re := by
    have := abs_le.mp hzre
    simp [hs]; linarith [this.1]
  have hn : 1 / 4 < ‖r + s‖ := by
    have : (r + s).re ≤ ‖r + s‖ := Complex.re_le_norm _
    simp at this; linarith
  have hmul : ‖r - s‖ * ‖r + s‖ = ‖t‖ := by rw [← norm_mul, hfac]
  have hrs : ‖r - s‖ ≤ 4 * ‖t‖ := by
    nlinarith [norm_nonneg (r - s), norm_nonneg t]
  have hα : cMultiplier a ν ψ h = (r - s) + z := by
    unfold cMultiplier; rw [← hr, hs]; ring
  rw [hα]
  calc ‖(r - s) + z‖ ≤ ‖r - s‖ + ‖z‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **P2 (2.15), the bound on `φ - ψ`, at `λ = ∞`.**  With `α` as above,
`‖φ - ψ‖ ≤ 4 (ν ‖h - ψ‖ + (|z| + 4 |ν² W²|) ‖ψ‖)`, provided `|z| + 4 |ν² W²| ≤ 1/4`. -/
theorem cNorm_cMinimizer_sub_le {a ν : ℝ} {ψ h : ι → ℂ} (hν : 0 ≤ ν) (hav : 1 / 2 < a + ν)
    (hU : sqrtDot ψ ≠ 0)
    (hα : ‖invZ a ν ψ h‖ + 4 * ‖(ν : ℂ) ^ 2 * invW2 ψ h‖ ≤ 1 / 4) :
    cNorm (cMinimizer a ν ψ h - ψ) ≤
      4 * (ν * cNorm (h - ψ) +
        (‖invZ a ν ψ h‖ + 4 * ‖(ν : ℂ) ^ 2 * invW2 ψ h‖) * cNorm ψ) := by
  have hz : ‖invZ a ν ψ h‖ ≤ 1 / 4 := by
    have := norm_nonneg ((ν : ℂ) ^ 2 * invW2 ψ h); linarith
  have hαb := norm_cMultiplier_le hav hU hz
  set α := cMultiplier a ν ψ h with hαdef
  set r := sqrtDot (cBlend a ν ψ h) with hr
  have hrα : r = (a : ℂ) + ν + α := (cMultiplier_add a ν ψ h).symm
  have hnorm_aν : ‖((a : ℂ) + ν)‖ = a + ν := by
    have : ((a : ℂ) + ν) = ((a + ν : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hrn : 1 / 4 ≤ ‖r‖ := by
    have : ‖((a : ℂ) + ν)‖ - ‖α‖ ≤ ‖(a : ℂ) + ν + α‖ := by
      have := norm_sub_norm_le ((a : ℂ) + ν) (-α)
      simpa [sub_eq_add_neg] using this
    rw [hrα]; linarith
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hrn; simp at hrn; linarith
  have hid : cMinimizer a ν ψ h - ψ = r⁻¹ • ((ν : ℂ) • (h - ψ) - α • ψ) := by
    funext i
    have hw : cBlend a ν ψ h i = a * ψ i + ν * h i := by simp [cBlend]
    simp only [cMinimizer, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hr, hw]
    have key : (a : ℂ) * ψ i + ν * h i = r * ψ i + (ν * (h i - ψ i) - α * ψ i) := by
      rw [hrα]; ring
    rw [key]; field_simp; ring
  rw [hid, cNorm_smul]
  have hinv : ‖r⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    calc ‖r‖⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hrn
      _ = 4 := by norm_num
  have hin : cNorm ((ν : ℂ) • (h - ψ) - α • ψ) ≤ ν * cNorm (h - ψ) + ‖α‖ * cNorm ψ := by
    refine (cNorm_sub_le _ _).trans ?_
    rw [cNorm_smul, cNorm_smul]
    simp [Complex.norm_real, abs_of_nonneg hν]
  have hαψ : ‖α‖ * cNorm ψ ≤ (‖invZ a ν ψ h‖ + 4 * ‖(ν : ℂ) ^ 2 * invW2 ψ h‖) * cNorm ψ :=
    mul_le_mul_of_nonneg_right hαb (cNorm_nonneg _)
  have hnn : 0 ≤ cNorm ((ν : ℂ) • (h - ψ) - α • ψ) := cNorm_nonneg _
  calc ‖r⁻¹‖ * cNorm ((ν : ℂ) • (h - ψ) - α • ψ) ≤ 4 * cNorm ((ν : ℂ) • (h - ψ) - α • ψ) :=
        mul_le_mul_of_nonneg_right hinv hnn
    _ ≤ _ := by nlinarith

/-! ### The polydisc around real data -/

theorem re_dot_pos_of_near (x : ι → ℝ) {m : ℝ} (hm : 0 < m) (hx : m ≤ cNorm (cplx x))
    {w : ι → ℂ} (hw : cNorm (w - cplx x) ≤ m / 4) : 0 < (w ⬝ᵥ w).re := by
  set N := cNorm (cplx x) with hN
  set d := cNorm (w - cplx x) with hd
  have hdec : w ⬝ᵥ w = cplx x ⬝ᵥ cplx x + 2 * (cplx x ⬝ᵥ (w - cplx x)) +
      (w - cplx x) ⬝ᵥ (w - cplx x) := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm (cplx x) w]
    ring
  have h0 : (cplx x ⬝ᵥ cplx x).re = N ^ 2 := by
    rw [cplx_dot, hN, cNorm_cplx_sq]; simp
  have h1 : ‖cplx x ⬝ᵥ (w - cplx x)‖ ≤ N * d := norm_dotProduct_le _ _
  have h2 : ‖(w - cplx x) ⬝ᵥ (w - cplx x)‖ ≤ d * d := norm_dotProduct_le _ _
  have h1' := (Complex.abs_re_le_norm (cplx x ⬝ᵥ (w - cplx x))).trans h1
  have h2' := (Complex.abs_re_le_norm ((w - cplx x) ⬝ᵥ (w - cplx x))).trans h2
  rw [hdec]
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, h0]
  have hd0 : 0 ≤ d := cNorm_nonneg _
  have h1'' := abs_le.mp h1'
  have h2'' := abs_le.mp h2'
  nlinarith [mul_nonneg hd0 hd0, mul_nonneg hd0 (le_trans hm.le hx)]

/-- **The polydisc around real data.**  If the real vector `w₀ = aψ₀ + νh₀` has `ℓ²` norm at least
`m` (`0 ≤ a ≤ 3/2`, `0 ≤ ν ≤ 1`), then every complex `(ψ, h)` with `‖ψ - ψ₀‖ ≤ m/10` and
`ν ‖h - h₀‖ ≤ m/10` lies in the domain `Re (w ⬝ᵥ w) > 0` of the analytic solution. -/
theorem mem_cDomain_of_near {a ν : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 3 / 2) (hν : 0 ≤ ν)
    (ψ₀ h₀ : ι → ℝ) {m : ℝ} (hm : 0 < m) (hx : m ≤ cNorm (cplx (blendVec a ν ψ₀ h₀)))
    {ψ h : ι → ℂ} (hψ : cNorm (ψ - cplx ψ₀) ≤ m / 10) (hh : ν * cNorm (h - cplx h₀) ≤ m / 10) :
    (ψ, h) ∈ cDomain a ν := by
  apply re_dot_pos_of_near (blendVec a ν ψ₀ h₀) hm hx
  have : cBlend a ν ψ h - cplx (blendVec a ν ψ₀ h₀) =
      (a : ℂ) • (ψ - cplx ψ₀) + (ν : ℂ) • (h - cplx h₀) := by
    funext i; simp [cBlend, cplx, blendVec]; ring
  change cNorm (cBlend a ν ψ h - cplx (blendVec a ν ψ₀ h₀)) ≤ m / 4
  rw [this]
  refine (cNorm_add_le _ _).trans ?_
  rw [cNorm_smul, cNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hν]
  have := mul_le_mul ha' hψ (cNorm_nonneg _) (by norm_num)
  linarith

end Balaban.Background
