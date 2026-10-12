/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovParam
public import Balaban.Localization.DecoupledFunctional
public import Balaban.Localization.DecoupledCovAnalytic
public import Balaban.Localization.DecoupledCovReal
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# I-4c (iv) for complex data: the principal inverse square root and logarithm

LOCALIZATION.md §3.4, Theorem I-4c (iv). For a square complex matrix `A` call `ResOK A` the
property that `x + A` is invertible for every `x ≥ 0` (equivalently, `A` has no eigenvalue in
`(-∞, 0]`). The landed identification `C_x(1) = (x + 𝒜)⁻¹` (`decCov_one_eq`) gives `ResOK 𝒜`
for **every** admissible datum, real or complex, so no positivity or spectral-gap hypothesis is
needed. Put

* `sqrtMat A = π⁻¹ ∫₀^∞ x^{-1/2} (x + A)⁻¹ dx`,
* `logMat A = -∫₀^∞ ((x + A)⁻¹ - (1 + x)⁻¹) dx`.

The matrix-level theory (any `A` with `ResOK A`):

* resolvent bounds `ResOK.bound`, stability `ResOK.perturb`, `resOK_nhds`, `isOpen_setOf_resOK`;
* `analyticOnNhd_sqrtMat_fam`, `analyticOnNhd_logMat_fam`: analyticity along analytic families;
* `principal_identity`: an analytic identity `Φ(A) = 0` valid for all positive definite `A` holds for
  all `A` with `ResOK A` (Step 1: for Hermitian `X`, `Y` the entries of `Φ(1 + t (X + z Y))` are
  analytic in `z` and vanish for real `z`; Step 2: the line `t ↦ 1 + t B` stays in the
  star-shaped open set `{t | ResOK (1 + t B)}`);
* `sqrtMat_mul_self : sqrtMat A * sqrtMat A = A⁻¹`, `exp_logMat : exp (logMat A) = A`;
* `sqrtMat_principal`, `logMat_principal`: the commutation with `A`, and the spectrum of `sqrtMat A`
  in `{Re z > 0}`, of `logMat A` in `{|Im z| < π}` (a common eigenvector of `A` and the matrix
  reduces to `1 × 1` matrices `mat1 l`, where the real part (imaginary part) cannot cross `0`
  (`±π`) along the path `t ↦ (1 - t) + t l`).

These characterize `sqrtMat A` as the principal inverse square root and `logMat A` as the principal
logarithm. The covariance statements:

* `decCovSqrt_one_eq_sqrtMat`, `decLog_one_eq_logMat`: `C^{1/2}(1) = sqrtMat 𝒜`, `𝕃(1) = logMat 𝒜`;
* `decCovSqrt_one_principal`: `C^{1/2}(1)² = C(1) = 𝒜⁻¹`, commutation with `𝒜`, positive real parts;
* `decLog_one_principal`: `exp 𝕃(1) = 𝒜`, commutation with `𝒜`, imaginary parts in `(-π, π)`.
-/

@[expose] public section

namespace Balaban.Localization

open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory Set
open scoped ComplexOrder

section Resolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem norm_one_matrix : ‖(1 : Matrix ι ι ℂ)‖ = 1 := norm_one

theorem isUnit_one_add_of_norm_le {u : Matrix ι ι ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    IsUnit (1 + u) ∧ ‖(1 + u)⁻¹‖ ≤ 2 := by
  have h1 : ‖-u‖ < 1 := by rw [norm_neg]; linarith
  set U := Units.oneSub (-u) h1 with hU
  have hUv : (U : Matrix ι ι ℂ) = 1 + u := by simp [hU, Units.val_oneSub]
  have hunit : IsUnit (1 + u) := hUv ▸ U.isUnit
  refine ⟨hunit, ?_⟩
  have hinv : (1 + u)⁻¹ = ↑U⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hUv, Ring.inverse_unit]
  have hmul : (1 + u) * (1 + u)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit)
  set w := (1 + u)⁻¹ with hw
  have e : w = 1 - u * w := by
    have : (1 + u) * w = w + u * w := by rw [add_mul, one_mul]
    rw [this] at hmul
    rw [← hmul]; abel
  have : ‖w‖ ≤ 1 + ‖u‖ * ‖w‖ := by
    calc ‖w‖ = ‖1 - u * w‖ := by rw [← e]
      _ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖u * w‖ := norm_sub_le _ _
      _ ≤ 1 + ‖u‖ * ‖w‖ := by rw [norm_one]; gcongr; exact norm_mul_le _ _
  nlinarith [norm_nonneg w]

def ResOK (A : Matrix ι ι ℂ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)

theorem ResOK.bound {A : Matrix ι ι ℂ} (hA : ResOK A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹‖ ≤ C / (1 + x) := by
  set m := ‖A‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  set X0 : ℝ := 2 * m + 1 with hX0
  have hcont : ContinuousOn (fun x : ℝ => ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹‖) (Icc 0 X0) := by
    refine continuous_norm.comp_continuousOn (contOn_matrix_inv ?_ ?_)
    · exact (Continuous.add (Complex.continuous_ofReal.smul continuous_const)
        continuous_const).continuousOn
    · intro x hx; exact hA x hx.1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont
  have hB' : ∀ x ∈ Icc 0 X0, ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹‖ ≤ B := fun x hx =>
    hB ⟨x, hx, rfl⟩
  refine ⟨max 4 (max B 0 * (1 + X0)), le_trans (by norm_num) (le_max_left _ _), fun x hx => ?_⟩
  have h1x : 0 < 1 + x := by linarith
  by_cases hxX : x ≤ X0
  · refine (hB' x ⟨hx, hxX⟩).trans ?_
    rw [le_div_iff₀ h1x]
    calc B * (1 + x) ≤ max B 0 * (1 + X0) := by
          have := le_max_left B 0
          have h0 := le_max_right B 0
          nlinarith
      _ ≤ _ := le_max_right _ _
  · push Not at hxX
    have hx1 : 1 ≤ x := by linarith
    have hxpos : 0 < x := by linarith
    set u : Matrix ι ι ℂ := ((x⁻¹ : ℝ) : ℂ) • A with hu
    have hun : ‖u‖ ≤ 1 / 2 := by
      rw [hu, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [inv_mul_le_iff₀ hxpos]
      linarith
    obtain ⟨hU, hUn⟩ := isUnit_one_add_of_norm_le hun
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
    have hprod : ((x : ℂ) • (1 : Matrix ι ι ℂ) + A) * (((x⁻¹ : ℝ) : ℂ) • (1 + u)⁻¹) = 1 := by
      have e : (x : ℂ) • (1 : Matrix ι ι ℂ) + A = (x : ℂ) • (1 + u) := by
        rw [hu, smul_add, smul_smul]
        push_cast
        rw [mul_inv_cancel₀ hxc, one_smul]
      rw [e, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)]
      push_cast
      rw [mul_inv_cancel₀ hxc, one_smul]
    rw [Matrix.inv_eq_right_inv hprod, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), le_div_iff₀ h1x]
    calc x⁻¹ * ‖(1 + u)⁻¹‖ * (1 + x) ≤ x⁻¹ * 2 * (2 * x) := by
          have : (1 + x) ≤ 2 * x := by linarith
          have h2 : 0 ≤ x⁻¹ := by positivity
          calc _ ≤ x⁻¹ * 2 * (1 + x) := by gcongr
            _ ≤ _ := by gcongr
      _ = 4 := by field_simp; norm_num
      _ ≤ _ := le_max_left _ _

omit [Nonempty ι] in
theorem entry_norm_le_l2 (N : Matrix ι ι ℂ) (p q : ι) : ‖N p q‖ ≤ ‖N‖ := by
  refine norm_entry_le N (norm_nonneg _) (fun f => ?_) p q
  rw [sqNorm_le_iff (norm_nonneg _), n2_eq_norm, n2_eq_norm]
  have := Matrix.l2_opNorm_mulVec N (WithLp.toLp 2 f)
  simpa using this

theorem ResOK.perturb {A A' : Matrix ι ι ℂ} {C : ℝ} (hC : 0 < C) (hA : ResOK A)
    (hb : ∀ x : ℝ, 0 ≤ x → ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹‖ ≤ C / (1 + x))
    (hd : ‖A' - A‖ ≤ 1 / (2 * C)) :
    ResOK A' ∧ ∀ x : ℝ, 0 ≤ x → ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹‖ ≤ 2 * C / (1 + x) := by
  have key : ∀ x : ℝ, 0 ≤ x → IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A') ∧
      ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹‖ ≤ 2 * C / (1 + x) := by
    intro x hx
    have h1x : 0 < 1 + x := by linarith
    set R := ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ with hR
    have hU := hA x hx
    have hRR : ((x : ℂ) • (1 : Matrix ι ι ℂ) + A) * R = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
    set u := R * (A' - A) with hu
    have hun : ‖u‖ ≤ 1 / 2 := by
      calc ‖u‖ ≤ ‖R‖ * ‖A' - A‖ := norm_mul_le _ _
        _ ≤ C / (1 + x) * (1 / (2 * C)) := by
          gcongr
          · exact hb x hx
        _ ≤ 1 / 2 := by
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    obtain ⟨hU1, hUn⟩ := isUnit_one_add_of_norm_le hun
    have e : (x : ℂ) • (1 : Matrix ι ι ℂ) + A' =
        ((x : ℂ) • (1 : Matrix ι ι ℂ) + A) * (1 + u) := by
      rw [hu, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
      abel
    refine ⟨e ▸ hU.mul hU1, ?_⟩
    rw [e, Matrix.mul_inv_rev]
    calc ‖(1 + u)⁻¹ * R‖ ≤ ‖(1 + u)⁻¹‖ * ‖R‖ := norm_mul_le _ _
      _ ≤ 2 * (C / (1 + x)) := by gcongr; exact hb x hx
      _ = 2 * C / (1 + x) := by ring
  exact ⟨fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

omit [Nonempty ι] in
/-- The resolvent integrand of the square root, as a function of `x`. -/
noncomputable def sqrtMat (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) • intMat (volume.restrict (Ioi (0 : ℝ)))
    (fun x => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹)

omit [Nonempty ι] in
noncomputable def logMat (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  -intMat (volume.restrict (Ioi (0 : ℝ)))
    (fun x => ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ))

/-- Local uniform resolvent bounds near a point of an open set on which the family is `ResOK`. -/
theorem fam_local_bound {M : ℂ → Matrix ι ι ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hRes : ∀ z ∈ D, ResOK (M z)) {z0 : ℂ} (hz0 : z0 ∈ D) (hc : ContinuousAt M z0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C m : ℝ, 0 < C ∧ Metric.ball z0 r ⊆ D ∧ ∀ z ∈ Metric.ball z0 r,
      ‖M z - 1‖ ≤ m ∧ ∀ x : ℝ, 0 ≤ x → ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹‖ ≤ C / (1 + x) := by
  obtain ⟨C0, hC0, hb0⟩ := (hRes z0 hz0).bound
  set C1 := max C0 1 with hC1
  have hC1p : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb1 : ∀ x : ℝ, 0 ≤ x → ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + M z0)⁻¹‖ ≤ C1 / (1 + x) := by
    intro x hx
    refine (hb0 x hx).trans ?_
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
  have hev : ∀ᶠ z in nhds z0, ‖M z - M z0‖ < 1 / (2 * C1) + 0 := by
    have := (continuous_norm.continuousAt.comp (hc.sub (continuousAt_const (y := M z0))))
    have h0 : ‖M z0 - M z0‖ = 0 := by simp
    have hpos : (0 : ℝ) < 1 / (2 * C1) := by positivity
    refine this.eventually (gt_mem_nhds ?_)
    show ‖M z0 - M z0‖ < _
    rw [h0]; linarith
  obtain ⟨r1, hr1, hr1'⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨r2, hr2, hr2'⟩ := Metric.isOpen_iff.1 hD z0 hz0
  refine ⟨min r1 r2, lt_min hr1 hr2, 2 * C1, ‖M z0 - 1‖ + 1 / (2 * C1), by positivity, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hr2'
  · intro z hz
    have hzr1 : dist z z0 < r1 := lt_of_lt_of_le (Metric.mem_ball.1 hz) (min_le_left _ _)
    have hd : ‖M z - M z0‖ ≤ 1 / (2 * C1) := (hr1' hzr1).le.trans (by simp)
    obtain ⟨hres, hbd⟩ := ResOK.perturb hC1p (hRes z0 hz0) hb1 hd
    refine ⟨?_, hbd⟩
    calc ‖M z - 1‖ = ‖(M z - M z0) + (M z0 - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖M z - M z0‖ + ‖M z0 - 1‖ := norm_add_le _ _
      _ ≤ _ := by linarith

omit [Nonempty ι] in
theorem rectAt_resolvent {M : ℂ → Matrix ι ι ℂ} {z : ℂ} (hM : RectAt M z) (x : ℝ)
    (hu : IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + M z)) :
    RectAt (fun w => ((x : ℂ) • (1 : Matrix ι ι ℂ) + M w)⁻¹) z :=
  ((RectAt.const _ z).add hM).inv ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem continuousAt_of_rectAt {M : ℂ → Matrix ι ι ℂ} {z : ℂ} (hM : RectAt M z) :
    ContinuousAt M z :=
  continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => (hM i j).continuousAt

omit [Nonempty ι] in
theorem continuousOn_resolvent_entry {A : Matrix ι ι ℂ} (hA : ∀ x : ℝ, 0 < x →
    IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) (p q : ι) :
    ContinuousOn (fun x : ℝ => ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ p q) (Ioi 0) := by
  have h := contOn_matrix_inv (F := fun x : ℝ => (x : ℂ) • (1 : Matrix ι ι ℂ) + A) (S := Ioi 0)
    (Continuous.add (Complex.continuous_ofReal.smul continuous_const)
      continuous_const).continuousOn (fun x hx => hA x hx)
  exact continuousOn_pi.1 (continuousOn_pi.1 h p) q

theorem analyticOnNhd_sqrtMat_fam {M : ℂ → Matrix ι ι ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hRes : ∀ z ∈ D, ResOK (M z)) (hM : ∀ z ∈ D, RectAt M z) (p q : ι) :
    AnalyticOnNhd ℂ (fun z => sqrtMat (M z) p q) D := by
  intro z0 hz0
  obtain ⟨r, hr, C, m, hC, hsub, hb⟩ := fam_local_bound hD hRes hz0
    (continuousAt_of_rectAt (hM z0 hz0))
  have hint : AnalyticOnNhd ℂ (fun z => ∫ y in Ioi (0 : ℝ),
      ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹ p q)
      (Metric.ball z0 r) := by
    refine analyticOnNhd_integral_Ioi (g := fun y => C * (y ^ (-(1 / 2 : ℝ)) * (1 + y)⁻¹))
      Metric.isOpen_ball ?_ ?_ ?_ ?_ ?_
    · intro y hy z hz
      exact analyticAt_const.mul
        (rectAt_resolvent (hM z (hsub hz)) y (hRes z (hsub hz) y hy.le) p q)
    · intro z hz
      refine ContinuousOn.mul ?_ (continuousOn_resolvent_entry
        (fun y hy => hRes z (hsub hz) y hy.le) p q)
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
    · refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
      · exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
      · exact continuousOn_inv_add_Ioi (ak := 1) one_pos
    · exact (integrableOn_rpow_inv_add (l := 1) one_pos).const_mul C
    · intro y hy z hz
      have h3 : 0 < y ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hy _
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      have h1 := entry_norm_le_l2 (((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹) p q
      have h2 := (hb z hz).2 y hy.le
      calc y ^ (-(1 / 2 : ℝ)) * ‖((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹ p q‖
          ≤ y ^ (-(1 / 2 : ℝ)) * (C / (1 + y)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) h3.le
        _ = _ := by rw [div_eq_mul_inv]; ring
  have := (analyticAt_const (v := ((1 / Real.pi : ℝ) : ℂ))).mul (hint z0 (Metric.mem_ball_self hr))
  refine this.congr ?_
  filter_upwards with z
  simp only [sqrtMat, intMat, Matrix.smul_apply, smul_eq_mul]
  rfl

omit [Nonempty ι] in
theorem resolvent_sub_scalar {A : Matrix ι ι ℂ} {x : ℝ} (hx : 0 ≤ x)
    (hu : IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) :
    ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) =
      (((1 + x)⁻¹ : ℝ) : ℂ) • (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * (1 - A)) := by
  set X := (x : ℂ) • (1 : Matrix ι ι ℂ) + A with hX
  have hXR : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hRX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have h1x : ((1 + x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 + x := by linarith
    exact_mod_cast this.ne'
  have hs : (((1 + x)⁻¹ : ℝ) : ℂ) * ((1 : ℂ) + x) = 1 := by
    push_cast at h1x ⊢
    exact inv_mul_cancel₀ h1x
  have e : (1 : Matrix ι ι ℂ) - A = ((1 : ℂ) + x) • (1 : Matrix ι ι ℂ) - X := by
    rw [hX, add_smul, one_smul]; abel
  rw [e, Matrix.mul_sub, hRX, Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul, hs, one_smul]

theorem analyticOnNhd_logMat_fam {M : ℂ → Matrix ι ι ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hRes : ∀ z ∈ D, ResOK (M z)) (hM : ∀ z ∈ D, RectAt M z) (p q : ι) :
    AnalyticOnNhd ℂ (fun z => logMat (M z) p q) D := by
  intro z0 hz0
  obtain ⟨r, hr, C, m, hC, hsub, hb⟩ := fam_local_bound hD hRes hz0
    (continuousAt_of_rectAt (hM z0 hz0))
  have hint : AnalyticOnNhd ℂ (fun z => ∫ y in Ioi (0 : ℝ),
      (((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹ - (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) p q)
      (Metric.ball z0 r) := by
    refine analyticOnNhd_integral_Ioi (g := fun y => C * m * ((1 + y)⁻¹) ^ 2)
      Metric.isOpen_ball ?_ ?_ ?_ ?_ ?_
    · intro y hy z hz
      simp only [Matrix.sub_apply]
      exact (rectAt_resolvent (hM z (hsub hz)) y (hRes z (hsub hz) y hy.le) p q).sub
        analyticAt_const
    · intro z hz
      refine ContinuousOn.sub (continuousOn_resolvent_entry
        (fun y hy => hRes z (hsub hz) y hy.le) p q) ?_
      simp only [Matrix.smul_apply]
      exact (Complex.continuous_ofReal.comp_continuousOn
        (continuousOn_inv_add_Ioi (ak := 1) one_pos)).smul continuousOn_const
    · exact continuousOn_const.mul ((continuousOn_inv_add_Ioi (ak := 1) one_pos).pow 2)
    · exact (integrableOn_inv_add_sq (a := 1) one_pos).const_mul _
    · intro y hy z hz
      have hy0 : 0 ≤ y := hy.le
      have h1y : 0 < 1 + y := by linarith
      rw [resolvent_sub_scalar hy0 (hRes z (hsub hz) y hy0)]
      have hsn : ‖(((1 + y)⁻¹ : ℝ) : ℂ)‖ = (1 + y)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖((((1 + y)⁻¹ : ℝ) : ℂ) • (((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹ * (1 - M z))) p q‖
          ≤ ‖(((1 + y)⁻¹ : ℝ) : ℂ) • (((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹ * (1 - M z))‖ :=
            entry_norm_le_l2 _ p q
        _ = (1 + y)⁻¹ * ‖((y : ℂ) • (1 : Matrix ι ι ℂ) + M z)⁻¹ * (1 - M z)‖ := by
            rw [norm_smul, hsn]
        _ ≤ (1 + y)⁻¹ * (C / (1 + y) * m) := by
            gcongr
            refine (norm_mul_le _ _).trans ?_
            refine mul_le_mul ((hb z hz).2 y hy0) ?_ (norm_nonneg _) (by positivity)
            rw [norm_sub_rev]; exact (hb z hz).1
        _ = C * m * ((1 + y)⁻¹) ^ 2 := by field_simp
  have := (hint z0 (Metric.mem_ball_self hr)).neg
  refine this.congr ?_
  filter_upwards with z
  simp only [logMat, intMat, Matrix.neg_apply]
  rfl

omit [Nonempty ι] in
theorem isUnit_smul_matrix {c : ℂ} (hc : c ≠ 0) {M : Matrix ι ι ℂ} (hM : IsUnit M) :
    IsUnit (c • M) := by
  rw [Matrix.isUnit_iff_isUnit_det] at hM ⊢
  rw [Matrix.det_smul]
  exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 hc)).mul hM

theorem resOK_one_add_of_norm_le {N : Matrix ι ι ℂ} (hN : ‖N‖ ≤ 1 / 2) :
    ResOK (1 + N) := by
  intro x hx
  have h1x : (0 : ℝ) < 1 + x := by linarith
  set u : Matrix ι ι ℂ := (((1 + x)⁻¹ : ℝ) : ℂ) • N with hu
  have hun : ‖u‖ ≤ 1 / 2 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (1 + x)⁻¹ * ‖N‖ ≤ 1 * ‖N‖ := by
          gcongr
          rw [inv_le_one₀ h1x]; linarith
      _ ≤ 1 / 2 := by linarith
  obtain ⟨hU, _⟩ := isUnit_one_add_of_norm_le hun
  have hc : ((1 + x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1x.ne'
  have e : (x : ℂ) • (1 : Matrix ι ι ℂ) + (1 + N) = ((1 + x : ℝ) : ℂ) • (1 + u) := by
    rw [hu, smul_add, smul_smul]
    push_cast at hc ⊢
    rw [mul_inv_cancel₀ hc, one_smul, add_smul, one_smul]
    abel
  rw [e]
  exact isUnit_smul_matrix hc hU

theorem resOK_nhds {A : Matrix ι ι ℂ} (hA : ResOK A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ A' : Matrix ι ι ℂ, ‖A' - A‖ ≤ ε → ResOK A' := by
  obtain ⟨C, hC, hb⟩ := hA.bound
  set C1 := max C 1 with hC1
  have hC1p : 0 < C1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb1 : ∀ x : ℝ, 0 ≤ x → ‖((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹‖ ≤ C1 / (1 + x) := by
    intro x hx
    exact (hb x hx).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith))
  exact ⟨1 / (2 * C1), by positivity, fun A' h => (ResOK.perturb hC1p hA hb1 h).1⟩

omit [Nonempty ι] in
theorem resOK_one : ResOK (1 : Matrix ι ι ℂ) := by
  intro x hx
  have h1x : ((1 + x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 + x := by linarith
    exact_mod_cast this.ne'
  have : (x : ℂ) • (1 : Matrix ι ι ℂ) + 1 = ((1 + x : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    push_cast; rw [add_smul, one_smul, add_comm]
  rw [this]
  exact isUnit_smul_matrix h1x isUnit_one

omit [Nonempty ι] in
theorem resOK_one_add_smul_mul {B : Matrix ι ι ℂ} {t : ℂ} (ht : ResOK (1 + t • B)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ResOK (1 + ((r : ℂ) * t) • B) := by
  intro x hx
  by_cases hr : r = 0
  · subst hr
    simp only [Complex.ofReal_zero, zero_mul, zero_smul, add_zero]
    exact resOK_one x hx
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    set x'' : ℝ := (x + 1) / r - 1 with hx''
    have hx''0 : 0 ≤ x'' := by
      rw [hx'', sub_nonneg, le_div_iff₀ hrp]; nlinarith
    have hU := ht x'' hx''0
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    have e : (x : ℂ) • (1 : Matrix ι ι ℂ) + (1 + ((r : ℂ) * t) • B) =
        (r : ℂ) • ((x'' : ℂ) • (1 : Matrix ι ι ℂ) + (1 + t • B)) := by
      have hrx : (r : ℂ) * (x'' : ℂ) = (x : ℂ) + 1 - r := by
        rw [hx'']; push_cast; field_simp
      rw [smul_add, smul_add, smul_smul, smul_smul, hrx]
      module
    rw [e]
    exact isUnit_smul_matrix hrc hU

end Resolvent

open Filter Topology in
theorem eqOn_zero_of_real_zeros {f : ℂ → ℂ} {D : Set ℂ} (hf : AnalyticOnNhd ℂ f D)
    (hD : IsPreconnected D) (h0 : (0 : ℂ) ∈ D)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < ε ∧ f (s : ℂ) = 0) : ∀ z ∈ D, f z = 0 := by
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
    obtain ⟨s, hs0, hsε, hfs⟩ := hz ε hε
    refine ⟨(s : ℂ), hεU ⟨?_, ?_⟩, hfs⟩
    · simp [Metric.mem_ball, abs_of_pos hs0, hsε]
    · simp [hs0.ne']
  exact fun z hz => (hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hD h0 hfr) hz

section Integrable

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem integrable_sqrt_entry {A : Matrix ι ι ℂ} (hA : ResOK A) (p q : ι) :
    Integrable (fun y : ℝ => ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ p q) (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := hA.bound
  refine Integrable.mono' ((integrableOn_rpow_inv_add (l := 1) one_pos).const_mul C) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ (continuousOn_resolvent_entry (fun y hy => hA y hy.le) p q)
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact fun y hy => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hy).ne')).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 < y := mem_Ioi.mp hy
    have h3 : 0 < y ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hy0 _
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
    have h1 := entry_norm_le_l2 (((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) p q
    have h2 := hb y hy0.le
    calc y ^ (-(1 / 2 : ℝ)) * ‖((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ p q‖
        ≤ y ^ (-(1 / 2 : ℝ)) * (C / (1 + y)) := mul_le_mul_of_nonneg_left (h1.trans h2) h3.le
      _ = C * (y ^ (-(1 / 2 : ℝ)) * (1 + y)⁻¹) := by rw [div_eq_mul_inv]; ring

theorem integrable_log_entry {A : Matrix ι ι ℂ} (hA : ResOK A) (p q : ι) :
    Integrable (fun y : ℝ => (((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) p q) (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := hA.bound
  refine Integrable.mono' ((integrableOn_inv_add_sq (a := 1) one_pos).const_mul (C * ‖A - 1‖)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.sub (continuousOn_resolvent_entry (fun y hy => hA y hy.le) p q) ?_
    simp only [Matrix.smul_apply]
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_inv_add_Ioi (ak := 1) one_pos)).smul continuousOn_const
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 ≤ y := (mem_Ioi.mp hy).le
    have h1y : 0 < 1 + y := by linarith
    rw [resolvent_sub_scalar hy0 (hA y hy0)]
    have hsn : ‖(((1 + y)⁻¹ : ℝ) : ℂ)‖ = (1 + y)⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc ‖((((1 + y)⁻¹ : ℝ) : ℂ) • (((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * (1 - A))) p q‖
        ≤ ‖(((1 + y)⁻¹ : ℝ) : ℂ) • (((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * (1 - A))‖ :=
          entry_norm_le_l2 _ p q
      _ = (1 + y)⁻¹ * ‖((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * (1 - A)‖ := by rw [norm_smul, hsn]
      _ ≤ (1 + y)⁻¹ * (C / (1 + y) * ‖A - 1‖) := by
          gcongr
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul (hb y hy0) ?_ (norm_nonneg _) (by positivity)
          rw [norm_sub_rev]
      _ = C * ‖A - 1‖ * ((1 + y)⁻¹) ^ 2 := by field_simp

omit [Nonempty ι] in
theorem resolvent_commute {A : Matrix ι ι ℂ} {x : ℝ} (hu : IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) :
    ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * A = A * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ := by
  set X := (x : ℂ) • (1 : Matrix ι ι ℂ) + A with hX
  have hXR : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hRX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hc : X * A = A * X := by
    rw [hX, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  calc X⁻¹ * A = X⁻¹ * A * (X * X⁻¹) := by rw [hXR, mul_one]
    _ = X⁻¹ * (A * X) * X⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X⁻¹ * (X * A) * X⁻¹ := by rw [hc]
    _ = A * X⁻¹ := by
        calc X⁻¹ * (X * A) * X⁻¹ = (X⁻¹ * X) * A * X⁻¹ := by simp only [Matrix.mul_assoc]
          _ = A * X⁻¹ := by rw [hRX, one_mul]

omit [Nonempty ι] [DecidableEq ι] in
theorem intMat_mul_right {μ : Measure ℝ} {F : ℝ → Matrix ι ι ℂ}
    (hint : ∀ p q, Integrable (fun x => F x p q) μ) (B : Matrix ι ι ℂ) :
    intMat μ F * B = intMat μ (fun x => F x * B) := by
  ext p q
  simp only [intMat, Matrix.mul_apply]
  rw [integral_finsetSum _ fun k _ => (hint p k).mul_const _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_mul_const]

omit [Nonempty ι] [DecidableEq ι] in
theorem intMat_mul_left {μ : Measure ℝ} {F : ℝ → Matrix ι ι ℂ}
    (hint : ∀ p q, Integrable (fun x => F x p q) μ) (B : Matrix ι ι ℂ) :
    B * intMat μ F = intMat μ (fun x => B * F x) := by
  ext p q
  simp only [intMat, Matrix.mul_apply]
  rw [integral_finsetSum _ fun k _ => (hint k q).const_mul _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul]

theorem sqrtMat_commute {A : Matrix ι ι ℂ} (hA : ResOK A) : sqrtMat A * A = A * sqrtMat A := by
  have hint : ∀ p q, Integrable (fun y : ℝ => (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) p q) (volume.restrict (Ioi (0 : ℝ))) := by
    intro p q
    simpa [Matrix.smul_apply] using integrable_sqrt_entry hA p q
  unfold sqrtMat
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [intMat_mul_right hint, intMat_mul_left hint]
  ext p q
  unfold intMat
  refine integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
  simp only [Matrix.smul_mul, Matrix.mul_smul, resolvent_commute (hA y (mem_Ioi.mp hy).le)]

end Integrable

section Propagation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem principal_identity (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ)
    (hana : ∀ (M : ℂ → Matrix ι ι ℂ) (D : Set ℂ), IsOpen D → (∀ z ∈ D, ResOK (M z)) →
      (∀ z ∈ D, RectAt M z) → ∀ z ∈ D, RectAt (fun w => Φ (M w)) z)
    (hherm : ∀ A : Matrix ι ι ℂ, A.PosDef → Φ A = 0) {A : Matrix ι ι ℂ} (hA : ResOK A) :
    Φ A = 0 := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι ι ℂ, B = A - 1 := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : Matrix ι ι ℂ, X = (1 / 2 : ℂ) • (B + Bᴴ) := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix ι ι ℂ, Y = (-Complex.I / 2) • (B - Bᴴ) := ⟨_, rfl⟩
  have hXh : Xᴴ = X := by
    rw [hXdef, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    simp
  have hYh : Yᴴ = Y := by
    rw [hYdef, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have : star (-Complex.I / 2) • (Bᴴ - B) = (-Complex.I / 2) • (B - Bᴴ) := by
      rw [← neg_sub, smul_neg, ← neg_smul]
      congr 1
      simp [Complex.ext_iff]
      norm_num
    exact this
  have hBXY : B = X + Complex.I • Y := by
    rw [hXdef, hYdef, smul_smul]
    have : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      field_simp; simp
    rw [this]
    module
  set t0 : ℝ := 1 / (2 * (‖X‖ + 2 * ‖Y‖ + 1)) with ht0
  have hden : 0 < 2 * (‖X‖ + 2 * ‖Y‖ + 1) := by positivity
  have ht0p : 0 < t0 := by positivity
  -- Step 1
  have step1 : ∀ t : ℝ, 0 < t → t ≤ t0 → Φ (1 + (t : ℂ) • B) = 0 := by
    intro t ht htt0
    obtain ⟨M, hM⟩ : ∃ M : ℂ → Matrix ι ι ℂ, M = fun z => 1 + (t : ℂ) • (X + z • Y) := ⟨_, rfl⟩
    have hnorm : ∀ z : ℂ, ‖z‖ < 2 → ‖(t : ℂ) • (X + z • Y)‖ ≤ 1 / 2 := by
      intro z hz
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht.le]
      calc t * ‖X + z • Y‖ ≤ t0 * (‖X‖ + 2 * ‖Y‖) := by
            gcongr
            calc ‖X + z • Y‖ ≤ ‖X‖ + ‖z • Y‖ := norm_add_le _ _
              _ ≤ ‖X‖ + 2 * ‖Y‖ := by
                rw [norm_smul]; gcongr
        _ ≤ 1 / 2 := by
            rw [ht0, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith [norm_nonneg X, norm_nonneg Y]
    have hres : ∀ z ∈ Metric.ball (0 : ℂ) 2, ResOK (M z) := fun z hz => by
      rw [hM]; exact resOK_one_add_of_norm_le (hnorm z (by simpa using hz))
    have hrect : ∀ z ∈ Metric.ball (0 : ℂ) 2, RectAt M z := by
      intro z _ i j
      simp only [hM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact analyticAt_const.add (analyticAt_const.mul (analyticAt_const.add
        (analyticAt_id.mul analyticAt_const)))
    have hRect := hana M _ Metric.isOpen_ball hres hrect
    have hzero : ∀ i j, ∀ z ∈ Metric.ball (0 : ℂ) 2, Φ (M z) i j = 0 := by
      intro i j
      refine eqOn_zero_of_real_zeros (f := fun w => Φ (M w) i j) (D := Metric.ball (0 : ℂ) 2)
        (fun z hz => hRect z hz i j) (convex_ball _ _).isPreconnected (Metric.mem_ball_self (by norm_num)) ?_
      intro ε hε
      refine ⟨min (ε / 2) 1, by positivity, ?_, ?_⟩
      · calc min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
          _ < ε := by linarith
      · set s : ℝ := min (ε / 2) 1 with hs
        have hs1 : s ≤ 1 := min_le_right _ _
        have hs0 : 0 < s := by positivity
        have hsb : ‖(s : ℂ)‖ < 2 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hs0.le]; linarith
        have hH : (M (s : ℂ)).IsHermitian := by
          unfold IsHermitian
          simp only [hM]
          rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_add,
            conjTranspose_smul, hXh, hYh]
          simp
        have hPD : (M (s : ℂ)).PosDef := posDef_of_hermitian_of_isUnit hH
          (fun x hx => hres _ (by simpa using hsb) x hx)
        simp only [hherm _ hPD, Matrix.zero_apply]
    have := hzero
    have hI : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by simp
    have hMI : M Complex.I = 1 + (t : ℂ) • B := by rw [hM, hBXY]
    ext i j
    rw [← hMI]
    exact hzero i j Complex.I hI
  -- Step 2: the line `t ↦ 1 + t B`
  obtain ⟨D', hD'⟩ : ∃ D' : Set ℂ, D' = {z | ResOK (1 + z • B)} := ⟨_, rfl⟩
  have hopen : IsOpen D' := by
    rw [Metric.isOpen_iff]
    intro z hz
    rw [hD'] at hz
    obtain ⟨ε, hε, hεA⟩ := resOK_nhds hz
    refine ⟨ε / (‖B‖ + 1), by positivity, fun w hw => ?_⟩
    rw [hD']
    refine hεA _ ?_
    have : 1 + w • B - (1 + z • B) = (w - z) • B := by module
    rw [this, norm_smul]
    have hwz : ‖w - z‖ ≤ ε / (‖B‖ + 1) := by
      have := Metric.mem_ball.1 hw
      rw [dist_eq_norm] at this; exact this.le
    calc ‖w - z‖ * ‖B‖ ≤ ε / (‖B‖ + 1) * ‖B‖ := by gcongr
      _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg B]
  have hstar : StarConvex ℝ (0 : ℂ) D' := by
    intro z hz a b ha hb hab
    rw [hD'] at hz ⊢
    have hb1 : b ≤ 1 := by linarith
    have := resOK_one_add_smul_mul hz hb hb1
    simpa [Complex.real_smul] using this
  have h0 : (0 : ℂ) ∈ D' := by
    rw [hD']
    simpa using resOK_one (ι := ι)
  have hrect : ∀ z ∈ D', RectAt (fun w : ℂ => 1 + w • B) z := by
    intro z _ i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hRect := hana (fun w : ℂ => 1 + w • B) D' hopen (fun z hz => by rw [hD'] at hz; exact hz) hrect
  have hone : (1 : ℂ) ∈ D' := by
    rw [hD']
    have : (1 : Matrix ι ι ℂ) + (1 : ℂ) • B = A := by rw [one_smul, hB]; abel
    show ResOK (1 + (1 : ℂ) • B)
    rw [this]; exact hA
  have hzero : ∀ i j, ∀ z ∈ D', Φ (1 + z • B) i j = 0 := by
    intro i j
    refine eqOn_zero_of_real_zeros (f := fun w => Φ (1 + w • B) i j) (D := D')
      (fun z hz => hRect z hz i j) (hstar.isPathConnected h0).isConnected.isPreconnected h0 ?_
    intro ε hε
    refine ⟨min (ε / 2) t0, lt_min (by positivity) ht0p, ?_, ?_⟩
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · have := step1 (min (ε / 2) t0) (lt_min (by positivity) ht0p) (min_le_right _ _)
      simp only [this, Matrix.zero_apply]
  have hfin : (1 : Matrix ι ι ℂ) + (1 : ℂ) • B = A := by rw [one_smul, hB]; abel
  ext i j
  have := hzero i j 1 hone
  rw [hfin] at this
  simpa using this

end Propagation

section Instances

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem resOK_of_posDef {A : Matrix ι ι ℂ} (hP : A.PosDef) : ResOK A := by
  intro x hx
  have h1 : ((x : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    (Matrix.PosSemidef.one (n := ι) (R := ℂ)).smul (show (0 : ℂ) ≤ (x : ℂ) by exact_mod_cast hx)
  simpa [add_comm] using (hP.add_posSemidef h1).isUnit

omit [Nonempty ι] in
theorem sqrtMat_phi {A : Matrix ι ι ℂ} (hP : A.PosDef) : sqrtMat A * sqrtMat A * A - 1 = 0 := by
  have hs : sqrtMat A = invSqrtMat hP := resolvent_sqrt_eq hP
  rw [hs, invSqrtMat_mul_self, sub_eq_zero]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP.isUnit)

theorem sqrtMat_mul_self {A : Matrix ι ι ℂ} (hA : ResOK A) : sqrtMat A * sqrtMat A = A⁻¹ := by
  have h := principal_identity (fun A => sqrtMat A * sqrtMat A * A - 1) ?_ (fun A hP => sqrtMat_phi hP) hA
  · have h' : sqrtMat A * sqrtMat A * A = 1 := sub_eq_zero.1 h
    exact (Matrix.inv_eq_left_inv h').symm
  · intro M D hD hRes hM z hz
    have hS : RectAt (fun w => sqrtMat (M w)) z := fun p q =>
      analyticOnNhd_sqrtMat_fam hD hRes hM p q z hz
    exact ((hS.mul hS).mul (hM z hz)).sub (RectAt.const _ z)

omit [Nonempty ι] in
theorem logMat_posDef {A : Matrix ι ι ℂ} (hP : A.PosDef) :
    logMat A = specFun hP.isHermitian (fun t => (Real.log t : ℂ)) := by
  have h := resolvent_log hP one_pos one_pos (0 : Matrix ι ι ℂ)
  have hb : ∀ f : ℝ → ℂ, blockFun 1 1 (0 : Matrix ι ι ℂ) f = f 1 • (1 : Matrix ι ι ℂ) := by
    intro f; unfold blockFun; simp
  have h1 : blockFun 1 1 (0 : Matrix ι ι ℂ) (fun t => (Real.log t : ℂ)) = 0 := by
    rw [hb]; simp
  have h2 : ∀ x : ℝ, blockFun 1 1 (0 : Matrix ι ι ℂ) (fun t => ((t : ℂ) + x)⁻¹) =
      (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    intro x; rw [hb]; push_cast; rfl
  simp only [h1, h2, zero_sub] at h
  unfold logMat
  exact h

omit [Nonempty ι] in
theorem exp_specFun_log {A : Matrix ι ι ℂ} (hP : A.PosDef) :
    NormedSpace.exp (specFun hP.isHermitian (fun t => (Real.log t : ℂ))) = A := by
  have hH := hP.isHermitian
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hUU
  have hunit : IsUnit U := IsUnit.of_mul_eq_one (star U) hUU
  have hD : (NormedSpace.exp (fun i => ((Real.log (hH.eigenvalues i) : ℝ) : ℂ)) : ι → ℂ) =
      fun i => ((hH.eigenvalues i : ℝ) : ℂ) := by
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp,
      Real.exp_log (hP.eigenvalues_pos i)]
  have key : specFun hH (fun t => (Real.log t : ℂ)) =
      U * Matrix.diagonal (fun i => ((Real.log (hH.eigenvalues i) : ℝ) : ℂ)) * U⁻¹ := by
    unfold specFun; rw [hUinv]
  have hA : U * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * U⁻¹ = A := by
    have := specFun_self hH
    unfold specFun at this
    rw [hUinv]; exact this
  rw [key, Matrix.exp_conj U _ hunit, Matrix.exp_diagonal, hD, hA]

omit [Nonempty ι] in
theorem exp_logMat_of_posDef {A : Matrix ι ι ℂ} (hP : A.PosDef) :
    NormedSpace.exp (logMat A) = A := by
  rw [logMat_posDef hP, exp_specFun_log hP]

omit [Nonempty ι] in
theorem analyticAt_of_rectAt' {L : ℂ → Matrix ι ι ℂ} {z : ℂ} (h : RectAt L z) :
    AnalyticAt ℂ L z := by
  let T : (ι → ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℂ).toLinearMap
  have hw : AnalyticAt ℂ (fun w => fun i => fun j => L w i j) z :=
    analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => h i j
  exact (T.analyticAt _).comp hw

omit [Nonempty ι] in
theorem rectAt_of_analyticAt' {F : ℂ → Matrix ι ι ℂ} {z : ℂ} (h : AnalyticAt ℂ F z) :
    RectAt F z := fun i j => by
  let T : Matrix ι ι ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  exact (T.analyticAt _).comp h

theorem exp_logMat {A : Matrix ι ι ℂ} (hA : ResOK A) : NormedSpace.exp (logMat A) = A := by
  have h := principal_identity (fun A => NormedSpace.exp (logMat A) - A) ?_
    (fun A hP => by rw [exp_logMat_of_posDef hP, sub_self]) hA
  · exact sub_eq_zero.1 h
  · intro M D hD hRes hM z hz
    have hL : RectAt (fun w => logMat (M w)) z := fun p q =>
      analyticOnNhd_logMat_fam hD hRes hM p q z hz
    have hLan : AnalyticAt ℂ (fun w => logMat (M w)) z := analyticAt_of_rectAt' hL
    have hE : AnalyticAt ℂ (fun w => NormedSpace.exp (logMat (M w))) z :=
      (NormedSpace.exp_analytic _).comp hLan
    exact (rectAt_of_analyticAt' hE).sub (hM z hz)

theorem isOpen_setOf_resOK {M : ℂ → Matrix ι ι ℂ} (hM : Continuous M) :
    IsOpen {z | ResOK (M z)} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨ε, hε, hεA⟩ := resOK_nhds hz
  have hev : ∀ᶠ w in nhds z, ‖M w - M z‖ < ε := by
    have := (continuous_norm.comp (hM.sub (continuous_const (y := M z)))).continuousAt (x := z)
    refine this.eventually (gt_mem_nhds ?_)
    simp [hε]
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 hev
  exact ⟨r, hr, fun w hw => hεA _ (hr' (Metric.mem_ball.1 hw)).le⟩

theorem logMat_commute {A : Matrix ι ι ℂ} (hA : ResOK A) : logMat A * A = A * logMat A := by
  have hint : ∀ p q, Integrable (fun y : ℝ => (((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) p q) (volume.restrict (Ioi (0 : ℝ))) :=
    fun p q => integrable_log_entry hA p q
  unfold logMat
  rw [Matrix.neg_mul, Matrix.mul_neg, intMat_mul_right hint, intMat_mul_left hint]
  congr 1
  ext p q
  unfold intMat
  refine integral_congr_ae ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, resolvent_commute (hA y (mem_Ioi.mp hy).le)]

omit [Nonempty ι] in
theorem exists_common_eigenvector {S A : Matrix ι ι ℂ} (hc : S * A = A * S) {μ : ℂ}
    {v : ι → ℂ} (hv : v ≠ 0) (hSv : S *ᵥ v = μ • v) :
    ∃ (u : ι → ℂ) (l : ℂ), u ≠ 0 ∧ S *ᵥ u = μ • u ∧ A *ᵥ u = l • u := by
  let E : Submodule ℂ (ι → ℂ) :=
    LinearMap.ker (Matrix.toLin' S - μ • LinearMap.id)
  have hE : ∀ w, w ∈ E ↔ S *ᵥ w = μ • w := by
    intro w
    simp [E, LinearMap.mem_ker, sub_eq_zero]
  have hmaps : ∀ w ∈ E, A *ᵥ w ∈ E := by
    intro w hw
    rw [hE] at hw ⊢
    calc S *ᵥ (A *ᵥ w) = (S * A) *ᵥ w := by rw [Matrix.mulVec_mulVec]
      _ = (A * S) *ᵥ w := by rw [hc]
      _ = A *ᵥ (S *ᵥ w) := by rw [← Matrix.mulVec_mulVec]
      _ = μ • (A *ᵥ w) := by rw [hw, Matrix.mulVec_smul]
  let f : E →ₗ[ℂ] E := (Matrix.toLin' A).restrict hmaps
  have : Nontrivial E := ⟨⟨⟨v, (hE v).2 hSv⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue f
  obtain ⟨w, hw⟩ := hc'.exists_hasEigenvector
  refine ⟨w, c, ?_, (hE _).1 w.2, ?_⟩
  · intro h; exact hw.2 (Subtype.ext h)
  · have h2 := congrArg Subtype.val (Module.End.HasEigenvector.apply_eq_smul hw)
    have h3 : ((f w : E) : ι → ℂ) = A *ᵥ (w : ι → ℂ) := LinearMap.coe_restrict_apply _ _
    rw [h3] at h2
    simpa using h2

omit [Nonempty ι] in
theorem resolvent_mulVec_eigen {A : Matrix ι ι ℂ} {x : ℝ}
    (hu : IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) {u : ι → ℂ} (hu0 : u ≠ 0) {l : ℂ}
    (hAu : A *ᵥ u = l • u) :
    ((x : ℂ) + l ≠ 0) ∧ ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ *ᵥ u = ((x : ℂ) + l)⁻¹ • u := by
  set X := (x : ℂ) • (1 : Matrix ι ι ℂ) + A with hX
  have hXR : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  have hXu : X *ᵥ u = ((x : ℂ) + l) • u := by
    rw [hX, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hAu, add_smul]
  have hne : (x : ℂ) + l ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hXu
    apply hu0
    calc u = (X⁻¹ * X) *ᵥ u := by rw [hXR, Matrix.one_mulVec]
      _ = X⁻¹ *ᵥ (X *ᵥ u) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hXu, Matrix.mulVec_zero]
  refine ⟨hne, ?_⟩
  have : X⁻¹ *ᵥ (X *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, hXR, Matrix.one_mulVec]
  rw [hXu, Matrix.mulVec_smul] at this
  calc X⁻¹ *ᵥ u = ((x : ℂ) + l)⁻¹ • (((x : ℂ) + l) • X⁻¹ *ᵥ u) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [this]

/-- The `1 × 1` matrix `(l)`. -/
def mat1 (l : ℂ) : Matrix Unit Unit ℂ := Matrix.of fun _ _ => l

theorem mat1_apply (l : ℂ) : mat1 l () () = l := rfl

theorem mat1_inv {c : ℂ} (hc : c ≠ 0) : (mat1 c)⁻¹ = mat1 c⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  simp [mat1, Matrix.mul_apply, hc]

theorem mat1_resolvent (x : ℝ) (c : ℂ) :
    (x : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 c = mat1 ((x : ℂ) + c) := by
  ext i j
  simp [mat1]

theorem resOK_sc_iff (c : ℂ) : ResOK (mat1 c) ↔ ∀ x : ℝ, 0 ≤ x → (x : ℂ) + c ≠ 0 := by
  constructor
  · intro h x hx h0
    have := h x hx
    rw [mat1_resolvent, h0, Matrix.isUnit_iff_isUnit_det] at this
    have h00 : mat1 (0 : ℂ) = 0 := by ext i j; simp [mat1]
    rw [h00] at this
    simp at this
  · intro h x hx
    rw [mat1_resolvent, Matrix.isUnit_iff_isUnit_det]
    have : (mat1 ((x : ℂ) + c)).det = (x : ℂ) + c := by simp [mat1, Matrix.det_unique]
    rw [this]
    exact (isUnit_iff_ne_zero).2 (h x hx)

omit [Nonempty ι] in
theorem resOK_sc_of_eigen {A : Matrix ι ι ℂ} (hA : ResOK A) {u : ι → ℂ} (hu0 : u ≠ 0) {l : ℂ}
    (hAu : A *ᵥ u = l • u) : ResOK (mat1 l) :=
  (resOK_sc_iff l).2 fun x hx => (resolvent_mulVec_eigen (hA x hx) hu0 hAu).1

theorem sqrtMat_mulVec_eigen {A : Matrix ι ι ℂ} (hA : ResOK A) {u : ι → ℂ} (hu0 : u ≠ 0)
    {l : ℂ} (hAu : A *ᵥ u = l • u) : sqrtMat A *ᵥ u = (sqrtMat (mat1 l) () ()) • u := by
  have hint : ∀ p q, Integrable (fun y : ℝ => (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) p q) (volume.restrict (Ioi (0 : ℝ))) := by
    intro p q
    simpa [Matrix.smul_apply] using integrable_sqrt_entry hA p q
  funext p
  have hsc : sqrtMat (mat1 l) () () = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ y in Ioi (0 : ℝ), ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((y : ℂ) + l)⁻¹ := by
    have key : ∀ y ∈ Ioi (0 : ℝ), ((((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 l)⁻¹) () ()) =
        ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((y : ℂ) + l)⁻¹ := by
      intro y hy
      have hne := ((resOK_sc_iff l).1 (resOK_sc_of_eigen hA hu0 hAu)) y (mem_Ioi.mp hy).le
      rw [mat1_resolvent, mat1_inv hne]
      simp [mat1]
    have h1 : sqrtMat (mat1 l) () () = ((1 / Real.pi : ℝ) : ℂ) *
        ∫ y in Ioi (0 : ℝ), ((((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
          ((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 l)⁻¹) () ()) := rfl
    rw [h1, setIntegral_congr_fun measurableSet_Ioi key]
  rw [hsc]
  unfold sqrtMat
  rw [Matrix.smul_mulVec, Pi.smul_apply, intMat_mulVec_apply hint u p]
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ∀ y ∈ Ioi (0 : ℝ), ((((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) *ᵥ u) p =
      (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((y : ℂ) + l)⁻¹) * u p := by
    intro y hy
    rw [Matrix.smul_mulVec, (resolvent_mulVec_eigen (hA y (mem_Ioi.mp hy).le) hu0 hAu).2]
    simp [mul_assoc]
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_mul_const]
  ring

theorem logMat_mulVec_eigen {A : Matrix ι ι ℂ} (hA : ResOK A) {u : ι → ℂ} (hu0 : u ≠ 0)
    {l : ℂ} (hAu : A *ᵥ u = l • u) : logMat A *ᵥ u = (logMat (mat1 l) () ()) • u := by
  have hint : ∀ p q, Integrable (fun y : ℝ => (((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) p q) (volume.restrict (Ioi (0 : ℝ))) :=
    fun p q => integrable_log_entry hA p q
  funext p
  have hsc : logMat (mat1 l) () () = -∫ y in Ioi (0 : ℝ),
      (((y : ℂ) + l)⁻¹ - (((1 + y)⁻¹ : ℝ) : ℂ)) := by
    have key : ∀ y ∈ Ioi (0 : ℝ), ((((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 l)⁻¹ -
        (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) () ()) =
        ((y : ℂ) + l)⁻¹ - (((1 + y)⁻¹ : ℝ) : ℂ) := by
      intro y hy
      have hne := ((resOK_sc_iff l).1 (resOK_sc_of_eigen hA hu0 hAu)) y (mem_Ioi.mp hy).le
      rw [mat1_resolvent, mat1_inv hne]
      simp [mat1]
    have h1 : logMat (mat1 l) () () = -∫ y in Ioi (0 : ℝ),
        ((((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 l)⁻¹ -
          (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) () ()) := rfl
    rw [h1, setIntegral_congr_fun measurableSet_Ioi key]
  rw [hsc]
  unfold logMat
  rw [Matrix.neg_mulVec, Pi.neg_apply, intMat_mulVec_apply hint u p]
  have : ∀ y ∈ Ioi (0 : ℝ), ((((y : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) *ᵥ u) p =
      (((y : ℂ) + l)⁻¹ - (((1 + y)⁻¹ : ℝ) : ℂ)) * u p := by
    intro y hy
    rw [Matrix.sub_mulVec, (resolvent_mulVec_eigen (hA y (mem_Ioi.mp hy).le) hu0 hAu).2,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [sub_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi this, integral_mul_const]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [Nonempty ι] in
theorem pow_mulVec_eigen {N : Matrix ι ι ℂ} {u : ι → ℂ} {μ : ℂ} (h : N *ᵥ u = μ • u) (n : ℕ) :
    (N ^ n) *ᵥ u = μ ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

omit [Nonempty ι] in
theorem exp_mulVec_eigen {N : Matrix ι ι ℂ} {u : ι → ℂ} {μ : ℂ} (h : N *ᵥ u = μ • u) :
    NormedSpace.exp N *ᵥ u = NormedSpace.exp μ • u := by
  let T : Matrix ι ι ℂ →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ u
      map_add' := fun M M' => Matrix.add_mulVec M M' u
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) N).mapL T
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const u
  have h3 : (fun n : ℕ => T (((n.factorial : ℂ)⁻¹) • N ^ n)) =
      fun n : ℕ => (((n.factorial : ℂ)⁻¹) • μ ^ n) • u := by
    funext n
    simp only [T, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
    rw [Matrix.smul_mulVec, pow_mulVec_eigen h, smul_assoc]
  rw [h3] at h1
  exact h1.unique h2

theorem mat1_ne_zero {c : ℂ} (hc : ResOK (mat1 c)) : c ≠ 0 := by
  have := (resOK_sc_iff c).1 hc 0 le_rfl
  simpa using this

theorem sqrtMat_sc_sq {c : ℂ} (hc : ResOK (mat1 c)) : (sqrtMat (mat1 c) () ()) ^ 2 = c⁻¹ := by
  have h := sqrtMat_mul_self hc
  have := congrFun (congrFun h ()) ()
  rw [mat1_inv (mat1_ne_zero hc)] at this
  simpa [Matrix.mul_apply, mat1, sq] using this

theorem re_ne_zero_of_sq {μ c : ℂ} (hμ : μ ^ 2 = c⁻¹) (hc : ResOK (mat1 c)) : μ.re ≠ 0 := by
  intro h0
  have hμ' : μ = (μ.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [h0]
  have hc0 := mat1_ne_zero hc
  have h1 : c⁻¹ = -((μ.im : ℂ) ^ 2) := by
    rw [← hμ, hμ']; ring_nf; simp
  have hy : μ.im ≠ 0 := by
    intro hy
    rw [hy] at h1
    simp at h1
    exact hc0 h1
  have h2 : c = -((μ.im : ℂ) ^ 2)⁻¹ := by
    have : c = (c⁻¹)⁻¹ := (inv_inv c).symm
    rw [this, h1, inv_neg]
  have hx := (resOK_sc_iff c).1 hc ((μ.im ^ 2)⁻¹) (by positivity)
  apply hx
  rw [h2]
  push_cast
  ring

theorem exp_logMat_sc {c : ℂ} (hc : ResOK (mat1 c)) : NormedSpace.exp (logMat (mat1 c) () ()) = c := by
  have h := exp_logMat hc
  have hu : (logMat (mat1 c)) *ᵥ (fun _ : Unit => (1 : ℂ)) =
      (logMat (mat1 c) () ()) • (fun _ : Unit => (1 : ℂ)) := by
    funext p
    simp [Matrix.mulVec, dotProduct]
  have := exp_mulVec_eigen hu
  rw [h] at this
  have := congrFun this ()
  simpa [Matrix.mulVec, dotProduct, mat1] using this.symm

theorem im_ne_pi {ν c : ℂ} (hν : NormedSpace.exp ν = c) (hc : ResOK (mat1 c)) :
    ν.im ≠ Real.pi ∧ ν.im ≠ -Real.pi := by
  have hcx : c = Complex.exp ν := by rw [← hν, Complex.exp_eq_exp_ℂ]
  have key : ∀ s : ℝ, ν.im = s → (Real.cos s = -1 ∧ Real.sin s = 0) → False := by
    intro s hs ⟨hcos, hsin⟩
    have hre : c.re = -Real.exp ν.re := by rw [hcx, Complex.exp_re, hs, hcos]; ring
    have him : c.im = 0 := by rw [hcx, Complex.exp_im, hs, hsin]; ring
    have := (resOK_sc_iff c).1 hc (Real.exp ν.re) (Real.exp_pos _).le
    apply this
    apply Complex.ext
    · rw [Complex.add_re, hre, Complex.ofReal_re]; simp
    · rw [Complex.add_im, him, Complex.ofReal_im]; simp
  exact ⟨fun h => key _ h ⟨Real.cos_pi, Real.sin_pi⟩,
    fun h => key _ h ⟨by simp, by simp⟩⟩

theorem resOK_sc_path {l : ℂ} (hl : ResOK (mat1 l)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ResOK (mat1 ((1 - (t : ℂ)) + t * l)) := by
  have h1 : (1 : Matrix Unit Unit ℂ) + (1 : ℂ) • mat1 (l - 1) = mat1 l := by
    ext i j; simp [mat1]
  have h2 := resOK_one_add_smul_mul (B := mat1 (l - 1)) (t := 1) (by rw [h1]; exact hl) ht0 ht1
  have h3 : (1 : Matrix Unit Unit ℂ) + ((t : ℂ) * 1) • mat1 (l - 1) = mat1 ((1 - (t : ℂ)) + t * l) := by
    ext i j; simp [mat1]; ring
  rw [h3] at h2; exact h2

theorem sqrtMat_sc_one : ∃ r : ℝ, 0 ≤ r ∧ sqrtMat (mat1 1) () () = (r : ℂ) := by
  have h1 : sqrtMat (mat1 1) () () = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ y in Ioi (0 : ℝ), ((((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 1)⁻¹) () ()) := rfl
  have key : ∀ y ∈ Ioi (0 : ℝ), ((((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        ((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 1)⁻¹) () ()) =
        (((y ^ (-(1 / 2 : ℝ)) * (y + 1)⁻¹ : ℝ)) : ℂ) := by
    intro y hy
    have hne : (y : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < y + 1 := by have := mem_Ioi.mp hy; linarith
      exact_mod_cast this.ne'
    rw [mat1_resolvent, mat1_inv hne]
    simp [mat1]
  rw [h1, setIntegral_congr_fun measurableSet_Ioi key, integral_complex_ofReal]
  refine ⟨(1 / Real.pi) * ∫ y in Ioi (0 : ℝ), y ^ (-(1 / 2 : ℝ)) * (y + 1)⁻¹, ?_, by push_cast; rfl⟩
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun y hy => ?_)
  have := mem_Ioi.mp hy
  positivity

theorem sqrtMat_sc_re_pos {l : ℂ} (hl : ResOK (mat1 l)) : 0 < (sqrtMat (mat1 l) () ()).re := by
  obtain ⟨M, hM⟩ : ∃ M : ℂ → Matrix Unit Unit ℂ, M = fun z => mat1 ((1 - z) + z * l) := ⟨_, rfl⟩
  have hMc : Continuous M := by
    rw [hM]
    exact continuous_pi fun _ => continuous_pi fun _ => by unfold mat1; fun_prop
  have hD : IsOpen {z | ResOK (M z)} := isOpen_setOf_resOK hMc
  have hRect : ∀ z ∈ {z | ResOK (M z)}, RectAt M z := by
    intro z _ i j
    rw [hM]
    simp only [mat1, Matrix.of_apply]
    fun_prop
  have hfz : AnalyticOnNhd ℂ (fun z => sqrtMat (M z) () ()) {z | ResOK (M z)} :=
    analyticOnNhd_sqrtMat_fam hD (fun z hz => hz) hRect () ()
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ)) ∈ {z | ResOK (M z)} := by
    intro t ht
    show ResOK (M t)
    rw [hM]; exact resOK_sc_path hl ht.1 ht.2
  have hG : ContinuousOn (fun t : ℝ => (sqrtMat (M t) () ()).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn
      ((hfz.continuousOn).comp Complex.continuous_ofReal.continuousOn hmem)
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (sqrtMat (M t) () ()).re ≠ 0 := by
    intro t ht
    have hres : ResOK (mat1 ((1 - (t : ℂ)) + t * l)) := resOK_sc_path hl ht.1 ht.2
    have hMt : M t = mat1 ((1 - (t : ℂ)) + t * l) := by rw [hM]
    rw [hMt]
    exact re_ne_zero_of_sq (sqrtMat_sc_sq hres) hres
  have h0 : 0 < (sqrtMat (M 0) () ()).re := by
    have hM0 : M 0 = mat1 1 := by rw [hM]; simp
    rw [hM0]
    obtain ⟨r, hr, hr'⟩ := sqrtMat_sc_one
    have hsq := sqrtMat_sc_sq (resOK_sc_path hl (le_refl 0) zero_le_one |> fun h => by
      simpa using h)
    rw [hr'] at hsq ⊢
    simp only [Complex.ofReal_re]
    have h2 : (r : ℂ) ^ 2 = 1 := by simpa using hsq
    have : r ^ 2 = 1 := by exact_mod_cast h2
    nlinarith
  by_contra hcon
  push Not at hcon
  have hM1 : M 1 = mat1 l := by rw [hM]; simp
  have hsub := intermediate_value_Icc' (zero_le_one' ℝ) hG
  have h0mem : (0 : ℝ) ∈ Icc ((fun t : ℝ => (sqrtMat (M t) () ()).re) 1)
      ((fun t : ℝ => (sqrtMat (M t) () ()).re) 0) := by
    refine ⟨?_, ?_⟩
    · show (sqrtMat (M ((1 : ℝ) : ℂ)) () ()).re ≤ 0
      rw [Complex.ofReal_one, hM1]; exact hcon
    · show 0 ≤ (sqrtMat (M ((0 : ℝ) : ℂ)) () ()).re
      rw [Complex.ofReal_zero]; exact h0.le
  obtain ⟨t, ht, ht0⟩ := hsub h0mem
  exact hne t ht ht0

theorem logMat_sc_one : logMat (mat1 1) () () = 0 := by
  have h1 : logMat (mat1 1) () () = -∫ y in Ioi (0 : ℝ),
      ((((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 1)⁻¹ -
        (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) () ()) := rfl
  have key : ∀ y ∈ Ioi (0 : ℝ), ((((y : ℂ) • (1 : Matrix Unit Unit ℂ) + mat1 1)⁻¹ -
      (((1 + y)⁻¹ : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) () ()) = 0 := by
    intro y hy
    have hne : (y : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < y + 1 := by have := mem_Ioi.mp hy; linarith
      exact_mod_cast this.ne'
    rw [mat1_resolvent, mat1_inv hne]
    simp [mat1, add_comm]
  rw [h1, setIntegral_congr_fun measurableSet_Ioi key]
  simp

theorem logMat_sc_im_abs_lt {l : ℂ} (hl : ResOK (mat1 l)) :
    |(logMat (mat1 l) () ()).im| < Real.pi := by
  obtain ⟨M, hM⟩ : ∃ M : ℂ → Matrix Unit Unit ℂ, M = fun z => mat1 ((1 - z) + z * l) := ⟨_, rfl⟩
  have hMc : Continuous M := by
    rw [hM]
    exact continuous_pi fun _ => continuous_pi fun _ => by unfold mat1; fun_prop
  have hD : IsOpen {z | ResOK (M z)} := isOpen_setOf_resOK hMc
  have hRect : ∀ z ∈ {z | ResOK (M z)}, RectAt M z := by
    intro z _ i j
    rw [hM]
    simp only [mat1, Matrix.of_apply]
    fun_prop
  have hfz : AnalyticOnNhd ℂ (fun z => logMat (M z) () ()) {z | ResOK (M z)} :=
    analyticOnNhd_logMat_fam hD (fun z hz => hz) hRect () ()
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ((t : ℂ)) ∈ {z | ResOK (M z)} := by
    intro t ht
    show ResOK (M t)
    rw [hM]; exact resOK_sc_path hl ht.1 ht.2
  have hG : ContinuousOn (fun t : ℝ => (logMat (M t) () ()).im) (Icc 0 1) :=
    Complex.continuous_im.comp_continuousOn
      ((hfz.continuousOn).comp Complex.continuous_ofReal.continuousOn hmem)
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (logMat (M t) () ()).im ≠ Real.pi ∧
      (logMat (M t) () ()).im ≠ -Real.pi := by
    intro t ht
    have hres : ResOK (mat1 ((1 - (t : ℂ)) + t * l)) := resOK_sc_path hl ht.1 ht.2
    have hMt : M t = mat1 ((1 - (t : ℂ)) + t * l) := by rw [hM]
    rw [hMt]
    exact im_ne_pi (exp_logMat_sc hres) hres
  have hM0 : M ((0 : ℝ) : ℂ) = mat1 1 := by rw [hM]; simp
  have hM1 : M ((1 : ℝ) : ℂ) = mat1 l := by rw [hM]; simp
  have h0 : (logMat (M ((0 : ℝ) : ℂ)) () ()).im = 0 := by rw [hM0, logMat_sc_one]; simp
  have hpi := Real.pi_pos
  rw [abs_lt]
  have hsub := intermediate_value_Icc (zero_le_one' ℝ) hG
  have hsub' := intermediate_value_Icc' (zero_le_one' ℝ) hG
  constructor
  · by_contra hcon
    push Not at hcon
    have hmem' : -Real.pi ∈ Icc ((fun t : ℝ => (logMat (M t) () ()).im) 1)
        ((fun t : ℝ => (logMat (M t) () ()).im) 0) := by
      refine ⟨?_, ?_⟩
      · show (logMat (M ((1 : ℝ) : ℂ)) () ()).im ≤ -Real.pi
        rw [hM1]; exact hcon
      · show -Real.pi ≤ (logMat (M ((0 : ℝ) : ℂ)) () ()).im
        rw [h0]; linarith
    obtain ⟨t, ht, ht0⟩ := hsub' hmem'
    exact (hne t ht).2 ht0
  · by_contra hcon
    push Not at hcon
    have hmem' : Real.pi ∈ Icc ((fun t : ℝ => (logMat (M t) () ()).im) 0)
        ((fun t : ℝ => (logMat (M t) () ()).im) 1) := by
      refine ⟨?_, ?_⟩
      · show (logMat (M ((0 : ℝ) : ℂ)) () ()).im ≤ Real.pi
        rw [h0]; linarith
      · show Real.pi ≤ (logMat (M ((1 : ℝ) : ℂ)) () ()).im
        rw [hM1]; exact hcon
    obtain ⟨t, ht, ht0⟩ := hsub hmem'
    exact (hne t ht).1 ht0
  
omit [Nonempty ι] [DecidableEq ι] in
theorem eq_of_smul_eq {u : ι → ℂ} (hu0 : u ≠ 0) {a b : ℂ} (h : a • u = b • u) : a = b := by
  obtain ⟨p, hp⟩ : ∃ p, u p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (funext hcon)
  have := congrFun h p
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hp this

/-- **The principal inverse square root.** For a matrix `A` with `x + A` invertible for all
`x ≥ 0` (equivalently, with no eigenvalue in `(-∞, 0]`), `π⁻¹ ∫₀^∞ x^{-1/2} (x + A)⁻¹ dx` squares to
`A⁻¹`, commutes with `A`, and all its eigenvalues have positive real part. -/
theorem sqrtMat_principal {A : Matrix ι ι ℂ} (hA : ResOK A) :
    sqrtMat A * sqrtMat A = A⁻¹ ∧ sqrtMat A * A = A * sqrtMat A ∧
      ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → sqrtMat A *ᵥ v = μ • v → 0 < μ.re := by
  refine ⟨sqrtMat_mul_self hA, sqrtMat_commute hA, fun μ v hv hSv => ?_⟩
  obtain ⟨u, l, hu0, hSu, hAu⟩ := exists_common_eigenvector (sqrtMat_commute hA) hv hSv
  have h1 := sqrtMat_mulVec_eigen hA hu0 hAu
  rw [hSu] at h1
  have : μ = sqrtMat (mat1 l) () () := eq_of_smul_eq hu0 h1
  rw [this]
  exact sqrtMat_sc_re_pos (resOK_sc_of_eigen hA hu0 hAu)

/-- **The principal logarithm.** For a matrix `A` with `x + A` invertible for all `x ≥ 0`,
`-∫₀^∞ ((x + A)⁻¹ - (1 + x)⁻¹) dx` is a logarithm of `A` commuting with `A`, all of whose
eigenvalues have imaginary part in `(-π, π)`. -/
theorem logMat_principal {A : Matrix ι ι ℂ} (hA : ResOK A) :
    NormedSpace.exp (logMat A) = A ∧ logMat A * A = A * logMat A ∧
      ∀ (μ : ℂ) (v : ι → ℂ), v ≠ 0 → logMat A *ᵥ v = μ • v → |μ.im| < Real.pi := by
  refine ⟨exp_logMat hA, logMat_commute hA, fun μ v hv hLv => ?_⟩
  obtain ⟨u, l, hu0, hLu, hAu⟩ := exists_common_eigenvector (logMat_commute hA) hv hLv
  have h1 := logMat_mulVec_eigen hA hu0 hAu
  rw [hLu] at h1
  have : μ = logMat (mat1 l) () () := eq_of_smul_eq hu0 h1
  rw [this]
  exact logMat_sc_im_abs_lt (resOK_sc_of_eigen hA hu0 hAu)

end Instances

section Covariance

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

theorem resOK_covOp (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) : ResOK (covOp G a aT ν α φ Q P) :=
  fun _ hx => (decCov_one_eq hfam hφ hδ hsm hU hx).1

/-- `C^{1/2}(1) = π⁻¹ ∫₀^∞ x^{-1/2} (x + 𝒜)⁻¹ dx` for every (complex) data. -/
theorem decCovSqrt_one_eq_sqrtMat (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) :
    decCovSqrt G a aT ν α (fun _ => 1) φ Q P = sqrtMat (covOp G a aT ν α φ Q P) := by
  unfold decCovSqrt sqrtMat
  congr 1
  ext p q
  unfold intMat
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [decSqrtInt]
  rw [(decCov_one_eq hfam hφ hδ hsm hU (mem_Ioi.mp hx).le).2]

omit [DecidableEq κι] in
theorem resolvent_one_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ℝ) (hx : 0 ≤ x) :
    ((x : ℂ) • (1 : Matrix ι ι ℂ) + 1)⁻¹ = (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  have h1x : ((1 + x : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < 1 + x := by linarith
    exact_mod_cast this.ne'
  refine Matrix.inv_eq_right_inv ?_
  have : ((x : ℂ) • (1 : Matrix ι ι ℂ) + 1) = ((1 + x : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
    push_cast; rw [add_smul, one_smul, add_comm]
  rw [this]
  simp only [smul_mul_assoc, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  push_cast at h1x ⊢
  rw [mul_inv_cancel₀ h1x, one_smul]

theorem decLog_one_eq_logMat_aux [Nonempty (κι × Fin N)]
    (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) :
    decLog G a aT ν α (fun _ => 1) φ Q P = logMat (covOp G a aT ν α φ Q P) := by
  have D0 := hfam 0 le_rfl
  have hak : 0 < a k := by
    have := D0.st.ha k D0.st.hk le_rfl
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D0.st.haT1
    positivity
  have hc2 : 0 < a k + aT / (L : ℝ) ^ 2 := by linarith
  have H : CovStanding G a aT ν α 0 (fun _ => 1) δ φ Q P := ⟨hfam, hφ, hδ, hsm, hU.toIsUnitLattice⟩
  have hres := resOK_covOp hfam hφ hδ hsm hU
  have hdec : ∀ x ∈ Ioi (0 : ℝ), decCov G a aT x ν α (fun _ => 1) φ Q P =
      ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + covOp G a aT ν α φ Q P)⁻¹ :=
    fun x hx => (decCov_one_eq hfam hφ hδ hsm hU (mem_Ioi.mp hx).le).2
  have hcov : ∀ x : ℝ, covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) =
      blockFun (a k) (a k + aT / (L : ℝ) ^ 2) (liftOp N P) (fun t => ((t : ℂ) + x)⁻¹) := by
    intro x
    unfold covA blockFun
    push_cast
    ring_nf
  set Pm : Matrix (κι × Fin N) (κι × Fin N) ℂ := liftOp N P with hPm
  set A𝒜 := covOp G a aT ν α φ Q P with hAc
  have hone : logMat (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) = 0 := by
    ext p q
    have : ∀ x ∈ Ioi (0 : ℝ), ((((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + 1)⁻¹ -
        (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) p q) = 0 := by
      intro x hx
      rw [resolvent_one_eq x (mem_Ioi.mp hx).le, sub_self]; rfl
    have h1 : logMat (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) p q = -∫ x in Ioi (0 : ℝ),
        ((((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + 1)⁻¹ -
        (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) p q) := rfl
    rw [h1, setIntegral_congr_fun measurableSet_Ioi this]
    simp
  have hL := resolvent_log (A := (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) Matrix.PosDef.one hak hc2 Pm
  have hspec : specFun (Matrix.PosDef.one : (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ).PosDef).isHermitian
      (fun t => (Real.log t : ℂ)) = 0 := by
    rw [← logMat_posDef Matrix.PosDef.one, hone]
  rw [hspec] at hL
  have hF : ∀ x ∈ Ioi (0 : ℝ), ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + 1)⁻¹ -
      blockFun (a k) (a k + aT / (L : ℝ) ^ 2) Pm (fun t => ((t : ℂ) + x)⁻¹) =
      (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) -
        covA (a k) (aT / (L : ℝ) ^ 2) x Pm := by
    intro x hx
    rw [resolvent_one_eq x (mem_Ioi.mp hx).le, hcov x]
  have key : ∀ p q, blockFun (a k) (a k + aT / (L : ℝ) ^ 2) Pm (fun t => (Real.log t : ℂ)) p q =
      ∫ x in Ioi (0 : ℝ), (((((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) -
        covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q) := by
    intro p q
    have h := congrFun (congrFun hL p) q
    have h' : (blockFun (a k) (a k + aT / (L : ℝ) ^ 2) Pm (fun t => (Real.log t : ℂ)) -
        intMat (volume.restrict (Ioi (0 : ℝ))) (fun x =>
          ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + 1)⁻¹ -
          blockFun (a k) (a k + aT / (L : ℝ) ^ 2) Pm (fun t => ((t : ℂ) + x)⁻¹))) p q = 0 := h
    have h2 : intMat (volume.restrict (Ioi (0 : ℝ))) (fun x =>
          ((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + 1)⁻¹ -
          blockFun (a k) (a k + aT / (L : ℝ) ^ 2) Pm (fun t => ((t : ℂ) + x)⁻¹)) p q =
        ∫ x in Ioi (0 : ℝ), (((((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) -
          covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q) := by
      unfold intMat
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only []
      rw [hF x hx]
    rw [Matrix.sub_apply, h2] at h'
    exact sub_eq_zero.1 h'
  -- integrability
  have hF1 : ∀ p q, Integrable (fun x : ℝ => (((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + A𝒜)⁻¹ -
      (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) p q)
      (volume.restrict (Ioi (0 : ℝ))) := fun p q => integrable_log_entry hres p q
  have hF2 : ∀ p q, Integrable (fun x : ℝ => (((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + A𝒜)⁻¹ -
      covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q) (volume.restrict (Ioi (0 : ℝ))) := by
    intro p q
    refine (integrable_decSub H p q).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
    simp only [hdec x hx]
    rfl
  ext p q
  have e1 : decLog G a aT ν α (fun _ => 1) φ Q P p q =
      blockFun (a k) (a k + aT / (L : ℝ) ^ 2) Pm (fun t => (Real.log t : ℂ)) p q -
        ∫ x in Ioi (0 : ℝ), (decCov G a aT x ν α (fun _ => 1) φ Q P -
          covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q := by
    unfold decLog blockFun
    simp only [Matrix.sub_apply, Matrix.add_apply]
    rfl
  have e2 : logMat A𝒜 p q = -∫ x in Ioi (0 : ℝ), (((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + A𝒜)⁻¹ -
      (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) p q := rfl
  have e3 : ∫ x in Ioi (0 : ℝ), (decCov G a aT x ν α (fun _ => 1) φ Q P -
          covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q =
      ∫ x in Ioi (0 : ℝ), (((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + A𝒜)⁻¹ -
          covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [hdec x hx]
  have e4 : ∫ x in Ioi (0 : ℝ), (((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + A𝒜)⁻¹ -
          covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q =
      (∫ x in Ioi (0 : ℝ), (((x : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) + A𝒜)⁻¹ -
      (((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ)) p q) +
      ∫ x in Ioi (0 : ℝ), (((((1 + x)⁻¹ : ℝ) : ℂ) • (1 : Matrix (κι × Fin N) (κι × Fin N) ℂ) -
        covA (a k) (aT / (L : ℝ) ^ 2) x Pm) p q) := by
    rw [← integral_add (hF1 p q)]
    · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [Matrix.sub_apply]; ring
    · refine ((hF2 p q).sub (hF1 p q)).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Matrix.sub_apply, Pi.sub_apply]; ring
  rw [e1, e3, e4, ← key p q, e2]
  ring

/-- `𝕃(1) = -∫₀^∞ ((x + 𝒜)⁻¹ - (1 + x)⁻¹) dx` for every (complex) data. -/
theorem decLog_one_eq_logMat
    (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) :
    decLog G a aT ν α (fun _ => 1) φ Q P = logMat (covOp G a aT ν α φ Q P) := by
  rcases isEmpty_or_nonempty (κι × Fin N) with h | h
  · exact Matrix.subsingleton_of_empty_left.elim _ _
  · exact decLog_one_eq_logMat_aux hfam hφ hδ hsm hU

/-- **I-4c (iv), complex data, the square root.** For every admissible (complex) data, with no
positivity hypothesis: `C^{1/2}(1)² = C(1) = 𝒜⁻¹`, `C^{1/2}(1)` commutes with `𝒜` and every
eigenvalue of `C^{1/2}(1)` has positive real part, i.e. `C^{1/2}(1)` is the principal inverse square
root of `𝒜`. -/
theorem decCovSqrt_one_principal
    (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) :
    decCovSqrt G a aT ν α (fun _ => 1) φ Q P * decCovSqrt G a aT ν α (fun _ => 1) φ Q P =
        decCov G a aT 0 ν α (fun _ => 1) φ Q P ∧
      decCovSqrt G a aT ν α (fun _ => 1) φ Q P * covOp G a aT ν α φ Q P =
        covOp G a aT ν α φ Q P * decCovSqrt G a aT ν α (fun _ => 1) φ Q P ∧
      ∀ (μ : ℂ) (v : κι × Fin N → ℂ), v ≠ 0 →
        decCovSqrt G a aT ν α (fun _ => 1) φ Q P *ᵥ v = μ • v → 0 < μ.re := by
  have hC0 : decCov G a aT 0 ν α (fun _ => 1) φ Q P = (covOp G a aT ν α φ Q P)⁻¹ := by
    have := (decCov_one_eq hfam hφ hδ hsm hU (le_refl (0 : ℝ))).2
    simpa using this
  rw [hC0, decCovSqrt_one_eq_sqrtMat hfam hφ hδ hsm hU]
  rcases isEmpty_or_nonempty (κι × Fin N) with h | h
  · refine ⟨Matrix.subsingleton_of_empty_left.elim _ _, Matrix.subsingleton_of_empty_left.elim _ _,
      fun μ v hv _ => absurd (funext fun i => isEmptyElim i) hv⟩
  · exact sqrtMat_principal (resOK_covOp hfam hφ hδ hsm hU)

/-- **I-4c (iv), complex data, the logarithm.** `exp 𝕃(1) = 𝒜`, `𝕃(1)` commutes with `𝒜` and all
eigenvalues of `𝕃(1)` have imaginary part in `(-π, π)`: `𝕃(1)` is the principal logarithm of `𝒜`. -/
theorem decLog_one_principal
    (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) :
    NormedSpace.exp (decLog G a aT ν α (fun _ => 1) φ Q P) = covOp G a aT ν α φ Q P ∧
      decLog G a aT ν α (fun _ => 1) φ Q P * covOp G a aT ν α φ Q P =
        covOp G a aT ν α φ Q P * decLog G a aT ν α (fun _ => 1) φ Q P ∧
      ∀ (μ : ℂ) (v : κι × Fin N → ℂ), v ≠ 0 →
        decLog G a aT ν α (fun _ => 1) φ Q P *ᵥ v = μ • v → |μ.im| < Real.pi := by
  rw [decLog_one_eq_logMat hfam hφ hδ hsm hU]
  rcases isEmpty_or_nonempty (κι × Fin N) with h | h
  · refine ⟨Matrix.subsingleton_of_empty_left.elim _ _, Matrix.subsingleton_of_empty_left.elim _ _,
      fun μ v hv _ => absurd (funext fun i => isEmptyElim i) hv⟩
  · exact logMat_principal (resOK_covOp hfam hφ hδ hsm hU)

end Covariance

end Balaban.Localization
