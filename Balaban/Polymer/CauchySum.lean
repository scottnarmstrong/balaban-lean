module

public import Balaban.Analysis.Cauchy

/-!
# Weighted Cauchy estimates for sums of analytic functions

If `f_t` are analytic on a polydisc `Δ` of polyradius `r` and `∑_t w_t ‖f_t‖ ≤ A` on `Δ`, then
`∑_t w_t ‖∂_i f_t(0)‖ ≤ A / r_i` and, for `i ≠ j`, `∑_t w_t ‖∂_j ∂_i f_t(0)‖ ≤ A / (r_i r_j)`.
The proof applies the one-function Cauchy estimates to `∑_t c_t f_t` with phases `c_t` chosen so
that `c_t ∂ f_t(0) = w_t ‖∂ f_t(0)‖`.
-/

@[expose] public section

noncomputable section

open Finset

namespace Balaban.Polymer

open Balaban.Analysis

/-- A complex phase `c` with `‖c‖ ≤ w` and `c u = w ‖u‖`. -/
theorem exists_phase (u : ℂ) {w : ℝ} (hw : 0 ≤ w) : ∃ c : ℂ, ‖c‖ ≤ w ∧ c * u = (w * ‖u‖ : ℝ) := by
  by_cases hu : u = 0
  · exact ⟨0, by simpa using hw, by simp [hu]⟩
  · refine ⟨(w * ‖u‖ : ℝ) / u, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : 0 < ‖u‖ := norm_pos_iff.mpr hu
      rw [mul_div_assoc, div_self this.ne', mul_one]
    · field_simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ} {T : Type*}

/-- The first derivative at the centre, in the direction `i`. -/
def D1 (i : ι) (f : (ι → ℂ) → ℂ) : ℂ := fderiv ℂ f 0 (Pi.single i 1)

/-- The mixed second derivative at the centre. -/
def D2 (i j : ι) (f : (ι → ℂ) → ℂ) : ℂ :=
  fderiv ℂ (fun w => fderiv ℂ f w (Pi.single i 1)) 0 (Pi.single j 1)

theorem sum_norm_D1_le (hr : ∀ i, 0 < r i) (s : Finset T) (f : T → (ι → ℂ) → ℂ)
    (hf : ∀ t, AnalyticOnNhd ℂ (f t) (polydisc 0 r)) (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) {A : ℝ}
    (hA : ∀ z ∈ polydisc (0 : ι → ℂ) r, ∑ t ∈ s, ‖f t z‖ * w t ≤ A) (i : ι) :
    ∑ t ∈ s, w t * ‖D1 i (f t)‖ ≤ A / r i := by
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k
  choose c hc1 hc2 using fun t => exists_phase (D1 i (f t)) (hw t)
  set Ψ : (ι → ℂ) → ℂ := fun z => ∑ t ∈ s, c t * f t z with hΨ
  have hΨa : AnalyticOnNhd ℂ Ψ (polydisc 0 r) :=
    Finset.analyticOnNhd_fun_sum _ (fun t _ => analyticOnNhd_const.mul (hf t))
  have hbd : ∀ z ∈ polydisc (0 : ι → ℂ) r, ‖Ψ z‖ ≤ A := fun z hz =>
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun t _ => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hc1 t) (norm_nonneg _))).trans (hA z hz))
  have h1 := norm_fderiv_single_le hΨa.differentiableOn hbd h0 i
  simp only [Pi.zero_apply, norm_zero, sub_zero] at h1
  have h2 : fderiv ℂ Ψ 0 (Pi.single i 1) = ∑ t ∈ s, c t * D1 i (f t) := by
    rw [hΨ, fderiv_fun_sum (fun t _ => ((analyticOnNhd_const.mul (hf t)) 0 h0).differentiableAt)]
    simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [fderiv_const_mul ((hf t) 0 h0).differentiableAt]
    rfl
  have h3 : ∑ t ∈ s, c t * D1 i (f t) = ((∑ t ∈ s, w t * ‖D1 i (f t)‖ : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun t _ => by rw [hc2 t]; push_cast; ring)
  rw [h2, h3, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun t _ => mul_nonneg (hw t) (norm_nonneg _)))] at h1
  exact h1

theorem sum_norm_D2_le [CompleteSpace ℂ] (hr : ∀ i, 0 < r i) (s : Finset T)
    (f : T → (ι → ℂ) → ℂ)
    (hf : ∀ t, AnalyticOnNhd ℂ (f t) (polydisc 0 r)) (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) {A : ℝ}
    (hA : ∀ z ∈ polydisc (0 : ι → ℂ) r, ∑ t ∈ s, ‖f t z‖ * w t ≤ A) {i j : ι} (hij : i ≠ j) :
    ∑ t ∈ s, w t * ‖D2 i j (f t)‖ ≤ A / r i / r j := by
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k
  have hopen := isOpen_polydisc (0 : ι → ℂ) r
  choose c hc1 hc2 using fun t => exists_phase (D2 i j (f t)) (hw t)
  set Ψ : (ι → ℂ) → ℂ := fun z => ∑ t ∈ s, c t * f t z with hΨ
  have hΨa : AnalyticOnNhd ℂ Ψ (polydisc 0 r) :=
    Finset.analyticOnNhd_fun_sum _ (fun t _ => analyticOnNhd_const.mul (hf t))
  have hbd : ∀ z ∈ polydisc (0 : ι → ℂ) r, ‖Ψ z‖ ≤ A := fun z hz =>
    (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun t _ => by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hc1 t) (norm_nonneg _))).trans (hA z hz))
  have h1 := norm_mixed_fderiv_le hr hΨa hbd hij
  -- derivative of the sum
  have hev : (fun w => fderiv ℂ Ψ w (Pi.single i 1)) =ᶠ[nhds (0 : ι → ℂ)]
      fun w => ∑ t ∈ s, c t * fderiv ℂ (f t) w (Pi.single i 1) := by
    filter_upwards [hopen.mem_nhds h0] with z hz
    rw [hΨ, fderiv_fun_sum (fun t _ => ((analyticOnNhd_const.mul (hf t)) z hz).differentiableAt)]
    simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [fderiv_const_mul ((hf t) z hz).differentiableAt]
    rfl
  have hdiff : ∀ t, DifferentiableAt ℂ (fun w => c t * fderiv ℂ (f t) w (Pi.single i 1)) 0 :=
    fun t => (((hf t).fderiv 0 h0).differentiableAt.clm_apply
      (differentiableAt_const _)).const_mul _
  have h2 : fderiv ℂ (fun w => fderiv ℂ Ψ w (Pi.single i 1)) 0 (Pi.single j 1) =
      ∑ t ∈ s, c t * D2 i j (f t) := by
    rw [hev.fderiv_eq, fderiv_fun_sum (fun t _ => hdiff t)]
    simp only [_root_.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [fderiv_const_mul (((hf t).fderiv 0 h0).differentiableAt.clm_apply
      (differentiableAt_const _))]
    rfl
  have h3 : ∑ t ∈ s, c t * D2 i j (f t) = ((∑ t ∈ s, w t * ‖D2 i j (f t)‖ : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl (fun t _ => by rw [hc2 t]; push_cast; ring)
  rw [h2, h3, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun t _ => mul_nonneg (hw t) (norm_nonneg _)))] at h1
  exact h1

end Balaban.Polymer
