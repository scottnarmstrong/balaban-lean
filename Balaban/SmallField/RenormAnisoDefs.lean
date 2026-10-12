/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseDefs

/-!
# I-6 on the anisotropic small-field domain: the polydisc and the scaled Cauchy estimates

The class domain `Ξᶜ` (P3 p. 74, (4.26); `CLASS-RULINGS.md` Q-D) allows, around the reference
point `(e_{i₀}, ν e_{i₀})` in the variables `(ψ, b)`, `b = ν h`, a spin perturbation and a
transverse field perturbation of size `O(ε_j)`, but a longitudinal field perturbation `b_{i₀} - ν`
only of size `O(ε_j²)`.  The isotropic `Tube i₀ ν ρ X` of the landed I-6 therefore has radius
`ρ ≲ ε_j²`.  This file replaces it by the anisotropic polydisc.

* `anisoWt i₀ r X`: the polyradius, `r` on the spin coordinates and on the transverse field
  coordinates `b_i` (`i ≠ i₀`), `r²` on the longitudinal coordinate `b_{i₀}`;
* `polyAniso i₀ ν r X`: the polydisc of polyradius `anisoWt i₀ r X` around `refPt i₀ ν X`;
* `TubeAniso i₀ ν r X`: its orbit under the admissible complex rotations (the analogue of
  `Tube`);
* `anisoScale`, `anisoUnscale`: the diagonal rescaling by the polyradius and its inverse;
  `refPt_add_anisoScale_mem_iff`, `polyAniso_eq_image`: the rescaling maps the unit ball onto the
  polydisc;
* `anisoGauge i₀ r X z = ‖anisoUnscale i₀ r X z‖ = max_p |z_p| / r_p`, the gauge of the polydisc;
* the scaled Cauchy estimates: for `f` analytic on the polydisc and bounded there by `M`,
  `aniso_taylor_first`, `aniso_taylor_second`, `aniso_taylor_diff` (Taylor remainders in the
  gauge), `aniso_norm_fderiv_le`, `aniso_norm_D2_le` (`‖f' v‖ ≤ M g(v)`,
  `‖f''(v, w)‖ ≤ 4 M g(v) g(w)`), and the tensor bounds `aniso_norm_tensA_le`,
  `aniso_norm_D2_basis_le` (radius `r` in every spin and transverse direction).

They are obtained by applying the landed ball estimates of `TaylorCauchy` to
`w ↦ f (c + S w)` on the unit ball, for a general continuous linear `S` with a right inverse
(`taylor_first_scale`, ...).  The isotropic tube of radius `r²` lies in `TubeAniso`
(`tube_subset_tubeAniso`), so the shape lemmas and the Ward identity of `TermOK` apply unchanged
(`termOK_of_tubeAniso`).
-/

@[expose] public section

open Metric Set

namespace Balaban.SmallField

variable {d N : ℕ}

/-! ### Cauchy estimates on the image of the unit ball under a linear map -/

section Scaled

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → ℂ} {c : E} {S Sinv : E →L[ℂ] E} {M : ℝ}

theorem analyticOnNhd_comp_scale (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w)) :
    AnalyticOnNhd ℂ (fun w => f (c + S w)) (ball 0 1) := by
  intro w hw
  have h1 : AnalyticAt ℂ (fun w => c + S w) w := analyticAt_const.add (S.analyticAt w)
  exact AnalyticAt.comp (g := f) (f := fun w => c + S w) (hf w (by simpa using hw)) h1

theorem bound_comp_scale (hM : ∀ w : E, ‖w‖ < 1 → ‖f (c + S w)‖ ≤ M) :
    ∀ w ∈ ball (0 : E) 1, ‖(fun w => f (c + S w)) w‖ ≤ M :=
  fun w hw => hM w (by simpa using hw)

/-- The image of the unit ball contains the ball of radius `1 / (‖S⁻¹‖ + 1)` around `c`. -/
theorem analyticOnNhd_ball_of_scale (hS : ∀ z, S (Sinv z) = z)
    (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w)) :
    AnalyticOnNhd ℂ f (ball c (1 / (‖Sinv‖ + 1))) := by
  intro x hx
  have hx' : ‖x - c‖ < 1 / (‖Sinv‖ + 1) := by simpa [dist_eq_norm] using hx
  have hpos : 0 < ‖Sinv‖ + 1 := by positivity
  have hw : ‖Sinv (x - c)‖ < 1 := by
    calc ‖Sinv (x - c)‖ ≤ ‖Sinv‖ * ‖x - c‖ := Sinv.le_opNorm _
      _ ≤ (‖Sinv‖ + 1) * ‖x - c‖ := by nlinarith [norm_nonneg Sinv, norm_nonneg (x - c)]
      _ < (‖Sinv‖ + 1) * (1 / (‖Sinv‖ + 1)) := mul_lt_mul_of_pos_left hx' hpos
      _ = 1 := by field_simp
  have h := hf _ hw
  have e : c + (x - c) = x := by abel
  rwa [hS, e] at h

theorem line_comp_scale (w : E) :
    (fun t : ℂ => (fun w => f (c + S w)) ((0 : E) + t • w)) = fun t : ℂ => f (c + t • S w) := by
  funext t
  simp [map_smul]

theorem fderiv_comp_scale (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w)) (w : E) :
    fderiv ℂ (fun w => f (c + S w)) 0 w = fderiv ℂ f c (S w) := by
  have hg := analyticOnNhd_comp_scale hf
  have h1 := iteratedDeriv_one_line (f := fun w => f (c + S w)) (c := (0 : E)) (z := w)
    (hg 0 (mem_ball_self one_pos)).differentiableAt
  have hc : DifferentiableAt ℂ f c := by
    have := (hf 0 (by simp)).differentiableAt
    simpa using this
  have h2 := iteratedDeriv_one_line (f := f) (c := c) (z := S w) hc
  rw [← h1, ← h2, line_comp_scale]

theorem D2_comp_scale_diag (hS : ∀ z, S (Sinv z) = z)
    (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w)) (w : E) :
    D2 (fun w => f (c + S w)) 0 w w = D2 f c (S w) (S w) := by
  have hg := analyticOnNhd_comp_scale hf
  have h1 := iteratedDeriv_two_line (f := fun w => f (c + S w)) (c := (0 : E)) (z := w) one_pos hg
  have h2 := iteratedDeriv_two_line (f := f) (c := c) (z := S w) (ρ := 1 / (‖Sinv‖ + 1))
    (by positivity) (analyticOnNhd_ball_of_scale hS hf)
  rw [← h1, ← h2, line_comp_scale]

theorem D2_comp_scale (hS : ∀ z, S (Sinv z) = z)
    (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w)) (v w : E) :
    D2 (fun w => f (c + S w)) 0 v w = D2 f c (S v) (S w) := by
  have hg := analyticOnNhd_comp_scale hf
  have hga : AnalyticAt ℂ (fun w => f (c + S w)) 0 := hg 0 (mem_ball_self one_pos)
  have hfa : AnalyticAt ℂ f c :=
    analyticOnNhd_ball_of_scale hS hf c (mem_ball_self (by positivity))
  have p1 := D2_comp_scale_diag hS hf (v + w)
  have p2 := D2_comp_scale_diag hS hf (v - w)
  have sg := D2_symm hga w v
  have sf := D2_symm hfa (S w) (S v)
  simp only [map_add, map_sub, D2_add_left, D2_add_right, D2_sub_left, D2_sub_right] at p1 p2
  linear_combination (p1 - p2) / 4 - sg / 2 + sf / 2

/-- First-order Taylor remainder on the image of the unit ball. -/
theorem taylor_first_scale (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w))
    (hM : ∀ w : E, ‖w‖ < 1 → ‖f (c + S w)‖ ≤ M) {w : E} (hw : ‖w‖ ≤ 1 / 2) :
    ‖f (c + S w) - f c - fderiv ℂ f c (S w)‖ ≤ 2 * M * ‖w‖ ^ 2 := by
  have h := taylor_first one_pos (analyticOnNhd_comp_scale hf) (bound_comp_scale hM) hw
  rw [fderiv_comp_scale hf w] at h
  simpa using h

/-- Second-order Taylor remainder on the image of the unit ball. -/
theorem taylor_second_scale (hS : ∀ z, S (Sinv z) = z)
    (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w))
    (hM : ∀ w : E, ‖w‖ < 1 → ‖f (c + S w)‖ ≤ M) {w : E} (hw : ‖w‖ ≤ 1 / 2) :
    ‖f (c + S w) - f c - fderiv ℂ f c (S w) - (1 / 2 : ℂ) * D2 f c (S w) (S w)‖ ≤
      2 * M * ‖w‖ ^ 3 := by
  have h := taylor_second one_pos (analyticOnNhd_comp_scale hf) (bound_comp_scale hM) hw
  rw [fderiv_comp_scale hf w, D2_comp_scale hS hf w w] at h
  simpa using h

/-- Cauchy estimate for the first derivative on the image of the unit ball. -/
theorem norm_fderiv_scale_le (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w))
    (hM : ∀ w : E, ‖w‖ < 1 → ‖f (c + S w)‖ ≤ M) (w : E) :
    ‖fderiv ℂ f c (S w)‖ ≤ M * ‖w‖ := by
  have h := norm_fderiv_apply_le one_pos (analyticOnNhd_comp_scale hf) (bound_comp_scale hM) w
  rw [fderiv_comp_scale hf w] at h
  simpa using h

/-- Cauchy estimate for the second derivative on the image of the unit ball. -/
theorem norm_D2_scale_le (hS : ∀ z, S (Sinv z) = z)
    (hf : ∀ w : E, ‖w‖ < 1 → AnalyticAt ℂ f (c + S w))
    (hM : ∀ w : E, ‖w‖ < 1 → ‖f (c + S w)‖ ≤ M) (v w : E) :
    ‖D2 f c (S v) (S w)‖ ≤ 4 * M * ‖v‖ * ‖w‖ := by
  have h := norm_D2_le one_pos (analyticOnNhd_comp_scale hf) (bound_comp_scale hM) v w
  rw [D2_comp_scale hS hf v w] at h
  simpa using h

end Scaled

/-! ### The anisotropic polydisc and its rotation orbit -/

/-- **The polyradius of the anisotropic polydisc**: `r` on the spin coordinates `ψ_i(x)` and on
the transverse field coordinates `b_i`, `i ≠ i₀`; `r²` on the longitudinal coordinate `b_{i₀}`. -/
def anisoWt (i₀ : Fin N) (r : ℝ) (X : Finset (Site d)) : Idx d N X → ℝ :=
  Sum.elim (fun _ => r) (fun i => if i = i₀ then r ^ 2 else r)

/-- **The anisotropic polydisc** around the reference point `(e_{i₀}, ν e_{i₀})`:
`|ψ_i(x) - δ_{i i₀}| < r`, `|b_{i₀} - ν| < r²`, `|b_i| < r` for `i ≠ i₀`. -/
def polyAniso (i₀ : Fin N) (ν r : ℝ) (X : Finset (Site d)) : Set (Cfg d N X) :=
  Balaban.Analysis.polydisc (refPt i₀ ν X) (anisoWt i₀ r X)

/-- **The analyticity domain of the anisotropic I-6**: the configurations of `X` which a complex
orthogonal matrix with entries bounded by `rotBound N` carries into the anisotropic polydisc
(the analogue of `Tube`). -/
def TubeAniso (i₀ : Fin N) (ν r : ℝ) (X : Finset (Site d)) : Set (Cfg d N X) :=
  {c | ∃ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R ∧ EntryBd N R ∧
    rotCfgL R X c ∈ polyAniso i₀ ν r X}

/-- The diagonal rescaling by the polyradius: `(S w)_p = r_p w_p`. -/
noncomputable def anisoScale (i₀ : Fin N) (r : ℝ) (X : Finset (Site d)) :
    Cfg d N X →L[ℂ] Cfg d N X :=
  ContinuousLinearMap.pi fun p => ((anisoWt i₀ r X p : ℝ) : ℂ) • ContinuousLinearMap.proj p

/-- The inverse rescaling: `(S⁻¹ z)_p = z_p / r_p`. -/
noncomputable def anisoUnscale (i₀ : Fin N) (r : ℝ) (X : Finset (Site d)) :
    Cfg d N X →L[ℂ] Cfg d N X :=
  ContinuousLinearMap.pi fun p => ((anisoWt i₀ r X p : ℝ) : ℂ)⁻¹ • ContinuousLinearMap.proj p

/-- The gauge of the anisotropic polydisc, `max_p |z_p| / r_p`. -/
noncomputable def anisoGauge (i₀ : Fin N) (r : ℝ) (X : Finset (Site d)) (z : Cfg d N X) : ℝ :=
  ‖anisoUnscale i₀ r X z‖

section Aniso

variable {i₀ : Fin N} {ν r : ℝ} {X : Finset (Site d)}

theorem anisoWt_inl (p : ↥X × Fin N) : anisoWt i₀ r X (Sum.inl p) = r := rfl

theorem anisoWt_inr_self : anisoWt (X := X) i₀ r (Sum.inr i₀) = r ^ 2 := by
  simp [anisoWt]

theorem anisoWt_inr_ne {i : Fin N} (hi : i ≠ i₀) : anisoWt (X := X) i₀ r (Sum.inr i) = r := by
  simp [anisoWt, hi]

theorem anisoWt_pos (hr : 0 < r) (p : Idx d N X) : 0 < anisoWt i₀ r X p := by
  rcases p with p | i
  · exact hr
  · simp only [anisoWt, Sum.elim_inr]
    split_ifs <;> positivity

/-- For `r ≤ 1` the polyradius is at least `r²` in every coordinate. -/
theorem sq_le_anisoWt (hr : 0 < r) (hr1 : r ≤ 1) (p : Idx d N X) : r ^ 2 ≤ anisoWt i₀ r X p := by
  have h : r ^ 2 ≤ r := by nlinarith
  rcases p with p | i
  · exact h
  · simp only [anisoWt, Sum.elim_inr]
    split_ifs
    · exact le_rfl
    · exact h

theorem anisoScale_apply (w : Cfg d N X) (p : Idx d N X) :
    anisoScale i₀ r X w p = (anisoWt i₀ r X p : ℂ) * w p := by
  simp [anisoScale]

theorem anisoUnscale_apply (z : Cfg d N X) (p : Idx d N X) :
    anisoUnscale i₀ r X z p = (anisoWt i₀ r X p : ℂ)⁻¹ * z p := by
  simp [anisoUnscale]

theorem anisoWt_ne_zero (hr : 0 < r) (p : Idx d N X) : ((anisoWt i₀ r X p : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (anisoWt_pos hr p).ne'

theorem anisoScale_unscale (hr : 0 < r) (z : Cfg d N X) :
    anisoScale i₀ r X (anisoUnscale i₀ r X z) = z := by
  ext p
  rw [anisoScale_apply, anisoUnscale_apply, ← mul_assoc, mul_inv_cancel₀ (anisoWt_ne_zero hr p),
    one_mul]

theorem anisoUnscale_scale (hr : 0 < r) (w : Cfg d N X) :
    anisoUnscale i₀ r X (anisoScale i₀ r X w) = w := by
  ext p
  rw [anisoUnscale_apply, anisoScale_apply, ← mul_assoc, inv_mul_cancel₀ (anisoWt_ne_zero hr p),
    one_mul]

theorem anisoGauge_nonneg (z : Cfg d N X) : 0 ≤ anisoGauge i₀ r X z := norm_nonneg _

theorem anisoGauge_add_le (z z' : Cfg d N X) :
    anisoGauge i₀ r X (z + z') ≤ anisoGauge i₀ r X z + anisoGauge i₀ r X z' := by
  unfold anisoGauge
  rw [map_add]
  exact norm_add_le _ _

theorem anisoGauge_sub_le (z z' : Cfg d N X) :
    anisoGauge i₀ r X (z - z') ≤ anisoGauge i₀ r X z + anisoGauge i₀ r X z' := by
  unfold anisoGauge
  rw [map_sub]
  exact norm_sub_le _ _

theorem anisoGauge_scale (hr : 0 < r) (w : Cfg d N X) :
    anisoGauge i₀ r X (anisoScale i₀ r X w) = ‖w‖ := by
  rw [anisoGauge, anisoUnscale_scale hr]

theorem norm_unscale_apply (hr : 0 < r) (z : Cfg d N X) (p : Idx d N X) :
    ‖anisoUnscale i₀ r X z p‖ = ‖z p‖ / anisoWt i₀ r X p := by
  rw [anisoUnscale_apply, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (anisoWt_pos hr p)]
  ring

/-- Each coordinate is bounded by its radius times the gauge. -/
theorem norm_apply_le_anisoWt_mul (hr : 0 < r) (z : Cfg d N X) (p : Idx d N X) :
    ‖z p‖ ≤ anisoWt i₀ r X p * anisoGauge i₀ r X z := by
  have h := norm_le_pi_norm (anisoUnscale i₀ r X z) p
  rw [norm_unscale_apply hr] at h
  have hw := anisoWt_pos (i₀ := i₀) hr p
  rw [div_le_iff₀ hw] at h
  unfold anisoGauge
  linarith

/-- The gauge is at most `G` if every coordinate is at most its radius times `G`. -/
theorem anisoGauge_le_of (hr : 0 < r) {z : Cfg d N X} {G : ℝ} (hG : 0 ≤ G)
    (h : ∀ p, ‖z p‖ ≤ anisoWt i₀ r X p * G) : anisoGauge i₀ r X z ≤ G := by
  unfold anisoGauge
  rw [pi_norm_le_iff_of_nonneg hG]
  intro p
  rw [norm_unscale_apply hr, div_le_iff₀ (anisoWt_pos hr p)]
  linarith [h p]

theorem anisoGauge_single (hr : 0 < r) (p : Idx d N X) :
    anisoGauge i₀ r X (Pi.single p 1) = (anisoWt i₀ r X p)⁻¹ := by
  classical
  have e : anisoUnscale i₀ r X (Pi.single p 1) =
      Pi.single p (((anisoWt i₀ r X p : ℝ) : ℂ)⁻¹) := by
    ext q
    rw [anisoUnscale_apply]
    by_cases h : q = p
    · subst h; simp
    · simp [h]
  rw [anisoGauge, e, Pi.norm_single, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (anisoWt_pos hr p)]

theorem anisoGauge_single_inl (hr : 0 < r) (p : ↥X × Fin N) :
    anisoGauge i₀ r X (Pi.single (Sum.inl p) 1) = 1 / r := by
  rw [anisoGauge_single hr, anisoWt_inl, one_div]

theorem anisoGauge_single_inr_ne (hr : 0 < r) {i : Fin N} (hi : i ≠ i₀) :
    anisoGauge i₀ r X (Pi.single (Sum.inr i) 1) = 1 / r := by
  rw [anisoGauge_single hr, anisoWt_inr_ne hi, one_div]

theorem anisoGauge_single_inr_self (hr : 0 < r) :
    anisoGauge i₀ r X (Pi.single (Sum.inr i₀) 1) = 1 / r ^ 2 := by
  rw [anisoGauge_single hr, anisoWt_inr_self, one_div]

/-- A pure spin displacement has gauge `‖·‖ / r`. -/
theorem anisoGauge_pack_zero_le (hr : 0 < r) (φ : Site d → Spin N) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ X, ‖φ x‖ ≤ D) : anisoGauge i₀ r X (pack X φ 0) ≤ D / r := by
  refine anisoGauge_le_of hr (by positivity) fun p => ?_
  have hpk := norm_pack_le X φ hD0 hD
  rcases p with p | i
  · rw [anisoWt_inl, mul_div_cancel₀ _ hr.ne']
    exact (norm_le_pi_norm _ _).trans hpk
  · have : pack X φ 0 (Sum.inr i) = 0 := by simp [pack]
    rw [this, norm_zero]
    exact mul_nonneg (anisoWt_pos hr _).le (by positivity)

/-- **The rescaling lemma**: `S` maps the unit ball onto the anisotropic polydisc. -/
theorem refPt_add_anisoScale_mem_iff (hr : 0 < r) (w : Cfg d N X) :
    refPt i₀ ν X + anisoScale i₀ r X w ∈ polyAniso i₀ ν r X ↔ ‖w‖ < 1 := by
  rw [pi_norm_lt_iff one_pos]
  unfold polyAniso Balaban.Analysis.polydisc
  simp only [mem_ofPred_eq, Pi.add_apply, add_sub_cancel_left, anisoScale_apply, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  refine forall_congr' fun p => ?_
  rw [abs_of_pos (anisoWt_pos hr p)]
  exact mul_lt_iff_lt_one_right (anisoWt_pos hr p)

theorem refPt_add_mem_polyAniso_iff (hr : 0 < r) (z : Cfg d N X) :
    refPt i₀ ν X + z ∈ polyAniso i₀ ν r X ↔ anisoGauge i₀ r X z < 1 := by
  conv_lhs => rw [← anisoScale_unscale (i₀ := i₀) hr z]
  exact refPt_add_anisoScale_mem_iff hr _

theorem mem_polyAniso_iff (hr : 0 < r) (c : Cfg d N X) :
    c ∈ polyAniso i₀ ν r X ↔ anisoGauge i₀ r X (c - refPt i₀ ν X) < 1 := by
  rw [← refPt_add_mem_polyAniso_iff hr, add_sub_cancel]

theorem polyAniso_eq_image (hr : 0 < r) :
    polyAniso i₀ ν r X = (fun w => refPt i₀ ν X + anisoScale i₀ r X w) '' ball 0 1 := by
  ext c
  constructor
  · intro hc
    refine ⟨anisoUnscale i₀ r X (c - refPt i₀ ν X), ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      exact (mem_polyAniso_iff hr c).mp hc
    · simp only
      rw [anisoScale_unscale hr, add_sub_cancel]
  · rintro ⟨w, hw, rfl⟩
    exact (refPt_add_anisoScale_mem_iff hr w).mpr (by simpa using hw)

theorem isOpen_polyAniso : IsOpen (polyAniso i₀ ν r X) :=
  Balaban.Analysis.isOpen_polydisc _ _

theorem refPt_mem_polyAniso (hr : 0 < r) : refPt i₀ ν X ∈ polyAniso i₀ ν r X := by
  have := (refPt_add_mem_polyAniso_iff (i₀ := i₀) (ν := ν) (X := X) hr 0).mpr
    (by simp [anisoGauge])
  simpa using this

theorem ball_subset_polyAniso (hr : 0 < r) (hr1 : r ≤ 1) :
    ball (refPt i₀ ν X) (r ^ 2) ⊆ polyAniso i₀ ν r X := by
  intro c hc p
  have h1 : ‖c p - refPt i₀ ν X p‖ < r ^ 2 := by
    rw [mem_ball, dist_eq_norm] at hc
    exact lt_of_le_of_lt (norm_le_pi_norm (c - refPt i₀ ν X) p) hc
  exact lt_of_lt_of_le h1 (sq_le_anisoWt hr hr1 p)

theorem polyAniso_subset_tubeAniso : polyAniso i₀ ν r X ⊆ TubeAniso i₀ ν r X :=
  fun c hc => ⟨1, isOrth_one, entryBd_one, by rwa [rotCfgL_one]⟩

/-- The isotropic tube of radius `r²` lies in the anisotropic one. -/
theorem tube_subset_tubeAniso (hr : 0 < r) (hr1 : r ≤ 1) :
    Tube i₀ ν (r ^ 2) X ⊆ TubeAniso i₀ ν r X := by
  rintro c ⟨R, hR, hb, hc⟩
  exact ⟨R, hR, hb, ball_subset_polyAniso hr hr1 hc⟩

/-- Analyticity and rotation invariance on `TubeAniso` give the hypotheses `TermOK` of the shape
lemmas and of the Ward identity, at the radius `r²`. -/
theorem termOK_of_tubeAniso {f : Cfg d N X → ℂ} (hr : 0 < r) (hr1 : r ≤ 1)
    (han : AnalyticOnNhd ℂ f (TubeAniso i₀ ν r X))
    (hinv : ∀ c ∈ TubeAniso i₀ ν r X, ∀ R : Matrix (Fin N) (Fin N) ℂ, IsOrth R → EntryBd N R →
      rotCfgL R X c ∈ TubeAniso i₀ ν r X → f (rotCfgL R X c) = f c) :
    TermOK i₀ ν (r ^ 2) X f :=
  ⟨by positivity, han.mono (tube_subset_tubeAniso hr hr1),
    fun c hc R hR hb hm => hinv c (tube_subset_tubeAniso hr hr1 hc) R hR hb
      (tube_subset_tubeAniso hr hr1 hm)⟩

end Aniso

/-! ### Cauchy estimates on the anisotropic polydisc -/

section AnisoCauchy

variable {i₀ : Fin N} {ν r M : ℝ} {X : Finset (Site d)} {f : Cfg d N X → ℂ}

theorem aniso_hf (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X)) :
    ∀ w : Cfg d N X, ‖w‖ < 1 → AnalyticAt ℂ f (refPt i₀ ν X + anisoScale i₀ r X w) :=
  fun w hw => han _ ((refPt_add_anisoScale_mem_iff hr w).mpr hw)

theorem aniso_hM (hr : 0 < r) (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) :
    ∀ w : Cfg d N X, ‖w‖ < 1 → ‖f (refPt i₀ ν X + anisoScale i₀ r X w)‖ ≤ M :=
  fun w hw => hM _ ((refPt_add_anisoScale_mem_iff hr w).mpr hw)

theorem aniso_analyticAt_refPt (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X)) :
    AnalyticAt ℂ f (refPt i₀ ν X) :=
  han _ (refPt_mem_polyAniso hr)

theorem aniso_M_nonneg (hr : 0 < r) (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) : 0 ≤ M :=
  le_trans (norm_nonneg _) (hM _ (refPt_mem_polyAniso hr))

/-- First-order Taylor remainder in the gauge: `‖f(P + z) - f(P) - f'(P) z‖ ≤ 2 M g(z)²`. -/
theorem aniso_taylor_first (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) {z : Cfg d N X}
    (hz : anisoGauge i₀ r X z ≤ 1 / 2) :
    ‖f (refPt i₀ ν X + z) - f (refPt i₀ ν X) - fderiv ℂ f (refPt i₀ ν X) z‖ ≤
      2 * M * anisoGauge i₀ r X z ^ 2 := by
  have h := taylor_first_scale (aniso_hf hr han) (aniso_hM hr hM) (w := anisoUnscale i₀ r X z) hz
  rwa [anisoScale_unscale hr] at h

/-- Second-order Taylor remainder in the gauge. -/
theorem aniso_taylor_second (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) {z : Cfg d N X}
    (hz : anisoGauge i₀ r X z ≤ 1 / 2) :
    ‖f (refPt i₀ ν X + z) - f (refPt i₀ ν X) - fderiv ℂ f (refPt i₀ ν X) z -
        (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) z z‖ ≤ 2 * M * anisoGauge i₀ r X z ^ 3 := by
  have h := taylor_second_scale (fun z => anisoScale_unscale (i₀ := i₀) (X := X) hr z)
    (aniso_hf hr han) (aniso_hM hr hM) (w := anisoUnscale i₀ r X z) hz
  rwa [anisoScale_unscale hr] at h

/-- Cauchy estimate in the gauge: `‖f'(P) v‖ ≤ M g(v)`. -/
theorem aniso_norm_fderiv_le (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) (v : Cfg d N X) :
    ‖fderiv ℂ f (refPt i₀ ν X) v‖ ≤ M * anisoGauge i₀ r X v := by
  have h := norm_fderiv_scale_le (aniso_hf hr han) (aniso_hM hr hM) (anisoUnscale i₀ r X v)
  rwa [anisoScale_unscale hr] at h

/-- Cauchy estimate in the gauge: `‖f''(P)(v, w)‖ ≤ 4 M g(v) g(w)`. -/
theorem aniso_norm_D2_le (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) (v w : Cfg d N X) :
    ‖D2 f (refPt i₀ ν X) v w‖ ≤ 4 * M * anisoGauge i₀ r X v * anisoGauge i₀ r X w := by
  have h := norm_D2_scale_le (fun z => anisoScale_unscale (i₀ := i₀) (X := X) hr z)
    (aniso_hf hr han) (aniso_hM hr hM) (anisoUnscale i₀ r X v) (anisoUnscale i₀ r X w)
  rwa [anisoScale_unscale hr, anisoScale_unscale hr] at h

/-- The difference of two second-order expansions (the analogue of `TermOK.taylor_diff`). -/
theorem aniso_taylor_diff (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) {z zc : Cfg d N X}
    (hz : anisoGauge i₀ r X z ≤ 1 / 2) (hzc : anisoGauge i₀ r X zc ≤ 1 / 2) :
    ‖f (refPt i₀ ν X + z) - f (refPt i₀ ν X + zc)
        - fderiv ℂ f (refPt i₀ ν X) (z - zc)
        - D2 f (refPt i₀ ν X) zc (z - zc)
        - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) (z - zc) (z - zc)‖ ≤
      2 * M * anisoGauge i₀ r X z ^ 3 + 2 * M * anisoGauge i₀ r X zc ^ 3 := by
  have h1 := aniso_taylor_second hr han hM hz
  have h2 := aniso_taylor_second hr han hM hzc
  have hs := D2_symm (aniso_analyticAt_refPt hr han) zc (z - zc)
  have hD : D2 f (refPt i₀ ν X) z z = D2 f (refPt i₀ ν X) zc zc +
      2 * D2 f (refPt i₀ ν X) zc (z - zc) + D2 f (refPt i₀ ν X) (z - zc) (z - zc) := by
    have : z = zc + (z - zc) := by abel
    conv_lhs => rw [this]
    simp only [D2_add_left, D2_add_right]
    rw [← hs]; ring
  have e : f (refPt i₀ ν X + z) - f (refPt i₀ ν X + zc)
        - fderiv ℂ f (refPt i₀ ν X) (z - zc)
        - D2 f (refPt i₀ ν X) zc (z - zc)
        - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) (z - zc) (z - zc) =
      (f (refPt i₀ ν X + z) - f (refPt i₀ ν X) - fderiv ℂ f (refPt i₀ ν X) z
          - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) z z) -
      (f (refPt i₀ ν X + zc) - f (refPt i₀ ν X) - fderiv ℂ f (refPt i₀ ν X) zc
          - (1 / 2 : ℂ) * D2 f (refPt i₀ ν X) zc zc) := by
    rw [map_sub, hD]; ring
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- The first derivative in a spin direction or a transverse field direction costs `1/r`. -/
theorem aniso_norm_fderiv_basis_le (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) (p : Idx d N X) :
    ‖fderiv ℂ f (refPt i₀ ν X) (Pi.single p 1)‖ ≤ M / anisoWt i₀ r X p := by
  have h := aniso_norm_fderiv_le hr han hM (Pi.single p 1)
  rwa [anisoGauge_single hr, ← div_eq_mul_inv] at h

theorem aniso_norm_tensA_le (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) (x : ↥X) :
    ‖tensA i₀ ν X f x‖ ≤ M / r :=
  aniso_norm_fderiv_basis_le hr han hM (Sum.inl (x, i₀))

/-- The longitudinal field derivative costs `1/r²`. -/
theorem aniso_norm_fderiv_inr_self_le (hr : 0 < r)
    (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X)) (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) :
    ‖fderiv ℂ f (refPt i₀ ν X) (Pi.single (Sum.inr i₀) 1)‖ ≤ M / r ^ 2 := by
  have h := aniso_norm_fderiv_basis_le hr han hM (Sum.inr i₀)
  rwa [anisoWt_inr_self] at h

/-- Second derivatives in two directions of radius `r` cost `4/r²`. -/
theorem aniso_norm_D2_basis_le (hr : 0 < r) (han : AnalyticOnNhd ℂ f (polyAniso i₀ ν r X))
    (hM : ∀ c ∈ polyAniso i₀ ν r X, ‖f c‖ ≤ M) {p q : Idx d N X}
    (hp : anisoWt i₀ r X p = r) (hq : anisoWt i₀ r X q = r) :
    ‖D2 f (refPt i₀ ν X) (Pi.single p 1) (Pi.single q 1)‖ ≤ 4 * M / r ^ 2 := by
  have h := aniso_norm_D2_le hr han hM (Pi.single p 1) (Pi.single q 1)
  rw [anisoGauge_single hr, anisoGauge_single hr, hp, hq] at h
  refine h.trans (le_of_eq ?_)
  field_simp

end AnisoCauchy

end Balaban.SmallField
