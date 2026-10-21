/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXLogShift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shifted logarithm of the base covariance family: integral, analyticity, bound (item 2)

`baseCovXLogShift s := ∫₀^∞ ((1+x)⁻¹ c(s) - C_x(s)) dx` (entrywise), where `c(s)` is the large-`x`
coefficient of `BaseXLogShift`.  By the decay `O((1+x)⁻²)` (`baseCovXShift_entry_le`) the integral
converges, and by dominated differentiation its entries are analytic in `(s, φ₀, α₀)` on the polydisc
`DecDom`, bounded by `B (1+ν)`.  At the physical point it is the logarithm of `A_e`
(`BASEX.md`; item 3).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Multiscale Balaban.Localization MeasureTheory Set Filter Topology

section Elementary

/-- `∫₀^∞ (1+x)⁻² dx = 1`, and the integrand is integrable. -/
theorem integrableOn_inv_one_add_sq : IntegrableOn (fun x : ℝ => ((1 + x)⁻¹) ^ 2) (Ioi 0) := by
  have h : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 + x)⁻¹) (((1 + x)⁻¹) ^ 2) x := by
    intro x hx
    have h1 : (1 + x) ≠ 0 := by have : (0 : ℝ) ≤ x := hx; linarith
    have h2 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have := (h2.inv h1).neg
    convert this using 1
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg' h (fun x hx => by positivity) (l := 0) ?_
  have : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
  simpa using this.neg

theorem integral_inv_one_add_sq : ∫ x in Ioi (0 : ℝ), ((1 + x)⁻¹) ^ 2 = 1 := by
  have h : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 + x)⁻¹) (((1 + x)⁻¹) ^ 2) x := by
    intro x hx
    have h1 : (1 + x) ≠ 0 := by have : (0 : ℝ) ≤ x := hx; linarith
    have h2 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    have := (h2.inv h1).neg
    convert this using 1
    field_simp
  have hl : Tendsto (fun x : ℝ => -(1 + x)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => (1 + x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using this.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' h integrableOn_inv_one_add_sq hl]
  simp

end Elementary

section Analytic

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}

/-- The multiplier `σ_s` is analytic in the decoupling parameters. -/
theorem rectAt_cubeSigma (e : DecData G N) :
    RectAt (fun p : DecData G N => (Matrix.diagonal (cubeSigma G (Dec2.extS (coverOf G) p.1)) :
      Matrix (G.Ω 1) (G.Ω 1) ℂ)) e := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, cubeSigma]
    refine Finset.analyticAt_fun_sum _ fun q _ => ?_
    have hpr : AnalyticAt ℂ (fun p : DecData G N => ((p.1, p.2.2) : Dec2.DecParams (coverOf G) × (G.Ω 1 → ℂ))) e :=
      AnalyticAt.prod analyticAt_fst (analyticAt_snd.comp analyticAt_snd)
    exact (AnalyticAt.comp (x := e) (f := fun p : DecData G N => ((p.1, p.2.2) :
      Dec2.DecParams (coverOf G) × (G.Ω 1 → ℂ))) (Dec2.analyticAt_sProd (C := coverOf G) (H := G) q (e.1, e.2.2))
      hpr).mul analyticAt_const
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact analyticAt_const

/-- The field projection `Q_φ` is analytic in `φ₀` where the bilinear squares do not vanish. -/
theorem rectAt_fieldProj (e : DecData G N) (hD : ∀ y : G.Ω 1, ∑ i, e.2.1 y i * e.2.1 y i ≠ 0) :
    RectAt (fun p : DecData G N => fieldProj G p.2.1) e := by
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hDi : RectAt (fun p : DecData G N => (Matrix.diagonal
      (fun y : G.Ω 1 => (∑ i, p.2.1 y i * p.2.1 y i)⁻¹) : Matrix (G.Ω 1) (G.Ω 1) ℂ)) e := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      refine AnalyticAt.inv ?_ (hD i)
      exact Finset.analyticAt_fun_sum _ fun r _ =>
        (analyticAt_field_coord (i : Balaban.Localization.CTorus d L N₁ m₁ 1) r e).mul
          (analyticAt_field_coord (i : Balaban.Localization.CTorus d L N₁ m₁ 1) r e)
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact analyticAt_const
  unfold fieldProj
  exact (hF.mul hDi).mul hF.transpose'

end Analytic

section Main

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The shifted logarithm of the first step's covariance family**,
`∫₀^∞ ((1+x)⁻¹ c(s) - C_x(s)) dx` (entrywise), `C_x(s) = (1+x)⁻¹ P_e + Ĝ_{0,s} - Π_{0,s}` at mass
`ν + x` and `c(s)` the large-`x` coefficient `baseCovXCoef`.  At the physical point it is
`logMat A_e`, `A_e = Q_e (H ⊗ I) Q_e + P_e` (`baseCovX_log`; `BASEX.md`, Q5). -/
noncomputable def baseCovXLogShift (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ)
    (aT ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) :
    Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ :=
  fun y z => ∫ x in Ioi (0 : ℝ), baseCovXShiftIntegrand G a aT ν α s φ x y z

/-- The coefficient `c(s)` is analytic on the polydisc. -/
theorem rectAt_baseCovXCoef {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} (e : DecData G N)
    (hD : ∀ y : G.Ω 1, ∑ i, e.2.1 y i * e.2.1 y i ≠ 0) :
    RectAt (fun p : DecData G N => baseCovXCoef G (Dec2.extS (coverOf G) p.1) p.2.1) e := by
  have hF := rectAt_fieldMul (G := G) (N := N) e
  have hP : RectAt (fun p : DecData G N => basePart (restrictField G p.2.1)) e := by
    unfold basePart; exact hF.mul hF.transpose'
  unfold baseCovXCoef
  exact hP.add ((rectAt_cubeSigma e).liftOp.mul ((RectAt.const _ e).sub (rectAt_fieldProj e hD)))

/-- **The shifted logarithm: integrability, analyticity and bound** (item 2).  With `B` depending
only on `d, L, N, κ`, at every point `e = (s, φ₀, α₀)` of the polydisc `DecDom` the entries of
`(1+x)⁻¹ c(s) - C_x(s)` are `≤ B (1+ν)(1+x)⁻²`, integrable on `(0, ∞)`, their integral
`baseCovXLogShift` is analytic in `e` on `DecDom` and bounded by `B (1+ν)`. -/
theorem baseCovXLogShift_main (d L N : ℕ) [NeZero L] (κ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
      (_S : Dec2.XCover (coverOf G) G a aT ν Cx) (_hCx : 0 ≤ Cx) (_hκ : 0 ≤ κ)
      (_hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
      {δ : ℝ} (_hδ : 0 ≤ δ) (_hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
      (_ha0 : a 0 = 2) (_ha1 : 0 ≤ a 1) (_ha1' : a 1 ≤ 2)
      (_haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1)) (y z : G.Ω 1 × Fin N),
      (∀ e ∈ DecDom G N κ δ, ∀ x : ℝ, 0 ≤ x →
        ‖baseCovXShiftIntegrand G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 x y z‖ ≤
          B * (1 + ν) * ((1 + x)⁻¹) ^ 2) ∧
      (∀ e ∈ DecDom G N κ δ, IntegrableOn (fun x : ℝ =>
        baseCovXShiftIntegrand G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 x y z)
        (Ioi 0)) ∧
      AnalyticOnNhd ℂ (fun e : DecData G N =>
        baseCovXLogShift G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 y z)
        (DecDom G N κ δ) ∧
      (∀ e ∈ DecDom G N κ δ,
        ‖baseCovXLogShift G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 y z‖ ≤
          B * (1 + ν)) := by
  obtain ⟨B, hB0, hent⟩ := baseCovXShift_entry_le d L N κ
  refine ⟨B, hB0, ?_⟩
  intro N₁ m₁ _ ϱ G a aT ν Cx S hCx hκ hM δ hδ hsm ha0 ha1 ha1' haT y z
  have hν : 0 ≤ ν := S.mass
  have hD : ∀ e ∈ DecDom G N κ δ, ∀ x : ℝ, 0 ≤ x →
      Dec2.XData (coverOf G) G a aT (ν + x) 0 e.2.2 κ (Dec2.extS (coverOf G) e.1) Cx :=
    fun e he x hx => xData_cover_of_mem (xCover_add_mass S hx) hCx le_rfl hκ hM he
  have hbd : ∀ e ∈ DecDom G N κ δ, ∀ x : ℝ, 0 ≤ x →
      ‖baseCovXShiftIntegrand G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 x y z‖ ≤
        B * (1 + ν) * ((1 + x)⁻¹) ^ 2 := by
    intro e he x hx
    have D := hD e he x hx
    exact hent (xCover_add_mass S hx) hCx hν hx hκ hM hδ hsm D.pot D.sb
      he.2.1.toIsConstraintField ha0 ha1 ha1' haT y z
  have hDne : ∀ e ∈ DecDom G N κ δ, ∀ y : G.Ω 1, ∑ i, e.2.1 y i * e.2.1 y i ≠ 0 := by
    intro e he y h0
    have := norm_sq_ge_half he.2.1.toIsConstraintField hδ hsm (κ := κ) y
    rw [h0] at this
    simp at this
    linarith
  have hcont : ∀ e ∈ DecDom G N κ δ, ContinuousOn (fun x : ℝ =>
      baseCovXShiftIntegrand G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 x y z) (Ioi 0) := by
    intro e he
    have h := continuousOn_baseCovX_shift (fun x hx => hD e he x hx)
      he.2.1.toIsConstraintField hδ hsm
    have hinv : ContinuousOn (fun x : ℝ => (1 + (x : ℂ))⁻¹) (Ioi 0) := by
      refine (continuousOn_const.add Complex.continuous_ofReal.continuousOn).inv₀ fun x hx => ?_
      have : (1 : ℝ) + x ≠ 0 := by have : (0 : ℝ) < x := hx; linarith
      show (1 : ℂ) + (x : ℂ) ≠ 0
      exact_mod_cast this
    have h1 := (continuousOn_pi.1 (continuousOn_pi.1 h y) z).mono Ioi_subset_Ici_self
    unfold baseCovXShiftIntegrand
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hinv.mul continuousOn_const).sub h1
  have hgi : IntegrableOn (fun x : ℝ => B * (1 + ν) * ((1 + x)⁻¹) ^ 2) (Ioi 0) :=
    integrableOn_inv_one_add_sq.const_mul _
  have hgc : ContinuousOn (fun x : ℝ => B * (1 + ν) * ((1 + x)⁻¹) ^ 2) (Ioi 0) := by
    refine continuousOn_const.mul ((Localization.continuousOn_inv_add_Ioi one_pos).pow 2)
  have hint : ∀ e ∈ DecDom G N κ δ, IntegrableOn (fun x : ℝ =>
      baseCovXShiftIntegrand G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 x y z) (Ioi 0) := by
    intro e he
    refine Integrable.mono' hgi ((hcont e he).aestronglyMeasurable measurableSet_Ioi) ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun x hx => hbd e he x (mem_Ioi.mp hx).le)
  refine ⟨hbd, hint, ?_, ?_⟩
  · have hA := Localization.analyticOnNhd_integral_Ioi (E := DecData G N)
      (G := fun x e => baseCovXShiftIntegrand G a aT ν e.2.2 (Dec2.extS (coverOf G) e.1) e.2.1 x y z)
      (g := fun x => B * (1 + ν) * ((1 + x)⁻¹) ^ 2) (isOpen_decDom κ δ)
      (fun x hx e he => ?_) hcont hgc hgi (fun x hx e he => hbd e he x hx.le)
    · exact hA
    · unfold baseCovXShiftIntegrand
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      exact (analyticAt_const.mul (rectAt_baseCovXCoef e (hDne e he) y z)).sub
        (baseCovX_analytic (xCover_add_mass S hx.le) hCx hκ hM hδ hsm y z e he)
  · intro e he
    have hn := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0 : ℝ))) hgi
      ((ae_restrict_iff' measurableSet_Ioi).2
        (Filter.Eventually.of_forall fun x hx => hbd e he x (mem_Ioi.mp hx).le))
    rw [integral_const_mul, integral_inv_one_add_sq, mul_one] at hn
    exact hn

end Main

end Balaban.LargeField.Base
