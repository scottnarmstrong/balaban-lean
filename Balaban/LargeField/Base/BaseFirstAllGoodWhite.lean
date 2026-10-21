/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFirstAllGood
public import Balaban.LargeField.Base.BaseFRWhiteChange

/-!
# The all-good sector of the first density in the whitened variables (route FR-1)

`baseRho1_allGood_whitened` restates `baseRho1_allGood_gaussian` with the change of variables
`u = W φ` of `integral_tangent_gaussian_whitened`, for any approximate square root `W` of the chart
Gaussian form (`⟨Wφ, gaussForm(Wφ)⟩ = |φ|² + q_D(φ)`; the finite-range whitening of
`BaseFRWhite.lean`): the all-good chart integral is

`(√β)^{-(N-1)|𝕋_{Ln}|} (2π)^{-|𝕋_{Ln}|/2} |det W| ∫ e^{-½(|φ|² + q_D(φ))} F(P(Wφ)) dφ`

with the explicit integrand `F = baseSectorF` (chart Jacobian, cutoff, normal shift, mass and
source terms). `rSmall` is the indicator `∏_x 1[|φ_x| < p₁]` of the small-fluctuation test (the
`𝖱₁` test, LFR Definition II.7.1, P5 (2.43) at `k = 0`) and `integral_rSmall_split` splits an
integrable integrand along it.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

section Split

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The small-fluctuation test `∏_x 1[|φ_x| < p₁]` on the Gaussian variable. -/
noncomputable def rSmall (p₁ : ℝ) (φ : Config ι N) : ℝ :=
  ∏ x, if ‖φ x‖ < p₁ then 1 else 0

theorem rSmall_zero_or_one (p₁ : ℝ) (φ : Config ι N) : rSmall p₁ φ = 0 ∨ rSmall p₁ φ = 1 := by
  unfold rSmall
  by_cases h : ∀ x, ‖φ x‖ < p₁
  · right; exact Finset.prod_eq_one fun x _ => by simp [h x]
  · left
    simp only [not_forall, not_lt] at h
    obtain ⟨x, hx⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [not_lt.2 hx])

theorem measurable_rSmall (p₁ : ℝ) : Measurable (rSmall (ι := ι) (N := N) p₁) := by
  unfold rSmall
  refine Finset.measurable_prod _ fun x _ => ?_
  refine Measurable.ite (measurableSet_lt ?_ measurable_const) measurable_const measurable_const
  exact (measurable_pi_apply x).norm

/-- **The split along the `𝖱₁` test**: an integrable integrand splits into the small-fluctuation
part and the rest. -/
theorem integral_rSmall_split (p₁ : ℝ) (G : Config ι N → ℂ) (hG : Integrable G) :
    ∫ φ, G φ = (∫ φ, ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ) +
      ∫ φ, ((1 - rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ := by
  have hb : ∀ φ : Config ι N, 0 ≤ rSmall (ι := ι) (N := N) p₁ φ ∧ rSmall (ι := ι) (N := N) p₁ φ ≤ 1 := fun φ => by
    rcases rSmall_zero_or_one p₁ φ with h | h <;> simp [h]
  have hi : Integrable (fun φ : Config ι N => ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ) := by
    refine hG.norm.mono' ?_ (Filter.Eventually.of_forall fun φ => ?_)
    · exact (Complex.measurable_ofReal.comp (measurable_rSmall (ι := ι) (N := N) p₁)).aestronglyMeasurable.mul
        hG.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb φ).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb φ).2
  have hi' : Integrable (fun φ : Config ι N => ((1 - rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ) := by
    refine hG.norm.mono' ?_ (Filter.Eventually.of_forall fun φ => ?_)
    · exact (Complex.measurable_ofReal.comp (measurable_const.sub (measurable_rSmall (ι := ι) (N := N) p₁))).aestronglyMeasurable.mul
        hG.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 (hb φ).2)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hb φ).1])
  have hadd := integral_add hi hi'
  have hpt : ∀ φ : Config ι N, G φ = ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ +
      ((1 - rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ := fun φ => by
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  calc ∫ φ, G φ = ∫ φ, (((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ +
        ((1 - rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) * G φ) := integral_congr_ae
          (Filter.Eventually.of_forall hpt)
    _ = _ := hadd

end Split

section Whitened

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

open Classical in
/-- **The all-good sector of the first density in the whitened variables** (route FR-1; LFR Lemmas
II.7.3–II.7.5, LF-BASE-KF0 (A.3)). With `θ = z₁ψ`, for every linear equivalence `W` of
`ℝ^{N|𝕋_{Ln}|}` and defect form `q_D` with `⟨Wφ, gaussForm(Wφ)⟩ = |φ|² + q_D(φ)`:
`ρ₁ = z₁^{N|𝕋_n|}` times the sum of

* `(√β)^{-(N-1)|𝕋_{Ln}|} (2π)^{-|𝕋_{Ln}|/2} |det W| ∫ e^{-½(|φ|² + q_D(φ))} F(P(Wφ)) dφ`, where
  `F = baseSectorF` is the chart integrand (chart Jacobian `J_β`, cutoff `χ = ∏ χ'^{(0)}_c`,
  normal shift `z`, mass difference `M`, source terms `⟨g, e⟩ + β^{-1/2}⟨g, w + z⟩`, the action at
  the background `e`, the kernel normalization `κ`) and `P` the tangent projection, and
* the sectors with failed cubes (`baseFirstRest`). -/
theorem baseRho1_allGood_whitened
    {β a z₁ : ℝ} (hβ : 0 < β) (ha0 : 0 < a)
    (ν δ₀ : ℝ) (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (g : Torus d (L * n) → Fin N → ℂ)
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h (z₁ • ψ) φ₀ ≠ 0) :
    let θ : Torus d n → EuclideanSpace ℝ (Fin N) := z₁ • ψ
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let κ : ℂ := ((∏ _y : Torus d n,
      ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
        ((N : ℝ) / 2) : ℝ) : ℂ)
    let F := baseSectorF β a ν regimeB h g θ e he Hα χ κ
    ∀ (W : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N)
      (qD : Config (Torus d (L * n)) N → ℝ),
      (∀ φ, cinner (W φ) (gaussForm e Hα (W φ)) = cinner φ φ + qD φ) →
      baseRho1 d N L n β a z₁ ν h ψ g =
        ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
          ((((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
            ((((2 * Real.pi) ^ (-(Fintype.card (Torus d (L * n)) : ℝ) / 2) *
              |LinearMap.det (W : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N)| :
                ℝ) : ℂ) *
              ∫ φ : Config (Torus d (L * n)) N,
                (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
                  F (tangentProj e he (W φ)))) +
            baseFirstRest d N L n β a z₁ ν regimeB δ₀ h g ψ) := by
  intro θ G α e he Hα χ κ F W qD hW
  rw [baseRho1_eq_allGood_add_rest ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 hΛ2 hβ ha0 g ψ]
  congr 2
  have hK := baseSector_gaussForm_posDef_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H hΛ1
    θ φ₀ hp
  have hcore := baseSectorChartIntegral_eq_tangent hβ a ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1 g θ
  have hF : Measurable F := measurable_baseSectorF β a ν regimeB h g θ e he Hα χ
    (measurable_baseSectorCubeProduct regimeB ν δ₀ h θ) κ
  have hw := FRWhite.integral_tangent_gaussian_whitened e he Hα hK W qD hW F hF
  rw [hcore]
  exact congrArg _ hw

open Classical in
/-- **The all-good sector split along the `𝖱₁` test** (LFR Definition II.7.1, P5 (2.43) at `k = 0`):
the whitened all-good term of `baseRho1_allGood_whitened` is the sum of the small-fluctuation term
(`∏_x 1[|φ_x| < p₁]`) and its complement, provided the whitened integrand is integrable
(`hint`; the chart integrand is integrable because the spin integrand is bounded on the compact
sphere configuration space, `integral_sphere_pi_hemisphere_complex`; the transfer of this
integrability to the whitened Gaussian variable is not proved here). -/
theorem integral_whitened_allGood_split {ι : Type*} [Fintype ι] {N : ℕ} (p₁ : ℝ)
    (qD : Config ι N → ℝ) (Ψ : Config ι N → ℂ)
    (hint : Integrable fun φ : Config ι N =>
      (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) * Ψ φ) :
    ∫ φ : Config ι N, (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) * Ψ φ =
      (∫ φ : Config ι N, ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) *
        ((((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) * Ψ φ)) +
      ∫ φ : Config ι N, ((1 - rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) *
        ((((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) * Ψ φ) :=
  integral_rSmall_split p₁ _ hint

end Whitened

end Balaban.LargeField
