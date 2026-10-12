/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RopNorm

/-!
# The normalization of `R` when the reference densities are good almost everywhere (Lemma III.8.4)

`ropProd_norm_ae`, `R_normalization_ae`, `R_normalization_sum_ae` are the Fubini argument of `RopNorm.lean` with the
integrability and positivity of the reference densities `ρ_{k,0}(Z)` required only for almost every value of the
remaining variables `ψ_k↾𝒵^c_{σ,0}` (they are defined from the unconditional solution `ψ⁰_k` of (2.34), which exists
for `ψ_k` in the tube `Ψ̃` only, so the densities are good on the tube and the field space is the tube).
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Function

namespace Balaban.LargeField

section Norm

variable {ι : Type} [Fintype ι] {W : ι → Type} [∀ c, MeasurableSpace (W c)] (μ : ∀ c, Measure (W c))
  [∀ c, SigmaFinite (μ c)] {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]

theorem ropProd_norm_ae (r : ∀ c, W c → Y → ℝ) (ρ : ((∀ c, W c) × Y) → ℝ)
    (hρ : Integrable ρ ((Measure.pi μ).prod ν))
    (hmeas : ∀ c, Measurable (fun p : W c × Y => r c p.1 p.2))
    (hnn : ∀ c w y, 0 ≤ r c w y)
    (hint : ∀ᵐ y ∂ν, ∀ c, Integrable (fun w => r c w y) (μ c))
    (hpos : ∀ᵐ y ∂ν, ∀ c, 0 < ∫ w, r c w y ∂(μ c)) :
    Integrable (RopProd μ r ρ) ((Measure.pi μ).prod ν) ∧
      ∫ p, RopProd μ r ρ p ∂((Measure.pi μ).prod ν) = ∫ p, ρ p ∂((Measure.pi μ).prod ν) := by
  set P : ((∀ c, W c) × Y) → ℝ := fun p => ∏ c, r c (p.1 c) p.2 with hP
  set Dn : Y → ℝ := fun y => ∏ c, ∫ w, r c w y ∂(μ c) with hDn
  set Nn : Y → ℝ := fun y => ∫ x, ρ (x, y) ∂(Measure.pi μ) with hNn
  have hgood : ∀ᵐ y ∂ν, (∀ c, Integrable (fun w => r c w y) (μ c)) ∧ ∀ c, 0 < ∫ w, r c w y ∂(μ c) :=
    hint.and hpos
  have hDpos : ∀ y, (∀ c, 0 < ∫ w, r c w y ∂(μ c)) → 0 < Dn y := fun y h =>
    Finset.prod_pos fun c _ => h c
  have hPnn : ∀ p, 0 ≤ P p := fun p => Finset.prod_nonneg fun c _ => hnn c _ _
  have hPint : ∀ y, (∀ c, Integrable (fun w => r c w y) (μ c)) →
      Integrable (fun x : ∀ c, W c => P (x, y)) (Measure.pi μ) := fun y h =>
    Integrable.fintype_prod_dep (f := fun c w => r c w y) (fun c => h c)
  have hPval : ∀ y, ∫ x, P (x, y) ∂(Measure.pi μ) = Dn y := fun y =>
    integral_fintype_prod_eq_prod (f := fun c w => r c w y)
  have hPmeas : Measurable P := by
    refine Finset.measurable_prod _ fun c _ => ?_
    exact (hmeas c).comp (by fun_prop : Measurable fun p : (∀ c, W c) × Y => (p.1 c, p.2))
  have hNint : Integrable Nn ν := hρ.integral_prod_right
  have hDmeas : Measurable Dn := by
    refine Finset.measurable_prod _ fun c _ => ?_
    have : StronglyMeasurable (uncurry fun (w : W c) (y : Y) => r c w y) := (hmeas c).stronglyMeasurable
    exact (this.integral_prod_left (μ := μ c)).measurable
  have hRop : RopProd μ r ρ = fun p => P p * (Nn p.2 * (Dn p.2)⁻¹) := by
    funext p; simp only [RopProd, hP, hNn, hDn, div_eq_mul_inv]
  have hRmeas : AEStronglyMeasurable (RopProd μ r ρ) ((Measure.pi μ).prod ν) := by
    have h1 : AEStronglyMeasurable (fun y => Nn y * (Dn y)⁻¹) ν :=
      hNint.1.mul hDmeas.inv.aestronglyMeasurable
    rw [hRop]
    exact hPmeas.aestronglyMeasurable.mul h1.comp_snd
  have hRint : Integrable (RopProd μ r ρ) ((Measure.pi μ).prod ν) := by
    rw [integrable_prod_iff' hRmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [hgood] with y hy
      rw [hRop]
      exact (hPint y hy.1).mul_const (Nn y * (Dn y)⁻¹)
    · refine hNint.norm.congr ?_
      filter_upwards [hgood] with y hy
      have hDy := hDpos y hy.2
      rw [hRop]
      simp only
      have : ∀ x : ∀ c, W c, ‖P (x, y) * (Nn y * (Dn y)⁻¹)‖ = P (x, y) * ‖Nn y * (Dn y)⁻¹‖ := fun x => by
        rw [norm_mul, Real.norm_of_nonneg (hPnn _)]
      simp_rw [this]
      rw [integral_mul_const, hPval y, norm_mul, norm_inv, Real.norm_of_nonneg hDy.le]
      field_simp [hDy.ne']
  refine ⟨hRint, ?_⟩
  rw [integral_prod_symm _ hRint, integral_prod_symm _ hρ]
  refine integral_congr_ae ?_
  filter_upwards [hgood] with y hy
  have hDy := hDpos y hy.2
  rw [hRop]
  simp only
  rw [integral_mul_const, hPval y]
  field_simp [hDy.ne']
  rfl

end Norm

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

theorem R_normalization_ae (D : RDecomp ν) {ρ : Ω → ℝ} (hρ : Integrable ρ ν)
    (hmeas : ∀ c, Measurable (fun p : D.W c × D.Y => D.r c p.1 p.2))
    (hnn : ∀ c w y, 0 ≤ D.r c w y)
    (hint : ∀ᵐ y ∂D.νY, ∀ c, Integrable (fun w => D.r c w y) (D.μ c))
    (hpos : ∀ᵐ y ∂D.νY, ∀ c, 0 < ∫ w, D.r c w y ∂(D.μ c)) :
    Integrable (Rop D ρ) ν ∧ ∫ ψ, Rop D ρ ψ ∂ν = ∫ ψ, ρ ψ ∂ν := by
  set ρt : ((∀ c, D.W c) × D.Y) → ℝ := fun p => ρ (D.e.symm p) with hρt
  have hρe : ρ = ρt ∘ D.e := by funext ψ; simp [hρt]
  have hρt_int : Integrable ρt ((Measure.pi D.μ).prod D.νY) := by
    rw [hρe] at hρ
    exact (D.mp.integrable_comp_emb D.e.measurableEmbedding).1 hρ
  obtain ⟨hint1, heq⟩ := ropProd_norm_ae D.μ D.νY D.r ρt hρt_int hmeas hnn hint hpos
  have hR : Rop D ρ = RopProd D.μ D.r ρt ∘ D.e := rfl
  refine ⟨?_, ?_⟩
  · rw [hR]; exact (D.mp.integrable_comp_emb D.e.measurableEmbedding).2 hint1
  · have e1 : ∫ ψ, Rop D ρ ψ ∂ν = ∫ p, RopProd D.μ D.r ρt p ∂((Measure.pi D.μ).prod D.νY) :=
      D.mp.integral_comp' (RopProd D.μ D.r ρt)
    have e2 : ∫ ψ, ρ ψ ∂ν = ∫ p, ρt p ∂((Measure.pi D.μ).prod D.νY) := by
      have := D.mp.integral_comp' ρt
      rw [← this]; exact integral_congr_ae (Filter.Eventually.of_forall fun ψ => by simp [hρt])
    rw [e1, e2, heq]

theorem R_normalization_sum_ae {T : Type*} [Fintype T] (D : T → RDecomp ν) {ρ : T → Ω → ℝ}
    (hρ : ∀ t, Integrable (ρ t) ν)
    (hmeas : ∀ t c, Measurable (fun p : (D t).W c × (D t).Y => (D t).r c p.1 p.2))
    (hnn : ∀ t c w y, 0 ≤ (D t).r c w y)
    (hint : ∀ t, ∀ᵐ y ∂(D t).νY, ∀ c, Integrable (fun w => (D t).r c w y) ((D t).μ c))
    (hpos : ∀ t, ∀ᵐ y ∂(D t).νY, ∀ c, 0 < ∫ w, (D t).r c w y ∂((D t).μ c)) :
    Integrable (RopSum D ρ) ν ∧ ∫ ψ, RopSum D ρ ψ ∂ν = ∫ ψ, (∑ t, ρ t ψ) ∂ν := by
  have h := fun t => R_normalization_ae (D t) (hρ t) (hmeas t) (hnn t) (hint t) (hpos t)
  have hsum : RopSum D ρ = fun ψ => ∑ t, Rop (D t) (ρ t) ψ := rfl
  refine ⟨?_, ?_⟩
  · rw [hsum]; exact integrable_finsetSum _ fun t _ => (h t).1
  · rw [hsum, integral_finsetSum _ fun t _ => (h t).1, integral_finsetSum _ fun t _ => hρ t]
    exact Finset.sum_congr rfl fun t _ => (h t).2

end Field




end Balaban.LargeField
