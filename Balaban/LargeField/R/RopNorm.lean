/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.Rop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The normalization of `R` (Lemma III.8.4, P7 (1.7)-(1.8)): `∫ ρ' dψ_k = ∫ ρ dψ_k`

The Fubini argument of the source proof, in the form of `ropProd_norm` (on the product of the variables
`ψ_k↾𝒵_{σ,0}` and the remaining variables) and `R_normalization_of_indep` (on the field space of an `RDecomp`).

The facts used by the source proof that are **not derived here** are the following named hypotheses of
`R_normalization_of_indep` (and `R_normalization_sum_of_indep`):

* `hρ` (absolute integrability of the term `ρ(𝔸, σ)`; source: (1.26), Lemma II.6.3 (b), boundedness of the small-field
  factor on the support of `χ_k`);
* `hmeas`, `hnn` (the reference densities `ρ_{k,0}(Z)` are measurable and non-negative: they are `χ_{Z₀}` times an
  exponential);
* `hint`, `hpos` (each `ρ_{k,0}(Z)` is integrable in `ψ_k↾Z₀` with positive integral: Lemma III.8.2, `denominator_eq`,
  `Denominator.lean`, for the `ρ_{k,0}` of `RhoZero.lean`).

The independence statements of the source proof (Lemma III.1.5 and Definition III.5.1: the factors of `ρ(𝔸, σ)` read
`ψ_k↾Z₀` only through the composed Gaussians; the boundary terms and the small-field functions do not read
`ψ_k↾𝒵_{σ,0}`; the denominators do not depend on `ψ_k↾𝒵_{σ,0}`) enter the normalization only through the form of the
data `RDecomp.r`: `ρ_{k,0}(Z)` is a function of `(ψ_k↾Z₀, ψ_k↾𝒵^c_{σ,0})`.  The concrete `ρ_{k,0}(Z)` of `RhoZero.lean`
reads `ψ_k` on `Z₀` and on the blocks of the generating set of `U_k = Z^≈`; its identification with a function of
`(ψ_k↾Z₀, ψ_k↾𝒵^c_{σ,0})` needs the separation of the components of `𝒵_σ` (the `Z'_0`, `Z' ≠ Z`, do not meet `U_k(Z)`),
which is the geometric input `RDecomp` takes as given.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Function

namespace Balaban.LargeField

section Norm

variable {ι : Type} [Fintype ι] {W : ι → Type} [∀ c, MeasurableSpace (W c)] (μ : ∀ c, Measure (W c))
  [∀ c, SigmaFinite (μ c)] {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]

/-- **Fubini step of Lemma III.8.4**, on the product of the variables of `𝒵_{σ,0}` and the others. -/
theorem ropProd_norm (r : ∀ c, W c → Y → ℝ) (ρ : ((∀ c, W c) × Y) → ℝ)
    (hρ : Integrable ρ ((Measure.pi μ).prod ν))
    (hmeas : ∀ c, Measurable (fun p : W c × Y => r c p.1 p.2))
    (hnn : ∀ c w y, 0 ≤ r c w y) (hint : ∀ c y, Integrable (fun w => r c w y) (μ c))
    (hpos : ∀ c y, 0 < ∫ w, r c w y ∂(μ c)) :
    Integrable (RopProd μ r ρ) ((Measure.pi μ).prod ν) ∧
      ∫ p, RopProd μ r ρ p ∂((Measure.pi μ).prod ν) = ∫ p, ρ p ∂((Measure.pi μ).prod ν) := by
  set P : ((∀ c, W c) × Y) → ℝ := fun p => ∏ c, r c (p.1 c) p.2 with hP
  set Dn : Y → ℝ := fun y => ∏ c, ∫ w, r c w y ∂(μ c) with hDn
  set Nn : Y → ℝ := fun y => ∫ x, ρ (x, y) ∂(Measure.pi μ) with hNn
  have hDpos : ∀ y, 0 < Dn y := fun y => Finset.prod_pos fun c _ => hpos c y
  have hPnn : ∀ p, 0 ≤ P p := fun p => Finset.prod_nonneg fun c _ => hnn c _ _
  have hPint : ∀ y, Integrable (fun x : ∀ c, W c => P (x, y)) (Measure.pi μ) := fun y =>
    Integrable.fintype_prod_dep (f := fun c w => r c w y) (fun c => hint c y)
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
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · rw [hRop]
      exact (hPint y).mul_const (Nn y * (Dn y)⁻¹)
    · have : (fun y => ∫ x, ‖RopProd μ r ρ (x, y)‖ ∂(Measure.pi μ)) = fun y => ‖Nn y‖ := by
        funext y
        rw [hRop]
        simp only
        have : ∀ x : ∀ c, W c, ‖P (x, y) * (Nn y * (Dn y)⁻¹)‖ = P (x, y) * ‖Nn y * (Dn y)⁻¹‖ := fun x => by
          rw [norm_mul, Real.norm_of_nonneg (hPnn _)]
        simp_rw [this]
        rw [integral_mul_const, hPval y, norm_mul, norm_inv, Real.norm_of_nonneg (hDpos y).le]
        field_simp [(hDpos y).ne']
      rw [this]
      exact hNint.norm
  refine ⟨hRint, ?_⟩
  rw [integral_prod_symm _ hRint, integral_prod_symm _ hρ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [hRop]
  simp only
  rw [integral_mul_const, hPval y]
  field_simp [(hDpos y).ne']
  rfl


end Norm

section Field

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- **Lemma III.8.4 (normalization), for one term `ρ(𝔸, σ)`** (P7 (1.7)): `R[ρ]` is integrable and `∫ R[ρ] = ∫ ρ`,
given the integrability of `ρ` and the properties of the reference densities listed in the module docstring. -/
theorem R_normalization_of_indep (D : RDecomp ν) {ρ : Ω → ℝ} (hρ : Integrable ρ ν)
    (hmeas : ∀ c, Measurable (fun p : D.W c × D.Y => D.r c p.1 p.2))
    (hnn : ∀ c w y, 0 ≤ D.r c w y) (hint : ∀ c y, Integrable (fun w => D.r c w y) (D.μ c))
    (hpos : ∀ c y, 0 < ∫ w, D.r c w y ∂(D.μ c)) :
    Integrable (Rop D ρ) ν ∧ ∫ ψ, Rop D ρ ψ ∂ν = ∫ ψ, ρ ψ ∂ν := by
  set ρt : ((∀ c, D.W c) × D.Y) → ℝ := fun p => ρ (D.e.symm p) with hρt
  have hρe : ρ = ρt ∘ D.e := by funext ψ; simp [hρt]
  have hρt_int : Integrable ρt ((Measure.pi D.μ).prod D.νY) := by
    rw [hρe] at hρ
    exact (D.mp.integrable_comp_emb D.e.measurableEmbedding).1 hρ
  obtain ⟨hint1, heq⟩ := ropProd_norm D.μ D.νY D.r ρt hρt_int hmeas hnn hint hpos
  have hR : Rop D ρ = RopProd D.μ D.r ρt ∘ D.e := rfl
  refine ⟨?_, ?_⟩
  · rw [hR]; exact (D.mp.integrable_comp_emb D.e.measurableEmbedding).2 hint1
  · have e1 : ∫ ψ, Rop D ρ ψ ∂ν = ∫ p, RopProd D.μ D.r ρt p ∂((Measure.pi D.μ).prod D.νY) :=
      D.mp.integral_comp' (RopProd D.μ D.r ρt)
    have e2 : ∫ ψ, ρ ψ ∂ν = ∫ p, ρt p ∂((Measure.pi D.μ).prod D.νY) := by
      have := D.mp.integral_comp' ρt
      rw [← this]; exact integral_congr_ae (Filter.Eventually.of_forall fun ψ => by simp [hρt])
    rw [e1, e2, heq]

/-- **Lemma III.8.4 for `ρ' = Σ_{(𝔸,σ)} R[ρ(𝔸,σ)]`** and `ρ = Σ_{(𝔸,σ)} ρ(𝔸,σ)`: term by term. -/
theorem R_normalization_sum_of_indep {T : Type*} [Fintype T] (D : T → RDecomp ν) {ρ : T → Ω → ℝ}
    (hρ : ∀ t, Integrable (ρ t) ν)
    (hmeas : ∀ t c, Measurable (fun p : (D t).W c × (D t).Y => (D t).r c p.1 p.2))
    (hnn : ∀ t c w y, 0 ≤ (D t).r c w y)
    (hint : ∀ t c y, Integrable (fun w => (D t).r c w y) ((D t).μ c))
    (hpos : ∀ t c y, 0 < ∫ w, (D t).r c w y ∂((D t).μ c)) :
    Integrable (RopSum D ρ) ν ∧ ∫ ψ, RopSum D ρ ψ ∂ν = ∫ ψ, (∑ t, ρ t ψ) ∂ν := by
  have h := fun t => R_normalization_of_indep (D t) (hρ t) (hmeas t) (hnn t) (hint t) (hpos t)
  have hsum : RopSum D ρ = fun ψ => ∑ t, Rop (D t) (ρ t) ψ := rfl
  refine ⟨?_, ?_⟩
  · rw [hsum]; exact integrable_finsetSum _ fun t _ => (h t).1
  · rw [hsum, integral_finsetSum _ fun t _ => (h t).1, integral_finsetSum _ fun t _ => hρ t]
    exact Finset.sum_congr rfl fun t _ => (h t).2

end Field

end Balaban.LargeField
