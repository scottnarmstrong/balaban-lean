/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.ChartIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The `𝖱₁` decomposition of a whitened Gaussian variable

On the whitened variables `ψ' = (ψ'_x)_x` of the sites of the good region `Ω` (a finite set `ι` of
sites, each in a cube `cube x` of a finite set `C` of cubes of `Ω`) the cube test is
`χ^{(0)}_c(ψ') = ∏_{x ∈ c} 1[|ψ'_x| < p₁]` (`cubeSmall`).  The binary partition of unity

`1 = ∑_{𝖱 ⊆ C} ∏_{c ∈ 𝖱} (1 - χ^{(0)}_c(ψ')) ∏_{c ∈ C \ 𝖱} χ^{(0)}_c(ψ')`

is exact for every `ψ'` (`rDecomp_pointwise`, `rDecomp_sum_eq_one`).  Its weights are measurable and
take values in `[0, 1]` (`measurable_rWeight`, `rWeight_nonneg`, `rWeight_le_one`), so it splits any
integrable integrand into integrable pieces (`rDecomp_integral`).  The term `𝖱 = ∅` is the
small-fluctuation test `∏_x 1[|ψ'_x| < p₁]` when the cubes of `C` cover the sites
(`rWeight_empty`).
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Classical

section RDecomp

variable {ι κ : Type*} [Fintype ι] {N : ℕ} (cube : ι → κ)

namespace Base

/-- **The cube test** `χ^{(0)}_c(ψ') = ∏_{x ∈ c} 1[|ψ'_x| < p₁]` on the whitened variables. -/
noncomputable def cubeSmall (p₁ : ℝ) (c : κ) (ψ : Config ι N) : ℝ :=
  ∏ x ∈ Finset.univ.filter (fun x => cube x = c), if ‖ψ x‖ < p₁ then 1 else 0

theorem cubeSmall_zero_or_one (p₁ : ℝ) (c : κ) (ψ : Config ι N) :
    cubeSmall cube p₁ c ψ = 0 ∨ cubeSmall cube p₁ c ψ = 1 := by
  unfold cubeSmall
  by_cases h : ∀ x ∈ Finset.univ.filter (fun x => cube x = c), ‖ψ x‖ < p₁
  · right; exact Finset.prod_eq_one fun x hx => by simp [h x hx]
  · left
    push Not at h
    obtain ⟨x, hx, hxp⟩ := h
    exact Finset.prod_eq_zero hx (by simp [not_lt.2 hxp])

theorem cubeSmall_nonneg (p₁ : ℝ) (c : κ) (ψ : Config ι N) : 0 ≤ cubeSmall cube p₁ c ψ := by
  rcases cubeSmall_zero_or_one cube p₁ c ψ with h | h <;> simp [h]

theorem cubeSmall_le_one (p₁ : ℝ) (c : κ) (ψ : Config ι N) : cubeSmall cube p₁ c ψ ≤ 1 := by
  rcases cubeSmall_zero_or_one cube p₁ c ψ with h | h <;> simp [h]

theorem measurable_cubeSmall (p₁ : ℝ) (c : κ) :
    Measurable (cubeSmall (ι := ι) (N := N) cube p₁ c) := by
  unfold cubeSmall
  refine Finset.measurable_prod _ fun x _ => ?_
  refine Measurable.ite (measurableSet_lt ?_ measurable_const) measurable_const measurable_const
  exact (measurable_pi_apply x).norm

/-- **The weight of the term `𝖱`** of the decomposition. -/
noncomputable def rWeight (C : Finset κ) (p₁ : ℝ) (R : Finset κ) (ψ : Config ι N) : ℝ :=
  (∏ c ∈ R, (1 - cubeSmall cube p₁ c ψ)) * ∏ c ∈ C \ R, cubeSmall cube p₁ c ψ

theorem rWeight_nonneg (C : Finset κ) (p₁ : ℝ) (R : Finset κ) (ψ : Config ι N) :
    0 ≤ rWeight cube C p₁ R ψ :=
  mul_nonneg (Finset.prod_nonneg fun c _ => sub_nonneg.mpr (cubeSmall_le_one cube p₁ c ψ))
    (Finset.prod_nonneg fun c _ => cubeSmall_nonneg cube p₁ c ψ)

theorem rWeight_le_one (C : Finset κ) (p₁ : ℝ) (R : Finset κ) (ψ : Config ι N) :
    rWeight cube C p₁ R ψ ≤ 1 := by
  unfold rWeight
  have h1 : ∏ c ∈ R, (1 - cubeSmall cube p₁ c ψ) ≤ 1 :=
    Finset.prod_le_one₀ (fun c _ => sub_nonneg.mpr (cubeSmall_le_one cube p₁ c ψ))
      (fun c _ => sub_le_self 1 (cubeSmall_nonneg cube p₁ c ψ))
  have h2 : ∏ c ∈ C \ R, cubeSmall cube p₁ c ψ ≤ 1 :=
    Finset.prod_le_one₀ (fun c _ => cubeSmall_nonneg cube p₁ c ψ)
      (fun c _ => cubeSmall_le_one cube p₁ c ψ)
  have h3 : 0 ≤ ∏ c ∈ R, (1 - cubeSmall cube p₁ c ψ) :=
    Finset.prod_nonneg fun c _ => sub_nonneg.mpr (cubeSmall_le_one cube p₁ c ψ)
  have h4 : 0 ≤ ∏ c ∈ C \ R, cubeSmall cube p₁ c ψ :=
    Finset.prod_nonneg fun c _ => cubeSmall_nonneg cube p₁ c ψ
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 h4 zero_le_one
    _ = 1 := one_mul 1

theorem measurable_rWeight (C : Finset κ) (p₁ : ℝ) (R : Finset κ) :
    Measurable (rWeight (ι := ι) (N := N) cube C p₁ R) := by
  unfold rWeight
  exact (Finset.measurable_prod _ fun c _ =>
      measurable_const.sub (measurable_cubeSmall cube p₁ c)).mul
    (Finset.measurable_prod _ fun c _ => measurable_cubeSmall cube p₁ c)

/-- **The partition of unity**: the weights of the decomposition sum to `1`. -/
theorem rDecomp_sum_eq_one (C : Finset κ) (p₁ : ℝ) (ψ : Config ι N) :
    ∑ R ∈ C.powerset, rWeight cube C p₁ R ψ = 1 := by
  unfold rWeight
  rw [← Finset.prod_add]
  exact Finset.prod_eq_one fun c _ => by ring

/-- **The `𝖱₁` decomposition, pointwise**: an arbitrary function is the sum of its weighted
copies. -/
theorem rDecomp_pointwise (C : Finset κ) (p₁ : ℝ) (F : Config ι N → ℂ) (ψ : Config ι N) :
    F ψ = ∑ R ∈ C.powerset, ((rWeight cube C p₁ R ψ : ℝ) : ℂ) * F ψ := by
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, rDecomp_sum_eq_one]
  simp

/-- **The `𝖱₁` decomposition, integrated**: an integrable function (for any measure on the
whitened variables) has the integral equal to the sum of the integrals of the weighted copies. -/
theorem rDecomp_integral (C : Finset κ) (p₁ : ℝ)
    (μ : Measure (Config ι N)) (F : Config ι N → ℂ) (hF : Integrable F μ) :
    ∫ ψ, F ψ ∂μ = ∑ R ∈ C.powerset, ∫ ψ, ((rWeight cube C p₁ R ψ : ℝ) : ℂ) * F ψ ∂μ := by
  have hInt : ∀ R ∈ C.powerset,
      Integrable (fun ψ => ((rWeight cube C p₁ R ψ : ℝ) : ℂ) * F ψ) μ := by
    intro R _
    refine hF.norm.mono' ((Complex.measurable_ofReal.comp (measurable_rWeight cube C p₁ R)).aestronglyMeasurable.mul
      hF.aestronglyMeasurable) (Filter.Eventually.of_forall fun ψ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rWeight_nonneg cube C p₁ R ψ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (rWeight_le_one cube C p₁ R ψ)
  conv_lhs => arg 2; ext ψ; rw [rDecomp_pointwise cube C p₁ F ψ]
  rw [integral_finsetSum _ hInt]

/-- **The term `𝖱 = ∅`** is the product of the cube tests, which is the small-fluctuation test
`∏_x 1[|ψ'_x| < p₁]` when every site lies in a cube of `C`. -/
theorem rWeight_empty (C : Finset κ) (p₁ : ℝ) (hC : ∀ x, cube x ∈ C) (ψ : Config ι N) :
    rWeight cube C p₁ ∅ ψ = ∏ x, if ‖ψ x‖ < p₁ then 1 else 0 := by
  unfold rWeight cubeSmall
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := C) (g := cube)
    (fun x _ => hC x)]
  
end Base

end RDecomp

end Balaban.LargeField
