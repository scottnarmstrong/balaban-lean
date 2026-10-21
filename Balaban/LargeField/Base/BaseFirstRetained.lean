/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRecordRetained
public import Balaban.LargeField.Base.BaseFirstPhysicalConditional

/-!
# The first density as a sum of integrals over the retained spins

The first density `baseRho1` is the sum over the sets `P` of failed cubes of the integral of the
weight `∏_{c ∈ P} (1 - χ'_c) ∏_{c ∉ P} χ'_c` times the physical density (`baseRho1_eq_sum_firstP`).
For a set `fam` of sets `P` and a generating set `Gf P` for each of them, the terms with `P ∈ fam` are
the iterated integrals over the retained spins (those outside the good region of `Gf P`) and the
interior spins (`baseRho1_eq_sum_retained`); for each retained configuration the interior integral
is the integral over the spins of the good region at the merged configuration, which is a chart
Gaussian integral by `baseRecord_physical_chartGaussian`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Classical MeasureTheory

noncomputable section

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- A bounded measurable weight times an integrable function is integrable. -/
theorem integrable_weight_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : X → ℂ} (hF : Integrable F μ) {w : X → ℝ} (hw : Measurable w) (hw1 : ∀ x, |w x| ≤ 1) :
    Integrable (fun x => ((w x : ℝ) : ℂ) * F x) μ := by
  refine hF.norm.mono' ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
    hF.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw1 x)

/-- **The weight of the base decomposition**: `∏_{c ∈ P} (1 - χ'_c) ∏_{c ∉ P} χ'_c`. -/
def firstWeight (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : ℝ :=
  recordWeightIn P regimeB ν δ₀ h θ φ * recordWeightOut P regimeB ν δ₀ h θ φ

/-- **The physical first-step density** `baseKernel · exp(-β energy + ⟨g, ·⟩)`. -/
def firstDensity (β a ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) : ℂ :=
  ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
    Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
      ∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))

variable {ϱ : ℝ}

/-- **The first density as a sum of integrals over the retained spins.**  For any family `Gf` of
generating sets (one for each set `P` of failed cubes) and any set `fam` of sets `P`, the terms with
`P ∈ fam` of the decomposition `baseRho1_eq_sum_firstP` are integrals over the retained spins (the
sites outside the good region of `Gf P`) of the integral over the spins of the good region of the
weighted density at the merged configuration; the other terms are unchanged. -/
theorem baseRho1_eq_sum_retained [NeZero N] (β a z ν : ℝ) (regimeB : Prop) (δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (Gf : Finset (Torus d n) → GeneratingSet d L (1 * n) 1 ϱ)
    (fam : Finset (Finset (Torus d n))) (ε₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    baseRho1 d N L n β a z ν h ψ g =
      ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        ((∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset.filter (· ∈ fam),
          ∫ σ : ↥(retSet (Gf P)) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
            ∫ ψ' : (Gf P).Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
              ((firstWeight P regimeB ν δ₀ h (z • ψ)
                  (baseMerge (Gf P) (retExtend (Gf P) σ ε₀) ψ') : ℝ) : ℂ) *
                firstDensity β a ν h g (z • ψ) (baseMerge (Gf P) (retExtend (Gf P) σ ε₀) ψ')
              ∂(Measure.pi fun _ : (Gf P).Ω 1 =>
                (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
            ∂(Measure.pi fun _ : ↥(retSet (Gf P)) =>
              (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) +
        ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset.filter (· ∉ fam),
          ∫ φ, ((firstWeight P regimeB ν δ₀ h (z • ψ) φ : ℝ) : ℂ) *
            firstDensity β a ν h g (z • ψ) φ ∂aprioriMeasure d N (L * n)) := by
  have hpart := baseRho1_eq_sum_firstP (d := d) (N := N) (L := L) (n := n) β a z ν regimeB δ₀ h g ψ
  have hFint : Integrable (firstDensity β a ν h g (z • ψ) : CfgT d N L n → ℂ)
      (aprioriMeasure d N (L * n)) := baseRho1_spinIntegrand_integrable β a z ν h ψ g
  change baseRho1 d N L n β a z ν h ψ g = ((z ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
    ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset,
      ∫ φ, ((firstWeight P regimeB ν δ₀ h (z • ψ) φ : ℝ) : ℂ) *
        firstDensity β a ν h g (z • ψ) φ ∂aprioriMeasure d N (L * n) at hpart
  rw [hpart, ← Finset.sum_filter_add_sum_filter_not _ (· ∈ fam)]
  congr 2
  refine Finset.sum_congr rfl fun P _ => ?_
  obtain ⟨hw, hw0, hw1⟩ := baseFirstPhysicalP_weight_measurable_unit
    (d := d) (N := N) (L := L) (n := n) regimeB ν δ₀ h (z • ψ) P
  have hInt := integrable_weight_mul hFint (w := firstWeight P regimeB ν δ₀ h (z • ψ)) hw
    (fun φ => (abs_of_nonneg (hw0 φ)).trans_le (hw1 φ))
  have hdis := baseRetained_disintegrate d N L n (retSet (Gf P))
    (fun φ : CfgT d N L n => ((firstWeight P regimeB ν δ₀ h (z • ψ) φ : ℝ) : ℂ) *
      firstDensity β a ν h g (z • ψ) φ) hInt
  rw [hdis]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact integral_interior_eq_merge (Gf P) (fun φ => ((firstWeight P regimeB ν δ₀ h (z • ψ) φ : ℝ) : ℂ) *
    firstDensity β a ν h g (z • ψ) φ) σ ε₀

/-- **The interior integral at fixed retained spins.**  For a base record `br` with failed cubes `P`
and good region the sites of the generating set `G`, the integral over the spins of the good region
of the weighted density at the merged configuration with the retained spins `σ` vanishes, or there
are lifted data `D` for which it is the failed-cube factor at `σ` times the chart Gaussian
integral (`recordGaussRHS`). -/
theorem baseRetained_inner_eval {Rk : ℝ} (G : GeneratingSet d L (1 * n) 1 ϱ)
    (br : BaseRecord d L (baseSectorN L n 1) Rk) (P : Finset (Torus d n))
    (hP : br.P = (↑P : Set (Torus d n)))
    (hΩ : ∀ x, x ∈ G.Ω 1 ↔ cubeMap (baseSectorN L n) L 1 1 1 x ∈ br.Omega)
    {β : ℝ} (hβ : 0 < β) (a : ℕ → ℝ) (a₀ ν δ₀ : ℝ) (regimeB : Prop) (ha : a 1 = a₀)
    (hδ₀ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (Hbg : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (φ₀ : CfgT d N L n) :
    (∫ ψ', ((firstWeight P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ') : ℝ) : ℂ) *
        firstDensity β a₀ ν h g θ (baseMerge G φ₀ ψ')
        ∂(Measure.pi fun _ : G.Ω 1 => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
      = 0) ∨
    ∃ D : BgData G N,
      (∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i =
        ((baseSectorTheta θ (jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ)) ∧
      (∀ x ∈ collar G, ∀ i, D.Ψ x i = ((baseSectorSpin φ₀ x i : ℝ) : ℂ)) ∧
      (∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ)) ∧
      ∀ he : ∀ x, ‖bgCenter G a (if regimeB then ν else 0) D x‖ = 1,
        ∃ R : Config (G.Ω 1) N ≃ₗ[ℝ] Config (G.Ω 1) N,
          (∀ v, gaussForm (bgCenter G a (if regimeB then ν else 0) D)
            (bgHess G a (if regimeB then ν else 0) D) (R (R v)) = v) ∧
          (∀ u v, cinner (R u) v = cinner u (R v)) ∧
          LinearMap.det (R : Config (G.Ω 1) N →ₗ[ℝ] Config (G.Ω 1) N) =
            Real.sqrt (LinearMap.det (gaussForm (bgCenter G a (if regimeB then ν else 0) D)
              (bgHess G a (if regimeB then ν else 0) D)))⁻¹ ∧
          ∫ ψ', ((firstWeight P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ') : ℝ) : ℂ) *
              firstDensity β a₀ ν h g θ (baseMerge G φ₀ ψ')
              ∂(Measure.pi fun _ : G.Ω 1 =>
                (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
            recordGaussRHS (G := G) P regimeB β a₀ ν δ₀ a h θ g φ₀ D he R := by
  by_cases hex : ∃ ψ, recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) ≠ 0
  · right
    obtain ⟨D, hDΨ, hDc, hDh⟩ := exists_recordDatum G θ h φ₀
    refine ⟨D, hDΨ, hDc, hDh, fun he => ?_⟩
    exact baseRecord_physical_chartGaussian br P hP hΩ hβ a a₀ ν δ₀ regimeB ha hδ₀ h hh θ g φ₀
      Hbg hΛ1 hΛ2 D hDΨ hDc hDh hex he
  · left
    push Not at hex
    exact baseRecord_integral_eq_zero P regimeB ν δ₀ β a₀ h θ g φ₀ hex

end

end Balaban.LargeField
