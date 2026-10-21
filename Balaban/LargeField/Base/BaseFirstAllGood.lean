/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFirstPhysicalP
public import Balaban.LargeField.Base.BaseChartComponentNormalization

/-!
# The all-good sector of the first density, exactly

LFR Lemmas II.7.3–II.7.5, LF-BASE-KF0 (A.3), BASE-KERNEL §2. The first density
`ρ₁(ψ; g) = z₁^{N|𝕋_n|} ∫ K(z₁ψ, φ) e^{-βH(φ) + ⟨g, φ⟩} dσ(φ)` is the exact sum over the sets `P₁` of
failed cubes of the selected spin integrals (`baseRho1_eq_sum_firstP`). The term `P₁ = ∅` (all cubes
good, the weight `∏_c χ'^{(0)}_c`) is the hemisphere chart integral of the hard-spin model around
the background (`baseGoodIntegral_eq_baseChartIntegral`), which is the Gaussian integral of the
cut Hessian with the exact normal-coordinate remainder
(`baseSectorChartIntegral_eq_normalized`):

* `baseRho1_eq_allGood_add_rest`: `ρ₁ = z₁^{N|𝕋_n|} (chart integral of the all-good sector +
  ∑_{P₁ ≠ ∅} selected spin integrals)`, exactly, for every `ψ` and `g`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

open Classical in
/-- **The sectors with failed cubes**: the sum over the nonempty sets `P₁` of failed cubes of the
selected spin integrals of `baseRho1_eq_sum_firstP` (the weights `∏_{c ∈ P₁}(1 - χ'_c)
∏_{c ∉ P₁} χ'_c`), the all-good sector `P₁ = ∅` excluded. -/
noncomputable def baseFirstRest (d N L n : ℕ) [NeZero L] [NeZero n] (β a z₁ ν : ℝ)
    (regimeB : Prop) (δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (ψ : Torus d n → EuclideanSpace ℝ (Fin N)) : ℂ :=
  ∑ P ∈ (Finset.univ : Finset (Torus d n)).powerset.erase ∅,
            ∫ φ, (((∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀
                (fun i => h i) c (baseSectorSpin φ, baseSectorTheta (z₁ • ψ)))) *
              ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
                chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
                  (baseSectorSpin φ, baseSectorTheta (z₁ • ψ)) : ℝ) : ℂ) *
              (((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) *
                Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
                  ∑ x : Torus d (L * n), ∑ i : Fin N,
                    g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
              ∂aprioriMeasure d N (L * n)

open Classical in
/-- **The first density, the all-good term and the rest.** With `θ = z₁ψ`, the cutoff
`χ = ∏_c χ'^{(0)}_c` (`baseSectorCubeProduct`) and the centre `e = baseSectorCenter` (the real
first-step background where it exists, `h` elsewhere), the term `P₁ = ∅` of `baseRho1_eq_sum_firstP`
is the chart integral `baseChartIntegral` (hemisphere chart around `e`, weights
`∏ (1 - |ξ_x|²)^{-1/2}`, source `g`). -/
theorem baseRho1_eq_allGood_add_rest
    (ϱ : ℝ) (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    {β a z₁ : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (g : Torus d (L * n) → Fin N → ℂ) (ψ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    baseRho1 d N L n β a z₁ ν h ψ g =
      ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
        (baseChartIntegral d N L n β a ν h g (z₁ • ψ)
            (baseSectorCubeProduct regimeB ν δ₀ h (z₁ • ψ))
            (baseSectorCenter ϱ aw regimeB ν h (z₁ • ψ))
            (baseSectorCenter_unit ϱ aw regimeB ν h hh H (z₁ • ψ)) +
          baseFirstRest d N L n β a z₁ ν regimeB δ₀ h g ψ) := by
  classical
  rw [baseRho1_eq_sum_firstP β a z₁ ν regimeB δ₀ h g ψ]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_powerset.2 (Finset.empty_subset _))]
  congr 1
  have hmeas := measurable_baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
    regimeB ν δ₀ h (z₁ • ψ)
  have hbound : ∀ φ, |baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
      regimeB ν δ₀ h (z₁ • ψ) φ| ≤ 1 := by
    intro φ
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 (z₁ • ψ) φ]
    exact baseSectorCutoff_abs_le_one ϱ regimeB ν δ₀ h (z₁ • ψ) φ
  have hsupport : ∀ φ, (∃ x, ¬ 0 < inner ℝ (baseSectorCenter ϱ aw regimeB ν h (z₁ • ψ) x)
      (φ x : EuclideanSpace ℝ (Fin N))) →
      baseSectorCubeProduct (d := d) (N := N) (L := L) (n := n)
        regimeB ν δ₀ h (z₁ • ψ) φ = 0 := by
    intro φ hbad
    rw [← baseSectorCutoff_eq_cubeProduct ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 (z₁ • ψ) φ]
    exact baseSectorCutoff_hemisphere_support ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 hΛ2 (z₁ • ψ) φ hbad
  rw [← baseGoodIntegral_eq_baseChartIntegral hβ ha ν h g (z₁ • ψ) _ hmeas hbound
    (baseSectorCenter ϱ aw regimeB ν h (z₁ • ψ))
    (baseSectorCenter_unit ϱ aw regimeB ν h hh H (z₁ • ψ)) hsupport]
  unfold baseGoodIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty, baseSectorCubeProduct, mul_assoc]

open Classical in
/-- **The all-good sector of the first density, exactly** (LFR Lemmas II.7.3–II.7.5; LF-BASE-KF0
(A.3); BASE-KERNEL §2). On a nonempty all-good sector (`∏_c χ'^{(0)}_c ≠ 0` at some spin
configuration), with `θ = z₁ψ`: the density `ρ₁(ψ; g)` is `z₁^{N|𝕋_n|}` times the sum of

* the Gaussian chart integral of the all-good sector: `(√β)^{-(N-1)|𝕋_{Ln}|}` times
  `(2π)^{(N-1)|𝕋_{Ln}|/2} (det A_e)^{-1/2}` (`A_e` = `gaussForm e Hα`, the cut Hessian of P4 (2.44)
  with the weights `a₀ = aw 1`) times the expectation, under the standard Gaussian, of
  `J_β(w) χ(φ) κ exp(-β(H(e) + (a₀ L^d / 2L²) ∑_y |θ_y - (Qe)_y|²) + ⟨g, e⟩ + β^{-1/2}⟨g, w + z⟩ -
  ⟨w, H z⟩ - ½⟨z, H z⟩ - M)` with the chart Jacobian `J_β`, the normal shift `z` (the exact
  remainder), the mass difference `M`, and `κ = ∏_y (β a₀ L^d/(2π L²))^{N/2}` the normalization of
  the Gaussian kernel (`baseSectorChartIntegral_eq_normalized`), and
* the sectors with failed cubes (`baseFirstRest`). -/
theorem baseRho1_allGood_gaussian
    {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]
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
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let κ : ℂ := ((∏ _y : Torus d n,
      ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
        ((N : ℝ) / 2) : ℝ) : ℂ)
    let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun v =>
      let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
      let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
      let z := chartShift β e w
      let M := β * (ν - (if regimeB then ν else 0)) / 2 *
        ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
      ((chartJac β w : ℝ) : ℂ) * ((χ φ : ℂ) * κ *
        Complex.exp (
          -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((e x) i : ℝ) : ℂ)) +
          (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
            (∑ x : Torus d (L * n), ∑ i : Fin N,
              g x i * (((w x + z x) i : ℝ) : ℂ)) -
          ((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ)))
    ∃ R : Config (Torus d (L * n)) N ≃ₗ[ℝ] Config (Torus d (L * n)) N,
      (∀ w, gaussForm e Hα (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config (Torus d (L * n)) N →ₗ[ℝ]
        Config (Torus d (L * n)) N) =
        Real.sqrt (LinearMap.det (gaussForm e Hα))⁻¹ ∧
      baseRho1 d N L n β a z₁ ν h ψ g =
        ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
          ((((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) *
            Fintype.card (Torus d (L * n)) / 2) *
            Real.sqrt (LinearMap.det (gaussForm e Hα))⁻¹ : ℝ) : ℂ) *
            ∫ ψ, F (tangentProj e he (R ψ)) ∂(stdGaussian (Torus d (L * n)) N))) +
            baseFirstRest d N L n β a z₁ ν regimeB δ₀ h g ψ) := by
  intro θ
  dsimp only
  obtain ⟨R, h1, h2, h3, h4⟩ := baseSectorChartIntegral_eq_normalized hβ a ν δ₀ ϱ aw ha regimeB hδ
    h hh H hΛ1 g (z₁ • ψ) φ₀ hp
  refine ⟨R, h1, h2, h3, ?_⟩
  rw [baseRho1_eq_allGood_add_rest ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 hΛ2 hβ ha0 g ψ, h4]

end Balaban.LargeField
