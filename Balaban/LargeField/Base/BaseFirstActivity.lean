module

public import Balaban.LargeField.Base.BaseFirstCutPositive
public import Balaban.LargeField.Base.BaseChartGaussianNormalization

/-!
# Exact cut activity and the local Gaussian expectation

The physical action remainder remains in the activity. The Gaussian identity integrates a
specified positive local quadratic form; identifying that form with the physical first
component is a separate assertion.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix MeasureTheory SphereChart

/-- The missing crossing quadratic stays in the exact activity after a cut. -/
theorem baseFirstCut_exponent_identity (B q₁ qs R source : ℂ) :
    Complex.exp (-B - q₁ - R + source) =
      Complex.exp (-qs) * Complex.exp (-B - R - (q₁ - qs) + source) := by
  have h : -B - q₁ - R + source = -qs + (-B - R - (q₁ - qs) + source) := by ring
  rw [h, Complex.exp_add]

open Classical in
/-- The exact Gaussian expectation on a selected local integrated set, at the record
background centre. The positive-definite identification of its quadratic matrix is stated
explicitly as `hK`; the theorem does not assert that an arbitrary physical remainder has
this quadratic part. -/
theorem baseFirstCut_integral_of_posDef
    {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ ν δ₀ : ℝ}
    (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ)
    (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    (D : BgData G N) (Hbg : BgHyp d L 1 ϱ a ν)
    (S : BaseSpinSupport G ν δ₀ φ h D)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (I : Finset (G.Ω 1))
    (Hq : Config I N →ₗ[ℝ] Config I N)
    (hK : (LinearMap.toMatrix
      (Pi.basis (fun _ : I => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : I => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm
        (fun x : I => WithLp.toLp 2 (fun i : Fin N =>
          (bgField G a ν D (x.1, i)).re)) Hq)).PosDef)
    (f : ((x : I) → perp (WithLp.toLp 2 (fun i : Fin N =>
      (bgField G a ν D (x.1, i)).re) : EuclideanSpace ℝ (Fin N))) → ℂ)
    (hf : Measurable f) :
    let e : Config I N := fun x => WithLp.toLp 2 (fun i : Fin N =>
      (bgField G a ν D (x.1, i)).re)
    ∃ he : ∀ x, ‖e x‖ = 1, ∃ R : Config I N ≃ₗ[ℝ] Config I N,
      (∀ w, gaussForm e Hq (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config I N →ₗ[ℝ] Config I N) =
        Real.sqrt (LinearMap.det (gaussForm e Hq))⁻¹ ∧
      (∫ v : (x : I) → perp (e x),
        (((Real.exp (-(1 / 2) * cinner
          (fun x => (v x : EuclideanSpace ℝ (Fin N)))
          (Hq (fun x => (v x : EuclideanSpace ℝ (Fin N)))))) : ℝ) : ℂ) * f v
        ∂(Measure.pi fun x => (volume : Measure (perp (e x))))) =
        (((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card I / 2) *
          Real.sqrt (LinearMap.det (gaussForm e Hq))⁻¹ : ℝ) : ℂ) *
          ∫ ψ, f (tangentProj e he (R ψ)) ∂(stdGaussian I N) := by
  let e : Config I N := fun x => WithLp.toLp 2 (fun i : Fin N =>
    (bgField G a ν D (x.1, i)).re)
  have he : ∀ x, ‖e x‖ = 1 := by
    intro x
    have hs := (spins_near_background (G := G) Hbg S hΛ1 hΛ2 x.1).1
    have hn : ‖e x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa only [Real.norm_eq_abs, sq_abs] using hs
    nlinarith [norm_nonneg (e x)]
  exact ⟨he, integral_tangent_gaussian_of_posDef e he Hq hK f hf⟩

end Balaban.LargeField
