/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartComponent

/-!
# Gaussian normalization of the full physical first chart

The quadratic factor in P4 (2.47)–(2.50) is integrated with the real
inverse square root; the hard-spin cutoff, Jacobian, source and nonlinear
normal-coordinate terms remain in the activity.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

variable {d N L n : ℕ} [NeZero L] [NeZero n]

attribute [local fun_prop] measurable_chartMapPi

/-- The radial chart Jacobian is measurable on a finite configuration space. -/
@[fun_prop] theorem measurable_chartJac {ι : Type*} [Fintype ι] (β : ℝ) :
    Measurable (chartJac (ι := ι) (N := N) β) := by
  classical
  unfold chartJac
  refine Finset.measurable_prod _ fun x _ => ?_
  refine Measurable.ite (measurableSet_lt ?_ measurable_const) ?_ measurable_const
  · exact (measurable_pi_apply x).norm
  · fun_prop

omit [NeZero L] [NeZero n] in
/-- The nonlinear normal shift is measurable. -/
@[fun_prop] theorem measurable_chartShift {ι : Type*} [Fintype ι]
    (β : ℝ) (e : Config ι N) : Measurable (chartShift β e) := by
  unfold chartShift
  refine measurable_pi_iff.mpr fun x => ?_
  fun_prop

/-- The full uncut P5 first-sector chart integral has the canonical real
Gaussian determinant normalization on nonzero all-good support. -/
theorem baseSectorChartIntegral_eq_normalized
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ₀ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ₀ ≠ 0) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let κ : ℂ := ((∏ _y : Torus d n,
      ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
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
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
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
      baseChartIntegral d N L n β a₀ ν h g θ χ e he =
        ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) *
            Fintype.card (Torus d (L * n)) / 2) *
            Real.sqrt (LinearMap.det (gaussForm e Hα))⁻¹ : ℝ) : ℂ) *
            ∫ ψ, F (tangentProj e he (R ψ)) ∂(stdGaussian (Torus d (L * n)) N)) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
  let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
  let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
  let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
  let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
    baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun z => (α z).re)
  let χ : CfgT d N L n → ℝ := baseSectorCubeProduct regimeB ν δ₀ h θ
  let κ : ℂ := ((∏ _y : Torus d n,
    ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
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
          (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
            ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
        (∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((e x) i : ℝ) : ℂ)) +
        (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((w x + z x) i : ℝ) : ℂ)) -
        ((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ)))
  have hK := baseSector_gaussForm_posDef_of_product_ne_zero
    ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ₀ hp
  have hF : Measurable F := by
    let V := (x : Torus d (L * n)) → perp (e x)
    let W : V → Config (Torus d (L * n)) N := fun v x => (v x : EuclideanSpace ℝ (Fin N))
    let Φ : V → CfgT d N L n := fun v => chartMapPi e he ((Real.sqrt β)⁻¹ • v)
    let Z : V → Config (Torus d (L * n)) N := fun v => chartShift β e (W v)
    let Mass : V → ℝ := fun v => β * (ν - (if regimeB then ν else 0)) / 2 *
      ∑ x : Torus d (L * n), ‖(Φ v x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
    let Source : V → ℂ := fun v => ∑ x : Torus d (L * n), ∑ i : Fin N,
      g x i * (((W v x + Z v x) i : ℝ) : ℂ)
    let Cross : V → ℝ := fun v => cinner (W v) (Hα (Z v))
    let Zquad : V → ℝ := fun v => cinner (Z v) (Hα (Z v))
    have hχ : Measurable χ := measurable_baseSectorCubeProduct regimeB ν δ₀ h θ
    have hHα : Measurable Hα :=
      (LinearMap.continuous_of_finiteDimensional Hα).measurable
    have hW : Measurable W := by
      refine measurable_pi_iff.mpr fun x => ?_
      fun_prop
    have hΦ : Measurable Φ := by fun_prop
    have hZ : Measurable Z := (measurable_chartShift β e).comp hW
    have hMass : Measurable Mass := by
      dsimp only [Mass]
      fun_prop
    have hSource : Measurable Source := by
      dsimp only [Source]
      fun_prop
    have hCross : Measurable Cross := by
      dsimp only [Cross, cinner]
      fun_prop
    have hZquad : Measurable Zquad := by
      dsimp only [Zquad, cinner]
      fun_prop
    change Measurable (fun v : V =>
      ((chartJac β (W v) : ℝ) : ℂ) *
        ((χ (Φ v) : ℂ) * κ * Complex.exp (
          -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((e x) i : ℝ) : ℂ)) +
          (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Source v -
          ((Cross v + (1 / 2) * Zquad v + Mass v : ℝ) : ℂ))))
    refine (Complex.measurable_ofReal.comp ((measurable_chartJac β).comp hW)).mul ?_
    refine ((Complex.measurable_ofReal.comp (hχ.comp hΦ)).mul measurable_const).mul ?_
    apply Complex.measurable_exp.comp
    fun_prop
  obtain ⟨R, hRR, hRs, hdet, hnorm⟩ :=
    integral_tangent_gaussian_of_posDef e he Hα hK F hF
  refine ⟨R, hRR, hRs, hdet, ?_⟩
  rw [baseSectorChartIntegral_eq_gaussian hβ a₀ ν δ₀ ϱ aw ha regimeB hδ
    h hh H hΛ1 g θ]
  apply congrArg (fun z : ℂ =>
    ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) • z)
  rw [← hnorm]
  apply integral_congr_ae
  filter_upwards [] with v
  dsimp only [F]
  rw [Complex.ofReal_exp]
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
  let z := chartShift β e w
  let q : ℝ := (1 / 2) * cinner w (Hα w)
  let b : ℂ := -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
    (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
      ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ)
  let s₀ : ℂ := ∑ x : Torus d (L * n), ∑ i : Fin N,
    g x i * (((e x) i : ℝ) : ℂ)
  let s₁ : ℂ := (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
    (∑ x : Torus d (L * n), ∑ i : Fin N,
      g x i * (((w x + z x) i : ℝ) : ℂ))
  let m : ℝ := β * (ν - (if regimeB then ν else 0)) / 2 *
    ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
  let r : ℝ := cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + m
  change ((chartJac β w : ℝ) : ℂ) *
      ((χ φ : ℂ) * κ * Complex.exp (b - (q : ℂ) + s₀ + s₁ - (r : ℂ))) =
    Complex.exp (((-(1 / 2) * cinner w (Hα w) : ℝ)) : ℂ) *
      (((chartJac β w : ℝ) : ℂ) *
        ((χ φ : ℂ) * κ * Complex.exp (b + s₀ + s₁ - (r : ℂ))))
  have hexp : Complex.exp (b - (q : ℂ) + s₀ + s₁ - (r : ℂ)) =
      Complex.exp (((-(1 / 2) * cinner w (Hα w) : ℝ)) : ℂ) *
        Complex.exp (b + s₀ + s₁ - (r : ℂ)) := by
    rw [← Complex.exp_add]
    dsimp [q]
    push_cast
    ring_nf
  rw [hexp]
  ring

end Balaban.LargeField
