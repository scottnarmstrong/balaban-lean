/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartComponentNormalization

/-!
# The cut family in the first physical sphere chart

The cut Hamiltonian is the bond interpolation of BASE-KERNEL-3 (1.2).
The difference between its quadratic form and the physical quadratic form
is retained in the exact chart activity, as in P4 (2.51)–(2.54).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix MeasureTheory SphereChart Classical
open Balaban.LargeField.Base

variable {d N L n : ℕ} [NeZero L] [NeZero n]

/-- The physical first-chart exponent written with the cut bond quadratic.
The extra term in the remainder is exactly the missing crossing-bond form;
no condition on the complex cut parameters is needed for this algebraic identity. -/
theorem baseSector_cut_exponent_of_product_ne_zero
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (v : (x : Torus d (L * n)) → perp (baseSectorCenter ϱ aw regimeB ν h θ x))
    (s : FineBond d L (1 * n) → ℂ) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
    let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
    let z := chartShift β e w
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let W : G.Ω 1 × Fin N → ℂ := fun p =>
      (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
    let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
      (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
        (if regimeB then ν else 0) α t) *ᵥ W)
    let B : CfgT d N L n → ℝ := fun ψ =>
      energy d N (L * n) (if regimeB then ν else 0) h ψ +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ψ y‖ ^ 2
    let M := β * (ν - (if regimeB then ν else 0)) / 2 *
      ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
    let S₀ := ∑ x : Torus d (L * n), ∑ i : Fin N,
      g x i * (((e x) i : ℝ) : ℂ)
    let S₁ := (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
      (∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((w x + z x) i : ℝ) : ℂ))
    baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0 →
    (∀ x, ‖v x‖ < Real.sqrt β) →
    -((β * B φ : ℝ) : ℂ) - (M : ℂ) + S₀ + S₁ =
      -((β * B ec : ℝ) : ℂ) - q s + S₀ + S₁ -
        (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
          (q (fun _ => 1) - q s)) := by
  dsimp only
  intro hp hv
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
  let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
  let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
  have hgauss := baseSector_gaussian_exponent_of_product_ne_zero
    hβ a₀ ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1 g θ v hp hv
  dsimp only at hgauss
  have hcut := baseSectorHessian_cut_core_one_of_product_ne_zero
    ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp w w
  dsimp only at hcut
  rw [hcut]
  push_cast at hgauss ⊢
  linear_combination hgauss

/-- The first physical chart is an exact integral against the cut quadratic
reference. Its activity contains the missing bond form, the hard-spin
normal-coordinate remainder, the P5 cutoff, Jacobian, and source. -/
theorem baseSectorChartIntegral_eq_cut_gaussian
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (s : FineBond d L (1 * n) → ℂ) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let α := bgMult G aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
    let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
      baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    baseChartIntegral d N L n β a₀ ν h g θ χ e he =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
        ∫ v : (x : Torus d (L * n)) → perp (e x),
          let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
          let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
          let z := chartShift β e w
          let W : G.Ω 1 × Fin N → ℂ := fun p =>
            (((w (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1)))) p.2 : ℝ) : ℂ)
          let q : (FineBond d L (1 * n) → ℂ) → ℂ := fun t =>
            (1 / 2) * pair G W (liftOp N (baseHamiltonian G aw
              (if regimeB then ν else 0) α t) *ᵥ W)
          let M := β * (ν - (if regimeB then ν else 0)) / 2 *
            ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
          ((chartJac β w : ℝ) : ℂ) *
            ((χ φ : ℂ) *
              ((∏ _y : Torus d n,
                ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
                  ((N : ℝ) / 2) : ℝ) : ℂ) *
              Complex.exp (
                -((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
                  (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
                    ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) -
                q s +
                (∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((e x) i : ℝ) : ℂ)) +
                (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
                  (∑ x : Torus d (L * n), ∑ i : Fin N,
                    g x i * (((w x + z x) i : ℝ) : ℂ)) -
                (((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) +
                  (q (fun _ => 1) - q s))))
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  dsimp only
  rw [baseSectorChartIntegral_eq_gaussian hβ a₀ ν δ₀ ϱ aw ha regimeB hδ
    h hh H hΛ1 g θ]
  apply congrArg (fun x : ℂ =>
    ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) • x)
  apply integral_congr_ae
  filter_upwards [] with v
  dsimp only
  by_cases hp : baseSectorCubeProduct regimeB ν δ₀ h θ
      (chartMapPi (baseSectorCenter ϱ aw regimeB ν h θ)
        (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ)
        ((Real.sqrt β)⁻¹ • v)) = 0
  · simp [hp]
  · let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
    let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
    have hcut := baseSectorHessian_cut_core_one_of_product_ne_zero
      ϱ aw regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp w w
    dsimp only at hcut
    rw [hcut]
    congr 1
    congr 1
    congr 1
    push_cast
    ring

end Balaban.LargeField
