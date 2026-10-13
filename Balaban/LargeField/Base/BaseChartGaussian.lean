module

public import Balaban.LargeField.Base.BaseChartHessian

/-!
# The first-step Gaussian chart exponent

The physical Hessian of P4 (2.44) and the hard-spin normal coordinates give the
Gaussian quadratic and the exact mixed/normal remainder on the P5 all-good support.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix MeasureTheory SphereChart Classical

variable {d N L n : ℕ} [NeZero L] [NeZero n]

private theorem baseSector_fold_exponent (β a₀ μ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) (M : ℝ) (S₀ S₁ : ℂ) :
    -((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 *
      ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 : ℝ) : ℂ) +
      (-((β * energy d N (L * n) μ h φ : ℝ) : ℂ) - (M : ℂ) + S₀ + S₁) =
    -((β * (energy d N (L * n) μ h φ +
      (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
        ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2) : ℝ) : ℂ) -
      (M : ℂ) + S₀ + S₁ := by
  push_cast
  ring

/-- The rescaled physical chart exponent is its background constant plus the
Gaussian form and hard-spin remainder on nonzero P5 support. -/
theorem baseSector_gaussian_exponent_of_product_ne_zero
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (v : (x : Torus d (L * n)) → perp (baseSectorCenter ϱ aw regimeB ν h θ x)) :
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
      -((β * B ec : ℝ) : ℂ) -
        (((1 / 2) * cinner w (Hα w) : ℝ) : ℂ) + S₀ + S₁ -
        ((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ) := by
  dsimp only
  intro hp hv
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let α := bgMult G aw (if regimeB then ν else 0) D
  let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
  let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
  let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
  let z := chartShift β e w
  let Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N :=
    baseSectorHessian ϱ aw (if regimeB then ν else 0) (fun p => (α p).re)
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
  have hB := baseSector_physical_B_hessian_of_product_ne_zero
    ϱ aw a₀ ha regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  dsimp only at hB
  change B φ - B ec = (1 / 2) * cinner
    (fun x => (φ x : EuclideanSpace ℝ (Fin N)) - e x)
    (Hα (fun x => (φ x : EuclideanSpace ℝ (Fin N)) - e x)) at hB
  have hpt := chartMapPi_inv_sqrt_eq_chartPoint e he hβ v hv
  have hu : chartPoint β e w - e =
      (fun x => (φ x : EuclideanSpace ℝ (Fin N)) - e x) := by
    funext x
    exact congrFun hpt x |>.symm ▸ rfl
  have hSphere : sphereExponent β e Hα (chartPoint β e w) = -β * (B φ - B ec) := by
    unfold sphereExponent
    rw [hu, hB]
    ring
  have hsrc := source_chartPoint_complex (β := β) e w g
  rw [← hpt] at hsrc
  have hrem := baseChart_pointwise_quadratic_remainder hβ e Hα
    (baseSectorHessian_symmetric ϱ aw (if regimeB then ν else 0)
      (fun p => (α p).re)) w ν (if regimeB then ν else 0) h g
  dsimp only at hrem
  rw [hSphere] at hrem
  rw [← hpt] at hrem
  rw [hsrc] at hrem
  change -((β * B φ : ℝ) : ℂ) - (M : ℂ) + S₀ + S₁ =
    -((β * B ec : ℝ) : ℂ) -
      (((1 / 2) * cinner w (Hα w) : ℝ) : ℂ) + S₀ + S₁ -
      ((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ)
  push_cast at hrem ⊢
  linear_combination hrem

/-- The physical rescaled chart integrand equals its Hessian Gaussian form at every
tangent vector; outside the chart balls the Jacobian vanishes. -/
theorem baseSector_gaussian_integrand_eq
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (κ : ℂ)
    (v : (x : Torus d (L * n)) → perp (baseSectorCenter ϱ aw regimeB ν h θ x)) :
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
    ((chartJac β w : ℝ) : ℂ) *
      ((baseSectorCubeProduct regimeB ν δ₀ h θ φ : ℂ) * κ *
        Complex.exp (
          -((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 *
            ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 : ℝ) : ℂ) +
          (-((β * energy d N (L * n) (if regimeB then ν else 0) h φ : ℝ) : ℂ) -
            (M : ℂ) + S₀ + S₁))) =
    ((chartJac β w : ℝ) : ℂ) *
      ((baseSectorCubeProduct regimeB ν δ₀ h θ φ : ℂ) * κ *
        Complex.exp (
          -((β * B ec : ℝ) : ℂ) -
            (((1 / 2) * cinner w (Hα w) : ℝ) : ℂ) + S₀ + S₁ -
            ((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ))) := by
  dsimp only
  let e : Config (Torus d (L * n)) N := baseSectorCenter ϱ aw regimeB ν h θ
  let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
  change ((chartJac β w : ℝ) : ℂ) *
      (((baseSectorCubeProduct regimeB ν δ₀ h θ φ : ℝ) : ℂ) * κ *
        Complex.exp _) =
    ((chartJac β w : ℝ) : ℂ) *
      (((baseSectorCubeProduct regimeB ν δ₀ h θ φ : ℝ) : ℂ) * κ *
        Complex.exp _)
  by_cases hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ = 0
  · rw [hp]
    simp
  by_cases hv : ∀ x, ‖v x‖ < Real.sqrt β
  · have hg := baseSector_gaussian_exponent_of_product_ne_zero
      hβ a₀ ν δ₀ ϱ aw ha regimeB hδ h hh H hΛ1 g θ v hp hv
    dsimp only at hg
    let M := β * (ν - (if regimeB then ν else 0)) / 2 *
      ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
    let S₀ := ∑ x : Torus d (L * n), ∑ i : Fin N,
      g x i * (((e x) i : ℝ) : ℂ)
    let S₁ := (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
      (∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ))
    have hf := baseSector_fold_exponent β a₀ (if regimeB then ν else 0)
      h θ φ M S₀ S₁
    exact congrArg (fun E : ℂ => ((chartJac β w : ℝ) : ℂ) *
      (((baseSectorCubeProduct regimeB ν δ₀ h θ φ : ℝ) : ℂ) * κ * Complex.exp E))
        (hf.trans hg)
  · obtain ⟨x, hx⟩ := not_forall.mp hv
    have hj : chartJac β w = 0 := chartJac_eq_zero (w := w) hx
    rw [hj]
    simp

/-- The P5 all-good physical chart integral is a Gaussian integral with the
P4 (2.44) Hessian and the exact hard-spin normal-coordinate remainder. -/
theorem baseSectorChartIntegral_eq_gaussian
    {β : ℝ} (hβ : 0 < β) (a₀ ν δ₀ : ℝ)
    (ϱ : ℝ) (aw : ℕ → ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
    let D := baseSectorDatum ϱ θ h
    let α := bgMult G aw (if regimeB then ν else 0) D
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
                (((1 / 2) * cinner w (Hα w) : ℝ) : ℂ) +
                (∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((e x) i : ℝ) : ℂ)) +
                (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
                  (∑ x : Torus d (L * n), ∑ i : Fin N,
                    g x i * (((w x + z x) i : ℝ) : ℂ)) -
                ((cinner w (Hα z) + (1 / 2) * cinner z (Hα z) + M : ℝ) : ℂ)))
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  dsimp only
  rw [baseSectorChartIntegral_eq_rescaled_action hβ a₀ ν δ₀ regimeB
    ϱ aw h hh H g θ]
  apply congrArg (fun z : ℂ =>
    ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) • z)
  apply integral_congr_ae
  filter_upwards [] with v
  exact baseSector_gaussian_integrand_eq hβ a₀ ν δ₀ ϱ aw ha regimeB hδ
    h hh H hΛ1 g θ
    (((∏ _y : Torus d n,
      ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
        ((N : ℝ) / 2) : ℝ) : ℂ)) v

end Balaban.LargeField
