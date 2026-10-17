module

public import Balaban.LargeField.Base.BaseFirstChart

/-!
# Conditional first chart integral for a selected base record

The record cutoff is checked only on cubes outside its failed set. Raw collar spins are fixed
while the good-region spins are integrated.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale SphereChart MeasureTheory Metric

open Classical in
/-- The selected first integral in the local background chart. A nonzero selected cutoff
supplies a support point at which the local background is known to be a unit field. -/
theorem baseFirstRecord_chartIntegral_of_goodCubes
    {d N L M : ℕ} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]
    {ϱ Rk : ℝ} (hnn : ∀ i, i < 1 → nn i = L * nn (i + 1))
    (G : GeneratingSet d L (M * nn 1) 1 ϱ)
    (br : BaseRecord d L (nn 1) Rk)
    (hΩ : ∀ x, x ∈ G.Ω 1 ↔ cubeMap nn L M 1 1 x ∈ br.Omega)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (σ : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ)
    (hσ : ∀ x, ∑ i, σ x i ^ 2 = 1)
    (θ : Torus d (M * nn 1 * L ^ (1 - 1)) → Fin N → ℝ)
    (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1)
    (D : BgData G N)
    (hDΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = (θ (jBlock d L (M * nn 1) 1 1 x) i : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (σ x i : ℂ))
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ))
    (a : ℕ → ℝ) (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (χ : ((x : G.Ω 1) → sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℝ)
    (hχ : Measurable χ) (hχ1 : ∀ ψ, |χ ψ| ≤ 1)
    (hgood : ∀ ψ, χ ψ ≠ 0 → ∀ c : Torus d (nn 1), c ∉ br.P →
      chiPrimeZero nn L M 1 regimeB ν δ₀ h c
        ((fun z i => if hz : z ∈ G.Ω 1 then
            ((ψ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N)) i : ℝ) else σ z i), θ) = 1)
    (hex : ∃ ψ, χ ψ ≠ 0)
    (F : ((x : G.Ω 1) → sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℂ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ ψ, ‖F ψ‖ ≤ C) :
    let e : G.Ω 1 → EuclideanSpace ℝ (Fin N) := fun x =>
      WithLp.toLp 2 (fun i : Fin N =>
        (bgField G a (if regimeB then ν else 0) D (x, i)).re)
    ∃ he : ∀ x, ‖e x‖ = 1,
      (∫ ψ, (χ ψ : ℂ) * F ψ
        ∂(Measure.pi fun _ : G.Ω 1 =>
          (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)) =
        ∫ ξ : (x : G.Ω 1) → perp (e x),
          (∏ x, ((chartWeight (e x) (ξ x) : ℝ) : ℂ)) *
            ((χ (chartMapPi e he ξ) : ℂ) * F (chartMapPi e he ξ))
            ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  classical
  let e : G.Ω 1 → EuclideanSpace ℝ (Fin N) := fun x =>
    WithLp.toLp 2 (fun i : Fin N =>
      (bgField G a (if regimeB then ν else 0) D (x, i)).re)
  obtain ⟨ψ₀, hψ₀⟩ := hex
  let φ₀ : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ := fun z i =>
    if hz : z ∈ G.Ω 1 then (ψ₀ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N)) i else σ z i
  have hφ (ψ : (x : G.Ω 1) → sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
      ∀ z, ∑ i, (if hz : z ∈ G.Ω 1 then
        (ψ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N)) i else σ z i) ^ 2 = 1 := by
    intro z
    by_cases hz : z ∈ G.Ω 1
    · simp only [dite_eq_left hz]
      have hn : ‖(ψ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp (ψ ⟨z, hz⟩).property
      have hs := EuclideanSpace.norm_sq_eq (ψ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N))
      simp only [Real.norm_eq_abs, sq_abs] at hs
      calc
        _ = ‖(ψ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N))‖ ^ 2 := hs.symm
        _ = 1 := by rw [hn]; norm_num
    · simpa [hz] using hσ z
  have hφ₀ : ∀ z, ∑ i, φ₀ z i ^ 2 = 1 := hφ ψ₀
  have hDc₀ : ∀ z ∈ collar G, ∀ i, D.Ψ z i = (φ₀ z i : ℂ) := by
    intro z hz i
    have hnot : z ∉ G.Ω 1 := (mem_collar G).1 hz |>.1
    simpa [φ₀, hnot] using hDc z hz i
  have hgood₀ : ∀ c : Torus d (nn 1), c ∉ br.P →
      chiPrimeZero nn L M 1 regimeB ν δ₀ h c (φ₀, θ) = 1 := hgood ψ₀ hψ₀
  have S₀ := baseSpinSupport_of_baseRecord hnn G br hΩ regimeB ν δ₀ hδ₀
    φ₀ θ h hφ₀ hh D hDΨ hDc₀ hDh hgood₀
  have he : ∀ x, ‖e x‖ = 1 := by
    intro x
    have hs := (spins_near_background (G := G) H S₀ hΛ1 hΛ2 x).1
    have hn : ‖e x‖ ^ 2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      simpa only [Real.norm_eq_abs, sq_abs] using hs
    nlinarith [norm_nonneg (e x)]
  refine ⟨he, ?_⟩
  have hhem : ∀ ψ, χ ψ ≠ 0 → ∀ x : G.Ω 1,
      0 < inner ℝ (e x) (ψ x : EuclideanSpace ℝ (Fin N)) := by
    intro ψ hψ x
    let φ : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ := fun z i =>
      if hz : z ∈ G.Ω 1 then (ψ ⟨z, hz⟩ : EuclideanSpace ℝ (Fin N)) i else σ z i
    have hDcφ : ∀ z ∈ collar G, ∀ i, D.Ψ z i = (φ z i : ℂ) := by
      intro z hz i
      have hnot : z ∉ G.Ω 1 := (mem_collar G).1 hz |>.1
      simpa [φ, hnot] using hDc z hz i
    have hp := baseFirstRecord_inner_pos_of_goodCubes hnn G br hΩ regimeB ν δ₀ hδ₀
      φ θ h (hφ ψ) hh D hDΨ hDcφ hDh (hgood ψ hψ) a H hΛ1 hΛ2 x
    simpa [e, φ, x.property] using hp
  have hvanish : ∀ ψ, (∃ x, ¬ 0 < inner ℝ (e x)
      (ψ x : EuclideanSpace ℝ (Fin N))) → χ ψ = 0 := by
    intro ψ ⟨x, hx⟩
    by_contra hn
    exact hx (hhem ψ hn x)
  exact integral_sphere_pi_hemisphere_cutoff e he χ hχ hχ1 hvanish F hF C hC

end Balaban.LargeField
