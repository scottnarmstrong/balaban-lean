/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiComposedData
public import Balaban.SmallField.XiFourData
public import Balaban.SmallField.IrrelTorusXidomData

/-!
# The data hypothesis on the polymers at the composed datum of a chart datum

`composeData_dataHypAnisoOn_of_pullback`: the composed datum `composeData 𝔹 𝔹' D` of a datum `D`
of `Ξ^c_K(𝔹'; 1, ε₀)`, with `𝔹 ≺ 𝔹'` under the hypotheses of `HypSle` (`L^j ≤ θ L^K`, the layers
of `𝔹` at most `j`, the scale gap `θ` and the collar condition), pulled back to `ℤ^d` through the
cells `f` of the layer `j` of `𝔹` (`f(x + e_μ) = f(x) + L^j e_μ`) on a region `R`, satisfies
`DataHypAnisoOn` on the polymers at `(σ, ε, K₂) = (C₀ θ, 10 C₁ ε₀, K_Σ θ^{2-θ'} ε₀)`:
the scaled coordinates `composeData_scaledPsiC_of_xiCData`, the second differences
`composeData_second_diff_of_xiCData`, assembled by `ScaledPsiC.dataHypAnisoOn_of_pullback`.  The
remaining premises are the geometry of the pullback (`R` in the layer `j`, its edges interface
pairs, the paths of the polymers), the chart membership of the pulled-back datum and of its constant
configuration (`hchart`), and the conditions on constants `C₀ θ ≤ 1`, `ν L^{2j} ≤ (C₀ θ)²`,
`C₁ ε₀ ≤ 1/200`, `(4d + 6) C₁ ε₀ ≤ 1`, `C₁ ε₀ ≤ c₁`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization

variable {d L : ℕ} [NeZero L]

/-- **`DataHypAnisoOn` at the composed datum of a chart datum, through the cells of a layer.**  For
a datum `D` of a member of `Ξ^c_K(𝔹'; 1, ε₀)` and `𝔹 ≺ 𝔹'` with the hypotheses of `HypSle`, a map
`f` of `ℤ^d` onto the cells of the layer `j` of `𝔹` (`f(x + e_μ) = f(x) + L^j e_μ`) and a region
`R` sent into that layer, whose edges are interface pairs, with the forward star of the origin in
`R` and paths of the polymers inside `R`: the pulled-back field `ψ(v) = Ψ(f v)` and external field
`b = ν L^{2j} h(f 0)` of the composed datum satisfy `DataHypAnisoOn` at
`(σ, ε, K₂) = (C₀ θ, 10 C₁ ε₀, K_Σ θ^{2-θ'} ε₀)` on every chart domain containing `(ψ, b)` and the
constant configuration `(ψ(0), b)`. -/
theorem composeData_dataHypAnisoOn_of_pullback (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 → ∀ {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ ϱ' : ℝ}
      {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
      (hq : Precedes G G') {a₁ ν ε₀ θ : ℝ} {j : ℕ},
      BgHyp d L K ϱ' (compWeight L a₁) ν → 0 < ν → 0 < a₁ → 0 < θ → θ ≤ 1 →
      (L : ℝ) ^ j ≤ θ * (L : ℝ) ^ K → (∀ x ∈ G.Ω 1, G.layerIndex x ≤ j) → ScaleGap G G' θ →
      (∀ z ∈ collar G, z ∈ G'.Ω 1 ∧ 1 ≤ θ * G'.spacing z) →
      (4 * d + 6) * (xiC1 d * ε₀) ≤ 1 → xiC1 d * ε₀ ≤ bgC1 d L N → xiC1 d * ε₀ ≤ 1 / 200 →
      scaledC0 d * θ ≤ 1 → ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * θ) ^ 2 →
      1 ≤ j → j ≤ K →
      ∀ D : BgData G' N, XiCData G' (compWeight L a₁) ν K 1 ε₀ D →
      ∀ (f : Site d → Torus d ((N₁ * L ^ m₁) * L ^ K)) {R : Set (Site d)},
      (∀ x μ, f (x + Pi.single μ 1) =
        f x + Pi.single μ ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) →
      (∀ x ∈ R, f x ∈ G.layer j) →
      (∀ x μ, x ∈ R → x + eU μ ∈ R → IsInterfacePair G (f (x + Pi.single μ 1)) (f x)) →
      StarIn R 0 →
      ∀ {polys : Set (Finset (Site d))} {ℓ : Finset (Site d) → ℝ},
      (∀ X ∈ polys, ∀ x ∈ X, ∃ (q : ℕ → Site d) (n : ℕ), q 0 = 0 ∧ q n = x ∧
        (n : ℝ) ≤ ℓ X ∧ IsLatPath q n ∧ ∀ i ≤ n, StarIn R (q i)) →
      ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun v => (composeData hq (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ (f v)),
        ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • (composeData hq (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).h (f 0)) ∈ Dom →
      ((fun _ => (composeData hq (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ (f 0)),
        ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • (composeData hq (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).h (f 0)) ∈ Dom →
      DataHypAnisoOn polys ℓ Dom (ν * ((L : ℝ) ^ j) ^ 2) (scaledC0 d * θ) (10 * (xiC1 d * ε₀))
        (xiSigma d L N B θh * θ ^ (2 - θh) * ε₀)
        (fun v => (composeData hq (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ (f v))
        (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • (composeData hq (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).h (f 0)) := by
  obtain ⟨B, hB0, hB⟩ := composeData_second_diff_of_xiCData (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N₁ m₁ K N _ ϱ ϱ' G G' hq a₁ ν ε₀ θ j H' hν0 ha₁ hθ0 hθ1 hjθ hnj hgap hcol
    hsmall hc1 hζ1 hτ1 hντ hj1 hjK D hD f R hf hlay hadj h0 polys ℓ hpath Dom hch hch0
  have hε₀ : 0 < ε₀ := by
    obtain ⟨_, _, _, _, hX, _⟩ := hD
    exact hX.2.1
  have hC1 := one_le_xiC1 d
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hC1a : 2 * (2 * (d : ℝ) + 1) ≤ xiC1 d := by unfold xiC1; nlinarith
  have hsm2 : (4 * d + 6) * ((2 * d + 1) * ε₀) ≤ 1 := by
    refine le_trans ?_ hsmall
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hε₀.le)
      (by positivity)
  obtain ⟨p, h₀, z, h'', hS, hΨ, hh, hsq⟩ :=
    composeData_scaledPsiC_of_xiCData H' hq (by omega) ha₁ hθ0 hθ1 hjθ hnj hgap hcol hsmall D hD
  have hsite : ∀ x ∈ R, f x ∈ G.Ω 1 := fun x hx => G.layer_subset hj1 hjK (hlay x hx)
  have hτ : 0 < scaledC0 d * θ := mul_pos (lt_of_lt_of_le one_pos (one_le_scaledC0 d)) hθ0
  have hζ : 0 < xiC1 d * ε₀ := by positivity
  have hK0 : 0 ≤ xiSigma d L N B θh * θ ^ (2 - θh) * ε₀ :=
    mul_nonneg (mul_nonneg (xiSigma_nonneg d L N hB0 hθh0) (Real.rpow_nonneg hθ0.le _)) hε₀.le
  refine ScaledPsiC.dataHypAnisoOn_of_pullback hS f
    (fun v => (composeData hq (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ (f v))
    (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • (composeData hq (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).h (f 0))
    (fun x i => hΨ (f x) i) ?_ hsite
    (G.layerIndex_eq hj1 hjK (hlay 0 h0.1)) hadj (fun x hx => hsq (f x) (hsite x hx))
    (mul_pos hν0 (by positivity)) hτ hτ1 hντ hζ hζ1 (by nlinarith [mul_pos (mul_pos hτ hτ) hζ])
    (by nlinarith [mul_pos hτ hζ]) (by nlinarith [mul_pos (mul_pos hτ hτ) hζ])
    (by nlinarith [mul_pos (mul_pos hτ hτ) (mul_pos hζ hζ)]) h0 hpath ⟨hch, hch0⟩ hK0 ?_
  · congr 1
    funext i
    exact hh (f 0) (hsite 0 h0.1) i
  · intro x μ μ' hx hxμ hxμ' hxμμ'
    have e1 : f (x + Pi.single μ 1) =
        f x + Pi.single μ ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := hf x μ
    have e2 : f (x + Pi.single μ' 1) =
        f x + Pi.single μ' ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := hf x μ'
    have e3 : f (x + Pi.single μ 1 + Pi.single μ' 1) =
        f x + Pi.single μ ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) +
          Pi.single μ' ((L ^ j : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
      rw [hf, e1]
    have l0 := hlay x hx
    have l1 := hlay _ hxμ
    have l2 := hlay _ hxμ'
    have l3 := hlay _ hxμμ'
    simp only [eU] at l1 l2 l3
    rw [e1] at l1
    rw [e2] at l2
    rw [e3] at l3
    show ‖(composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ
        (f (x + Pi.single μ 1 + Pi.single μ' 1)) -
      (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ
        (f (x + Pi.single μ 1)) -
      (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ
        (f (x + Pi.single μ' 1)) +
      (composeData hq (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ
        (f x)‖ ≤ _
    rw [e1, e2, e3]
    exact hB hθh0 hθh1 hq ha₁ H' hgap hθ0 hθ1 hsm2 hc1 D hD hj1 hjK μ μ' l0 l1 l2 l3

end Balaban.SmallField
