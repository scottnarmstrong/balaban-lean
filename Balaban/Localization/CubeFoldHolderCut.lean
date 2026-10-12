/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldHolderLong

/-!
# The mixed-wall Hölder estimate in the coordinate-cube form (VMOD-10 Theorem 1.1 (1.4))

`mixedKh = max {K_short, K_long}`; `cubeFold_holder_cut`: the short regime (`cubeFold_holder_short`) or the
long regime (`cubeFold_holder_long`), for the cut of the operator `H` along the coordinate cube
`cubeSet T S c`, with the physical Dirichlet wall retained.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.LatticeGreen Balaban.Reflection Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The constant `K_h = max {K_short, K_long}` of VMOD-10 (1.3).** -/
noncomputable def mixedKh (d L : ℕ) : ℝ := max (holderKshort d L) (holderKlong d L)

/-- **VMOD-10 Theorem 1.1 (1.4), in the coordinate-cube form.** -/
theorem cubeFold_holder_cut (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ}
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c)) {B : ℕ} (hB : 2 ≤ B)
    (hSB : S + B ≤ N₀ * L ^ k)
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (hy'Λ : y' ∈ cubeSet (N₀ * L ^ k) S c) {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1)
    (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c) (hx'Λ : x' ∈ cubeSet (N₀ * L ^ k) S c) {μ : Fin d}
    (hxe : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'e : x' + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hlay : G.layerIndex x ≤ G.layerIndex x' + 1) {z : Fin d → ℤ}
    (hxz : x' = x + intTorus z) (hz1 : 1 ≤ ‖z‖) (hzB : ‖z‖ < B)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (G.spacing x) ^ 2 *
        ‖(zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x' + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x') -
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x)‖ ≤
      (mixedKh d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        ((decay (agmonRate d / 2) (G.pathDist x y') + decay (agmonRate d / 2) (G.pathDist x' y')) *
          ((L : ℝ) ^ (2 * j') * Mf)) := by
  classical
  have hdx := decay_nonneg (agmonRate d / 2) (G.pathDist x y')
  have hdx' := decay_nonneg (agmonRate d / 2) (G.pathDist x' y')
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have hX0 : 0 ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have := spacing_pos G (x := x)
    have : (0 : ℝ) < ‖z‖ := by linarith
    positivity
  by_cases hshort : 2 ≤ G.layerIndex x ∧
      8 ≤ cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d ∧
      ‖z‖ ≤ (cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d) / 4
  · have h := cubeFold_holder_short hd hL hϱ hsep hν hν1 ha hα S c hSℓ hΛ hB hSB hj'1 hj'k hy' hy'Λ
      hsupp hMf0 hMf hx hxΛ hx'Λ hxe hx'e hxz hz1 hzB hshort hθ0 hθ1
    refine h.trans ?_
    have hK : holderKshort d L ≤ mixedKh d L := le_max_left _ _
    have hq : 0 ≤ (decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) := by
      positivity
    calc _ ≤ (mixedKh d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
          (decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by
            have : 0 ≤ mixedKh d L := (holderKshort_nonneg hd).trans hK
            positivity)
          have : 0 ≤ decay (agmonRate d / 2) (G.pathDist x' y') * ((L : ℝ) ^ (2 * j') * Mf) := by
            positivity
          nlinarith only [this]
  · have h := cubeFold_holder_long hd hL hϱ hsep hν hν1 ha hα S c hSℓ hΛ hj'1 hj'k hy' hy'Λ hsupp
      hMf0 hMf hx hx' hxΛ hx'Λ hxe hx'e hlay (r := ‖z‖) hz1 hshort hθ0 hθ1
    refine h.trans ?_
    have hK : holderKlong d L ≤ mixedKh d L := le_max_right _ _
    gcongr

end Balaban.Localization
