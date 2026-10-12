/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldHolderShort

/-!
# The long regime of the mixed-wall Hölder estimate (VMOD-10 (2.4))

Outside the short regime the two retained forward gradients are bounded by the pointwise estimate
`cut_cutU_decay` and `ℓ ≤ (8dL/c₀) ℓ^θ r^{1-θ}` absorbs the scale: `cubeFold_holder_long`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.LatticeGreen Balaban.Reflection Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The constant `K_long = (8dL/c₀)(L+1) K_p` of VMOD-10 (1.3). -/
noncomputable def holderKlong (d L : ℕ) : ℝ :=
  8 * d * L / cutC0 d L * ((L + 1) * cutKp d L)

theorem holderKlong_nonneg (hd : 3 ≤ d) : 0 ≤ holderKlong d L := by
  have := cutKp_nonneg_of_three_le (L := L) hd
  have := cutC0_pos (L := L) hd
  unfold holderKlong
  positivity

/-- A retained forward bond is controlled by the retained quantity `U_D`. -/
theorem spacing_mul_grad_le_cutU (G : GeneratingSet d L N₀ k ϱ)
    (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (w : Torus d (N₀ * L ^ k) → ℂ)
    {x : Torus d (N₀ * L ^ k)} {μ : Fin d} (hnc : (x, μ) ∉ cut) :
    G.spacing x * ‖w (x + Pi.single μ 1) - w x‖ ≤ cutU G cut w x := by
  unfold cutU
  have hsp := (spacing_pos G (x := x)).le
  have hnn : ∀ μ' : Fin d, 0 ≤ (if (x, μ') ∈ cut then (0 : ℝ) else
      ‖w (x + Pi.single μ' 1) - w x‖) := fun μ' => by split_ifs <;> positivity
  have h3 := Finset.single_le_sum (fun μ' _ => hnn μ') (Finset.mem_univ μ)
  simp only [hnc, ↓reduceIte] at h3
  have := mul_le_mul_of_nonneg_left h3 hsp
  have h4 := norm_nonneg (w x)
  linarith only [this, h4]

/-- **VMOD-10 (2.4) (long regime).** -/
theorem cubeFold_holder_long (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ}
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c))
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (hy'Λ : y' ∈ cubeSet (N₀ * L ^ k) S c) {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1)
    (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c) (hx'Λ : x' ∈ cubeSet (N₀ * L ^ k) S c) {μ : Fin d}
    (hxe : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'e : x' + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hlay : G.layerIndex x ≤ G.layerIndex x' + 1) {r : ℝ} (hr : 1 ≤ r)
    (hnot : ¬ (2 ≤ G.layerIndex x ∧
      8 ≤ cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d ∧
      r ≤ (cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d) / 4))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (G.spacing x) ^ 2 *
        ‖(zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x' + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x') -
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x)‖ ≤
      (holderKlong d L / θ) * ((G.spacing x) ^ θ * r ^ (1 - θ)) *
        ((decay (agmonRate d / 2) (G.pathDist x y') + decay (agmonRate d / 2) (G.pathDist x' y')) *
          ((L : ℝ) ^ (2 * j') * Mf)) := by
  classical
  have hd0 : 0 < d := by omega
  set cut := cubeCut G (cubeSet (N₀ * L ^ k) S c) with hcutdef
  set ut := zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) with hutdef
  set F : ℝ := (L : ℝ) ^ (2 * j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  set Kp := cutKp d L with hKp
  have hKp0 : 0 ≤ Kp := cutKp_nonneg_of_three_le hd
  have hU := fun {w} (hw : w ∈ G.Ω 1) => cut_cutU_decay hd hL hϱ hsep hν hν1 ha hα S c hSℓ hΛ hj'1
    hj'k hy' hy'Λ hsupp hMf0 hMf hw
  have hnc : ∀ {p : Torus d (N₀ * L ^ k)}, p ∈ cubeSet (N₀ * L ^ k) S c →
      p + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c → (p, μ) ∉ cut := by
    intro p hp hpe
    rw [hcutdef, mem_cubeCut]
    rintro (⟨-, -, h3⟩ | ⟨h1, -, -⟩)
    · exact h3 hpe
    · exact h1 hp
  have hgx := spacing_mul_grad_le_cutU G cut ut (hnc hxΛ hxe)
  have hgx' := spacing_mul_grad_le_cutU G cut ut (hnc hx'Λ hx'e)
  have hUx := hU hx
  have hUx' := hU hx'
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hj1', hjk', hxl'⟩ := G.layerIndex_spec hx'
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hsx : G.spacing x = (L : ℝ) ^ G.layerIndex x := G.spacing_eq hj1 hjk hxl
  have hsx' : G.spacing x' = (L : ℝ) ^ G.layerIndex x' := G.spacing_eq hj1' hjk' hxl'
  have hspl : G.spacing x ≤ L * G.spacing x' := by
    rw [hsx, hsx', ← pow_succ']
    exact pow_le_pow_right₀ hL1 hlay
  have hsp0 := spacing_pos G (x := x)
  have hsp0' := spacing_pos G (x := x')
  set ℓ := G.spacing x with hℓ
  set ℓ' := G.spacing x' with hℓ'
  set g := ut (x + Pi.single μ 1) - ut x with hg
  set g' := ut (x' + Pi.single μ 1) - ut x' with hg'
  set Ex := decay (agmonRate d / 2) (G.pathDist x y') with hEx
  set Ex' := decay (agmonRate d / 2) (G.pathDist x' y') with hEx'
  have hEx0 : 0 ≤ Ex := decay_nonneg _ _
  have hEx0' : 0 ≤ Ex' := decay_nonneg _ _
  have hA : ℓ * ‖g‖ ≤ Kp * (Ex * F) := by
    refine hgx.trans (hUx.trans (le_of_eq ?_)); ring
  have hB : ℓ' * ‖g'‖ ≤ Kp * (Ex' * F) := by
    refine hgx'.trans (hUx'.trans (le_of_eq ?_)); ring
  have hn := norm_nonneg g
  have hn' := norm_nonneg g'
  have hsub : ‖g' - g‖ ≤ ‖g'‖ + ‖g‖ := norm_sub_le _ _
  have h1 : ℓ ^ 2 * ‖g' - g‖ ≤ ℓ * (Kp * (Ex * F) + L * (Kp * (Ex' * F))) := by
    have e1 : ℓ ^ 2 * ‖g‖ ≤ ℓ * (Kp * (Ex * F)) := by
      calc ℓ ^ 2 * ‖g‖ = ℓ * (ℓ * ‖g‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hA hsp0.le
    have e2 : ℓ ^ 2 * ‖g'‖ ≤ ℓ * (L * (Kp * (Ex' * F))) := by
      calc ℓ ^ 2 * ‖g'‖ = ℓ * (ℓ * ‖g'‖) := by ring
        _ ≤ ℓ * ((L * ℓ') * ‖g'‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hspl hn') hsp0.le
        _ = ℓ * (L * (ℓ' * ‖g'‖)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hL0.le) hsp0.le
    calc ℓ ^ 2 * ‖g' - g‖ ≤ ℓ ^ 2 * (‖g'‖ + ‖g‖) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = ℓ ^ 2 * ‖g'‖ + ℓ ^ 2 * ‖g‖ := by ring
      _ ≤ _ := by linarith only [e1, e2]
  have h2 : Kp * (Ex * F) + L * (Kp * (Ex' * F)) ≤ ((L + 1) * Kp) * ((Ex + Ex') * F) := by
    have : 0 ≤ Kp * (Ex * F) := by positivity
    have : 0 ≤ Kp * (Ex' * F) := by positivity
    have e : ((L + 1) * Kp) * ((Ex + Ex') * F) = (L + 1) * (Kp * (Ex * F)) +
        (L + 1) * (Kp * (Ex' * F)) := by ring
    rw [e]
    nlinarith only [‹0 ≤ Kp * (Ex * F)›, ‹0 ≤ Kp * (Ex' * F)›, hL1]
  have hc0 := cutC0_pos (L := L) hd
  have hc04 := cutC0_le (d := d) (L := L)
  have hscale := cut_holder_scale (L := L) hc0 hc04 hj1 hr hnot (by omega) hθ0 hθ1
  rw [← hsx] at hscale
  have hX0 : 0 ≤ ℓ ^ θ * r ^ (1 - θ) := by
    have : (0 : ℝ) < r := by linarith
    positivity
  have h3 : ℓ ≤ 8 * d * L / cutC0 d L * (ℓ ^ θ * r ^ (1 - θ)) := hscale
  have hY : 0 ≤ ((L + 1) * Kp) * ((Ex + Ex') * F) := by positivity
  have h4 : ℓ ^ 2 * ‖g' - g‖ ≤ holderKlong d L * ((ℓ ^ θ * r ^ (1 - θ)) * ((Ex + Ex') * F)) := by
    calc ℓ ^ 2 * ‖g' - g‖ ≤ ℓ * (((L + 1) * Kp) * ((Ex + Ex') * F)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hsp0.le)
      _ ≤ (8 * d * L / cutC0 d L * (ℓ ^ θ * r ^ (1 - θ))) * (((L + 1) * Kp) * ((Ex + Ex') * F)) :=
          mul_le_mul_of_nonneg_right h3 hY
      _ = _ := by unfold holderKlong; ring
  have hKl := holderKlong_nonneg (L := L) hd
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hW : 0 ≤ (ℓ ^ θ * r ^ (1 - θ)) * ((Ex + Ex') * F) := by positivity
  refine h4.trans ?_
  calc holderKlong d L * ((ℓ ^ θ * r ^ (1 - θ)) * ((Ex + Ex') * F))
      = holderKlong d L * 1 * ((ℓ ^ θ * r ^ (1 - θ)) * ((Ex + Ex') * F)) := by ring
    _ ≤ holderKlong d L * (1 / θ) * ((ℓ ^ θ * r ^ (1 - θ)) * ((Ex + Ex') * F)) := by
        gcongr
    _ = _ := by ring

end Balaban.Localization
