/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSwitchLoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The switch of the background between two generating sets in a restricted action

P7 p. 501 (2.14)–(2.16): for a region `X` of a generating set `Gl` and a second generating set `Gw`
on an identified torus whose layers, `h̃` and data (within `δ_d`) agree with those of `Gl` on the
ball `B(X, R)`, the restricted action of `X` at the background `φ_l` of `Gl` and at the background
`φ_w` of `Gw` read through the identification (`transportField`) differ by at most
`A |X|_{mix} (V (…) + V²/2 (…))`, where `V ≥ K (δ_d + (δ_l + δ_w) e^{-γ_w D₀})`,
`D₀ = (R - (ϱ_B + 3d) L^{k_l} - 2) / L^{k_l}` (`actionRegionC_switch_of_genSet`).

Proof: `genSet_stability_grad` gives `|φ_w ∘ e⁻¹ - φ_l| ≤ V` and `ℓ |∂(φ_w ∘ e⁻¹ - φ_l)| ≤ V` on the
sites of `X` (a union of blocks), and `Region.actionDiff_local_le` turns them into the action
bound with the read budgets of `φ_l` and the per-cube coefficient budgets.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Localization Finset

variable {d L N : ℕ} [NeZero L]

/-- **The background switch in a restricted action** (P7 (2.14)).  There are `K, δ_s > 0`
depending only on `(d, L, N)` such that, under the hypotheses of `genSet_stability_grad` on the
ball `B(X, R)` (`R ≥ (ϱ_B + 3d) L^{k_l} + 2`) and with the read bounds `S_b, S_g, S_m` of
`φ_l = bgFieldC Gl` on `X` and the per-cube budgets `C_b, C_g, C_m`, every
`V ≥ K (δ_d + (δ_l + δ_w) e^{-γ_w D₀})` bounds the switch
`β |A_X(φ_l) - A_X(φ_w ∘ e⁻¹)| ≤ A |X|_{mix} (V (…) + V²/2 (…))`. -/
theorem actionRegionC_switch_of_genSet (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K δs : ℝ, 0 < K ∧ 0 < δs ∧
      ∀ {N₀l kl N₀w kw : ℕ} [NeZero N₀l] [NeZero N₀w] {ϱl ϱw ϱB : ℝ}
        (Gl : GeneratingSet d L N₀l kl ϱl) (Gw : GeneratingSet d L N₀w kw ϱw)
        (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl)) {a : ℕ → ℝ} {ν : ℝ},
        BgHyp d L kl ϱl a ν → BgHyp d L kw ϱw a ν → bgR0 d L ≤ ϱB →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱB - 1) → ϱB ≤ ϱl → kl ≤ kw →
        (∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1) →
        (∀ n, n ≤ kl → ∀ x y, jBlock d L N₀l kl n x = jBlock d L N₀l kl n y ↔
          jBlock d L N₀w kw n (e.symm x) = jBlock d L N₀w kw n (e.symm y)) →
        ∀ (X : Region Gl) (Dc : StepDecomp X) (R : ℝ), (ϱB + 3 * d) * (L : ℝ) ^ kl + 2 ≤ R →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ kl) z x ≤ R) →
          ∀ n, 1 ≤ n → n ≤ kl + 1 → (x ∈ Gl.Ω n ↔ e.symm x ∈ Gw.Ω n)) →
        ∀ {Dl : BgData Gl N} {Dw : BgData Gw N} {δl δw δd : ℝ},
        0 < δl → δl ≤ bgC1 d L N → InDomainR Gl ν δl Dl →
        0 < δw → δw ≤ bgC1 d L N → InDomainR Gw ν δw Dw → 0 ≤ δd →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ kl) z x ≤ R) →
          vn (fun i => Dl.Ψ x i - Dw.Ψ (e.symm x) i) ≤ δd) →
        (∀ x, (∃ z ∈ X.sites, Green.torusDist d (N₀l * L ^ kl) z x ≤ R) →
          Dl.h x = Dw.h (e.symm x)) →
        bgK1 d L N * (δl + δw) + δd ≤ δs →
        ∀ {β A V Cb Cg Cm Sb Sg Sm : ℝ}, 0 ≤ β → 0 ≤ A → 0 ≤ Cb → 0 ≤ Cg → 0 ≤ Cm →
        0 ≤ Sb → 0 ≤ Sg → 0 ≤ Sm →
        (∀ c, β * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff Gl a x‖ ≤ Cb * (A * Dc.wt c)) →
        (∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((Gl.spacing x) ^ 2)⁻¹ ≤ Cg * (A * Dc.wt c)) →
        (∀ c, β * ∑ _x ∈ (Dc.cube c).sites, |ν| ≤ Cm * (A * Dc.wt c)) →
        (∀ x ∈ X.sites, ∑ j,
          ‖Dl.Ψ x j - blockAvg Gl (bgFieldC Gl a ν (bgC0 d L N) Dl) x j‖ ^ 2 ≤ Sb) →
        (∀ x ∈ X.sites, ∀ μ : Fin d, Gl.spacing x ^ 2 * ∑ j,
          ‖barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) (x + Pi.single μ 1) j -
            barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) x j‖ ^ 2 ≤ Sg) →
        (∀ x ∈ X.sites, ∀ μ : Fin d, Gl.spacing x ^ 2 * ∑ j,
          ‖barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) (x - Pi.single μ 1) j -
            barField Gl Dl.Ψ (bgFieldC Gl a ν (bgC0 d L N) Dl) x j‖ ^ 2 ≤ Sg) →
        (∀ x ∈ X.sites, ∑ j,
          ‖svec Gl (bgFieldC Gl a ν (bgC0 d L N) Dl) x j - Dl.h x j‖ ^ 2 ≤ Sm) →
        K * (δd + (δl + δw) *
          Real.exp (-(gammaW d * ((R - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) / (L : ℝ) ^ kl)))) ≤ V →
        ‖(β : ℂ) * actionRegionC X a ν Dl (bgFieldC Gl a ν (bgC0 d L N) Dl) -
            (β : ℂ) * actionRegionC X a ν Dl
              (transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw))‖ ≤
          A * Dc.total * (V * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
            Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) := by
  obtain ⟨K, δs, hK, hδs, hstab⟩ := genSet_stability_grad (L := L) N hd hL
  refine ⟨K, δs, hK, hδs, ?_⟩
  intro N₀l kl N₀w kw _ _ ϱl ϱw ϱB Gl Gw e a ν H Hw hϱB0 hsepB hϱB hk he hblk X Dc R hR hag Dl Dw
    δl δw δd hδl0 hδl hDl hδw0 hδw hDw hδd hΨ hh hsm β A V Cb Cg Cm Sb Sg Sm hβ hA hCb hCg hCm
    hSb hSg hSm hcb hcg hcm hrB hrGf hrGb hrM hV
  have hst := fun (y : Gl.Ω 1) (hy : (y : Torus d (N₀l * L ^ kl)) ∈ X.sites) =>
    hstab Gl Gw e H Hw hϱB0 hsepB hϱB hk he hblk X.sites R hR hag hδl0 hδl hDl hδw0 hδw hDw hδd
      hΨ hh hsm y hy
  have hE0 : 0 ≤ Real.exp (-(gammaW d * ((R - (ϱB + 3 * d) * (L : ℝ) ^ kl - 2) /
      (L : ℝ) ^ kl))) := (Real.exp_pos _).le
  have hV0 : 0 ≤ V := le_trans (by positivity) hV
  set φl := bgFieldC Gl a ν (bgC0 d L N) Dl with hφl
  set φ' := transportField (Gl := Gl) e Dw.Ψ (bgFieldC Gw a ν (bgC0 d L N) Dw) with hφ'
  have ew : (fun p => φ' p - φl p) = φ' - φl := rfl
  refine Region.actionDiff_local_le X Dc a ν Dl φl φ' hβ hA hV0 hCb hCg hCm hSb hSg hSm hcb hcg
    hcm (fun x hx y hy j => ?_) (fun x hx μ j => ?_) (fun x hx μ j => ?_) hrB hrGf hrGb hrM
  · have hyX := X.blockClosed x hx y hy
    have hy1 := X.sub_Ω hyX
    rw [svec_of_mem Gl _ ⟨y, hy1⟩ j]
    exact ((hst ⟨y, hy1⟩ hyX).1 j).trans hV
  · have := (hst ⟨x, X.sub_Ω hx⟩ hx).2.1 μ j
    rw [ew] at this
    exact this.trans hV
  · have := (hst ⟨x, X.sub_Ω hx⟩ hx).2.2 μ j
    rw [ew] at this
    exact this.trans hV

end Balaban.LargeField.ActionConv
