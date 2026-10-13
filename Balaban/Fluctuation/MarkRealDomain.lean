/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedSharpCount
public import Balaban.Fluctuation.Prop33CloseReal
import Mathlib.Tactic.Linarith

/-!
# The domain premise of the marked derivative identity from the marked disc

The identity `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` assumes that for real `s ∈ [0,1]`
and `|t| < t₁` the datum of the complex point `ζ` near `s` along the marked tangent lies in the
union domain.  This follows from the exact-field premise `hreal` (Lemma 2.3 (d), landed as
`hreal_level`) and the marked disc `hdisc`: for `|ζ| < R₁ + r` the field `ζ · lift v_t` is a
layer-constant element of the fluctuation ball, `hreal` gives a datum with the same `h` and
that tangent, and the line from the composed datum through it, at parameter `1 < R`, is the datum
of `ψ^{(k)} + ζ v_t` (`dataUC_psiAtV_eq_lineAt`).

* `markReal_hdomT_of_hreal`: `hdomT` from `hreal` and `hdisc`.
* `markReal_hdomT_of_disc`: `hdomT` from the premises of `hreal_level` and `hdisc`.
* `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_disc`: the marked derivative identity without
  `hdomT`.

The uniform slice producer and `E1MarksC` are not here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.SmallField Set Filter Topology

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`hdomT` from `hreal` and the marked disc.** -/
theorem markReal_hdomT_of_hreal {R : ℝ} (hR : 2 ≤ R)
    (hreal : ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁, IsLayerConstant (stepG d L N₁ m₁ k ϱ) ψ' →
      ∃ D : BgData (stepG d L N₁ m₁ k ϱ) N, (∀ x i, D.h x i = S.D'.h x i) ∧
      compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        ((composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').lineAt
          (tangentData D (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D')) t))
    {R₁ r t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (x : S.E) (u : ℂ)
    (hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    ∀ t : ℂ, ‖t‖ < t₁ → ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in nhds (s : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ (S.markedTangentC z u t x))) := by
  intro t ht s hs
  have hsn : ‖(s : ℂ)‖ < R₁ + r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
  filter_upwards [Metric.ball_mem_nhds (s : ℂ) (sub_pos.2 hsn)] with ζ hζ
  have hζn : ‖ζ‖ < R₁ + r := by
    have h1 : ‖ζ - (s : ℂ)‖ < (R₁ + r) - ‖(s : ℂ)‖ := by
      simpa [dist_eq_norm] using hζ
    calc ‖ζ‖ = ‖(ζ - (s : ℂ)) + (s : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖ζ - (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ < R₁ + r := by linarith
  set v := S.markedTangentC z u t x with hv
  have hmem : ζ • liftC S.hG' v ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁ := by
    rw [hv, S.liftC_markedTangentC]; exact hdisc t ht ζ hζn
  obtain ⟨D, hDh, hct, hline⟩ :=
    hreal _ hmem (isLayerConstant_smul (isLayerConstant_liftC S.hG S.hG' v) _)
  have h1 := hline 1 (by rw [norm_one]; linarith)
  have hbase : S.dataUC S.psi0C = composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' := S.dataUC_psi0C
  have hDeq : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').lineAt
      (tangentData D (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D')) 1 =
      S.dataUC (S.psiAtV ζ v) := by
    have hBh : (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').h = D.h := by
      funext y i
      rw [hDh]
      simp [composeData, (S.hG y).1]
    rw [lineAt_tangent D _ hBh.symm]
    refine bgData_ext' ?_ ?_
    · funext y i
      have e := congrFun (congrFun hct y) i
      have e2 : D.Ψ y i = (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').Ψ y i + ζ * v (unitPt S.hG' y, i) := by
        have : D.Ψ y i - (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').Ψ y i = ζ * v (unitPt S.hG' y, i) := by
          rw [← liftC_apply S.hG' v y i]; exact e
        linear_combination this
      rw [e2, S.dataUC_Ψ, ← hbase, S.dataUC_Ψ]
      simp [psiAtV]
    · funext y i
      rw [hDh, S.dataUC_h, S.hh₀]
  rw [hDeq] at h1
  exact h1

/-- **`hdomT` from the marked disc.**  The premises of `hreal_level` at the step
(`R ≥ 2`, `2 C₄ K₁ (C₁ ε) + 5 R δ₁ ≤ c₁`), the datum premise `hD` and the marked disc `hdisc` give
the domain premise `hdomT` of `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`. -/
theorem markReal_hdomT_of_disc (ha₁ : 0 < S.a₁) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    {R₁ r t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (x : S.E) (u : ℂ)
    (hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    ∀ t : ℂ, ‖t‖ < t₁ → ∀ s ∈ Icc (0 : ℝ) 1, ∀ᶠ ζ : ℂ in nhds (s : ℂ),
      InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        (S.dataUC (S.psiAtV ζ (S.markedTangentC z u t x))) :=
  S.markReal_hdomT_of_hreal z hR
    (fun ψ' h1 h2 => hreal_level (Gp := S.G') (Hm := stepG d L N₁ m₁ k ϱ) hC S.hG S.hG'
      (le_refl (k + 1)) ha₁ H hc7 (by linarith) hsm S.D' hD ψ' h1 h2) hR₁ hr x u hdisc

section Phi

/-- **The marked derivative identity without the domain premise `hdomT`**: the landed
`hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` with `hdomT` discharged by
`markReal_hdomT_of_hreal` from `hreal` and `hdisc`.  All other premises are unchanged. -/
theorem hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_disc (ha₁ : 0 < S.a₁)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D')
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (hreal : ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁, IsLayerConstant (stepG d L N₁ m₁ k ϱ) ψ' →
      ∃ D : BgData (stepG d L N₁ m₁ k ϱ) N, (∀ x i, D.h x i = S.D'.h x i) ∧
      compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
        ((composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D').lineAt
          (tangentData D (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D')) t))
    (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (han : ∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
      (XiCRaw S.G' S.a S.ν (k + 1) 1 eps ×ˢ FlBall (stepG d L N₁ m₁ k ϱ) δ₁))
    (hsum : ∀ zb, ∀ Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps,
      ∀ ψ' ∈ FlBall (stepG d L N₁ m₁ k ϱ) δ₁,
      blockEnergyOne S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG₂ κ eps k zb (Θ, ψ') =
        ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ'))
    {R₁ r t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁) (x : S.E) (u : ℂ)
    (hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • S.shiftUC x) + t • liftC S.hG' (S.maskUC z (S.shiftUC x))) ∈
        FlBall (stepG d L N₁ m₁ k ϱ) δ₁) :
    HasDerivAt (fun t : ℂ => S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) (S.markedTangentC z u t x))
      (-(S.β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb, deriv (markedBlockTerm (Ev zb Y) taylorWeight
        (liftC S.hG' (u • S.shiftUC x)) (liftC S.hG' (S.maskUC z (S.shiftUC x)))
        (rawOf S.D')) 0) 0 :=
  S.hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom z ha₁ H hD2 hC hc7 hR hRs hsmall hnum hnum' hD
    hreal 𝒴 Ev han hsum hR₁ hr ht₁ x u hdisc (S.markReal_hdomT_of_hreal z hR hreal hR₁ hr x u hdisc)

end Phi

end StepSetting

end Balaban.Fluctuation
