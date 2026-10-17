/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalConstants
public import Balaban.Inhabited.DAPhysicalCutoff
public import Balaban.Fluctuation.StepRegWitnessGeneral

/-!
# The radius comparison for the last-scale interaction (W887, blocker 5)

The cutoff of the last integral is the logarithmic cutoff of the papers, `ρ = p₁(β) = A₁ (log β)^p`
(`pLog`), which is small against `√β`; the physical analyticity radius `fluctRadius` does not depend
on `β`.  Hence the condition `B(κ) β^{-1/2} ρ < fluctRadius` of `cutoffInteraction_final_fluctRadius`
holds as it stands for all large `β`, with the row constant `B(κ)` of the cut family, and no cutoff
smaller by a constant factor is needed.

* `cutConst_mul_pLog_lt`: for `B ≥ 0`, `R > 0` and `β ≥ 1 + (A₁ (4p/e)^p · 2(B+1)/R)^4`,
  `B β^{-1/2} pLog A₁ p β < R`.
* `cutoffInteraction_final_pLog`: the analyticity of the cutoff interaction on the polydisc with
  `ρ = pLog A₁ p β` and the physical radius `fluctRadius`, for `β` above that threshold.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Filter Metric

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.Inhabited

/-- **The cutoff `pLog` against a fixed radius.**  For `B ≥ 0`, `R > 0`, `A₁ ≥ 0` and
`β ≥ max 1 (pLogThreshold A₁ p (R / (2 (B + 1))))`, one has `B β^{-1/2} pLog A₁ p β < R`. -/
theorem cutConst_mul_pLog_lt {B R A₁ : ℝ} (hB : 0 ≤ B) (hR : 0 < R) (hA : 0 ≤ A₁) (p : ℕ)
    {β : ℝ} (hβ1 : 1 ≤ β) (hβ : pLogThreshold A₁ p (R / (2 * (B + 1))) ≤ β) :
    B * (β ^ (-(1 / 2 : ℝ)) * pLog A₁ p β) < R := by
  have hc : 0 < R / (2 * (B + 1)) := by positivity
  have h := pLog_le_mul_sqrt hA p hc hβ1 hβ
  have hβ0 : 0 < β := by linarith
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have e : β ^ (-(1 / 2 : ℝ)) = (Real.sqrt β)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hβ0.le]
  have h2 : (Real.sqrt β)⁻¹ * pLog A₁ p β ≤ R / (2 * (B + 1)) := by
    rw [inv_mul_le_iff₀ hs]; linarith
  have h3 : B * ((Real.sqrt β)⁻¹ * pLog A₁ p β) ≤ B * (R / (2 * (B + 1))) :=
    mul_le_mul_of_nonneg_left h2 hB
  have h4 : B * (R / (2 * (B + 1))) < R := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  rw [e]; linarith

section Final

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The cutoff interaction at the logarithmic cutoff.**  For `β ≥ 1` above the explicit threshold
`pLogThreshold A₁ p (fluctRadius / (2 (B(κ) + 1)))`, with `ρ = pLog A₁ p β`, the integral
`∫_{box ρ} F (φ₀ + β^{-1/2} C_fin(s) ψ) dγ` of an interaction `F` analytic and bounded on the
polydisc of radius `fluctRadius` around `φ₀` is analytic on the polydisc of radius `e^κ`. -/
theorem cutoffInteraction_final_pLog {d' L' N' : ℕ} [NeZero L']
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) (hd' : 0 < d') {β B' : ℝ} (hβ1 : 1 ≤ β)
    (hβ : pLogThreshold A₁ p (fluctRadius d' L' N' /
      (2 * ((4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) + 1))) ≤ β)
    {γ : Measure (L1Torus d N₀ → ℝ)}
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p β} < ⊤)
    {F : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc φ₀ (fun _ => fluctRadius d' L' N')))
    (hFB : ∀ w ∈ polydisc φ₀ (fun _ => fluctRadius d' L' N'), ‖F w‖ ≤ B') :
    AnalyticOnNhd ℂ (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ pLog A₁ p β},
        F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := by
  have hBpos := cutConst_pos (d := d) (L := L) hd κ
  have hR := fluctRadius_pos_general (d := d') (L := L') (N := N') hd'
  have hρ : 0 ≤ pLog A₁ p β := pLog_nonneg hA p hβ1
  exact cutoffInteraction_final_fluctRadius (d' := d') (L' := L') (N' := N') hd hk hv0 hv1 ha1 ha2
    hmass hM hκ hMB hMκ hρ (by linarith) hγ
    (cutConst_mul_pLog_lt hBpos.le hR hA p hβ1 hβ) hF hFB

end Final

end Balaban.Green
