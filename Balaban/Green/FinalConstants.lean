/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalInteractionCutoff
public import Balaban.Fluctuation.Lemma25

/-!
# The cutoff interaction fed with an interaction on a physical field ball (W790, leaf L-C)

The last integral is over the unit Gaussian variable `ψ`; the physical field is
`φ₀ + β^{-1/2} C(s) ψ` (P4 (6.4)-(6.6)), and the interaction is analytic on the polydisc of radius
`Rphys` around the background `φ₀`.  Hence in the variable `ψ` the interaction has analyticity
radius `β^{1/2} Rphys`, and the condition `B ρ < R` of `cutoffInteraction_final` reads
`B β^{-1/2} ρ < Rphys` with `B` the row constant of the cut family and `ρ = p₁(β)` the cutoff.
This is the shape of the landed condition `B₅ β^{-1/2} p₁ ≤ fluctRadius` of Lemma 2.5, with `B₅`
replaced by the larger constant `B(κ)`; for fixed `p₁` it holds for all large `β`
(`cutConst_mul_lt_of_large`).

* `cutConst_pos`: `B(κ) > 0`.
* `cutConst_mul_lt_of_large`: for `β ≥ (B p / R)² + 1`, `B β^{-1/2} p < R`.
* `cutoffInteraction_final_phys`: `cutoffInteraction_final` for `F(φ₀ + β^{-1/2} w)`, `F` analytic
  and bounded on the polydisc of radius `Rphys` around `φ₀`, under `B β^{-1/2} ρ < Rphys`.
* `cutoffInteraction_final_fluctRadius`: the same with `Rphys = fluctRadius d' L' N'`.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Filter Metric

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis Balaban.Fluctuation

section Constants

variable {d L : ℕ} [NeZero L]

/-- The row constant `B(κ)` of the cut family is positive. -/
theorem cutConst_pos (hd : 0 < d) (κ : ℝ) :
    0 < 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L) := by
  have he := pdEps_pos (d := d) (L := L) hd
  have hg := Real.sqrt_pos.2 (finalGap_pos (d := d) (NeZero.pos L))
  have h1 : 0 < Real.exp (-(pdEps d L / 2)) := Real.exp_pos _
  have h2 : Real.exp (-(pdEps d L / 2)) < 1 := (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith))
  have hb : 0 < ballConst d (pdEps d L / 2) := by
    unfold ballConst
    exact pow_pos (div_pos (by linarith) (by linarith)) _
  positivity

/-- At `d = 3` the exponent constant of `B(κ)` is `pdH 3 = 13357`, so `B(κ) ≥ 8/3 · e^{13357 κ}/√finalGap`:
the comparison needs `β^{-1/2} p₁` smaller than `fluctRadius` by this factor. -/
theorem pdH_three : pdH 3 = 13357 := by
  norm_num [pdH]

end Constants

/-- For `β ≥ (B p / R)² + 1` (with `R > 0`), `B β^{-1/2} p < R`. -/
theorem cutConst_mul_lt_of_large {B p R : ℝ} (hR : 0 < R) {β : ℝ}
    (hβ : (B * p / R) ^ 2 + 1 ≤ β) : B * (β ^ (-(1 / 2 : ℝ)) * p) < R := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ0
  have e : β ^ (-(1 / 2 : ℝ)) = (Real.sqrt β)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hβ0.le]
  have hlt : B * p / R < Real.sqrt β := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  rw [e, ← mul_assoc, mul_comm B, mul_assoc, ← div_eq_inv_mul, div_lt_iff₀ hs]
  rw [div_lt_iff₀ hR] at hlt
  nlinarith

section Final

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The cutoff interaction for an interaction on a physical field ball.**  Let `F` be analytic and
bounded by `B'` on the polydisc of radius `Rphys` around `φ₀`, and `β > 0`.  If
`B β^{-1/2} ρ < Rphys` (`B` the row constant of the cut family, `ρ` the cutoff), then
`J(s) = ∫_{box ρ} F (φ₀ + β^{-1/2} C_fin(s) ψ) dγ(ψ)` is analytic on the polydisc of radius `e^κ`,
bounded by `B' γ(box ρ)`, and satisfies the conclusions of Lemma AE. -/
theorem cutoffInteraction_final_phys (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ Rphys B' β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < Rphys)
    {F : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc φ₀ (fun _ => Rphys)))
    (hFB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖F w‖ ≤ B') :
    let J : (MacIdx d N₀ M → ℂ) → ℂ := fun s =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ
    AnalyticOnNhd ℂ J (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖J s‖ ≤ B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal) ∧
    J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) x y * ((ψ y : ℝ) : ℂ)) ∂γ ∧
    J (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef J C ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal /
      (Real.exp κ - 1) ^ C.card) ∧
    (∀ C, ‖coef J C‖ ≤ B' * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal *
      Real.exp (-(κ - 1) * C.card)) := by
  have hc0 : 0 < β ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hβ _
  have hs0 : 0 < β ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hβ _
  have hcs : β ^ (-(1 / 2 : ℝ)) * β ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hβ]; simp
  set c : ℝ := β ^ (-(1 / 2 : ℝ)) with hc
  set sb : ℝ := β ^ (1 / 2 : ℝ) with hsb
  set F' : (L1Torus d N₀ → ℂ) → ℂ := fun w => F (fun x => φ₀ x + ((c : ℝ) : ℂ) * w x) with hF'
  have hmem : ∀ w ∈ polydisc (0 : L1Torus d N₀ → ℂ) (fun _ => sb * Rphys),
      (fun x => φ₀ x + ((c : ℝ) : ℂ) * w x) ∈ polydisc φ₀ (fun _ => Rphys) := by
    intro w hw x
    have := hw x
    simp only [Pi.zero_apply, sub_zero] at this
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc0]
    calc c * ‖w x‖ < c * (sb * Rphys) := mul_lt_mul_of_pos_left this hc0
      _ = Rphys := by rw [← mul_assoc, hcs, one_mul]
  have hFa : AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N₀ → ℂ) (fun _ => sb * Rphys)) := by
    intro w hw
    refine AnalyticAt.comp (g := F) (f := fun w : L1Torus d N₀ → ℂ =>
      fun x => φ₀ x + ((c : ℝ) : ℂ) * w x) (hF _ (hmem w hw)) ?_
    refine analyticAt_pi_iff.2 fun x => ?_
    exact analyticAt_const.add (analyticAt_const.mul (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : L1Torus d N₀ => ℂ) x).analyticAt w)))
  have hFB' : ∀ w ∈ polydisc (0 : L1Torus d N₀ → ℂ) (fun _ => sb * Rphys), ‖F' w‖ ≤ B' :=
    fun w hw => hFB _ (hmem w hw)
  have hBR' : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * ρ < sb * Rphys := by
    generalize (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) = Bc at hBR ⊢
    have h1 := mul_lt_mul_of_pos_right hBR hs0
    have h2 : Bc * (c * ρ) * sb = Bc * ρ * (c * sb) := by ring
    rw [h2, hcs, mul_one] at h1
    linarith
  have key := cutoffInteraction_final (N₀ := N₀) (M := M) (k := k) (L := L) (v := v) (a := a) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hγ hBR' hFa hFB'
  simpa only [hF'] using key

/-- The same with the landed radius `fluctRadius d' L' N'` of Lemma 2.5 as the physical radius. -/
theorem cutoffInteraction_final_fluctRadius {d' L' N' : ℕ} [NeZero L']
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ B' β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < fluctRadius d' L' N')
    {F : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc φ₀ (fun _ => fluctRadius d' L' N')))
    (hFB : ∀ w ∈ polydisc φ₀ (fun _ => fluctRadius d' L' N'), ‖F w‖ ≤ B') :
    AnalyticOnNhd ℂ (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) :=
  (cutoffInteraction_final_phys hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR hF hFB).1

end Final

end Balaban.Green
