/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalConstants
public import Balaban.Green.FinalAmplitude

/-!
# The amplitude of the `g`-dependent part of the last integral (W809)

Leaf 3 of `notes/phase1/FINALAMP.md`.  The `g`-dependent part of the final term is the Gaussian
average of `δF(ψ') = F(φ₀ + ψ') - F(φ₀)`, which vanishes at `ψ' = 0` (P4 (2.52)-(2.53) p. 694,
where `β^{-1/2} ∫₀¹ ⟨∂δF(β^{-1/2} C^{1/2} t ψ), C^{1/2} ψ⟩ dt = δF(β^{-1/2} C^{1/2} ψ)`).

* `norm_sub_le_of_polydisc`: Schwarz on a polydisc.  If `F` is analytic on the polydisc of radius
  `T` around `c` with `‖F w - F c‖ ≤ B` there, then `‖F w - F c‖ ≤ B R / T` on the polydisc of
  radius `R < T`.
* `cutoffInteraction_final_phys_sub`: `cutoffInteraction_final_phys` for `F - F(φ₀)`, where the
  sup bound `B` on the polydisc of radius `Rphys` becomes `B R₁ / Rphys` on a smaller polydisc of
  radius `R₁` that still contains the cut field (`B_cut β^{-1/2} ρ < R₁ < Rphys`).  The
  coefficients of the cutoff integral of `F - F(φ₀)` are then bounded by
  `B (R₁ / Rphys) γ(box ρ) e^{-(κ-1)|C|}`; with `R₁ ≤ 2 B_cut β^{-1/2} ρ` the amplitude is
  `2 B B_cut ρ β^{-1/2} / Rphys`.
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Filter Metric

namespace Balaban.Green

open Balaban.Localization Balaban.Analysis

section Schwarz

variable {ι : Type*} [Fintype ι]

/-- **Schwarz on a polydisc.**  `F` analytic on the polydisc of radius `T` around `c`, with
`‖F w - F c‖ ≤ B` there; then `‖F w - F c‖ ≤ B * (R / T)` on the polydisc of radius `R`,
`0 < R < T`. -/
theorem norm_sub_le_of_polydisc {c : ι → ℂ} {T R B : ℝ} (hR : 0 < R) (hRT : R < T)
    {F : (ι → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polydisc c (fun _ => T)))
    (hB : ∀ w ∈ polydisc c (fun _ => T), ‖F w - F c‖ ≤ B) {w : ι → ℂ}
    (hw : w ∈ polydisc c (fun _ => R)) :
    ‖F w - F c‖ ≤ B * (R / T) := by
  have hT : 0 < T := hR.trans hRT
  set u : ι → ℂ := ((R : ℂ))⁻¹ • (w - c) with hu
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hu1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h := hw i
    simp only [hu, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [inv_mul_le_iff₀ hR]
    simpa using h.le
  have hmem : ∀ t : ℂ, ‖t‖ < T → c + t • u ∈ polydisc c (fun _ => T) := by
    intro t ht i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, norm_mul]
    calc ‖t‖ * ‖u i‖ ≤ ‖t‖ * 1 := mul_le_mul_of_nonneg_left (hu1 i) (norm_nonneg _)
      _ < T := by simpa using ht
  have hG := Balaban.Localization.norm_le_of_vanishing_zero (ι := Unit) (R := 1) (T := T) (B := B)
    (fun t (_ : Unit → ℂ) => F (c + t • u) - F c)
    (fun p hp => by
      have hFt : AnalyticAt ℂ F (c + p.1 • u) :=
        hF _ (hmem _ (by simpa using hp.1))
      have hc : AnalyticAt ℂ (fun q : ℂ × (Unit → ℂ) => c + q.1 • u) p :=
        analyticAt_const.add (analyticAt_fst.smul analyticAt_const)
      exact (AnalyticAt.comp (g := F) (f := fun q : ℂ × (Unit → ℂ) => c + q.1 • u) hFt hc).sub
        analyticAt_const)
    (fun _ => by simp)
    (fun t ht _ _ => hB _ (hmem t (by simpa using ht)))
    (t := (R : ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]; exact hRT)
    (s := fun _ => 0) (fun i => by simp)
  have he : c + (R : ℂ) • u = w := by
    rw [hu, smul_smul, mul_inv_cancel₀ hRne, one_smul]; abel
  simpa only [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using hG

end Schwarz

section Cutoff

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The cutoff interaction of the `g`-dependent part.**  As `cutoffInteraction_final_phys`, for
the interaction `F - F(φ₀)`, which vanishes at the background.  Let `F` be analytic on the polydisc
of radius `Rphys` around `φ₀` with `‖F w - F φ₀‖ ≤ B` there, and let the cut field lie in the
smaller polydisc: `B_cut β^{-1/2} ρ < R₁ < Rphys` (`B_cut` the row constant of the cut family).
Then the cutoff integral `J` of `F - F(φ₀)` is analytic on the polydisc of radius `e^κ`, bounded
there by `B (R₁/Rphys) γ(box ρ)`, equals at `s = 1` the average with the square root of the final
operator, is the sum of its coefficients, and its coefficients are bounded by
`B (R₁/Rphys) γ(box ρ) e^{-(κ-1)|C|}`. -/
theorem cutoffInteraction_final_phys_sub (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ R₁ Rphys B β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < R₁) (hR₁ : R₁ < Rphys)
    {F : (L1Torus d N₀ → ℂ) → ℂ} {φ₀ : L1Torus d N₀ → ℂ}
    (hF : AnalyticOnNhd ℂ F (polydisc φ₀ (fun _ => Rphys)))
    (hFB : ∀ w ∈ polydisc φ₀ (fun _ => Rphys), ‖F w - F φ₀‖ ≤ B) :
    let J : (MacIdx d N₀ M → ℂ) → ℂ := fun s =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) - F φ₀) ∂γ
    AnalyticOnNhd ℂ J (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) ∧
    (∀ s ∈ polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ),
      ‖J s‖ ≤ B * (R₁ / Rphys) * (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal) ∧
    J (fun _ => 1) = ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (F (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          ∑ y, Localization.sqrtMat (finalOp d L N₀ k v a) x y * ((ψ y : ℝ) : ℂ)) - F φ₀) ∂γ ∧
    J (fun _ => 1) = ∑ C : Finset (MacIdx d N₀ M), coef J C ∧
    (∀ C, ‖coef J C‖ ≤ B * (R₁ / Rphys) *
      (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * Real.exp (-(κ - 1) * C.card)) := by
  have hcut : 0 ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) :=
    mul_nonneg (cutConst_pos (L := L) hd κ).le
      (mul_nonneg (Real.rpow_nonneg hβ.le _) hρ)
  have hR0 : 0 < R₁ := lt_of_le_of_lt hcut hBR
  have hsub : polydisc φ₀ (fun _ => R₁) ⊆ polydisc φ₀ (fun _ => Rphys) :=
    fun w hw i => lt_trans (hw i) hR₁
  have h := cutoffInteraction_final_phys (N₀ := N₀) (M := M) (L := L) (k := k) (v := v) (a := a)
    hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ (γ := γ) (ρ := ρ) (Rphys := R₁)
    (B' := B * (R₁ / Rphys)) (β := β) hρ hβ hγ hBR (F := fun w => F w - F φ₀) (φ₀ := φ₀)
    (fun w hw => (hF w (hsub hw)).sub analyticAt_const)
    (fun w hw => by
      simpa using norm_sub_le_of_polydisc hR0 hR₁ hF hFB hw)
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h6⟩

end Cutoff

end Balaban.Green
