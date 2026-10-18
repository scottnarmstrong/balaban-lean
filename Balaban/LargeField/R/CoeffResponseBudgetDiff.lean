/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBudgetHcoef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The action difference of two backgrounds from the response sup bounds

For two fields `φ⁰, φ¹` on one datum, one coefficient `a` and one mass `ν` (the mass-convention
residual `hswitch` of P7CONV §3.5 and the datum-response residual `hpair` of §3.3 are of this
form), the same counting as for `hcoef` gives
`‖β A_X(φ¹) - β A_X(φ⁰)‖ ≤ A |X|_{mix} [V ∑_Z √(G_Z G'_Z) + V²/2 ∑_Z G'_Z]`
from the weight-one sup bounds `V` of `φ¹ - φ⁰` (for the mass change:
`massChange_sameData_response`, `V = K_w m B_h`) and the sup bounds of the reads at `φ⁰`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **Action difference of two backgrounds from the response sup bounds.** -/
theorem Region.actionDiff_response_le (X : Region G) (Dc : StepDecomp X) (a : ℕ → ℝ) (ν : ℝ)
    (Dat : BgData G N) (φ0 φ1 : G.Ω 1 × Fin N → ℂ)
    {β A V Cb Cg Cm Sb Sg Sm : ℝ} (hβ : 0 ≤ β) (hA : 0 ≤ A) (hV : 0 ≤ V)
    (hCb : 0 ≤ Cb) (hCg : 0 ≤ Cg) (hCm : 0 ≤ Cm) (hSb : 0 ≤ Sb) (hSg : 0 ≤ Sg) (hSm : 0 ≤ Sm)
    (hcb : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a x‖ ≤ Cb * (A * Dc.wt c))
    (hcg : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ Cg * (A * Dc.wt c))
    (hcm : ∀ c, β * ∑ _x ∈ (Dc.cube c).sites, |ν| ≤ Cm * (A * Dc.wt c))
    (hval : ∀ (x : G.Ω 1) (j : Fin N), 1 * ‖(φ1 - φ0) (x, j)‖ ≤ V)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G (φ1 - φ0) (x + Pi.single μ 1) j - svec G (φ1 - φ0) x j‖) ≤ V)
    (hbwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (j : Fin N),
      1 * (G.spacing x * ‖svec G (φ1 - φ0) (x - Pi.single μ 1) j - svec G (φ1 - φ0) x j‖) ≤ V)
    (hrB : ∀ x ∈ X.sites, ∑ j, ‖Dat.Ψ x j - blockAvg G φ0 x j‖ ^ 2 ≤ Sb)
    (hrGf : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (x + Pi.single μ 1) j - barField G Dat.Ψ φ0 x j‖ ^ 2 ≤ Sg)
    (hrGb : ∀ x ∈ X.sites, ∀ μ : Fin d, G.spacing x ^ 2 * ∑ j,
      ‖barField G Dat.Ψ φ0 (x - Pi.single μ 1) j - barField G Dat.Ψ φ0 x j‖ ^ 2 ≤ Sg)
    (hrM : ∀ x ∈ X.sites, ∑ j, ‖svec G φ0 x j - Dat.h x j‖ ^ 2 ≤ Sm) :
    ‖(β : ℂ) * actionRegionC X a ν Dat φ1 - (β : ℂ) * actionRegionC X a ν Dat φ0‖ ≤
      A * Dc.total * (V * (Real.sqrt ((Sb * Cb) * (N * Cb)) +
        Real.sqrt ((d * (Sg * Cg)) * (d * (N * Cg))) + Real.sqrt ((Sm * Cm) * (N * Cm))) +
      V ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) := by
  have hT := Dc.total_nonneg
  have hAT : 0 ≤ A * Dc.total := mul_nonneg hA hT
  have e1 : φ0 + (φ1 - φ0) = φ1 := by abel
  have key := actionRegionC_add_sub_le X a ν Dat φ0 (φ1 - φ0) (β := β) (A := A * Dc.total)
    (σ := V) (GB := Sb * Cb) (GB' := N * Cb) (GG := d * (Sg * Cg)) (GG' := d * (N * Cg))
    (GM := Sm * Cm) (GM' := N * Cm) hβ hAT hV (mul_nonneg hSb hCb) (by positivity)
    (mul_nonneg hSm hCm)
    (by
      have := Region.siteEnergy_le Dc (fun x => ‖levelCoeff G a x‖)
        (fun x j => Dat.Ψ x j - blockAvg G φ0 x j) (B := Sb) (κ := Cb * A) hβ hSb
        (fun x => norm_nonneg _) hrB (fun c => by simpa only [mul_assoc] using hcb c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.blockEnergy_response_le Dc a (φ1 - φ0) (V := V) (A := A) (Cb := Cb) hβ hval
        hcb
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.bondEnergy_le Dc (barField G Dat.Ψ φ0) (B := Sg) (κ := Cg * A) hβ hSg
        hrGf hrGb (fun c => by simpa only [mul_assoc] using hcg c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.bondEnergy_response_le Dc (φ1 - φ0) (V := V) (A := A) (Cg := Cg) hβ hfwd
        hbwd hcg
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.siteEnergy_le Dc (fun _ => |ν|) (fun x j => svec G φ0 x j - Dat.h x j)
        (B := Sm) (κ := Cm * A) hβ hSm (fun _ => abs_nonneg _) hrM
        (fun c => by simpa only [mul_assoc] using hcm c)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (by
      have := Region.massEnergy_response_le Dc (φ1 - φ0) (V := V) (A := A) (Cm := Cm) (ν := ν)
        hβ hval hcm
      calc _ ≤ _ := this
        _ = _ := by ring)
  rw [e1] at key
  rw [← mul_sub]
  calc _ ≤ _ := key
    _ = _ := by ring

end Balaban.LargeField.ActionConv
