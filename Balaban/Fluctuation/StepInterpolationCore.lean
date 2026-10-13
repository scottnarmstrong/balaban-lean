/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexCov

/-!
# The two-stage interpolation algebra of the step identity (internal proof-step lemma)

The generic part of the proof of the fixed-field step identity (FLUCTUATION.md §2.6, P4
(2.36)-(2.63)): for a probability measure `ν`, the truncated exponents `Wt₁, Wt₂` (equal to the
exponents `W₁, W₂` almost everywhere), the normalization of the Gaussian weight and the
determinant prefactor, the fluctuation integral equals `exp` of the sum of the prefactor exponent
and the two interpolation integrals.  This is an internal lemma: the source-facing theorems are
`prop26C_step` and the later identity for free data.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Set

/-- **The two-stage interpolation algebra of the step identity** (internal proof-step lemma).
Let `ν` be a probability measure; `Wt₁, Wt₂` be `C¹` families on a neighbourhood of `[0,1]` that
agree with `W₁, W₂` almost everywhere (for all parameters at once), vanish at the parameter `0`,
with `Z_{s,0} ≠ 0` and `Z_{1,t} ≠ 0` on `[0,1]`.  If the integrand is
`P w exp (Wt₁(1) + Wt₂(1))`, the integral of the weight is `P Zc Z_{1,1}`, `P = K0 exp Y`,
`exp δ = K0 (Bp Zc)`, `Dt = exp h` and `Ytot = Y + δ + h + (E1 + F0)`, where `E1` and `F0` are the
two interpolation integrals, then `Bp Dt ∫ f = exp Ytot`. -/
theorem step_interp_identity {Ω : Type*} [MeasurableSpace Ω] (ν m : Measure Ω)
    [IsProbabilityMeasure ν] (Wt₁ Wt₂ W₁ W₂ : ℝ → Ω → ℂ) {U : Set ℝ} {W₁' W₂' : ℝ → Ω → ℂ}
    (h₁ : IsC1Family U Wt₁ W₁') (h₂ : IsC1Family U Wt₂ W₂')
    (hae₁ : ∀ᵐ x ∂ν, ∀ r, Wt₁ r x = W₁ r x) (hae₂ : ∀ᵐ x ∂ν, ∀ r, Wt₂ r x = W₂ r x)
    (hWt₁0 : ∀ x, Wt₁ 0 x = 0) (hWt₂0 : ∀ x, Wt₂ 0 x = 0) (hW₂0 : ∀ x, W₂ 0 x = 0)
    (hnv₁ : ∀ s ∈ Icc (0 : ℝ) 1, partFun₂ ν W₁ W₂ s 0 ≠ 0)
    (hnv₂ : ∀ t ∈ Icc (0 : ℝ) 1, partFun₂ ν W₁ W₂ 1 t ≠ 0)
    (f : Ω → ℂ) (w : Ω → ℝ) (P Zc K0 Bp Dt Y δ h E1 F0 Ytot : ℂ)
    (hE1 : E1 = ∫ s in (0 : ℝ)..1,
      avgFun ν W₁ (fun x => deriv (fun r => W₁ r x) s) s)
    (hF0 : F0 = ∫ t in (0 : ℝ)..1,
      avgFun₂ ν W₁ W₂ (fun x => deriv (fun r => W₂ r x) t) 1 t)
    (hint : ∀ x, f x = P * ((w x : ℝ) : ℂ) * Complex.exp (Wt₁ 1 x + Wt₂ 1 x))
    (hweight : ∫ x, P * ((w x : ℝ) : ℂ) * Complex.exp (Wt₁ 1 x + Wt₂ 1 x) ∂m =
      P * Zc * partFun₂ ν Wt₁ Wt₂ 1 1)
    (hP : P = K0 * Complex.exp Y) (hδ : Complex.exp δ = K0 * (Bp * Zc))
    (hdet : Dt = Complex.exp h) (hX : Ytot = Y + δ + h + (E1 + F0)) :
    Bp * Dt * ∫ x, f x ∂m = Complex.exp Ytot := by
  have hZ00 : partFun₂ ν Wt₁ Wt₂ 0 0 = 1 := by
    unfold partFun₂
    simp [hWt₁0, hWt₂0]
  have hexp := partFun₂_one_one_eq (ν := ν) h₁ h₂
    (fun s hs => by
      have h := hnv₁ s hs
      rwa [← partFun₂_congr_ae (ν := ν) (W₁ := Wt₁) (W₁' := W₁) (W₂ := Wt₂) (W₂' := W₂)
        (hae₁.mono fun x hx => hx s) (hae₂.mono fun x hx => hx 0)] at h)
    (fun t ht => by
      have h := hnv₂ t ht
      rwa [← partFun₂_congr_ae (ν := ν) (W₁ := Wt₁) (W₁' := W₁) (W₂ := Wt₂) (W₂' := W₂)
        (hae₁.mono fun x hx => hx 1) (hae₂.mono fun x hx => hx t)] at h)
  rw [hZ00, one_mul] at hexp
  have hI1 : (∫ s in (0 : ℝ)..1, avgFun₂ ν Wt₁ Wt₂ (W₁' s) s 0) = E1 := by
    rw [hE1]
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hsU : s ∈ U := h₁.Icc_subset (by rwa [Set.uIcc_of_le zero_le_one] at hs)
    rw [avgFun_eq_avgFun₂ (W₂ := W₂) hW₂0]
    refine avgFun₂_congr_ae ?_ ?_ ?_
    · exact hae₁.mono fun x hx => hx s
    · exact hae₂.mono fun x hx => hx 0
    · filter_upwards [hae₁] with x hx
      have hd := h₁.hasDerivAt x s hsU
      have hfun : (fun r => Wt₁ r x) = fun r => W₁ r x := funext hx
      rw [hfun] at hd
      exact hd.deriv.symm
  have hI2 : (∫ t in (0 : ℝ)..1, avgFun₂ ν Wt₁ Wt₂ (W₂' t) 1 t) = F0 := by
    rw [hF0]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htU : t ∈ U := h₂.Icc_subset (by rwa [Set.uIcc_of_le zero_le_one] at ht)
    refine avgFun₂_congr_ae ?_ ?_ ?_
    · exact hae₁.mono fun x hx => hx 1
    · exact hae₂.mono fun x hx => hx t
    · filter_upwards [hae₂] with x hx
      have hd := h₂.hasDerivAt x t htU
      have hfun : (fun r => Wt₂ r x) = fun r => W₂ r x := funext hx
      rw [hfun] at hd
      exact hd.deriv.symm
  have hI : ∫ x, f x ∂m = P * Zc * Complex.exp (E1 + F0) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hint), hweight, hexp, hI1, hI2]
  rw [hI, hdet, hP, hX]
  simp only [Complex.exp_add]
  rw [hδ]
  ring

end Balaban.Fluctuation
