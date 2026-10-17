/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedWindowGen
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The window integral: the pointwise bound of the exponentials (Lemma III.8.7 (2)) (W905)

`notes/phase1/LF4R-PLAN.md`, leaf 6, step (2).  For the removed outcome the integrand, after the
integration of the Gaussian-only variables and of `ψ_k↾Z₀` (the composition identity), is the
product of the core operators, the window exponential `e^{Re b_win}`, the constant of the composed
Gaussian `const = e^{Lc}`, and the quotient of (2.58′) (`frac`, whose bound is
`removedFactor_le_restricted`); it vanishes off the support set `E` of the window characteristic
functions.  `window_pointwise_le` bounds it, uniformly in the core variables, by the core factor
times `e^{B_w + L_c + F} 1_E`, where `Re b_win ≤ B_w` is (S0) (the quiet-step bounds
`Σ_j (C_b log β_j + C_b B₀) |X_j|_{j+1}`) and `frac ≤ e^F` is `removedFactor_le_restricted`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- **The pointwise bound of the integrand, uniformly in the core variables** (step (2)). -/
theorem window_pointwise_le {Wd Cr : Type*} (G Core : Wd → Cr → ℝ≥0∞) (E : Set Wd)
    (bw frac : Wd → Cr → ℝ) (Bw Lc Fr : ℝ)
    (hid : ∀ w c, G w c ≤ Core w c *
      ENNReal.ofReal (Real.exp (bw w c) * Real.exp Lc * frac w c))
    (hsupp : ∀ w c, w ∉ E → G w c = 0)
    (hbw : ∀ w c, w ∈ E → bw w c ≤ Bw) (hfrac0 : ∀ w c, 0 ≤ frac w c)
    (hfrac : ∀ w c, w ∈ E → frac w c ≤ Real.exp Fr) (w : Wd) (c : Cr) :
    G w c ≤ Core w c * E.indicator (fun _ => ENNReal.ofReal (Real.exp (Bw + Lc + Fr))) w := by
  by_cases hw : w ∈ E
  · rw [Set.indicator_of_mem hw]
    refine (hid w c).trans ?_
    gcongr
    have h1 := Real.exp_le_exp.2 (hbw w c hw)
    have h2 := hfrac w c hw
    have h3 := hfrac0 w c
    rw [Real.exp_add, Real.exp_add]
    calc Real.exp (bw w c) * Real.exp Lc * frac w c
        ≤ Real.exp Bw * Real.exp Lc * frac w c := by gcongr
      _ ≤ Real.exp Bw * Real.exp Lc * Real.exp Fr := by gcongr
  · rw [Set.indicator_of_notMem hw, hsupp w c hw]
    simp

end Balaban.LargeField
