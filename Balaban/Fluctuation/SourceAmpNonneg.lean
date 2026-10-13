/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceFamilyRelative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Nonnegativity of the step amplitudes; the source label activities over the chart

The landed `sourceFamilyRelative_scale` states its label-activity conclusions under the inner
premise `0 ≤ ε_U`, with `ε_U = β · prop33EpsEtaScaled … 0 0 (q/β)`, because no landed lemma gives the
sign of the source constant `cK2' · δ₁`.  This file proves the signs and the scale statement without
the premise.

* `cK2'_nonneg`: `0 ≤ cK2' d L N B` for `0 ≤ B`.
* `famConst_nonneg`: `0 ≤ famConst d L BG κ` for `0 ≤ BG` and `0 < d`.
* `cK2'_famConst_mul_nonneg`: `0 ≤ cK2' d L N (famConst d L BG₂ κ) · δ₁` for `0 ≤ BG₂`, `0 < d`,
  `0 ≤ δ₁`.
* `prop33EpsEtaScaled_nonneg`: `0 ≤ prop33EpsEtaScaled … 0 0 η` for `0 < r`, `0 ≤ η`, `0 ≤ δ₁` and
  the signs above; `beta_mul_prop33EpsEtaScaled_nonneg`: the same for `β · … (q/β)`.
* `Balaban.Inhabited.sourceFamilyRelative_scale_nonneg`: the statement of
  `sourceFamilyRelative_scale` at every scale, with `0 ≤ ε_U` part of the conclusion (so that the
  label activity family is defined without a premise), the amplitude bound
  `4 ε_U ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k` of `sourceAmp_scale`, and the signs of
  the constants.  The constants `BG, BG₂, κ` are hidden by the existential of the landed scale
  theorem, so its proof is re-run with the signs exposed.
* `Balaban.Inhabited.sourceFamilyRelative_nonneg_instance`: the case `k = 1`, `N₁ = 6`.

What is NOT proved here: the identification of the exponent on the chart (the value of `physVal` at
`(q, g/β)` with `JointRep.W1 + W2`) and the complex activity bound off the central real datum.  The
class enters only through the zero class of the landed theorems, so nothing depends on a choice of
generating sets of class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background

section Signs

/-- `cK2'` is nonnegative for a nonnegative family constant. -/
theorem cK2'_nonneg (d L N : ℕ) [NeZero L] {B : ℝ} (hB : 0 ≤ B) : 0 ≤ cK2' d L N B := by
  have h1 := cA_ge d L N
  have h2 := cF_pos d L
  unfold cK2' cN'
  positivity

/-- `famConst` is nonnegative for `0 ≤ BG` and `0 < d` (it is at least `1`). -/
theorem famConst_nonneg (d L : ℕ) {BG : ℝ} (hBG : 0 ≤ BG) (hd : 0 < d) (κ : ℝ) :
    0 ≤ famConst d L BG κ := by
  have := famConst_ge_one (L := L) hBG κ hd
  linarith

/-- The source constant `cK2' · δ₁` is nonnegative. -/
theorem cK2'_famConst_mul_nonneg (d L N : ℕ) [NeZero L] {BG₂ κ δ₁ : ℝ} (hBG₂ : 0 ≤ BG₂)
    (hd : 0 < d) (hδ₁ : 0 ≤ δ₁) : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
  mul_nonneg (cK2'_nonneg d L N (famConst_nonneg d L hBG₂ hd κ)) hδ₁

/-- `cK2'` times `δ₁` is nonnegative from the sign of the family constant (the form the tower
supplies: `0 ≤ famConst d L BG₂ κ`). -/
theorem cK2'_famConst_mul_nonneg_of_famConst (d L N : ℕ) [NeZero L] {BG₂ κ δ₁ : ℝ}
    (hB : 0 ≤ famConst d L BG₂ κ) (hδ₁ : 0 ≤ δ₁) :
    0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
  mul_nonneg (cK2'_nonneg d L N hB) hδ₁

/-- **The amplitude of the zero class is nonnegative.**  For `0 < r`, `0 ≤ η`, `0 ≤ δ₁` and
`0 ≤ famConst d L BG₂ κ`, `prop33EpsEtaScaled … 0 0 η ≥ 0`. -/
theorem prop33EpsEtaScaled_nonneg (d L N m₁ n m₀ : ℕ) [NeZero L] {a₁ BG BG₂ κ δ₁ r η : ℝ}
    (hB : 0 ≤ famConst d L BG₂ κ) (hδ₁ : 0 ≤ δ₁) (hr : 0 < r) (hη : 0 ≤ η) :
    0 ≤ prop33EpsEtaScaled d L N m₁ n m₀ a₁ BG BG₂ κ δ₁ r 0 0 η := by
  have hc1 : 0 ≤ c1 d L := by have := one_le_c1 d L; linarith
  have hK := cK2'_famConst_mul_nonneg_of_famConst d L N (κ := κ) (δ₁ := δ₁) hB hδ₁
  unfold prop33EpsEtaScaled
  have h0 : 0 ≤ 3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L a₁) n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
        (rho4 d L N BG κ)‖ / r ^ 3 := by positivity
  have h1 : 0 ≤ η * (cK2' d L N (famConst d L BG₂ κ) * δ₁ + 0) / r := by
    rw [add_zero]; positivity
  have h2 : (0 : ℝ) * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r = 0 := by
    simp
  rw [h2]
  linarith

/-- `0 ≤ β · prop33EpsEtaScaled … 0 0 (q/β)` for `0 < β`, `0 ≤ q`. -/
theorem beta_mul_prop33EpsEtaScaled_nonneg (d L N m₁ n m₀ : ℕ) [NeZero L]
    {a₁ BG BG₂ κ δ₁ r q β : ℝ} (hB : 0 ≤ famConst d L BG₂ κ) (hδ₁ : 0 ≤ δ₁) (hr : 0 < r)
    (hq : 0 ≤ q) (hβ : 0 < β) :
    0 ≤ β * prop33EpsEtaScaled d L N m₁ n m₀ a₁ BG BG₂ κ δ₁ r 0 0 (q / β) :=
  mul_nonneg hβ.le (prop33EpsEtaScaled_nonneg d L N m₁ n m₀ hB hδ₁ hr (div_nonneg hq hβ.le))

end Signs

end Balaban.Fluctuation
