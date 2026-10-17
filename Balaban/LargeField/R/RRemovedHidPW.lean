/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidChain
public import Balaban.LargeField.R.RRemovedKernel
public import Balaban.LargeField.R.RRemovedHidCover

/-!
# The pointwise bound of the integrand of the removed-kernel window integral (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (3), (5).  `window_pw`: the integrand
`c₀(o) K^{→R}(o', x) e^{Re b(o', x)} / ∫ r` is at most `Q_b · e^{B_w}` times the Gaussian products of the steps,
the indicator `I_O I_S` of the shells of the outputs and of the new′ variables, and the product of the
weights of the core operators, when the quotient `c₀(o) / ∫ r` is at most `Q_b` on the shells.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section PW

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The integrand is at most its absolute-value density**: the weights `t s z w ∈ [0, 1]` of "to `R`". -/
theorem remF_le_absW {a : LocalHistory S n M K} {k : ℕ} (Z0 : Set (BlockAt S n M K k))
    (P : OpPkg N R a k) {t s z w : OutT N R a k → SubCfg N a k P.A → ℝ} {c0 : OutT N R a k → ℝ}
    {r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ}
    (ht : ∀ o x, 0 ≤ t o x ∧ t o x ≤ 1) (hs : ∀ o x, 0 ≤ s o x ∧ s o x ≤ 1)
    (hz : ∀ o x, 0 ≤ z o x ∧ z o x ≤ 1) (hw : ∀ o x, 0 ≤ w o x ∧ w o x ≤ 1)
    (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y) (o o' : OutT N R a k) (x : SubCfg N a k P.A)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    ENNReal.ofReal (c0 o * (toRKernel a k P.T.K t s z w o' x hv *
        Real.exp (P.T.b o' x hv g).re) / remDen a k Z0 r o) ≤
      ENNReal.ofReal (c0 o / remDen a k Z0 r o) * P.T.absW o' x hv g := by
  have hD := remDen_nonneg a k Z0 hr o
  have hK := P.T.K_nonneg o' x hv
  have hE := (Real.exp_pos (P.T.b o' x hv g).re).le
  have hwt : ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR ≤ 1 := by
    simp only [ROutcome.weight]
    have := ht o' x; have := hs o' x; have := hz o' x; have := hw o' x
    calc t o' x * s o' x * z o' x * w o' x ≤ 1 * 1 * 1 * 1 := by gcongr <;> simp_all
      _ = 1 := by norm_num
  have hwt0 : 0 ≤ ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR := by
    simp only [ROutcome.weight]
    exact mul_nonneg (mul_nonneg (mul_nonneg (ht o' x).1 (hs o' x).1) (hz o' x).1) (hw o' x).1
  have hq0 : 0 ≤ c0 o / remDen a k Z0 r o := div_nonneg (hc0 o) hD
  unfold LFKernel.absW toRKernel
  rw [← ENNReal.ofReal_mul hq0]
  refine ENNReal.ofReal_le_ofReal ?_
  have : c0 o * (P.T.K o' x hv * ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR *
      Real.exp (P.T.b o' x hv g).re) / remDen a k Z0 r o =
      (c0 o / remDen a k Z0 r o) * (P.T.K o' x hv * Real.exp (P.T.b o' x hv g).re) *
        ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR := by ring
  rw [this]
  calc (c0 o / remDen a k Z0 r o) * (P.T.K o' x hv * Real.exp (P.T.b o' x hv g).re) *
        ROutcome.weight (t o' x) (s o' x) (z o' x) (w o' x) ROutcome.toR
      ≤ (c0 o / remDen a k Z0 r o) * (P.T.K o' x hv * Real.exp (P.T.b o' x hv g).re) * 1 := by
        gcongr
    _ = _ := mul_one _

end PW

end Balaban.LargeField
