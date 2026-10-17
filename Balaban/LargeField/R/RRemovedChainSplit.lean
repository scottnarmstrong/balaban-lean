/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainLevel
public import Balaban.LargeField.Operators.QuietInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The weight of a quiet step: Gaussian factor times the rest (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (b), (c).  The weight `K e^{Re b}` of a quiet step
kernel is the Gaussian product `gaussProd` times `quietRest e^{Re b}` (`absW_quiet_split`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Split

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs : ℕ → LocalHistory S n M K → ℝ}
  (SD : StepData k0 geo cs N κs)

/-- **The weight of a quiet step**: `K e^{Re b} = (∏ z^N t_k) · (quietRest e^{Re b})`. -/
theorem absW_quiet_split {k : ℕ} (hk : k + 1 ≤ K) (hadm : H.Admissible) (Z' : H.Comp (k + 1))
    (hQ : IsQuiet (H.locRH (k + 1) Z') k Z'.1) (hz : 0 ≤ cs.z (k + 1))
    (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    (SD.ker k (H.localHistory M K (k + 1) Z')).absW o x hv g =
      ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs o x) *
        ENNReal.ofReal (quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
          (locRH_rem (k + 1) Z') o x hv *
          Real.exp ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g).re) := by
  have hK : (SD.ker k (H.localHistory M K (k + 1) Z')).K o x hv =
      gaussProd N (H.localHistory M K (k + 1) Z') k cs o x *
        quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
          (locRH_rem (k + 1) Z') o x hv :=
    (SD.quiet H hadm k hk Z' hQ o x hv).trans
      (quietKernel_eq geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') o x hv)
  unfold LFKernel.absW
  rw [hK, mul_assoc, ENNReal.ofReal_mul (gaussProd_nonneg N _ k cs hz hc o x)]

end Split

end Balaban.LargeField
