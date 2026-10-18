/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseSmallField
import Mathlib.Tactic.Linarith

/-!
# `BaseStepData` and `GaussStructureFn` are inhabited

The zero-remainder `BaseSmallFieldInput` (`baseSmallFieldInput_nonempty`) gives `BaseStepData`
through `baseStepData_of_input` and the Gaussian structure through `baseStepData_of_input`'s field
`gauss1`; the kernel of this member is `∏ z^N t_0 · ∑_w F^w · 0 = 0` (degenerate, as
`baseSmallFieldInput_nonempty` is), so these are inhabitation witnesses only.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L]

/-- **`BaseStepData` is inhabited** for `0 ≤ z_1` and `0 ≤ β_0 a_ker L^{d-2}`. -/
theorem baseStepData_nonempty (geo : Geo S n R 1) (cs : OpConsts) (N k0 : ℕ)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) :
    Nonempty (BaseStepData k0 geo cs N) := by
  obtain ⟨inp⟩ := baseSmallFieldInput_nonempty geo cs N k0
  exact ⟨baseStepData_of_input inp hz hc⟩

/-- **The Gaussian structure is inhabited** for every admissible history, component and raw spins. -/
theorem gaussStructureFn_nonempty (geo : Geo S n R 1) (cs : OpConsts) (N k0 : ℕ)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (H : RegionHistory S n R k0 1) (hH : H.Admissible) (Z' : H.Comp 1)
    (br : BaseRecord S.d S.L (n 1) (R 0)) (hbr : br = H.baseRecord)
    (φ : CfgT S.d N S.L (n 1)) :
    ∃ (Kfn : OutT N R (H.localHistory 1 1 1 Z') 1 → NewCfg N (H.localHistory 1 1 1 Z') 0 →
        EuclideanSpace ℝ (Fin N) → ℝ) (wit : GaussWit N R (H.localHistory 1 1 1 Z') 0),
      GaussStructureFn cs (H.localHistory 1 1 1 Z') 0 Kfn wit := by
  obtain ⟨inp⟩ := baseSmallFieldInput_nonempty geo cs N k0
  exact ⟨_, _, (baseStepData_of_input inp hz hc).gauss1 H hH Z' br hbr φ⟩

end Balaban.Inhabited
