/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseSmallField
import Mathlib.Tactic.Linarith

/-!
# `BaseStepData` and `GaussStructure` are inhabited

The zero-remainder, zero-boundary `BaseSmallFieldInput` (`baseSmallFieldInput_nonempty`) gives
`BaseStepData` through `baseStepData_of_input` and `GaussStructure` through
`baseKernel_gaussStructure_of_input`; the kernel of this member is `∏ z^N t_0 · ∑_w F^w · 0 = 0`
(degenerate, as `baseSmallFieldInput_nonempty` is), so these are inhabitation witnesses only.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M] [NeZero S.L]

/-- **`BaseStepData` is inhabited** for constants with `0 ≤ C_b`, `0 ≤ B_0`, `1 ≤ β_0`,
`0 ≤ z_1` and `0 ≤ β_0 a_ker L^{d-2}`. -/
theorem baseStepData_nonempty (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) (hβ : 1 ≤ cs.beta 0)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) :
    Nonempty (BaseStepData K k0 geo cs N) := by
  obtain ⟨inp⟩ := baseSmallFieldInput_nonempty (K := K) geo cs N k0 hCb hB0 hβ
  exact ⟨baseStepData_of_input inp hz hc⟩

/-- **`GaussStructure` is inhabited** for every local history `a`. -/
theorem gaussStructure_nonempty (geo : Geo S n R M) (cs : OpConsts) (N k0 : ℕ)
    (hCb : 0 ≤ cs.Cb) (hB0 : 0 ≤ cs.B0) (hβ : 1 ≤ cs.beta 0)
    (hz : 0 ≤ cs.z (0 + 1)) (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (a : LocalHistory S n M K) :
    ∃ (T : LFKernel (OutT N R a (0 + 1)) (NewCfg N a 0) (EuclideanSpace ℝ (Fin N))
        (GIdx S n M K N)) (wit : GaussWit N R a 0), GaussStructure cs a 0 T wit := by
  obtain ⟨inp⟩ := baseSmallFieldInput_nonempty (K := K) geo cs N k0 hCb hB0 hβ
  exact ⟨_, _, baseKernel_gaussStructure_of_input inp hz hc a⟩

end Balaban.Inhabited
