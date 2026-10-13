/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DetDecCovSymm
public import Balaban.Fluctuation.DetActivitySymm

/-!
# Covariance of the root trace and of the determinant activities under lattice symmetries

Let `S : LatSymm G G σ`, `hU : UnitBlockPres σ`, `CS : CoverSymm (coverOf G) σ` and
`u = unitAct G S hU` the induced permutation of the unit points.  From the covariance of the
decoupled logarithm (`DetDecCov.decLog_rm`) the diagonal trace over the transported unit root
satisfies exactly the hypothesis `hRT` of `detActivityBg_sym_of_rootTrace`:

`rootTrace {u y} (CS.par s) (symSite σ φ) (S.mul α) = rootTrace {y} s φ α`

(`rootTrace_unitAct`, `hRT_unitAct`).  Together with the identity `rootIdxOf (u y) = rootAct σ
(rootIdxOf y)` for a paving symmetry (`rootIdxOf_unitAct`) this gives the covariance of the
determinant activities (`detActivityBg_sym`) with the remaining premises of
`detActivityBg_sym_of_rootTrace` (paving membership and patch covariance).

Covariance of the CLASS terms (after the collar regrouping, on the class domain) is NOT proved
here.  The statements are not chart-sensitive and independent of the choice of generator.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv
  Balaban.Localization.DetUnitIncidence Balaban.Localization.DetDecCov Finset Matrix

section Trace

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
variable (S : LatSymm G G σ) (hU : UnitBlockPres σ) (CS : CoverSymm (coverOf G) σ)

include S hU CS in
/-- **T3. The root trace over the transported unit root is unchanged**: for the induced
permutation `u = unitAct G S hU` of the unit points,
`rootTrace {u y} (CS.par s) (σ-transported φ) (S.mul α) = rootTrace {y} s φ α`. -/
theorem rootTrace_unitAct (a : ℕ → ℝ) (aT ν : ℝ) (y : unitPts G) (s : DecParams G)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    rootTrace G a aT ν (unitQ G) (unitP G) {unitAct G S hU y} (CS.par s) (symSite σ φ)
        (S.mul α) =
      rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α := by
  unfold rootTrace
  simp only [Finset.sum_singleton]
  refine congrArg (fun t => -(1 / 2 : ℂ) * t) (Finset.sum_congr rfl fun i _ => ?_)
  have h : decLog G a aT ν (S.mul α) (extS G (CS.par s)) (symSite σ φ) (unitQ G) (unitP G) =
      rm ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
        (decLog G a aT ν α (extS G s) φ (unitQ G) (unitP G)) := decLog_rm S hU CS a aT ν α s φ
  rw [h]
  exact rm_apply ((unitAct G S hU).prodCongr (Equiv.refl (Fin N)))
    (decLog G a aT ν α (extS G s) φ (unitQ G) (unitP G)) (y, i) (y, i)

end Trace

end Balaban.Fluctuation
