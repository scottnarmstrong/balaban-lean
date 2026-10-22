/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeSum
public import Balaban.Localization.I5Inhabited

/-!
# The P3 premises of one root are satisfiable (Rule 10)

`RootLocPremises` holds for the geometry of `I5Inhabited` (`d = L = 3`, `N₁ = 6`, `K = 2`, the
level-one cube `X` with `𝒦_X = {0}`, `j = 1`, `m₀ = 0`) with no cut cube and the zero extension.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Analysis Balaban.Localization.I5Inhabited

/-- **`RootLocPremises` is inhabited** at an admissible choice of the parameters. -/
theorem rootLocPremises_nonempty (m₁ : ℕ) (ϱ κ κ₁ : ℝ) :
    RootLocPremises (GP m₁ ϱ) 0 (U := ℂ) (Empty.elim : Empty → ℕ × CTorus 3 3 6 m₁ 2) 1
      (box (0 : CTorus 3 3 6 m₁ 2) (3 * cellSide 3 0 m₁ 1)) {0} κ κ₁ 0 Set.univ
      (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ => 0) where
  cov := GP_covSetup
  mem := fun i => i.elim
  inj := fun i => i.elim
  disj := fun i => i.elim
  opt := GP_hopt
  Eb_nonneg := le_rfl
  refl := fun _ _ _ => trivial
  link := fun _ _ _ _ => trivial
  ana := analyticOnNhd_const
  bd := fun _ _ _ _ => by simp
  loc := fun _ _ _ _ _ _ _ _ _ _ _ => rfl

end Balaban.LargeField
