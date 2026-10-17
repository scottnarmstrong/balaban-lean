/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftMomentGeom
public import Balaban.SmallField.Def6InfD2

/-!
# The inherited second-moment derivative

The full finite-torus energy agrees after a linear field reindexing.  At
analytic reference fields this identity transports its second derivative.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A second derivative of the full inherited energy is unchanged by field pullback. -/
theorem liftOldTerms_D2 (m₀ j : ℕ)
    (Tm : Terms d L (L * N₁) m₁ k N ϱ)
    (h c v w : Fld d L N₁ m₁ (k + 1) N)
    (hAnNew : AnalyticAt ℂ
      (fun ψ : Fld d L N₁ m₁ (k + 1) N =>
        Edens m₀ (liftOldTerms Tm) j ψ h) c)
    (hAnOld : AnalyticAt ℂ
      (fun ψ : Fld d L (L * N₁) m₁ k N =>
        Edens m₀ Tm j ψ (lowerNewField h)) (lowerNewField c)) :
    D2 (fun ψ : Fld d L N₁ m₁ (k + 1) N =>
      Edens m₀ (liftOldTerms Tm) j ψ h) c v w =
    D2 (fun ψ : Fld d L (L * N₁) m₁ k N =>
      Edens m₀ Tm j ψ (lowerNewField h))
      (lowerNewField c) (lowerNewField v) (lowerNewField w) := by
  apply D2_congr_slice hAnNew hAnOld (δ := 1) (by exact zero_lt_one)
  intro s t _ _
  rw [liftOldTerms_Edens]
  congr 1

end Balaban.Fluctuation
