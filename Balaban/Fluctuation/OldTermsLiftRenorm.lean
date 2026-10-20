/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftLimit

/-!
# The first three inherited renormalization conditions

At inherited levels the infinite-volume local energy is identical. The value
and derivative conditions therefore transport without a change in the reference
field. The positivity test in the external-field derivative uses the old mass.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
  {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
  {j : ℕ} {νk : ℝ} {idx : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}

/-- The zero value at the reference field is retained at an inherited level. -/
theorem liftOldTermsFam_renormVal (hT : TorusIndep m₀ Tm)
    (hR : RenormCondAlong m₀ k νk Tm j idx hidx) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (i₀ : Fin N) :
    ElocInf m₀ (liftOldTermsFam Tm) j 0
      (constInf (Pi.single i₀ 1)) (constInf (Pi.single i₀ 1)) = 0 := by
  rw [liftOldTermsFam_ElocInf_eq hT hj1 hjk]
  exact hR.val i₀

/-- The external-field derivative condition is retained at an inherited level. -/
theorem liftOldTermsFam_renormDh (hT : TorusIndep m₀ Tm)
    (hR : RenormCondAlong m₀ k νk Tm j idx hidx) (hν : 0 < νk)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N) :
    fderiv ℂ (fun h : Fin N → ℂ => ElocInf m₀ (liftOldTermsFam Tm) j 0
      (constInf (Pi.single i₀ 1)) (constInf h))
      (Pi.single i₀ 1) (Pi.single i₀ 1) = 0 := by
  have heq : (fun h : Fin N → ℂ => ElocInf m₀ (liftOldTermsFam Tm) j 0
      (constInf (Pi.single i₀ 1)) (constInf h)) =
      (fun h : Fin N → ℂ => ElocInf m₀ Tm j 0
        (constInf (Pi.single i₀ 1)) (constInf h)) := by
    funext h
    exact liftOldTermsFam_ElocInf_eq hT hj1 hjk _ _ _
  rw [heq]
  have hνj : 0 < nuIdeal L k νk j := by
    have hL : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    unfold nuIdeal
    positivity
  exact hR.dh i₀ hνj

/-- The constant-field derivative condition is retained at an inherited level. -/
theorem liftOldTermsFam_renormDpsi (hT : TorusIndep m₀ Tm)
    (hR : RenormCondAlong m₀ k νk Tm j idx hidx) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (i₀ : Fin N) :
    deriv (fun t : ℂ => ElocInf m₀ (liftOldTermsFam Tm) j 0
      (constInf ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ)))
      (constInf (Pi.single i₀ 1))) 0 = 0 := by
  have heq : (fun t : ℂ => ElocInf m₀ (liftOldTermsFam Tm) j 0
      (constInf ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ)))
      (constInf (Pi.single i₀ 1))) =
      (fun t : ℂ => ElocInf m₀ Tm j 0
        (constInf ((1 + t) • (Pi.single i₀ 1 : Fin N → ℂ)))
        (constInf (Pi.single i₀ 1))) := by
    funext t
    exact liftOldTermsFam_ElocInf_eq hT hj1 hjk _ _ _
  rw [heq]
  exact hR.dpsi i₀

end Balaban.Fluctuation
