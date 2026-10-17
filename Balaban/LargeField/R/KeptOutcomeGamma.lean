module

public import Balaban.LargeField.R.SmallFactorGe
public import Balaban.LargeField.R.Outcome
public import Balaban.LargeField.History.Scale
import Mathlib.Tactic.Positivity

/-!
# The bound (III.5.1) in the form of `KeptData.gam_ge`

The bridge from `SmallFactorPar.smallFactor_ge` to the setting: with `P.A3 = S.A3'`, `P.pR = S.pR`
and `P.lamHat = λ̂_k`, one has `A'₃ λ̂_k^{p_R} ≤ γ_i - log C_dec`.
-/

@[expose] public section

namespace Balaban.LargeField

variable {S : Setting}

/-- **(III.5.1) in the setting** (the form `KeptData.gam_ge` needs): if the constants of
`SmallFactorPar` are those of the setting (`A3 = A'₃`, `p_R`) and `λ̂_k` is its scale parameter, then
`A'₃ λ̂_k^{p_R} ≤ γ_i - log C_dec(ϰ_i)`. -/
theorem smallFactor_ge_setting {P : SmallFactorPar} (h : P.Hyp) (hA : P.A3 = S.A3')
    (hp : P.pR = (S.pR : ℝ)) (i : Fin 5) :
    S.A3' * P.lamHat ^ S.pR ≤ P.gamma i - Real.log (cDec i) := by
  have h1 := SmallFactorPar.smallFactor_ge h i
  have hx : 0 < P.lamHat := by linarith [h.lamHat_ge]
  have h0 : 0 ≤ S.A3' * P.lamHat ^ S.pR := by
    have := SmallFactorPar.A3_nonneg h
    rw [hA] at this
    positivity
  rw [hA, hp, Real.rpow_natCast] at h1
  linarith

end Balaban.LargeField
