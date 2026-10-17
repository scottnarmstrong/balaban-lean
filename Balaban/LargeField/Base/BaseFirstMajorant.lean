module

public import Balaban.LargeField.Base.BaseFirstActivity

/-!
# Arithmetic closure of five first-component witness gains

This theorem exposes each physical witness gain. The estimate of the actual first-component
integral by these five gains is a named premise, not supplied by the arithmetic theorem.
-/

@[expose] public section

namespace Balaban.LargeField

/-- Five typewise charges absorb a witness-choice cost and a local volume cost. The parameters
`nPA`, `nPB`, `nQ`, `nR`, `nS` are nonnegative real cardinalities of the five seed types. -/
theorem baseFirst_fiveShare_exponent_bound
    (lam : ℝ) (p₀ : ℕ) (A₃ Cwit Cloc c₁ c₂ V : ℝ)
    (nPA nPB nQ nR nS gPA gPB gQ gR gS : ℝ)
    (hPA : 2 * A₃ * lam ^ (2 * p₀) * nPA ≤ gPA)
    (hPB : 2 * A₃ * lam ^ (2 * p₀) * nPB ≤ gPB)
    (hQ : 2 * A₃ * lam ^ (2 * p₀) * nQ ≤ gQ)
    (hR : 2 * A₃ * lam ^ (2 * p₀) * nR ≤ gR)
    (hS : 2 * A₃ * lam ^ (2 * p₀) * nS ≤ gS)
    (hPA0 : 0 ≤ nPA) (hPB0 : 0 ≤ nPB) (hQ0 : 0 ≤ nQ)
    (hR0 : 0 ≤ nR) (hS0 : 0 ≤ nS) (hV : 0 ≤ V)
    (hWit : Cwit ≤ A₃ * lam ^ (2 * p₀))
    (hVol : Cloc * (lam + 1) ≤ c₁ * lam + c₂) :
    Real.exp (-(gPA + gPB + gQ + gR + gS) +
      Cwit * (nPA + nPB + nQ + nR + nS) + Cloc * (lam + 1) * V) ≤
      Real.exp (-A₃ * lam ^ (2 * p₀) * (nPA + nPB + nQ + nR + nS) +
        (c₁ * lam + c₂) * V) := by
  have hn : 0 ≤ nPA + nPB + nQ + nR + nS := by linarith
  have hw := mul_le_mul_of_nonneg_right hWit hn
  have hv := mul_le_mul_of_nonneg_right hVol hV
  have hg : 2 * A₃ * lam ^ (2 * p₀) * (nPA + nPB + nQ + nR + nS) ≤
      gPA + gPB + gQ + gR + gS := by
    nlinarith [hPA, hPB, hQ, hR, hS]
  apply Real.exp_le_exp.mpr
  nlinarith [hg, hw, hv]

/-- A physical integral estimate with the five explicitly stated gain inequalities implies
P5's local form (30), provided the supremum of the input is nonnegative. -/
theorem baseFirst_operator_majorant_of_fiveShares
    (lam : ℝ) (p₀ : ℕ) (A₃ Cwit Cloc c₁ c₂ V : ℝ)
    (nPA nPB nQ nR nS gPA gPB gQ gR gS B supF : ℝ)
    (hPA : 2 * A₃ * lam ^ (2 * p₀) * nPA ≤ gPA)
    (hPB : 2 * A₃ * lam ^ (2 * p₀) * nPB ≤ gPB)
    (hQ : 2 * A₃ * lam ^ (2 * p₀) * nQ ≤ gQ)
    (hR : 2 * A₃ * lam ^ (2 * p₀) * nR ≤ gR)
    (hS : 2 * A₃ * lam ^ (2 * p₀) * nS ≤ gS)
    (hPA0 : 0 ≤ nPA) (hPB0 : 0 ≤ nPB) (hQ0 : 0 ≤ nQ)
    (hR0 : 0 ≤ nR) (hS0 : 0 ≤ nS) (hV : 0 ≤ V)
    (hWit : Cwit ≤ A₃ * lam ^ (2 * p₀))
    (hVol : Cloc * (lam + 1) ≤ c₁ * lam + c₂)
    (hsup : 0 ≤ supF)
    (hPhysicalActivity : B ≤ Real.exp (-(gPA + gPB + gQ + gR + gS) +
      Cwit * (nPA + nPB + nQ + nR + nS) + Cloc * (lam + 1) * V) * supF) :
    B ≤ Real.exp (-A₃ * lam ^ (2 * p₀) * (nPA + nPB + nQ + nR + nS) +
      (c₁ * lam + c₂) * V) * supF :=
  hPhysicalActivity.trans (mul_le_mul_of_nonneg_right
    (baseFirst_fiveShare_exponent_bound lam p₀ A₃ Cwit Cloc c₁ c₂ V
      nPA nPB nQ nR nS gPA gPB gQ gR gS
      hPA hPB hQ hR hS hPA0 hPB0 hQ0 hR0 hS0 hV hWit hVol) hsup)

end Balaban.LargeField
