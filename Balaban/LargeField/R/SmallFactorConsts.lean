module

public import Balaban.LargeField.R.Outcome
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The small-factor exponents `γ₁, …, γ₅` and the bound (III.5.1) (Lemma III.5.3)

The five exponents of Lemma III.5.3 as explicit functions of the constants of the chain, and the
final bound (III.5.1)
`γ_i - log C_dec(ϰ_i) ≥ 2 A'₃ λ̂_k^{p_R}`, `p_R = 2 p₀ - 2 w₀`, under the premises collected in
`SmallFactorPar` (the constants of rows 0-15, Lemma III.1.2 (a), Lemma III.4.4 and (Λ19), (Λ20),
(Λ24)).  The constant exponent `wE = w₀ - 2` is real.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The constants entering Lemma III.5.3: `γ₀`, `A₀`, `A₁`, `a`, `K₁`, `ε`, `c_*`, `C_Ŵ`, `p₀`,
`w₀ - 2` (`wE`), and the scale data `η_k`, `λ_k`, `λ_{k₁}`, `Ŵ_k`, `λ̂_k`. -/
structure SmallFactorPar where
  gamma0 : ℝ
  A0 : ℝ
  A1 : ℝ
  a : ℝ
  K1 : ℝ
  eps : ℝ
  cStar : ℝ
  CW : ℝ
  p0 : ℕ
  wE : ℝ
  eta : ℝ
  lamK : ℝ
  lamK1 : ℝ
  What : ℝ
  lamHat : ℝ

namespace SmallFactorPar

variable (P : SmallFactorPar)

/-- `γ₁ = 9/8 (1-η_k) γ₀ A₀² λ_k^{2p₀}/a - 1/2` (Lemma III.5.3 (a)). -/
noncomputable def gamma1 : ℝ :=
  9 / 8 * (1 - P.eta) * P.gamma0 * P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a - 1 / 2

/-- `γ₂ = (1-η_k)/(144 K₁²) γ₀ A₀² λ_k^{2p₀}/a - 1` (Lemma III.5.3 (b)). -/
noncomputable def gamma2 : ℝ :=
  (1 - P.eta) / (144 * P.K1 ^ 2) * P.gamma0 * P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a - 1

/-- `γ₃ = e^{-2ε} γ₀ A₀² λ_{k₁}^{2p₀}/(72 a K₁² Ŵ_k²)` (Lemma III.5.3 (c)). -/
noncomputable def gamma3 : ℝ :=
  Real.exp (-2 * P.eps) * P.gamma0 * P.A0 ^ 2 * P.lamK1 ^ (2 * P.p0) /
    (72 * P.a * P.K1 ^ 2 * P.What ^ 2)

/-- `γ₄ = e^{-2ε} γ₀ A₁² λ_{k₁}^{2p₀}/(2 a Ŵ_k²) - 1` (Lemma III.5.3 (d)). -/
noncomputable def gamma4 : ℝ :=
  Real.exp (-2 * P.eps) * P.gamma0 * P.A1 ^ 2 * P.lamK1 ^ (2 * P.p0) / (2 * P.a * P.What ^ 2) - 1

/-- `γ₅ = γ₀ A₀² λ_k^{2p₀}/(72 K₁² a)` (Lemma III.5.3 (e)). -/
noncomputable def gamma5 : ℝ :=
  P.gamma0 * P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / (72 * P.K1 ^ 2 * P.a)

/-- The exponent `γ_i` of the kept outcome `ϰ_{i+1}`. -/
noncomputable def gamma : Fin 5 → ℝ
  | 0 => P.gamma1
  | 1 => P.gamma2
  | 2 => P.gamma3
  | 3 => P.gamma4
  | 4 => P.gamma5

/-- `p_R = 2 p₀ - 2 w₀ = 2 p₀ - 2 (wE + 2)`. -/
noncomputable def pR : ℝ := 2 * (P.p0 : ℝ) - 2 * (P.wE + 2)

/-- `A'₃ = e^{-2ε} γ₀/(8 a C_Ŵ² (4c_*)^{2p₀}) · min{A₀²/(72 K₁²), A₁²/2}`. -/
noncomputable def A3 : ℝ :=
  Real.exp (-2 * P.eps) * P.gamma0 / (8 * P.a * P.CW ^ 2 * (4 * P.cStar) ^ (2 * P.p0)) *
    min (P.A0 ^ 2 / (72 * P.K1 ^ 2)) (P.A1 ^ 2 / 2)

/-- The premises of Lemma III.5.3 (III.5.1): the positivity of the constants of rows 0-15, the
comparisons of Lemma III.1.2 (a) (`λ_k ≥ λ̂_k/2`, `λ_{k₁} ≥ λ̂_k/(4c_*)`), Lemma III.4.4
(`Ŵ_k ≤ C_Ŵ λ̂_k^{wE}`), (Λ19) (`η_k ≤ 1/2`) and (Λ20), (Λ24) (`λ̂_k ≥ 4` and
`2 A'₃ λ̂_k^{p_R} ≥ 3 + log 5`). -/
structure Hyp : Prop where
  gamma0_pos : 0 < P.gamma0
  A0_pos : 0 < P.A0
  A1_pos : 0 < P.A1
  a_pos : 0 < P.a
  K1_ge : 1 ≤ P.K1
  eps_nonneg : 0 ≤ P.eps
  cStar_ge : 1 ≤ P.cStar
  CW_ge : 1 ≤ P.CW
  p0_pos : 1 ≤ P.p0
  wE_nonneg : 0 ≤ P.wE
  eta_nonneg : 0 ≤ P.eta
  eta_le : P.eta ≤ 1 / 2
  lamK_ge : P.lamHat / 2 ≤ P.lamK
  lamK1_ge : P.lamHat / (4 * P.cStar) ≤ P.lamK1
  What_pos : 0 < P.What
  What_le : P.What ≤ P.CW * P.lamHat ^ P.wE
  lamHat_ge : 4 ≤ P.lamHat
  absorb : 3 + Real.log 5 ≤ 2 * P.A3 * P.lamHat ^ P.pR

end SmallFactorPar

end Balaban.LargeField
