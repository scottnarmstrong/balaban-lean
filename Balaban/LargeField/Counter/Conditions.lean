module

public import Balaban.LargeField.Counter.Params

/-!
# The conditions defining `λ_*` (Part I, §I.5.3)

`LamStarConditions T x₀` is the conjunction of (Λ0)–(Λ11): each condition is a statement
`∀ x ≥ x₀, …` about the auxiliary functions of the typing data.  `FlowLamConditions` collects
the flow-specific conditions (Λ12), (Λ12′), (Λ13), (Λ14).
-/

@[expose] public section

namespace Balaban.LargeField

/-- The conditions (Λ0)–(Λ11) of the abstract LF-2 (§I.5.3), for all real `x ≥ x₀`. -/
structure LamStarConditions (T : Typing) (x₀ : ℝ) : Prop where
  one_le : 1 ≤ x₀
  -- (Λ0)
  l0_a : ∀ x ≥ x₀, 4 * T.cStar * T.θp ≤ x
  l0_b : ∀ x ≥ x₀, T.θp * (T.hBar x + 2) ≤ x / (4 * T.cStar)
  l0_c : ∀ x ≥ x₀, T.n2Bar x ≤ x / (T.α * T.logL)
  l0_d : ∀ x ≥ x₀, T.CE * x ^ (2 * T.d + 1) + 1 ≤ 2 * T.A2 * x ^ T.p2
  l0_e : ∀ x ≥ x₀, T.CE * x ^ (2 * T.d + 1) + 1 ≤ 1 / 2 * T.A3 * (x / 2) ^ (2 * T.p0)
  -- (Λ1)
  l1_a : ∀ x ≥ x₀, T.θp * (2 + Real.logb T.L (T.nuBar x * T.Dbar x)) ≤ x
  l1_b : ∀ x ≥ x₀,
    1 + Real.logb T.L (T.nuBar x * T.Dbar x) + T.n2Bar (2 * x) ≤ x / (T.α * T.logL)
  -- (Λ2)
  l2 : ∀ x ≥ x₀, T.CE * x ^ (2 * T.d + 1) + T.Phi x + 1 ≤ 1 / 2 * T.A3 * (x / 2) ^ (2 * T.p0)
  -- (Λ3)
  l3 : ∀ x ≥ x₀, T.Phi x + 1 ≤ 1 / 2 * (T.L : ℝ) ^ x
  -- (Λ4)
  l4 : ∀ x ≥ x₀, T.Phi x + 1 ≤ (T.L : ℝ) ^ x / (2 * T.Dbar x)
  -- (Λ5)
  l5_a : ∀ x ≥ x₀, T.DeltaBar x * T.Abar (3 * T.cStar * x) ≤ 1 / 2 * T.A2 * x ^ T.p2
  l5_b : ∀ x ≥ x₀, T.CE * x ^ (2 * T.d + 1) ≤ 1 / 2 * T.A2 * x ^ T.p2
  -- (Λ6)
  l6 : ∀ x ≥ x₀, (T.cStar * (T.hBar x + 1) + 1) * T.Abar (3 * T.cStar * x) ≤
    T.A2 * (x / (4 * T.cStar)) ^ T.p2
  -- (Λ7)
  l7 : ∀ x ≥ x₀, (T.Gbar x + 2 * T.cStar) * T.Abar (T.cPrime * x) + T.CE * x ^ (2 * T.d + 1) ≤
    2 * T.A2 * x ^ T.p2
  -- (Λ8)
  l8_a : ∀ x ≥ x₀, T.Phi x ≤ (T.L : ℝ) ^ (x / 2 - 1)
  l8_b : ∀ x ≥ x₀, T.Phi x ≤ (T.L : ℝ) ^ (x / 2) / (2 * (1 + T.Dbar x))
  -- (Λ9)
  l9 : ∀ x ≥ x₀, T.Phi x ≤ T.Cν * x ^ T.p2
  -- (Λ10)
  l10 : ∀ x ≥ x₀, T.CR * x ^ (2 * T.d + 1) + 2 * T.A2 * (T.cDPrime * x) ^ T.p2 +
      (x / (T.α * T.logL) + 1) * T.Cw * (T.cDPrime * x) ^ (2 * T.d + 1) + 1 ≤
    T.A3' * x ^ T.pR
  -- (Λ11)
  l11_a : ∀ x ≥ x₀, T.cH ≤ T.d / 2 * x
  l11_b : ∀ x ≥ x₀, x * T.Cw * (T.d * x) ^ (2 * T.d + 1) ≤ T.A2 * x ^ T.p2
  l11_c : ∀ x ≥ x₀, T.A2 * x ^ T.p2 ≥ T.CE * (T.d * x) ^ (2 * T.d + 1)
  l11_d : ∀ x ≥ x₀, T.A2 * x ^ T.p2 + x * T.Cw * (T.d * x) ^ (2 * T.d + 1) +
      T.CE * (T.d * x) ^ (2 * T.d + 1) ≤ 1 / 2 * T.A3 * x ^ (2 * T.p0)

/-- The flow-specific conditions (Λ12), (Λ12′), (Λ13), (Λ14) of §I.5.3. -/
structure FlowLamConditions (T : Typing) (x₀ : ℝ) : Prop where
  l12 : ∀ x ≥ x₀, x * (1 - 1 / (2 * T.logL)) ≥ ((T.d : ℝ) + 3) / 2
  l12' : ∀ x ≥ x₀, 2 * (T.L : ℝ) ^ 2 ≤ 2 / 3 * Real.exp (x - 2)
  l13 : ∀ x ≥ x₀, 4 * T.nuBar x * (T.critBar x + T.omegaBar x) + 4 ≤
    Real.exp (x / 2 - 1) / Real.sqrt 2
  l14 : ∀ x ≥ x₀, 3 ≤ x

end Balaban.LargeField
