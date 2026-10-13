/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityDirectGeneral
public import Balaban.Inhabited.StepActivityDirectWitness
public import Balaban.Inhabited.GeneralClassWitnessStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The general step activity bound: consistency with the zero class and instances

* `stepActivityBound_zeroClass_direct_of_general`: the general theorem
  `stepActivityBound_direct_of_oldEnergyHatMatch`, specialized to the zero class with no old
  energy terms, is the landed `stepActivityBound_zeroClass_direct` (same conclusion, from a subset
  of its hypotheses; the named hypothesis is `oldEnergyHatMatch_zeroClass`).
* `oldEnergyHatMatch_witClass`, `oldObsHatMatch_witClass`: for the non-zero class member
  `witClass` of `GeneralClassWitnessStep`, at its step `witnessSetting`, the two named hypotheses
  hold with no old-term functionals.  The energy of `witClass` is `c · avg_z h(z)·h(z)`: it is not
  zero along the fluctuation path, but it does not depend on the spin, and the field `h` is fixed
  along the path, so its increment `δℰ_k` vanishes.  `Wone_witClass_eq_hat` and
  `Wtwo_witClass_eq_hat` are the two segment identities for this class (conditional on the chart
  hypotheses of the hat expansion at that step, which are not constructed there).
* `hatQClass`, `hatQClass_edens_ne_zero`, `stepActivityBound_hatQClass_nonempty`: the same terms
  on the torus of the hat witness (`N₁ = 9`, step `hatStep`), where every hypothesis of the
  general theorem is satisfied: a step activity bound with `κ_H = 2 κ_dec - 1` for a class whose
  old energy is not zero along the path.

What these instances do not show: an instance with an old term that varies along the fluctuation
(a nonempty family of old-term functionals).  For such a class the named hypotheses
`OldEnergyHatMatch`, `OldObsHatMatch` and the hypotheses of the expansion on the functionals are
not constructed.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section ZeroClass

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {c BG κ eps : ℝ}

/-- **The general theorem at the zero class is the landed theorem.**  With no old energy terms
(`𝒯E = ∅`) and the zero class, `stepActivityBound_direct_of_oldEnergyHatMatch` gives the conclusion
of `stepActivityBound_zeroClass_direct`: a step activity bound of the zero class for the source `0`
with `κ_H = 2 κ_dec - 1` and `ε_H = R_σ ε_U`. -/
theorem stepActivityBound_zeroClass_direct_of_general
    (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU κ0 κ' Kc' : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites (stepG d L N₁ m₁ k ϱ) k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ)
      (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L S.a₁) S.ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ)
      (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃
      Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L S.a₁) S.ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁V z))
    (hc : (Rσ * R₁ + r) * ρ < cψ)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU)
    (hεb : prop33Eps d L N m₁ k m₀ S.a₁ S.ν BG BG₂ κ δ₁ r ρE ρM * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1)
    (hDA : Rσ * εU ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp) (hRσ1 : 1 < Rσ) (h𝒯E : 𝒯E = ∅) :
    ∃ B : StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) 0,
      B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU := by
  subst h𝒯E
  exact stepActivityBound_direct_of_oldEnergyHatMatch S (zeroClass d L N₁ m₁ k N ϱ)
    (hC := hC) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1)
    (hR₁ := hR₁) (hr := hr) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX)
    (hδ₁ := hδ₁) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum)
    (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV)
    (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (hBE := hBE) (hFE := hFE) (hcovE := hcovE)
    (hX₁E := hX₁E) (hoptE := hoptE) (hlogE := hlogE) (hEbE := hEbE) (hEanE := hEanE)
    (hEbdE := hEbdE) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF)
    (hyF := hyF) (𝒯M := 𝒯M) (ys := ys) (is := is) (hys := hys) (hBM := hBM) (hFM := hFM)
    (hcovM := hcovM) (hX₁M := hX₁M) (hoptM := hoptM) (hlogM := hlogM) (hEbM := hEbM)
    (hEanM := hEanM) (hEbdM := hEbdM) (rE := rE) (hrE := hrE) (hρE0 := hρE0) (hρE := hρE)
    (hρM0 := hρM0) (hρM := hρM) (hBh0 := hBh0) (hBh := hBh) (hZν := hZν) (hc := hc) (hD := hD)
    (hN := hN) (hp := hp) (hpρ := hpρ) (hεpos := hεpos) (hεb := hεb) (hκE := hκE) (hKc := hKc)
    (hκ' := hκ') (hκa := hκa) (hDA := hDA) (R0 := R0) (hlt := hlt) (hRσ1 := hRσ1)
    (hmatchE := oldEnergyHatMatch_zeroClass S hBE hFE EE)

end ZeroClass

end Balaban.Fluctuation

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.Analysis Balaban.Inhabited Balaban.Localization.I5Inhabited Finset Matrix Set Metric

section WitClass

variable (m₁ : ℕ) {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **`OldEnergyHatMatch` for the non-zero class member `witClass` at its step**, with no old-term
functionals: its energy does not depend on the spin, so its increment along the fluctuation
vanishes. -/
theorem oldEnergyHatMatch_witClass (β δ : ℝ)
    {τι : Type*} [DecidableEq τι] {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus 3 3 6 m₁ (1 + 1))} {jE : τι → ℕ}
    (hBE : ∀ τ ∈ (∅ : Finset τι), BgSetting 2 (witnessSetting m₁ β δ).G' (GkE τ) (GjE τ)
      (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ (∅ : Finset τι), FlSetting 2 (witnessSetting m₁ β δ).G' (GkE τ)
      (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν κ BG eps
      δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (EE : τι → RawData 3 3 (6 * 3 ^ m₁) (1 + 1) 2 → ℂ) :
    OldEnergyHatMatch (witnessSetting m₁ β δ) (witClass m₁) ∅ hBE hFE EE :=
  oldEnergyHatMatch_empty_of_spinIndependent _ _ (fun _ _ _ _ _ _ => rfl) hBE hFE EE

/-- **`OldObsHatMatch` for `witClass` at its step**, with no old-term functionals, for every
source: its observable terms do not depend on the spin. -/
theorem oldObsHatMatch_witClass (β δ : ℝ) (g : Fld 3 3 6 m₁ (1 + 1) 2)
    {μι : Type*} [DecidableEq μι] {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) (ϱ₂M τ)} {r₀ δ₃ δfl : ℝ}
    {X₀M X₁M : μι → Finset (CTorus 3 3 6 m₁ (1 + 1))} {jM : μι → ℕ}
    (ys : μι → CTorus 3 3 6 m₁ (1 + 1)) (is : μι → Fin 2)
    (hBM : ∀ τ ∈ (∅ : Finset μι), BgSetting 2 (witnessSetting m₁ β δ).G' (GkM τ) (GjM τ)
      (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ (∅ : Finset μι), FlSetting 2 (witnessSetting m₁ β δ).G' (GkM τ)
      (stepG 3 3 6 m₁ 1 (rhoSep m₁)) (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν κ BG eps
      δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (EM : μι → RawData 3 3 (6 * 3 ^ m₁) (1 + 1) 2 → ℂ) :
    OldObsHatMatch (witnessSetting m₁ β δ) (witClass m₁) g ∅ ys is hBM hFM EM :=
  oldObsHatMatch_empty_of_spinIndependent _ _ (fun _ _ _ _ _ _ _ => rfl) g ys is hBM hFM EM

/-- **T1 on `witClass`.**  At the step `witnessSetting` and the non-zero class `witClass`, under
the chart hypotheses of the hat expansion at that step, the first exponent is the potential part of
the hat expansion (its old energy has no increment). -/
theorem Wone_witClass_eq_hat (β δ : ℝ) {pp : ℝ}
    (hC : FlCore 2 (witnessSetting m₁ β δ).G' (stepG 3 3 6 m₁ 1 (rhoSep m₁))
      (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (R0 : (witnessSetting m₁ β δ).RayData pp) (hlt : (witnessSetting m₁ β δ).p₁ < pp)
    (hD : XiCData (witnessSetting m₁ β δ).G' (witnessSetting m₁ β δ).a (witnessSetting m₁ β δ).ν (1 + 1) 1 eps (witnessSetting m₁ β δ).D')
    (hc7 : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * eps))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
    (hRs : R * δ₁ ≤ deltaStar 3 3 2) (hsmall : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
    (hnum : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
    (hnum' : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
      c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
    (hMX : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁)
    (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * eps) < δc)
    (hα : K4 3 3 2 BG κ * (xiC1 3 * eps) < coerciveConst 3 / 2)
    (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4) (hp₁ : 0 < (witnessSetting m₁ β δ).p₁) {cψ : ℝ}
    (hcψ : 0 ≤ cψ) (hpc : (witnessSetting m₁ β δ).p₁ < cψ)
    (hδ₁ : Real.sqrt ((2 : ℕ) : ℝ) * (‖(((witnessSetting m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC 3 3 2 (compWeight 3 (witnessSetting m₁ β δ).a₁ 1) κ * cψ)) < δ₁)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : (witnessSetting m₁ β δ).E}
    (hx : chiFl (witnessSetting m₁ β δ).U 2 (witnessSetting m₁ β δ).p₁ x = 1) :
    (s : ℂ) ^ 2 * ((-((witnessSetting m₁ β δ).β : ℂ)) * raySrc3 (hatFun (witnessSetting m₁ β δ).G'
        (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν eps (witnessSetting m₁ β δ).hG'
        (((witnessSetting m₁ β δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne (witnessSetting m₁ β δ).hG (witnessSetting m₁ β δ).hG' (le_refl (1 + 1))
          (witnessSetting m₁ β δ).a₁ (witnessSetting m₁ β δ).ν eps)) taylorWeight ((witnessSetting m₁ β δ).hatC x)
        ((witnessSetting m₁ β δ).hatC x) (s : ℂ) (rawOf (witnessSetting m₁ β δ).D')) =
      (witnessSetting m₁ β δ).Wone (witClass m₁) s x :=
  (witnessSetting m₁ β δ).Wone_eq_hat_of_spinIndependent (witClass m₁) hC R0 hlt hD hc7 hR hsmR hRs
    hsmall hnum hnum' hMX hdm hα hsm hp₁ hcψ hpc hδ₁ (fun _ _ _ _ _ _ => rfl) hs hx

end WitClass

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Filter Topology

/-- The class of the hat-witness step with a non-zero old energy: the terms `qTerms` of
`GeneralClassWitness` (energy `c · avg_z h(z)·h(z)` on the whole-torus polymer at the level `1`,
source part zero) on the torus of `hatStep` (`d = L = 3`, `N₁ = 9`, `N = 2`, index `2`),
`m₀ = 0`, `E_k = 0`. -/
noncomputable def hatQClass (m₁ : ℕ) : StepClass 3 3 9 m₁ 1 2 (rhoSep m₁) :=
  ⟨witConsts.m₀, qTerms 3 3 9 m₁ (1 + 1) 2 (rhoSep m₁) witConsts (fun _ => 0) 1, 0⟩

/-- **The old energy of `hatQClass` is not zero along the fluctuation path**: at every real old
spin `ψ` of the step `hatStep`, the density `ℰ^{(1)}` at the composed datum is not zero. -/
theorem hatQClass_edens_ne_zero (m₁ : ℕ) (β p₁ δ : ℝ) (ψ : (hatStep m₁ β p₁ δ).E) :
    Edens (hatQClass m₁).m₀ (hatQClass m₁).Tm 1
      (composedPairAt (hatStep m₁ β p₁ δ).a (hatStep m₁ β p₁ δ).ν (Nat.le_succ 1) 1
        ((hatStep m₁ β p₁ δ).dataU ψ)).1
      (composedPairAt (hatStep m₁ β p₁ δ).a (hatStep m₁ β p₁ δ).ν (Nat.le_succ 1) 1
        ((hatStep m₁ β p₁ δ).dataU ψ)).2 ≠ 0 := by
  classical
  rw [(hatStep m₁ β p₁ δ).composedPairAt_h ψ (Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩)]
  unfold Edens
  have hloc : ∀ y (ψ' : Fld 3 3 9 m₁ (1 + 1) 2),
      Eloc (hatQClass m₁).m₀ (hatQClass m₁).Tm 1 y ψ'
        (fun _ i => ((hatStep m₁ β p₁ δ).h₀ i : ℂ)) =
        ((cQ 3 3 9 m₁ (1 + 1) witConsts 1 : ℝ) : ℂ) := by
    intro y ψ'
    show Eloc witConsts.m₀ (qTerms 3 3 9 m₁ (1 + 1) 2 (rhoSep m₁) witConsts (fun _ => 0) 1) 1 y ψ'
      (constFld (fun i => ((unitVec hN2 i : ℝ) : ℂ))) = _
    rw [Eloc_qTerms, qAvg_const]
    simp only [↓reduceIte]
    rw [qCore_unit, mul_one]
  simp only [hloc]
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ ?_
  · have hne : ((Finset.univ : Finset (CTorus 3 3 9 m₁ (1 + 1))).filter
        (Aligned (3 ^ 1))).Nonempty :=
      ⟨cbase (3 ^ 1) (0 : CTorus 3 3 9 m₁ (1 + 1)), by simpa using aligned_cbase _⟩
    exact_mod_cast hne.card_pos.ne'
  · have : 0 < cQ 3 3 9 m₁ (1 + 1) witConsts 1 := by
      unfold cQ witConsts; positivity
    exact_mod_cast this.ne'

open Classical in
/-- **The general theorem has an instance at a class with a non-zero old energy**: at the step
`hatStep m₁ β p₁ δ` (`d = L = 3`, `β > 0`) every hypothesis of
`stepActivityBound_direct_of_oldEnergyHatMatch` holds for the class `hatQClass` (with no old-term
functionals; the named hypothesis is `oldEnergyHatMatch_empty_of_spinIndependent`), and the
activity bound has `κ_H = 2 κ_dec - 1` and `ε_H = R_σ ε_U`. -/
theorem stepActivityBound_hatQClass_main :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ), 0 < β ∧ 0 < p₁ ∧ p₁ < 2 ∧
      Nonempty ((hatStep m₁ β p₁ δ).RayData 2) ∧
      ∃ B : StepActivityBound (hatStep m₁ β p₁ δ) (hatQClass m₁) 0,
        ∃ κdec Rσ εU : ℝ, B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU ∧ 1 < Rσ ∧ 0 < εU := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  set β : ℝ := T ^ 2 / 3 with hβdef
  have hβ0 : 0 < β := by positivity
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hamp⟩ := directWitness_core_amp 2 β
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨cψ, hcψ0, hcψ1, hδ₁⟩ := exists_cpsi_le_one (Real.sqrt ((2 : ℕ) : ℝ))
    ‖(((hatStep m₁ β 0 δ).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖
    (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) 1) κ) ht0
  obtain ⟨R0⟩ := rayData_hatStep m₁ (cψ / 6) h4 hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2
  set S := hatStep m₁ β (cψ / 6) δ with hS
  have hp : 0 < S.p₁ := by show 0 < cψ / 6; positivity
  have hpρ : S.p₁ ≤ cψ / 6 := le_rfl
  have hlt : S.p₁ < 2 := by show cψ / 6 < 2; linarith
  have hc : ((2 : ℝ) * 2 + 1) * (cψ / 6) < cψ := by linarith
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  have hBh := hBh_of_xi (N := 2) (Gp := Gp m₁ (rhoSep m₁)) (bgHypNu m₁) nuW_pos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData S.G' (compWeight 3 1) nuW (1 + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  set Kc' : ℝ := K0 3 3 κ0 + 1 with hKc'
  have hK0 : 0 ≤ K0 3 3 κ0 := by
    unfold K0
    apply div_nonneg (Real.exp_pos _).le
    have : Real.exp (-1) < 1 := by simp
    linarith
  have hKc0 : 0 < Kc' := by rw [hKc']; linarith
  set εU : ℝ := 1 / (8 * Kc' ^ 3 * c1 3 3 *
    Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) / 2 with hεUdef
  have hc1p : 0 < c1 3 3 := by linarith [one_le_c1 3 3]
  have hεpos : 0 < εU := by rw [hεUdef]; positivity
  have hDA : 2 * εU ≤ 1 / (8 * Kc' ^ 3 * c1 3 3 *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG 3 3 + c1 3 3 + 0 * cG 3 3)) := by
    rw [hεUdef]; linarith
  have hκa' : 0 + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 := hκa
  have hεb : prop33Eps 3 3 2 m₁ 1 1 S.a₁ S.ν BG BG₂ κ t 1 0 0 * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + m₁)) ^ 3 *
        nuBd 3 3 2 1 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * t)
          (K4 3 3 2 BG κ * (xiC1 3 * t) + (1 + 3 * (xiC1 3 * t)) + (1 + 2 / nuW)) / 1)) ≤ εU := by
    rw [norm_zero, zero_mul, add_zero, Complex.norm_real, Real.norm_of_nonneg (show (0 : ℝ) ≤ S.β from hβ0.le)]
    exact hamp
  refine ⟨m₁, β, cψ / 6, δ, hβ0, by positivity, by linarith, ⟨R0⟩, ?_⟩
  obtain ⟨B, hB1, hB2⟩ := stepActivityBound_direct_of_oldEnergyHatMatch S (hatQClass m₁)
      (ρ := cψ / 6) (εU := εU) (κ0 := κ0) (κ' := 0) (Kc' := Kc')
      (Rσ := 2) (R₁ := 2) (r := 1) (R := 2) (m₀ := 1) (κdec := κdec) (κ₀ := κ0) (ρE := 0)
      (ρM := 0) (Bh := 1 + 2 / nuW) (δc := δc) (cψ := cψ)
      (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0})
      (X₁V := fun _ => Finset.univ) (jF := fun _ => 1) (XF := fun _ => Xr)
      (𝒦XF := fun _ => {0}) (X₁F := fun _ => Finset.univ)
      (τι := PEmpty.{1}) (μι := PEmpty.{1}) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
      (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
      (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
      (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
      (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
      (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
      (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
      (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
      hC hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) hκ0
      hκdec (by exact_mod_cast hκ) h1 (by norm_num) (by norm_num)
      hcψ0.le hMX hdm hα hsmX hδ₁ hc7 le_rfl g1 g2 g3 g4 g5
      (fun _ => covSetup)
      (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog)
      (fun z _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (fun z => blockMargin_univ fun x _ _ => mem_some_intBox h4 x)
      (∅ : Finset PEmpty.{1}) (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp))
      (fun _ => covSetup) (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm) (fun _ => hopt)
      (fun _ => treeLen_zero) (fun _ => hlog) (fun s => Finset.mem_univ _)
      (∅ : Finset PEmpty.{1}) (fun τ => PEmpty.elim τ) (fun τ => PEmpty.elim τ)
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ hτ => absurd hτ (by simp)) (fun τ hτ => absurd hτ (by simp))
      (fun τ => PEmpty.elim τ) (fun τ hτ => absurd hτ (by simp)) le_rfl (fun x => by simp) le_rfl
      (fun p => by simp) (by unfold nuW; norm_num) hBh
      (fun z x _ => Finset.mem_coe.2 (Finset.mem_univ _)) hc hD
      (by norm_num) hp hpρ hεpos hεb hκE le_rfl le_rfl hκa' hDA R0 hlt (by norm_num)
      (oldEnergyHatMatch_empty_of_spinIndependent S (hatQClass m₁) (fun _ _ _ _ _ _ => rfl) _ _ _)
  exact ⟨B, κdec, 2, εU, hB1, hB2, one_lt_two, hεpos⟩

/-- **Non-vacuity of the general theorem beyond the zero class.**  There is a step with `β > 0`
and a class whose old energy is not zero at any point of the fluctuation path, with a step
activity bound of rate `κ_H = 2 κ_dec - 1` and prefactor `ε_H = R_σ ε_U`, `R_σ > 1`, `ε_U > 0`,
obtained from `stepActivityBound_direct_of_oldEnergyHatMatch`. -/
theorem stepActivityBound_hatQClass_nonempty :
    ∃ (m₁ : ℕ) (β p₁ δ : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ β p₁ δ ∧ 0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      (∀ ψ : S.E, Edens (hatQClass m₁).m₀ (hatQClass m₁).Tm 1
        (composedPairAt S.a S.ν (Nat.le_succ 1) 1 (S.dataU ψ)).1
        (composedPairAt S.a S.ν (Nat.le_succ 1) 1 (S.dataU ψ)).2 ≠ 0) ∧
      ∃ B : StepActivityBound S (hatQClass m₁) 0,
        ∃ κdec Rσ εU : ℝ, B.κH = 2 * κdec - 1 ∧ B.εH = Rσ * εU ∧ 1 < Rσ ∧ 0 < εU := by
  obtain ⟨m₁, β, p₁, δ, hβ, hp, -, hR, hA⟩ := stepActivityBound_hatQClass_main
  exact ⟨m₁, β, p₁, δ, hatStep m₁ β p₁ δ, rfl, hβ, hp, hR,
    fun ψ => hatQClass_edens_ne_zero m₁ β p₁ δ ψ, hA⟩

end Balaban.Inhabited
