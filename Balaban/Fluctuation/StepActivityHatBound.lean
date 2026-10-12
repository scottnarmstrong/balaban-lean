/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHat
public import Balaban.Fluctuation.StepNonvanishBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The step activity bound of the zero class from the hat expansion

`stepActivityBound_zeroClass_of_hatExpansion` builds `StepActivityBound S (zeroClass …) 0` whose
activities are the label activities of `labelAct_of_interaction_expansion_hat` (the `ψ̂`-local
expansion of Proposition 3.3, `u = s`), rescaled by the Taylor factor `s²`
(`StepSetting.Wone_zeroClass_eq_hat`): on the first segment `(s, 0)`, the exponent is
`W₁(s, ψ̂) = s² · val(s)`, so `A (s, 0) = s² · A_hat(s)`; on the second segment `(1, t)` the exponent
is `W₁(1, ψ̂) + W₂(t, ψ̂; 0) = val(1)`, since `W₂ = 0` for the source `0`.

Real data: the landed step is the physical object at a real block datum; the statements use the
real chart block `RayData` of `StepRegBg`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Scale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
variable {Lb : Type*} [Fintype Lb] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}

/-- A label activity multiplied by a complex constant of norm at most `1` is a label activity with
the same bounds. -/
noncomputable def LabelAct.cscale
    {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (A : LabelAct Lab Ωb εH κH κ0 Kc) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    LabelAct Lab Ωb εH κH κ0 Kc where
  H y Φ := c * A.H y Φ
  meas y := (A.meas y).const_mul c
  dep y Φ Φ' h := by simp only [A.dep y Φ Φ' h]
  bound y Φ := by
    rw [norm_mul]
    calc ‖c‖ * ‖A.H y Φ‖ ≤ 1 * (εH * Real.exp (-κH * Lab.dl y)) :=
          mul_le_mul hc (A.bound y Φ) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  entropy := A.entropy

end Scale

/-- The rescaling constant of the first segment has norm at most `1`. -/
theorem norm_ite_sq_le (s : ℝ) :
    ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 := by
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg s)]
    nlinarith [h.1, h.2]
  · simp

theorem norm_ofReal_lt_of_mem {s Rσ : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hRσ1 : 1 < Rσ) :
    ‖(s : ℂ)‖ < Rσ := by
  rw [Complex.norm_real, Real.norm_of_nonneg hs.1]; linarith [hs.2]

theorem p₁_lt_of_margin {p₁ ρ Rσ R₁ r cψ : ℝ} (hp : 0 < p₁) (hpρ : p₁ ≤ ρ) (hRσ1 : 1 < Rσ)
    (hR₁ : 1 < R₁) (hr : 0 < r) (hc : (Rσ * R₁ + r) * ρ < cψ) : p₁ < cψ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hp hpρ
  have h1' : 1 ≤ Rσ * R₁ := by nlinarith
  calc p₁ ≤ ρ := hpρ
    _ ≤ (Rσ * R₁ + r) * ρ := by nlinarith
    _ < cψ := hc

section Main

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {c BG κ eps : ℝ}

/-- **T2: the step activity bound of the zero class from the `ψ̂`-local expansion of
Proposition 3.3.**  At a real block datum (`R0 : RayData`, the landed step) with `D'` in
`Ξ^c(𝔹_{k+1}; 1, ε)`, for the zero class (no old energy or observable term: `𝒯E = 𝒯M = ∅`) and
the source `0`, the activities of `labelAct_of_interaction_expansion_hat` at the parameter
`u = s` (rescaled by `s²`) give `StepActivityBound S (zeroClass …) 0`: for `(s, 0)` the exponent
`W₁(s, ψ̂)` is `s² · val(s)` (T1) and for `(1, t)` it is `val(1)`.  The hypotheses are those of
`labelAct_of_interaction_expansion_hat` (with `c_β = β`, `c_ν = 0`, `cc = β_k^{-1/2}`, the old
spin generating set `stepG` and the weights of `S`) and `Rσ > 1`. -/
theorem stepActivityBound_zeroClass_of_hatExpansion
    (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU κ0 κ' Kc' : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    (hk : 1 ≤ k) (hG : IsLevel (stepG d L N₁ m₁ k ϱ) k)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ * (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
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
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites (stepG d L N₁ m₁ k ϱ) k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jE τ) (𝒦XE τ))
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
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jM τ) (𝒦XM τ))
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
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z))
    (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
    (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    (hN : L ^ m₀ ∣ N₁) (hL2 : 2 ≤ L) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU)
    (hεb : prop33Eps d L N m₁ k m₀ S.a₁ S.ν BG BG₂ κ δ₁ r ρE ρM * ‖(S.β : ℂ)‖ +
      ‖(0 : ℂ)‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : (κ' + 3 * κ0 + c1 d L + 3 / 2 + c1 d L) * hatA d L ≤ 2 * κdec - 1)
    (hεU : εU ≤ hatEpsMax d L Rσ (2 * κdec - 1) κ0 κ' Kc')
    {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp)
    (hbase : InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC2 d L N) S.ν
      (S.dataU S.psi0))
    (hRσ1 : 1 < Rσ) (h𝒯E : 𝒯E = ∅) (h𝒯M : 𝒯M = ∅) :
    Nonempty (StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) 0) := by
  classical
  subst h𝒯E h𝒯M
  have hpc : S.p₁ < cψ := p₁_lt_of_margin hp hpρ hRσ1 hR₁ hr hc
  obtain ⟨Lb, hLb, Lab, Ahat, hdiff, hid, hnum⟩ := labelAct_of_interaction_expansion_hat
    (Θ₀ := (rawOf S.D', (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) S hC (S.β : ℂ) hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hk hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV hX₁V hoptV hΔV hlogV hZV hmarV _ hBE hFE hcovE hX₁E hoptE hlogE hEbE hEanE hEbdE hcovF hX₁F hoptF hΔF hlogF hyF _ ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM hEanM hEbdM rE hrE hρE0 hρE hρM0 hρM hBh0 hBh (0 : ℂ) hZν hRσ hc ⟨⟨S.D', hD, rfl⟩, by simp [l1Ball]⟩ hN hL2 hp hpρ hεpos hεb hκE hKc hκ' hκa hεU
  have hcfun : ∀ s : ℝ, ‖((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)‖ ≤ 1 :=
    norm_ite_sq_le
  have key : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      S.Wone (zeroClass d L N₁ m₁ k N ϱ) s x = ∑ y, ((Ahat (s : ℂ)).cscale
        ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ) (hcfun s)).H y
          ((S.blockSplit m₀ hp).restr x) := by
    intro s hs
    have hu : ‖(s : ℂ)‖ < Rσ := norm_ofReal_lt_of_mem hs hRσ1
    filter_upwards [hid (s : ℂ) hu, S.ae_ball hp] with x hx hχ
    have hT1 := S.Wone_zeroClass_eq_hat hC R0 hlt hbase hD hc7 (lt_of_lt_of_le one_lt_two hR) hsm
      hMX hdm hα hsmX hp hcψ hpc hδ₁ hs hχ
    simp only [LabelAct.cscale, hs, ↓reduceIte]
    rw [← Finset.mul_sum, hx, ← hT1]
    simp only [Finset.sum_empty, mul_zero, zero_mul, Pi.zero_apply, Finset.sum_const_zero,
      add_zero]
    push_cast
    rfl
  refine ⟨{
    m₀ := m₀
    hN := hN
    BS := S.blockSplit m₀ hp
    Lb := Lb
    Lab := Lab
    εH := hatEpsH d L Rσ εU (2 * κdec - 1)
    κH := hatKappaH d L (2 * κdec - 1)
    κ0 := κ0
    κ' := κ'
    Kc := Kc'
    A := fun p => (Ahat (p.1 : ℂ)).cscale
      ((if p.1 ∈ Icc (0 : ℝ) 1 then p.1 ^ 2 else 0 : ℝ) : ℂ) (hcfun p.1)
    hκ0 := hκE
    hKc := hKc
    hεpos := hnum.1
    hκ' := hκ'
    hκ := hnum.2.1
    hε := hnum.2.2
    hW := ?_ }⟩
  intro p hpS
  have hs : p.1 ∈ Icc (0 : ℝ) 1 := by
    rcases hpS with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · rw [h1]; exact ⟨zero_le_one, le_rfl⟩
  filter_upwards [key p.1 hs] with x hx
  rw [Wtwo_zero_class, add_zero]
  exact hx

end Main

end Balaban.Fluctuation
