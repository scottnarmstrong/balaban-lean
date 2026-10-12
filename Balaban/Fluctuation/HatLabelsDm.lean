/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsExpansion
public import Balaban.Fluctuation.InteractionHatAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Label activities from Proposition 3.3 in the variable `ψ̂`, without the `dom`/`meas` hypotheses

`labelAct_of_interaction_expansion_hat` applies `labelAct_of_hatExpansion` to the witness of
`interaction_expansion_hat_dm`.  The two properties of the witness that the existential statement
of `interaction_expansion_hat` does not export are exported by the strengthened statement: the
labels are domains of `𝒟_{k+1}` (`dom`) and the diagonal terms `ψ̂ ↦ T_Y(ψ̂, ψ̂, σ, Θ)` are
continuous on the set of admissible `ψ̂`, hence measurable on the disk `|ψ̂| ≤ ρ` (`meas`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix Set Metric

section LabelActExpansion

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps : ℝ}

/-- **The label activities of the ψ̂-local expansion of Proposition 3.3** (Theorem 3.4 input).
Under the hypotheses of `interaction_expansion_hat`, a block structure of `ν_{p₁}` with `p₁ ≤ ρ`,
`|σ R₁| + r` small against the radius `cψ` of the hat ball, and the numerical hypotheses
(`κ₀ ≥ a_ent + 1`, `K_c ≥ K₀ + 1`, `a = 2 κ_dec - 1` large, `ε_U` small and a bound of the
coefficient of the expansion), there are `CubeLabels` and, for each `u`, a `LabelAct` of the block
variables of `ν_{p₁}`, holomorphic in `u` on `|u| < R_σ`, with the sum over the labels equal to the
expanded function at the hat variable, `ν_{p₁}`-almost surely, and with the numerics of Theorem 3.4.
No `dom` or `meas` hypothesis is assumed. -/
theorem labelAct_of_interaction_expansion_hat
    (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU κ0 κ' Kc' : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the hat variable
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    -- the potential part
    (ha₁ : 0 < a₁)
    (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
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
    (hZV : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ (k + 1))} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ (k + 1))} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N S.G' (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N S.G' (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup S.G' (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
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
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ (k + 1))} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ (k + 1))} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ (k + 1)) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N S.G' (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N S.G' (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup S.G' (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ (k + 1)) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ (k + 1) × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM)
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(X₁V z))
    (hRσ : 0 < Rσ) (hc : (Rσ * R₁ + r) * ρ < cψ)
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hΘ₀ : Θ₀ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
    (hN : L ^ m₀ ∣ N₁) (hL2 : 2 ≤ L) (hp : 0 < S.p₁) (hpρ : S.p₁ ≤ ρ)
    (hεpos : 0 < εU)
    (hεb : prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) ≤ εU)
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : (κ' + 3 * κ0 + c1 d L + 3 / 2 + c1 d L) * hatA d L ≤ 2 * κdec - 1)
    (hεU : εU ≤ hatEpsMax d L Rσ (2 * κdec - 1) κ0 κ' Kc') :
    ∃ (Lb : Type) (_ : Fintype Lb)
      (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ Lb)
      (A : ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb (hatEpsH d L Rσ εU (2 * κdec - 1))
        (hatKappaH d L (2 * κdec - 1)) κ0 Kc'),
      (∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) (Metric.ball 0 Rσ)) ∧
      (∀ u : ℂ, ‖u‖ < Rσ → ∀ᵐ x ∂S.nuFl, ∑ y, (A u).H y ((S.blockSplit m₀ hp).restr x) =
        (fun x w σ p =>
          (-cβ) * raySrc3 (hatFun S.G' a₁ ν eps S.hG' cc (interactionOne hG S.hG' le_rfl a₁ ν eps))
            taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc (flComp (hBE τ h) (hFE τ h) (EE τ)))
              (fun _ => (1 : ℂ)) x.1 w.1 σ p.1 else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
            dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc (onXi S.G' a₁ ν eps
              (fun D ψ' => svec Hm (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc
              (flComp (hBM τ h) (hFM τ h) (EM τ))) (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0) +
          cν * dirTermSrc (hatFun S.G' a₁ ν eps S.hG' cc (onXi S.G' a₁ ν eps
            (fun D ψ' => nuTotal S.G' Hm a₁ ν BG₂ κ D ψ'))) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1)
          (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u Θ₀) ∧
      (0 < hatEpsH d L Rσ εU (2 * κdec - 1) ∧
        κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ hatKappaH d L (2 * κdec - 1) ∧
        hatEpsH d L Rσ εU (2 * κdec - 1) ≤ 1 / (8 * Kc' ^ 3 * c1 d L *
          Real.exp ((hatKappaH d L (2 * κdec - 1) - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) := by
  have hR₁0 : 0 ≤ R₁ := by linarith
  obtain ⟨𝒴, T, hD⟩ := interaction_expansion_hat_dm (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) hC cβ hconn hrow (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 (R₁ := R₁) hR₁ (r := r) (Rσ := Rσ) hr hk hG S.hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsmX hδ₁ ha₁ H hc7 (R := R) hR hRs hsmall hnum hnum' hsm (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) hcovV hX₁V hoptV hΔV hlogV hZV hmarV (τι := τι) 𝒯E (ϱ₁ := ϱ₁) (ϱ₂ := ϱ₂) (GkE := GkE) (GjE := GjE) (r₀ := r₀) (δ₃ := δ₃) (δfl := δfl) (X₀E := X₀E) (X₁E := X₁E) (jE := jE) (XE := XE) (𝒦XE := 𝒦XE) (EbE := EbE) hBE hFE hcovE hX₁E hoptE hlogE hEbE (EE := EE) hEanE hEbdE (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) hcovF hX₁F hoptF hΔF hlogF hyF (μι := μι) 𝒯M (ϱ₁M := ϱ₁M) (ϱ₂M := ϱ₂M) (GkM := GkM) (GjM := GjM) (X₀M := X₀M) (X₁M := X₁M) (jM := jM) (XM := XM) (𝒦XM := 𝒦XM) (EbM := EbM) ys is hys hBM hFM hcovM hX₁M hoptM hlogM hEbM (EM := EM) hEanM hEbdM rE hrE (ρE := ρE) hρE0 hρE (ρM := ρM) hρM0 hρM (Bh := Bh) hBh0 hBh cν hZν
  refine labelAct_of_hatExpansion S m₀ hRσ hR₁0 hr.le hc 𝒴 T _ hD.loc hD.dom ?_ hΘ₀
    ?_ ?_ hN hL2 hp hpρ hεpos hκE hKc hκ' hκa hεU
  · intro Y _
    have hexp := (Real.exp_pos (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)).le
    calc _ = (prop33Eps d L N m₁ k m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ +
      ‖cν‖ * (1 * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r))) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hεb hexp
  · intro Y
    exact ⟨fun x _ => ⟨rfl, rfl⟩, fun x _ => rfl⟩
  · intro Y _ σ hσ
    have hρ : 0 < ρ := lt_of_lt_of_le hp hpρ
    have hcont := hD.cont Y ‹_› σ hσ Θ₀ hΘ₀
    refine (continuousOn_iff_continuous_domRestrict.1 (hcont.mono ?_)).measurable
    intro ψ hψ
    exact ⟨hatRaysO_pair S hψ hRσ.le hR₁0 hr.le hc, hatRaysO_pair S hψ hRσ.le hR₁0 hr.le hc⟩

end LabelActExpansion

end Balaban.Fluctuation
