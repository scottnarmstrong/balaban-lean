/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33Bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition 3.3: the bound `|𝒰(Y)| ≤ ε_U e^{-κ_U d^cov_{k+1}(Y)}` (non-(Vmod) part)

`interaction_expansion` (W106) expands the localized interaction `𝒰` over domains `Y` with the
bound by sums over all terms (blocks, old terms, sites) with the multiscale size `d̃^cov`; these sums
are not uniform in the volume.  `interaction_expansion_bound` keeps the label sets of the terms and
resums them (FLUCTUATION (3.5)):

* the generating set `Gp` has level `n + 1 = k + 1` (`IsLevel Gp (n + 1)`), so `d̃^cov(Y)` is the
  single-scale covering size `d^cov_{k+1}(Y)` of Definition 1.1 (`treeLenCov_eq_treeLenCovOne`);
* a block `B_{n+1}(z) ⊄ Y` does not contribute; the number of blocks in `Y` is at most
  `c₁ M^d (1 + d^cov_{k+1}(Y))` (G1), `M = L^{m₀ + m₁}`;
* an old term contributes to `Y` only if its root `rE τ` lies in `Y`; the bounds of the terms
  rooted at one site add up to `ρE` (the source bound of the old effective action, (3.2)), and
  `|Y| ≤ c₁ (L^{n+1} M)^d (1 + d^cov_{k+1}(Y))`;
* the source terms are linear in `g` with `‖g‖_{ℓ¹} < 1`: `LocInt.wsum`.

The factor `1 + d^cov` is absorbed by one unit of the rate, `e^{-2κ_dec d} (1 + d) ≤ e^{-(2κ_dec - 1) d}`:
`κ_U = 2 κ_dec - 1`, `ε_U = R_σ ‖c_β‖ ε` with `ε =` `prop33Eps`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Prop33

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ}

/-- **The amplitude `ε` of the bound**: the sum of the amplitudes of the potential part
(`3 c₁ M^d ‖E‖ / r³`, `E` the bound of a block energy), of the old terms (`ρE c₁ (L^{n+1} M)^d / r`),
of the source sites (`cK2' δ₁ / r`) and of the observable terms (`ρM / r`). -/
noncomputable def prop33Eps (d L N m₁ n m₀ : ℕ) (a₁ ν BG BG₂ κ δ₁ r ρE ρM : ℝ) : ℝ :=
  3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBd d L N (compWeight L a₁) ν n
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3 +
    ρE * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r +
    cK2' d L N (famConst d L BG₂ κ) * δ₁ / r + ρM / r

/-- **Proposition 3.3 (without the modular boundary part), with the bound of (3.4).**  The
localized interaction `𝒰_{t,u}(σ; ψ̂)` of (3.3) is `∑_Y 𝒰(Y)`, with the terms analytic, local, vanishing at
`σ = 0` and `|𝒰(Y)| ≤ |σ| ‖c_β‖ ε e^{-κ_U d^cov_{k+1}(Y)}`, `κ_U = 2 κ_dec - 1`,
`ε = prop33Eps ...`, `d^cov_{k+1}(Y) = treeLenCovOne m₀ (n + 1) Y` (Definition 1.1, whole torus).
Extra premises with respect to `interaction_expansion`: a common cover scale `m₀`, the roots and
the per-site sums `ρE`, `ρM` of the bounds of the old terms and of the observable terms. -/
theorem interaction_expansion_bound {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the potential part
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hZV : ∀ z, readSites Hm n z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ K)} {jE : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ K)} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jE τ)) E₀ = treeLenCovOne (m₀) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jE τ) (XE τ)))
    -- the sites of the source
    {jF : CTorus d L N₁ m₁ K × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ K × Fin N → Set (CTorus d L N₁ m₁ K)}
    {X₁F : CTorus d L N₁ m₁ K × Fin N → Finset (CTorus d L N₁ m₁ K)}
    (hcovF : ∀ s, CovSetup Gp (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ K × Fin N, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ K × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ K)} {jM : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ K)} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ K) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jM τ)) E₀ = treeLenCovOne (m₀) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀) (jM τ) (XM τ)))
    -- the sizes of the old terms and of the observable terms (the source bounds of (3.2)-(3.4)):
    -- the bounds of the terms rooted at one site (resp. at one source site) add up to `ρ`
    (rE : τι → CTorus d L N₁ m₁ K) (hrE : ∀ τ ∈ 𝒯E, rE τ ∈ X₁E τ) {ρE : ℝ} (hρE0 : 0 ≤ ρE)
    (hρE : ∀ x : CTorus d L N₁ m₁ K, ∑ τ ∈ 𝒯E.filter (fun τ => rE τ = x),
      EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) ≤ ρE)
    {ρM : ℝ} (hρM0 : 0 ≤ ρM)
    (hρM : ∀ p : CTorus d L N₁ m₁ K × Fin N, ∑ τ ∈ 𝒯M.filter (fun τ => (ys τ, is τ) = p),
      EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) ≤ ρM) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Set (CTorus d L N₁ m₁ K) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
            ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) |
          ((xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}) ∧
          (xw.1.1, xw.2.1) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} ∧
          (xw.1.2, xw.2.2) ∈ {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) ×
              (CTorus d L N₁ m₁ K → Fin N → ℂ) |
            (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
            IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2}} Rσ 𝒴 T
        (fun x w σ p =>
          (-cβ) * raySrc3 (interactionOne hG hG' hp a₁ ν eps) taylorWeight x.1 w.1 σ p.1 +
          cβ * (∑ τ ∈ 𝒯E, if h : τ ∈ 𝒯E then
            dirTermSrc (flComp (hBE τ h) (hFE τ h) (EE τ)) (fun _ => (1 : ℂ)) x.1 w.1 σ p.1
            else 0) +
          cβ * (∑ s : CTorus d L N₁ m₁ K × Fin N, p.2 s.1 s.2 * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1) +
          cβ * (∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
            p.2 (ys τ) (is τ) * dirTermSrc (flComp (hBM τ h) (hFM τ h) (EM τ))
              (fun _ => (1 : ℂ)) x.2 w.2 σ p.1 else 0))
        (fun Y => prop33Eps d L N m₁ n m₀ a₁ ν BG BG₂ κ δ₁ r ρE ρM * ‖cβ‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y)) (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => (∀ y ∈ psiThick Y, a.1 y = a'.1 y) ∧ (∀ y ∈ psiThick Y, a.2 y = a'.2 y)) := by
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hK2 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hr3 : 0 < r ^ 3 := by positivity
  have hM0 : 0 ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hP0 : 0 ≤ ((L : ℝ) ^ (n + 1)) ^ d := by positivity
  -- the potential part, with its labels
  obtain ⟨TV, hLV⟩ := vpart_locInt_dom (m₀ := fun _ => m₀) (j := jV) (X := XV) (𝒦X := 𝒦XV)
    (X₁f := X₁V) hC hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum' hreal hcovV hX₁V hconn hrow
    hoptV hΔV hκ₀ hκdec hκ h1 hlogV hn1 hZV hmarV continuous_taylorWeight hR₁
    (analyticOnNhd_taylorWeight _) (Mω := 1 / 2) (by norm_num)
    (fun t ht => norm_taylorWeight_le t ht) hr (Rσ := Rσ)
  have hbV : ∀ Y ∈ Finset.univ.biUnion
      (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)),
      (∑ z, if Y ∈ polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z) then
        (1 / 2 : ℝ) * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3) else 0) ≤
      (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := by
    intro Y hY
    obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
    have hMD := polyDom_isMultiDom (hcovV z₀) hd (hoptV z₀) hz₀
    have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁V z) m₀ (jV z)
        (𝒦XV z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
      refine card_blocks_filter_le hG' hp (hcovV z₀).hN hMD _ (fun z hz => ?_)
      have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
      rw [← hX₁V z] at h1'
      intro x hx
      exact h1' (hZV z ⟨x, Finset.mem_coe.1 hx, Or.inl rfl⟩)
    have ht0 := treeLenCov_nonneg Gp m₀ Y
    set Eb := ‖energyBd d L N (compWeight L a₁) ν n
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ with hEb
    have hv : 0 ≤ (1 / 2 : ℝ) * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3) := by positivity
    refine (sum_ite_card_le _ hv hcard).trans ?_
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, ← hEb,
      ← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
    have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
    have hCV : 0 ≤ 3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * Eb / r ^ 3 := by positivity
    calc c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          ((1 / 2 : ℝ) * (6 * (Eb * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r ^ 3))
        = (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * Eb / r ^ 3) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key hCV
  have hLV' := hLV.mono_on hbV
  -- the old terms
  have hexE : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ), τ ∈ 𝒯E →
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯E then
          dirTermSrc (flComp (hBE τ h) (hFE τ h) (EE τ)) (fun _ => (1 : ℂ)) x₀ w σ Θ else 0)
        (fun Y => 1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ)
          (XE τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
    intro τ
    by_cases hτ : τ ∈ 𝒯E
    · obtain ⟨Ev, hEv⟩ := eterm_locInt (hBE τ hτ) (hFE τ hτ) (hcovE τ hτ) (hX₁E τ hτ) hconn
        hrow (hoptE τ hτ) hκ₀ hκdec hκ h1 (hlogE τ hτ) (hEbE τ hτ) (hEanE τ hτ) (hEbdE τ hτ)
        (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const (Mω := 1) zero_le_one
        (fun t ht => by simp) hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose EvE hEvE using hexE
  have hLE := LocInt.finsum 𝒯E (fun τ hτ => hEvE τ hτ)
  have hbE : ∀ Y ∈ 𝒯E.biUnion (fun τ => polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)),
      (∑ τ ∈ 𝒯E, if Y ∈ polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ) then
        1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ)
          (XE τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r) else 0) ≤
      (ρE * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := by
    classical
    intro Y hY
    obtain ⟨τ₀, hτ₀, hz₀⟩ := Finset.mem_biUnion.1 hY
    have hMD := polyDom_isMultiDom (hcovE τ₀ hτ₀) hd (hoptE τ₀ hτ₀) hz₀
    have hnc := ncard_le_of_isMultiDom hG' (hcovE τ₀ hτ₀).hN hMD
    have ht0 := treeLenCov_nonneg Gp m₀ Y
    set w : τι → ℝ := fun τ => EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ) (XE τ)) with hw
    have hw0 : ∀ τ ∈ 𝒯E, 0 ≤ w τ := fun τ hτ => mul_nonneg (hEbE τ hτ) (Real.exp_pos _).le
    have hs := sum_roots_le 𝒯E w hw0 rE Y hρE
    have hq : 0 ≤ Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r := by positivity
    have e1 : ∀ τ ∈ 𝒯E, (if Y ∈ polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ) then
        1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jE τ)
          (XE τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r) else 0) ≤
        (if rE τ ∈ Y then w τ else 0) * (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
      intro τ hτ
      by_cases hYτ : Y ∈ polyDom Gp (X₁E τ) m₀ (jE τ) (𝒦XE τ)
      · have hin : rE τ ∈ Y := by
          have h1' := subset_polyDom hYτ
          rw [← hX₁E τ hτ] at h1'
          exact h1' (Finset.mem_coe.2 (hrE τ hτ))
        simp only [hYτ, hin, ite_true, hw, one_mul]
        refine le_of_eq ?_
        rw [sub_eq_add_neg, show -κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) +
          -(2 * κdec * treeLenCov Gp m₀ Y) = -κ₀ * treeLenCovOne m₀ (jE τ) (XE τ) +
          (-2 * κdec * treeLenCov Gp m₀ Y) by ring, Real.exp_add]
        ring
      · simp only [hYτ, ite_false]
        split_ifs
        · exact mul_nonneg (hw0 τ hτ) hq
        · simp
    calc _ ≤ ∑ τ ∈ 𝒯E, (if rE τ ∈ Y then w τ else 0) *
            (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := Finset.sum_le_sum e1
      _ = (∑ τ ∈ 𝒯E, (if rE τ ∈ Y then w τ else 0)) *
            (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by rw [Finset.sum_mul]
      _ ≤ (ρE * (c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
            (1 + treeLenCov Gp m₀ Y))) *
            (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
          refine mul_le_mul_of_nonneg_right (hs.trans ?_) hq
          exact mul_le_mul_of_nonneg_left hnc hρE0
      _ = (ρE * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
            ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
      _ ≤ _ := by
          rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
          exact mul_le_mul_of_nonneg_left (one_add_mul_exp_le _ κdec) (by positivity)
  have hLE' := hLE.mono_on hbE
  -- the sites of the source
  have hexF : ∀ s : CTorus d L N₁ m₁ K × Fin N, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))
          (fun _ => (1 : ℂ)) x₀ w σ Θ)
        (fun Y => 1 * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := fun s =>
    fsite_base_locInt hC (hcovF s) (hX₁F s) hconn hrow (hoptF s) (hΔF s) hκ₀ hκdec hκ h1
      (hlogF s) s.1 (hyF s) s.2 (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const
      (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  choose EvF hEvF using hexF
  have hLF := LocInt.wsum (Finset.univ : Finset (CTorus d L N₁ m₁ K × Fin N))
    (𝒴 := fun s => polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s)) (fun s _ => hEvF s)
    (SG := l1Ball d L N₁ m₁ K N) (amp := fun s g => g s.1 s.2)
    (fun s _ => (analyticOnNhd_coord s.1 s.2).mono (Set.subset_univ _))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ K → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (fun s _ Y hY g _ g' _ hag => by
      have h1' := subset_polyDom hY
      rw [← hX₁F s] at h1'
      exact congrFun (hag s.1 (h1' (Finset.mem_coe.2 (hyF s)))) s.2)
    (B := fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))
    (fun Y _ g hg => by
      have ht0 := treeLenCov_nonneg Gp m₀ Y
      rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
      set β := 1 * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r) with hβ
      have hβ0 : 0 ≤ β := by positivity
      have hβle : β ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y) := by
        rw [hβ, one_mul, mul_div_right_comm]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)
      have hsum : ∑ s : CTorus d L N₁ m₁ K × Fin N, ‖g s.1 s.2‖ ≤ 1 := by
        rw [Fintype.sum_prod_type]; exact le_of_lt hg
      calc ∑ s : CTorus d L N₁ m₁ K × Fin N, (if Y ∈ polyDom Gp (X₁F s) m₀ (jF s) (𝒦XF s) then
            ‖g s.1 s.2‖ * β else 0) ≤ ∑ s : CTorus d L N₁ m₁ K × Fin N, ‖g s.1 s.2‖ * β :=
            Finset.sum_le_sum fun s _ => by
              split_ifs
              · exact le_rfl
              · exact mul_nonneg (norm_nonneg _) hβ0
        _ = (∑ s : CTorus d L N₁ m₁ K × Fin N, ‖g s.1 s.2‖) * β := by rw [Finset.sum_mul]
        _ ≤ 1 * β := mul_le_mul_of_nonneg_right hsum hβ0
        _ ≤ _ := by rw [one_mul]; exact hβle)
  -- the observable terms
  have hexM : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ), τ ∈ 𝒯M →
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯M then
          dirTermSrc (flComp (hBM τ h) (hFM τ h) (EM τ)) (fun _ => (1 : ℂ)) x₀ w σ Θ else 0)
        (fun Y => 1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ)
          (XM τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
    intro τ
    by_cases hτ : τ ∈ 𝒯M
    · obtain ⟨Ev, hEv⟩ := eterm_locInt (hBM τ hτ) (hFM τ hτ) (hcovM τ hτ) (hX₁M τ hτ) hconn
        hrow (hoptM τ hτ) hκ₀ hκdec hκ h1 (hlogM τ hτ) (hEbM τ hτ) (hEanM τ hτ) (hEbdM τ hτ)
        (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const (Mω := 1) zero_le_one
        (fun t ht => by simp) hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose EvM hEvM using hexM
  have hLM := LocInt.wsum 𝒯M (𝒴 := fun τ => polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ))
    (fun τ hτ => hEvM τ hτ) (SG := l1Ball d L N₁ m₁ K N) (amp := fun τ g => g (ys τ) (is τ))
    (fun τ _ => (analyticOnNhd_coord (ys τ) (is τ)).mono (Set.subset_univ _))
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ K → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    (fun τ hτ Y hY g _ g' _ hag => by
      have h1' := subset_polyDom hY
      rw [← hX₁M τ hτ] at h1'
      exact congrFun (hag (ys τ) (h1' (Finset.mem_coe.2 (hys τ hτ)))) (is τ))
    (B := fun Y => (ρM / r) * Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))
    (fun Y _ g hg => by
      classical
      have ht0 := treeLenCov_nonneg Gp m₀ Y
      rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
      set w : μι → ℝ := fun τ => EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ) (XM τ)) with hw
      have hw0 : ∀ τ ∈ 𝒯M, 0 ≤ w τ := fun τ hτ => mul_nonneg (hEbM τ hτ) (Real.exp_pos _).le
      have hq : 0 ≤ Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r := by positivity
      have hws := sum_weighted_le 𝒯M w (fun τ => (ys τ, is τ))
        (fun p : CTorus d L N₁ m₁ K × Fin N => ‖g p.1 p.2‖) (fun p => norm_nonneg _)
        (by rw [Fintype.sum_prod_type]; exact le_of_lt hg) hρM0 hρM
      calc ∑ τ ∈ 𝒯M, (if Y ∈ polyDom Gp (X₁M τ) m₀ (jM τ) (𝒦XM τ) then
            ‖g (ys τ) (is τ)‖ * (1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jM τ)
              (XM τ) - 2 * κdec * treeLenCov Gp m₀ Y)) / r)) else 0)
          ≤ ∑ τ ∈ 𝒯M, (‖g (ys τ) (is τ)‖ * w τ) *
              (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by
            refine Finset.sum_le_sum fun τ hτ => ?_
            split_ifs
            · refine le_of_eq ?_
              simp only [hw, one_mul]
              rw [sub_eq_add_neg, show -κ₀ * treeLenCovOne m₀ (jM τ) (XM τ) +
                -(2 * κdec * treeLenCov Gp m₀ Y) = -κ₀ * treeLenCovOne m₀ (jM τ) (XM τ) +
                (-2 * κdec * treeLenCov Gp m₀ Y) by ring, Real.exp_add]
              ring
            · exact mul_nonneg (mul_nonneg (norm_nonneg _) (hw0 τ hτ)) hq
        _ = (∑ τ ∈ 𝒯M, ‖g (ys τ) (is τ)‖ * w τ) *
              (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) := by rw [Finset.sum_mul]
        _ ≤ ρM * (Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / r) :=
            mul_le_mul_of_nonneg_right hws hq
        _ ≤ ρM * (Real.exp (-(2 * κdec - 1) * treeLenCov Gp m₀ Y) / r) := by
            refine mul_le_mul_of_nonneg_left ?_ hρM0
            exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) hr.le
        _ = _ := by ring)
  have hLM' := hLM.congr_val (val' := fun x w σ p => ∑ τ ∈ 𝒯M, if h : τ ∈ 𝒯M then
      p.2 (ys τ) (is τ) * dirTermSrc (flComp (hBM τ h) (hFM τ h) (EM τ))
        (fun _ => (1 : ℂ)) x w σ p.1 else 0)
    (fun xw _ σ _ p _ => Finset.sum_congr rfl fun τ hτ => by simp [hτ])
  -- assemble
  have hnV : ∀ Y : Set (CTorus d L N₁ m₁ K), 0 ≤ (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := fun Y => by positivity
  have hnE : ∀ Y : Set (CTorus d L N₁ m₁ K), 0 ≤ (ρE * c1 d L * ((L : ℝ) ^ (n + 1)) ^ d * ((L : ℝ) ^ (m₀ + m₁)) ^ d / r) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := fun Y => by positivity
  have hnF : ∀ Y : Set (CTorus d L N₁ m₁ K), 0 ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁ / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := fun Y => by positivity
  have hnM : ∀ Y : Set (CTorus d L N₁ m₁ K), 0 ≤ (ρM / r) *
      Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y) := fun Y => by positivity
  obtain ⟨𝒴, T, b, hb, hL⟩ := locInt_assemble
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ K → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    hLV' hLE' hLF hLM' (-cβ) cβ cβ cβ hnV hnE hnF hnM
  refine ⟨𝒴, T, (hL.mono_XW fun xw h => ⟨h.1, h.1, h.2.2.1, h.2.2.2⟩).mono
    fun Y => (hb Y).trans (le_of_eq ?_)⟩
  simp only [norm_neg, prop33Eps]
  ring

end Prop33

end Balaban.Localization
