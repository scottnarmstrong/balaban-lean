/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionVPart
public import Balaban.Fluctuation.InteractionMPart
public import Balaban.Fluctuation.InteractionAssemble
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Proposition 3.3: the localized interaction (FLUCTUATION §3.3; P6 Lemmas 4.1-4.2, (4.32)-(4.34))

Without the modular boundary part (which needs the open (Vmod)): the potential part (the interaction
potential `V^{(k)}` pre-localized per block with the decoupled solution of I-4a in mode P, Lemma AE,
GM3/GM4), the `δ𝓔'`-part (the old effective action along the fluctuation, via I-5 with `ψ'`) and the
`δ𝓕'`-part (the source: `⟨g, δφ⟩` and the observable terms).

`localizedInteraction` is the sum, with the prefactor `c_β = β_k^{-1/2}` of (3.3),

`𝒰_{t,u}(σ; ψ̂) = - c_β σ ∫₀¹ (1-t')²/2 V'''(σ t' x_t)[w_t]³ dt' + c_β σ ∫₀¹ ⟨δ𝓔'(σ t' x_t), w_t⟩ dt'
  + c_β σ ∫₀¹ ⟨δ𝓕'(σ t' x_u, g), w_u⟩ dt'`

with `(x_t, w_t) = (ψ'(tψ̂), C^{1/2} t ψ̂)`, `(x_u, w_u)` the same for `u`.  `interaction_expansion`
proves that it is `∑_Y 𝒰(Y; σ, ψ̂)` over the domains `Y ⊃ X₁` of the polymer expansion, with the
terms analytic in the data `(θ, h)`, the source `g` and `σ`, local, vanishing at `σ = 0`, and
bounded by the explicit sums of the term bounds.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Interaction

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ}

/-- The weight `(1 - t')²/2` of the Taylor formula in (3.3). -/
noncomputable def taylorWeight (t : ℂ) : ℂ := (1 - t) ^ 2 / 2

theorem continuous_taylorWeight : Continuous taylorWeight := by
  unfold taylorWeight; fun_prop

theorem analyticOnNhd_taylorWeight (s : Set ℂ) : AnalyticOnNhd ℂ taylorWeight s := by
  intro t _
  unfold taylorWeight
  fun_prop

theorem norm_taylorWeight_le (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖taylorWeight (t : ℂ)‖ ≤ 1 / 2 := by
  unfold taylorWeight
  have h0 : 0 ≤ 1 - t := by linarith [ht.2]
  have h1 : 1 - t ≤ 1 := by linarith [ht.1]
  have : ((1 - (t : ℂ)) ^ 2 / 2) = (((1 - t) ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  nlinarith

theorem norm_one_le (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) : ‖(fun _ : ℂ => (1 : ℂ)) (t : ℂ)‖ ≤ 1 := by
  simp

/-- **Proposition 3.3 (without the modular boundary part): the localized interaction.**

* the potential part: the blocks `z` of `B_{n+1}`, with the covers `(m₀V z, jV z, XV z, 𝒦XV z, X₁V z)`;
* the `δ𝓔'`-part: the old terms `τ ∈ 𝒯E` along the fluctuation (hypotheses of `i5_fluct` for each);
* the source part: the sites `(y, i)` of `⟨g, δφ⟩` (covers `F`) and the observable terms `τ ∈ 𝒯M`.

`𝒰(σ; ψ̂)` is analytic in `(θ, h, g, σ)` on `Ξ^c × {‖g‖_{ℓ¹} < 1} × {|σ| < R_σ}`, vanishes at `σ = 0`,
and is `∑_Y 𝒰(Y)` with `𝒰(Y)` depending on `(θ, h, g, x, w)` only through their restriction to the
thickening of `Y`, bounded by `|σ|` times `‖c_β‖` times the sum of the term bounds. -/
theorem interaction_expansion {Kc Cx c₂ BG₂ δ₁ : ℝ}
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
    {m₀V jV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcovV : ∀ z, CovSetup Gp (m₀V z) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀V z) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀V z) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀V z) m₁ (jV z)) E₀ = treeLenCovOne (m₀V z) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀V z) (jV z) (XV z) = 0)
    (hlogV : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀V z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hZV : ∀ z, readSites Hm n z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    -- the old terms
    {τι : Type*} [DecidableEq τι] (𝒯E : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂ τ)} {r₀ δ₃ δfl : ℝ}
    {X₀E X₁E : τι → Finset (CTorus d L N₁ m₁ K)} {jE m₀E : τι → ℕ}
    {XE 𝒦XE : τι → Set (CTorus d L N₁ m₁ K)} {EbE : τι → ℝ}
    (hBE : ∀ τ ∈ 𝒯E, BgSetting N Gp (GkE τ) (GjE τ) a₁ ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E, FlSetting N Gp (GkE τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁E τ))
    (hcovE : ∀ τ ∈ 𝒯E, CovSetup Gp (m₀E τ) (jE τ) (XE τ) (𝒦XE τ))
    (hX₁E : ∀ τ ∈ 𝒯E, (↑(X₁E τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀E τ) (jE τ) (𝒦XE τ))
    (hoptE : ∀ τ ∈ 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XE τ) ∧ MeetsOne (m₀E τ) (jE τ) (𝒦XE τ) W₀ ∧
        bondCost (scaleW L (m₀E τ) m₁ (jE τ)) E₀ = treeLenCovOne (m₀E τ) (jE τ) (XE τ))
    (hlogE : ∀ τ ∈ 𝒯E, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀E τ) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbE : ∀ τ ∈ 𝒯E, 0 ≤ EbE τ) {EE : τι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanE : ∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ (EE τ) (XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdE : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (GjE τ) (compWeight L a₁) ν (jE τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EE τ r‖ ≤ EbE τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀E τ) (jE τ) (XE τ)))
    -- the sites of the source
    {m₀F jF : CTorus d L N₁ m₁ K × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ K × Fin N → Set (CTorus d L N₁ m₁ K)}
    {X₁F : CTorus d L N₁ m₁ K × Fin N → Finset (CTorus d L N₁ m₁ K)}
    (hcovF : ∀ s, CovSetup Gp (m₀F s) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀F s) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀F s) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀F s) m₁ (jF s)) E₀ = treeLenCovOne (m₀F s) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀F s) (jF s) (XF s) = 0)
    (hlogF : ∀ s, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀F s) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ K × Fin N, s.1 ∈ X₁F s)
    -- the observable terms
    {μι : Type*} [DecidableEq μι] (𝒯M : Finset μι) {ϱ₁M ϱ₂M : μι → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁M τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂M τ)}
    {X₀M X₁M : μι → Finset (CTorus d L N₁ m₁ K)} {jM m₀M : μι → ℕ}
    {XM 𝒦XM : μι → Set (CTorus d L N₁ m₁ K)} {EbM : μι → ℝ}
    (ys : μι → CTorus d L N₁ m₁ K) (is : μι → Fin N) (hys : ∀ τ ∈ 𝒯M, ys τ ∈ X₁M τ)
    (hBM : ∀ τ ∈ 𝒯M, BgSetting N Gp (GkM τ) (GjM τ) a₁ ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M, FlSetting N Gp (GkM τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁M τ))
    (hcovM : ∀ τ ∈ 𝒯M, CovSetup Gp (m₀M τ) (jM τ) (XM τ) (𝒦XM τ))
    (hX₁M : ∀ τ ∈ 𝒯M, (↑(X₁M τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀M τ) (jM τ) (𝒦XM τ))
    (hoptM : ∀ τ ∈ 𝒯M, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XM τ) ∧ MeetsOne (m₀M τ) (jM τ) (𝒦XM τ) W₀ ∧
        bondCost (scaleW L (m₀M τ) m₁ (jM τ)) E₀ = treeLenCovOne (m₀M τ) (jM τ) (XM τ))
    (hlogM : ∀ τ ∈ 𝒯M, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) *
      (((L ^ m₀M τ) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEbM : ∀ τ ∈ 𝒯M, 0 ≤ EbM τ) {EM : μι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEanM : ∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ (EM τ) (XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ)
      (scaledC0 d) (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbdM : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (GjM τ) (compWeight L a₁) ν (jM τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖EM τ r‖ ≤ EbM τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀M τ) (jM τ) (XM τ))) :
    ∃ (𝒴 : Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Set (CTorus d L N₁ m₁ K) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) →
        ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ)) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ)
      (b : Set (CTorus d L N₁ m₁ K) → ℝ),
      (∀ Y, b Y ≤ ‖cβ‖ * (
        (∑ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), (1 / 2) * (6 * ‖energyBd d L N
          (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀V z) Y)‖ / r ^ 3)) +
        (∑ τ ∈ 𝒯E, (1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne (m₀E τ) (jE τ) (XE τ)
          - 2 * κdec * treeLenCov Gp (m₀E τ) Y)) / r))) +
        (∑ s : CTorus d L N₁ m₁ K × Fin N, 1 * (1 * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀F s) Y)) / r))) +
        (∑ τ ∈ 𝒯M, 1 * (1 * ((EbM τ * Real.exp (-κ₀ * treeLenCovOne (m₀M τ) (jM τ) (XM τ)
          - 2 * κdec * treeLenCov Gp (m₀M τ) Y)) / r))))) ∧
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
            ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
              (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁}} Rσ 𝒴 T
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
        b (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y a a' => (∀ y ∈ psiThick Y, a.1 y = a'.1 y) ∧ (∀ y ∈ psiThick Y, a.2 y = a'.2 y)) := by
  classical
  obtain ⟨𝒴V, TV, hLV⟩ := vpart_locInt hC hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum' hreal
    hcovV hX₁V hconn hrow hoptV hΔV hκ₀ hκdec hκ h1 hlogV hn1 hZV hmarV continuous_taylorWeight
    hR₁ (analyticOnNhd_taylorWeight _) (Mω := 1 / 2) (by norm_num)
    (fun t ht => norm_taylorWeight_le t ht) hr (Rσ := Rσ)
  obtain ⟨𝒴E, TE, hLE⟩ := eterms_locInt 𝒯E hBE hFE hcovE hX₁E hconn hrow hoptE hκ₀ hκdec hκ h1
    hlogE hEbE hEanE hEbdE (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const
    (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  obtain ⟨𝒴F, TF, hLF⟩ := fsites_locInt hC hcovF hX₁F hconn hrow hoptF hΔF hκ₀ hκdec hκ h1 hlogF
    hyF (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const (Mω := 1) zero_le_one
    (fun t ht => by simp) hr (Rσ := Rσ)
  obtain ⟨𝒴M, TM, hLM⟩ := mterms_locInt 𝒯M ys is hys hBM hFM hcovM hX₁M hconn hrow hoptM hκ₀
    hκdec hκ h1 hlogM hEbM hEanM hEbdM (ω := fun _ => (1 : ℂ)) continuous_const hR₁
    analyticOnNhd_const (Mω := 1) zero_le_one (fun t ht => by simp) hr (Rσ := Rσ)
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hKc : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hbV : ∀ Y, 0 ≤ ∑ z, if Y ∈ 𝒴V z then (1 / 2 : ℝ) * (6 * ‖energyBd d L N (compWeight L a₁) ν n
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
      Real.exp (-2 * κdec * treeLenCov Gp (m₀V z) Y)‖ / r ^ 3) else 0 :=
    fun Y => Finset.sum_nonneg fun z _ => by split_ifs <;> positivity
  have hbE : ∀ Y, 0 ≤ ∑ τ ∈ 𝒯E, if Y ∈ 𝒴E τ then 1 * ((EbE τ * Real.exp (-κ₀ * treeLenCovOne
      (m₀E τ) (jE τ) (XE τ) - 2 * κdec * treeLenCov Gp (m₀E τ) Y)) / r) else 0 :=
    fun Y => Finset.sum_nonneg fun τ hτ => by
      split_ifs
      · exact mul_nonneg zero_le_one (div_nonneg (mul_nonneg (hEbE τ hτ) (Real.exp_pos _).le) hr.le)
      · exact le_rfl
  have hbF : ∀ Y, 0 ≤ ∑ s : CTorus d L N₁ m₁ K × Fin N, if Y ∈ 𝒴F s then 1 * (1 * (((cK2' d L N
      (famConst d L BG₂ κ) * δ₁) * Real.exp (-2 * κdec * treeLenCov Gp (m₀F s) Y)) / r)) else 0 :=
    fun Y => Finset.sum_nonneg fun s _ => by
      split_ifs
      · exact mul_nonneg zero_le_one (mul_nonneg zero_le_one (div_nonneg (mul_nonneg hKc
          (Real.exp_pos _).le) hr.le))
      · exact le_rfl
  have hbM : ∀ Y, 0 ≤ ∑ τ ∈ 𝒯M, if Y ∈ 𝒴M τ then 1 * (1 * ((EbM τ * Real.exp (-κ₀ *
      treeLenCovOne (m₀M τ) (jM τ) (XM τ) - 2 * κdec * treeLenCov Gp (m₀M τ) Y)) / r)) else 0 :=
    fun Y => Finset.sum_nonneg fun τ hτ => by
      split_ifs
      · exact mul_nonneg zero_le_one (mul_nonneg zero_le_one (div_nonneg (mul_nonneg (hEbM τ hτ)
          (Real.exp_pos _).le) hr.le))
      · exact le_rfl
  obtain ⟨𝒴, T, b, hb, hL⟩ := locInt_assemble
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgG := fun Y (g g' : CTorus d L N₁ m₁ K → Fin N → ℂ) => ∀ x ∈ Y, g x = g' x)
    hLV hLE hLF hLM (-cβ) cβ cβ cβ hbV hbE hbF hbM
  refine ⟨𝒴, T, b, fun Y => ?_, hL⟩
  refine (hb Y).trans ?_
  simp only [norm_neg]
  have hle : ∀ (P : Prop) [Decidable P] (u : ℝ), 0 ≤ u → (if P then u else 0) ≤ u := by
    intro P _ u hu; split_ifs <;> linarith
  have eV := Finset.sum_le_sum (s := (Finset.univ : Finset (Torus d (N₁ * L ^ m₁ *
      L ^ (K - (n + 1)))))) (fun z _ => hle (Y ∈ 𝒴V z) ((1 / 2 : ℝ) * (6 * ‖energyBd d L N
      (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
      Real.exp (-2 * κdec * treeLenCov Gp (m₀V z) Y)‖ / r ^ 3)) (by positivity))
  have eE := Finset.sum_le_sum (s := 𝒯E) (fun τ hτ => hle (Y ∈ 𝒴E τ) (1 * ((EbE τ *
      Real.exp (-κ₀ * treeLenCovOne (m₀E τ) (jE τ) (XE τ) - 2 * κdec *
        treeLenCov Gp (m₀E τ) Y)) / r))
      (mul_nonneg zero_le_one (div_nonneg (mul_nonneg (hEbE τ hτ) (Real.exp_pos _).le) hr.le)))
  have eF := Finset.sum_le_sum (s := (Finset.univ : Finset (CTorus d L N₁ m₁ K × Fin N)))
    (fun s _ => hle (Y ∈ 𝒴F s) (1 * (1 * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
      Real.exp (-2 * κdec * treeLenCov Gp (m₀F s) Y)) / r)))
      (mul_nonneg zero_le_one (mul_nonneg zero_le_one (div_nonneg (mul_nonneg hKc
        (Real.exp_pos _).le) hr.le))))
  have eM := Finset.sum_le_sum (s := 𝒯M) (fun τ hτ => hle (Y ∈ 𝒴M τ) (1 * (1 * ((EbM τ *
      Real.exp (-κ₀ * treeLenCovOne (m₀M τ) (jM τ) (XM τ) - 2 * κdec *
        treeLenCov Gp (m₀M τ) Y)) / r)))
      (mul_nonneg zero_le_one (mul_nonneg zero_le_one (div_nonneg (mul_nonneg (hEbM τ hτ)
        (Real.exp_pos _).le) hr.le))))
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add eV eE) eF) eM)
    (norm_nonneg cβ)
  linarith

end Interaction

end Balaban.Localization
