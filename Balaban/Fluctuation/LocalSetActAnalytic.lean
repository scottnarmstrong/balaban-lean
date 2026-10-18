/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalHatTerm
public import Balaban.Fluctuation.InteractionVBlock

/-!
# The block energy with the local hat variable: analyticity and bound on a generating set

P6 Lemma 4.1 (analyticity and bounds of the localized terms on a modified generating set) for the
zero-source part of the activities: the integrand of the zero-source term is the block energy
`blockEnergyFun 𝔹 H⁻ … n z` at the decoupled background `F₁(σ w, Θ)` of the cover of `𝔹`, the
fluctuation field `Sol(σ w, …)` of `H⁻` and the local hat lift `ψ' = cc C^{1/2}(σ w) ψ̂` of the
cover of `𝔹` (`coef_blockEnergyFun_replacement_localB_hat`).  For an arbitrary generating set `𝔹`
with a cover base (no `IsLevel`, no `DGSetting`; the local generating set `localB (k + 1) … Y` with
`localB_coverData` qualifies):

* `fanLocalHat_blockEnergy_analytic_cover`: the composite is analytic in `((Θ, ψ̂), w)` on the
  chart `Ξ^c(𝔹; 1, ε)` times the ball `|ψ̂| ≤ c_ψ` times the polydisc (`fanLocalHat_analytic_cover`
  with the block energy, which is analytic everywhere, `blockEnergyFun_analytic`);
* `fanLocalHat_blockEnergy_norm_le_cover`: it is bounded there by the block-energy bound `energyBd`
  (`fanLocalHat_norm_le_cover` with `blockEnergyFun_bound_of_num`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Finset Matrix

section FanHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*} [Fintype ι]

/-- **Analyticity of the block energy with the local hat variable** (P6 Lemma 4.1 (AE1) on `𝔹`,
cover form).  The block energy of `B_{n+1}(z)` at the decoupled background of the cover of `𝔹`, the
fluctuation field of `H⁻` and the local hat lift `ψ' = cc C^{1/2}(σ w) ψ̂`, for an analytic
parameter map `σ` from the polydisc of radius `e^κ` equal to `1` on the cubes meeting `X₁`, is
analytic in `((Θ, ψ̂), w)` on the chart `Ξ^c(𝔹; 1, ε)` times the ball `|ψ̂| ≤ c_ψ` times the
polydisc. -/
theorem fanLocalHat_blockEnergy_analytic_cover (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1)))) :
    AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
        (ι → ℂ) =>
      blockEnergyFun Gp Hm (compWeight L a₁) ν n z (F₁ (σ p.2, p.1.1))
        (Sol (σ p.2, flEdat Gp Hm (F₁ (σ p.2, p.1.1)) p.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) :=
  fanLocalHat_analytic_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm
    cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1
    ((blockEnergyFun_analytic (compWeight L a₁) ν n z).mono (Set.subset_univ _))

omit [Fintype ι] in
/-- **The bound of the block energy with the local hat variable** (P6 Lemma 4.1 on `𝔹`, cover
form): on the chart `Ξ^c(𝔹; 1, ε)` times the ball `|ψ̂| ≤ c_ψ` times the polydisc, the composite of
`fanLocalHat_blockEnergy_analytic_cover` is bounded by the block-energy bound
`energyBd … n (K₂' δ₁) δ₁ ρ₄` (`1 ≤ n`, `n + 1 ≤ k + 1`). -/
theorem fanLocalHat_blockEnergy_norm_le_cover (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    (hBG₂ : 0 ≤ BG₂) {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ k + 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1)))) :
    ∀ p ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖blockEnergyFun Gp Hm (compWeight L a₁) ν n z (F₁ (σ p.2, p.1.1))
        (Sol (σ p.2, flEdat Gp Hm (F₁ (σ p.2, p.1.1)) p.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0)‖ ≤
        energyBd d L N (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ) :=
  fanLocalHat_norm_le_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm
    cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁ hSol hσκ hσ1 fun _ ht =>
      blockEnergyFun_bound_of_num (by have := HBp.hd; omega) hS.fam.2.1 hBG₂ hδ₁0 HBp.mass
        HBp.weights hn1 hn z ht.1

end FanHat

end Balaban.Localization
