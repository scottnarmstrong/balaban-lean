/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActTerm
public import Balaban.Fluctuation.LocalSetActAnalytic

/-!
# The zero-source term recomputed on the local generating set: analyticity and bound

P6 Lemma 4.1 (analyticity and bounds of the localized terms on a modified generating set) for the
term `evTerm_z(Y)` of the block energy recomputed on `𝔹 = 𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺`
(`evTerm_blockEnergyFun_replacement_localB_hat`): the families are those of the expansion of the
ambient set `𝔹_{k+1}` (cover data `(m₀, j, 𝒦_X)`), the parameters are transported to the cover of
`𝔹` (`τ ∘ extParams`), the hat variable `ψ̂` of the ambient unit lattice is restricted to the unit
lattice of `𝔹`, and only the datum `Θ` of `𝔹` enters.

* `evTerm_blockEnergy_localHat_bound_analytic`: for a block `B_{k+1}(z)` in the top layer of `𝔹`
  (the blocks of the zero-source terms, at the scale `n = k`), the local term is analytic on the
  local chart `Ξ^c(𝔹; 1, ε')` times the box `|ψ̂ q| ≤ c_ψ` and bounded there by
  `Eb e^{-κ₀ d^{cov,1}_j(X) - 2 κ d̃^{cov}(Y)}` whenever the scale-uniform block-energy majorant
  `energyBdScaled` (that of the step's potential terms) is at most `Eb e^{-(κ - 1) d^{cov,1}_j(X)}`.
  Proof: the integrand is analytic and bounded on the chart times the box times the polydisc
  (`fanLocalHat_blockEnergy_analytic_cover`, `fanLocalHat_blockEnergy_norm_le_cover_scaled` at `𝔹`
  with `localB_coverData` and the layers `localB_layers_of_top`, the parameter map of
  `localB_tauExt_analyticAt`, `localB_tauExt_norm_lt`, composed with the restriction of `ψ̂`), and
  `evTerm_bound_analyticOnNhd_of_bd` (the Cauchy bound of the coefficients and the Peierls sum
  over the connected families of the expansion of `𝔹_{k+1}`; no locality is used).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Bound

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {ν : ℝ}

/-- **Analyticity and bound of the zero-source term recomputed on the local generating set (P6
Lemma 4.1).**  For `𝔹 = localB (k + 1) … Y⁺`, `H⁻ = localB k … Ω_k(𝔹)`, analytic maps `F₁'`, `Sol'`
with the specifications of the decoupled background and fluctuation fields of the local pairs, and
cover data `(m₀, j, 𝒦_X)` of the ambient set `𝔹_{k+1}` and a block `B_{k+1}(z)` in the top layer
`Ω_{k+1}(𝔹)`, the term `∑_{𝒞 : Y[𝒞] = Y} coef(blockEnergyFun 𝔹 H⁻ … k z, 𝒞)` with the transported
parameters and the local hat lift of the restriction of `ψ̂` is analytic on the chart
`Ξ^c(𝔹; 1, ε')` times the box `|ψ̂ q| ≤ c_ψ` and bounded there by
`Eb e^{-κ₀ d^{cov,1}_j(X) - 2 κ d̃^{cov}(Y)}`, for `energyBdScaled ≤ Eb e^{-(κ - 1) d^{cov,1}_j(X)}`. -/
theorem evTerm_blockEnergy_localHat_bound_analytic (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN : 5 < N₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {κ : ℝ} (hκ : 0 < κ)
    (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁'an : AnalyticOnNhd ℂ F₁' {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N,
        InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧
          q.2 = (D.Ψ, D.h)})
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {BG₂ : ℝ} (hBG₂ : 0 ≤ BG₂) {δ₀ δ₁ : ℝ} (h1 : 0 < δ₁)
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol'an : AnalyticOnNhd ℂ Sol' {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2})
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {eps' δc : ℝ} (heps' : 0 < eps') (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1)
    (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κd κ₀ κ₁ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ₁)
    (h1κ : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hκ₁κ : κ₁ ≤ κ) (hEb0 : 0 ≤ Eb)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hzT : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z,
      x ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1))
    (hEb : energyBdScaled d L N (compWeight L a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
        (rho4 d L N BG κ) ≤ Eb * Real.exp (-(κd - 1) * treeLenCovOne m₀ j X)) :
    (∀ Y, ∀ u ∈ XiCRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps' ×ˢ
        {ψ : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψ q‖ ≤ cψ},
      ‖evTerm (fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) w =>
        blockEnergyFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (compWeight L a₁) ν k z
          (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
              then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1))
          (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
              then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0),
            flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
              (localB k (Nat.le_succ k)
                (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                  Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
              (F₁' ((fun P => if P.1.2 ∈
                  (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1))
                u.1.1
              (fun x i => if h : unitBlock x ∈
                  unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (compWeight L a₁) a₁ ν
                  (F₁' ((fun P => if P.1.2 ∈
                      (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                      then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1
                        else 0), u.1)).2
                  (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (fun P => if P.1.2 ∈
                        (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                      then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0))
                  (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1.1
                    (F₁' ((fun P => if P.1.2 ∈
                        (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                      then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1
                        else 0), u.1)).1)
                  (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                  (fun p => if hp : p.1.1 ∈ unitPts Gp then u.2 (⟨p.1.1, hp⟩, p.2) else 0)))
                  (⟨unitBlock x, h⟩, i)
                else 0))).1
          (u.1, (fun x i => if h : unitBlock x ∈
              unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
            (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
              (compWeight L a₁) a₁ ν
              (F₁' ((fun P => if P.1.2 ∈
                  (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1)).2
              (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0))
              (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1.1
                (F₁' ((fun P => if P.1.2 ∈
                    (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1)).1)
              (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
              (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
              (fun p => if hp : p.1.1 ∈ unitPts Gp then u.2 (⟨p.1.1, hp⟩, p.2) else 0)))
              (⟨unitBlock x, h⟩, i)
            else 0)))
        Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κd * treeLenCov Gp m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (evTerm (fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1) Gp m₀
        (X1 Gp m₀ j 𝒦X)
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) w =>
        blockEnergyFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (compWeight L a₁) ν k z
          (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
              then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1))
          (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
              then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0),
            flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
              (localB k (Nat.le_succ k)
                (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                  Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
              (F₁' ((fun P => if P.1.2 ∈
                  (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1))
                u.1.1
              (fun x i => if h : unitBlock x ∈
                  unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (compWeight L a₁) a₁ ν
                  (F₁' ((fun P => if P.1.2 ∈
                      (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                      then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1
                        else 0), u.1)).2
                  (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (fun P => if P.1.2 ∈
                        (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                      then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0))
                  (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1.1
                    (F₁' ((fun P => if P.1.2 ∈
                        (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                      then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1
                        else 0), u.1)).1)
                  (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                  (fun p => if hp : p.1.1 ∈ unitPts Gp then u.2 (⟨p.1.1, hp⟩, p.2) else 0)))
                  (⟨unitBlock x, h⟩, i)
                else 0))).1
          (u.1, (fun x i => if h : unitBlock x ∈
              unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
            (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
              (compWeight L a₁) a₁ ν
              (F₁' ((fun P => if P.1.2 ∈
                  (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1)).2
              (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0))
              (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1.1
                (F₁' ((fun P => if P.1.2 ∈
                    (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                  then Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0), u.1)).1)
              (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
              (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
              (fun p => if hp : p.1.1 ∈ unitPts Gp then u.2 (⟨p.1.1, hp⟩, p.2) else 0)))
              (⟨unitBlock x, h⟩, i)
            else 0)))
        Y)
      (XiCRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1
        eps' ×ˢ {ψ : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψ q‖ ≤ cψ})) := by
  classical
  have hcd := localB_coverData hk Yp hN hM hagl HB'
  have hHl : (localB k (Nat.le_succ k)
      (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
        Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) = ∅ :=
    localB_Ω_of_gt (Nat.lt_succ_self k)
  have hP := localB_drop_precedes hk (Nat.le_succ k) Yp (le_refl (minSep L (L ^ m₁)))
    (le_refl (minSep L (L ^ m₁)))
  have hσ1 : ∀ (w : ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) (P : ℕ × CTorus d L N₁ m₁ (k + 1))
      (hP : P ∈ (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).parCubes ∅ →
      (fun P : ↥(coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx =>
          if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) then
            Dec2.extS (coverOf Gp) (extParams Gp (X1 Gp m₀ j 𝒦X) w) P.1 else 0) ⟨P, hP⟩ = 1 :=
    fun _ P hP hnot => absurd (Finset.mem_filter.2 ⟨hP, fun h =>
      Finset.notMem_empty _ (h (mem_cubeP.2 (SameCell.refl _ _)))⟩) hnot
  have hA := fanLocalHat_blockEnergy_analytic_cover hk1 ha₁ ha₂ hS hcd.1 HB' hκ hMc hMX
    (Cchi_nonneg d L) heps' hsmall' hc7' hphi' hmarD' hαD' hsm cc hcψ h1 hδ₁c hP hHl hF₁'an hF₁'
    (hSol'an.mono fun p hp => ⟨hp.1, strictDataM_mono_left hδ₀e hp.2⟩)
    (fun p hp hp2 => hSol' p hp (strictDataM_mono_left hδ₀e hp2)) (localB_tauExt_analyticAt hk Yp (X1 Gp m₀ j 𝒦X))
    (localB_tauExt_norm_lt hk Yp (X1 Gp m₀ j 𝒦X) hκ) hσ1 k z
  have hB := fanLocalHat_blockEnergy_norm_le_cover_scaled hk1 ha₁ ha₂ hS hcd.1 HB' hκ hMc hMX
    (Cchi_nonneg d L) heps' hsmall' hc7' hphi' hmarD' hαD' hsm cc hcψ h1 hδ₁c hP hHl hF₁'
    (fun p hp hp2 => hSol' p hp (strictDataM_mono_left hδ₀e hp2))
    (localB_tauExt_norm_lt hk Yp (X1 Gp m₀ j 𝒦X) hκ) hσ1 hBG₂ hk1 le_rfl z
    (fun x hx => localB_layers_of_top hk1 hk Yp (hzT x hx))
  -- the restriction of the hat variable to the unit lattice of `𝔹`
  set rs : (unitPts Gp × Fin N → ℂ) →
      (unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℂ) :=
    fun ψ p => if hp : p.1.1 ∈ unitPts Gp then ψ (⟨p.1.1, hp⟩, p.2) else 0 with hrs
  have hrsA : ∀ ψ, AnalyticAt ℂ rs ψ := fun ψ => by
    refine analyticAt_pi_iff.2 fun p => ?_
    by_cases hp : p.1.1 ∈ unitPts Gp
    · simp only [hp, ↓reduceDIte]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : unitPts Gp × Fin N => ℂ)
        (⟨p.1.1, hp⟩, p.2)).analyticAt ψ
    · simp only [hp, ↓reduceDIte]
      exact analyticAt_const
  have hrsB : ∀ ψ : unitPts Gp × Fin N → ℂ, (∀ q, ‖ψ q‖ ≤ cψ) → ∀ p, ‖rs ψ p‖ ≤ cψ := by
    intro ψ hψ p
    simp only [hrs]
    split_ifs
    · exact hψ _
    · simpa using hcψ
  have hpd : polydisc (0 : ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) (fun _ => Real.exp κ₁) ⊆
      polydisc (0 : ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) (fun _ => Real.exp κ) :=
    fun w hw i => (hw i).trans_le (Real.exp_le_exp.2 hκ₁κ)
  refine evTerm_bound_analyticOnNhd_of_bd hcov hd hL (fun i => i.1.2)
    (fun i i' h => Subtype.ext (Subtype.ext h)) (fun i => i.2) hopt hκ₀ hκd hκ₁ h1κ hlog hEb0
    ?_ ?_
  · rintro ⟨u, w⟩ ⟨⟨hu1, hu2⟩, hw⟩
    have hA1 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) => p.1) (u, w) :=
      analyticAt_fst
    have hA11 : AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ) => q.1) u := analyticAt_fst
    have hA12 : AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ) => q.2) u := analyticAt_snd
    have h1 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) => p.1.1) (u, w) :=
      hA11.comp hA1
    have h12 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) => p.1.2) (u, w) :=
      hA12.comp hA1
    have h2 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) => rs p.1.2) (u, w) :=
      AnalyticAt.comp (g := rs) (hrsA u.2) h12
    have hf : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (X1 Gp m₀ j 𝒦X) → ℂ) =>
          ((p.1.1, rs p.1.2), p.2)) (u, w) := (h1.prod h2).prod analyticAt_snd
    have hc := (hA ((u.1, rs u.2), w) ⟨⟨hu1, hrsB u.2 hu2⟩, hpd hw⟩).comp_of_eq hf rfl
    exact hc
  · intro u hu s hs
    exact (hB ((u.1, rs u.2), s) ⟨⟨hu.1, hrsB u.2 hu.2⟩, hpd hs⟩).trans hEb

end Bound

end Balaban.Localization
