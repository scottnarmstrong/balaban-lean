/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActTermBound
public import Balaban.Fluctuation.LocalSetActRayTerm
public import Balaban.Fluctuation.LocalSetActRayBound

/-!
# The zero-source term of a domain recomputed on the local generating set of its collar

P6 Lemma 4.1 and P3 pp. 78-79, (4.44)-(4.47), for the potential part of the zero-source activity
of a domain `Y`.  At zero source the term of `Y` is (`zeroSourceActivity_common_fromTowerG_core`,
clause of the direct terms) `-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ evTerm_z(Y)(Θ, σ t x₀) dt`, the
sum over the blocks `z` whose label set contains `Y` of the ray integrals of the terms `evTerm_z(Y)`
of the localization expansion of the block energy `blockEnergyFun 𝔹_{k+1} 𝔹_k … k z` at the
decoupled background and fluctuation fields of the step.

* `zeroSourceTerm_localB_hat`: the same sum recomputed on `𝔹 = 𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺`,
  `Y⁺` the collar of `Y`, `Tl(x₀, w, σ, Θ) = ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ evTerm^loc_z(Y)(Θ, σ t x₀) dt`
  (one local background map `F₁'` and fluctuation map `Sol'` for all blocks, the transported
  parameters and the local hat lift of the restriction of `ψ̂`), satisfies:
  (1) it is analytic in `(Θ, σ)` on the local chart `Ξ^c(𝔹; 1, ε')` times `|σ| < R_σ`, for every
  admissible ray `(x₀, w)` of the box `|ψ̂ q| ≤ c_ψ` (`HatRays`);
  (2) it is bounded there by `|σ| ∑_z [Y ∈ polyDom_z] M_ω 6 |E_sc e^{-2 κ d̃^{cov}(Y)}| / r³`, with
  `E_sc = energyBdScaled … k (K₂' δ₁) δ₁ ρ₄` the scale-uniform block-energy majorant: this is
  the bound of the step's potential terms (`vpart_locInt_hat_dir_dm_scaled_ray`);
  (3) at a datum `D` of the step's chart and a datum `D'` of the local chart agreeing with `D` on
  the top layer of `𝔹`, the step's sum at `D` equals `Tl` at `D'`.
  Proof: for each block `z` with `Y ∈ polyDom_z` the block lies in `X₁ ⊆ Y` and hence in the top
  layer of `𝔹` (`localB_collar_margin`); (1)-(2) from `evTerm_blockEnergy_localHat_bound_analytic`
  (with `treeLenCovOne = 0` for the local covers) and `rayTerm_dl3_analytic_bound`; (3) from
  `rayTerm_dl3_blockEnergyFun_replacement_localB_hat` (the base point stays strictly inside the
  box, `norm_smul_lt_of_mem_hatRays`).  The label index sets `↑X₁` of the step's terms are
  identified with `X1` through `hX₁`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Domain

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {ν : ℝ}

/-- **The zero-source term of a domain recomputed on the local generating set of its collar (P6
Lemma 4.1; P3 pp. 78-79).**  For level sets `𝔹_{k+1}`, `𝔹_k`, per-block decoupled maps `F₁ z`,
`Sol z` of the step, local maps `F₁'`, `Sol'` of `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))`, and per-block cover data
`(m₀, j z, 𝒦_X z)` with `d^{cov,1}_{j z}(X z) = 0` and the block `B_{k+1}(z)` inside `X₁(z)`, the
sum `Tl` over the blocks `z` with `Y ∈ polyDom_z` of the ray integrals of the third derivatives of
the terms `evTerm_z(Y)` recomputed on `𝔹_{k+1}(Y⁺)` is analytic on the local chart times the disc,
bounded by the bound of the step's potential terms, and equals the step's sum at a step datum `D`
when evaluated at a local datum `D'` agreeing with `D` on the top layer of `𝔹_{k+1}(Y⁺)`. -/
theorem zeroSourceTerm_localB_hat (hG' : IsLevel Gp (k + 1))
    (hG : IsLevel Hm k) (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ z (s, rawOf D) = (φ, α))
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
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
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
    (hSol : ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf Gp) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
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
    {m₀ : ℕ} {j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    (hzX : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 Gp m₀ (j z) (𝒦X z))
    {κd κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1κ : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {eps eps' δc : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (heps' : 0 < eps') (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1)
    (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 < cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {ω : ℂ → ℂ} {R₁ : ℝ} (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (Metric.ball (0 : ℂ) R₁))
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Tl : (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      (∀ x₀ w σ Θ, Tl x₀ w σ Θ = ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z) then
          rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ (j z) (𝒦X z))
            (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) w =>
              blockEnergyFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (localB k (Nat.le_succ k)
                  (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                    Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) ν k z
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                    then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), u.1))
                (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                    then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0),
                  flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                    (localB k (Nat.le_succ k)
                      (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                        Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
                    (F₁' ((fun P => if P.1.2 ∈
                        (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                        then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), u.1))
                      u.1.1
                    (fun x i => if h : unitBlock x ∈
                        unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                      (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                        (compWeight L a₁) a₁ ν
                        (F₁' ((fun P => if P.1.2 ∈
                            (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                            then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1
                              else 0), u.1)).2
                        (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                          (fun P => if P.1.2 ∈
                              (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                            then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0))
                        (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1.1
                          (F₁' ((fun P => if P.1.2 ∈
                              (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                            then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1
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
                        then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), u.1)).2
                    (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                      (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                        then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0))
                    (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1.1
                      (F₁' ((fun P => if P.1.2 ∈
                          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
                        then Dec2.extS (coverOf Gp) (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), u.1)).1)
                    (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                    (fun p => if hp : p.1.1 ∈ unitPts Gp then u.2 (⟨p.1.1, hp⟩, p.2) else 0)))
                    (⟨unitBlock x, h⟩, i)
                  else 0)))
              Y) w) ω x₀ σ Θ
        else 0) ∧
      (∀ xw ∈ HatRays (N := N) Gp cψ R₁ Rσ r,
        AnalyticOnNhd ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ => Tl xw.1 xw.2 p.2 p.1)
          (XiCRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps' ×ˢ
            Metric.ball (0 : ℂ) Rσ)) ∧
      (∀ xw ∈ HatRays (N := N) Gp cψ R₁ Rσ r,
        ∀ Θ ∈ XiCRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps',
        ∀ σ : ℂ, ‖σ‖ < Rσ → ‖Tl xw.1 xw.2 σ Θ‖ ≤ ‖σ‖ * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
          if Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z) then
            Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) k
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
              Real.exp (-2 * κd * treeLenCov Gp m₀ Y)‖ / r ^ 3)
          else 0) ∧
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ D' : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N,
        XiCData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps' D' →
        (∀ x ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1), D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x) →
        ∀ xw ∈ HatRays (N := N) Gp cψ R₁ Rσ r, ∀ σ : ℂ, ‖σ‖ < Rσ →
          (∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
            if Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z) then
              rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ (j z) (𝒦X z))
            (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) w =>
              blockEnergyFun Gp Hm (compWeight L a₁) ν k z
                (F₁ z (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w, u.1))
                (Sol z (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w,
                  flEdat Gp Hm (F₁ z (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w, u.1))
                    u.1.1 (hatPsiF Gp a₁ ν hG' cc (F₁ z)
                      (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) u.1 u.2))).1
                (u.1, hatPsiF Gp a₁ ν hG' cc (F₁ z)
                  (extParams Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ (k + 1))) w) u.1 u.2))
              Y) xw.2) ω xw.1 σ (rawOf D)
            else 0) = Tl xw.1 xw.2 σ (rawOf D')) := by
  classical
  have hcψ0 : 0 ≤ cψ := hcψ.le
  have hd0 : 0 < d := by have := HB'.hd; omega
  have hBG₂ : 0 ≤ BG₂ := hF₂.2.1
  have hBG : 0 ≤ BG := hS.fam.2.1
  have hEb0 : 0 ≤ energyBdScaled d L N (compWeight L a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) := by
    have hB0 : 0 ≤ famConst d L BG₂ κ := by
      have := famConst_ge_one (L := L) hBG₂ κ hd0; linarith
    have hρ : 0 ≤ rho4 d L N BG κ := by
      have hB1 : 0 ≤ famConst d L BG κ := by
        have := famConst_ge_one (L := L) hBG κ hd0; linarith
      unfold rho4
      exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
    exact energyBdScaled_nonneg ((HB'.weights k hk1 (by omega)).1.trans' (by norm_num))
      (mul_nonneg (cK2'_nonneg hB0) h1.le) h1.le hρ
  -- a block of a label set containing `Y` lies in the top layer of `𝔹_{k+1}(Y⁺)`
  have hzT : ∀ z, Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z) →
      ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z,
        x ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) := by
    intro z hY x hx
    have hxY : x ∈ Y := subset_polyDom hY (hzX z x hx)
    exact localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp (R := {x})
      (fun y hy => (Finset.mem_singleton.1 hy) ▸ hxY) x (Finset.mem_singleton_self x) x
      (by rw [supDist_self]; exact Nat.zero_le _)
  refine ⟨_, fun _ _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro xw hxw p hp
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z)
    · simp only [hY, ↓reduceIte]
      rw [hX₁ z]
      have hT := evTerm_blockEnergy_localHat_bound_analytic hk1 hk Yp hN hM hagl hS HB' ha₁ ha₂
        hκ hMc hMX hF₁'an hF₁' hBG₂ h1 hSol'an hSol' heps' hsmall' hc7' hphi' hδ₀e hmarD' hαD'
        hsm cc hcψ0 hδ₁c (hcov z) HB'.hd HB'.hL (hopt z) hκ₀ hκd hκκ h1κ hlog le_rfl hEb0 z
        (hzT z hY) (by rw [hΔ z]; simp)
      exact (rayTerm_dl3_analytic_bound (hT.2 Y) (hT.1 Y) hR₁ hω hMω hωb hr hxw).1 p hp
    · simp only [hY, ↓reduceIte]
      exact analyticAt_const
  · intro xw hxw Θ hΘ σ hσ
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z)
    · simp only [hY, ↓reduceIte]
      rw [hX₁ z]
      have hT := evTerm_blockEnergy_localHat_bound_analytic hk1 hk Yp hN hM hagl hS HB' ha₁ ha₂
        hκ hMc hMX hF₁'an hF₁' hBG₂ h1 hSol'an hSol' heps' hsmall' hc7' hphi' hδ₀e hmarD' hαD'
        hsm cc hcψ0 hδ₁c (hcov z) HB'.hd HB'.hL (hopt z) hκ₀ hκd hκκ h1κ hlog le_rfl hEb0 z
        (hzT z hY) (by rw [hΔ z]; simp)
      refine ((rayTerm_dl3_analytic_bound (hT.2 Y) (hT.1 Y) hR₁ hω hMω hωb hr hxw).2 Θ hΘ σ
        hσ).trans ?_
      have e : -κ₀ * treeLenCovOne m₀ (j z) (X z) - 2 * κd * treeLenCov Gp m₀ Y =
          -2 * κd * treeLenCov Gp m₀ Y := by rw [hΔ z]; ring
      rw [e]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hMω) (norm_nonneg _)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.le_norm_self _) (by norm_num)) (by positivity)
    · simp [hY]
  · intro D hD D' hD'x hD' xw hxw σ hσ
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁f z) m₀ (j z) (𝒦X z)
    · simp only [hY, ↓reduceIte]
      rw [hX₁ z]
      exact rayTerm_dl3_blockEnergyFun_replacement_localB_hat hG' hG hk1 hk Y Yp hYp hN hm₁ hM
        hag hagm hagl hS HB HB' ha₁ ha₂ hκ hMc hMX (hF₁ z) hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ (hSol z)
        hSol' (hcov z) heps hsmall hc7 hphi heps' hsmall' hc7' hphi' hδ₀a hδ₀e hmarD hαD hmarD'
        hαD' hsm hD hD'x hD' cc hcψ0 hδ₁c (Nat.le_succ k) z (hzX z) ω xw.1 xw.2 σ
        (fun q => norm_smul_lt_of_mem_hatRays hcψ hR₁ hr.le hxw hσ q)
    · simp only [hY, ↓reduceIte]

end Domain

end Balaban.Localization
