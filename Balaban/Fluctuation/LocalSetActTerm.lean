/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActHat
public import Balaban.Fluctuation.LocalPairCollar
public import Balaban.Fluctuation.LocalClassTau

/-!
# The zero-source term of a domain recomputed on the local generating set of its collar

P3 pp. 78-79, (4.44)-(4.47) and P6 Lemma 4.1 for the potential part of the zero-source activities.
At zero source the term of a domain `Y` is built from the terms
`evTerm_z(Y) = ∑_{𝒞 : Y[𝒞] = Y} coef(blockEnergyFun … z, 𝒞)` of the localization expansion of the
block energy of `B_{k+1}(z)` (`zeroSourceActivity_common_fromTowerG_core`): the expansion of the
level set `𝔹_{k+1}` with the cover data `(m₀, j, 𝒦_X)`, the parameter cubes disjoint from
`X₁ = X1 𝔹_{k+1} m₀ j 𝒦_X`, the parameters `σ w = extParams 𝔹_{k+1} X₁ w` and the ambient hat lift.

* `evTerm_blockEnergyFun_replacement_localB_hat`: `evTerm_z(Y)` is the same sum recomputed on
  `𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺`, `Y⁺` the collar of `Y` (`hYp`), with the transported
  parameters `τ w`, the local datum `D'` (agreeing with `D` on the top layer of `𝔹_{k+1}(Y⁺)`) and
  the local hat lift of the restriction of `ψ̂`.  The read region of every family `𝒞` with
  `Y[𝒞] = Y` lies in `Y`: the cubes of `𝒞` (`Pset_subset_Ysites'`), the cubes meeting `X₁`
  (`Pset_subset_of_not_disjoint`, `X₁ ⊆ Y[𝒞]`) and the block `B_{n+1}(z)` (in `X₁`, `hzX`; for the
  cover data of the zero-source terms this is `LocalCover.blockSites_subset_nbhdF` with
  `LocalCover.coe_nbhdF_eq_X1`); the margin in the top layer of `𝔹_{k+1}(Y⁺)` is
  `localB_collar_margin`; each coefficient is `coef_blockEnergyFun_replacement_localB_hat`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation Matrix

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {ν : ℝ}

/-- **The term `evTerm_z(Y)` of the block energy recomputed on the local generating set of the
collar (P3 pp. 78-79; P6 Lemma 4.1).**  Let `𝔹_{k+1}`, `𝔹_k` be level sets (`k ≥ 1`), `(m₀, j, 𝒦_X)`
cover data of `𝔹_{k+1}` (`CovSetup`) with `X₁ = X1 𝔹_{k+1} m₀ j 𝒦_X` containing the block
`B_{n+1}(z)`, `Y` a set of sites and `Y⁺` its collar.  For a datum `D` of the chart
`Ξ^c(𝔹_{k+1}; 1, ε)`, a datum `D'` of `Ξ^c(𝔹_{k+1}(Y⁺); 1, ε')` agreeing with `D` on the top layer
of `𝔹_{k+1}(Y⁺)` and a hat variable `|ψ̂| ≤ c_ψ`, the term `∑_{𝒞 : Y[𝒞] = Y} coef(·, 𝒞)` of the
ambient block energy (parameters `extParams 𝔹_{k+1} X₁ w`, ambient hat lift) at `(D, ψ̂)` equals the
same sum of the block energy recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` (transported parameters, local
hat lift) at `(D', ψ̂)`. -/
theorem evTerm_blockEnergyFun_replacement_localB_hat (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
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
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ (s, rawOf D) = (φ, α))
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
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
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
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
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
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Gp m₀ j X 𝒦X)
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
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {D' : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N}
    (hD'x : XiCData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
      (k + 1) 1 eps' D')
    (hD' : ∀ x ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1),
      D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ψh : unitPts Gp × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {n : ℕ} (hn : n ≤ k + 1) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (hzX : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ X1 Gp m₀ j 𝒦X) :
    evTerm (fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) w =>
        blockEnergyFun Gp Hm (compWeight L a₁) ν n z (F₁ (extParams Gp (X1 Gp m₀ j 𝒦X) w, u.1))
          (Sol (extParams Gp (X1 Gp m₀ j 𝒦X) w,
            flEdat Gp Hm (F₁ (extParams Gp (X1 Gp m₀ j 𝒦X) w, u.1)) u.1.1
              (hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (X1 Gp m₀ j 𝒦X) w) u.1 u.2))).1
          (u.1, hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (X1 Gp m₀ j 𝒦X) w) u.1 u.2))
      Y (rawOf D, ψh) =
    evTerm (fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) w =>
        blockEnergyFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (compWeight L a₁) ν n z
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
      Y (rawOf D', ψh) := by
  classical
  unfold evTerm
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨-, hYs⟩ := (mem_connFams _).1 hC
  set R : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (· ∈ Y) with hRdef
  have hRY : ∀ x ∈ R, x ∈ Y := fun x hx => (Finset.mem_filter.1 hx).2
  have hYR : ∀ x ∈ Y, x ∈ R := fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
  have hXY : X1 Gp m₀ j 𝒦X ⊆ Y := by
    rw [← hYs]
    exact subset_Ysites _ _
  have hCY : ∀ i ∈ C, Pset m₁ i.1.1 ⊆ Y := fun i hi => by
    rw [← hYs]
    exact Pset_subset_Ysites' hcov (c := fun i : ParIdx Gp (X1 Gp m₀ j 𝒦X) => i.1.1)
      (fun i => i.1.2) hi
  exact coef_blockEnergyFun_replacement_localB_hat hG' hG hk1 hk Yp hN hm₁ hM hag hagm hagl hS
    HB HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' C
    (Real.one_lt_exp_iff.2 hκ) le_rfl heps hsmall hc7 hphi heps' hsmall' hc7' hphi' hδ₀a hδ₀e
    hmarD hαD hmarD' hαD' hsm hD hD'x hD' cc hcψ hδ₁c ψh hψh
    (fun i hi y hy => hYR y (hCY i hi hy))
    (fun P hP hd y hy => hYR y (hXY (Pset_subset_of_not_disjoint hcov.polySetup hP hd hy)))
    hn z (fun x hx => hYR x (hXY (hzX x hx)))
    (localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp hRY) (rawOf D) (rawOf D')

end Assembly

end Balaban.Localization
