/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActLocalB
public import Balaban.Fluctuation.LocalPairReplacementHat

/-!
# The block energy recomputed on the local generating set with the local hat variable

P3 pp. 78-79, (4.46) and P6 Lemma 4.1 for the zero-source part of the activities: the ambient term
uses the fluctuation variable `hatPsiF` of the level set `𝔹_{k+1}` (the decoupled square root of
its cover at the parameters `σ w = extParams 𝔹_{k+1} X₁ w`); the term recomputed on
`𝔹_{k+1}(Y) = localB (k + 1) … Y` uses the local hat lift (the decoupled square root of the cover of
`𝔹_{k+1}(Y)` at the local background and the transported parameters `τ w`, applied to the
restriction of `ψ̂` to the unit lattice of `𝔹_{k+1}(Y)`).

* `coef_blockEnergyFun_replacement_localB_hat`: the coefficient equality of Lemma AE for the block
  energy `blockEnergyFun … n z` (the potential part of the zero-source term of
  `zeroSourceActivity_common_fromTowerG_core`) between the ambient pair with the ambient hat lift
  and the local pair with the local hat lift, for a level set `𝔹_{k+1}` (the step's set `S.G'`
  qualifies: `S.hG'`), a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, a datum `D'` of
  `Ξ^c(𝔹_{k+1}(Y); 1, ε')` agreeing with `D` on the top layer, and a read region (the cubes of `𝒞`,
  the cubes meeting `X₁`, the block `B_{n+1}(z)`) with the margin `2 M₁ L^{k+1}` in the top layer.
  Proof: `coef_blockEnergyFun_replacement_localB` with `ψ₁ = hatPsiF`, `ψ₂` the local hat lift; the
  strict data inequalities by `strictDataM_flEdat_cover` (both lifts lie in the fluctuation ball,
  `localHatLift_mem_flBallLC_of_spec`), and the agreement within `L^{k+1}` of the read region by
  `localHatLift_eq_hatPsiF_localB`.
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

/-- **The block energy recomputed on the local generating set with the local hat variable (P3
pp. 78-79, (4.46); P6 Lemma 4.1).**  Let `𝔹_{k+1}`, `𝔹_k` be level sets (`k ≥ 1`),
`𝔹_{k+1}(Y) = localB (k + 1) … Y`, `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))`, and let the read region
`R` (the cubes of `𝒞`, the cubes meeting `X₁` and the block `B_{n+1}(z)`) have the margin: every
site within `2 M₁ L^{k+1}` of `R` lies in `Ω_{k+1}(𝔹_{k+1}(Y))`.  For a datum `D` of the chart
`Ξ^c(𝔹_{k+1}; 1, ε)`, a datum `D'` of `Ξ^c(𝔹_{k+1}(Y); 1, ε')` agreeing with `D` on the top layer
of `𝔹_{k+1}(Y)` and a hat variable `|ψ̂| ≤ c_ψ`, the coefficient `coef (·) 𝒞` of the ambient block
energy (parameters `σ w`, fluctuation variable `hatPsiF … (σ w) ψ̂`) equals that of the block energy
recomputed on `(𝔹_{k+1}(Y), 𝔹_k(Y))` (parameters `τ w`, the local hat lift of `ψ̂`).  The hypotheses
are the constants (those of `coef_eTermFun_replacement_localB_hat` at `ε` and `ε'`), the
specifications of the solution maps and the two charts. -/
theorem coef_blockEnergyFun_replacement_localB_hat (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
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
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
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
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx Gp X₁)) {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
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
    {D' : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N}
    (hD'x : XiCData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
      (k + 1) 1 eps' D')
    (hD' : ∀ x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1),
      D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ψh : unitPts Gp × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {n : ℕ} (hn : n ≤ k + 1) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (hRz : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1))
    (Θ₁ Θ₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    coef (fun w => blockEnergyFun Gp Hm (compWeight L a₁) ν n z
        (F₁ (extParams Gp X₁ w, rawOf D))
        (Sol (extParams Gp X₁ w,
          flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ
            (hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp X₁ w) (rawOf D) ψh))).1
        (Θ₁, hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp X₁ w) (rawOf D) ψh)) C =
      coef (fun w => blockEnergyFun (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        (compWeight L a₁) ν n z
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
            D'.Ψ
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
                  rawOf D')).2
                (Dec2.extS (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) D'.Ψ
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
                  rawOf D')).1)
                (unitQ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
                (⟨unitBlock x, h⟩, i)
              else 0))).1
        (Θ₂, fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
                  rawOf D')).2
                (Dec2.extS (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) D'.Ψ
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
                  rawOf D')).1)
                (unitQ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
                (⟨unitBlock x, h⟩, i)
              else 0)) C := by
  classical
  obtain ⟨Sb, Sb', -, -⟩ := localB_replacement_coverBases hG' Hm hk Y hN hm₁ hM HB hag hagm hagl
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ0' : 0 < xiC1 d * eps' := by positivity
  have hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB hδ0 (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7
      (xiCData_inDomainC HB hsmall hD)
  have hDd' : InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
      (c7 d L N BG κ) ν D' := by
    have hc1 : xiC1 d * eps' ≤ bgC1 d L N := hc7'.trans (c7_le_bgC1 d L N BG κ)
    exact inUnionDomainC_of_inDomainC HB' hδ0' (hc1.trans (bgC1_le_bgC0 d L N hd0)) hc7'
      (xiCData_inDomainC HB' hsmall' hD'x)
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams Gp X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hHm : Hm.Ω (k + 1) = ∅ :=
    Finset.eq_empty_of_forall_notMem fun x => isLevel_not_mem_Ω hG le_rfl (by omega) x
  have hψh' : ∀ p : unitPts (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) × Fin N,
      ‖(fun p : unitPts (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) × Fin N =>
        if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0) p‖ ≤ cψ := by
    intro p
    dsimp only
    split_ifs
    · exact hψh _
    · simpa using hcψ
  refine coef_blockEnergyFun_replacement_localB hG' hG hk1 hk Y hN hm₁ hM hag hagm hagl hS HB HB'
    hκ.le hMc hF₁ hF₁' hF₂ hM₂ h0 h1.le hδ₀ hδ₁ hSol hSol' C hR' hRκ hDd hDd' hD'
    (fun w => hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp X₁ w) (rawOf D) ψh)
    (fun w x i => if h : unitBlock x ∈
        unitPts (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) then
      (cc • (decCovSqrt (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) a₁ ν
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).2
        (Dec2.extS (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
        (barField (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) D'.Ψ
          (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).1)
        (unitQ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
        (unitP (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) *ᵥ
        (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)))
        (⟨unitBlock x, h⟩, i)
      else 0)
    (fun w hw => ?_) (fun w hw => ?_) hRC hRX hn z hRz hmar (fun w hw x hx y hy => ?_) Θ₁ Θ₂
  · -- the strict data inequalities of the ambient fluctuation problem
    have hψa : hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp X₁ w) (rawOf D) ψh ∈ FlBall Hm δ₁ := by
      rw [hatPsiF_eq_dite (a₁ := a₁) (ν := ν) hG' cc F₁ (extParams _ X₁ w) (rawOf D) ψh]
      exact (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb HB hκ.le hMc hMX
        (Cchi_nonneg d L) hF₁ heps hsmall hc7 hphi hmarD hαD hsm (hsσ w hw) hD cc hcψ h1 hδ₁c
        hψh).1
    exact strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD hψa
  · -- the strict data inequalities of the local fluctuation problem
    have hψl := (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb' HB' hκ.le hMc hMX
      (Cchi_nonneg d L) hF₁' heps' hsmall' hc7' hphi' hmarD' hαD' hsm
      (localB_tau_norm_lt hk Y _ (hsσ w hw) hE1) hD'x cc hcψ h1 hδ₁c hψh').1
    exact strictDataM_flEdat_cover hS Sb' HB' hκ hMc heps' hsmall' hc7' hphi' h1 hδ₀e
      (localB_drop_precedes hk (Nat.le_succ k) Y le_rfl le_rfl) hF₁' hSol'
      (localB_tau_norm_lt hk Y _ (hsσ w hw) hE1) hD'x
      (fun x _ => hψl x ((mem_dataSites Hm).2 (Or.inl (hG x).1)))
  · -- the two hat lifts agree within `L^{k+1}` of the read region
    exact funext fun i => (localHatLift_eq_hatPsiF_localB hG' hk1 hk Y hN hm₁ hM hag hagl hS HB HB'
      ha₁ ha₂ hκ hMc hMX hF₁ hF₁' heps hsmall hc7 hphi heps' hsmall' hc7' hphi' hmarD hαD hmarD'
      hαD' hsm hD hD'x hD' hRC hRX hmar hw.1 (hsσ w hw) cc ψh ⟨x, hx, hy⟩ i).symm

end Assembly

end Balaban.Localization
