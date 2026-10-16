/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassLat
public import Balaban.Fluctuation.LocalClassLatData

/-!
# Lattice covariance of the local terms under the paving group

`localB_eTermHat_evTerm_paving`: the instance of `localB_eTermHat_evTerm_lat` at an element `σ` of
the paving group `pavingSymGroup L m₀ (k + 1)` and the local generating sets `𝔹 = 𝔹_{k+1}(Y⁺)`,
`𝔹' = 𝔹_{k+1}((σ Y)⁺)` of the polymers `Y`, `σ Y`.  The symmetry data of `𝔹 → 𝔹'` (lattice symmetry,
unit blocks, transport of the covers, blocks and unit points) are supplied by
`localB_collar_symmData`; those of the other generating sets of the terms (`𝔹_k`, `𝔹_j`, `H⁻`) by
`nonempty_latSymm_of_mem_symGroupBy` from `Ω_i(G') = σ Ω_i(G)`.  The hypotheses that mention the
transports are stated through their defining properties:

* the parameter maps correspond at the centres of a cube and of its image cube (`hww`);
* `K'`, `γ'` are the images of `K`, `γ` under the relabelling of the unit points by every bijection
  matching the unit blocks (`hKγ`);
the symmetry of the ambient expansion (`Sa`, `Pa`, `κι`, `hcI`) and the covariance of the old
term on its chart (`hEr`) are hypotheses as in `localB_eTermHat_evTerm_lat`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.Localization.DecEquiv
  Balaban.Localization.DetDecCov Balaban.Localization.DetUnitIncidence MeasureTheory Finset Matrix

section LocalBPaving

open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk Gk₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj Gj₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}

/-- **Lattice covariance under the paving group of the term of the local class recomputed on
`𝔹 = 𝔹_{k+1}(Y⁺)`, on the class domain** (the clause `eucE` of the successor class for the E-part,
before the y-labels; instance of `localB_eTermHat_evTerm_lat` with the symmetry data of
`localB_collar_symmData`).  See the module docstring for the hypotheses. -/
theorem localB_eTermHat_evTerm_paving {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι']
    [Fintype ι'] {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa}
    {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)} {cI' : ι' → ℕ × CTorus d L N₁ m₁ (k + 1)} {m₀ : ℕ}
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) (hk : k + 1 ≤ k + 1)
    (Yp Yp₂ : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁) {Bd : ℝ}
    (hP : Precedes Gk (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    (hF : FlSetting N (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))) (D : BgData (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σp : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))} (hσan : ∀ w, AnalyticAt ℂ σp w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f → σp w ⟨P, hP⟩ = 1)
    {γ : Measure (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)} {K : Set (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ Bd)
    (hP₂ : Precedes Gk₂ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (hq₂ : Precedes Gj₂ Gk₂)
    (colk₂ : ∀ z ∈ collar Gk₂, z ∈ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1) (colj₂ : ∀ z ∈ collar Gj₂, z ∈ Gk₂.Ω 1)
    {X₀₂ X₁f₂ : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀₂ : ∀ x ∈ dataSites Gk₂, x ∈ X₀₂)
    (hN₂ : ∀ x ∈ X₀₂, x ∈ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f₂)
    (hF₂ : FlSetting N (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Hm₂ a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f₂)
    (hHm₂ : Hm₂.Ω (k + 1) = ∅)
    {Fk₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk₂.Ω 1 × Fin N → ℂ) × (Gk₂.Ω 1 → ℂ)}
    (hFkan₂ : AnalyticOnNhd ℂ Fk₂ {p | ∃ D : BgData Gk₂ N,
      InUnionDomainC Gk₂ (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk₂ : ∀ D : BgData Gk₂ N, InUnionDomainC Gk₂ (bgC0 d L N) (bgC1 d L N) ν D →
      Fk₂ (rawOf D) = (bgFieldC Gk₂ (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk₂ (compWeight L a₁) ν (bgC0 d L N) D))
    {E₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE₂ : AnalyticOnNhd ℂ E₂ (XiCRaw Gj₂ (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {F₁₂ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an₂ : AnalyticOnNhd ℂ F₁₂ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁₂ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))) (D : BgData (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁₂ (s, rawOf D) = (φ, α))
    {Sol₂ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) × Edat Hm₂ N → (Hm₂.Ω 1 × Fin N → ℂ) × (Hm₂.Ω 1 → ℂ)}
    (hSolan₂ : AnalyticOnNhd ℂ Sol₂ {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol₂ : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) × Edat Hm₂ N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ p).1 = dphi Hm₂ (Dec2.decG (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ p).2 ∧
        Small Hm₂ (Sol₂ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm₂ (Sol₂ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm₂ (Sol₂ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm₂.Ω 1 → ℂ, Small Hm₂ δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ p).2))
    {σp₂ : (ι' → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))} (hσan₂ : ∀ w, AnalyticAt ℂ σp₂ w)
    (hσκ₂ : ∀ w ∈ polydisc (0 : ι' → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp₂ w P‖ < Real.exp κ)
    (hσ1₂ : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).parCubes X₁f₂ → σp₂ w ⟨P, hP⟩ = 1)
    {γ₂ : Measure (unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)} {K₂ : Set (unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc₂ : IsCompact K₂) (hKb₂ : ∀ ψ ∈ K₂, ∀ r, |ψ r| ≤ cψ) (hγ₂ : γ₂ K₂ < ⊤)
    (hEb₂ : ∀ r ∈ XiCRaw Gj₂ (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E₂ r‖ ≤ Bd)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (hYp : (∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)))
    (hYp₂ : (∀ z, z ∈ Yp₂ ↔ ∃ x ∈ σ '' Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (GsSpec.torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)))
    (hΩk : ∀ i, ((Gk₂.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      σ '' ((Gk.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)))) (hΩj : ∀ i, ((Gj₂.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      σ '' ((Gj.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)))) (hΩm : ∀ i, ((Hm₂.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
      σ '' ((Hm.Ω i : Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))))
    (Sa : LatSymm Ga Ga σ) {τa : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (Pa : PolymerSymm Ga m₀ σ τa) (κι : ι ≃ ι') (hcI : ∀ i, cI' (κι i) = τa (cI i))
    (hcI1 : ∀ i, cI i ∈ (coverOf Ga).cubeIdx)
    (hww : ∀ w' (P P' : ℕ × CTorus d L N₁ m₁ (k + 1)), P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx →
      P' ∈ (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx → P'.1 = P.1 → SameCell (L ^ (P.1 + m₁)) (σ P.2) P'.2 →
      Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w') P' = Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σp (w' ∘ κι)) P)
    (hEr : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), E₂ (symRaw σ r) = E r)
    (hKγ : ∀ u : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) ≃ unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))),
      (∀ (y : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (x : CTorus d L N₁ m₁ (k + 1)),
        unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k)) →
      (∀ ψ : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ,
        (fun r : unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N => ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) ∈ K₂ ↔
          ψ ∈ K) ∧
      Measure.map (fun (ψ : unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ) (r : unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N) =>
        ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) γ = γ₂)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (Gf : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGf : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gf Θ w =
      ∫ ψ in K,
            eTermFun (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
              (compWeight L a₁) Fk E (F₁ (σp w, Θ))
        (Sol (σp w, flEdat (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σp w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σp w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σp w))
                (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σp w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σp w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σp w))
                (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σp w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (Gf₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι' → ℂ) → ℂ)
    (hGf₂ : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι' → ℂ), Gf₂ Θ w =
      ∫ ψ in K₂,
            eTermFun (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Gj₂ Hm₂
              (compWeight L a₁) Fk₂ E₂ (F₁₂ (σp₂ w, Θ))
        (Sol₂ (σp₂ w, flEdat (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Hm₂ (F₁₂ (σp₂ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁₂ (σp₂ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w))
                (barField (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁₂
                  (σp₂ w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁₂ (σp₂ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w))
                (barField (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁₂
                  (σp₂ w, Θ)).1) (unitQ (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ₂)
    (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hp : (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2) :
    evTerm cI' Ga m₀ (σ '' X₁) Gf₂ (σ '' Y) (clipRaw (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁)))) (actField σ p.1, actField σ p.2)) =
      evTerm cI Ga m₀ X₁ Gf Y (clipRaw (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p) := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨⟨S⟩, hU, ⟨τ, hidx, hchi, hbox, hqset, hτ1, hτc⟩, ⟨τb, hbidx, hblayer, hbump, hbbase⟩,
    ⟨u, hu⟩⟩ := localB_collar_symmData hk hm₁ hσ hYp hYp₂
  have hbs : L ^ (k + 1) ∣ cellSide L m₀ m₁ (k + 1) := pow_dvd_pow L (by omega)
  obtain ⟨Sk⟩ := nonempty_latSymm_of_mem_symGroupBy hbs hσ (mem_Ω_iff_of_image hΩk)
  obtain ⟨Sj⟩ := nonempty_latSymm_of_mem_symGroupBy hbs hσ (mem_Ω_iff_of_image hΩj)
  obtain ⟨Sm⟩ := nonempty_latSymm_of_mem_symGroupBy hbs hσ (mem_Ω_iff_of_image hΩm)
  obtain ⟨hKu, hγu⟩ := hKγ u hu
  have hww' : ∀ w' P, Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w') (τ P) =
      Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σp (w' ∘ κι)) P := by
    intro w' P
    by_cases hP : P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx
    · exact hww w' P (τ P) hP ((hidx P).2 hP) (hτ1 P) (hτc P hP)
    · have hP' : τ P ∉ (coverOf (GsSpec.localB (k + 1) hk Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx := fun h => hP ((hidx P).1 h)
      unfold Dec2.extS
      simp only [hP, hP', ↓reduceDIte]
  exact localB_eTermHat_evTerm_lat Y hb₁ hbC hk Yp Yp₂ hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj
    hκ hM hMX hnum hj hmarD hαD hsm cc hcψ hδ₁ hP hq colk colj dsX₀ hN hF hHm hFkan hFk hE
    hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hEb hP₂ hq₂ colk₂ colj₂ dsX₀₂ hN₂ hF₂ hHm₂
    hFkan₂ hFk₂ hE₂ hF₁an₂ hF₁₂ hSolan₂ hSol₂ hσan₂ hσκ₂ hσ1₂ hKc₂ hKb₂ hγ₂ hEb₂ S Sk Sj Sm hU
    hidx hchi hbox hqset hbidx hblayer hbump hbbase hu Sa Pa κι hcI hcI1 hww' hEr hKu hγu hεseq
    Gf hGf Gf₂ hGf₂ p hp

end LocalBPaving

end Balaban.Localization
