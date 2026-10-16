/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassLatHat

/-!
# Lattice covariance of the local terms on the class domain (W811 checklist item 9)

`localB_eTermHat_evTerm_lat`: the term of the polymer `Y` recomputed on `𝔹 = 𝔹_{t}(Y⁺)`
(`localB_eTermHat_evTerm_xiFieldDom`) and the term of the polymer `σ Y` recomputed on
`𝔹' = 𝔹_{t}(Y'⁺)` agree at the pair `(σ Ψ, σ h)` and the pair `(Ψ, h)` of the class domain of `𝔹`:

`evTerm c' (σ X₁) G' (σ Y) (clipRaw 𝔹' (σ Ψ, σ h)) = evTerm c X₁ G Y (clipRaw 𝔹 (Ψ, h))`,

for lattice symmetries `σ` between the generating sets of the two terms (`𝔹 → 𝔹'`,
`𝔹_k(X) → 𝔹'_k`, `𝔹_j(X) → 𝔹'_j`, `H⁻ → H'⁻`; `LatSymm`), the transport of the covers of `𝔹`, `𝔹'`
(`τ`), of their blocks (`τb`) and of their unit points (`u`), a symmetry of the ambient expansion
(`LatSymm Ga Ga σ`, `PolymerSymm Ga m₀ σ τa`, relabelling `κ` of the parameters), corresponding
parameter maps (`hww`), an old term with `E'(σ r) = E(r)` on the chart of `𝔹_j(X)` (`hEr`), and the
images `K'`, `γ'` of `K`, `γ` under the relabelling of the unit points (`hKu`, `hγu`).

The symmetry data are hypotheses: their existence for the paving group and the local generating
sets is a separate (geometric) statement.  The proof chains `clipRaw_act_pair`, `evTerm_relabel`
(the ambient expansion), `localHat_integral_sym_pair` (the `ψ̂`-integral) and
`eTermFun_sym_cover_pair` (the old-term functional); the analyticity of the slices in the
parameters is `localB_eTermHat_integral`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.Localization.DecEquiv
  Balaban.Localization.DetDecCov Balaban.Localization.DetUnitIncidence MeasureTheory Finset Matrix

section LocalBLat

open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk Gk₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj Gj₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm Hm₂ : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}

/-- **Lattice covariance of the term of the local class recomputed on `𝔹 = localB t … Y⁺`, on the
class domain** (W811 checklist item 9; the clause `eucE` of the successor class for the E-part,
before the y-labels).  See the module docstring for the hypotheses. -/
theorem localB_eTermHat_evTerm_lat {ι ι' : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq ι']
    [Fintype ι'] {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa}
    {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)} {cI' : ι' → ℕ × CTorus d L N₁ m₁ (k + 1)} {m₀ : ℕ}
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ} (ht : t ≤ k + 1)
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
    (hP : Precedes Gk (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    (hF : FlSetting N (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
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
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))) (D : BgData (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σp : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))} (hσan : ∀ w, AnalyticAt ℂ σp w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f → σp w ⟨P, hP⟩ = 1)
    {γ : Measure (unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)} {K : Set (unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ Bd)
    (hP₂ : Precedes Gk₂ (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) (hq₂ : Precedes Gj₂ Gk₂)
    (colk₂ : ∀ z ∈ collar Gk₂, z ∈ (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1) (colj₂ : ∀ z ∈ collar Gj₂, z ∈ Gk₂.Ω 1)
    {X₀₂ X₁f₂ : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀₂ : ∀ x ∈ dataSites Gk₂, x ∈ X₀₂)
    (hN₂ : ∀ x ∈ X₀₂, x ∈ (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f₂)
    (hF₂ : FlSetting N (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Hm₂ a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f₂)
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
    {F₁₂ : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an₂ : AnalyticOnNhd ℂ F₁₂ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁₂ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))))) (D : BgData (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁₂ (s, rawOf D) = (φ, α))
    {Sol₂ : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) × Edat Hm₂ N → (Hm₂.Ω 1 × Fin N → ℂ) × (Hm₂.Ω 1 → ℂ)}
    (hSolan₂ : AnalyticOnNhd ℂ Sol₂ {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol₂ : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) × Edat Hm₂ N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm₂ N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ p).1 = dphi Hm₂ (Dec2.decG (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ p).2 ∧
        Small Hm₂ (Sol₂ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm₂ (Sol₂ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm₂ (Sol₂ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm₂.Ω 1 → ℂ, Small Hm₂ δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) Hm₂ (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm₂ (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ p).2))
    {σp₂ : (ι' → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))))} (hσan₂ : ∀ w, AnalyticAt ℂ σp₂ w)
    (hσκ₂ : ∀ w ∈ polydisc (0 : ι' → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σp₂ w P‖ < Real.exp κ)
    (hσ1₂ : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))).parCubes X₁f₂ → σp₂ w ⟨P, hP⟩ = 1)
    {γ₂ : Measure (unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)} {K₂ : Set (unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc₂ : IsCompact K₂) (hKb₂ : ∀ ψ ∈ K₂, ∀ r, |ψ r| ≤ cψ) (hγ₂ : γ₂ K₂ < ⊤)
    (hEb₂ : ∀ r ∈ XiCRaw Gj₂ (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E₂ r‖ ≤ Bd)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} (S : LatSymm (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) σ)
    (Sk : LatSymm Gk Gk₂ σ) (Sj : LatSymm Gj Gj₂ σ) (Sm : LatSymm Hm Hm₂ σ) (hU : UnitBlockPres σ)
    {τ τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hidx : ∀ q, τ q ∈ (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))).cubeIdx ↔ q ∈ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx)
    (hchi : ∀ q x, (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))).chi (τ q) (σ x) = (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))).Qset (τ q) ↔ q' ∈ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).Qset q)
    (hbidx : ∀ q, τb q ∈ blockIdx (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) ↔ q ∈ blockIdx (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))), jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 (σ.symm (τb q).2) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) q.1 q.2)
    {u : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) ≃ unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))}
    (hu : ∀ (y : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (x : CTorus d L N₁ m₁ (k + 1)),
      unitBlock (σ x) = (u y : UnitTorus d L N₁ m₁ k) ↔ unitBlock x = (y : UnitTorus d L N₁ m₁ k))
    (Sa : LatSymm Ga Ga σ) {τa : Equiv.Perm (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (Pa : PolymerSymm Ga m₀ σ τa) (κι : ι ≃ ι') (hcI : ∀ i, cI' (κι i) = τa (cI i))
    (hcI1 : ∀ i, cI i ∈ (coverOf Ga).cubeIdx)
    (hww : ∀ w' P, Dec2.extS (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w') (τ P) =
      Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (σp (w' ∘ κι)) P)
    (hEr : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), E₂ (symRaw σ r) = E r)
    (hKu : ∀ ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ,
      (fun r : unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N => ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) ∈ K₂ ↔
        ψ ∈ K)
    (hγu : Measure.map (fun (ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ) (r : unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) × Fin N) =>
      ψ ((u.prodCongr (Equiv.refl (Fin N))).symm r)) γ = γ₂)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (Gf : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGf : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gf Θ w =
      ∫ ψ in K,
            eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
              (compWeight L a₁) Fk E (F₁ (σp w, Θ))
        (Sol (σp w, flEdat (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σp w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σp w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (σp w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σp w, Θ)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σp w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (σp w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σp w, Θ)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
    (Gf₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι' → ℂ) → ℂ)
    (hGf₂ : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι' → ℂ), Gf₂ Θ w =
      ∫ ψ in K₂,
            eTermFun (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Gj₂ Hm₂
              (compWeight L a₁) Fk₂ E₂ (F₁₂ (σp₂ w, Θ))
        (Sol₂ (σp₂ w, flEdat (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Hm₂ (F₁₂ (σp₂ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁₂ (σp₂ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w))
                (barField (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁₂
                  (σp₂ w, Θ)).1) (unitQ (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁₂ (σp₂ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) (σp₂ w))
                (barField (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁₂
                  (σp₂ w, Θ)).1) (unitQ (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ₂)
    (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hp : (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) p.1 p.2) :
    evTerm cI' Ga m₀ (σ '' X₁) Gf₂ (σ '' Y) (clipRaw (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) (actField σ p.1, actField σ p.2)) =
      evTerm cI Ga m₀ X₁ Gf Y (clipRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) p) := by
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have hcd₂ := localB_coverData ht Yp₂ hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  have hΦ : ∀ (bg : ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) × ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)) δφ u',
      (bg, δφ, u') ∈ FlRealLC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((S.fld bg.1, S.mul bg.2), Sm.fld δφ, symU σ u') ∈
        FlRealLC (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Hm₂ a₁ ν BG κ eps X₁f₂ BG₂ δ₁ →
      eTermFun (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) Gk₂ Gj₂ Hm₂ (compWeight L a₁) Fk₂ E₂ (S.fld bg.1, S.mul bg.2) (Sm.fld δφ)
        (symU σ u') =
      eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm (compWeight L a₁) Fk E bg δφ u' := fun bg δφ u' h1 h2 =>
    eTermFun_sym_cover_pair (t := (bg, δφ, u')) hb₁ hbC hS hcd.1 hcd.2.1 hcd.2.2.1 hcd₂.1
      hcd₂.2.1 hcd₂.2.2.1 hMM ha₁0 HBp HBk HBj hP hq colk colj hP₂ hq₂ colk₂ colj₂ hκ hM hnum
      dsX₀ hN dsX₀₂ hN₂ hcd.2.2.2.1 hcd.2.2.2.2 hj hF hF₂ hFk hFk₂ S Sk Sj Sm hEr h1 h2
  have hp' : XiDom (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) (εseq (k + 1)) p.1 p.2 := hp
  obtain ⟨D, hD, hDu⟩ := clipRaw_mem_xiCRaw_of_xiDom hεseq hp'
  rw [clipRaw_act_pair S p, hDu]
  have hD' := xiCData_sym_pair S hD
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hint := localB_eTermHat_integral hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP hq
    colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hE hmarD hαD hsm cc hcψ hδ₁ hF₁an hF₁
    hSolan hSol hσan hσκ hσ1 hKc hKb hγ hEb
  have hint₂ := localB_eTermHat_integral hb₁ hbC ht Yp₂ hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP₂
    hq₂ colk₂ colj₂ hκ hM hMX hnum dsX₀₂ hN₂ hj hF₂ hHm₂ hFkan₂ hFk₂ hE₂ hmarD hαD hsm cc hcψ hδ₁
    hF₁an₂ hF₁₂ hSolan₂ hSol₂ hσan₂ hσκ₂ hσ1₂ hKc₂ hKb₂ hγ₂ hEb₂
  have hGfa : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι → ℂ) => Gf q.1 q.2)
      (XiCRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := by
    simp only [hGf]
    exact hint.1
  have hGfa₂ : AnalyticOnNhd ℂ
      (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι' → ℂ) => Gf₂ q.1 q.2)
      (XiCRaw (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        polydisc (0 : ι' → ℂ) (fun _ => Real.exp κ)) := by
    simp only [hGf₂]
    exact hint₂.1
  have hmem : rawOf D ∈ XiCRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have hmem₂ : symRaw σ (rawOf D) ∈ XiCRaw (GsSpec.localB t ht Yp₂ (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1) 1 eps :=
    ⟨S.sym D, hD', rfl⟩
  refine evTerm_relabel cI cI' κι hR Pa Sa hcI hcI1 X₁ Y
    (analytic_slice (Fn := Gf) hGfa hmem) (analytic_slice (Fn := Gf₂) hGfa₂ hmem₂)
    fun s hs => ?_
  have hsp : s ∈ polydisc (0 : ι' → ℂ) (fun _ => Real.exp κ) := unitCube_subset_polydisc hR hs
  have hsκ : s ∘ κι ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := fun i => by
    simpa using hsp (κι i)
  exact localHat_integral_sym_pair hk1 ha₁ ha₂ hS hcd.1 hcd₂.1 HBp hκ hM hMX (Cchi_nonneg d L)
    hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
    hF.hPmp hHm hF₂.hPmp hF₁ hF₁₂ hSol hSol₂ hσκ hσ1 hσ1₂ S Sm hU hidx hchi hbox hqset hbidx
    hblayer hbump hbbase hu hΦ hKc hKb hKu hγu Gf hGf Gf₂ hGf₂ hD hsκ (hww s)

end LocalBLat

end Balaban.Localization
