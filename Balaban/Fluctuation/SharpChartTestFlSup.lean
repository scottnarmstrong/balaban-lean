/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SharpChartTestSup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The point facts of Lemma DL with the fluctuation, for a sup-separated parent (WIDEGEN route A)

`point_facts_fl_of_one_le` (`Localization/I5FluctFacts.lean`) is stated for a parent `𝔹_{k+1}`
with `BgSetting` (built on `DGSetting` and `r₀ M₁ ≤ ϱ - 1`).  Here the same facts are proved for the
decoupled background field of the pair `(coverOf 𝔹_{k+1}, 𝔹_{k+1})` (Theorem I-4b in cover form),
from the cover data of `Localization/I5Cover.lean`; the fluctuation hypotheses are the landed
`FlSetting` (which does not involve `DGSetting`).  Both versions are applications of the common
fluctuation step `point_facts_fl_of_bg`.

* `point_facts_fl_sup_of_one_le`: the point facts with the fluctuation for a sup-separated,
  cube-aligned parent (`point_facts_sup_of_one_le`, `Dec2.i4b_exists_unique`,
  `point_facts_fl_of_bg`);
* `point_facts_fl_xiDom_sup_of_le`: the corrected chart test of P3 (4.37) with the fluctuation,
  `ε' + K₂' δ₃ + K₂' δ_fl ≤ ε_j`, for such a parent;
* `localB_point_facts_fl_xiDom`: **the instance `𝔹_{k+1} = localB …`** at the separation
  `ϱ = 5 L M₁` and the collar `r₀ = 4 d L³ + L`, for every fluctuation generating set `H⁻` with
  `FlSetting` (the local `H⁻ = 𝔹_k(Y)` of `Fluctuation/LocalFluctGen.lean` has `H⁻ ≺ 𝔹_{k+1}`,
  `FootLocal` and `RowInHat`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.LargeField Finset Matrix

section Sup

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- **The point facts of Lemma DL with the fluctuation for a sup-separated parent** (cover form of
`point_facts_fl_of_one_le`).  For the decoupled background field of the pair
`(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, `𝔹_{k+1}` sup-separated and cube aligned (no `DGSetting`), with the
target bound `T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1` in place of `r₀ M₁ ≤ ϱ - 1`, realizable data
`Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')`, `s` in the polydisc and a layer-constant fluctuation `ψ'` with
`|ψ'| < δ₁`: the composite of P3 (4.32) is computed through `F₁` (Theorem I-4b for the cover),
`Sol` and `F_k`, the composed datum of `𝔹_k(X)` lies in `Ξ^c_K(𝔹_k(X); 1, ε₃)` and the argument of
the term in `Ξ^c_j(𝔹_j(X); b, ε₃)`, `ε₃ = b² ε' + K₂' δ₃ + K₂' δfl`, `1 ≤ b ≤ C₀`. -/
theorem point_facts_fl_sup_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ K)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
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
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁)
    (hψc : IsLayerConstant Hm ψ') :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ),
      Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
        (flEdat Gp Hm (φ, α) D.Ψ ψ') ∧
      (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ ∧
      XiCData Gk (compWeight L a₁) ν K 1
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol s (rawOf D, ψ') =
        rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) ∧
      XiCData Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) := by
  obtain ⟨hδ0, hδ0', hδ1, hνε, hDom, -⟩ := hnum.domain HBp hD
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  -- the background facts (cover form)
  obtain ⟨φ, α, hI, hFeq, hst, -, -, -⟩ := point_facts_sup_of_one_le hb₁ hbC hS S hG hSS hMM ha₁
    HBp HBk HBj hP hq colk colj hκ hM hnum dsX₀ hN hT hr₀ hj hF₁ hFk hs hs1 hD
  obtain ⟨φ', α', -, hu', -, -, hbb⟩ := Dec2.i4b_exists_unique hS S HBp hκ.le hM hsle hδ0 le_rfl
    hδ0' hδ1 hνε hDom
  obtain ⟨rfl, rfl⟩ := hu' φ α hI
  -- the fluctuation step
  obtain ⟨δφ, hstrict, hSolφ, hX3, hrawD, hD2, hXj⟩ := point_facts_fl_of_bg (F₁ := F₁) hb₁ hbC
    hS.fam.2.1 ha₁ HBp HBk HBj hP hq colj hnum hj hF hFk hSol hs hD hFeq hbb hst hψ hψc
  exact ⟨φ, α, δφ, hI, hFeq, hstrict, hSolφ, hX3, hrawD, hD2, hXj⟩

/-- **The corrected chart test with the fluctuation for a sup-separated parent** (cover form of
`point_facts_fl_xiDom_of_le`, P3 (4.37)).  Under the hypotheses of `point_facts_fl_sup_of_one_le`
the argument of an old term lies in the class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever
`ε' + K₂' δ₃ + K₂' δ_fl ≤ ε_j`. -/
theorem point_facts_fl_xiDom_sup_of_le {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ K)
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
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
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁)
    (hψc : IsLayerConstant Hm ψ') {εj : ℝ}
    (hε : eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ εj) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ),
      Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      (Sol (s, flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ ∧
      D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol s (rawOf D, ψ') =
        rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) ∧
      XiDom Gj (compWeight L a₁) ν j εj
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)).Ψ
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)).h := by
  obtain ⟨φ, α, δφ, hI, hFeq, -, hSolφ, -, hD1, hD2, hX⟩ := point_facts_fl_sup_of_one_le le_rfl
    (one_le_scaledC0 d) hS S hG hSS hMM ha₁ HBp HBk HBj hP hq colk colj hκ hM hnum dsX₀ hN hT hr₀
    hj hF hF₁ hFk hSol hs hs1 hD hψ hψc
  have hε' : (1 : ℝ) ^ 2 * (1 ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ≤ εj := by
    simpa using hε
  exact ⟨φ, α, δφ, hI, hFeq, hSolφ, hD1, hD2, Fluctuation.xiDom_of_xiCData_of_one_le le_rfl hε' hX⟩

end Sup

section LocalB

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a₁ ν : ℝ}

/-- **The chart test of P3 (4.37) with the fluctuation for the literal local generator**
`𝔹_{k+1} = localB t ht Y …` at the separation `ϱ = 5 L M₁` (P3 (4.4)-(4.6)) and the collar
`r₀ = 4 d L³ + L` (`r₁ = 1`).  For the decoupled background field of the pair
`(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, a fluctuation generating set `H⁻` with the landed `FlSetting`
(in particular `H⁻ ≺ 𝔹_{k+1}` and `FootLocal (coverOf 𝔹_{k+1}) H⁻`), realizable data
`Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')`, `s` in the polydisc and a layer-constant fluctuation `ψ'` with
`|ψ'| < δ₁`, the composite of P3 (4.32) is computed through `F₁`, `Sol`, `F_k`, and the argument
of an old term lies in the class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever
`ε' + K₂' δ₃ + K₂' δ_fl ≤ ε_j`.  The cover geometry needs `N₁ > 5`, `M₁ = L^{m₁} ≥ 4 L²` and
`2 d log L ≤ (γ_A/16)(5 L M₁ - 1)`. -/
theorem localB_point_facts_fl_xiDom {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν) (HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
    (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1)
    (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ K, Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ *
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ K) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃
      Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
      RawData d L (N₁ * L ^ m₁) K N →
      ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
          (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
      Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Y
            (le_refl (minSep L (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {s : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))}
    (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K)
      (hP : P ∈ (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))).parCubes X₁f →
        s ⟨P, hP⟩ = 1)
    {D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N}
    (hD : XiCData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν K 1
      eps D)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁)
    (hψc : IsLayerConstant Hm ψ') {εj : ℝ}
    (hε : eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ εj) :
    ∃ (φ : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
      (α : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)
      (δφ : Hm.Ω 1 × Fin N → ℂ),
      Dec2.IsDecBg (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
        (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
        (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      (Sol (s, flEdat (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Hm (φ, α) D.Ψ
        ψ')).1 = δφ ∧
      D1rawFl (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk Hm (compWeight L a₁) F₁
          Sol s (rawOf D, ψ') =
        rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc) ∧
      D2raw Gk Gj (compWeight L a₁) Fk
          (rawOf (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)) ∧
      XiDom Gj (compWeight L a₁) ν j εj
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)).Ψ
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
            (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc))
          (flDatum Gk hP hF.hPm (compWeight L a₁) φ δφ D ψ' hψc)).h := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨hT1, hT2⟩ := target_le_minSep (d := d) (m₁ := m₁) (by omega : 1 ≤ L)
  exact point_facts_fl_xiDom_sup_of_le hS
    (localB_coverBase ht Y le_rfl hN₁ hm₁ hMM HBp.hd hL HBp.mass HBp.massLe HBp.weights hag)
    (localB_cubeAligned ht Y le_rfl hm₁) (localB_supSep ht Y le_rfl) hMM ha₁ HBp HBk HBj hP hq
    colk colj hκ hM hnum dsX₀ hN (by rw [hT1]; exact hT2)
    (by linarith [show (0 : ℝ) ≤ L from by positivity]) hj hF hF₁ hFk hSol hs hs1 hD hψ hψc hε

end LocalB

end Balaban.Localization
