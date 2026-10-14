/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SharpChartTest
public import Balaban.Localization.I5Cover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chart test of P3 (4.37) for the literal local generator (WIDEGEN route A)

`point_facts_xiDom_of_le` (`Fluctuation/SharpChartTest.lean`) is the corrected chart test of
Lemma DL for a parent `𝔹_{k+1}` with `BgSetting` (built on `DGSetting` and `r₀ M₁ ≤ ϱ - 1`).  Here
it is proved for a sup-separated, cube-aligned parent with the cover data of
`Localization/I5Cover.lean`, and instantiated at the literal local generator of P3 (4.4)-(4.6).

* `point_facts_xiDom_sup_of_le`: the chart test for the decoupled background field of the pair
  `(coverOf 𝔹_{k+1}, 𝔹_{k+1})` (`point_facts_sup_of_one_le` at `b = 1`);
* `localB_point_facts_xiDom`: **the instance `𝔹_{k+1} = localB …`** at the separation
  `ϱ = 5 L M₁` of P3 and the collar `r₀ = 4 d L³ + L` (P3's `r₁ = 1`): for realizable data
  `Θ ∈ Ξ^c(𝔹_{k+1}; 1, ε')` and `s` in the polydisc, the composite of Lemma DL is computed through
  `F₁`, `F_k`, and the argument of an old term lies in `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever
  `ε' + K₂' δ₃ ≤ ε_j`.  The cover base is `localB_coverBase`; the remaining hypotheses are those
  of `BgSetting` other than `DGSetting` and `r₀ M₁ ≤ ϱ - 1`, and the separation condition
  `2 d log L ≤ (γ_A/16)(5 L M₁ - 1)` of the cover geometry.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.LargeField Finset Matrix

section Test

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {a₁ ν Kc Cx : ℝ}

/-- **The corrected chart test for a sup-separated parent** (cover form of
`point_facts_xiDom_of_le`, P3 (4.35)-(4.37)).  For the decoupled background field of the pair
`(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, realizable data `Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` and `s` in the
polydisc, the composite of Lemma DL is computed through `F₁`, `F_k`, and the argument of an old
term lies in the class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever `ε' + K₂' δ₃ ≤ ε_j`. -/
theorem point_facts_xiDom_sup_of_le {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
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
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) {εj : ℝ}
    (hε : eps + xiK2 d L N * δ₃ ≤ εj) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      D1raw Gp Gk (compWeight L a₁) F₁ (s, rawOf D) =
        rawOf (composeData hP (compWeight L a₁) φ D) ∧
      D2raw Gk Gj (compWeight L a₁) Fk (rawOf (composeData hP (compWeight L a₁) φ D)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)) ∧
      XiDom Gj (compWeight L a₁) ν j εj
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)).Ψ
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)).h := by
  obtain ⟨φ, α, hI, hFeq, -, hD1, hD2, hX⟩ := point_facts_sup_of_one_le le_rfl
    (one_le_scaledC0 d) hS S hG hSS hMM ha₁ HBp HBk HBj hP hq colk colj hκ hM hnum dsX₀ hN hT hr₀
    hj hF₁ hFk hs hs1 hD
  have hε' : (1 : ℝ) ^ 2 * (1 ^ 2 * eps + xiK2 d L N * δ₃) ≤ εj := by
    simpa using hε
  exact ⟨φ, α, hI, hFeq, hD1, hD2, Fluctuation.xiDom_of_xiCData_of_one_le le_rfl hε' hX⟩

end Test

section LocalB

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
  {a₁ ν : ℝ}

/-- **The chart test of P3 (4.37) for the literal local generator** `𝔹_{k+1} = localB t ht Y …`
at the separation `ϱ = 5 L M₁` (P3 (4.4)-(4.6)) and the collar `r₀ = 4 d L³ + L` (`r₁ = 1`).  For
the decoupled background field of the pair `(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, realizable data
`Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` and `s` in the polydisc (`‖s_P‖ < e^κ`, `s = 1` off the parameter
cubes of `X₁`), the composite of Lemma DL is computed through `F₁`, `F_k`, and the argument of an
old term lies in the class domain `Ξ^c_j(𝔹_j(X); 1, ε_j)` whenever `ε' + K₂' δ₃ ≤ ε_j`.  The cover
geometry needs `N₁ > 5`, `M₁ = L^{m₁} ≥ 4 L²` and `2 d log L ≤ (γ_A/16)(5 L M₁ - 1)`. -/
theorem localB_point_facts_xiDom {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
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
    {j : ℕ} (hj : j ≤ K)
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
    {s : Dec2.DecParams (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))}
    (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K)
      (hP : P ∈ (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁))))).parCubes X₁f →
        s ⟨P, hP⟩ = 1)
    {D : BgData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) N}
    (hD : XiCData (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν K 1
      eps D) {εj : ℝ} (hε : eps + xiK2 d L N * δ₃ ≤ εj) :
    ∃ (φ : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
      (α : (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))))
        (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
        (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      D1raw (GsSpec.localB t ht Y (le_refl (minSep L (L ^ m₁)))) Gk (compWeight L a₁) F₁
          (s, rawOf D) = rawOf (composeData hP (compWeight L a₁) φ D) ∧
      D2raw Gk Gj (compWeight L a₁) Fk (rawOf (composeData hP (compWeight L a₁) φ D)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)) ∧
      XiDom Gj (compWeight L a₁) ν j εj
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)).Ψ
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)).h := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  obtain ⟨hT1, hT2⟩ := target_le_minSep (d := d) (m₁ := m₁) (by omega : 1 ≤ L)
  exact point_facts_xiDom_sup_of_le hS
    (localB_coverBase ht Y le_rfl hN₁ hm₁ hMM HBp.hd hL HBp.mass HBp.massLe HBp.weights hag)
    (localB_cubeAligned ht Y le_rfl hm₁) (localB_supSep ht Y le_rfl) hMM ha₁ HBp HBk HBj hP hq
    colk colj hκ hM hnum dsX₀ hN (by rw [hT1]; exact hT2)
    (by linarith [show (0 : ℝ) ≤ L from by positivity]) hj hF₁ hFk hs hs1 hD hε

end LocalB

end Balaban.Localization
