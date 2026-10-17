/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyGenAct

/-!
# The activity family of a generic label functional as a `LabelAct` (`LocalClassDensityFamilyGenLabelAct`)

The generic version of `classActivityFamily_labelAct` (`LocalClassDensityFamilyAct`): under the
hypotheses of `classActivityFamily_fields_gen`, the entropy rate `κ₀' ≥ a_ent + 1` and the
numerical condition `hnumH` (the bound of `classActivityFamily_fields_gen` is at most
`ε_C e^{-κ_H d^cov_1(Y)}` on every domain), the activities form one `LabelAct` family on the
labels `thickLabels 𝒴C` with the entropy constant `K₀(κ₀')`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section ActFamilyGenLabel

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The activity family of the inherited energy as one `LabelAct` family.**  Under the hypotheses
of `classActivityFamily_fields_gen`, the entropy rate `κ₀' ≥ a_ent + 1` and the numerical condition
`hnumH` (the bound of `classActivityFamily_fields_gen` is at most `ε_C e^{-κ_H d^cov_1(Y)}` on every
domain of `𝒴C`), the activities `H θ · u` are the activities of one family
`A : physParam → ℂ → LabelAct (thickLabels 𝒴C) … ε_C κ_H κ₀' K₀(κ₀')` on the labels of the domains
of `𝒴C` (site `Y`, size `d^cov_1(Y)`), with the entropy constant of `entropy_thick`. -/
theorem classActivityFamily_labelAct_gen {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d)
    (Zm : Finset (unitPts S.G')) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    {εC κH κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    (hnumH : ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y)
      else 0) ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y)) :
    ∃ A : physParam N S → ℂ → LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj)
        (S.blockSplit 1 hp).Ωb εC κH κ0 (K0 d L κ0),
      ∀ θ u Y, (A θ u).H Y = H θ Y u := by
  obtain ⟨hmeas, hdep, hbd, -, -, -, -⟩ := classActivityFamily_fields_gen S hb₁ hbC Eτ Bτ hBτ
    hβ jL XL Gk Gj X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hN hm1 hd Zm hρ
    hρc hp ha1 hbb hab 𝒴C h𝒴 H hH
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hm1).trans hN
  refine ⟨fun θ u => ⟨fun Y => H θ Y u, fun Y => hmeas θ Y u, fun Y => hdep θ Y u,
    fun Y Φ => (hbd θ Y u Φ).trans (hnumH Y.1 Y.2),
    fun b' => entropy_thick hN1 le_rfl 𝒴C h𝒴dj hκ0 b'⟩, fun _ _ _ => rfl⟩

end ActFamilyGenLabel

end Balaban.Fluctuation
