/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyGenLabelAct
public import Balaban.Fluctuation.LocalClassDensityFamilyGenAmp

/-!
# The activity family on the small radius (`LocalClassDensityFamilyRedLabelAct`)

`classActivityFamily_labelAct_gen` takes the bound of the activities on the whole disc
`‖u‖ < a` as the sum of the label bounds.  Here the bound of the activities on the disc `‖u‖ < a`
is the sum multiplied by `a / a′`, `a′ = δ₁ / (2 markedRad)` (Schwarz lemma at the radius `a′`,
`classActivityFamily_amplitude_gen`), which is small for `markedRad ∝ β_k^{-1/2}` small.  The
Schwarz lemma holds for the parameters of `physV`, so the family is the activity cut off outside
`physV`; it agrees with `H` on `physV`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section ActFamilyRed

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The activity family of a generic label functional with the amplitude of the small radius.**
Under the hypotheses of `classActivityFamily_labelAct_gen`, but with the numerical condition
`hnumR` on the bound `(a / a′) ∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{m₀}(Y)}`
of the activities on `‖u‖ < a` (`a′ = δ₁ / (2 markedRad)`, `2 a markedRad < δ₁`), the activities
on `physV` are those of one `LabelAct` family of amplitude `ε_C`, analytic, continuous, holomorphic
and local as in `classActivityFamily_fields_gen`. -/
theorem classActivityFamily_labelAct_red {ι : Type*} [Fintype ι]
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
    (hmr : 0 < markedRad d L N k a₁ κ cψ cc)
    (hsa : 2 * a * markedRad d L N k a₁ κ cψ cc < δ₁)
    (hnumR : ∀ Y ∈ 𝒴C, a / (δ₁ / (2 * markedRad d L N k a₁ κ cψ cc)) *
      (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y)
      else 0) ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y)) :
    ∃ A : physParam N S → ℂ → LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj)
        (S.blockSplit 1 hp).Ωb εC κH κ0 (K0 d L κ0),
      (∀ θ ∈ physV S a₁ ν eps, ∀ u Y, (A θ u).H Y = H θ Y u) ∧
      (∀ Y Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A r.1 r.2).H Y Φ)
        (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
      (∀ Y, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, Continuous ((A θ u).H Y)) ∧
      (∀ θ ∈ physV S a₁ ν eps, ∀ Y Φ,
        DifferentiableOn ℂ (fun u => (A θ u).H Y Φ) (Metric.ball (0 : ℂ) a)) ∧
      (∀ Z : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
        physRestrict (N := N) Z (physIncl N S θ) = physRestrict Z (physIncl N S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C},
          Y.1 ⊆ Yhat Set.univ Z → (A θ (s : ℂ)).H Y = (A θ' (s : ℂ)).H Y) := by
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hm1).trans hN
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hδ₁ : 0 < δ₁ := lt_of_le_of_lt (by positivity) hsa
  have haa' : a < δ₁ / (2 * markedRad d L N k a₁ κ cψ cc) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hab' : (δ₁ / (2 * markedRad d L N k a₁ κ cψ cc) + 0) * markedRad d L N k a₁ κ cψ cc < δ₁ :=
    markedRad_radius_admissible d L N k a₁ κ cψ cc hδ₁ hmr
  obtain ⟨hmeas, hdep, hbd, hhol, hcont, hdiff, hloc⟩ := classActivityFamily_fields_gen S hb₁ hbC
    Eτ Bτ hBτ hβ jL XL Gk Gj X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt
    hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hN hm1 hd Zm hρ
    hρc hp ha1 hbb hab 𝒴C h𝒴 H hH
  -- the same activity at the radius `a′`
  obtain ⟨H', hH'⟩ : ∃ H' : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ,
      ∀ θ Y u Φ, H' θ Y u Φ = if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < δ₁ / (2 * markedRad d L N k a₁ κ cψ cc) then
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
      else 0 :=
    ⟨fun θ Y u Φ => if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < δ₁ / (2 * markedRad d L N k a₁ κ cψ cc) then
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
      else 0, fun _ _ _ _ => rfl⟩
  have hamp := classActivityFamily_amplitude_gen S hb₁ hbC Eτ Bτ hBτ hβ jL XL Gk Gj X₀ X₁f 𝒦X
    hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁
    hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hN hm1 hd Zm hρ hρc hp (ha1.trans haa') le_rfl hab'
    𝒴C h𝒴 H' hH'
  have hnn : ∀ Y : {Y // Y ∈ 𝒴C}, 0 ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y.1) :=
    fun Y => le_trans (mul_nonneg (div_nonneg ha0.le (div_nonneg hδ₁.le (by positivity)))
      (Finset.sum_nonneg fun τ _ => by
        split_ifs
        · have := hBτ τ
          positivity
        · exact le_rfl)) (hnumR Y.1 Y.2)
  -- the amplitude on the disc `‖u‖ < a`
  have hsmall : ∀ θ ∈ physV S a₁ ν eps, ∀ (Y : {Y // Y ∈ 𝒴C}) Φ u, ‖H θ Y u Φ‖ ≤
      εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y.1) := by
    intro θ hθ Y Φ u
    by_cases hu : ‖u‖ < a
    · have hu' : ‖u‖ < δ₁ / (2 * markedRad d L N k a₁ κ cψ cc) := hu.trans haa'
      have h1' := hamp θ hθ Y Φ u a hu.le haa'
      have heq : H θ Y u Φ = H' θ Y u Φ := by
        rw [hH, hH']
        by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps
        · simp only [hc, hu, hu', and_self, ite_true]
        · simp only [hc, false_and, ite_false]
      rw [heq]
      exact h1'.trans (hnumR Y.1 Y.2)
    · rw [hH]
      simp only [hu, and_false, ite_false, norm_zero]
      exact hnn Y
  obtain ⟨H1, hH1⟩ : ∃ H1 : physParam N S → {Y // Y ∈ 𝒴C} → ℂ →
      (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ, ∀ θ Y u,
      H1 θ Y u = if θ ∈ physV S a₁ ν eps then H θ Y u else fun _ => 0 :=
    ⟨fun θ Y u => if θ ∈ physV S a₁ ν eps then H θ Y u else fun _ => 0, fun _ _ _ => rfl⟩
  have hH1p : ∀ θ ∈ physV S a₁ ν eps, ∀ Y u, H1 θ Y u = H θ Y u := fun θ hθ Y u => by
    rw [hH1]; simp [hθ]
  refine ⟨fun θ u => ⟨fun Y => H1 θ Y u, fun Y => ?_, fun Y => ?_, fun Y Φ => ?_,
    fun b' => entropy_thick hN1 le_rfl 𝒴C h𝒴dj hκ0 b'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hθ : θ ∈ physV S a₁ ν eps
    · rw [hH1p θ hθ]; exact hmeas θ Y u
    · rw [hH1]; simp only [hθ, ↓reduceIte]; exact measurable_const
  · by_cases hθ : θ ∈ physV S a₁ ν eps
    · rw [hH1p θ hθ]; exact hdep θ Y u
    · rw [hH1]; simp only [hθ, ↓reduceIte]; exact fun _ _ _ => rfl
  · by_cases hθ : θ ∈ physV S a₁ ν eps
    · rw [hH1p θ hθ]; exact hsmall θ hθ Y Φ u
    · rw [hH1]; simp only [hθ, ↓reduceIte, norm_zero]; exact hnn Y
  · intro θ hθ u Y
    exact hH1p θ hθ Y u
  · intro Y Φ
    have hopen : IsOpen (physV S a₁ ν eps) := by
      have hY : Y.1 ∈ Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) := by
        rw [← h𝒴]; exact Y.2
      rw [Finset.mem_biUnion] at hY
      obtain ⟨τ, -, -⟩ := hY
      exact isOpen_physV S a₁ ν eps (hB τ).HBp
    refine (hhol Y Φ).congr (hopen.prod Metric.isOpen_ball) fun r hr => ?_
    show H r.1 Y r.2 Φ = H1 r.1 Y r.2 Φ
    rw [hH1p r.1 hr.1]
  · intro Y θ hθ u hu
    show Continuous (H1 θ Y u)
    rw [hH1p θ hθ]
    exact hcont Y θ hθ u hu
  · intro θ hθ Y Φ
    have : (fun u => H1 θ Y u Φ) = fun u => H θ Y u Φ := funext fun u => by rw [hH1p θ hθ]
    show DifferentiableOn ℂ (fun u => H1 θ Y u Φ) _
    rw [this]
    exact hdiff θ hθ Y Φ
  · intro Z θ hθ θ' hθ' hres s hs Y hsub
    show H1 θ Y (s : ℂ) = H1 θ' Y (s : ℂ)
    rw [hH1p θ hθ, hH1p θ' hθ']
    exact hloc Z θ hθ θ' hθ' hres s hs Y hsub
