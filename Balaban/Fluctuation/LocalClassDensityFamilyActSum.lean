/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyAct
public import Balaban.Fluctuation.LocalClassDensityValFamily

/-!
# The sum identity of the activity family of the inherited energy (`LocalClassDensityFamilyActSum`)

For the labels of the class (`𝒯E`, the label set of `sum_classLabels_E_eq_Edens`) with their
settings and given maps, and the activities `H` of `LocalClassDensityFamilyAct` (mask `blockU z`,
`Hm = stepG`, `cc = β_k^{-1/2}`):

* `StepSetting.JointRep.classActivityFamily_sum_eq`: at every datum `D` of the chart, every
  `s ∈ [0, 1]` and every real field `x` with `|x(u)| ≤ ρ`, the sum of the activities at
  `(rawOf D, 0)`, `s` and the block configuration of `x` is
  `ℰ_k(rawOf D, s ψ̂) - ℰ_k(rawOf D, 0)`: label by label, the label value along the line is `β`
  times the sum of the marked terms at the second mark `0` (`classLabel_PJ_masked_eq_flComp` at
  `t = 0` and the sum identity of `classOldMarkedLocal_joint_of`), and the sum over the labels and
  their domains is regrouped by domains.
* `StepSetting.JointRep.classActivityFamily_ae_W1_eq`: `ν_{p₁}`-almost surely,
  `W₁^C(rawOf D, s ψ̂) = W₁^0(rawOf D, s ψ̂) + ∑_Y H (rawOf D, 0) Y s (restr x)`
  (`W1_eq_zeroClass_add_EJ`, `p₁ ≤ ρ`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {eps pp : ℝ} (Jr : S.JointRep eps pp)
  {c BG κ r₀ δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The sum identity of the activity family, with the label charts replaced by any sets
containing the composed step data** (`h𝒮`).  `classActivityFamily_sum_eq_gen` is the case of the
label charts. -/
theorem classActivityFamily_sum_eq_gen_onSet {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, (∀ u, ‖x u‖ ≤ ρ) →
      ∑ Y, H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        Jr.EJ C (rawOf D, (s : ℂ) • yhat x) - Jr.EJ C (rawOf D, 0) := by
  classical
  intro D hD s hs x hx
  have hΘ : rawOf D ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have hsn : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hca : ‖(s : ℂ)‖ < a := lt_of_le_of_lt hsn ha1
  have hhat : S.hatOf 1 ρ hp ((S.blockSplit 1 hp).restr x) = yhat x := S.hatOf_restr 1 hρ hp x hx
  have hyρ : ∀ p, ‖yhat x p‖ ≤ ρ := fun p => by
    show ‖((x p.1 p.2 : ℝ) : ℂ)‖ ≤ ρ
    rw [Complex.norm_real]
    exact (PiLp.norm_apply_le (x p.1) p.2).trans (hx p.1)
  have hyx : ∀ p, ‖yhat x p‖ ≤ cψ := fun p => (hyρ p).trans hρc
  -- the marked term of a label at the second mark `0`, at the datum
  set T : ι → ℂ → Set (CTorus d L N₁ m₁ (k + 1)) → ℂ := fun τ um Y =>
    evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
      (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
        (compWeight L S.a₁) (Fk τ)
        (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) um 0 Y
      (rawOf D, yhat x) with hTdef
  -- the value of one label along the line, at `s' ψ̂`
  have hlab : ∀ τ, ∀ s' : ℂ, ‖s'‖ ≤ 1 →
      Eτ τ (Jr.PJ (jL τ) (rawOf D, s' • yhat x)) =
        (S.β : ℂ) * ∑ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ), T τ s' Y := by
    intro τ s' hs'
    have hum : (‖s'‖ + ‖(0 : ℂ)‖) *
        markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ :=
      mem_markedRadiusSet_of_pos (flCore_of (hB τ) (hF τ)).δ₁_pos hab (hs'.trans ha1.le)
        (by rw [norm_zero]; exact hbb)
    have hw : ∀ p, ‖(s' • yhat x + (0 : ℂ) • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
        S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) p‖ ≤ pp := fun p => by
      rw [zero_smul, add_zero, Pi.smul_apply, smul_eq_mul, norm_mul]
      calc ‖s'‖ * ‖yhat x p‖ ≤ 1 * ρ := mul_le_mul hs' (hyρ p) (norm_nonneg _) zero_le_one
        _ ≤ pp := by rw [one_mul]; exact hρpp.le
    have key := Jr.classLabel_PJ_masked_eq_flComp_gen (Eτ τ) (hj1 τ) (hjk τ) (hlocE τ) (hS τ _)
      (hB τ) (hF τ) hc7 hR hsmR hRs hsmall hnum hnum' hcψ hMX hdm hα hsm hβ hD z x hyx s' 0 hw hum
    rw [zero_smul, add_zero] at key
    rw [key]
    obtain ⟨e1, -⟩ := classOldMarkedLocal_joint_gen_onSet (h𝒮 := h𝒮 τ) hb₁ hbC (Eτ τ) (hBτ τ) hβ (hB τ) (hF τ)
      S.hk1 S.hG S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm (hcov τ) (hX₁ τ)
      hconn hrow (hopt τ) hκ₀ hκdec hκ h1 hlog (hEan τ) (hEbd τ) (hF₁an τ) (hF₁ τ) (hSolan τ) (hSolprop τ) (hFkan τ) (hFk τ) (S.blockU z)
    rw [e1 s' 0 hum D hD (yhat x) hyx]
  -- the activities at the datum
  have hpt : ∀ Y : {Y // Y ∈ 𝒴C},
      H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (T τ (s : ℂ) Y.1 - T τ 0 Y.1) else 0 := by
    intro Y
    rw [hH, ite_eq_left ⟨hΘ, hca⟩, hhat]
  -- regroup by labels
  have hsub : ∀ τ, polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) ⊆ 𝒴C := fun τ => by
    rw [h𝒴]
    exact Finset.subset_biUnion_of_mem (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
      (Finset.mem_univ τ)
  rw [Finset.sum_congr rfl fun Y _ => hpt Y, Finset.sum_coe_sort 𝒴C (fun Y =>
    ∑ τ, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
      (S.β : ℂ) * (T τ (s : ℂ) Y - T τ 0 Y) else 0), Finset.sum_comm]
  have hinner : ∀ τ, (∑ Y ∈ 𝒴C, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
      (S.β : ℂ) * (T τ (s : ℂ) Y - T τ 0 Y) else 0) =
      Eτ τ (Jr.PJ (jL τ) (rawOf D, (s : ℂ) • yhat x)) -
        Eτ τ (Jr.PJ (jL τ) (rawOf D, 0)) := by
    intro τ
    rw [← Finset.sum_subset (hsub τ) (fun Y _ hY => ite_eq_right hY),
      Finset.sum_congr rfl fun Y hY => ite_eq_left hY, ← Finset.mul_sum, Finset.sum_sub_distrib,
      mul_sub, ← hlab τ (s : ℂ) hsn, ← hlab τ 0 (by rw [norm_zero]; exact zero_le_one),
      zero_smul]
  rw [Finset.sum_congr rfl fun τ _ => hinner τ, Finset.sum_sub_distrib]
  rw [hEJ D hD, hEJ D hD]

open Classical in
/-- The generic version of `classActivityFamily_sum_eq` (any label functionals `Eτ`). -/
theorem classActivityFamily_sum_eq_gen {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w))) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, (∀ u, ‖x u‖ ≤ ρ) →
      ∑ Y, H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        Jr.EJ C (rawOf D, (s : ℂ) • yhat x) - Jr.EJ C (rawOf D, 0) :=
  Jr.classActivityFamily_sum_eq_gen_onSet C hb₁ hbC Eτ Bτ hBτ hβ jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X
    hB hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁
    Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' z hρ hρc hρpp hp ha1 hbb
    hab 𝒴C h𝒴 H hH hEJ (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht)


open Classical in
/-- **The sum identity of the activity family at every datum of the chart.**  For the labels of
the class with their settings and given maps (the hypotheses of `classActivityFamily_fields` and of
`classLabel_PJ_masked_eq_flComp`), the activities `H` (formula `hH`, mask `blockU z`), `1 < a` and
`ρ < p⁺`: at every datum `D` of the chart, every `s ∈ [0, 1]` and every real field `x` with
`|x(u)| ≤ ρ`, the sum of the activities at `(rawOf D, 0)`, `s` and the block configuration of `x`
is `ℰ_k(rawOf D, s ψ̂) - ℰ_k(rawOf D, 0)`, `ψ̂ = yhat x`. -/
theorem classActivityFamily_sum_eq {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (Gk : 𝒯E → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : 𝒯E → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : 𝒯E → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ : 𝒯E, BgSetting N S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) τ.1.1)
    (hF : ∀ τ : 𝒯E, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ : 𝒯E, CovSetup S.G' C.m₀ τ.1.1 τ.1.2.2 (𝒦X τ))
    (hX₁ : ∀ τ : 𝒯E, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ : 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ τ.1.2.2) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ : 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1.1 τ.1.2.2) (compWeight L S.a₁) S.ν τ.1.1 b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2)
    (F₁ : 𝒯E → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ : 𝒯E, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : 𝒯E → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ : 𝒯E, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ : 𝒯E, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ : 𝒯E, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : 𝒯E) (h : τ.1.1 ≤ k + 1), GsSpecStrong τ.1.1 h τ.1.2.2
      (C.Tm.gs τ.1.1 τ.1.2.2))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, (∀ u, ‖x u‖ ≤ ρ) →
      ∑ Y, H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        Jr.EJ C (rawOf D, (s : ℂ) • yhat x) - Jr.EJ C (rawOf D, 0) := by
  classical
  have hmem𝒯 : ∀ τ : 𝒯E, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (L ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : 𝒯E, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem𝒯 τ).1).1
  have hjk : ∀ τ : 𝒯E, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem𝒯 τ).1).2
  have hXp : ∀ τ : 𝒯E, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem𝒯 τ).2.2.1
  have hy : ∀ τ : 𝒯E, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem𝒯 τ).2.2.2
  have hraw := fun τ : 𝒯E => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀
    S.a₁ S.ν δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  have hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ : 𝒯E,
        C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 (Jr.PJ τ.1.1 (rawOf D, w)).1
          (Jr.PJ τ.1.1 (rawOf D, w)).2 := fun D _ w => by
    unfold StepSetting.JointRep.EJ
    rw [Finset.sum_coe_sort 𝒯E (fun τ => C.Tm.E τ.1 τ.2.1 τ.2.2 (Jr.PJ τ.1 (rawOf D, w)).1
      (Jr.PJ τ.1 (rawOf D, w)).2), h𝒯,
      sum_classLabels_E_eq_Edens C.m₀ C.Tm (fun j => (Jr.PJ j (rawOf D, w)).1)
      (fun j => (Jr.PJ j (rawOf D, w)).2)]
  have key := Jr.classActivityFamily_sum_eq_gen (ι := 𝒯E) (m₀ := C.m₀) C hb₁ hbC
    (fun τ r => C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ
    (fun τ => τ.1.1) (fun τ => τ.1.2.2) hj1 hjk Gk (fun τ => C.Tm.gs τ.1.1 τ.1.2.2)
    (fun τ Ψ Ψ' h h' hag => hcl.localE τ.1.1 τ.1.2.1 τ.1.2.2 Ψ Ψ' h h' hag) X₀ X₁f 𝒦X hB hF hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1)
    (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall
    hnum hnum' z hρ hρc hρpp hp ha1 hbb hab 𝒴C h𝒴 H hH hEJ
  exact key

open Classical in
/-- **The class exponent is the zero-class exponent plus the activities, almost surely, with the
label charts replaced by any sets containing the composed step data** (`h𝒮`).
`classActivityFamily_ae_W1_eq_gen` is the case of the label charts. -/
theorem classActivityFamily_ae_W1_eq_gen_onSet {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
    (hρp : S.p₁ ≤ ρ)
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
        Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) +
          ∑ Y, H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ)
            ((S.blockSplit 1 hp).restr x) := by
  intro D hD s hs
  filter_upwards [S.ae_norm_nuFl hp] with x hx
  rw [Jr.W1_eq_zeroClass_add_EJ C, Jr.classActivityFamily_sum_eq_gen_onSet (h𝒮 := h𝒮) C hb₁ hbC Eτ Bτ hBτ hβ jL XL
    hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1
    hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum
    hnum' z hρ hρc hρpp hp ha1 hbb hab 𝒴C h𝒴 H hH hEJ D hD s hs x
    (fun u => (hx u).le.trans hρp)]

open Classical in
/-- The generic version of `classActivityFamily_ae_W1_eq` (any label functionals `Eτ`). -/
theorem classActivityFamily_ae_W1_eq_gen {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
    (hρp : S.p₁ ≤ ρ) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
        Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) +
          ∑ Y, H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ)
            ((S.blockSplit 1 hp).restr x) :=
  Jr.classActivityFamily_ae_W1_eq_gen_onSet C hb₁ hbC Eτ Bτ hBτ hβ jL XL hj1 hjk Gk Gj hlocE X₀ X₁f
    𝒦X hB hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁
    Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' z hρ hρc hρpp hp ha1 hbb
    hab 𝒴C h𝒴 H hH hEJ hρp
    (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht)


open Classical in
/-- **The class exponent is the zero-class exponent plus the activities, almost surely.**  Under
the hypotheses of `classActivityFamily_sum_eq` and `p₁ ≤ ρ`: at every datum of the chart and every
`s ∈ [0, 1]`, for `ν_{p₁}`-almost every `x`,
`W₁^C(rawOf D, s ψ̂) = W₁^0(rawOf D, s ψ̂) + ∑_Y H (rawOf D, 0) Y s (restr x)`
(`W1_eq_zeroClass_add_EJ`; the support of `ν_{p₁}` is `|x(u)| < p₁`, `ae_norm_nuFl`). -/
theorem classActivityFamily_ae_W1_eq {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (Gk : 𝒯E → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : 𝒯E → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : 𝒯E → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ : 𝒯E, BgSetting N S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) τ.1.1)
    (hF : ∀ τ : 𝒯E, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ : 𝒯E, CovSetup S.G' C.m₀ τ.1.1 τ.1.2.2 (𝒦X τ))
    (hX₁ : ∀ τ : 𝒯E, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ : 𝒯E, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ τ.1.2.2) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ : 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1.1 τ.1.2.2) (compWeight L S.a₁) S.ν τ.1.1 b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2)
    (F₁ : 𝒯E → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ : 𝒯E, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : 𝒯E → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ : 𝒯E, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ)
            (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1)
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ,
          Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
          δα' = (Sol τ p).2))
    (Fk : ∀ τ : 𝒯E, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ : 𝒯E, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ (τ : 𝒯E) (h : τ.1.1 ≤ k + 1), GsSpecStrong τ.1.1 h τ.1.2.2
      (C.Tm.gs τ.1.1 τ.1.2.2))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG d L N₁ m₁ k ϱ)
              (compWeight L S.a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    (hρp : S.p₁ ≤ ρ) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
      Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
        Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, (s : ℂ) • yhat x) +
          ∑ Y, H ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) Y (s : ℂ)
            ((S.blockSplit 1 hp).restr x) := by
  classical
  have hmem𝒯 : ∀ τ : 𝒯E, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (L ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : 𝒯E, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem𝒯 τ).1).1
  have hjk : ∀ τ : 𝒯E, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem𝒯 τ).1).2
  have hXp : ∀ τ : 𝒯E, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem𝒯 τ).2.2.1
  have hy : ∀ τ : 𝒯E, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem𝒯 τ).2.2.2
  have hraw := fun τ : 𝒯E => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀
    S.a₁ S.ν δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  have hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ : 𝒯E,
        C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 (Jr.PJ τ.1.1 (rawOf D, w)).1
          (Jr.PJ τ.1.1 (rawOf D, w)).2 := fun D _ w => by
    unfold StepSetting.JointRep.EJ
    rw [Finset.sum_coe_sort 𝒯E (fun τ => C.Tm.E τ.1 τ.2.1 τ.2.2 (Jr.PJ τ.1 (rawOf D, w)).1
      (Jr.PJ τ.1 (rawOf D, w)).2), h𝒯,
      sum_classLabels_E_eq_Edens C.m₀ C.Tm (fun j => (Jr.PJ j (rawOf D, w)).1)
      (fun j => (Jr.PJ j (rawOf D, w)).2)]
  have key := Jr.classActivityFamily_ae_W1_eq_gen (ι := 𝒯E) (m₀ := C.m₀) C hb₁ hbC
    (fun τ r => C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ
    (fun τ => τ.1.1) (fun τ => τ.1.2.2) hj1 hjk Gk (fun τ => C.Tm.gs τ.1.1 τ.1.2.2)
    (fun τ Ψ Ψ' h h' hag => hcl.localE τ.1.1 τ.1.2.1 τ.1.2.2 Ψ Ψ' h h' hag) X₀ X₁f 𝒦X hB hF hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1)
    (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall
    hnum hnum' z hρ hρc hρpp hp ha1 hbb hab 𝒴C h𝒴 H hH hEJ hρp
  exact key

end StepSetting.JointRep

end Balaban.Fluctuation
