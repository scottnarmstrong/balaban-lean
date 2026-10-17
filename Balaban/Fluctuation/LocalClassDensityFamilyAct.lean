/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActLabel
public import Balaban.Fluctuation.HatLabelsAct
public import Balaban.Fluctuation.LocalClassDensityFamilyGenAct
public import Balaban.Fluctuation.LocalClassDensityFamilyGenLabelAct

/-!
# The activity family of the inherited energy of a class (`LocalClassDensityFamilyAct`)

The input (M1) of `e0CoeffFamily_class_fromTower` asks for one activity family `A θ` on labels of
the block index `1` whose label sum is the class exponent `W₁^C(rawOf D, s ψ̂)`.  By
`W1_eq_zeroClass_add_EJ`, `W₁^C = W₁^0 + (ℰ_k(·) - ℰ_k(·, 0))`; the part `W₁^0` is the zero-source
activity of the zero class.  This file constructs the activities of the inherited part.  For a
finite family of labels `τ` of the class (degree `jL τ`, site `yL τ`, domain `XL τ`) with their
settings and given maps (`exists_classOldLabel_maps`), a mask `Zm`, the clamp radius `ρ` and a disc
`‖u‖ < a`, the label value along the line is expanded by the marked terms of
`classOldMarkedLocal_joint_of` at the second mark `0`.  The labels of the activity are the domains
`Y` of all these expansions (`𝒴C`, the union over `τ` of `polyDom` of the label), and the activity
of `Y` at a parameter `θ` whose raw datum lies in the chart and `‖u‖ < a` is

  `H θ Y u Φ = ∑_{τ : Y ∈ polyDom τ} β (evDec … Eτ … Zm u 0 Y - evDec … Eτ … Zm 0 0 Y)
    (θ.1, S.hatOf 1 ρ hp Φ)`,

and `0` otherwise (the hypothesis `hH` gives `H` by this formula).

The values of the marked terms at the blocks are `classOldMarkedLocal_blockActs_of`
(`LocalClassDensityFamilyActLabel`).

* `classActivityDomains_isDj`: every domain of `𝒴C` is a domain of `𝒟_{k+1}` for the index `1`.
* `classActivityFamily_fields`: the activities are measurable, depend only on the blocks of their
  domain, are bounded by `∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{C.m₀}(Y)}`, are
  analytic in `(θ, u)` on `physV × {‖u‖ < a}`, continuous in the configuration, holomorphic in
  `u`, and local in the parameter: two parameters of `physV` whose raw data and sources agree on a
  set `A` give the same activity of a domain `Y ⊆ Ŷ(A)` at every `s ∈ [0, 1]`
  (`evDec_eTermFun_local_rawY`).
* `classActivityFamily_labelAct`: under the numerical condition `hnumH` (the bound above is at most
  `ε_C e^{-κ_H d^cov_1(Y)}`), the activities form one `LabelAct` family on the labels
  `thickLabels 𝒴C` with the entropy constant `K₀(κ₀)` (`entropy_thick`).

The bound of a label decays in the size `d^cov_{C.m₀}` at the index of the class, while the label
size of `LabelAct` is `d^cov_1`; the comparison is the numerical condition `hnumH`, a hypothesis.
The sum identity is `LocalClassDensityFamilyActSum`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section ActFamily

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **The domains of the activity family are domains of `𝒟_{k+1}` for the index `1`.**  Every
domain of the expansion of a label of the class (`polyDom` at the index `C.m₀ ≥ 1`) is a domain of
`𝒟_{k+1}` for the index `1` (`polyDom_isDj_one`). -/
theorem classActivityDomains_isDj {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hcov : ∀ τ, CovSetup S.G' C.m₀ (jL τ) (XL τ) (𝒦X τ))
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ (jL τ)) E₀ = treeLenCovOne C.m₀ (jL τ) (XL τ))
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) :
    ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y := by
  exact classActivityDomains_isDj_gen S jL XL X₁f 𝒦X hcov hopt hN hm1 hd 𝒴C h𝒴

open Classical in
/-- **The fields of the activity family of the inherited energy.**  For a finite family of labels
of the class `C` with their settings and given maps (the hypotheses of
`classOldMarkedLocal_joint_of`), a mask `Zm`, a clamp radius `0 < ρ ≤ c_ψ`, radii `1 < a`,
`0 ≤ b'` with `(a + b') · markedRad < δ₁`, and the activities `H` of the domains of `𝒴C` given by
the formula `hH`:

1. `H θ Y u` is measurable;
2. it depends only on the blocks of `Y` (index `1`);
3. it is bounded by `∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{C.m₀}(Y)}`;
4. it is analytic in `(θ, u)` on `physV × {‖u‖ < a}`;
5. it is continuous in the configuration for `θ ∈ physV`, `‖u‖ < a`;
6. it is holomorphic in `u` on the disc for `θ ∈ physV`;
7. it is local in the parameter: if `θ, θ' ∈ physV` agree on `A` (`physRestrict`), `s ∈ [0, 1]`
   and `Y ⊆ Ŷ(A)`, then `H θ Y s = H θ' Y s`. -/
theorem classActivityFamily_fields {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXp : ∀ τ, IsPolyDom C.m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' C.m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ (jL τ)) E₀ = treeLenCovOne C.m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ, ∀ r ∈ XiCRaw (C.Tm.gs (jL τ) (XL τ)) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom (jL τ) (C.Tm.gs (jL τ) (XL τ)) r.1 r.2)
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
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d)
    (Zm : Finset (unitPts S.G')) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ))
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) C.m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2)) Zm u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) C.m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2)) Zm 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0) :
    (∀ θ Y u, Measurable (H θ Y u)) ∧
    (∀ θ (Y : {Y // Y ∈ 𝒴C}) u, DepOn (blocksOf 1 (k + 1) Set.univ Y.1) (H θ Y u)) ∧
    (∀ θ (Y : {Y // Y ∈ 𝒴C}) u Φ, ‖H θ Y u Φ‖ ≤
      ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
        2 * P.E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' C.m₀ Y.1)
      else 0) ∧
    (∀ Y Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => H r.1 Y r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    (∀ Y, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, Continuous (H θ Y u)) ∧
    (∀ θ ∈ physV S a₁ ν eps, ∀ Y Φ,
      DifferentiableOn ℂ (fun u => H θ Y u Φ) (Metric.ball (0 : ℂ) a)) ∧
    (∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C},
        Y.1 ⊆ Yhat Set.univ A → H θ Y (s : ℂ) = H θ' Y (s : ℂ)) := by
  have hraw := fun τ => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀ a₁ ν
    δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  exact classActivityFamily_fields_gen S hb₁ hbC
    (fun τ r => C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ jL XL Gk
    (fun τ => C.Tm.gs (jL τ) (XL τ)) X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn
    hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1) (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol
    hSolan hSolprop Fk hFkan hFk hN hm1 hd Zm hρ hρc hp ha1 hbb hab 𝒴C h𝒴 H hH

open Classical in
/-- **The activity family of the inherited energy as one `LabelAct` family.**  Under the hypotheses
of `classActivityFamily_fields`, the entropy rate `κ₀' ≥ a_ent + 1` and the numerical condition
`hnumH` (the bound of `classActivityFamily_fields` is at most `ε_C e^{-κ_H d^cov_1(Y)}` on every
domain of `𝒴C`), the activities `H θ · u` are the activities of one family
`A : physParam → ℂ → LabelAct (thickLabels 𝒴C) … ε_C κ_H κ₀' K₀(κ₀')` on the labels of the domains
of `𝒴C` (site `Y`, size `d^cov_1(Y)`), with the entropy constant of `entropy_thick`. -/
theorem classActivityFamily_labelAct {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXp : ∀ τ, IsPolyDom C.m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' C.m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ (jL τ)) E₀ = treeLenCovOne C.m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ, ∀ r ∈ XiCRaw (C.Tm.gs (jL τ) (XL τ)) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom (jL τ) (C.Tm.gs (jL τ) (XL τ)) r.1 r.2)
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
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d)
    (Zm : Finset (unitPts S.G')) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 ≤ bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ))
    (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
    (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hH : ∀ θ Y u Φ, H θ Y u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) C.m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2)) Zm u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) C.m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2)) Zm 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0
      else 0)
    {εC κH κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    (hnumH : ∀ Y ∈ 𝒴C, (∑ τ, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ) then
        2 * P.E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' C.m₀ Y)
      else 0) ≤ εC * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y)) :
    ∃ A : physParam N S → ℂ → LabelAct (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj)
        (S.blockSplit 1 hp).Ωb εC κH κ0 (K0 d L κ0),
      ∀ θ u Y, (A θ u).H Y = H θ Y u := by
  have hraw := fun τ => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀ a₁ ν
    δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  exact classActivityFamily_labelAct_gen S hb₁ hbC
    (fun τ r => C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ jL XL Gk
    (fun τ => C.Tm.gs (jL τ) (XL τ)) X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn
    hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1) (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol
    hSolan hSolprop Fk hFkan hFk hN hm1 hd Zm hρ hρc hp ha1 hbb hab 𝒴C h𝒴 h𝒴dj H hH hκ0 hnumH

end ActFamily

end Balaban.Fluctuation
