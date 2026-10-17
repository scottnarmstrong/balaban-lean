/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyDeriv
public import Balaban.Fluctuation.MarkedVRawY

/-!
# Exact locality of the marks of the inherited energy (`LocalClassDensityFamilyLocal`)

The input (M2) of `e0CoeffFamily_class_fromTower` asks the marks to be local in the parameter:
`G₁ θ j s = G₁ θ' j s` when `θ, θ'` agree on `sitesOf T` and the label of `j` lies in
`Ŷ(sitesOf T)`.  For the marks of the inherited labels this needs the exact (raw) locality of the
marked terms of the old-term functional `eTermFun` (the thick locality `AgHatDir` reads the data on
the thickening of `Y`, which is not inside the label):

* `marked_eterm_fan_local_rawY`, `evDec_eTermFun_local_rawY`: the cores
  `marked_fan_local_rawY_of`, `evDec_local_rawY_of` (`MarkedVRawY`) for `Φ = eTermFun`: the marked
  terms of a label depend on the raw datum only on `Y` itself;
* `classMarksFamily_local`: the locality of the marks family of `LocalClassDensityFamilyMarks` in
  the parameter, for `s ∈ [0, 1]` (`1 < a`): if `θ, θ' ∈ physV` agree on a set `A` (`physRestrict`)
  and the bridge label of the pair lies in `Ŷ(A) = A`, the marks of the pair at `θ` and `θ'` are
  equal.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section MarkedE

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Exact locality of the marked fan of the old-term functional.**  `marked_fan_local_rawY_of`
with `Φ = eTermFun … Fk E` (`eTermFun_eq_of_component`, `SharpENu`): two configurations whose raw
data agree on the component `Yc` itself, whose hat variables agree at the unit points of its sites
and whose cut parameters agree on the patches inside `Yc` give the same value of the fan along the
masked tangent `markedHatPsiF … Zm um tm`. -/
theorem marked_eterm_fan_local_rawY (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
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
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) :
    LocalityAEOn (Real.exp κ)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => agreeOn (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u.1 u'.1 ∧
        ∀ y ∈ compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C,
          ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
      (fun u s => eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E
        (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            u.1.1 (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) :=
  marked_fan_local_rawY_of (flCore_of hB hF) hk hG hG' cc hcψ Zm um tm hMX hdm hα hsm hδ hcov hX₁
    hconn hrow hF₁ hSol (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (fun _ hφd hδ' hψ hdata hXY =>
      eTermFun_eq_of_component hB hF hG' hcov hX₁ Fk E hφd hδ' hψ hdata hXY)

/-- **Exact locality of the marked terms of the old-term functional.**  For a pair `(F₁, Sol)` with
the defining properties and marks `(um, tm)` of the radius set, the coefficient
`evDec … (eTermFun … Fk E) Zm um tm Y` takes equal values at two data of `XiCRaw × ball` whose raw
parts agree on `Y` itself and whose hat variables agree at the unit points of `Y`
(`evDec_local_rawY_of` with `marked_eterm_fan_local_rawY`). -/
theorem evDec_eTermFun_local_rawY (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
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
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hu' : u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
    (hag : agreeOn Y u.1 u'.1)
    (hagψ : ∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) :
    evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E) Zm
        um tm Y u =
      evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E) Zm
        um tm Y u' :=
  evDec_local_rawY_of (flCore_of hB hF) hG' cc Zm um tm hcov hX₁ F₁ Sol
    (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
    (marked_eterm_fan_local_rawY hB hF hk hG hG' cc hcψ Zm um tm hMX hdm hα hsm hδ hcov hX₁ hconn
      hrow hF₁ hSol Fk E) Y hu hu' hag hagψ

end MarkedE

end Balaban.Localization

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section FamilyLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The locality of the marks family in the parameter.**  For a finite family of labels of the
class with their settings and given maps (the defining properties suffice), `1 < a`, the marks
`G₁` of `classMarksFamily_fields` (formula `hG₁`): for every set `A`, parameters `θ, θ' ∈ physV`
whose raw data and sources agree on `A`, every `s ∈ [0, 1]` and every rooted pair `q` whose bridge
label lies in `Ŷ(A)`, `G₁ θ q s = G₁ θ' q s` (`evDec_eTermFun_local_rawY` on the domain `Y` of the
pair, `Y ⊆ bridge 1 z Y ⊆ A`). -/
theorem classMarksFamily_local_gen {ι : Type*} [Fintype ι] {m₀ : ℕ}
    (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
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
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
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
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) a₁ ν S.hG'
          cc (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) Hm (compWeight L a₁)
            (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0) :
    ∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z},
      bridge 1 z q.1.2 ⊆ Yhat Set.univ A → G₁ θ q (s : ℂ) = G₁ θ' q (s : ℂ) := by
  classical
  intro A θ hθ θ' hθ' hres s hs q hsub
  have hagA := ((physRestrict_physIncl_eq_iff S A θ θ').1 hres).1
  rw [Yhat_univ] at hsub
  have hagY : agreeOn q.1.2 (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
    agreeOn_mono ((subset_bridge z q.1.2).trans hsub) hagA
  have hsn : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hca : ‖(s : ℂ)‖ < a := lt_of_le_of_lt hsn ha1
  have hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖(s : ℂ)‖ < a := ⟨hθ.1, hca⟩
  have hc' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖(s : ℂ)‖ < a := ⟨hθ'.1, hca⟩
  funext Φ
  rw [hG₁, hG₁, ite_eq_left hc, ite_eq_left hc']
  refine congrArg (fun w : ℂ => (S.β : ℂ) * w) (Filter.EventuallyEq.deriv_eq ?_)
  have hopen : IsOpen {t : ℂ | (‖(s : ℂ)‖ + ‖t‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ :=
    mem_markedRadiusSet_of_pos (flCore_of (hB q.1.1) (hF q.1.1)).δ₁_pos hab hca.le
      (by rw [norm_zero]; exact hbb.le)
  filter_upwards [hopen.mem_nhds h0] with t ht
  exact evDec_eTermFun_local_rawY (hB q.1.1) (hF q.1.1) S.hk1 hG S.hG' cc hcψ (S.blockU z)
    (s : ℂ) t hMX hdm hα hsm ht (hcov q.1.1) (hX₁ q.1.1) hconn hrow (hF₁ q.1.1) (hSolprop q.1.1)
    (Fk q.1.1) (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r) q.1.2
    ⟨hθ.1, fun p => (S.hatOf_mem 1 hρ hp Φ p).trans hρc⟩
    ⟨hθ'.1, fun p => (S.hatOf_mem 1 hρ hp Φ p).trans hρc⟩ hagY (fun _ _ _ => rfl)

open Classical in
/-- **The locality of the marks family in the parameter.**  For a finite family of labels of the
class with their settings and given maps (the defining properties suffice), `1 < a`, the marks
`G₁` of `classMarksFamily_fields` (formula `hG₁`): for every set `A`, parameters `θ, θ' ∈ physV`
whose raw data and sources agree on `A`, every `s ∈ [0, 1]` and every rooted pair `q` whose bridge
label lies in `Ŷ(A)`, `G₁ θ q s = G₁ θ' q s` (`evDec_eTermFun_local_rawY` on the domain `Y` of the
pair, `Y ⊆ bridge 1 z Y ⊆ A`). -/
theorem classMarksFamily_local {ι : Type*} [Fintype ι]
    (C : StepClass d L N₁ m₁ k N ϱ)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
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
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
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
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ (jL q.1.1) (𝒦X q.1.1) a₁ ν S.hG'
          cc (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (C.Tm.gs (jL q.1.1) (XL q.1.1)) Hm (compWeight L a₁)
            (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL q.1.1) (yL q.1.1) (XL q.1.1) r.1 r.2))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0) :
    ∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z},
      bridge 1 z q.1.2 ⊆ Yhat Set.univ A → G₁ θ q (s : ℂ) = G₁ θ' q (s : ℂ) := by
  exact classMarksFamily_local_gen S (fun τ r => C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2) jL XL Gk
    (fun τ => C.Tm.gs (jL τ) (XL τ)) X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow
    F₁ hF₁ Sol hSolprop Fk z hρ hρc hp ha1 hbb hab G₁ hG₁

end FamilyLocal

end Balaban.Fluctuation
