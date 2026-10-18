/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActLabel
public import Balaban.Fluctuation.LocalClassDensityFamilyGenJoint
public import Balaban.Fluctuation.HatLabelsAct

/-!
# The activity family of a generic label functional (`LocalClassDensityFamilyGenAct`)

The generic versions of `classOldMarkedLocal_blockActs_of`, `classActivityDomains_isDj` and
`classActivityFamily_fields` (`LocalClassDensityFamilyActLabel`, `LocalClassDensityFamilyAct`) for a
family of label functionals `Eτ τ : RawData → ℂ`, indexed by the labels `τ`, each analytic on the
chart image of its generating set `Gj τ` and bounded there by
`B_τ e^{-(κ_dec - 1) d^cov_{m₀}(X_τ)}`; the label functional of the activity is `β⁻¹ Eτ τ`.
The generating set `Gj τ` carries the locality of the label (the support `X^⋆ = X ∪ st₊(y)` in
the application to the irrelevant terms).  The landed theorems for the class `C` are the
applications with `Eτ τ r = ℰ^{(j)}(y, X; r)` and `B_τ = E₀`.

* `classOldMarkedLocal_blockActs_gen`: the block values of one label (value analogue).
* `classActivityDomains_isDj_gen`: the domains of the family are domains of `𝒟_{k+1}` of index `1`.
* `classActivityFamily_fields_gen`: measurability, block dependence, the bound
  `∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{m₀}(Y)}`, analyticity in `(θ, u)`,
  continuity, holomorphy in `u` and locality in the parameter.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section BlockActsGen

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block-level values of one label, with the label chart replaced by any set containing the
composed step data** (`h𝒮`).  `classOldMarkedLocal_blockActs_gen` is the case of the label chart. -/
theorem classOldMarkedLocal_blockActs_gen_onSet {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) {Bτ : ℝ} (hBτ : 0 ≤ Bτ)
    {β : ℝ} (hβ : 0 < β) {j : ℕ}
    (hB : BgSetting N S.G' Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} (hEan : AnalyticOnNhd ℂ Eτ 𝒮)
    (hEbd : ∀ r ∈ 𝒮, ‖Eτ r‖ ≤ Bτ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData S.G' N,
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (Zm : Finset (unitPts S.G')) (mb : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁)
    (h𝒮 : ∀ t ∈ FlRealLC S.G' Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      D2raw Gk Gj (compWeight L a₁) Fk (d1Triple S.G' Gk Hm (compWeight L a₁) t.1.1 t.2.1
        t.2.2) ∈ 𝒮) :
    (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
      (∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') →
      ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      DepOn (blocksOf mb (k + 1) Set.univ Y')
        (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um 0 Y
            (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um 0 Y
          (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      ‖evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um 0 Y
          (Θ, S.hatOf mb ρ hp Φ)‖ ≤
        (β⁻¹ * Bτ) *
          Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov S.G' m₀ Y)) ∧
    (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm p.2 0 Y
          ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf mb ρ hp Φ))
        (physV S a₁ ν eps ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  obtain ⟨-, e2, e3, -, -, hJ⟩ := classOldMarkedLocal_joint_gen_onSet (h𝒮 := h𝒮)
      hb₁ hbC Eτ hBτ hβ hB hF S.hk1 hG
    S.hG' cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd hF₁an hF₁
    hSolan hSolprop hFkan hFk Zm
  exact evDec_hatOf_value_fields S mb F₁ Sol (B := fun Y => (β⁻¹ * Bτ) *
      Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov S.G' m₀ Y)) e2 e3 hJ
    hρ hρc hp

/-- **The block-level values of one label with a generic functional, for given maps and any block
index `mb`.**  As `classOldMarkedLocal_blockActs_of` for the functional `β⁻¹ Eτ`, with the bound
`β⁻¹ B_τ e^{-κ₀ d(X) - 2κ_dec d(Y)}`. -/
theorem classOldMarkedLocal_blockActs_gen {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) {Bτ : ℝ} (hBτ : 0 ≤ Bτ)
    {β : ℝ} (hβ : 0 < β) {j : ℕ}
    (hB : BgSetting N S.G' Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : AnalyticOnNhd ℂ Eτ (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ r‖ ≤ Bτ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData S.G' N,
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (Zm : Finset (unitPts S.G')) (mb : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ)
    (hp : 0 < S.p₁) :
    (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
      (∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') →
      ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      DepOn (blocksOf mb (k + 1) Set.univ Y')
        (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um 0 Y
            (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um 0 Y
          (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      ‖evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm um 0 Y
          (Θ, S.hatOf mb ρ hp Φ)‖ ≤
        (β⁻¹ * Bτ) *
          Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov S.G' m₀ Y)) ∧
    (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk Gj Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * Eτ r)) Zm p.2 0 Y
          ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf mb ρ hp Φ))
        (physV S a₁ ν eps ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) :=
  classOldMarkedLocal_blockActs_gen_onSet S hb₁ hbC Eτ hBτ hβ hB hF hG cc hcψ hMX hdm hα hsm hcov
    hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd hF₁an hF₁ hSolan hSolprop hFkan hFk Zm mb hρ
    hρc hp (fun _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC hB hF hFk ht)

end BlockActsGen

section ActFamilyGen

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

theorem classActivityDomains_isDj_gen {ι : Type*} [Fintype ι]
    {m₀ : ℕ}
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d)
    (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒴 : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) :
    ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y := by
  intro Y hY
  rw [h𝒴, Finset.mem_biUnion] at hY
  obtain ⟨τ, -, hYτ⟩ := hY
  exact polyDom_isDj_one S.hG' le_rfl hN hm1 (hcov τ) hd (hopt τ) hYτ


open Classical in
/-- **The fields of the activity family, with the label charts replaced by any sets containing the
composed step data** (`h𝒮`).  `classActivityFamily_fields_gen` is the case of the label charts. -/
theorem classActivityFamily_fields_gen_onSet {ι : Type*} [Fintype ι]
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
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
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
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' Hm a₁ ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ) :
    (∀ θ Y u, Measurable (H θ Y u)) ∧
    (∀ θ (Y : {Y // Y ∈ 𝒴C}) u, DepOn (blocksOf 1 (k + 1) Set.univ Y.1) (H θ Y u)) ∧
    (∀ θ (Y : {Y // Y ∈ 𝒴C}) u Φ, ‖H θ Y u Φ‖ ≤
      ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y.1)
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
  classical
  set CHr := XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps with hCHr
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hm1).trans hN
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hBA := fun τ => classOldMarkedLocal_blockActs_gen_onSet (h𝒮 := h𝒮 τ)
      S hb₁ hbC (Eτ τ) (hBτ τ) hβ (hB τ)
    (hF τ) hG cc hcψ hMX hdm hα hsm (hcov τ) (hX₁ τ) hconn hrow (hopt τ) hκ₀ hκdec hκ h1 hlog
    (hEan τ) (hEbd τ) (hF₁an τ) (hF₁ τ) (hSolan τ) (hSolprop τ) (hFkan τ) (hFk τ) Zm 1 hρ hρc hp
  have hW : ∀ τ (u : ℂ), ‖u‖ ≤ a →
      (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := fun τ u hu =>
    mem_markedRadiusSet_of_pos (flCore_of (hB τ) (hF τ)).δ₁_pos hab hu
      (by rw [norm_zero]; exact hbb)
  have hmem : ∀ Θ ∈ CHr, ∀ Φ : (∀ b, (S.blockSplit 1 hp).Ωb b), (Θ, S.hatOf 1 ρ hp Φ) ∈
      CHr ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} :=
    fun Θ hΘ Φ => ⟨hΘ, fun p => (S.hatOf_mem 1 hρ hp Φ p).trans hρc⟩
  have hYdj := classActivityDomains_isDj_gen S jL XL X₁f 𝒦X hcov hopt hN hm1 hd 𝒴C h𝒴
  -- the term of a label at the clamped hat field
  have hcontT := fun τ Y Θ (hΘ : Θ ∈ CHr) (um : ℂ) (hum : ‖um‖ ≤ a) =>
    (hBA τ).2.1 Y Θ hΘ um (hW τ um hum)
  have hdepT := fun τ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hY : ∀ y ∈ Y, box (cbase (cellSide L 1 m₁ (k + 1)) y) (cellSide L 1 m₁ (k + 1)) ⊆ Y)
    Θ (hΘ : Θ ∈ CHr) (um : ℂ) (hum : ‖um‖ ≤ a) =>
    (hBA τ).1 Y Y subset_rfl hY Θ hΘ um (hW τ um hum)
  have hbdT := fun τ Y Θ (hΘ : Θ ∈ CHr) (um : ℂ) (hum : ‖um‖ ≤ a) Φ =>
    (hBA τ).2.2.1 Y Θ hΘ a bb ha0.le hbb hab um hum Φ
  have hanT := fun τ Y Φ => ((hBA τ).2.2.2 Y Φ).mono
    (Set.prod_mono subset_rfl (fun u hu => hW τ u (mem_ball_zero_iff.1 hu).le))
  -- the activity on and off the chart
  have hpos : ∀ θ u, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a →
      ∀ Y : {Y // Y ∈ 𝒴C}, H θ Y u = fun Φ =>
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm u 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm 0 0 Y.1
              ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0 := fun θ u hc Y => by
    funext Φ
    rw [hH, ite_eq_left hc]
  have hneg : ∀ θ u, ¬ ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a) →
      ∀ Y : {Y // Y ∈ 𝒴C}, H θ Y u = fun _ => 0 := fun θ u hc Y => by
    funext Φ
    rw [hH, ite_eq_right hc]
  have h0a : ‖(0 : ℂ)‖ ≤ a := by rw [norm_zero]; exact ha0.le
  have hholH : ∀ Y Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => H r.1 Y r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a) := by
    intro Y Φ
    have hsum : AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
        ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
          (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm r.2 0 Y.1
              ((r.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
            evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) a₁ ν S.hG' cc (F₁ τ) (Sol τ)
            (eTermFun S.G' (Gk τ) (Gj τ) Hm (compWeight L a₁) (Fk τ)
              (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) Zm 0 0 Y.1
              ((r.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
        else 0) (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a) := by
      refine Finset.analyticOnNhd_fun_sum _ fun τ _ => ?_
      by_cases hYτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
      · have hA := hanT τ Y.1 Φ
        have h0 := (hanT τ Y.1 Φ).comp (f := fun r : physParam N S × ℂ => (r.1, (0 : ℂ)))
          (fun r _ => analyticAt_fst.prod analyticAt_const)
          (fun r (hr : r ∈ physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a) =>
            ⟨hr.1, Metric.mem_ball_self ha0⟩)
        rw [Function.comp_def] at h0
        have hd := (analyticOnNhd_const (v := (S.β : ℂ))).mul (hA.sub h0)
        refine hd.congr ((isOpen_physV S a₁ ν eps (hB τ).HBp).prod Metric.isOpen_ball) ?_
        intro r _
        exact (ite_eq_left hYτ).symm
      · refine (analyticOnNhd_const (v := (0 : ℂ))).congr
          ((isOpen_physV S a₁ ν eps (hB τ).HBp).prod Metric.isOpen_ball) ?_
        intro r _
        exact (ite_eq_right hYτ).symm
    by_cases hι : Nonempty ι
    · obtain ⟨τ₀⟩ := hι
      refine hsum.congr ((isOpen_physV S a₁ ν eps (hB τ₀).HBp).prod Metric.isOpen_ball) ?_
      intro r hr
      have hc : (r.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖r.2‖ < a :=
        ⟨hr.1.1, mem_ball_zero_iff.1 hr.2⟩
      show _ = H r.1 Y r.2 Φ
      rw [hpos r.1 r.2 hc Y]
    · exfalso
      have hY2 : Y.1 ∈ Finset.univ.biUnion
          fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) := by
        rw [← h𝒴]; exact Y.2
      obtain ⟨τ, -, -⟩ := Finset.mem_biUnion.1 hY2
      exact hι ⟨τ⟩
  refine ⟨?_, ?_, ?_, hholH, ?_, ?_, ?_⟩
  · intro θ Y u
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a
    · rw [hpos θ u hc Y]
      refine Finset.measurable_fun_sum _ fun τ _ => ?_
      by_cases hYτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
      · simp only [hYτ, ite_true]
        exact (continuous_const.mul ((hcontT τ Y.1 _ hc.1 u hc.2.le).sub
          (hcontT τ Y.1 _ hc.1 0 h0a))).measurable
      · simp only [hYτ, ite_false]
        exact measurable_const
    · rw [hneg θ u hc Y]
      exact measurable_const
  · intro θ Y u
    have hYc := cell_subset_of_isDj hN1 (hYdj Y.1 Y.2)
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a
    · rw [hpos θ u hc Y]
      intro Φ Φ' h
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases hYτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
      · rw [ite_eq_left hYτ, ite_eq_left hYτ]
        exact congrArg (fun w => (S.β : ℂ) * w) (congrArg₂ (fun x y => x - y)
          (hdepT τ Y.1 hYc _ hc.1 u hc.2.le Φ Φ' h) (hdepT τ Y.1 hYc _ hc.1 0 h0a Φ Φ' h))
      · rw [ite_eq_right hYτ, ite_eq_right hYτ]
    · rw [hneg θ u hc Y]
      intro Φ Φ' _
      rfl
  · intro θ Y u Φ
    have hnn : ∀ τ, 0 ≤ (if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y.1) else 0) := fun τ => by
      split_ifs
      · have := hBτ τ
        positivity
      · exact le_rfl
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a
    · rw [hpos θ u hc Y]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
      by_cases hYτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
      · rw [ite_eq_left hYτ, ite_eq_left hYτ, norm_mul, Complex.norm_of_nonneg hβ.le]
        have hA := hbdT τ Y.1 _ hc.1 u hc.2.le Φ
        have hB0 := hbdT τ Y.1 _ hc.1 0 h0a Φ
        have hsub := (norm_sub_le _ _).trans (add_le_add hA hB0)
        calc S.β * ‖_ - _‖ ≤ S.β * ((S.β⁻¹ * Bτ τ) * Real.exp (-κ₀ *
              treeLenCovOne m₀ (jL τ) (XL τ) - 2 * κdec * treeLenCov S.G' m₀ Y.1) +
              (S.β⁻¹ * Bτ τ) * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
                2 * κdec * treeLenCov S.G' m₀ Y.1)) :=
              mul_le_mul_of_nonneg_left hsub hβ.le
          _ = 2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
              2 * κdec * treeLenCov S.G' m₀ Y.1) := by
              field_simp
              ring
      · rw [ite_eq_right hYτ, ite_eq_right hYτ, norm_zero]
    · rw [hneg θ u hc Y, norm_zero]
      exact Finset.sum_nonneg fun τ _ => hnn τ
  · intro Y θ hθ u hu
    have hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a :=
      ⟨hθ.1, mem_ball_zero_iff.1 hu⟩
    rw [hpos θ u hc Y]
    refine continuous_finsetSum _ fun τ _ => ?_
    by_cases hYτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
    · simp only [hYτ, ite_true]
      exact continuous_const.mul ((hcontT τ Y.1 _ hc.1 u hc.2.le).sub
        (hcontT τ Y.1 _ hc.1 0 h0a))
    · simp only [hYτ, ite_false]
      exact continuous_const
  · intro θ hθ Y Φ
    refine AnalyticOnNhd.differentiableOn ?_
    exact (hholH Y Φ).comp (f := fun u : ℂ => (θ, u))
      (fun _ _ => analyticAt_const.prod analyticAt_id) (fun u hu => ⟨hθ, hu⟩)
  · intro A θ hθ θ' hθ' hres s hs Y hsub
    have hagA := ((physRestrict_physIncl_eq_iff S A θ θ').1 hres).1
    rw [Yhat_univ] at hsub
    have hagY : agreeOn Y.1 (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) := agreeOn_mono hsub hagA
    have hsn : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    have hca : ‖(s : ℂ)‖ < a := lt_of_le_of_lt hsn ha1
    rw [hpos θ (s : ℂ) ⟨hθ.1, hca⟩ Y, hpos θ' (s : ℂ) ⟨hθ'.1, hca⟩ Y]
    funext Φ
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hYτ : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
    · rw [ite_eq_left hYτ, ite_eq_left hYτ]
      have hloc := fun um (hum : ‖um‖ ≤ a) => evDec_eTermFun_local_rawY (hB τ) (hF τ) S.hk1 hG
        S.hG' cc hcψ Zm um 0 hMX hdm hα hsm (hW τ um hum) (hcov τ) (hX₁ τ) hconn hrow (hF₁ τ)
        (hSolprop τ) (Fk τ) (fun r => (S.β : ℂ)⁻¹ * Eτ τ r) Y.1
        (hmem (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) hθ.1 Φ)
        (hmem (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) hθ'.1 Φ) hagY (fun _ _ _ => rfl)
      exact congrArg (fun w => (S.β : ℂ) * w) (congrArg₂ (fun x y => x - y)
        (hloc (s : ℂ) hca.le) (hloc 0 h0a))
    · rw [ite_eq_right hYτ, ite_eq_right hYτ]

open Classical in
/-- **The fields of the activity family of a generic label functional.**  For a finite family of
labels with functionals `Eτ τ` (analytic on the chart image of `Gj τ`, bounded by
`B_τ e^{-(κ_dec - 1) d^cov_{m₀}(X_τ)}`), their settings and given maps (the hypotheses of
`classOldMarkedLocal_joint_gen`), a mask `Zm`, a clamp radius `0 < ρ ≤ c_ψ`, radii `1 < a`,
`0 ≤ b'` with `(a + b') · markedRad < δ₁`, and the activities `H` of the domains of `𝒴C` given by
the formula `hH`:

1. `H θ Y u` is measurable;
2. it depends only on the blocks of `Y` (index `1`);
3. it is bounded by `∑_{τ : Y ∈ polyDom τ} 2 B_τ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{m₀}(Y)}`;
4. it is analytic in `(θ, u)` on `physV × {‖u‖ < a}`;
5. it is continuous in the configuration for `θ ∈ physV`, `‖u‖ < a`;
6. it is holomorphic in `u` on the disc for `θ ∈ physV`;
7. it is local in the parameter: if `θ, θ' ∈ physV` agree on `A` (`physRestrict`), `s ∈ [0, 1]`
   and `Y ⊆ Ŷ(A)`, then `H θ Y s = H θ' Y s`. -/
theorem classActivityFamily_fields_gen {ι : Type*} [Fintype ι]
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
      else 0) :
    (∀ θ Y u, Measurable (H θ Y u)) ∧
    (∀ θ (Y : {Y // Y ∈ 𝒴C}) u, DepOn (blocksOf 1 (k + 1) Set.univ Y.1) (H θ Y u)) ∧
    (∀ θ (Y : {Y // Y ∈ 𝒴C}) u Φ, ‖H θ Y u Φ‖ ≤
      ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
          2 * κdec * treeLenCov S.G' m₀ Y.1)
      else 0) ∧
    (∀ Y Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => H r.1 Y r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    (∀ Y, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, Continuous (H θ Y u)) ∧
    (∀ θ ∈ physV S a₁ ν eps, ∀ Y Φ,
      DifferentiableOn ℂ (fun u => H θ Y u Φ) (Metric.ball (0 : ℂ) a)) ∧
    (∀ A : Set (CTorus d L N₁ m₁ (k + 1)), ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict (N := N) A (physIncl N S θ) = physRestrict A (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C},
        Y.1 ⊆ Yhat Set.univ A → H θ Y (s : ℂ) = H θ' Y (s : ℂ)) :=
  classActivityFamily_fields_gen_onSet S hb₁ hbC Eτ Bτ hBτ hβ jL XL Gk Gj X₀ X₁f 𝒦X hB hF hG cc hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan
    hSolprop Fk hFkan hFk hN hm1 hd Zm hρ hρc hp ha1 hbb hab 𝒴C h𝒴 H hH
    (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht)


end ActFamilyGen

end Balaban.Fluctuation
