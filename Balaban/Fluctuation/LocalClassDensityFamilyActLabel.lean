/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyLocal

/-!
# Block values of the marked terms of an inherited label (`LocalClassDensityFamilyActLabel`)

The activities of (M1) are built from the values of the marked terms of the inherited labels at
the second mark `0` (no mask derivative), at the clamped hat field of a block configuration.

* `evDec_hatOf_value_fields`: for any functional `En` and any block index `mb`, from the locality,
  the bound on closed bidiscs and the joint analyticity of the marked terms of `En` (the forms of
  clauses 2, 3, 6 of `classOldMarkedLocal_joint_of`): the value
  `Φ ↦ evDec … En … Zm um 0 Y (Θ, S.hatOf mb ρ hp Φ)` depends only on the blocks of any `mb`-cell
  union `Y′ ⊇ Y`, is continuous in the configuration, is bounded by `B Y`, and is analytic in
  `(e, u)` on `physV × {u | (u, 0) ∈ W}` (`analyticOnNhd_physV_of_chart`).  The value analogue of
  `deriv_evDec_hatOf_fields`.
* `classOldMarkedLocal_blockActs_of`: the same for the label functional
  `Eτ = eTermFun … (β⁻¹ ℰ^{(j)}(y, X; ·))` of one inherited label with given maps, with the bound
  `β⁻¹ E₀ e^{-κ₀ d(X) - 2κ_dec d^cov_{C.m₀}(Y)}` (`classOldMarkedLocal_joint_of`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section ValueCore

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν κ eps δ₁ cψ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
variable {cc : ℂ} {Zm : Finset (unitPts S.G')}

/-- **The block-level values of the marked terms at the second mark `0`, for any functional `En`
and any block index `mb`.**  The value analogue of `deriv_evDec_hatOf_fields`: for a pair
`(F₁, Sol)` and a functional `En` whose marked terms are local (`hloc`, the form of clause 2 of
`classOldMarkedLocal_joint_of`), bounded by `B` on closed bidiscs (`hbd`, clause 3) and jointly
analytic on the chart (`hJ2`, clause 6), the value at the clamped hat field of the `mb`-block
configuration, `Φ ↦ evDec … En … Zm um 0 Y (Θ, S.hatOf mb ρ hp Φ)`:

1. depends only on the blocks inside any union `Y′ ⊇ Y` of `mb`-cells;
2. is continuous in the configuration;
3. is bounded by `B Y`;
4. is analytic in `(e, u)` on `physV × {u | (u, 0) ∈ W}`. -/
theorem evDec_hatOf_value_fields (mb : ℕ)
    (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    {En : ((S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : Set (CTorus d L N₁ m₁ (k + 1)) → ℝ}
    (hloc : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u')
    (hbd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
      ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um tm Y u‖ ≤ B Y)
    (hJ2 : ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}))
    {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁) :
    (∀ (Y Y' : Set (CTorus d L N₁ m₁ (k + 1))), Y ⊆ Y' →
      (∀ y ∈ Y', box (cbase (cellSide L mb m₁ (k + 1)) y) (cellSide L mb m₁ (k + 1)) ⊆ Y') →
      ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      DepOn (blocksOf mb (k + 1) Set.univ Y')
        (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um 0 Y (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um 0 Y (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      ‖evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um 0 Y (Θ, S.hatOf mb ρ hp Φ)‖ ≤ B Y) ∧
    (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm p.2 0 Y
          ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf mb ρ hp Φ))
        (physV S a₁ ν eps ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  have hmem : ∀ Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N,
      Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
      ∀ Φ : ∀ b, (S.blockSplit mb hp).Ωb b, (Θ, S.hatOf mb ρ hp Φ) ∈
        XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} :=
    fun Θ hΘ Φ => ⟨hΘ, fun p => (S.hatOf_mem mb hρ hp Φ p).trans hρc⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y Y' hYY hY' Θ hΘ um hum Φ Φ' h
    have hhat := S.agHatFDir_hatOf mb hY' ρ hp Φ Φ' h
    exact hloc um 0 hum Y _ (hmem Θ hΘ Φ) _ (hmem Θ hΘ Φ')
      ⟨agreeOn_refl _ _, fun y hy i => hhat y (hYY hy) i⟩
  · intro Y Θ hΘ um hum
    have hW : (um, (0 : ℂ)) ∈ {w : ℂ × ℂ |
        (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} := hum
    have hc : ContinuousOn (fun ψ : unitPts S.G' × Fin N → ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol En Zm um 0 Y (Θ, ψ))
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ} := by
      have h1 := (hJ2 Y).continuousOn.comp
        (f := fun ψ : unitPts S.G' × Fin N → ℂ => ((Θ, ψ), (um, (0 : ℂ))))
        (by fun_prop) (fun ψ hψ => ⟨⟨hΘ, hψ⟩, hW⟩)
      rw [Function.comp_def] at h1
      exact h1
    exact hc.comp_continuous (S.continuous_hatOf mb ρ hp)
      (fun Φ q => (S.hatOf_mem mb hρ hp Φ q).trans hρc)
  · intro Y Θ hΘ a b ha hb hab um hum Φ
    exact hbd a b ha hb hab um 0 hum (by rw [norm_zero]; exact hb) Y _ (hmem Θ hΘ Φ)
  · intro Y Φ
    have hP := analyticOnNhd_physV_of_chart S a₁ ν eps (hJ2 Y)
    have key := hP.comp
      (f := fun r : physParam N S × ℂ => ((r.1, S.hatOf mb ρ hp Φ), (r.2, (0 : ℂ))))
      (fun r _ => (analyticAt_fst.prod analyticAt_const).prod
        (analyticAt_snd.prod analyticAt_const))
      (fun r (hr : r ∈ physV S a₁ ν eps ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) =>
        ⟨⟨hr.1, fun q => (S.hatOf_mem mb hρ hp Φ q).trans hρc⟩, hr.2⟩)
    rw [Function.comp_def] at key
    exact key

end ValueCore

section BlockActs

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block-level values of one inherited label, for given maps and any block index `mb`.**
For a step `S`, a label `τ = (j, y, X)` of the class `C` with the hypotheses of
`classOldMarkedLocal_joint_of`, given maps `(F₁, Sol, Fk)`, a mask `Zm`, a block index `mb` and a
clamp radius `0 < ρ ≤ c_ψ`, the value of the marked term of the domain `Y` at the second mark `0`,
`Φ ↦ evDec … Eτ … Zm um 0 Y (Θ, S.hatOf mb ρ hp Φ)`, depends only on the blocks inside any
`mb`-cell union `Y′ ⊇ Y`, is continuous in the configuration, is bounded by
`β⁻¹ E₀ e^{-κ₀ d(X) - 2κ_dec d(Y)}`, and is analytic in `(e, u)` on `physV × {u | (u, 0) ∈ W}`
(`evDec_hatOf_value_fields` with the clauses of `classOldMarkedLocal_joint_of`). -/
theorem classOldMarkedLocal_blockActs_of {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)} (hXp : IsPolyDom C.m₀ j X) (hy : y ∈ X)
    (hB : BgSetting N S.G' Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup S.G' C.m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne C.m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L C.m₀ m₁ j) E₀ = treeLenCovOne C.m₀ j X)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ r ∈ XiCRaw (C.Tm.gs j X) (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom j (C.Tm.gs j X) r.1 r.2)
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
          evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
              (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um 0 Y
            (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ um : ℂ,
      (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      Continuous (fun Φ : ∀ b, (S.blockSplit mb hp).Ωb b =>
        evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um 0 Y
          (Θ, S.hatOf mb ρ hp Φ))) ∧
    (∀ Y, ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ → ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      ‖evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm um 0 Y
          (Θ, S.hatOf mb ρ hp Φ)‖ ≤
        (β⁻¹ * P.E₀) *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov S.G' C.m₀ Y)) ∧
    (∀ Y, ∀ Φ : (∀ b, (S.blockSplit mb hp).Ωb b),
      AnalyticOnNhd ℂ (fun p : physParam N S × ℂ =>
        evDec X₁f C.m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (eTermFun S.G' Gk (C.Tm.gs j X) Hm (compWeight L a₁) Fk
            (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)) Zm p.2 0 Y
          ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf mb ρ hp Φ))
        (physV S a₁ ν eps ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  obtain ⟨-, e2, e3, -, -, hJ⟩ := classOldMarkedLocal_joint_of hb₁ hbC C hm hcl hβ hE₀ hj1 hjk
    hXp hy hB hF S.hk1 hG S.hG' cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1
    hlog hκP hchart hF₁an hF₁ hSolan hSolprop hFkan hFk Zm
  exact evDec_hatOf_value_fields S mb F₁ Sol (B := fun Y => (β⁻¹ * P.E₀) *
      Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov S.G' C.m₀ Y)) e2 e3 hJ
    hρ hρc hp

end BlockActs

end Balaban.Fluctuation
