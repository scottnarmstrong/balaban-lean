/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelValueUnique
public import Balaban.Inhabited.NewLevelPinUnique
public import Balaban.Inhabited.StepTowerCoreFamMark

/-!
# Uniqueness of the localized old terms of a new-level system

The inherited marks `G₁` and the explicit thick activities `H` of a `NewLevelSystem` are built from
`evDec` of the old term `eTermFun … FkL (β⁻¹ Eτ)`, with the pinned fields `F₁L`, `SolL`, `FkL`.
`oldTermEvDec_unique` shows that the localized old term does not depend on the choice of the pinned
fields, at the points of the chart.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Localization Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}

/-- **The localized old term agrees for two choices of the pinned fields.** -/
theorem oldTermEvDec_unique (S : StepSetting d L N₁ m₁ k N ϱ)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {jj : ℕ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f jj)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel (stepG d L N₁ m₁ k ϱ) k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ F₁' : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : DecFieldPin S κ BG F₁) (hF₁' : DecFieldPin S κ BG F₁')
    {Sol Sol' : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    (hSol : DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ Sol)
    (hSol' : DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ Sol')
    {Fk Fk' : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : FkPin S Gk Fk) (hFk' : FkPin S Gk Fk')
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {m₀ j : ℕ} (Zm : Finset (unitPts S.G')) (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) {um tm : ℂ}
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    {ψh : unitPts S.G' × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDec X₁f m₀ j 𝒦X S.a₁ S.ν S.hG' cc F₁ Sol
      (eTermFun S.G' Gk Gj (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk E) Zm um tm Y
      (rawOf D, ψh) =
    evDec X₁f m₀ j 𝒦X S.a₁ S.ν S.hG' cc F₁' Sol'
      (eTermFun S.G' Gk Gj (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk' E) Zm um tm Y
      (rawOf D, ψh) :=
  evDec_unique hC hk hG S.hG' cc hcψ hMX hmar hα hsm hF₁ hF₁' hSol hSol'
    (fun _ ht => eTermFun_unique le_rfl (one_le_scaledC0 d) hB hF hFk hFk' E ht) Zm 𝒦X hδ Y hD hψh

/-- **The tangent of the localized old term agrees for two choices of the pinned fields.** -/
theorem oldTermEvDec_deriv_unique (S : StepSetting d L N₁ m₁ k N ϱ)
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {jj : ℕ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hB : BgSetting N S.G' Gk Gj S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f jj)
    (hF : FlSetting N S.G' Gk (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hk : 1 ≤ k) (hG : IsLevel (stepG d L N₁ m₁ k ϱ) k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ F₁' : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : DecFieldPin S κ BG F₁) (hF₁' : DecFieldPin S κ BG F₁')
    {Sol Sol' : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N →
      ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
    (hSol : DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ Sol)
    (hSol' : DecSolPin S κ BG₂ (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ Sol')
    {Fk Fk' : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : FkPin S Gk Fk) (hFk' : FkPin S Gk Fk')
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {m₀ j : ℕ} (Zm : Finset (unitPts S.G')) (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) {um : ℂ}
    (hδ : (‖um‖ + ‖(0 : ℂ)‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D)
    {ψh : unitPts S.G' × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    deriv (fun t' : ℂ => evDec X₁f m₀ j 𝒦X S.a₁ S.ν S.hG' cc F₁ Sol
      (eTermFun S.G' Gk Gj (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk E) Zm um t' Y
      (rawOf D, ψh)) 0 =
    deriv (fun t' : ℂ => evDec X₁f m₀ j 𝒦X S.a₁ S.ν S.hG' cc F₁' Sol'
      (eTermFun S.G' Gk Gj (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) Fk' E) Zm um t' Y
      (rawOf D, ψh)) 0 := by
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖um‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hδ] with t ht
  exact oldTermEvDec_unique S hC hB hF hk hG cc hcψ hMX hmar hα hsm hF₁ hF₁' hSol hSol' hFk hFk'
    E Zm 𝒦X ht Y hD hψh

end Balaban.Inhabited
