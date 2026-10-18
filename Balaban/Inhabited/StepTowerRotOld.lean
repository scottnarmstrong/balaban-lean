/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotMark
public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Fluctuation.InteractionHatE

/-!
# Spin covariance of the old-term functional and of its localized terms

`eTermFun_rot_real`: for the old term `E` of a label `τ` that is invariant under the rotation `R`
at the pairs of fields of the set `𝒮` that contains the composed step data, the functional
`eTermFun … E` is invariant at the realizable triples whose rotation is again realizable.  The
raw datum read by the old term is rotated by `d2raw_d1Triple_rot_of_chain`; the invariance of `E` is
needed only there.

`evDec_eTerm_rot`: the localized terms `evDec` of that functional along the masked tangent are spin
invariant.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Matrix

section Old

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
variable {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}

/-- **The old-term functional is spin invariant at the realizable triples.**  `E` is invariant under
the rotation `R` at the raw data of `𝒮` whose rotation is again in `𝒮`, and `𝒮` contains the raw
datum read by the old term at every realizable triple. -/
theorem eTermFun_rot_real {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (h𝒮 : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hE : ∀ r ∈ 𝒮, rotRaw (cmat Q) r ∈ 𝒮 → E (rotRaw (cmat Q) r) = E r)
    (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))
    (ht : (bg, δφ, u) ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (ht' : ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ∈
      FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E (rotFld (cmat Q) bg.1, bg.2)
        (rotFld (cmat Q) δφ) (rotU (cmat Q) u) =
      eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E bg δφ u := by
  obtain ⟨D, ψ', hlc, -, -, hd1, hD2, -⟩ := eTerm_chain_of_one_le hb₁ hbC hB hF hFk ht
  obtain ⟨D2, ψ2, hlc2, -, -, hd1', hD2', -⟩ := eTerm_chain_of_one_le hb₁ hbC hB hF hFk ht'
  have hr := d2raw_d1Triple_rot_of_chain hB.hP hF.hPm hB.hq hQ hd1 hD2 hd1' hD2'
  show E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁)
      (rotFld (cmat Q) bg.1) (rotFld (cmat Q) δφ) (rotU (cmat Q) u))) =
    E (D2raw Gk Gj (compWeight L a₁) Fk (d1Triple Gp Gk Hm (compWeight L a₁) bg.1 δφ u))
  rw [hr]
  refine hE _ (h𝒮 (bg, δφ, u) ht) ?_
  have h2 := h𝒮 ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ht'
  rw [hr] at h2
  exact h2

/-- **The localized terms of the old-term functional along the masked tangent are spin
invariant.**  `evDec_rot_real` for `Φ = eTermFun … E`, whose invariance at the realizable triples is
`eTermFun_rot_real`. -/
theorem evDec_eTerm_rot {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) (hk : 1 ≤ k)
    (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (h𝒮 : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮)
    (hE : ∀ r ∈ 𝒮, rotRaw (cmat Q) r ∈ 𝒮 → E (rotRaw (cmat Q) r) = E r)
    {ι : Type*} [DecidableEq ι] [Fintype ι] {m₀ : ℕ}
    (Zm : Finset (unitPts Gp)) (j' : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ (k + 1)))
    {um tm : ℂ}
    (hδ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDec X₁f m₀ j' 𝒦X a₁ ν hG' cc F₁ Sol (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
        Zm um tm Y (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) =
      evDec X₁f m₀ j' 𝒦X a₁ ν hG' cc F₁ Sol (eTermFun Gp Gk Gj Hm (compWeight L a₁) Fk E)
        Zm um tm Y (rawOf D, ψh) :=
  evDec_rot_real (flCore_of hB hF) hk hG hG' cc hcψ hMX hmar hα hsm hF₁ hSol hQ
    (fun bg δφ u ht ht' => eTermFun_rot_real hb₁ hbC hB hF hFk h𝒮 hQ hE bg δφ u ht ht') Zm j' 𝒦X
    hδ Y hD hψh

end Old

end Balaban.Inhabited
