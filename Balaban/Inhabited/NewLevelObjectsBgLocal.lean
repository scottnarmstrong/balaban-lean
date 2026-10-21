/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelTermsBgLocal
public import Balaban.Fluctuation.NewLevelZeroSourceBgFields
public import Balaban.Inhabited.NewLevelBridgeMarksBgCast

/-!
# Locality of the objects of the new level recomputed on a local generating set

P3 pp. 78-79 and Lemma 4.2 at `Gb`, (AE2) (route R-LOC, the form of (A3)): every activity and mark of
the new level recomputed on a background generating set `Gb` with the canonical transport takes the
same value at two parameters of `Gb` whose raw data agree near the label, as soon as its terms do.

* `zeroTermBg_canon_local`, `zeroActBg_canon_local`: the zero-source terms and activities of a label
  with the margin in `Gb` agree at two data of the chart of `Gb` agreeing on `thickSet Y`
  (`evDecBg_canon_local_blockEnergy` along the ray, `rayTerm_dl3_congr_of_box`);
* `oldActBg_congr_of_terms`, `oldMarkGBg_congr_of_terms`: the activities and the marks of the old
  labels agree at two parameters of the chart and two configurations when their terms `evDecBg` do
  (on the radius set of the marks; the forms of (A3) and (A4));
* `e1MarkGParamGBgOn_congr_of_terms`: the bridge marks agree at two parameters of the chart when the
  terms of the block energies of the pairs of the bridge do (`decMarkCorrBg_eq_of_evDecBg`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Finset

section Zero

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

open Classical in
/-- **Locality of the zero-source terms recomputed on `Gb`** (P3 Lemma 4.2 at `Gb`, (AE2)): for a
label `Y` with the margin in `Gb`, blocks read inside their regions (`hZ`) and with the block margin
(`hBM`), the zero-source terms `zeroTermBg` with the canonical transport at two data `Θ`, `Θ'` of the
chart of `Gb` that agree on `thickSet Y` are equal, for a ray inside the box `|ψ̂| ≤ c_ψ`. -/
theorem zeroTermBg_canon_local {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hHm : Hm.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L S.a₁) S.ν) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {m₀ : ℕ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup S.G' m₀ (jV z) (XV z) (𝒦XV z))
    (hX₁ : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ z (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hZ : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hBM : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (ω : ℂ → ℂ) {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y)
    (x₀ w : unitPts S.G' × Fin N → ℂ) (σ : ℂ) (hσx : ∀ q, ‖σ‖ * ‖x₀ q‖ < cψ)
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hag : agreeOn (thickSet S.G' Y) Θ Θ') :
    zeroTermBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ Θ =
      zeroTermBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ Θ' := by
  have hW : (‖(1 : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rw [norm_one, norm_zero, add_zero, one_mul]
    exact hδ₁c
  unfold zeroTermBg
  refine congrArg (fun x => -(S.β : ℂ) * x) (Finset.sum_congr rfl fun z _ => ?_)
  by_cases hY : Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z)
  · simp only [hY, ↓reduceIte]
    refine rayTerm_dl3_congr_of_box ω (fun ψ hψ => ?_) hσx
    exact evDecBg_canon_local_blockEnergy hC S.hk1 S.hG' hHm hHmtop hrow _ hcψ hMX hdm hα hsm
      (hcov z) (hX₁ z) (hF₁ z) (hSol z) z (hZ z) (hBM z) ∅ 1 0 hW Y hYm (Θ, ψ) ⟨hΘ, hψ⟩
      (Θ', ψ) ⟨hΘ', hψ⟩ ⟨hag, fun _ _ _ => rfl⟩
  · simp only [hY, ↓reduceIte]

open Classical in
/-- **Locality of the zero-source activities recomputed on `Gb`** (P3 Lemma 4.2 at `Gb`, (AE2)):
under the hypotheses of `zeroTermBg_canon_local` and `2 ρ ≤ c_ψ` (the clamped hat field of radius
`ρ` stays in the box along the ray `|u| < 2`), the zero-source activities `zeroActBg` (gate radius
`ε`) at two parameters of the chart of `Gb` whose raw data agree on `thickSet Y` are equal. -/
theorem zeroActBg_canon_local {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hHm : Hm.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L S.a₁) S.ν) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {m₀ : ℕ}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ z, CovSetup S.G' m₀ (jV z) (XV z) (𝒦XV z))
    (hX₁ : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ z (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hZ : ∀ z, readSites Hm k z ⊆ ↑(X₁V z))
    (hBM : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (ω : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρc : 2 * ρ ≤ cψ) (hp : 0 < S.p₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y) {θ θ' : physParamBg N Gb}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hag : agreeOn (thickSet S.G' Y) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y Φ =
      zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ' u Y Φ := by
  by_cases hu : ‖u‖ < 2
  · rw [zeroActBg_of_mem S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hθ hu Y Φ,
      zeroActBg_of_mem S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hθ' hu Y Φ]
    refine congrArg (fun x => u ^ 2 * x) ?_
    refine zeroTermBg_canon_local S hC hHm hHmtop hrow hcψ hMX hdm hα hsm hcov hX₁ hF₁ hSol hZ hBM
      hδ₁c ω hYm _ _ u (fun q => ?_) hθ hθ' hag
    have hq : ‖S.hatOf m₀ ρ hp Φ q‖ ≤ ρ := S.hatOf_mem m₀ hρ hp Φ q
    calc ‖u‖ * ‖S.hatOf m₀ ρ hp Φ q‖ ≤ ‖u‖ * ρ := mul_le_mul_of_nonneg_left hq (norm_nonneg u)
      _ < 2 * ρ := mul_lt_mul_of_pos_right hu hρ
      _ ≤ cψ := hρc
  · rw [zeroActBg_of_not S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps (fun h => hu h.2) Y Φ,
      zeroActBg_of_not S Gb _ X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps (fun h => hu h.2) Y Φ]

end Zero

section Old

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱd : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱd} (Tr : BgTransport S.G' Gb N)
  (Zb : Finset (unitPts Gb)) {ι : Type*} [Fintype ι]
  (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ : ℕ) (jL : ι → ℕ)
  (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
  (F₁ : ι → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
  (Sol : ι → Dec2.DecParams (coverOf Gb) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (Φ : ι → ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Gd.Ω 1 × Fin N → ℂ) →
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
  (ρ : ℝ) (hp : 0 < S.p₁) (Ru eps : ℝ)

open Classical in
/-- **The activities of the old labels at two parameters of the chart agree when their terms do**:
if the terms `evDecBg … um 0 Y` of the old terms whose expansion has the domain `Y` agree at the
raw data of `θ` and `θ'` (both in the chart) and the hat fields of the configurations `Ψ`, `Ψ'` for
`‖um‖ < R_u`, then so do the activities `oldActBg … θ Y u Ψ` and `oldActBg … θ' Y u Ψ'`. -/
theorem oldActBg_congr_of_terms (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    {θ θ' : physParamBg N Gb}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (Y : {Y // Y ∈ 𝒴C})
    (Ψ Ψ' : ∀ b, (S.blockSplit 1 hp).Ωb b)
    (hterm : ∀ τ, Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) → ∀ um : ℂ, ‖um‖ < Ru →
        evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb S.a₁ S.ν Tr
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ) (Φ τ) Zb um 0 Y.1
            ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Tr.res (S.hatOf 1 ρ hp Ψ)) =
          evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb S.a₁ S.ν Tr
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ) (Φ τ) Zb um 0 Y.1
            ((θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Tr.res (S.hatOf 1 ρ hp Ψ')))
    (hRu : 0 < Ru) (u : ℂ) :
    oldActBg S Gb Tr Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps 𝒴C θ Y u Ψ =
      oldActBg S Gb Tr Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps 𝒴C θ' Y u Ψ' := by
  by_cases hu : ‖u‖ < Ru
  · have h0 : ‖(0 : ℂ)‖ < Ru := by rw [norm_zero]; exact hRu
    unfold oldActBg
    simp only [hθ, hθ', hu, and_self, ↓reduceIte]
    refine Finset.sum_congr rfl fun τ _ => ?_
    by_cases hY : Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)
    · simp only [hY, ↓reduceIte]
      rw [hterm τ hY u hu, hterm τ hY 0 h0]
    · simp only [hY, ↓reduceIte]
  · unfold oldActBg
    simp only [hu, and_false, ↓reduceIte]

open Classical in
/-- **The marks of the old labels at two parameters of the chart agree when their terms do**: if the
terms `evDecBg … u t q.2` of the old term `q.1` agree at the raw data of `θ` and `θ'` (both in the
chart) and the hat fields of the configurations `Ψ`, `Ψ'` for `‖u‖ < R_u`, `‖t‖ < t₀` (`t₀ > 0`),
then so do the marks `oldMarkGBg … θ q u Ψ` and `oldMarkGBg … θ' q u Ψ'`. -/
theorem oldMarkGBg_congr_of_terms (z : RootIdx d L N₁ m₁ (k + 1)) {θ θ' : physParamBg N Gb}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (Ψ Ψ' : ∀ b, (S.blockSplit 1 hp).Ωb b)
    (hterm : ∀ um : ℂ, ‖um‖ < Ru → ∀ t : ℂ, ‖t‖ < t₀ →
      evDecBg S.G' (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) Gb S.a₁ S.ν Tr
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1) (Φ q.1.1) Zb um t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Tr.res (S.hatOf 1 ρ hp Ψ)) =
        evDecBg S.G' (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) Gb S.a₁ S.ν Tr
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1) (Φ q.1.1) Zb um t q.1.2
          ((θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Tr.res (S.hatOf 1 ρ hp Ψ')))
    (u : ℂ) :
    oldMarkGBg S Gb Tr Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z θ q u Ψ =
      oldMarkGBg S Gb Tr Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps z θ' q u Ψ' := by
  by_cases hu : ‖u‖ < Ru
  · unfold oldMarkGBg
    simp only [hθ, hθ', hu, and_self, ↓reduceIte]
    refine congrArg (fun x => (S.β : ℂ) * x) (Filter.EventuallyEq.deriv_eq ?_)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ht₀] with t ht
    exact hterm u hu t (mem_ball_zero_iff.1 ht)
  · unfold oldMarkGBg
    simp only [hu, and_false, ↓reduceIte]

end Old

section Bridge

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

open Classical in
/-- **The bridge marks at two parameters of the chart agree when the terms of the block energies
do**: if for every pair `(b, Y)` of the root `z` whose bridge is `Y′` the terms of the block energy
of `b` agree at the raw data of `θ` and `θ'` (both in the chart of `Gb`) at every pair of marks of
the radius set `(‖v‖ + ‖t‖) m_R < δ₁` and the hat fields of the configurations `Ψ`, `Ψ'`, then the
bridge marks `e1MarkGParamGBgOn … θ Y′ u Ψ` and `e1MarkGParamGBgOn … θ' Y′ u Ψ'` agree, when `(17/16) m_R < δ₁`. -/
theorem e1MarkGParamGBgOn_congr_of_terms (T : BgTransport S.G' Gb N)
    (Zb : Finset (unitPts Gb))
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (ρ : ℝ) (hp : 0 < S.p₁) (z : RootIdx d L N₁ m₁ (k + 1)) (eps : ℝ) {mR δ₁ : ℝ}
    (hmR : (17 / 16 : ℝ) * mR < δ₁) (hδ₁ : 0 < δ₁) {θ θ' : physParamBg N Gb}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps)
    (Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
    (Ψ Ψ' : ∀ b, (S.blockSplit 1 hp).Ωb b)
    (hterm : ∀ q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (e1DomG S) z, bridge 1 z q.2 = Y'.1 → ∀ v t : ℂ, (‖v‖ + ‖t‖) * mR < δ₁ →
        evDecBg S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k q.1)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k q.1)) Gb S.a₁ S.ν T
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1) (Sol q.1)
            (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k q.1) Zb v t q.2
            ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), T.res (S.hatOf 1 ρ hp Ψ)) =
          evDecBg S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k q.1)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k q.1)) Gb S.a₁ S.ν T
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1) (Sol q.1)
            (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k q.1) Zb v t q.2
            ((θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), T.res (S.hatOf 1 ρ hp Ψ')))
    (u : ℂ) :
    e1MarkGParamGBgOn S Gb T Zb F₁ Sol ρ hp z Gb eps θ Y' u Ψ =
      e1MarkGParamGBgOn S Gb T Zb F₁ Sol ρ hp z Gb eps θ' Y' u Ψ' := by
  by_cases hu : ‖u‖ < (17 / 16 : ℝ)
  · have hum : ‖u‖ * mR < δ₁ := by
      rcases le_or_gt 0 mR with h | h
      · nlinarith [norm_nonneg u]
      · nlinarith [norm_nonneg u]
    rw [e1MarkGParamGBgOn_of_mem S Gb T Zb F₁ Sol ρ hp z Gb eps θ Y' u Ψ hθ hu,
      e1MarkGParamGBgOn_of_mem S Gb T Zb F₁ Sol ρ hp z Gb eps θ' Y' u Ψ' hθ' hu,
      markedOutDec_decMarkCorrTermBg_eq S F₁ Sol ρ hp (S.β : ℂ) _ u Ψ z Y'.1,
      markedOutDec_decMarkCorrTermBg_eq S F₁ Sol ρ hp (S.β : ℂ) _ u Ψ' z Y'.1]
    refine Finset.sum_congr rfl fun q hq => congrArg (fun x => -(S.β : ℂ) * x) ?_
    obtain ⟨hqm, hbr⟩ := Finset.mem_filter.1 hq
    exact decMarkCorrBg_eq_of_evDecBg_conf S (fun v t hvt => hterm q hqm hbr v t hvt) hum hδ₁
  · rw [e1MarkGParamGBgOn_of_not S Gb T Zb F₁ Sol ρ hp z Gb eps θ Y' u Ψ fun h => hu h.2,
      e1MarkGParamGBgOn_of_not S Gb T Zb F₁ Sol ρ hp z Gb eps θ' Y' u Ψ' fun h => hu h.2]

end Bridge

end Balaban.Inhabited
