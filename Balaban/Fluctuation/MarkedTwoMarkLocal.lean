/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedScaledCountDec

/-!
# Two-mark locality of the marked decoupled terms (`MarkedTwoMarkLocal`)

PLACEHOLDER
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Rows

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **Two-mark rows of the masked tangent.**  The hypotheses of `markedHatPsiF_rows`, for two marks
`(u, t)`, `(u', t')` of the same block `Z`: if the mark factors `u + 1[unitPt y ∈ Z] t` and
`u' + 1[unitPt y ∈ Z] t'` agree at the sites `y` of the component `Y`, the tangents agree on `Y`. -/
theorem markedHatPsiF_rows_two (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (hconn : HatConn Gp)
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
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    (Z : Finset (unitPts Gp)) (u t u' t' : ℂ)
    (hm : ∀ y ∈ Y, (u + if unitPt hG' y ∈ Z then t else 0) =
      (u' + if unitPt hG' y ∈ Z then t' else 0)) :
    ∀ y ∈ Y,
      markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh y =
        markedHatPsiF a₁ ν hG' cc F₁ Z u' t' s' (rawOf D') ψh' y := by
  intro y hy
  have h := hatPsiF_rows hC hk hG' cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁
    h𝒞 hdata ψh ψh' hh y hy
  funext i
  rw [markedHatPsiF_apply, markedHatPsiF_apply, hm y hy, h]

/-- **Two-mark fluctuation rows.**  The conclusion of `fluct_correction_rows_marked_of_ball` for two
marks `(u, t)`, `(u', t')` of the block `Z` whose factors agree on `Y`; the ball bounds on both
tangents are hypotheses. -/
theorem fluct_correction_rows_marked_two_of_ball
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hG : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k) (cc : ℂ)
    (hconn : HatConn Gp)
    (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
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
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (hX₁ : IsCellUnion (L ^ (k + 1)) (X₁ : Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (ψh ψh' : unitPts Gp × Fin N → ℂ)
    (hh : ∀ b' : unitPts Gp, UnitOut Gp Y b' → ∀ i, ψh (b', i) = ψh' (b', i))
    (Z : Finset (unitPts Gp)) (u t u' t' : ℂ)
    (hm : ∀ y ∈ Y, (u + if unitPt hG y ∈ Z then t else 0) =
      (u' + if unitPt hG y ∈ Z then t' else 0))
    {φ φ₂ : Gp.Ω 1 × Fin N → ℂ} {α α₂ : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hI₂ : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂)
    (Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (markedHatPsiF a₁ ν hG cc F₁ Z u t s (rawOf D) ψh) 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    (Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α₂) (barField Gp D'.Ψ φ₂)
      (markedHatPsiF a₁ ν hG cc F₁ Z u' t' s' (rawOf D') ψh') 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false (flAlpha Gp Hm α)
      (barField Gp D.Ψ φ)
      (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u t s (rawOf D) ψh) 0) δα)
    (hsmδ : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s' false (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u' t' s' (rawOf D') ψh') 0)
      δα')
    (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
        Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u t s (rawOf D) ψh) 0)
        δα (y, i) =
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u' t' s' (rawOf D') ψh') 0)
        δα' (y, i)) :=
  fluct_correction_rows_of_tangent_agree hC hG hHm hconn hrow hs hs' hD hD' hY hs1 hs0 hag h𝒞
    hdata _ _ (markedHatPsiF_rows_two hC hk hG cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1
      hs0 hag hX₁ h𝒞 hdata ψh ψh' hh Z u t u' t' hm) hI hI₂ Hh Hh' hfix hsmδ hfix' hsmδ'

end Rows

section Fan

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Two-mark sharp locality of the fan.**  `fanHL_local_marked` with two marks. -/
theorem fanHL_local_marked_two (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (Zm : Finset (unitPts Gp)) (um tm um' tm' : ℂ)
    (hδ₁ : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (hδ₁' : (‖um'‖ + ‖tm'‖) *
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
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∀ (C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))))
      (u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)),
      u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} →
      u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} →
      ∀ s s' : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ,
      s ∈ supN C (Real.exp κ) → s' ∈ supN C (Real.exp κ) →
      (∀ i ∈ C, Pset m₁ i.1.1 ⊆ compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C → s i = s' i) →
      AgHatDir hG' (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u' →
      (∀ y ∈ compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C,
        (um + if unitPt hG' y ∈ Zm then tm else 0) =
          (um' + if unitPt hG' y ∈ Zm then tm' else 0)) →
      FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm u s =
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um' tm' u' s' := by
  classical
  rintro C ⟨u, ψh⟩ ⟨u', ψh₂⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ ⟨⟨D', hD', rfl⟩, hψh₂⟩ s s' hs hs' hag hAg hmk
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  set cmap : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  have hψ : markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
      (rawOf D) ψh ∈ FlBall Hm δ₁ :=
    (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx hD hψh Zm hδ₁).1
  have hψ₂ : markedHatPsiF a₁ ν hG' cc F₁ Zm um' tm' (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s')
      (rawOf D') ψh₂ ∈ FlBall Hm δ₁ :=
    (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx' hD' hψh₂ Zm hδ₁').1
  set ψ := markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
    (rawOf D) ψh with hψdef
  set ψ₂ := markedHatPsiF a₁ ν hG' cc F₁ Zm um' tm' (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s')
    (rawOf D') ψh₂ with hψ₂def
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hFeq', hstrict', hSeq', hmem'⟩ :=
    point_facts_core hC hF₁ hSol hsx' hs1' hD' hψ₂
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ ψ)).1 (rawOf D, ψ) =
    Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s',
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
          D'.Ψ ψ₂)).1 (rawOf D', ψ₂)
  rw [hFeq, hFeq', hSeq, hSeq']
  -- notation
  set Yc : Set (CTorus d L N₁ m₁ (k + 1)) := compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := C.image cmap with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hcc_mem : ∀ i, cmap i ∈ cubeIdx Gp := fun i => i.1.2
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hPatchΩ : patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C ⊆
      ↑(Gp.Ω 1) := by
    intro x hx
    rcases hx with hx | hx
    · exact hX₁Ω hx
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact Pset_subset_Omega1 hcov (hcc_mem i) hxi
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cmap C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cmap C).1 hy.1) hadj)
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f →
      Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    intro P hP
    by_contra hnd
    have hsub := Pset_subset_of_not_disjoint (hX₁ ▸ hcov.polySetup) P.2 hnd
    unfold parCubes at hP
    rw [Finset.mem_filter] at hP
    apply hP.2
    intro y hy
    have := hsub (mem_cubeP.1 hy)
    exact Finset.mem_coe.1 this
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) ∉ C := fun hi =>
      hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨P, hPc⟩ =
        s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨P, hPc⟩ =
        s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs.1 _ hi, hs'.1 _ hi⟩
  have hsub : ∀ P ∈ 𝒞, (∀ x ∈ cubeP P, x ∈ Y) →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cmap i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub x (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨cmap i, hcc_mem i⟩ = s i from
        extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨cmap i, hcc_mem i⟩ = s' i from
        extParams_par s' i]
    exact this
  -- the data domain
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  have hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
      D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y) := by
    intro x hx y hy
    have := hAgΘ y (Or.inr ⟨x, (hmemY x).1 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    refine hsub P hP𝒞 (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    exact hSub ⟨x, Pset_subset_Omega1 hcov (hcc_mem i) (mem_cubeP.1 hx)⟩ hx
  have hYYc : (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) = Yc := by
    ext x; exact hmemY x
  -- the background fields agree
  obtain ⟨hαSY, hφY⟩ := i4b_local hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hYnn
    hs1E hs0E hagE hdata hI hI'
  -- the geometry of the pair
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hC.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hcc_mem i
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hC.hPmp.mem_Ω1 hx
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hYnn
  -- the fluctuation fields agree
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ₂ with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e') hsx' hstrict'
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  have Hh : DecHyp Hm (compWeight L a₁) ν false e.2.1 e.1 e.2.2.1 e.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false e'.2.1 e'.1 e'.2.2.1 e'.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have hX₁cell : IsCellUnion (L ^ (k + 1)) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    rw [hX₁]; exact X1_isCellUnion_unit hcov.hN
  have h𝒞' : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp := h𝒞c
  have hdataY : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z) := fun z hz => by
    have := hAgΘ z (Or.inl ((hmemY z).1 hz))
    exact ⟨this.1, fun _ => this.2⟩
  have hh : ∀ b : unitPts Gp, UnitOut Gp Y b → ∀ i, ψh (b, i) = ψh₂ (b, i) := by
    intro b hb i
    obtain ⟨x, -, hxb⟩ := (mem_unitPts Gp).1 b.2
    have hxΩ : x ∈ Gp.Ω 1 := by rw [hG'.Ω_one]; exact Finset.mem_univ _
    have hxY : x ∈ Y := hb ⟨x, hxΩ⟩ (by simp only [hxb])
    have hbx : b = unitPt hG' x := Subtype.ext hxb.symm
    rw [hbx]
    exact hAgψ x ((hmemY x).1 hxY) i
  have hmkY : ∀ y ∈ Y, (um + if unitPt hG' y ∈ Zm then tm else 0) =
      (um' + if unitPt hG' y ∈ Zm then tm' else 0) := fun y hy => hmk y ((hmemY y).1 hy)
  have hψY := markedHatPsiF_rows_two hC hk hG' cc hconn hMX hdm hα hsm hF₁ hsx hsx' hD hD' hYnn hs1E hs0E
    hagE hX₁cell h𝒞' hdataY ψh ψh₂ hh Zm um tm um' tm' hmkY
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ₂ with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e') hsx' hstrict'
  have Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ) ψ 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α') (barField Gp D'.Ψ φ') ψ₂ 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have h1 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e)).1 = δφ :=
    congrArg Prod.fst hSeq
  have h2 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e')).1 = δφ' :=
    congrArg Prod.fst hSeq'
  have h1' : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e)).2 = δα :=
    congrArg Prod.snd hSeq
  have h2' : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e')).2 = δα' :=
    congrArg Prod.snd hSeq'
  rw [h1'] at hfld hfix hs6
  rw [h2'] at hfld' hfix' hs6'
  have hflc := fluct_correction_rows_marked_two_of_ball hC hk hG' hG cc hconn hrow hMX hdm hα
    hsm hF₁ hsx hsx' hD hD' hYnn hs1E hs0E hagE hX₁cell h𝒞' hdataY ψh ψh₂ hh Zm um tm um' tm' hmkY hI hI' Hh Hh'
    hfix hs6 hfix' hs6'
  have hδeq : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i) := by
    intro y hy i
    rw [← h1, ← h2, hfld, hfld']
    exact hflc.2 y hy i
  have hZY : ∀ y ∈ Z, y ∈ Yc := fun y hy =>
    subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (hZ hy)
  have hXY' : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hαeq : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → α y = α' y := by
    intro y hy
    obtain ⟨z, hz, hyz, hQ, hhat⟩ := hBM y hy y.2
    refine hαSY y (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_, ?_⟩, hyz⟩)
    · intro P hP hPpar
      exact absurd hPpar (hQ P hP)
    · intro x hx
      exact hXY' _ (hhat x hx)
  refine hΦlocDir _ ⟨hmem, isLayerConstant_markedHatPsiF hG hG' cc F₁ Zm um tm _ _ _⟩ _ ⟨hmem', isLayerConstant_markedHatPsiF hG hG' cc F₁ Zm um' tm' _ _ _⟩ (fun y hy i => ?_) (fun y hy => hαeq y hy) (fun y hy i => ?_) ?_ ?_
  · exact hφY y ((hmemY _).2 (hZY _ hy)) i
  · exact hδeq y ((hmemY _).2 (hZY _ hy)) i
  · exact agreeOn_mono (thickSet_mono (fun y hy => hZY y hy)) hAgΘ
  · exact fun y hy => hψY y ((hmemY y).2 (hZY y hy))

end Fan

section Core

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The exposed expansion for a given pair `(F₁, Sol)`, with the two-mark clause.**  PLACEHOLDER -/
theorem i5_functional_hat_marked_exposed_pair (hk : 1 ≤ k) (hG : IsLevel Hm k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ : ℕ} {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) :
      -- sum identity, every mark of the radius set
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y (rawOf D, ψh)) ∧
      -- locality
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' →
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u =
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u') ∧
      -- the bound, every mark of the radius set
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- the bound, uniform on every closed bidisc
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- analyticity in the data
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, AnalyticOnNhd ℂ
          (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y)
          (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      -- analyticity in the marks, at fixed data
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) ∧
      -- Cauchy estimate for the mark derivative at `t = 0`
      (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖deriv (fun t : ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um t) Y u) 0‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y) / t₀) ∧
      -- sum identity for the derivatives at `t = 0`
      (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        deriv (fun tm : ℂ =>
          Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))) 0 =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), deriv (fun t : ℂ =>
            evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
              (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um t) Y (rawOf D, ψh)) 0) ∧
      -- two-mark locality: marks differing only on the mask, mask missing the domain
      (∀ um tm tm' : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        (‖um‖ + ‖tm'‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ y ∈ Y, unitPt hG' y ∉ Zm) →
        ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u =
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm') Y u) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  set W : Set (ℂ × ℂ) := {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
    (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} with hWdef
  have hWopen : IsOpen W := isOpen_markedRadiusSet _ _
  have hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}, ∀ w ∈ W,
      markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    intro σ hσ D hD ψh hψh w hw
    have hs' : ∀ i, ‖σ i‖ < Real.exp κ := fun i => by simpa using hσ i
    exact (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁
      (norm_extParams_lt hE1 hs') hD hψh Zm hw).1
  have hanaW := fanH_analytic_marked hC hk hG' cc
    {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} Zm W
    hMX hdm hα hsm hF₁an hF₁ hSolan hSolprop hΦan hSup
  have hbdW : ∀ w ∈ W, ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2 u s‖ ≤
        Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    intro w hw
    rintro ⟨u1, ψh⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
      norm_extParams_lt hE1 hs'
    have hψ := hSup s hs D hD ψh hψh w hw
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core hC hF₁ hSolprop hsx
      (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ
    show ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ (markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh))).1
      (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)‖ ≤ _
    rw [hFeq, hSeq]
    exact hΦbd _ hmem
  have hexp := fun (um tm : ℂ) (hw : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁) =>
    expansion_of_AE_hat_dir_exposed (a₁ := a₁) hC.HBp.hd hC.HBp.hL hG' hcov hX₁ hopt hκ₀ hκdec
      hκ h1 hlog hEb
      (FF := FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm)
      (analyticOnNhd_slice_marks hanaW (show (um, tm) ∈ W from hw))
      (fun u hu s hs => hbdW (um, tm) hw u hu s hs)
      (fanHL_local_marked hC hk hG hG' cc hcψ hMX hdm hα hsm Zm um tm hw hcov hX₁ hconn hrow hF₁
        hSolprop hZ hBM (fun t ht t' ht' => hΦlocDir t ht.1 t' ht'.1))
  have hanaM : ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u) W := by
    intro Y u hu
    have hslice : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × (ParIdx Gp
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm x.1.1 x.1.2 u x.2)
        (W ×ˢ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) := by
      refine hanaW.comp (f := fun x : (ℂ × ℂ) × (ParIdx Gp
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => (((u, x.2), x.1)))
        (fun x _ => (analyticAt_const.prod analyticAt_snd).prod analyticAt_fst)
        (fun x hx => ⟨⟨hu, hx.2⟩, hx.1⟩)
    intro w hw
    unfold evTerm
    refine Finset.analyticAt_fun_sum _ fun C _ => ?_
    exact analyticOnNhd_coef (Φ := fun x : (ℂ × ℂ) × (ParIdx Gp
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm x.1.1 x.1.2 u x.2) hE1 hWopen hslice
      (fun x hx => hbdW x.1 hx.1 u hu x.2 hx.2) C w hw
  have hsumall : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y (rawOf D, ψh) := by
    intro um tm hw D hD ψh hψh
    have hsum' := (hexp um tm hw).1 (rawOf D, ψh) ⟨⟨D, hD, rfl⟩, hψh⟩
    rw [← hsum']
    have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
      fun P => by simpa using hE1
    have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
        (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
    have hψ1 := (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx hD hψh
      Zm hw).1
    symm
    show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
            D.Ψ (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh))).1
        (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh) = _
    rw [extParams_one]
    set ψ' := markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (fun _ => 1) (rawOf D) ψh with hψ'def
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
      point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ1
    have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
    have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
      (bgC1_le_bgC0 d L N hd0))
    have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
      have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
    have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
    obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
      hνε hDom hI
    have hψeq : ψ' = liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
        (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
        (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
        tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
        (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
        (unitQ Gp) (unitP Gp) *ᵥ ψh))) := by
      rw [hψ'def, markedHatPsiF_eq_liftC]
      unfold hatSqrtF
      rw [hFeq, extS_one, hφ1, hα1]
      rfl
    rw [← hψeq]
    rw [hFeq, hSeq]
    obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
      flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
    have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
      (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
      (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
      (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
    have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = δφ := by
      have hSol1 : (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
          flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := congrArg Prod.fst hSeq
      unfold flFieldOne flField
      rw [hφ1, hα1]
      exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
        (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
        (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
        (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
        (hfld.symm.trans hSol1)
    rw [hφ1, hα1, hfl]
  refine ⟨hsumall, fun um tm hw => (hexp um tm hw).2.1,
    fun um tm hw => (hexp um tm hw).2.2.1, ?_, fun um tm hw => (hexp um tm hw).2.2.2, hanaM,
    ?_, ?_, ?_⟩
  · intro a b ha hb hab um tm hum htm Y u hu
    exact (hexp um tm (mem_markedRadiusSet_of_pos hC.δ₁_pos hab hum htm)).2.2.1 Y u hu
  · intro a b t₀ ha hb ht₀ htb hab um hum Y u hu
    exact norm_deriv_mark_le (W := W) (g := fun w : ℂ × ℂ =>
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
        (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u)
      (hanaM Y u hu) (fun w hw => (hexp w.1 w.2 hw).2.2.1 Y u hu) ht₀ htb
      (fun t ht => mem_markedRadiusSet_of_pos hC.δ₁_pos hab hum ht)
  · intro um h0 D hD ψh hψh
    have hu : (rawOf D, ψh) ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := ⟨⟨D, hD, rfl⟩, hψh⟩
    refine deriv_sum_marks _ hWopen (um := um) (show (um, (0 : ℂ)) ∈ W from h0) ?_ ?_
    · intro t ht
      exact hsumall um t ht D hD ψh hψh
    · intro Y
      exact differentiableAt_mark_slice (g := fun w : ℂ × ℂ =>
        evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y (rawOf D, ψh))
        ((hanaM Y (rawOf D, ψh) hu) (um, 0) h0)

  · intro um tm tm' hr hr' Y hY u hu
    have hc : ∀ i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), i.1.1 ∈ cubeIdx Gp :=
      fun i => i.1.2
    unfold evTerm
    refine Finset.sum_congr rfl fun C hC' => ?_
    obtain ⟨-, hYC⟩ := (mem_connFams (fun i : ParIdx Gp
      (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)).1 hC'
    have hsub : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C ⊆ Y := by
      rw [← hYC]
      have e1 : compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C =
          compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (X1 Gp m₀ j 𝒦X) C := congrArg (fun S => compY _ S C) hX₁
      rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
    refine coef_congr_near (Real.one_lt_exp_iff.2 hC.hκ) fun w hw => ?_
    exact fanHL_local_marked_two hC hk hG hG' cc hcψ hMX hdm hα hsm Zm um tm um tm' hr hr' hcov hX₁
      hconn hrow hF₁ hSolprop hZ hBM (fun t ht t' ht' => hΦlocDir t ht.1 t' ht'.1)
      C u u hu hu w w hw hw (fun _ _ _ => rfl) (agHatDir_refl hG' _ u)
      (fun y hy => by simp [hY y (hsub hy)])


end Core

end Balaban.Localization
