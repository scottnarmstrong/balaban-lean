/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedHatRows

/-!
# Locality of the fluctuation correction for a general and for the masked decoupled tangent

(`MARKASM.md`, section 4, package 3.)  The row theorem `fluct_correction_rows_of_agree_on_component`
(`RowsCompose`) is proved for the tangent `hatPsiF`.  Its proof uses the tangent only through its
agreement on the component `Y` and through the bound hypotheses `DecHyp` on the tangent, which are
premises of the statement (the fixed-point equations involve the tangent only through `pertSource`).

* `fluct_correction_rows_of_tangent_agree`: the same statement for two arbitrary tangents `v, v'`
  with `v = v'` on `Y`.
* `fluct_correction_rows_of_agree_on_component_check`: the landed theorem re-derived from it.
* `fluct_correction_rows_marked_of_ball`: the statement for `markedHatPsiF ... Z u t` on both sides
  (same `Z, u, t`); the agreement of the tangents is proved from `markedHatPsiF_rows`.  The bounds
  `Hh, Hh'` on the marked tangent are hypotheses (the ball membership of the marked tangent).
* `fluct_correction_rows_marked_zero_of_ball`: the case `t = 0`, where `markedHatPsiF = u * hatPsiF`.

`MARK-BALL`, `MARK-AN`, `MARK-COUNT` (decoupled) and `MARK-PARAM` are NOT proved here; no mark family
is constructed, and nothing depends on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Fl

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The fluctuation correction on the component, for any tangent agreeing on the component.**  As
`fluct_correction_rows_of_agree_on_component`, with `hatPsiF` replaced by two arbitrary tangents
`v, v'` that agree at the sites of `Y`; the bounds on the tangents are the hypotheses `Hh, Hh'`. -/
theorem fluct_correction_rows_of_tangent_agree
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k)
    (hconn : HatConn Gp)
    (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {s s' : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ Gp.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁ → extS Gp s P = 1 ∧ extS Gp s' P = 1)
    (hs0 : ∀ P ∈ parCubes Gp X₁, P ∉ 𝒞 → extS Gp s P = 0 ∧ extS Gp s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y → extS Gp s P = extS Gp s' P)
    (h𝒞 : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp)
    (hdata : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z))
    (v v' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hv : ∀ y ∈ Y, v y = v' y)
    {φ φ₂ : Gp.Ω 1 × Fin N → ℂ} {α α₂ : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hI₂ : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂)
    (Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (v) 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    (Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α₂) (barField Gp D'.Ψ φ₂)
      (v') 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false (flAlpha Gp Hm α)
      (barField Gp D.Ψ φ) (pertSource Hm (compWeight L a₁) (v) 0)
      δα)
    (hsmδ : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s' false (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (v') 0) δα')
    (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
        Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (v) 0) δα (y, i) =
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (v') 0)
        δα' (y, i)) := by
  classical
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hC.hPmp.mem_Ω1 hx
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hC.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := h𝒞
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hY
  obtain ⟨hαSY, hφ⟩ := bgField_of_agree_on_component hC hconn hG hs hs' hD hD' hY hs1 hs0 hag
    hdata φ α φ₂ α₂ hI hI₂
  have hψ := hv
  have hDA : Dec2.RowsFl.DataAgreeRows Hm N (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y)
      (Dec2.RowsFl.RowF Hm (compWeight L a₁) ν (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y))
      (flAlpha Gp Hm α) (flAlpha Gp Hm α₂) (barField Gp D.Ψ φ) (barField Gp D'.Ψ φ₂)
      (v) (v')
      (0 : Hm.Ω 1 × Fin N → ℂ) 0 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx i => rfl⟩
    · have := hαSY ⟨x, hsubΩ x x.2⟩ (SYF_subset_SY_level hG hC.Sp hconn hY hx)
      show flAlpha Gp Hm α x = flAlpha Gp Hm α₂ x
      rw [flAlpha_of_prec hC.hPmp, flAlpha_of_prec hC.hPmp]
      exact this
    · have hxΩ := hsubΩ x x.2
      -- the sites of `R(S_Y^F)` read the approximate field only on `Y`
      have hres : ∀ u : Hm.Ω 1, (u : CTorus d L N₁ m₁ (k + 1)) ∈ Dec2.SYF (coverOf Gp) Hm
          (compWeight L a₁) ν X₁ 𝒞 Y → ∀ w ∈ resSites Hm (u : CTorus d L N₁ m₁ (k + 1)),
          approxDep Gp w ⊆ Y := fun u hu w hw =>
        (fluct_footprint_subset hG hHm hC.Sp hconn hY hu).2 w hw
      have hap : approxDep Gp (x : CTorus d L N₁ m₁ (k + 1)) ⊆ Y := by
        unfold Dec2.RowsFl.RowF at hx
        obtain ⟨-, u, hu, hxu⟩ := Finset.mem_filter.1 hx
        rcases hxu with hxu | ⟨w, hw, hxw⟩
        · rw [hxu]; exact hres u hu _ (mem_resSites_self _)
        · rw [hxw]; exact hres u hu _ (mem_resSites_of_entry_ne_zero hw)
      funext i
      show barField Gp D.Ψ φ x i = barField Gp D'.Ψ φ₂ x i
      simp only [barField, hxΩ, ↓reduceDIte]
      exact hφ ⟨x, hxΩ⟩ hap i
    · exact hψ x (Dec2.SYF_subset_Y hx)
  exact Dec2.RowsFl.i4a_local_fpS_rows_level hC.hS2.fam hC.SM hC.hκ.le hC.hM2
    (fun P => (hs P).le) (fun P => (hs' P).le) Hh Hh' hC.B_le hC.δ₁_le hIU hs1 hs0
    (fun P hP hPA => hag P hP (fun x hx => (hAcube P hPA).2 x hx)) hDA hHm hfix hsmδ hfix' hsmδ'

/-- The landed row theorem re-derived from the abstract one. -/
theorem fluct_correction_rows_of_agree_on_component_check
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
    {φ φ₂ : Gp.Ω 1 × Fin N → ℂ} {α α₂ : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hI₂ : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂)
    (Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    (Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α₂) (barField Gp D'.Ψ φ₂)
      (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false (flAlpha Gp Hm α)
      (barField Gp D.Ψ φ) (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0)
      δα)
    (hsmδ : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s' false (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0) δα')
    (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
        Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα (y, i) =
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0)
        δα' (y, i)):= by
  classical
  exact fluct_correction_rows_of_tangent_agree hC hG hHm hconn hrow hs hs' hD hD' hY
    hs1 hs0 hag h𝒞 hdata _ _ (hatPsiF_rows hC hk hG cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁ h𝒞 hdata ψh ψh' hh) hI hI₂ Hh Hh' hfix hsmδ hfix' hsmδ'

/-- **Marked rows.**  The fluctuation correction for the masked tangent `markedHatPsiF` with the same `Z, u, t` on both sides; the bounds `Hh, Hh'` of the marked tangent are hypotheses. -/
theorem fluct_correction_rows_marked_of_ball
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
    (Z : Finset (unitPts Gp)) (u t : ℂ)
    {φ φ₂ : Gp.Ω 1 × Fin N → ℂ} {α α₂ : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hI₂ : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂)
    (Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (markedHatPsiF a₁ ν hG cc F₁ Z u t s (rawOf D) ψh) 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    (Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α₂) (barField Gp D'.Ψ φ₂)
      (markedHatPsiF a₁ ν hG cc F₁ Z u t s' (rawOf D') ψh') 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false (flAlpha Gp Hm α)
      (barField Gp D.Ψ φ) (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u t s (rawOf D) ψh) 0)
      δα)
    (hsmδ : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s' false (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u t s' (rawOf D') ψh') 0) δα')
    (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
        Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u t s (rawOf D) ψh) 0) δα (y, i) =
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u t s' (rawOf D') ψh') 0)
        δα' (y, i)):= by
  classical
  exact fluct_correction_rows_of_tangent_agree hC hG hHm hconn hrow hs hs' hD hD' hY
    hs1 hs0 hag h𝒞 hdata _ _ (markedHatPsiF_rows hC hk hG cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁ h𝒞 hdata ψh ψh' hh Z u t) hI hI₂ Hh Hh' hfix hsmδ hfix' hsmδ'

/-- The case `t = 0` of the marked rows (the tangent is `u • hatPsiF`). -/
theorem fluct_correction_rows_marked_zero_of_ball
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
    (Z : Finset (unitPts Gp)) (u : ℂ)
    {φ φ₂ : Gp.Ω 1 × Fin N → ℂ} {α α₂ : Gp.Ω 1 → ℂ}
    (hI : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (hI₂ : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D' φ₂ α₂)
    (Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (markedHatPsiF a₁ ν hG cc F₁ Z u 0 s (rawOf D) ψh) 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    (Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α₂) (barField Gp D'.Ψ φ₂)
      (markedHatPsiF a₁ ν hG cc F₁ Z u 0 s' (rawOf D') ψh') 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁)
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s false (flAlpha Gp Hm α)
      (barField Gp D.Ψ φ) (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u 0 s (rawOf D) ψh) 0)
      δα)
    (hsmδ : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν s' false (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u 0 s' (rawOf D') ψh') 0) δα')
    (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈
        Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u 0 s (rawOf D) ψh) 0) δα (y, i) =
      dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (markedHatPsiF a₁ ν hG cc F₁ Z u 0 s' (rawOf D') ψh') 0)
        δα' (y, i)):= by
  classical
  exact fluct_correction_rows_of_tangent_agree hC hG hHm hconn hrow hs hs' hD hD' hY
    hs1 hs0 hag h𝒞 hdata _ _ (markedHatPsiF_rows hC hk hG cc hconn hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁ h𝒞 hdata ψh ψh' hh Z u 0) hI hI₂ Hh Hh' hfix hsmδ hfix' hsmδ'

/-- At `u = 1`, `t = 0` the masked tangent is `hatPsiF`, so the marked rows reduce to the landed
statement with the same tangents. -/
theorem markedHatPsiF_one_zero (hG : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (ψh : unitPts Gp × Fin N → ℂ) :
    markedHatPsiF a₁ ν hG cc F₁ Z 1 0 s Θ ψh = hatPsiF Gp a₁ ν hG cc F₁ s Θ ψh := by
  rw [markedHatPsiF_zero_t, one_smul]

end Fl

end Balaban.Localization
