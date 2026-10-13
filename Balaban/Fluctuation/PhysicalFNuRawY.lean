/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.PhysicalReadsFNu
public import Balaban.Fluctuation.RowsCompose

/-!
# Exact locality of the source summand `F` and the mass summand `ν` on the component

The landed locality of the physical terms asks for raw data agreeing on `thickSet Y`.  Here the raw
data (and the source amplitude) agree on the component `Y` itself, and the hat variables agree at
the unit points of `Y`.

Both statements run the row comparison `fluct_correction_rows_of_agree_on_component` and add the
reads of the functional itself:

* `fsite_exact_local` (source `F`): the term `g(y,i) δφ(y,i)` at a site `y` of `X₁` (which lies in
  `Y`, `raw_site_mem_comp`) agrees for the two inputs; the amplitude is read by
  `source_amplitude_read`, the fluctuation field by the row comparison on `Y`.
* `nuBlock_exact_local` (mass `ν`): the block functional `nuBlockFun` agrees.  At a site `x` of the
  block either `δφ(x) = 0` (then the density vanishes for both inputs), or `x` is in the core, hence
  in `S_Y^F` (`mem_SYF_of_mem_core`), and the background field is read inside `Y`
  (`reads_subset_of_mem_SYF`, `bgField_of_agree_on_component`); the raw field is read by
  `raw_field_read`.

Hypotheses beyond the thick statements (see the report): the component `Y` of `V(𝒞) ∩ Ω₁` with
`Y = compY` of the marked family (`hY`, `hmemY`), the parameter vectors equal to one off the
parameter cubes of `X₁`, zero on those of `X₁` not in `𝒞`, and equal on the cubes of `𝒞` inside `Y`
(`hs1`, `hs0`, `hag`), and the footprint hypotheses `hrow`, `hconn`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section FNuRawY

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
  (hG : IsLevel Gp (k + 1)) (hHm : IsLevel Hm k) (cc : ℂ) (hconn : HatConn Gp)
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
  (hsmδ' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
  {ι : Type*} (cen : ι → ℕ × CTorus d L N₁ m₁ (k + 1)) (C : Finset ι)
  (hmemY : ∀ x, x ∈ Y ↔ x ∈ compY cen (↑X₁ : Set (CTorus d L N₁ m₁ (k + 1))) C)

include hC hk hG hHm hconn hrow hMX hmar hα hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁ h𝒞 hdata hh
  hI hI₂ Hh Hh' hfix hsmδ hfix' hsmδ'  cen C hmemY

/-- **Exact locality of the source summand `F`, one site.**  Raw data agreeing on the component `Y`
(`hdata`), hat variables agreeing at the unit points of `Y` (`hh`), and source amplitudes agreeing on
`Y` give equal values of `g(y,i) δφ(y,i)` at every site `y` of `X₁`, for decoupling parameter
vectors `s, s'` equal to one off `X₁`, zero on the cubes of `X₁` outside `𝒞`, equal on the cubes of
`𝒞` inside `Y`.  The fluctuation field is the field `dphi` of the fixed points `δα, δα'`
(`flField` when `δα = flMult`).  Needs: the row comparison (`hC … hsmδ'`), `raw_site_mem_comp`
(`hmemY`), `source_amplitude_read`. -/
theorem fsite_exact_local (g g' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (hg : ∀ z ∈ Y, g z = g' z)
    (ψ₁ ψ₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ X₁) (i : Fin N) :
    g y i * siteFun Gp Hm y i (φ, α)
      (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα)
      (rawOf D, ψ₁) =
    g' y i * siteFun Gp Hm y i (φ₂, α₂)
      (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0) δα')
      (rawOf D', ψ₂) := by
  classical
  have hflc := fluct_correction_rows_of_agree_on_component hC hk hG hHm cc hconn hrow hMX hmar hα
    hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁ h𝒞 hdata ψh ψh' hh hI hI₂ Hh Hh' hfix hsmδ hfix'
    hsmδ'
  have hyY : y ∈ Y := raw_site_mem_comp cen X₁ C Y hmemY hy
  have hga : g y = g' y := source_amplitude_read cen X₁ C Y hmemY g g' hg hy
  have hsv : svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα) y i =
      svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0) δα')
        y i := by
    by_cases hyΩ : y ∈ Hm.Ω 1
    · rw [svec_of_mem' _ hyΩ, svec_of_mem' _ hyΩ]
      exact hflc.2 ⟨y, hyΩ⟩ hyY i
    · rw [svec_of_not_mem Hm _ hyΩ, svec_of_not_mem Hm _ hyΩ]
  show g y i * svec Hm _ y i = g' y i * svec Hm _ y i
  rw [hga, hsv]

/-- **Exact locality of the mass summand `ν`, one block.**  Under the hypotheses of
`fsite_exact_local`, and for a block whose sites lie in `X₁`, the block functional `nuBlockFun`
(`∑_x [δφ(x)(φ_s(x) - h(x)) + ½ δφ(x)²]`) takes equal values for the two inputs.  Needs: the row
comparison; `raw_site_mem_comp`; `raw_field_read`; the dichotomy (`dphi_svec_eq_zero_of_not_mem_core`,
`mem_SYF_of_mem_core`, `reads_subset_of_mem_SYF`) for the background field at a site where `δφ`
does not vanish (`bgField_of_agree_on_component`). -/
theorem nuBlock_exact_local (ψ₁ ψ₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ ((k + 1) - (n + 1))))
    (hblk : (↑(blockSites d L N₁ m₁ (k + 1) n z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑X₁) :
    nuBlockFun Gp Hm n z (φ, α)
      (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s) (flAlpha Gp Hm α)
        (barField Gp D.Ψ φ)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα)
      (rawOf D, ψ₁) =
    nuBlockFun Gp Hm n z (φ₂, α₂)
      (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
        (barField Gp D'.Ψ φ₂)
        (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0) δα')
      (rawOf D', ψ₂) := by
  classical
  have hflc := fluct_correction_rows_of_agree_on_component hC hk hG hHm cc hconn hrow hMX hmar hα
    hsm hF₁ hs hs' hD hD' hY hs1 hs0 hag hX₁ h𝒞 hdata ψh ψh' hh hI hI₂ Hh Hh' hfix hsmδ hfix'
    hsmδ'
  have hbg := bgField_of_agree_on_component hC hconn hG hs hs' hD hD' hY hs1 hs0 hag hdata
    φ α φ₂ α₂ hI hI₂
  unfold nuBlockFun
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxX : x ∈ X₁ := hblk (Finset.mem_coe.2 hx)
  have hxY : x ∈ Y := raw_site_mem_comp cen X₁ C Y hmemY hxX
  have hδ : ∀ i, svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s)
      (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα) x i =
    svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s') (flAlpha Gp Hm α₂)
      (barField Gp D'.Ψ φ₂)
      (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s' (rawOf D') ψh') 0) δα') x i := by
    intro i
    by_cases hxΩ : x ∈ Hm.Ω 1
    · rw [svec_of_mem' _ hxΩ, svec_of_mem' _ hxΩ]
      exact hflc.2 ⟨x, hxΩ⟩ hxY i
    · rw [svec_of_not_mem Hm _ hxΩ, svec_of_not_mem Hm _ hxΩ]
  by_cases h0 : ∀ i, svec Hm (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν s)
      (flAlpha Gp Hm α) (barField Gp D.Ψ φ)
      (pertSource Hm (compWeight L a₁) (hatPsiF Gp a₁ ν hG cc F₁ s (rawOf D) ψh) 0) δα) x i = 0
  · rw [nuDensity_eq_zero_of_svec _ _ _ h0,
      nuDensity_eq_zero_of_svec _ _ _ (fun i => (hδ i).symm.trans (h0 i))]
  · push Not at h0
    obtain ⟨i₀, hi₀⟩ := h0
    have hxΩ : x ∈ Hm.Ω 1 := by
      by_contra hn
      exact hi₀ (svec_of_not_mem Hm _ hn i₀)
    have hcore : x ∈ Dec2.Core (coverOf Gp) (Dec2.extS (coverOf Gp) s) := by
      by_contra hn
      exact hi₀ (dphi_svec_eq_zero_of_not_mem_core (Dec2.footLocalGeom_coverOf Gp) s _ _ _ _ hn i₀)
    have hSYF := mem_SYF_of_mem_core hG hHm hC.Sp hconn hY (fun P hP hn => (hs0 P hP hn).1)
      hcore hxΩ hxY
    obtain ⟨-, -, -, -, happ⟩ := reads_subset_of_mem_SYF hG hHm hC.Sp hconn hY hSYF
    have hxG : x ∈ Gp.Ω 1 := by rw [hG.Ω_one]; exact Finset.mem_univ _
    have hphi : ∀ i, svec Gp φ x i = svec Gp φ₂ x i := fun i => by
      rw [svec_of_mem' _ hxG, svec_of_mem' _ hxG]
      exact hbg.2 ⟨x, hxG⟩ happ i
    have hhh : ∀ i, (rawOf D).2 x i = (rawOf D').2 x i := fun i => by
      have := raw_field_read cen X₁ C Y hmemY (fun w => D.h w) (fun w => D'.h w)
        (fun w hw => (hdata w hw).2 (by rw [hG.Ω_one]; exact Finset.mem_univ _)) hxX
      exact congrFun this i
    unfold nuDensity
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hδ i, hphi i]
    show _ + _ = svec Hm _ x i * (svec Gp φ₂ x i - (rawOf D').2 x i) + _
    rw [hhh i]

end FNuRawY

end Balaban.Localization

