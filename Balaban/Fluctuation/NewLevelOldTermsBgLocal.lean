/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelOldTermsBgSetting
public import Balaban.Fluctuation.SharpENu
public import Balaban.Fluctuation.NewLevelTermsBgLocal

/-!
# (AE2) of Lemma 4.2 at a background generating set for the old terms

P3 pp. 78-79 and Lemma 4.2 at `Gb`, (AE2), for the terms of the old labels of the new level
recomputed on a background generating set `Gb` with the canonical transport (route R-LOC): the
agreement property of the row theorems for the old-term functional `eTermFun Gb …` and the
locality of its terms `evDecBg … Y` for every label `Y` with `LabelMargin Gb Y`.

When every site within lift distance `3 L^{k+1}` of the frozen region `X₁` of the old term lies in
the top layer of `Gb`, the old term has the settings of the step on `Gb` (`bgSetting_of_top`,
`flSetting_of_top`), the approximate field of `Gb` read at the composite sites of its data sites
reads `X₁` only (`approxDep_composeDep_subset_X1_of`, the active blocks there being of the top
layer: `active_layer_of_near`), and the functional has the agreement property
(`eTermFun_eq_of_component_of`); the terms are local by `evDecBg_canon_local_of`.  Otherwise no
label with the margin contains `X₁` and the terms vanish (`evDecBg_eq_zero_of_not_subset`).

* `evDecBg_canon_local_eTerm`: the hypothesis `hloc` of the R8 field lemmas at `Gg = Gb` for the
  old terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset

section Local

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **(AE2) of Lemma 4.2 at `Gb` for the old terms**: under the hypotheses of
`evDecBg_canon_local_of` (the standing hypotheses of the pair `(Gb, H⁻)`, `H⁻` with
`Ω_k(H⁻) = Ω_k(Gb)` and without layer `k + 1`), for the old term with the step's settings
`BgSetting N Gp Gk Gj`, `FlSetting N Gp Gk H_s` (`H_s` the level-`k` set of the step) and its
functional `eTermFun Gb Gk Gj H⁻ … Fk E` recomputed on `Gb`, the terms of every label `Y` with
`LabelMargin Gb Y` agree at two data of the chart of `Gb` with `AgHatDir Y`. -/
theorem evDecBg_canon_local_eTerm (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (hHm : Hm.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1) (hdk : Hm.Ω k = Gb.Ω k)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L a₁) ν)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {ϱ₁ ϱ₂ ϱs : ℝ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs} {r₀ δ₃ δfl : ℝ}
    {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hs a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f) (hGs : IsLevel Hs k)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Zb : Finset (unitPts Gb)) :
    ∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir hG' Y u u' →
        evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol
            (eTermFun Gb Gk Gj Hm (compWeight L a₁) Fk E) Zb um tm Y
            (u.1, (BgTransport.canon Gp Gb N).res u.2) =
          evDecBg Gp X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol
            (eTermFun Gb Gk Gj Hm (compWeight L a₁) Fk E) Zb um tm Y
            (u'.1, (BgTransport.canon Gp Gb N).res u'.2) := by
  classical
  intro um tm hW Y hYm u hu u' hu' hAg
  by_cases hnear : ∀ x ∈ X₁f, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ (k + 1)) (3 * (L : ℝ) ^ (k + 1)) (y μ) (x μ)) →
        y ∈ Gb.layer (k + 1)
  · -- the frozen region and its neighbourhood lie in the top layer: the settings on `Gb`
    have htop : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1) := fun x hx =>
      (Gb.mem_layer.1 (hnear x hx x fun μ => CoordNear.refl (by positivity) _)).1
    have hdsX : ∀ x ∈ dataSites Gk, x ∈ X₁f := fun x hx => hB.dep x hx x (self_mem_composeDep x)
    have hdsTop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1) := fun x hx => htop x (hdsX x hx)
    have hB' := bgSetting_of_top hB hG' hC.Sp HBb hrb hdsTop
    have hF' := flSetting_of_top hF hGs hk hC hdk hHm hdsTop
    have hΩ1 : ∀ x ∈ X₁f, x ∈ Gb.Ω 1 := fun x hx =>
      Gb.Ω_antitone le_rfl (by omega) (by omega) (htop x hx)
    have hread : ∀ x ∈ dataSites Gk, ∀ w ∈ composeDep Gk Gb x, approxDep Gb w ⊆ X₁f := by
      intro x hx w hw
      have hxX := hdsX x hx
      have hxΩ := hΩ1 x hxX
      refine approxDep_composeDep_subset_X1_of hB' (n := k + 1) le_rfl hx hxΩ
        (Gb.layerIndex_eq (by omega) le_rfl (mem_layer_top (htop x hxX))) ?_ hw
      refine active_layer_of_near (by omega) le_rfl (hnear x hxX) fun μ => ?_
      refine (composeDep_coord_bound le_rfl hw (fun hxk => (Gk.layerIndex_spec hxk).2.1)
        (fun _ => (Gb.layerIndex_spec hxΩ).2.1) μ).mono ?_
      linarith
    exact evDecBg_canon_local_of hC hk hG' hHm hHmtop hrow cc hcψ hMX hdm hα hsm hcov hX₁ hF₁
      hSol _ (fun {_ _ _ _ _ _ _ _ _ _ _ _} _ hφd hδ hψ hdata hXY =>
        eTermFun_eq_of_component_of hB' hF' (fun x hx => hΩ1 x hx) hread Fk E hφd hδ hψ hdata
          hXY) Zb um tm hW Y hYm u hu u' hu' hAg
  · -- otherwise no label with the margin contains the frozen region
    have hnot : ¬ ∀ x ∈ X₁f, x ∈ Y := fun hXY => hnear fun x hx y hy =>
      layer_near_of_labelMargin hC.Sp hYm (Y := {x}) (by simpa using hXY x hx) x
        (Finset.mem_singleton_self x) y hy
    rw [evDecBg_eq_zero_of_not_subset _ hX₁ hnot, evDecBg_eq_zero_of_not_subset _ hX₁ hnot]

end Local

end Balaban.Localization
