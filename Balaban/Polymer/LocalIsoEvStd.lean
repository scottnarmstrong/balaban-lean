/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoEvPrem
public import Balaban.Inhabited.StepTowerThetaDetG
import Mathlib.Tactic.Linarith

/-!
# The recomputed terms on two tori from the standing hypotheses of the local pairs

`OmegaIso.evDecBg_canon_twoTorus_core` with its premises discharged on each torus: the standing
hypotheses of the local pair `(Gb, H⁻)` (`FlCore`, the cover base and the specifications of the
decoupled background), the defining properties of the decoupling pair `(F₁, Sol)` (and, on the first
torus, their analyticity), a datum of the chart, a bounded hat variable and marks of the radius set.
The functional `Φ` is asked to be analytic on the realizable triples of a frozen region `X₁g ⊆ X₁f`
in the top layer of `Gb`, and `Φ'`, `Φ` to agree on corresponding realizable triples.

* `pairTriple_mem_flRealLC`: at a parameter of the polydisc equal to `1` off the parameter cubes of
  `X₁g`, the point triple of the masked hat field is realizable (`point_facts_core_cover`,
  `markedHatPsiFBg_liftZ_mem_flBallLC_core`);
* `OmegaIso.evDecBg_canon_twoTorus`: the recomputed terms of `bm '' Y` on the second torus and of
  `Y` on the first agree.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Analysis Matrix

/-- **The raw chart grows with the radius** (`xiCData_mono_radius` on the raw data). -/
theorem xiCRaw_mono_radius {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} {ε ε' : ℝ}
    (hle : ε ≤ ε') {p : RawData d L (N₁ * L ^ m₁) K N} (hp : p ∈ XiCRaw G a ν n 1 ε) :
    p ∈ XiCRaw G a ν n 1 ε' := by
  obtain ⟨D, hD, rfl⟩ := hp
  exact ⟨D, Balaban.Inhabited.xiCData_mono_radius zero_le_one hle hD, rfl⟩

section Real

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **The point triple of the masked hat field is realizable** (one torus): at a parameter of
modulus `< e^κ` equal to `1` off the parameter cubes of `X₁g`, the triple
`(F₁(σ, Θ), δφ(σ), (Θ, ψ'))` of a datum of the chart and the masked local hat field `ψ'` lies in the
realizable triples with layer-constant fluctuation. -/
theorem pairTriple_mem_flRealLC {a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁) (hk : 1 ≤ k) (hHm : Hm.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
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
    {X₁g : Finset (CTorus d L N₁ m₁ (k + 1))} {σ : DecParams Gb}
    (hσ : ∀ P, ‖σ P‖ < Real.exp κ)
    (hσ1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gb).cubeIdx),
      P ∉ (coverOf Gb).parCubes X₁g → σ ⟨P, hP⟩ = 1)
    {D : BgData Gb N} (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (Zm : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁) :
    (F₁ (σ, rawOf D),
      (Sol (σ, flEdat Gb Hm (F₁ (σ, rawOf D)) D.Ψ
        (markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm σ (rawOf D) (resZ Gp Gb ψh)))).1,
      (rawOf D, markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm σ (rawOf D) (resZ Gp Gb ψh))) ∈
      FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁ := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδ0 : 0 < xiC1 d * eps := by
    have := one_le_xiC1 d; have := hC.eps_pos; positivity
  have hF₁o : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α) := fun s D hs hD' φ α hI =>
    hF₁ s D hs hD' φ α ((dec2_isDecBg_iff Gb _ _ _ s D φ α).2 hI)
  have hψ := markedHatPsiFBg_liftZ_mem_flBallLC_core hC hk hHm cc hcψ hMX hmar hα hsm hF₁o hσ hD
    (ψh := resZ Gp Gb ψh) (fun q => by
      rw [resZ_apply]
      split_ifs
      · exact hψh _
      · rw [norm_zero]; exact hcψ) Zm hW
  obtain ⟨φ, α, δφ, δα, -, hFe, -, hSe, hmem⟩ := point_facts_core_cover hS Sb hC.HBp hC.hκ hC.hM
    hC.eps_pos hC.small1 hC.c7le hC.phi_lt hC.δ₁_pos hC.hPmp hF₁ hSol hσ hσ1 hD hψ.1
  have hFe' : F₁ (σ, rawOf D) = (φ, α) := hFe
  refine ⟨?_, hψ.2⟩
  rw [hFe', hSe]
  exact hmem

end Real

section Std

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱb ϱb' ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

namespace OmegaIso

variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The recomputed terms on two tori from the standing hypotheses of the local pairs.**  Let `Gb`,
`Hm` be carried onto `Gb'`, `Hm'` by the box map; on each torus let the local pair have the standing
hypotheses (`FlCore`, the cover base `Sb`, `Sb'` and the specifications `hS` of the decoupled
background, `Hm.Ω (k + 1) = ∅`) and the decoupling pair its defining properties (`hF₁`, `hSol`;
`hF₁'`, `hSol'`; on the first torus also its analyticity `hF₁an`, `hSolan`).  Let `X₁g ⊆ X₁f` be a
region in the top layer of `Gb`, `Φ` analytic on the realizable triples of `X₁g` and `Φ'`, `Φ` agree
on corresponding realizable triples (`hΦ`).  For data `D`, `D'` of the charts corresponding on the
box of radius `ρ + 1`, hat variables of size `≤ c_ψ` corresponding on the box of radius `ρ`, the
mask `Zm` and its image and marks of the radius set (`hW`), the terms `evDecBg` of `bm '' Y` on the
second torus and of `Y` on the first agree. -/
theorem evDecBg_canon_twoTorus (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ} (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L a₁) ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gb') × Edat Hm' N → (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
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
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gb') × Edat Hm' N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hm' (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))} {X₁f X₁g : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    (hX₁g : ∀ x ∈ X₁g, x ∈ X₁f) (hX₁gtop : ∀ x ∈ X₁g, x ∈ Gb.Ω (k + 1))
    {R : ℕ} (hρR : ρ ≤ R) (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁))
    (hΦ : ∀ t ∈ FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gb' Hm' a₁ ν BG κ eps (X₁g.image bk) BG₂ δ₁,
      (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    (Zm : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {D : BgData Gb N} {D' : BgData Gb' N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gb' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bk x), i) = ψh (unitPt hGA x, i)) :
    evDecBg (GB) (X₁f.image bk) m₀ j 𝒦X' Gb' a₁ ν (BgTransport.canon (GB) Gb' N) cc F₁' Sol' Φ'
        (Zm.map hI.unitEquiv.toEmbedding) um tm (bk '' Y)
        (rawOf D', (BgTransport.canon (GB) Gb' N).res ψh') =
      evDecBg (GA) X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon (GA) Gb N) cc F₁ Sol Φ Zm um tm Y
        (rawOf D, (BgTransport.canon (GA) Gb N).res ψh) := by
  classical
  -- the image region lies in the top layer of the second set
  have hX₁gtop' : ∀ x ∈ X₁g.image bk, x ∈ Gb'.Ω (k + 1) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    have hy1 : y ∈ Gb.Ω 1 := Gb.Ω_antitone le_rfl (by omega) (by omega) (hX₁gtop y hy)
    exact (hI.corr y (hI.inBox_succ hy1) (k + 1) (by omega) le_rfl).2 (hX₁gtop y hy)
  have hX₁g' : ∀ x ∈ X₁g.image bk, x ∈ (↑(X₁f.image bk) : Set (CTorus d L N₁' m₁ (k + 1))) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (hX₁g y hy))
  -- the premises of the pairs on the two tori
  have P1 := evDecBg_pairPremises hC hk hHm hS Sb cc hcψ hMX hmar hα hsm hF₁ hSol hD hψh Zm hW
  have P2 := evDecBg_pairPremises hC' hk hHm' hS Sb' cc hcψ hMX hmar hα hsm hF₁' hSol' hD' hψh'
    (Zm.map hI.unitEquiv.toEmbedding) hW
  have hFan := evDecBg_fanAnalytic hk hGA ha₁ ha₂ hS Sb hC.HBp hC.hκ hC.hM hMX' hCx hC.eps_pos
    hC.small1 hC.c7le hC.phi_lt hmar hα hsm cc hcψ hC.δ₁_pos hC.hPmp hHm hF₁an hF₁ hSolan hSol
    (fun x hx => Finset.mem_coe.2 (hX₁g x hx)) hX₁gtop hΦan Zm hW hD hψh
  refine hI.evDecBg_canon_twoTorus_core hH hGA hGB a₁ ν (rho4 d L N BG κ) cc hC.hκ hcov hX₁ hcov'
    hX₁' hρR hX₁R hYR hnS hnS' hnF hnF' Zm um tm hΨ hh hhat hFan
    (Sg := {σ | (∀ P, ‖σ P‖ < Real.exp κ) ∧
      ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gb).cubeIdx),
        P ∉ (coverOf Gb).parCubes X₁g → σ ⟨P, hP⟩ = 1})
    (Sg' := {σ | (∀ P, ‖σ P‖ < Real.exp κ) ∧
      ∀ (P : ℕ × CTorus d L N₁' m₁ (k + 1)) (hP : P ∈ (coverOf Gb').cubeIdx),
        P ∉ (coverOf Gb').parCubes (X₁g.image bk) → σ ⟨P, hP⟩ = 1})
    (fun w hw => ⟨tauExt_norm_lt (Gl := Gb) _ hC.hκ w hw,
      tauExt_eq_one (Gl := Gb) hGA (fun x hx => Finset.mem_coe.2 (hX₁g x hx)) hX₁gtop w⟩)
    (fun w hw => ⟨tauExt_norm_lt (Gl := Gb') _ hC.hκ w hw,
      tauExt_eq_one (Gl := Gb') hGB hX₁g' hX₁gtop' w⟩)
    (fun σ hσ => P1.1 σ hσ.1) (fun σ hσ => P2.1 σ hσ.1) (fun σ hσ => P1.2.1 σ hσ.1)
    (r := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (Rl := FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁)
    (Rl' := FlRealLC Gb' Hm' a₁ ν BG κ eps (X₁g.image bk) BG₂ δ₁)
    (fun σ hσ => ⟨(P1.2.2 σ hσ.1).1, (P1.2.2 σ hσ.1).2.1, (P1.2.2 σ hσ.1).2.2.1,
      pairTriple_mem_flRealLC hC hk hHm hS Sb cc hcψ hMX hmar hα hsm hF₁ hSol hσ.1 hσ.2 hD hψh Zm
        hW⟩)
    (fun σ hσ => ⟨(P2.2.2 σ hσ.1).1, (P2.2.2 σ hσ.1).2.2.2,
      pairTriple_mem_flRealLC hC' hk hHm' hS Sb' cc hcψ hMX hmar hα hsm hF₁' hSol' hσ.1 hσ.2 hD'
        hψh' _ hW⟩)
    (fun t t' ht ht' => hΦ t ht t' ht')

end OmegaIso

end Std

end Balaban.Polymer.LocalIso
