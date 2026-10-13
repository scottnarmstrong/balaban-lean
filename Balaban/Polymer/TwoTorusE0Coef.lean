/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDirectTermsTower
public import Balaban.Inhabited.DetOutputTermsWitnessG

/-!
# The energy coefficient `E0` of one zero-class step on two tori, from the tower

The localized energy of one step is `ℰ₀(z) = -½ ∑_{y ∈ B(z)} tr 𝕃(y, y) + ℰ₁(z)`
(`StepSetting.E0locC`), and its coefficient family at the tower (`e0CoeffFamily_value_fromTowerG`)
is `e0 θ T = dz θ T + c θ T`, where

* `dz θ T` is the term `E.term D T` of the localized determinant record at the datum `D` of the
  chart with `rawOf D = θ.1` (`detParamFamily`); for the record of the tower
  (`detExpansionLocC_scale_of_towerG`) this term is the sum over the unit points `y` of the block
  `B(z)` of the rooted determinant activities `detActivityBg 1 (compWeight L 1) 1 ν ρ₄ D y T`;
* `c θ T` is the energy coefficient of the marks, `gsumCoeff μ (labels) (activity) (anchors)
  (marks) T`, with the labels `thickLabels I.𝒴 I.dom` of the direct terms, the activity
  `zeroSourceAct (labelActFamilyOn … I hF) 2` (at zero source the potential part, built from the
  marked energy terms `evDec … ∅ 1 0`) and the bridge marks `e1MarkGParamG`.

The second summand is compared on two tori by `gsumCoeff_e1_twoTorus_fromTowerG`; the first by
`sum_blockU_detActivityBg_twoTorus`.  This file supplies the tower inputs of the latter and adds the
two comparisons.

## Main statements

* `detTerm_twoTorus_fromTowerG`: for the general tower `T`, the determinant term of the root
  block `B(bc z)` at `cubeMap '' T` on the second torus equals that of `B(z)` at `T` on the first,
  for data of the two charts whose raw data agree on the box and sets `T` of cubes of the box.
* `detExpansionLocC_term_twoTorus_fromTowerG`: the same for any two records `DetExpansionLocC` whose
  terms are the explicit sums of `detExpansionLocC_scale_of_towerG`.
* `e0Coeff_twoTorus_fromTowerG`: at `T.m₀ = 1`, the energy coefficient `E0` (determinant term plus
  energy coefficient of the marks, with the labels and activities of the tower witnesses) agrees on
  two tori, for labels and blocks of a common box.

Only roots, labels and blocks of a common box are compared; labels that wind around a torus are not
covered.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale Balaban.Inhabited
  Balaban.Inhabited.LevelStep MeasureTheory

section Det

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "SB" => StepTowerG.step T k hk N₁' ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := T.m₁)
  (K := k + 1) (m₀ := 1) hN hN' (le_refl (k + 1))

/-- **The determinant term of the root block on two tori, from the tower.**  For the general tower
`T`, the steps `T.step k hk N₁ ν β p₁` and `T.step k hk N₁' ν β p₁` on two tori, data `D₀`, `D₀'` of
the charts `Ξ^c(𝔹_{k+1}; 1, t)` whose raw data agree on the box of radius `R + 3 L^(k+1)`, a coarse
root `z` (`|z| ≤ r_c`, `L^(k+1) (r_c + 1) ≤ R`) whose root cell lies in the box of radius `R`, and a
set `T` of level-`(k+1)` cubes of that box: the term of the determinant record of the tower
(`detExpansionLocC_scale_of_towerG`), `∑_{y ∈ B(z)} detActivityBg D y T`, takes the same value at
`(bc z, D₀', cubeMap '' T)` on the second torus as at `(z, D₀, T)` on the first.  This is
`sum_blockU_detActivityBg_twoTorus` with the core of the tower transferred to the level pair of the
scale (`flCore_stepG`) and the margins from `4 R + 19 L^(k+3+m₁) + 5 < N₁ L^m₁ L^(k+1),
N₁′ L^m₁ L^(k+1)` (`twoTorus_margins_of_lt_min`). -/
theorem detTerm_twoTorus_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁] [NeZero N₁']
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (h5 : 5 < N₁) (h5' : 5 < N₁')
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    {D₀ : BgData (GA) N} {D₀' : BgData (GB) N}
    (hD₀ : XiCData (GA) (compWeight L 1) ν (k + 1) 1 T.t D₀)
    (hD₀' : XiCData (GB) (compWeight L 1) ν (k + 1) 1 T.t D₀')
    (z : TA) {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (rawOf D₀) (rawOf D₀'))
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x) :
    ∑ y ∈ (SB).blockU (bc z),
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D₀' y (Tb.image (σc)) =
      ∑ y ∈ (SA).blockU z,
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D₀ y Tb := by
  have hm₁ : 1 ≤ T.m₁ := by have := T.m₁_four; omega
  obtain ⟨⟨hn1, hnS, -, hnH, -⟩, ⟨hn1', hnS', -, hnH', -⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := T.m₁) hm₁ (lt_min hn hn')
  have hC := flCore_stepG (N := N) T.hd T.hL T.m₁_four (Classical.choice T.core) hk h5 hν0 hν
  have hC' := flCore_stepG (N := N) (N₁ := N₁') T.hd T.hL T.m₁_four (Classical.choice T.core) hk
    h5' hν0 hν
  have hδc : 0 ≤ T.δc := δc_nonneg_of_flCore T.hd T.t_pos hC T.dom_margin
  have hYr : ∀ x ∈ sitesOf Tb, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
    exact hTb b hb x hxb
  exact sum_blockU_detActivityBg_twoTorus hN hN' hC hC' hk hδc T.large_block T.δc_small
    T.dom_margin T.coer_margin (hatConn_lvTopG T.hL) (hatConn_lvTopG T.hL) hD₀ hD₀' z hz hrc
    hroot Tb hYr hn1 hn1' hnS hnS' hnH hnH' hraw


/-- **The term of the localized determinant record on two tori, from the tower.**  For any two
records `E`, `E'` of the localized determinant expansion (`DetExpansionLocC`) of the two steps at
the roots `z` and `bc z` whose terms are the sums of the rooted activities over the unit points of
the root block (the form exported by `detExpansionLocC_scale_of_towerG`), the term of `E'` at
`(D₀', cubeMap '' T)` equals the term of `E` at `(D₀, T)`, under the hypotheses of
`detTerm_twoTorus_fromTowerG`. -/
theorem detExpansionLocC_term_twoTorus_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁] [NeZero N₁']
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (h5 : 5 < N₁) (h5' : 5 < N₁')
    {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    {D₀ : BgData (GA) N} {D₀' : BgData (GB) N}
    (hD₀ : XiCData (GA) (compWeight L 1) ν (k + 1) 1 T.t D₀)
    (hD₀' : XiCData (GB) (compWeight L 1) ν (k + 1) 1 T.t D₀')
    (z : TA) {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (rawOf D₀) (rawOf D₀'))
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    {eps κ'' cdet : ℝ} (E : DetExpansionLocC (SA) 1 z eps κ'' cdet)
    (E' : DetExpansionLocC (SB) 1 (bc z) eps κ'' cdet)
    (hE : ∀ D Y, E.term D Y = ∑ y ∈ (SA).blockU z,
      detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y Y)
    (hE' : ∀ D Y, E'.term D Y = ∑ y ∈ (SB).blockU (bc z),
      detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y Y) :
    E'.term D₀' (Tb.image (σc)) = E.term D₀ Tb :=
  (hE' D₀' _).trans ((detTerm_twoTorus_fromTowerG T hk hN hN' h5 h5' hν0 hν β p₁ hD₀ hD₀' z hz hrc
    hroot hn hn' hraw Tb hTb).trans (hE D₀ Tb).symm)

end Det

section E0

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "SB" => StepTowerG.step T k hk N₁' ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := T.m₁)
  (K := k + 1) (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "ΛB" => RawData d L (N₁' * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => (((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ))
set_option hygiene false in
local notation "FB" => (((SB).U × Fin N → ℂ) × ((SB).U × Fin N → ℂ))

/-- **D1: the energy coefficient `E0` of the zero class on two tori, from the tower.**  For the
tower `T` with block scale `T.m₀ = 1` and its steps `SA = T.step k hk N₁ ν β p₁`,
`SB = T.step k hk N₁' ν β p₁` on two tori, with the hypotheses of `gsumCoeff_e1_twoTorus_fromTowerG`
(in which the parameters `θ`, `θ'` are the raw data of data `D₀`, `D₀'` of the charts, and the root
`z` satisfies `L^(k+1) (r_c + 1) ≤ R`): there are the expanded functions, domains and terms of the
direct terms of the zero class on both tori, such that for EVERY pair of `DirectTerms` instances
`I`, `I'` with these domains and terms and relative families `hF`, `hF'`, the energy coefficients
`E0` agree:
`∑_{y ∈ B(bc z)} detActivityBg D₀' y (cubeMap '' T) + c′ θ′ (cubeMap '' T)
  = ∑_{y ∈ B(z)} detActivityBg D₀ y T + c θ T`.
The first summand is the determinant term of the record of the tower
(`detExpansionLocC_scale_of_towerG`, the value of `dz` in `e0CoeffFamily_value_fromTowerG` at the
chart datum with raw datum `θ.1`), compared by `detTerm_twoTorus_fromTowerG`; the second is the
energy coefficient of the marks, compared by `gsumCoeff_e1_twoTorus_fromTowerG`.  Only labels and
blocks of a common box are compared. -/
theorem e0Coeff_twoTorus_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁]
    [NeZero N₁'] (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (h5 : 5 < N₁) (h5' : 5 < N₁')
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β ρs : ℝ) (hρs : 0 < ρs)
    (hβρ : max 1 ρs ≤ β) (p₁ q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρs)
    (D : StepScaleDataG T k hk N₁ ν β p₁) (D' : StepScaleDataG T k hk N₁' ν β p₁)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (z : TA) {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    {D₀ : BgData (GA) N} {D₀' : BgData (GB) N}
    (hD₀ : XiCData (GA) (compWeight L 1) ν (k + 1) 1 T.t D₀)
    (hD₀' : XiCData (GB) (compWeight L 1) ν (k + 1) 1 T.t D₀')
    (hθD : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D₀)
    (hθD' : (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) = rawOf D₀')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 →
      ‖u‖ * markedRad d L N k 1 T.κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t)
    (hGdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol ρ hp z T.t θ i u))
    (hL2 : 2 ≤ L) (hdom : ∀ b, ∀ Y ∈ e1DomG (SA) b, IsDj 1 (k + 1) Y)
    (hdom' : ∀ b, ∀ Y ∈ e1DomG (SB) b, IsDj 1 (k + 1) Y)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hrad : markedRad d L N k 1 T.κ cψ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t)
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x) :
    ∃ (val : FA → FA → ℂ → ΛA → ℂ) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → ℂ → ΛA → ℂ)
      (val' : FB → FB → ℂ → ΛB → ℂ) (𝒴' : Finset (Set (CTorus d L N₁' T.m₁ (k + 1))))
      (Tt' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → ℂ → ΛB → ℂ),
      (∀ Θ ∈ physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β),
        ∃ I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
            ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SA).β))
            (2 * T.κdec - 1) Θ (physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β))
            (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
            (physAgΘ (SA)) (AgFDirPair (SA)),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (∀ Θ ∈ physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β),
        ∃ I' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) p₁ 2
            ((SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SB).β))
            (2 * T.κdec - 1) Θ (physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β))
            (physXW (SB) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
            (physAgΘ (SB)) (AgFDirPair (SB)),
          I'.𝒴 = 𝒴' ∧ I'.T = Tt') ∧
      ∀ {ρI Rσ εU a κ0 KcL : ℝ} {Θ₀ : ΛA} {Θ₀' : ΛB} {SΛ : Set ΛA} {SΛ' : Set ΛB}
        {XW : Set (FA × FA)} {XW' : Set (FB × FB)} {valI : FA → FA → ℂ → ΛA → ℂ}
        {valI' : FB → FB → ℂ → ΛB → ℂ} {AgΘ : Set (CTorus d L N₁ T.m₁ (k + 1)) → ΛA → ΛA → Prop}
        {AgΘ' : Set (CTorus d L N₁' T.m₁ (k + 1)) → ΛB → ΛB → Prop}
        {AgF : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → Prop}
        {AgF' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → Prop}
        (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀ SΛ XW valI AgΘ AgF)
        (I' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀' SΛ' XW' valI' AgΘ' AgF'),
        I.𝒴 = 𝒴 → I.T = Tt → I'.𝒴 = 𝒴' → I'.T = Tt' →
        ∀ {cJ cJ' : ℂ} {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
          (hF : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I V)
          (hF' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' V')
          (hρI : 0 < ρI) (hRσ : 1 < Rσ) (hεU : 0 ≤ εU) (hκ0 : aEnt d L + 2 ≤ κ0)
          (hKc : K0 d L κ0 ≤ KcL),
          ((θ.1, 0) : physParam N (SA)) ∈ V → ((θ'.1, 0) : physParam N (SB)) ∈ V' →
          2 * ρI ≤ cψ →
        ∑ y ∈ (SB).blockU (bc z),
            detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D₀' y (Tb.image (σc)) +
          gsumCoeff ((SB).blockSplit 1 hp').μ
            (commonLabels (thickLabels I'.𝒴 I'.dom) hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
            (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
                hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
              hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom'
              (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
            (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB)) (bc z) i')
            (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc z) T.t θ' i' u Φ') (Tb.image (σc)) =
          ∑ y ∈ (SA).blockU z,
            detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D₀ y Tb +
          gsumCoeff ((SA).blockSplit 1 hp).μ
            (commonLabels (thickLabels I.𝒴 I.dom) hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
            (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
                hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
              hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom
              (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
            (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
            (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z T.t θ i u Φ) Tb := by
  have hθ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) ν (k + 1) 1 T.t := ⟨D₀, hD₀, hθD⟩
  have hθ' : (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) ν (k + 1) 1 T.t := ⟨D₀', hD₀', hθD'⟩
  obtain ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', hE⟩ :=
    gsumCoeff_e1_twoTorus_fromTowerG T hm₀ hk hN hN' h5 h5' ν hνpos hν β ρs hρs hβρ p₁ q hq0 hq
      D D' hF₁ hF₁' hSol hSol' z hz (le_trans (Nat.le_add_right _ _) hrc) hroot hn hn' θ θ' hθ
      hθ' hraw hρ hp hp' hum hGdep hL2 hdom hdom' hcψ hrad Tb hTb
  refine ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', ?_⟩
  intro ρI Rσ εU a κ0 KcL Θ₀ Θ₀' SΛ SΛ' XW XW' valI valI' AgΘ AgΘ' AgF AgF' I I' h1 h2 h1' h2'
    cJ cJ' V V' hF hF' hρI hRσ hεU hκ0 hKc hV hV' hρc
  have hraw₀ : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (rawOf D₀) (rawOf D₀') := by
    rw [← hθD, ← hθD']; exact hraw
  rw [detTerm_twoTorus_fromTowerG T hk hN hN' h5 h5' hνpos.le hν β p₁ hD₀ hD₀' z hz hrc hroot hn
      hn' hraw₀ Tb hTb,
    hE I I' h1 h2 h1' h2' hF hF' hρI hRσ hεU hκ0 hKc hV hV' hρc]

end E0

end Balaban.Polymer.TwoTorusStep
