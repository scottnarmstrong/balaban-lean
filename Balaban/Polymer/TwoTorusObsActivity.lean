/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsAssembly
public import Balaban.Polymer.TwoTorusDirectTerms

/-!
# The activities of the observable on two tori at the zero source

The activities of the observable coefficient are the scalar tilt `tiltActObs A …` of the extension
by zero of `physAct A e t = (A (e.1, 0) 1 - A (e.1, 0) t) ⊕ A e t` to the observable labels.  At
a parameter of zero source, `e = (e.1, 0)`, they read only the activity family `A` at the zero
source, whose values are explicit (the appended conjunct of `obsTiltLabels_local_fromTowerG`): the
labels correspond to the domains of the potential and the source parts, and the activity of a
label at `(e.1, 0)` is the potential part
`-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evDec_z(Y)) ω ψ̂ σ e.1` at its domain `Y`.

## Main statements

* `rayTerm_evTerm_eq_evDec`: the potential part in the form of the export (terms `evTerm …`) is
  the potential part with the marked terms `evDec … ∅ 1 0` (`FFmarked_one_zero`).
* `labelActZero_twoTorus`: the explicit activities of corresponding labels of the box agree at
  corresponding parameters of zero source (`vpartTerm_twoTorus`).
* `labelMap_twoTorus`: the correspondence `Y ↦ bm '' Y` of the labels of the box.
* `tiltActObs_twoTorus`: the hypotheses of `obsCoeffParam_twoTorus_of_activities` on the
  activities `tiltActObs A …`, at parameters of zero source.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric

section Activity

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : (SB).U)
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ y) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ (bm y)) : Set (CTorus d L N₁' m₁ (k + 1)))
set_option hygiene false in
local notation "𝒴A" => polyDom (GA) (LocalCover.nbhdF m₀ y) m₀ k (LocalCover.fam m₀ y)
set_option hygiene false in
local notation "𝒴B" => polyDom (GB) (LocalCover.nbhdF m₀ (bm y)) m₀ k (LocalCover.fam m₀ (bm y))


set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

omit [NeZero N₁'] in
/-- **The potential part with the marked terms.**  The potential part of the direct terms at a
domain `Y`, written with the terms `evTerm … (blockEnergyFun …)` of the blocks (the form of the
export of `obsTiltLabels_local_fromTowerG`), is the potential part written with the marked terms
`evDec … ∅ 1 0` (the form of `vpartTerm_twoTorus`). -/
theorem rayTerm_evTerm_eq_evDec {a₁ ν : ℝ} {m₀ : ℕ} (hGA : IsLevel (GA) (k + 1)) (cc : ℂ)
    (F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ))
    (Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (w x : unitPts (GA) × Fin N → ℂ) (σ : ℂ)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    (∑ z : TA, if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
      rayTerm (dl3 (evTerm
        (fun i : ParIdx (GA) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
          Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (GA) m₀ (X1 (GA) m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)))
        (fun u s => blockEnergyFun (GA) (HA) (compWeight L a₁) ν k z
          (F₂ z (extParams (GA) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
            Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          (Sol₂ z (extParams (GA) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
              Set (CTorus d L N₁ m₁ (k + 1))) s,
            flEdat (GA) (HA) (F₂ z (extParams (GA) (↑(LocalCover.nbhdF m₀
              (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc (F₂ z)
                (extParams (GA) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
                  Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc (F₂ z)
            (extParams (GA) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
              Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) Y) w) taylorWeight x σ Θ
      else 0) =
    ∑ z : TA, if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
      rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k z)) a₁ ν hGA cc (F₂ z) (Sol₂ z)
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k z) ∅ 1 0 Y) w) taylorWeight x σ Θ
      else 0 := by
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hY : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
      (LocalCover.fam m₀ (LocalCover.blockSite k z))
  · rw [ite_eq_left hY, ite_eq_left hY]
    exact congrArg (fun FF => rayTerm (dl3 (evTerm
      (fun i : ParIdx (GA) (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) :
        Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (GA) m₀
      (X1 (GA) m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z))) FF Y) w)
        taylorWeight x σ Θ)
      (FFmarked_one_zero (a₁ := a₁) (ν := ν)
        (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) hGA cc (F₂ z) (Sol₂ z)
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k z) ∅).symm
  · rw [ite_eq_right hY, ite_eq_right hY]

/-- **D3 (e): the explicit activities of corresponding labels on two tori.**  Let the activity
families `A`, `A'` of the two steps have the explicit values at the zero source (`hAx`, `hAx'`: the
potential part `-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evDec_z(Y)) ω ψ̂ σ e.1` at the domain `Y` of the
label, at the clamped hat field `ψ̂`), for decoupled pairs `(F₂, Sol₂)`, `(F₂', Sol₂')` per block.
For a label `l` of the box and a label `l'` with domain `bm '' Y`, parameters `θ`, `θ'` (raw data in
the charts, agreeing on the box), `‖σ‖ ≤ 1` and block variables agreeing at corresponding unit points
of the box, the activities of `l'` at `(θ'.1, 0)` and of `l` at `(θ.1, 0)` agree
(`vpartTerm_twoTorus`).  The radius: `2 p₁ ≤ c_ψ` and `markedRad … c_ψ cc < δ₁`. -/
theorem labelActZero_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ R : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρ : 2 * p₁ ≤ cψ)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₂' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    {Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol₂' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Small (HA) (Sol₂ b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₂ b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₂ b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ b p).2))
    (hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small (HB) (Sol₂' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₂' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₂' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N (SA) → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N (SB) → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
    (hAx : ∀ e ∈ V, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb) (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b),
      (A ((e.1, 0) : physParam N (SA)) σ).H l Φ = -(β : ℂ) *
        ∑ z : TA, if Lab.ysite l ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
            m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SA).hG' cc (F₂ z) (Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) νS k z) ∅ 1 0 (Lab.ysite l))
            ((SA).hatOf m₀ p₁ hp Φ)) taylorWeight ((SA).hatOf m₀ p₁ hp Φ) σ
            (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        else 0)
    (hAx' : ∀ e ∈ V', ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb') (Φ : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ = -(β : ℂ) *
        ∑ z : TB, if Lab'.ysite l ∈ polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
            m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SB).hG' cc (F₂' z) (Sol₂' z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) νS k z) ∅ 1 0 (Lab'.ysite l))
            ((SB).hatOf m₀ p₁ hp' Φ)) taylorWeight ((SB).hatOf m₀ p₁ hp' Φ) σ
            (e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
        else 0)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθV : θ ∈ V) (hθV' : θ' ∈ V')
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (l : Lb) (l' : Lb')
    (hlR : ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hl' : Lab'.ysite l' = bm '' Lab.ysite l)
    (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) :
    (A' ((θ'.1, 0) : physParam N (SB)) σ).H l' Φ' = (A ((θ.1, 0) : physParam N (SA)) σ).H l Φ := by
  have hσ2 : ‖σ‖ < 2 := by linarith
  have hp1 : (0 : ℝ) < p₁ := hp
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  rw [hAx' θ' hθV' σ hσ2 l' Φ', hAx θ hθV σ hσ2 l Φ, hl', hDe, hDe']
  congr 1
  have hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → ∀ i,
      (SB).hatOf m₀ p₁ hp' Φ' (unitPt (SB).hG' (bm x), i) =
        (SA).hatOf m₀ p₁ hp Φ (unitPt (SA).hG' x, i) :=
    hatOf_boxMap (SA).hG' (SB).hG' hN2 hk νS β p₁ δ m₀ p₁ hp hp' Φ Φ' hΦ
  exact vpartTerm_twoTorus hC hC' hk (SA).hG' (SB).hG' cc hcψ hMX hmar hαK hsm hF₂ hF₂' hSol₂
    hSol₂' hm₀ hN hN' hlR hn hn' hnS hnS' hnF hnF' hD hD' (by rw [← hDe, ← hDe']; exact hraw)
    (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p) (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p)
    (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) hρ
    hhat hhat hrad taylorWeight hσ

/-- **The labels of the box on two tori.**  For label systems whose labels correspond (`ys`, `ys'`)
to domain families with `bm '' Y ∈ 𝒴′ ↔ Y ∈ 𝒴` for the sets `Y` of the box, and a set `T` of
cubes of the box: the labels with blocks in `T` lie in the box, and `l ↦ l′` with
`ysite l′ = bm '' ysite l` is a bijection onto the labels of the second system with blocks in
`cubeMap '' T`.  Margins: `2 R + L a_K < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem labelMap_twoTorus {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Lb Lb' : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ 𝒴' ↔ Y ∈ 𝒴)) :
    ∃ lm : ∀ l : Lb, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T → Lb',
      (∀ l (_ : blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T),
        ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) ∧
      (∀ l hl, Lab'.ysite (lm l hl) = bm '' Lab.ysite l) ∧
      (∀ l₁ hl₁ l₂ hl₂, lm l₁ hl₁ = lm l₂ hl₂ → l₁ = l₂) ∧
      (∀ l', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite l') ⊆ T.image (σc) →
        ∃ l hl, lm l hl = l') := by
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hR : ∀ l, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T →
      ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun l hl => inBox_of_blocksOf_subset hN hT (Lab.isDj l) hl
  have hR' : ∀ l, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T →
      ∀ x ∈ (ys l).1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun l hl => by rw [← hys]; exact hR l hl
  have hm : ∀ l (hl : blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T), bm '' (ys l).1 ∈ 𝒴' :=
    fun l hl => (hmem _ (hR' l hl)).2 (ys l).2
  refine ⟨fun l hl => ys'.symm ⟨bm '' (ys l).1, hm l hl⟩, hR, fun l hl => ?_,
    fun l₁ hl₁ l₂ hl₂ h => ?_, fun l' hl' => ?_⟩
  · rw [hys', Equiv.apply_symm_apply, hys]
  · have h1 : bm '' (ys l₁).1 = bm '' (ys l₂).1 := by
      have := congrArg (fun l' => (ys' l').1) h
      simpa only [Equiv.apply_symm_apply] using this
    exact ys.injective (Subtype.ext (image_boxMap_inj (N₁' := N₁') hm' (hR' l₁ hl₁)
      (hR' l₂ hl₂) h1))
  · rw [hys'] at hl'
    have hDj : IsDj m₀ (k + 1) (ys' l').1 := hys' l' ▸ Lab'.isDj l'
    obtain ⟨-, hZR, hZimg, hZT⟩ := preimage_of_blocksOf_subset_image hN hN' hnL hnL' hT hDj hl'
    have hZmem : bm' '' (ys' l').1 ∈ 𝒴 := (hmem _ hZR).1 (by rw [hZimg]; exact (ys' l').2)
    refine ⟨ys.symm ⟨_, hZmem⟩, by rw [hys, Equiv.apply_symm_apply]; exact hZT, ?_⟩
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    show bm '' (ys (ys.symm ⟨_, hZmem⟩)).1 = (ys' l').1
    rw [Equiv.apply_symm_apply]
    exact hZimg

/-- **D3 (f): the activities of the observable on two tori at the zero source.**  Let the labels
of the activity families `A`, `A'` correspond to domain families (`ys`, `ys'`) with
`bm '' Y ∈ 𝒴′ ↔ Y ∈ 𝒴` on the box, and let the activities of corresponding labels of the box
agree at the zero-source parameters `(θ.1, 0)`, `(θ'.1, 0)` (`hAeq`, for `‖σ‖ ≤ 1` and block
variables agreeing at corresponding unit points of the box; `labelActZero_twoTorus`).  For
parameters `θ`, `θ'` of zero source, the activities `tiltActObs A …` and `tiltActObs A' …` on the
observable labels satisfy the hypotheses of `obsCoeffParam_twoTorus_of_activities`: the active
labels are those of `Lab.sum Lab`; on the others the activities vanish; the active labels with
blocks in `T` correspond bijectively to those of the second step with blocks in `cubeMap '' T`,
with image blocks and equal activities. -/
theorem tiltActObs_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Lb Lb' : Type} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴v : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    {𝒴v' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴v}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴v'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ 𝒴v' ↔ Y ∈ 𝒴v))
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N (SA) → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N (SB) → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0' : aEnt d L + 1 ≤ κ0') (hεH : 0 ≤ εH) (hεH' : 0 ≤ εH')
    {Kobs Kobs' : ℝ} (hK : Kco + Kco + K0 d L κ0 + K0 d L κ0 ≤ Kobs)
    (hK' : Kco' + Kco' + K0 d L κ0' + K0 d L κ0' ≤ Kobs')
    (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθ0 : θ.2 = 0) (hθ0' : θ'.2 = 0)
    (hAeq : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      Lab'.ysite l' = bm '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' ((θ'.1, 0) : physParam N (SB)) σ).H l' Φ' = (A ((θ.1, 0) : physParam N (SA)) σ).H l Φ) :
    ∃ (P : ObsLb (Lb ⊕ Lb) m₀ 𝒴 → Prop) (P' : ObsLb (Lb' ⊕ Lb') m₀ 𝒴' → Prop)
      (ψ : ∀ l, P l → blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite l) ⊆ T →
        ObsLb (Lb' ⊕ Lb') m₀ 𝒴'),
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l, ¬ P l → ∀ Φ,
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H l Φ = 0) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l', ¬ P' l' → ∀ Φ',
        (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H l' Φ' = 0) ∧
      (∀ l hP hl, P' (ψ l hP hl)) ∧
      (∀ l hP hl, blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab'.sum Lab') hdj').ysite (ψ l hP hl)) =
        (blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite l)).image (σc)) ∧
      (∀ l₁ hP₁ hl₁ l₂ hP₂ hl₂, ψ l₁ hP₁ hl₁ = ψ l₂ hP₂ hl₂ → l₁ = l₂) ∧
      (∀ l', P' l' → blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab'.sum Lab') hdj').ysite l') ⊆
        T.image (σc) → ∃ l hP hl, ψ l hP hl = l') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l hP hl, ∀ Φ Φ',
        (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
            Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H (ψ l hP hl) Φ' =
          (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H l Φ) := by
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hnc : 2 * R + aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnc' : 2 * R + aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨lm, hlmR, hlmy, hlminj, hlmsurj⟩ := labelMap_twoTorus hN hN' hnL hnL' hT Lab Lab' ys ys'
    hys hys' hmem
  obtain ⟨θ₁, θ₂⟩ := θ
  obtain ⟨θ₁', θ₂'⟩ := θ'
  simp only at hθ0 hθ0'
  subst hθ0 hθ0'
  have hP0 : ∀ (Y : {Y // Y ∈ 𝒴}), ¬ ∃ w : Lb ⊕ Lb,
      (Sum.inl (Sum.inr Y) : ObsLb (Lb ⊕ Lb) m₀ 𝒴) = Sum.inl (Sum.inl w) := by
    intro Y ⟨w, h⟩
    simp at h
  have hP1 : ∀ (Z : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (m₀ := m₀) (k + 1)}), ¬ ∃ w : Lb ⊕ Lb,
      (Sum.inr Z : ObsLb (Lb ⊕ Lb) m₀ 𝒴) = Sum.inl (Sum.inl w) := by
    intro Z ⟨w, h⟩
    simp at h
  refine ⟨fun l => ∃ w, l = Sum.inl (Sum.inl w), fun l => ∃ w, l = Sum.inl (Sum.inl w),
    fun l => match l with
      | Sum.inl (Sum.inl (Sum.inl a)) => fun _ hl => Sum.inl (Sum.inl (Sum.inl (lm a hl)))
      | Sum.inl (Sum.inl (Sum.inr a)) => fun _ hl => Sum.inl (Sum.inl (Sum.inr (lm a hl)))
      | Sum.inl (Sum.inr Y) => fun hP _ => absurd hP (hP0 Y)
      | Sum.inr Z => fun hP _ => absurd hP (hP1 Z), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ l hl Φ
    rw [tiltActObs_H, physActObs_H_new A hN hκ0 hεH hdj hK _ _ l (fun z hz => hl ⟨z, hz⟩),
      mul_zero]
  · intro s _ l hl Φ
    rw [tiltActObs_H, physActObs_H_new A' hN' hκ0' hεH' hdj' hK' _ _ l (fun z hz => hl ⟨z, hz⟩),
      mul_zero]
  · intro l hP hl
    rcases l with ((a | a) | Y) | Z
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)
  · intro l hP hl
    rcases l with ((a | a) | Y) | Z
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (lm a hl')) =
        (blocksOf m₀ (k + 1) Set.univ (Lab.ysite a)).image (σc)
      rw [hlmy a hl']
      exact blocksOf_image_boxMap hN hN' hnc hnc' (hlmR a hl')
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (lm a hl')) =
        (blocksOf m₀ (k + 1) Set.univ (Lab.ysite a)).image (σc)
      rw [hlmy a hl']
      exact blocksOf_image_boxMap hN hN' hnc hnc' (hlmR a hl')
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)
  · intro l₁ hP₁ hl₁ l₂ hP₂ hl₂ h
    rcases l₁ with ((a₁ | a₁) | Y₁) | Z₁
    · rcases l₂ with ((a₂ | a₂) | Y₂) | Z₂
      · have h' : lm a₁ hl₁ = lm a₂ hl₂ := by
          injection h with h; injection h with h; injection h
        rw [hlminj a₁ hl₁ a₂ hl₂ h']
      · injection h with h; injection h with h; injection h
      · exact absurd hP₂ (hP0 Y₂)
      · exact absurd hP₂ (hP1 Z₂)
    · rcases l₂ with ((a₂ | a₂) | Y₂) | Z₂
      · injection h with h; injection h with h; injection h
      · have h' : lm a₁ hl₁ = lm a₂ hl₂ := by
          injection h with h; injection h with h; injection h
        rw [hlminj a₁ hl₁ a₂ hl₂ h']
      · exact absurd hP₂ (hP0 Y₂)
      · exact absurd hP₂ (hP1 Z₂)
    · exact absurd hP₁ (hP0 Y₁)
    · exact absurd hP₁ (hP1 Z₁)
  · intro l' hP' hl'
    obtain ⟨w', rfl⟩ := hP'
    rcases w' with a' | a'
    · obtain ⟨a, ha, rfl⟩ := hlmsurj a' hl'
      exact ⟨Sum.inl (Sum.inl (Sum.inl a)), ⟨_, rfl⟩, ha, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := hlmsurj a' hl'
      exact ⟨Sum.inl (Sum.inl (Sum.inr a)), ⟨_, rfl⟩, ha, rfl⟩
  · intro s hs l hP hl Φ Φ' hΦ
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
    rcases l with ((a | a) | Y) | Z
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 (θ₁', 0) (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl (lm a hl')))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 (θ₁, 0) (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inl,
        physAct_H_inl, hAeq 1 h1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ,
        hAeq (s : ℂ) hs1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ]
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 (θ₁', 0) (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr (lm a hl')))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 (θ₁, 0) (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inr,
        physAct_H_inr, hAeq (s : ℂ) hs1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ]
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)

/-- **D3: the coefficient of the observable on two tori at the zero source.**  The hypotheses of
`obsCoeffParam_twoTorus_of_activities` on the steps, the local covers of the site `y` and of
`bm y`, the explicit terms `Ev`, `Ev'` of the site functionals, the parameters `θ`, `θ'` and the set
`T` of cubes of the box, with parameters of zero source (`θ.2 = 0`, `θ'.2 = 0`); the activities are
`tiltActObs A …`, `tiltActObs A' …` for activity families `A`, `A'` whose labels correspond (`ys`,
`ys'`) to domain families with `bm '' Y ∈ 𝒴v′ ↔ Y ∈ 𝒴v` on the box and whose values at the zero
source are the potential parts `-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evDec_z(Y)) ω ψ̂ σ e.1`
(`hAx`, `hAx'`, decoupled pairs `(F₂, Sol₂)`, `(F₂', Sol₂')` per block; the form exported by
`obsTiltLabels_local_fromTowerG`).  Then the coefficients of the observable agree:
`obsCoeffParam … θ' (cubeMap '' T) = obsCoeffParam … θ T`.  Radius: `2 p₁ ≤ c_ψ`,
`markedRad … c_ψ cc < δ₁`. -/
theorem obsCoeffParam_twoTorus_zeroSource (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    -- the site and the terms of its expansion
    (y : CTorus d L N₁ m₁ (k + 1)) (iy : Fin N)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 < cψ) (hq : p₁ / cψ ≤ 1 / 4)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    (hEv : Ev = evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ y))
        (fun u s => siteFun (GA) (HA) y iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc F₁
            (extParams (GA) (XA) s) u.1 u.2)))
    (hEv' : Ev' = evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm y)))
        (fun u s => siteFun (GB) (HB) (bm y) iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) 1 νS (SB).hG' cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc F₁'
            (extParams (GB) (XB) s) u.1 u.2)))
    (hdEv : ∀ Y ∈ 𝒴A, ∀ u ∈ XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir (SA).hG' Y u u' → Ev Y u = Ev Y u')
    (hdj : ∀ Y ∈ 𝒴A, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴B, IsDj m₀ (k + 1) Y)
    -- the parameters
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    -- the activities at the zero source
    (hθ0 : θ.2 = 0) (hθ0' : θ'.2 = 0) (hm₀ : 1 ≤ m₀) (hρ : 2 * p₁ ≤ cψ)
    {Lb Lb' : Type} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴v : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    {𝒴v' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴v}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴v'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmemV : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ 𝒴v' ↔ Y ∈ 𝒴v))
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N (SA) → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N (SB) → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0' : aEnt d L + 1 ≤ κ0') (hεH : 0 ≤ εH) (hεH' : 0 ≤ εH')
    {Kobs Kobs' : ℝ} (hK : Kco + Kco + K0 d L κ0 + K0 d L κ0 ≤ Kobs)
    (hK' : Kco' + Kco' + K0 d L κ0' + K0 d L κ0' ≤ Kobs')
    (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₂' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    {Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol₂' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Small (HA) (Sol₂ b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₂ b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₂ b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ b p).2))
    (hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small (HB) (Sol₂' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₂' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₂' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))} (hθV : θ ∈ V) (hθV' : θ' ∈ V')
    (hAx : ∀ e ∈ V, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb) (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b),
      (A ((e.1, 0) : physParam N (SA)) σ).H l Φ = -(β : ℂ) *
        ∑ z : TA, if Lab.ysite l ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
            m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SA).hG' cc (F₂ z) (Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) νS k z) ∅ 1 0 (Lab.ysite l))
            ((SA).hatOf m₀ p₁ hp Φ)) taylorWeight ((SA).hatOf m₀ p₁ hp Φ) σ
            (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        else 0)
    (hAx' : ∀ e ∈ V', ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb') (Φ : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ = -(β : ℂ) *
        ∑ z : TB, if Lab'.ysite l ∈ polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
            m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) 1 νS (SB).hG' cc (F₂' z) (Sol₂' z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) νS k z) ∅ 1 0 (Lab'.ysite l))
            ((SB).hatOf m₀ p₁ hp' Φ)) taylorWeight ((SB).hatOf m₀ p₁ hp' Φ) σ
            (e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
        else 0) :
    obsCoeffParam ((SB).blockSplit m₀ hp').μ
        (fun θ t σ => tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ t σ)
        (fun m => obsY1 m₀ (SB) (Lb' ⊕ Lb') (𝒴B) m)
        (fun m => blockMarkC (SB) m₀ hp' m.1 m.2)
        (fun θ m T'' => obsHker (𝒴B) (fun Y => hatCoeff (Ev' Y)
          (θ.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) (obsUnitVec (SB) m)) m₀ T'')
        (obsRemLab (𝒴B) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ (Lb' ⊕ Lb') (𝒴B) (rootCube (m₀ := m₀) (blockIndex (bm y)))))
        (fun θ => obsGrFam (SB) m₀ hp' Ev' (𝒴B)
          (XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps) θ) θ' (T.image (σc)) =
      obsCoeffParam ((SA).blockSplit m₀ hp).μ
        (fun θ t σ => tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ t σ)
        (fun m => obsY1 m₀ (SA) (Lb ⊕ Lb) (𝒴A) m)
        (fun m => blockMarkC (SA) m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker (𝒴A) (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec (SA) m)) m₀ T'')
        (obsRemLab (𝒴A) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ (Lb ⊕ Lb) (𝒴A) (rootCube (m₀ := m₀) (blockIndex y))))
        (fun θ => obsGrFam (SA) m₀ hp Ev (𝒴A)
          (XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps) θ) θ T := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨P, P', ψ, hA0, hA0', hψP, hψb, hψinj, hψsurj, hA⟩ := tiltActObs_twoTorus hN2 hk νS β p₁ δ
    hN hN' hnL hnL' hT Lab Lab' ys ys' hys hys' hmemV hdj hdj' hp hp' A A' hκ0 hκ0' hεH hεH' hK hK'
    Rg hR 𝒰 θ θ' hθ0 hθ0'
    (fun σ hσ l l' hlR hl' Φ Φ' hΦ => labelActZero_twoTorus hN2 hk νS β p₁ δ hC hC' hMX hmar hαK
      hsm hm₀ hN hN' hn hn' hnS hnS' hnF hnF' cc hcψ.le hρ hrad hF₂ hF₂' hSol₂ hSol₂' hp hp' Lab
      Lab' A A' hAx hAx' θ θ' hθV hθV' hθ hθ' hraw hσ l l' hlR hl' Φ Φ' hΦ)
  exact obsCoeffParam_twoTorus_of_activities hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm hN hN' hn hn'
    hnS hnS' hnF hnF' y iy hX₁R cc hcψ hq hrad hF₁ hF₁' hSol hSol' hEv hEv' hdEv hdj hdj' θ θ' hθ
    hθ' hraw hp hp' T hT (Lab.sum Lab) (Lab'.sum Lab')
    (fun θ t σ => tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ t σ)
    (fun θ t σ => tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ t σ) P P' hA0 hA0' ψ hψP hψb
    hψinj hψsurj hA

end Activity

end Balaban.Polymer.TwoTorusStep
