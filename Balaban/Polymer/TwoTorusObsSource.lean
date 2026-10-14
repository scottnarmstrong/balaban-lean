/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsSourceSite

/-!
# The activities of the observable on two tori at nonzero source

At a parameter `e = (e.1, g)` of nonzero source the activity of a label reads, besides the activity
at the zero source `(e.1, 0)` (the potential part of the direct terms), the source part
`∑_s g(s) [Y ∈ polyDom_s] dirTerm (Ev_s Y) (fun _ => 1) ψ̂ ψ̂ σ e.1` of the direct terms at its
domain `Y` (`hAs`; the source part of the appended conjunct of
`sourceDirectTerms_scale_fromTowerG_ray_rho`, with `β · (g / β) = g`).  The terms `Ev_s` are the
explicit terms `evTerm … (siteFun …)` of the expansion of the site functional `δφ(s)`.

## Main statements

* `labelActSource_twoTorus`: the activities of corresponding labels of the box agree at
  corresponding parameters, including the source, which agree on the box.
* `tiltActObs_twoTorus_source`: the hypotheses of `obsCoeffParam_twoTorus_of_activities` on the
  activities `tiltActObs A …` at parameters of arbitrary source.
* `obsCoeffParam_twoTorus_source`: the coefficients of the observable on two tori at parameters of
  nonzero source.
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

/-- **D2 (source part): the activities of corresponding labels on two tori at nonzero source.**
  Let the activity families `A`, `A'` of the two steps have the explicit values at the zero source (`hAx`,
 `hAx'`, as in `labelActZero_twoTorus`) and, at the parameters `θ ∈ V`, `θ' ∈ V'`, the source decomposition
 `hAs`, `hAs'`: the activity at `θ` is the activity at `(θ.1, 0)` plus the source part
 `∑_s θ.2(s) [Y ∈ polyDom_s] dirTerm (Ev₃_s Y) (fun _ => 1) ψ̂ ψ̂ σ θ.1` at the domain `Y` of the label, the
 terms `Ev₃_s` of the expansion of the site functionals being explicit (`hEv₃`, decoupled pairs
 `(F₃, Sol₃)`) and analytic (`hanEv₃`).  For a label `l` of the box and a label `l'` with domain
 `bm '' Y`, parameters whose raw data agree on the box of radius `R + 3 L^(k+1)` and whose sources
 agree on the box of radius `R` (`hsrc`), `‖σ‖ ≤ 1` and block variables agreeing at corresponding
 unit points of the box, the activities of `l'` at `θ'` and of `l` at `θ` agree.  The radius:
 `2 p₁ ≤ c_ψ` and `markedRad … c_ψ cc < δ₁`. -/
theorem labelActSource_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
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
    {F₃ : CTorus d L N₁ m₁ (k + 1) × Fin N →
      DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₃ : CTorus d L N₁ m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Ev₃ : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) → ℂ}
    (hF₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃ a (s, rawOf D) = (φ, α))
    (hSol₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃ a p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Small (HA) (Sol₃ a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₃ a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₃ a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ a p).2))
    (hEv₃ : ∀ a : CTorus d L N₁ m₁ (k + 1) × Fin N, Ev₃ a =
      evTerm (fun i : ParIdx (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) =>
        i.1.1) (GA) m₀ (X1 (GA) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GA) (HA) a.1 a.2
          (F₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
            u.1))
          (Sol₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
            flEdat (GA) (HA)
              (F₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc (F₃ a)
                (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc (F₃ a)
            (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁ m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃ a Y) (XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GA) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {F₃' : CTorus d L N₁' m₁ (k + 1) × Fin N →
      DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
        ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    {Sol₃' : CTorus d L N₁' m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    {Ev₃' : CTorus d L N₁' m₁ (k + 1) × Fin N → Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) → ℂ}
    (hF₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃' a (s, rawOf D) = (φ, α))
    (hSol₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃' a p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Small (HB) (Sol₃' a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₃' a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₃' a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃' a p).2))
    (hEv₃' : ∀ a : CTorus d L N₁' m₁ (k + 1) × Fin N, Ev₃' a =
      evTerm (fun i : ParIdx (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) =>
        i.1.1) (GB) m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GB) (HB) a.1 a.2
          (F₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
            u.1))
          (Sol₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
            flEdat (GB) (HB)
              (F₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (GB) 1 νS (SB).hG' cc (F₃' a)
                (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc (F₃' a)
            (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁' m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃' a Y) (XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GB) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hAs : ∀ e ∈ V, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb)
      (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b),
      (A e σ).H l Φ = (A ((e.1, 0) : physParam N (SA)) σ).H l Φ +
        ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
          if Lab.ysite l ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃ s (Lab.ysite l)) (fun _ => (1 : ℂ))
              ((SA).hatOf m₀ p₁ hp Φ) ((SA).hatOf m₀ p₁ hp Φ) σ
              (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          else 0)
    (hAs' : ∀ e ∈ V', ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb')
      (Φ : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (A' e σ).H l Φ = (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ +
        ∑ s : CTorus d L N₁' m₁ (k + 1) × Fin N,
          if Lab'.ysite l ∈ polyDom (GB) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃' s (Lab'.ysite l)) (fun _ => (1 : ℂ))
              ((SB).hatOf m₀ p₁ hp' Φ) ((SB).hatOf m₀ p₁ hp' Φ) σ
              (e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
          else 0)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθV : θ ∈ V) (hθV' : θ' ∈ V')
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hsrc : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → ∀ i, θ'.2 (bm x) i = θ.2 x i)
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (l : Lb) (l' : Lb')
    (hlR : ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hl' : Lab'.ysite l' = bm '' Lab.ysite l)
    (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) :
    (A' θ' σ).H l' Φ' = (A θ σ).H l Φ := by
  have hσ2 : ‖σ‖ < 2 := by linarith
  have hp1 : (0 : ℝ) < p₁ := hp
  have h0 := labelActZero_twoTorus hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm hm₀ hN hN' hn hn' hnS
    hnS' hnF hnF' cc hcψ hρ hrad hF₂ hF₂' hSol₂ hSol₂' hp hp' Lab Lab' A A' hAx hAx' θ θ' hθV hθV'
    hθ hθ' hraw hσ l l' hlR hl' Φ Φ' hΦ
  rw [hAs' θ' hθV' σ hσ2 l' Φ', hAs θ hθV σ hσ2 l Φ, h0]
  congr 1
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  have hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → ∀ i,
      (SB).hatOf m₀ p₁ hp' Φ' (unitPt (SB).hG' (bm x), i) =
        (SA).hatOf m₀ p₁ hp Φ (unitPt (SA).hG' x, i) :=
    hatOf_boxMap (SA).hG' (SB).hG' hN2 hk νS β p₁ δ m₀ p₁ hp hp' Φ Φ' hΦ
  rw [hl', hDe, hDe']
  refine sourceSum_twoTorus (ϱ := ϱ) hN hN' hnF hnF' hlR _ _ (fun s hs => ?_)
  have hsY : s.1 ∈ Lab.ysite l := mem_of_mem_polyDom_site hN s.1 hs
  have hxR := hlR _ hsY
  have hX₁R : ∀ x ∈ LocalCover.nbhd m₀ s.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun x hx => hlR x (nbhd_subset_of_mem_polyDom hN s.1 hs hx)
  simp only
  rw [hsrc s.1 hxR s.2]
  congr 1
  exact dirTerm_siteEv_twoTorus hC hC' hk (SA).hG' (SB).hG' cc hcψ hMX hmar hαK hsm
    (hF₃ s) (hF₃' (bm s.1, s.2)) (hSol₃ s) (hSol₃' (bm s.1, s.2)) hN hN' s.1 s.2 hX₁R hlR hn hn'
    hnS hnS' hnF hnF' hD hD' (by rw [← hDe, ← hDe']; exact hraw)
    (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p) (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p)
    (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) hρ hhat hhat
    hrad (hEv₃ s) (hEv₃' (bm s.1, s.2)) (hanEv₃ s _) (hanEv₃' (bm s.1, s.2) _) hσ

/-- **D2 (source part): the activities of the observable on two tori at parameters of arbitrary
source.**  As `tiltActObs_twoTorus`, without the condition that the sources of `θ`, `θ'` vanish: the
activities of corresponding labels agree at the zero-source parameters `(θ.1, 0)`, `(θ'.1, 0)`
(`hAeq`) and at the parameters `θ`, `θ'` themselves (`hAeqθ`).  Then the activities
`tiltActObs A …` and `tiltActObs A' …` on the observable labels satisfy the hypotheses of
`obsCoeffParam_twoTorus_of_activities`: the first-order component of the label `(a)` reads the
activity at `(θ.1, 0)`, the second reads the activity at `θ`. -/
theorem tiltActObs_twoTorus_source (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
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
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hAeq : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      Lab'.ysite l' = bm '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' ((θ'.1, 0) : physParam N (SB)) σ).H l' Φ' = (A ((θ.1, 0) : physParam N (SA)) σ).H l Φ)
    (hAeqθ : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      Lab'.ysite l' = bm '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' θ' σ).H l' Φ' = (A θ σ).H l Φ) :
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
      show (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl (lm a hl')))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inl,
        physAct_H_inl, hAeq 1 h1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ,
        hAeq (s : ℂ) hs1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ]
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr (lm a hl')))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inr,
        physAct_H_inr, hAeqθ (s : ℂ) hs1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ]
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)

/-- **D2 (source part): the coefficient of the observable on two tori at nonzero source.**  The
statement of `obsCoeffParam_twoTorus_zeroSource` for parameters `θ`, `θ'` of arbitrary source, which
agree on the box of radius `R` (`hsrc`), with the activity families `A`, `A'` of the zero-source
values `hAx`, `hAx'` and of the source decomposition `hAs`, `hAs'` (the activity at `θ` is the
activity at `(θ.1, 0)` plus the source part, with the explicit analytic terms `Ev₃_s` of the
expansions of the site functionals, decoupled pairs `(F₃, Sol₃)`; the form of the appended conjunct
of `sourceDirectTerms_scale_fromTowerG_ray_rho`).  Then the coefficients of the observable agree:
`obsCoeffParam … θ' (cubeMap '' T) = obsCoeffParam … θ T`. -/
theorem obsCoeffParam_twoTorus_source (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
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
    -- the activities
    (hm₀ : 1 ≤ m₀) (hρ : 2 * p₁ ≤ cψ)
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
        else 0)
    {F₃ : CTorus d L N₁ m₁ (k + 1) × Fin N →
      DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₃ : CTorus d L N₁ m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Ev₃ : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) → ℂ}
    (hF₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃ a (s, rawOf D) = (φ, α))
    (hSol₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃ a p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Small (HA) (Sol₃ a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₃ a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₃ a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ a p).2))
    (hEv₃ : ∀ a : CTorus d L N₁ m₁ (k + 1) × Fin N, Ev₃ a =
      evTerm (fun i : ParIdx (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) =>
        i.1.1) (GA) m₀ (X1 (GA) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GA) (HA) a.1 a.2
          (F₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
            u.1))
          (Sol₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
            flEdat (GA) (HA)
              (F₃ a (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc (F₃ a)
                (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc (F₃ a)
            (extParams (GA) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁ m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃ : ∀ (a : CTorus d L N₁ m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁ m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃ a Y) (XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GA) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {F₃' : CTorus d L N₁' m₁ (k + 1) × Fin N →
      DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
        ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    {Sol₃' : CTorus d L N₁' m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    {Ev₃' : CTorus d L N₁' m₁ (k + 1) × Fin N → Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) → ℂ}
    (hF₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₃' a (s, rawOf D) = (φ, α))
    (hSol₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₃' a p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Small (HB) (Sol₃' a p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₃' a p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₃' a p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃' a p).2))
    (hEv₃' : ∀ a : CTorus d L N₁' m₁ (k + 1) × Fin N, Ev₃' a =
      evTerm (fun i : ParIdx (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) =>
        i.1.1) (GB) m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ a.1))
        (fun u t => siteFun (GB) (HB) a.1 a.2
          (F₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
            u.1))
          (Sol₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
            flEdat (GB) (HB)
              (F₃' a (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (GB) 1 νS (SB).hG' cc (F₃' a)
                (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc (F₃' a)
            (extParams (GB) (↑(LocalCover.nbhdF m₀ a.1) : Set (CTorus d L N₁' m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃' : ∀ (a : CTorus d L N₁' m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁' m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃' a Y) (XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : unitPts (GB) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hAs : ∀ e ∈ V, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb)
      (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b),
      (A e σ).H l Φ = (A ((e.1, 0) : physParam N (SA)) σ).H l Φ +
        ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
          if Lab.ysite l ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃ s (Lab.ysite l)) (fun _ => (1 : ℂ))
              ((SA).hatOf m₀ p₁ hp Φ) ((SA).hatOf m₀ p₁ hp Φ) σ
              (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
          else 0)
    (hAs' : ∀ e ∈ V', ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb')
      (Φ : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (A' e σ).H l Φ = (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ +
        ∑ s : CTorus d L N₁' m₁ (k + 1) × Fin N,
          if Lab'.ysite l ∈ polyDom (GB) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃' s (Lab'.ysite l)) (fun _ => (1 : ℂ))
              ((SB).hatOf m₀ p₁ hp' Φ) ((SB).hatOf m₀ p₁ hp' Φ) σ
              (e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
          else 0)
    (hsrc : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → ∀ i, θ'.2 (bm x) i = θ.2 x i) :
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
  obtain ⟨P, P', ψ, hA0, hA0', hψP, hψb, hψinj, hψsurj, hA⟩ := tiltActObs_twoTorus_source hN2 hk νS β p₁ δ
    hN hN' hnL hnL' hT Lab Lab' ys ys' hys hys' hmemV hdj hdj' hp hp' A A' hκ0 hκ0' hεH hεH' hK hK'
    Rg hR 𝒰 θ θ'
    (fun σ hσ l l' hlR hl' Φ Φ' hΦ => labelActZero_twoTorus hN2 hk νS β p₁ δ hC hC' hMX hmar hαK
      hsm hm₀ hN hN' hn hn' hnS hnS' hnF hnF' cc hcψ.le hρ hrad hF₂ hF₂' hSol₂ hSol₂' hp hp' Lab
      Lab' A A' hAx hAx' θ θ' hθV hθV' hθ hθ' hraw hσ l l' hlR hl' Φ Φ' hΦ)
    (fun σ hσ l l' hlR hl' Φ Φ' hΦ => labelActSource_twoTorus hN2 hk νS β p₁ δ hC hC' hMX hmar hαK
      hsm hm₀ hN hN' hn hn' hnS hnS' hnF hnF' cc hcψ.le hρ hrad hF₂ hF₂' hSol₂ hSol₂' hp hp' Lab
      Lab' A A' hAx hAx' hF₃ hSol₃ hEv₃ hanEv₃ hF₃' hSol₃' hEv₃' hanEv₃' hAs hAs' θ θ' hθV hθV' hθ
      hθ' hraw hsrc hσ l l' hlR hl' Φ Φ' hΦ)
  exact obsCoeffParam_twoTorus_of_activities hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm hN hN' hn hn'
    hnS hnS' hnF hnF' y iy hX₁R cc hcψ hq hrad hF₁ hF₁' hSol hSol' hEv hEv' hdEv hdj hdj' θ θ' hθ
    hθ' hraw hp hp' T hT (Lab.sum Lab) (Lab'.sum Lab')
    (fun θ t σ => tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ t σ)
    (fun θ t σ => tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ t σ) P P' hA0 hA0' ψ hψP hψb
    hψinj hψsurj hA

end Activity

end Balaban.Polymer.TwoTorusStep
