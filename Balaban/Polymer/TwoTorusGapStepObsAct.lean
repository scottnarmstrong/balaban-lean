/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsPart
public import Balaban.Polymer.TwoTorusGapObsRecentreMarks
public import Balaban.Polymer.TwoTorusObsActivity

/-!
# The explicit activities of corresponding labels under the recentring map

`labelActZero_recentred`: the activities of the label `l` at `(θ.1, 0)` and of the label `l'` with
domain `φ '' (ysite l)` at `(θ'.1, 0)` agree, `φ x = bm (x + tA) - tB`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric

section ActRec

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

/-- **The explicit activities of corresponding labels under the recentring map.**  As
`labelActZero_twoTorus`, for the domains `φ '' Y` with `φ x = bm (x + tA) - tB`. -/
theorem labelActZero_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ R : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htAz : tA = (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (htBz : tB = (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
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
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tA) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      (symRaw (Equiv.addRight tB) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)))
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (l : Lb) (l' : Lb')
    (hlR : ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    (hl' : Lab'.ysite l' = (fun x => bm (x + tA) - tB) '' Lab.ysite l)
    (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
        ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) :
    (A' ((θ'.1, 0) : physParam N (SB)) σ).H l' Φ' = (A ((θ.1, 0) : physParam N (SA)) σ).H l Φ := by
  have hσ2 : ‖σ‖ < 2 := by linarith
  have hp1 : (0 : ℝ) < p₁ := hp
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  rw [hAx' θ' hθV' σ hσ2 l' Φ', hAx θ hθV σ hσ2 l Φ, hl', hDe, hDe']
  congr 1
  have hhat := hatOf_rec (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) m₀ p₁ hp hp'
    (R := R) (tA := tA) (tB := tB) hΦ
  subst htAz htBz
  exact vpartTerm_recentred hC hC' hk (SA).hG' (SB).hG' cc hcψ hMX hmar hαK hsm hF₂ hF₂' hSol₂
    hSol₂' hd hL hm₀ hm₁ hN hN' z hz hlR hn20 hn20' hnF hnF' hD hD'
    (by rw [← hDe, ← hDe']; exact hraw)
    (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p) (fun p => (SA).hatOf_mem m₀ hp1 hp Φ p)
    (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) (fun p => (SB).hatOf_mem m₀ hp1 hp' Φ' p) hρ
    hhat hhat hrad taylorWeight hσ

end ActRec

end Balaban.Polymer.TwoTorusStep
