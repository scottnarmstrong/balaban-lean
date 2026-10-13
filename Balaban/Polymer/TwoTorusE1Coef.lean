/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusCoef
public import Balaban.Inhabited.E1MarkParamCommon
public import Balaban.Inhabited.E1LabelsBudgetG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The energy coefficient of one zero-class step on two tori

For two step tori `CTorus d L N₁ m₁ (k + 1)` and `CTorus d L N₁' m₁ (k + 1)` identified on a centred
box by `boxMap` (`bm`; `bc` on the coarse tori of the roots and blocks), this file continues
`TwoTorusCoef` towards the energy coefficient `c θ C = gsumCoeff μ … (A₀ θ) … C` of one step.

## D1: the margins

* `twoTorus_margins_of_lt`, `twoTorus_margins_of_lt_min`: the margins of the comparison of the
  marks (`markedOutDec_twoTorus`) follow from `4 R + 19 L^(k+2+m₀+m₁) + 5 < n` for `m₁ ≥ 1`.

## D2: the marks of the parameter family on two tori

* `e1MarkGParamG_twoTorus`: at a bridge label `Y′` of the box and the corresponding label
  `bm '' Y′` of the image root, for parameters `θ`, `θ′` whose raw data lie in the charts of the
  two tori and agree on the box, and `‖u‖ < 17/16`, the marks `e1MarkGParamG` of the two tori are
  equal.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis
  Balaban.Polymer Balaban.Multiscale

/-! ### D1: the margins -/

section Margins

variable {L : ℕ} [NeZero L]

/-- **D1: the margins of the comparison of the marks from one inequality.**  For `m₁ ≥ 1`, the
inequality `4 R + 19 L^(k+2+m₀+m₁) + 5 < n` implies the margins of `markedOutDec_twoTorus`
(`hn`, `hnS`, `hnF`, `hnH`, with `a_K = cellSide L m₀ m₁ (k + 1) = L^(k+1+m₀+m₁)`) and the margin
`2 R + 3 L^(k+1) + 5 < n` of the root masks (`rootMask_bc`). -/
theorem twoTorus_margins_of_lt {R k m₀ m₁ n : ℕ} (hm₁ : 1 ≤ m₁)
    (h : 4 * R + 19 * L ^ (k + 2 + m₀ + m₁) + 5 < n) :
    4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < n ∧
      2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
        5 * (L * cellSide L 0 m₁ (k + 1)) < n ∧
      2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < n ∧
      2 * (R + 2 * (L * cellSide L m₀ m₁ (k + 1))) + L * cellSide L m₀ m₁ (k + 1) < n ∧
      2 * R + 3 * L ^ (k + 1) + 5 < n := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hpow : ∀ {a b : ℕ}, a ≤ b → L ^ a ≤ L ^ b := fun hab => Nat.pow_le_pow_right hL hab
  have hcK : L * cellSide L m₀ m₁ (k + 1) = L ^ (k + 2 + m₀ + m₁) := by
    unfold cellSide
    rw [← pow_succ']
    congr 1
    omega
  have hc0 : L * cellSide L 0 m₁ (k + 1) = L ^ (k + 2 + m₁) := by
    unfold cellSide
    rw [← pow_succ']
    congr 1
    omega
  have h1 : L ^ (k + 1 + m₁) ≤ L ^ (k + 2 + m₀ + m₁) := hpow (by omega)
  have h2 : L ^ (k + 1) ≤ L ^ (k + 2 + m₀ + m₁) := hpow (by omega)
  have h3 : L ^ (k + 1 + 2) ≤ L ^ (k + 2 + m₀ + m₁) := hpow (by omega)
  have h4 : L ^ (k + 2 + m₁) ≤ L ^ (k + 2 + m₀ + m₁) := hpow (by omega)
  rw [hcK, hc0]
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **D1 on two tori**: `twoTorus_margins_of_lt` for both sides `n`, `n′` from
`4 R + 19 L^(k+2+m₀+m₁) + 5 < min n n′`. -/
theorem twoTorus_margins_of_lt_min {R k m₀ m₁ n n' : ℕ} (hm₁ : 1 ≤ m₁)
    (h : 4 * R + 19 * L ^ (k + 2 + m₀ + m₁) + 5 < min n n') :
    (4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < n ∧
      2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
        5 * (L * cellSide L 0 m₁ (k + 1)) < n ∧
      2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < n ∧
      2 * (R + 2 * (L * cellSide L m₀ m₁ (k + 1))) + L * cellSide L m₀ m₁ (k + 1) < n ∧
      2 * R + 3 * L ^ (k + 1) + 5 < n) ∧
    (4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < n' ∧
      2 * (R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
        5 * (L * cellSide L 0 m₁ (k + 1)) < n' ∧
      2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < n' ∧
      2 * (R + 2 * (L * cellSide L m₀ m₁ (k + 1))) + L * cellSide L m₀ m₁ (k + 1) < n' ∧
      2 * R + 3 * L ^ (k + 1) + 5 < n') :=
  ⟨twoTorus_margins_of_lt hm₁ (lt_of_lt_of_le h (min_le_left _ _)),
    twoTorus_margins_of_lt hm₁ (lt_of_lt_of_le h (min_le_right _ _))⟩

end Margins

/-! ### D2: the marks of the parameter family on two tori -/

section MarkParam

open Balaban.Inhabited Balaban.Inhabited.LevelStep Balaban.Localization.I5Inhabited
  Balaban.Inhabited.MarkBudgetAudit

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
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
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

omit [NeZero N₁'] in
/-- Membership in the block mask `blockU w` of a step: the unit block of level `k + 1` of the unit
point is `w`. -/
theorem mem_blockU_iff_unitBlock1 (S : StepSetting d L N₁ m₁ k N ϱ) (y : S.U)
    (w : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    y ∈ S.blockU w ↔ unitBlock1 (y : UnitTorus d L N₁ m₁ k) = w := by
  unfold StepSetting.blockU
  simp

/-- **D2: the marks of the parameter family at a label of the box, on two tori.**  Let `z` be a
root of the first torus and `Y′` a bridge label of `z` (for the label domains `e1DomG` of the
blocks) inside the box of radius `R`, and let `bc z`, `bm '' Y′` be the root and the label of the
second torus.  Let `θ`, `θ′` be parameters whose raw data lie in the charts `XiCRaw … eps` of the
two tori and agree on the box of radius `R + 3 L^(k+1)`, let `‖u‖ < 17/16`, and let the block
variables `Φ`, `Φ′` agree at corresponding unit points of the box.  Then the marks `e1MarkGParamG`
of the two steps are equal.  This is `markedOutDec_twoTorus` (with `m₀ = 1`, `a₁ = 1`, the mask
`blockU`, `cc = β_U^{-1/2}`) under the two guards of `e1MarkGParamG_of_mem`; the root masks
correspond by `rootMask_bc`, and the margins come from the single inequality
`4 R + 19 L^(k+3+m₁) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)` (`twoTorus_margins_of_lt`). -/
theorem e1MarkGParamG_twoTorus
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (hm₁ : 1 ≤ m₁)
    (z : TA) {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z})
    (i' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SB)) (bc z)})
    (hi : i'.1 = bm '' i.1)
    (hiR : ∀ y ∈ i.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit 1 hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit 1 hp').Ωb c)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    {u : ℂ} (hu : ‖u‖ < (17 / 16 : ℝ))
    (hum : ‖u‖ * markedRad d L N k 1 κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc z) eps θ' i' u Φ' =
      e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ := by
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  rw [e1MarkGParamG_of_mem (SB) F₁' Sol' ρ hp' (bc z) eps θ' i' u Φ' hθ' hu,
    e1MarkGParamG_of_mem (SA) F₁ Sol ρ hp z eps θ i u Φ hθ hu]
  obtain ⟨D, hD, hDθ⟩ := hθ
  obtain ⟨D', hD', hDθ'⟩ := hθ'
  rw [hDθ] at hraw ⊢
  rw [hDθ'] at hraw ⊢
  rw [hi]
  refine markedOutDec_twoTorus hC hC' hk hGA hGB _ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' le_rfl
    hN hN' z hz hrc hroot hiR hn1 hn1' hnS hnS' hnF hnF' hnH hnH' hD hD' hraw hN2 νS β p₁ δ hρ
    hp hp' Φ Φ' hΦ (fun x hx => ?_) hum _
  have h := rootMask_bc (N₁' := N₁') hnM hnM' hGA hGB z hz hrc hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact (mem_blockU_iff_unitBlock1 (SB) _ _).trans (h.trans (mem_blockU_iff_unitBlock1 (SA) _ _).symm)

end MarkParam

/-! ### D2 at `d = L = 3`, `N = 2` -/

section MarkParamThree

open Balaban.Inhabited Balaban.Inhabited.LevelStep Balaban.Localization.I5Inhabited
  Balaban.Inhabited.MarkBudgetAudit

variable {N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁']

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * 3 ^ m₁) * 3 ^ (k + 1)) ((N₁' * 3 ^ m₁) * 3 ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))
  (N₁' * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus 3 (N₁' * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
  (ϱ := rhoSep m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := 3) (L := 3) (N₁ := N₁') (m₁ := m₁) (k := k + 1)
  (ϱ := rhoSep m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
  (ϱ := rhoSep m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := 3) (L := 3) (N₁ := N₁') (m₁ := m₁) (k := k + 1)
  (ϱ := rhoSep m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "SA" => hatStepK (N₁ := N₁) k m₁ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepK (N₁ := N₁') k m₁ hk νS β p₁ δ

/-- **D2 at `d = L = 3`, `N = 2`: the marks `e1MarkGParam` of the fixed tower on two tori.**  The
statement of `e1MarkGParamG_twoTorus` for the steps `hatStepK` (the steps `T.step` of a
`StepTower`, with `ϱ = rhoSep m₁`) and the marks `e1MarkGParam` (`e1MarkGParamG_three`). -/
theorem e1MarkGParam_twoTorus
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hC : FlCore 2 (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore 2 (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin 3 3 2 BG κ (xiC1 3 * eps) < δc)
    (hαK : K4 3 3 2 BG κ * (xiC1 3 * eps) < coerciveConst 3 / 2)
    (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 →
      ((GA).Ω 1 × Fin 2 → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData 3 3 (N₁' * 3 ^ m₁) (k + 1) 2 →
      ((GB).Ω 1 × Fin 2 → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) 2),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 3 3 2) (c7 3 3 2 BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin 2 → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight 3 1) νS (rho4 3 3 2 BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) 2),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 3 3 2) (c7 3 3 2 BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin 2 → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight 3 1) νS (rho4 3 3 2 BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) 2 →
      ((HA).Ω 1 × Fin 2 → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) 2 →
      ((HB).Ω 1 × Fin 2 → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) 2),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight 3 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight 3 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight 3 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight 3 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight 3 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight 3 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) 2),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight 3 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight 3 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight 3 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight 3 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight 3 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight 3 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hN : 3 ∣ N₁) (hN' : 3 ∣ N₁') (hm₁ : 1 ≤ m₁)
    (z : TA) {rc R : ℕ} (hz : InBox 3 rc (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))) z)
    (hrc : 3 ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox 3 R ((N₁ * 3 ^ m₁) * 3 ^ (k + 1)) x)
    (hn : 4 * R + 19 * 3 ^ (k + 2 + 1 + m₁) + 5 < (N₁ * 3 ^ m₁) * 3 ^ (k + 1))
    (hn' : 4 * R + 19 * 3 ^ (k + 2 + 1 + m₁) + 5 < (N₁' * 3 ^ m₁) * 3 ^ (k + 1))
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (SA)) z})
    (i' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom (SB)) (bc z)})
    (hi : i'.1 = bm '' i.1)
    (hiR : ∀ y ∈ i.1, InBox 3 R ((N₁ * 3 ^ m₁) * 3 ^ (k + 1)) y)
    (θ : physParam 2 (SA)) (θ' : physParam 2 (SB))
    (hθ : (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) ∈
      XiCRaw (GA) (compWeight 3 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData 3 3 (N₁' * 3 ^ m₁) (k + 1) 2) ∈
      XiCRaw (GB) (compWeight 3 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox 3 (R + 3 * 3 ^ (k + 1)) ((N₁ * 3 ^ m₁) * 3 ^ (k + 1)) z}
      (θ.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2) (θ'.1 : RawData 3 3 (N₁' * 3 ^ m₁) (k + 1) 2))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit 1 hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit 1 hp').Ωb c)
    (hΦ : ∀ x, InBox 3 R ((N₁ * 3 ^ m₁) * 3 ^ (k + 1)) x →
      Φ' ((SB).cellOf 1 (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
        Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    {u : ℂ} (hu : ‖u‖ < corrU)
    (hum : ‖u‖ * markedRad 3 3 2 k 1 κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    e1MarkGParam (SB) F₁' Sol' ρ hp' (bc z) eps θ' i' u Φ' =
      e1MarkGParam (SA) F₁ Sol ρ hp z eps θ i u Φ :=
  e1MarkGParamG_twoTorus (d := 3) (L := 3) (N := 2) le_rfl hk νS β p₁ δ hC hC' hGA hGB hMX hmar hαK
    hsm hF₁ hF₁' hSol hSol' (by simpa using hN) (by simpa using hN') hm₁ z hz hrc hroot hn hn' i i'
    hi hiR θ θ' hθ hθ' hraw hρ hp hp' Φ Φ' hΦ hu hum

end MarkParamThree

/-! ### D3: integrals of local functions against product measures -/

section PiIntegral

open MeasureTheory

/-- **The integral of a function of the coordinates in `S`**: against a product of probability
measures it is the integral, against the product over `S`, of the function of the configuration
extended off `S` by any reference configuration `Φ₀`. -/
theorem integral_pi_eq_of_depOn {B : Type*} [Fintype B] {Ω : B → Type*}
    [∀ b, MeasurableSpace (Ω b)] (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (S : Finset B) (Φ₀ : ∀ b, Ω b) {F : (∀ b, Ω b) → ℂ} (hF : DepOn S F) :
    ∫ Φ, F Φ ∂(Measure.pi μ) =
      ∫ x, F (extendCfg S Φ₀ x) ∂(Measure.pi fun i : S => μ i) := by
  classical
  let p : B → Prop := fun b => b ∈ S
  let e := MeasurableEquiv.piEquivPiSubtypeProd Ω p
  let g : (∀ i : {i // p i}, Ω i) → ℂ := fun x => F (extendCfg S Φ₀ x)
  have hkey : ∀ w, F (e.symm w) = g w.1 := by
    intro w
    refine hF _ _ (fun b hb => ?_)
    show (Equiv.piEquivPiSubtypeProd p Ω).symm w b = extendCfg S Φ₀ w.1 b
    have hb' : p b := hb
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]
    simp [hb', extendCfg, hb]
  have hmp := measurePreserving_piEquivPiSubtypeProd μ p
  have h2 : ∫ Φ, F Φ ∂(Measure.pi μ) = ∫ x, F (e.symm (e x)) ∂(Measure.pi μ) := by simp
  rw [h2, hmp.integral_comp' (g := fun w => F (e.symm w))]
  simp_rw [hkey]
  rw [integral_fun_fst]
  simp only [probReal_univ, one_smul]
  convert rfl

/-- **Transport of an integral along an injective relabelling of the coordinates.**  Let `f`
depend only on the coordinates in `W` and let `ι : U → U'` be injective on `W`.  Then the integral
of `x' ↦ f (x' ∘ ι)` against the product of copies of a probability measure `ν₁` over `U'` equals
the integral of `f` against the product over `U`. -/
theorem integral_pi_comp_of_injOn {U U' E : Type*} [Fintype U] [Fintype U'] [MeasurableSpace E]
    (ν₁ : Measure E) [IsProbabilityMeasure ν₁] (ι : U → U') (W : Finset U)
    (hι : Set.InjOn ι W) {f : (U → E) → ℂ} (hf : DepOn (Ω := fun _ : U => E) W f) :
    ∫ x', f (fun u => x' (ι u)) ∂(Measure.pi fun _ : U' => ν₁) =
      ∫ x, f x ∂(Measure.pi fun _ : U => ν₁) := by
  classical
  have : Nonempty E := nonempty_of_isProbabilityMeasure ν₁
  let x₀ : U → E := fun _ => Classical.arbitrary E
  let x₀' : U' → E := fun _ => Classical.arbitrary E
  have hbij : Function.Bijective
      (fun a : W => (⟨ι a.1, Finset.mem_image_of_mem ι a.2⟩ : W.image ι)) := by
    refine ⟨fun a b h => Subtype.ext (hι a.2 b.2 (congrArg Subtype.val h)), fun b => ?_⟩
    obtain ⟨u, hu, hub⟩ := Finset.mem_image.1 b.2
    exact ⟨⟨u, hu⟩, Subtype.ext hub⟩
  let τ : W ≃ W.image ι := Equiv.ofBijective _ hbij
  have hf' : DepOn (Ω := fun _ : U' => E) (W.image ι) (fun x' : U' → E => f (fun u => x' (ι u))) :=
    fun x' y' h => hf _ _ (fun u hu => h _ (Finset.mem_image_of_mem ι hu))
  rw [integral_pi_eq_of_depOn (fun _ => ν₁) (W.image ι) x₀' hf',
    integral_pi_eq_of_depOn (fun _ => ν₁) W x₀ hf]
  have hmp := measurePreserving_piCongrLeft (α := fun _ : W.image ι => E)
    (fun _ : W.image ι => ν₁) τ
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine hf _ _ (fun u hu => ?_)
  have hu' : ι u ∈ W.image ι := Finset.mem_image_of_mem ι hu
  have hτ : (⟨ι u, hu'⟩ : W.image ι) = τ ⟨u, hu⟩ := rfl
  simp only [extendCfg, hu, hu', dite_true]
  rw [hτ, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

end PiIntegral

/-! ### D3: the block measures on two tori -/

section BlockMeasure

open MeasureTheory Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

omit [NeZero N₁'] in
/-- The integral against the block measures of a step is the integral against the product
measure `ν_{p₁}` over the unit points, of the function of the block restrictions. -/
theorem integral_blockSplit_eq (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (hp : 0 < S.p₁)
    (G : (∀ c, (S.blockSplit m₀ hp).Ωb c) → ℂ) :
    ∫ Φ, G Φ ∂(Measure.pi (S.blockSplit m₀ hp).μ) =
      ∫ x, G (fun _ u => x u.1) ∂(Measure.pi fun _ : S.U => fluctMeasure1 N S.p₁) := by
  rw [← (S.blockSplit m₀ hp).map_eq]
  exact integral_map_equiv (piSplitEquiv (E := Rn N) (S.cellOf m₀)).symm G

omit [NeZero N₁'] in
/-- A unit point lies in the block `cellOf m₀ u` of the site chosen for it. -/
theorem exists_site_of_unitPt (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) (u : S.U) :
    ∃ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = (u : UnitTorus d L N₁ m₁ k) ∧
      x ∈ box (S.cellOf m₀ u).1 (cellSide L m₀ m₁ (k + 1)) := by
  have h := Classical.choose_spec ((mem_unitPts S.G').1 u.2)
  exact ⟨_, h.2, mem_box_cbase (cellSide_pos m₀ m₁ (k + 1)) _⟩

/-- **D3: the block measures on two tori.**  Let `Z` be a set of blocks (`π_{k+1}`-cubes of side
`a = L^(k+1+m₀+m₁)`) of the first torus inside the box of radius `R`, `F` a function of the block
variables depending only on the blocks of `Z`, and `F′` a function of the block variables of the
second torus with `F′ Φ′ = F Φ` whenever `Φ` and `Φ′` agree at corresponding unit points of the
box.  Then the integrals of `F′` and `F` against the products of the block measures
`(S.blockSplit m₀ hp).μ` of the two steps are equal.  The block measures are the products of the
one-site measure `ν₁` over the unit points of the block (a formula, the same on both tori); the
unit points of the blocks of `Z` correspond injectively under the box map of the unit lattices
(`unitBlock_boxMap`), and the integral is transported by `integral_pi_comp_of_injOn`.  Margin:
`2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem integral_blockSplit_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Z : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hZ : ∀ b ∈ Z, ∀ x ∈ box b.1 (cellSide L m₀ m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {F : (∀ c, ((SA).blockSplit m₀ hp).Ωb c) → ℂ} (hF : DepOn Z F)
    {F' : (∀ c, ((SB).blockSplit m₀ hp').Ωb c) → ℂ}
    (hFF : ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) → F' Φ' = F Φ) :
    ∫ Φ', F' Φ' ∂(Measure.pi ((SB).blockSplit m₀ hp').μ) =
      ∫ Φ, F Φ ∂(Measure.pi ((SA).blockSplit m₀ hp).μ) := by
  classical
  have : IsProbabilityMeasure (fluctMeasure1 N p₁) := isProbabilityMeasure_fluctMeasure1 N hp
  rw [integral_blockSplit_eq (SB) m₀ hp' F', integral_blockSplit_eq (SA) m₀ hp F]
  let ι : (SA).U → (SB).U := fun u =>
    ⟨bU (u : UnitTorus d L N₁ m₁ k), mem_unitPts_levelTop (N₁ := N₁') (ϱ := ϱ) _⟩
  have hι : ∀ x : CTorus d L N₁ m₁ (k + 1), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      unitPt hGB (bm x) = ι (unitPt hGA x) :=
    fun x hx => Subtype.ext (unitBlock_boxMap hn hx)
  have key : ∀ x' : (SB).U → Rn N,
      F' (fun _ u => x' u.1) = F (fun _ u => x' (ι u.1)) := by
    intro x'
    refine hFF _ _ (fun x hx => ?_)
    exact congrArg x' (hι x hx)
  simp_rw [key]
  let W : Finset (SA).U := Finset.univ.filter fun u => (SA).cellOf m₀ u ∈ Z
  have hsite : ∀ u ∈ W, ∃ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = (u : UnitTorus d L N₁ m₁ k) ∧
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro u hu
    obtain ⟨x, hxu, hxb⟩ := exists_site_of_unitPt (SA) m₀ u
    exact ⟨x, hxu, hZ _ (Finset.mem_filter.1 hu).2 x hxb⟩
  have hinj : Set.InjOn ι W := by
    intro u₁ hu₁ u₂ hu₂ h
    obtain ⟨x₁, hx₁u, hx₁⟩ := hsite u₁ hu₁
    obtain ⟨x₂, hx₂u, hx₂⟩ := hsite u₂ hu₂
    have h1 : bU (unitBlock x₁) = bU (unitBlock x₂) := by
      rw [hx₁u, hx₂u]; exact congrArg Subtype.val h
    rw [← unitBlock_boxMap hn hx₁, ← unitBlock_boxMap hn hx₂] at h1
    have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
    have e1 := unitBlock_boxMap (N₁ := N₁') (N₁' := N₁) hn' (inBox_boxMap hm' hx₁)
    have e2 := unitBlock_boxMap (N₁ := N₁') (N₁' := N₁) hn' (inBox_boxMap hm' hx₂)
    rw [boxMap_boxMap hm' hx₁] at e1
    rw [boxMap_boxMap hm' hx₂] at e2
    apply Subtype.ext
    rw [← hx₁u, ← hx₂u, e1, e2, h1]
  have hdep : DepOn (Ω := fun _ : (SA).U => Rn N) W
      (fun x : (SA).U → Rn N => F (fun _ u => x u.1)) := by
    intro x y hxy
    refine hF _ _ (fun b hb => ?_)
    funext u
    refine hxy u.1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    rw [u.2]; exact hb
  exact integral_pi_comp_of_injOn (fluctMeasure1 N p₁) ι W hinj hdep

end BlockMeasure

end Balaban.Polymer.TwoTorusStep
