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

/-! ### D4: finite sets under a map injective on a set -/

section ImageInj

variable {α β : Type*} [DecidableEq β] {σ : α → β} {S : Finset α}

/-- Images of subsets of `S` under a map injective on `S` are equal only for equal subsets. -/
theorem eq_of_image_eq_of_injOn (hσ : Set.InjOn σ (S : Set α)) {U V : Finset α} (hU : U ⊆ S)
    (hV : V ⊆ S) (h : U.image σ = V.image σ) : U = V := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (h ▸ Finset.mem_image_of_mem σ hx)
    rw [hσ (hV hy) (hU hx) hyx] at hy
    exact hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (h.symm ▸ Finset.mem_image_of_mem σ hx)
    rw [hσ (hU hy) (hV hx) hyx] at hy
    exact hy

/-- Images of subsets of `S` under a map injective on `S` meet iff the subsets meet. -/
theorem not_disjoint_image_iff_of_injOn (hσ : Set.InjOn σ (S : Set α)) {U V : Finset α}
    (hU : U ⊆ S) (hV : V ⊆ S) : ¬ Disjoint (U.image σ) (V.image σ) ↔ ¬ Disjoint U V := by
  rw [not_iff_not, Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro h x hxU hxV
    exact h (Finset.mem_image_of_mem σ hxU) (Finset.mem_image_of_mem σ hxV)
  · intro h x' hxU hxV
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hxU
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hxV
    have := hσ (hV hy) (hU hx) hxy
    subst this
    exact h hx hy

/-- A nonempty subset of the image of `U` is the image of a nonempty subset of `U`. -/
theorem exists_nePoly_image {U : Finset α} (t' : NePoly β) (ht' : t'.1 ⊆ U.image σ) :
    ∃ t : NePoly α, t.1 ⊆ U ∧ t.1.image σ = t'.1 := by
  classical
  have hne : (U.filter fun b => σ b ∈ t'.1).Nonempty := by
    obtain ⟨b', hb'⟩ := t'.2
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (ht' hb')
    exact ⟨b, Finset.mem_filter.2 ⟨hb, hb'⟩⟩
  refine ⟨⟨_, hne⟩, Finset.filter_subset _ _, ?_⟩
  ext b'
  constructor
  · intro hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    exact (Finset.mem_filter.1 hb).2
  · intro hb'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (ht' hb')
    exact Finset.mem_image_of_mem σ (Finset.mem_filter.2 ⟨hb, hb'⟩)

end ImageInj

/-! ### D4 (a): transport of the activities of the polymer gas -/

section PolyActTransport

variable {E E' B B' : Type*} [Fintype E] [Fintype E'] [DecidableEq B'] {cs : E → Finset B}
  {cs' : E' → Finset B'}

/-- **Transport of the activity of a polymer.**  Let `σ : B → B'` be injective on the polymer
`Y` with `Y′ = σ '' Y`, and let `φ : E → E′` map the objects supported in `Y` bijectively onto the
objects supported in `Y′`, with supports `cs′ (φ t) = σ '' cs t` and weights `w′ (φ t) = w t`.
Then the activities `∑_{C} ∏_{t ∈ C} w t` (connected families with union `Y`) agree:
`polyAct cs′ w′ Y′ = polyAct cs w Y`. -/
theorem polyAct_transport (σ : B → B') (φ : E → E') (Y : NePoly B) (Y' : NePoly B')
    (hY' : Y'.1 = Y.1.image σ) (hσ : Set.InjOn σ (Y.1 : Set B))
    (hφcs : ∀ t, cs t ⊆ Y.1 → cs' (φ t) = (cs t).image σ)
    (hφinj : ∀ t₁ t₂, cs t₁ ⊆ Y.1 → cs t₂ ⊆ Y.1 → φ t₁ = φ t₂ → t₁ = t₂)
    (hφsurj : ∀ t', cs' t' ⊆ Y'.1 → ∃ t, cs t ⊆ Y.1 ∧ φ t = t')
    (w : E → ℂ) (w' : E' → ℂ) (hw : ∀ t, cs t ⊆ Y.1 → w' (φ t) = w t) :
    polyAct cs' (fun _ => True) w' Y' = polyAct cs (fun _ => True) w Y := by
  classical
  unfold polyAct
  -- contacts inside `Y` are preserved and reflected
  have hcontact : ∀ a b, cs a ⊆ Y.1 → cs b ⊆ Y.1 →
      (Contact cs' (φ a) (φ b) ↔ Contact cs a b) := by
    intro a b ha hb
    unfold Contact
    rw [hφcs a ha, hφcs b hb, not_iff_not, Finset.disjoint_left, Finset.disjoint_left]
    constructor
    · intro h x hxa hxb
      exact h (Finset.mem_image_of_mem σ hxa) (Finset.mem_image_of_mem σ hxb)
    · intro h x' hxa hxb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hxa
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hxb
      have := hσ (hb hy) (ha hx) hxy
      subst this
      exact h hx hy
  have hunion : ∀ C : Finset E, (∀ t ∈ C, cs t ⊆ Y.1) →
      unionCs cs' (C.image φ) = (unionCs cs C).image σ := by
    intro C hC
    ext b'
    rw [mem_unionCs, Finset.mem_image]
    constructor
    · rintro ⟨t', ht', hb'⟩
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ht'
      rw [hφcs t (hC t ht)] at hb'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
      exact ⟨b, mem_unionCs.2 ⟨t, ht, hb⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨t, ht, hbt⟩ := mem_unionCs.1 hb
      refine ⟨φ t, Finset.mem_image_of_mem φ ht, ?_⟩
      rw [hφcs t (hC t ht)]
      exact Finset.mem_image_of_mem σ hbt
  have himg_inj : ∀ U ⊆ Y.1, ∀ V ⊆ Y.1, U.image σ = V.image σ → U = V := by
    intro U hU V hV h
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (h ▸ Finset.mem_image_of_mem σ hx)
      rw [hσ (hV hy) (hU hx) hyx] at hy
      exact hy
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (h.symm ▸ Finset.mem_image_of_mem σ hx)
      rw [hσ (hU hy) (hV hx) hyx] at hy
      exact hy
  symm
  refine Finset.sum_bij (fun C _ => C.image φ) (fun C hC => ?_) (fun C₁ hC₁ C₂ hC₂ h => ?_)
    (fun C' hC' => ?_) (fun C hC => ?_)
  · -- the image family is admissible
    have hsub : ∀ t ∈ C, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC ht
    obtain ⟨⟨hne, hreach⟩, -, hU⟩ := mem_Cfam.1 hC
    refine mem_Cfam.2 ⟨⟨hne.image φ, fun s hs s' hs' => ?_⟩, trivial, ?_⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hs'
      refine Relation.ReflTransGen.lift φ (fun x y hxy => ?_) _ _ (hreach a ha b hb)
      exact ⟨Finset.mem_image_of_mem φ hxy.1, Finset.mem_image_of_mem φ hxy.2.1,
        (hcontact x y (hsub x hxy.1) (hsub y hxy.2.1)).2 hxy.2.2⟩
    · rw [hunion C hsub, hU, hY']
  · -- injectivity
    have hs1 : ∀ t ∈ C₁, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC₁ ht
    have hs2 : ∀ t ∈ C₂, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC₂ ht
    ext t
    constructor
    · intro ht
      obtain ⟨t₂, ht₂, he⟩ := Finset.mem_image.1 (h ▸ Finset.mem_image_of_mem φ ht)
      rw [hφinj t₂ t (hs2 t₂ ht₂) (hs1 t ht) he] at ht₂
      exact ht₂
    · intro ht
      obtain ⟨t₁, ht₁, he⟩ := Finset.mem_image.1 (h.symm ▸ Finset.mem_image_of_mem φ ht)
      rw [hφinj t₁ t (hs1 t₁ ht₁) (hs2 t ht) he] at ht₁
      exact ht₁
  · -- surjectivity
    have hsub' : ∀ t' ∈ C', cs' t' ⊆ Y'.1 := fun t' ht' => sub_of_mem_Cfam hC' ht'
    obtain ⟨⟨hne', hreach'⟩, -, hU'⟩ := mem_Cfam.1 hC'
    let C : Finset E := Finset.univ.filter fun t => cs t ⊆ Y.1 ∧ φ t ∈ C'
    have hCsub : ∀ t ∈ C, cs t ⊆ Y.1 := fun t ht => (Finset.mem_filter.1 ht).2.1
    have himg : C.image φ = C' := by
      ext t'
      constructor
      · intro ht'
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ht'
        exact (Finset.mem_filter.1 ht).2.2
      · intro ht'
        obtain ⟨t, ht, rfl⟩ := hφsurj t' (hsub' t' ht')
        exact Finset.mem_image_of_mem φ (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht, ht'⟩)
    have hreachC : ∀ s₁ ∈ C, ∀ x', Reach cs' C' (φ s₁) x' →
        ∃ s ∈ C, φ s = x' ∧ Reach cs C s₁ s := by
      intro s₁ hs₁ x' h
      induction h with
      | refl => exact ⟨s₁, hs₁, rfl, Reach.refl cs _ _⟩
      | tail _ hyz ih =>
        obtain ⟨s, hs, rfl, hr⟩ := ih
        obtain ⟨-, hz', hcon⟩ := hyz
        obtain ⟨u, hu, rfl⟩ := hφsurj _ (hsub' _ hz')
        have huC : u ∈ C := Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, hz'⟩
        exact ⟨u, huC, rfl, hr.trans cs (Reach.single cs hs huC
          ((hcontact s u (hCsub s hs) hu).1 hcon))⟩
    refine ⟨C, mem_Cfam.2 ⟨⟨?_, fun s hs s' hs' => ?_⟩, trivial, ?_⟩, himg⟩
    · obtain ⟨t', ht'⟩ := hne'
      obtain ⟨t, ht, rfl⟩ := hφsurj t' (hsub' t' ht')
      exact ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, ht, ht'⟩⟩
    · obtain ⟨u, hu, he, hr⟩ := hreachC s hs (φ s') (hreach' _ (Finset.mem_filter.1 hs).2.2 _
        (Finset.mem_filter.1 hs').2.2)
      rw [hφinj u s' (hCsub u hu) (hCsub s' hs') he] at hr
      exact hr
    · refine himg_inj _ (fun x hx => ?_) _ le_rfl ?_
      · obtain ⟨t, ht, hxt⟩ := mem_unionCs.1 hx
        exact hCsub t ht hxt
      · rw [← hunion C hCsub, himg, hU', hY']
  · -- the weights
    have hsub : ∀ t ∈ C, cs t ⊆ Y.1 := fun t ht => sub_of_mem_Cfam hC ht
    rw [Finset.prod_image (fun t₁ h₁ t₂ h₂ h => hφinj t₁ t₂ (hsub t₁ h₁) (hsub t₂ h₂) h)]
    exact Finset.prod_congr rfl (fun t ht => (hw t (hsub t ht)).symm)

end PolyActTransport

/-! ### D4 (b): transport of the local terms of the marked cluster expansion -/

section GstTransport

open MeasureTheory

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {m₀ j : ℕ}
  {Ω : Set (CTorus d L N₁ m₁ K)} {Ω' : Set (CTorus d L N₁' m₁ K)}
  {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω
local notation "𝔅'" => CubeB (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) m₀ j Ω'

/-- The pre-summed term of a polymer depends only on its blocks when each activity depends only
on the blocks of its label. -/
theorem presum_depOn {Ωb : 𝔅 → Type*} (Lab : CubeLabels m₀ j Ω Lb)
    {H : Lb → (∀ b, Ωb b) → ℂ} (hHdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y))
    (t : NePoly 𝔅) : DepOn t.1 (presum Lab H t) := by
  intro Φ Φ' h
  unfold presum
  refine Finset.sum_congr rfl fun y hy => ?_
  have hyS : blocksOf m₀ j Ω (Lab.ysite y) = t.1 := (Finset.mem_filter.1 hy).2
  exact hHdep y Φ Φ' (fun b hb => h b (hyS ▸ hb))

/-- **The local term of a mark outside `S` vanishes**: if the blocks `S₀` of the mark are not
contained in `S`, then `G*(S₀, S) = 0` (the local term does not depend on the mark). -/
theorem Gst_eq_zero_of_not_subset {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) {S₀ S : Finset 𝔅} (G : (∀ b, Ωb b) → ℂ) (h : ¬ S₀ ⊆ S) :
    Gst μ Lab H S₀ G S = 0 := by
  classical
  unfold Gst
  have hconst : Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
      (marksK μ Subtype.val (presum Lab H) (gMark S₀ G)) S =
      fun _ => Ff (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val
        (marksK μ Subtype.val (presum Lab H) (gMark S₀ G)) S 0 := by
    funext l
    unfold Ff
    refine PY_congr (shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅)) Subtype.val S
      (fun x hx => ?_)
    unfold marksK mayerK mayerAct polyAct
    refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
    refine Finset.sum_congr rfl (fun C hC => Finset.prod_congr rfl (fun t ht => ?_))
    have htS : t.1 ⊆ S := (sub_of_mem_Cfam hC ht).trans hx
    have hne : t.1 ≠ S₀ := fun he => h (he ▸ htS)
    simp [Hlam, gMark, hne]
  rw [hconst]
  simp [D1]

/-- **D4 (b): transport of the local term `G*(S₀, S)` of the marked cluster expansion.**  Let
`σ` map the blocks of the first system to those of the second, injectively on `S`, and let a
relation `Rel` between configurations of the two systems carry integrals of functions of the
blocks of `Z ⊆ S` to integrals of the corresponding functions (`hint`).  Let the labels `y` with
blocks in `S` correspond bijectively (`ψ`) to the labels `y′` with blocks in `σ '' S`, with
`blocks (ψ y) = σ '' blocks y`, and let the activities and the mark agree on related
configurations.  Then `G*(σ '' S₀, σ '' S)` of the second system equals `G*(S₀, S)` of the
first, for `S₀ ⊆ S`.  The polymers of the two cluster expansions inside `S` and `σ '' S`
correspond (`PY_transport`), and so do their connected families (`polyAct_transport`), the
labels of a polymer (`presum`) and the marks (`gMark`). -/
theorem Gst_transport {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb' b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀ j Ω' Lb')
    (H : Lb → (∀ b, Ωb b) → ℂ) (H' : Lb' → (∀ b, Ωb' b) → ℂ)
    (hHdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y))
    (σ : 𝔅 → 𝔅') (S : Finset 𝔅) (hσ : Set.InjOn σ (S : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (hint : ∀ Z ⊆ S, ∀ (F : (∀ b, Ωb b) → ℂ) (F' : (∀ b, Ωb' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (ψ : ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ S → Lb')
    (hψb : ∀ y hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hy₁ y₂ hy₂, ψ y₁ hy₁ = ψ y₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ S.image σ → ∃ y hy, ψ y hy = y')
    (hH : ∀ y hy, ∀ Φ Φ', Rel Φ Φ' → H' (ψ y hy) Φ' = H y Φ)
    {S₀ : Finset 𝔅} (hS₀ : S₀ ⊆ S) {G : (∀ b, Ωb b) → ℂ} {G' : (∀ b, Ωb' b) → ℂ}
    (hGdep : DepOn S₀ G) (hG : ∀ Φ Φ', Rel Φ Φ' → G' Φ' = G Φ) :
    Gst μ' Lab' H' (S₀.image σ) G' (S.image σ) = Gst μ Lab H S₀ G S := by
  classical
  -- the image of a polymer
  let img : NePoly 𝔅 → NePoly 𝔅' := fun t => ⟨t.1.image σ, t.2.image σ⟩
  have himg_inj : ∀ t₁ t₂ : NePoly 𝔅, t₁.1 ⊆ S → t₂.1 ⊆ S → img t₁ = img t₂ → t₁ = t₂ :=
    fun t₁ t₂ h₁ h₂ h => Subtype.ext (eq_of_image_eq_of_injOn hσ h₁ h₂ (congrArg Subtype.val h))
  -- the terms of the polymers agree on related configurations
  have hHlam : ∀ (l : Unit → ℂ) (t : NePoly 𝔅), t.1 ⊆ S → ∀ Φ Φ', Rel Φ Φ' →
      Hlam (presum Lab' H') (gMark (S₀.image σ) G') l (img t) Φ' =
        Hlam (presum Lab H) (gMark S₀ G) l t Φ := by
    intro l t htS Φ Φ' hR
    have hpre : presum Lab' H' (img t) Φ' = presum Lab H t Φ := by
      unfold presum
      symm
      have hyS : ∀ y ∈ Finset.univ.filter (fun y => blocksOf m₀ j Ω (Lab.ysite y) = t.1),
          blocksOf m₀ j Ω (Lab.ysite y) ⊆ S := fun y hy => (Finset.mem_filter.1 hy).2 ▸ htS
      refine Finset.sum_bij (fun y hy => ψ y (hyS y hy)) (fun y hy => ?_)
        (fun y₁ hy₁ y₂ hy₂ h => hψinj y₁ _ y₂ _ h) (fun y' hy' => ?_)
        (fun y hy => (hH y _ Φ Φ' hR).symm)
      · have hyt : blocksOf m₀ j Ω (Lab.ysite y) = t.1 := (Finset.mem_filter.1 hy).2
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        rw [hψb y _, hyt]
      · have h' : blocksOf m₀ j Ω' (Lab'.ysite y') = t.1.image σ := (Finset.mem_filter.1 hy').2
        obtain ⟨y, hyS', rfl⟩ := hψsurj y' (h' ▸ Finset.image_subset_image htS)
        have hyt : blocksOf m₀ j Ω (Lab.ysite y) = t.1 :=
          eq_of_image_eq_of_injOn hσ hyS' htS ((hψb y hyS').symm.trans h')
        exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hyt⟩, rfl⟩
    have hmark : gMark (S₀.image σ) G' () (img t) Φ' = gMark S₀ G () t Φ := by
      by_cases ht0 : t.1 = S₀
      · have h1 : (img t).1 = S₀.image σ := by
          show t.1.image σ = S₀.image σ
          rw [ht0]
        simp only [gMark, h1, ht0, ite_true]
        exact hG Φ Φ' hR
      · have h1 : (img t).1 ≠ S₀.image σ := fun he => ht0 (eq_of_image_eq_of_injOn hσ htS hS₀ he)
        simp only [gMark, h1, ht0, ite_false]
    simp only [Hlam, Finset.univ_unique, Finset.sum_singleton, hpre, hmark]
  -- the activities of the polymers inside `S` agree
  have hK : ∀ (l : Unit → ℂ) (x : NePoly 𝔅), x.1 ⊆ S →
      marksK μ' Subtype.val (presum Lab' H') (gMark (S₀.image σ) G') (img x) l =
        marksK μ Subtype.val (presum Lab H) (gMark S₀ G) x l := by
    intro l x hx
    unfold marksK mayerK
    refine hint x.1 hx _ _ (depOn_mayerAct (fun t => ?_) x) (fun Φ Φ' hR => ?_)
    · intro Φ₁ Φ₂ h12
      unfold Hlam
      rw [presum_depOn Lab hHdep t Φ₁ Φ₂ h12]
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => by rw [gMark_dep S₀ hGdep t Φ₁ Φ₂ h12])
    · unfold mayerAct
      refine polyAct_transport σ img x (img x) rfl (hσ.mono (by exact_mod_cast hx))
        (fun t _ => by rfl) (fun t₁ t₂ h₁ h₂ h => himg_inj t₁ t₂ (h₁.trans hx) (h₂.trans hx) h)
        (fun t' ht' => ?_) _ _ (fun t ht => ?_)
      · obtain ⟨t, htx, hte⟩ := exists_nePoly_image t' ht'
        exact ⟨t, htx, Subtype.ext hte⟩
      · show Complex.exp (Hlam (presum Lab' H') (gMark (S₀.image σ) G') l (img t) Φ') - 1 =
          Complex.exp (Hlam (presum Lab H) (gMark S₀ G) l t Φ) - 1
        rw [hHlam l t (ht.trans hx) Φ Φ' hR]
  -- the polymers inside `S` and `σ '' S`
  have hbij : Function.Bijective (fun x : {x : NePoly 𝔅 // x.1 ⊆ S} =>
      (⟨img x.1, Finset.image_subset_image x.2⟩ : {x' : NePoly 𝔅' // x'.1 ⊆ S.image σ})) := by
    refine ⟨fun x₁ x₂ h => Subtype.ext (himg_inj _ _ x₁.2 x₂.2 (congrArg Subtype.val h)),
      fun x' => ?_⟩
    obtain ⟨t, htS, hte⟩ := exists_nePoly_image x'.1 x'.2
    exact ⟨⟨t, htS⟩, Subtype.ext (Subtype.ext hte)⟩
  let Ψ := Equiv.ofBijective _ hbij
  unfold Gst
  congr 1
  funext l
  unfold Ff
  refine PY_transport (inc := shareBlock (Subtype.val : NePoly 𝔅 → Finset 𝔅))
    (inc' := shareBlock (Subtype.val : NePoly 𝔅' → Finset 𝔅'))
    (supp := Subtype.val) (supp' := Subtype.val) S (S.image σ) σ hσ
    (fun b' => by simp [Finset.mem_image]) Ψ (fun x b' => ?_) (fun x y => ?_) (fun x => ?_)
  · show b' ∈ x.1.1.image σ ↔ _
    exact Finset.mem_image
  · rw [lnk_shareBlock, lnk_shareBlock]
    exact not_disjoint_image_iff_of_injOn hσ x.2 y.2
  · exact hK l x.1 x.2

/-- **D4 (c): transport of the interpolation coefficient `gsumCoeff`.**  In the setting of
`Gst_transport` for the set `T` of blocks: let the activities `A(s)` (for `s ∈ [0,1]`) of the
corresponding labels agree on related configurations, and let the marks `i` whose label lies in
`T` correspond bijectively (`κ`) to the marks `i′` whose label lies in `σ '' T`, with labels
`y₀′ (κ i) = ψ (y₀ i)` and marks agreeing on related configurations.  Then
`gsumCoeff μ′ Lab′ A′ y₀′ G′ (σ '' T) = gsumCoeff μ Lab A y₀ G T`.  The marks outside `T` (and
outside `σ '' T`) contribute zero (`Gst_eq_zero_of_not_subset`); the others are transported by
`Gst_transport`. -/
theorem gsumCoeff_transport {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    {Ωb' : 𝔅' → Type*} [∀ b, MeasurableSpace (Ωb' b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (μ' : ∀ b, Measure (Ωb' b)) [∀ b, IsProbabilityMeasure (μ' b)]
    (Lab : CubeLabels m₀ j Ω Lb) (Lab' : CubeLabels m₀ j Ω' Lb')
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (A' : ℂ → LabelAct Lab' Ωb' εH' κH' κ0' Kc')
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (y0 : ι → Lb) (y0' : ι' → Lb')
    (G : ι → ℂ → (∀ b, Ωb b) → ℂ) (G' : ι' → ℂ → (∀ b, Ωb' b) → ℂ)
    (hGdep : ∀ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i u))
    (σ : 𝔅 → 𝔅') (T : Finset 𝔅) (hσ : Set.InjOn σ (T : Set 𝔅))
    (Rel : (∀ b, Ωb b) → (∀ b, Ωb' b) → Prop)
    (hint : ∀ Z ⊆ T, ∀ (F : (∀ b, Ωb b) → ℂ) (F' : (∀ b, Ωb' b) → ℂ), DepOn Z F →
      (∀ Φ Φ', Rel Φ Φ' → F' Φ' = F Φ) →
        ∫ Φ', F' Φ' ∂(Measure.pi μ') = ∫ Φ, F Φ ∂(Measure.pi μ))
    (ψ : ∀ y, blocksOf m₀ j Ω (Lab.ysite y) ⊆ T → Lb')
    (hψb : ∀ y hy, blocksOf m₀ j Ω' (Lab'.ysite (ψ y hy)) =
      (blocksOf m₀ j Ω (Lab.ysite y)).image σ)
    (hψinj : ∀ y₁ hy₁ y₂ hy₂, ψ y₁ hy₁ = ψ y₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', blocksOf m₀ j Ω' (Lab'.ysite y') ⊆ T.image σ → ∃ y hy, ψ y hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hy,
      ∀ Φ Φ', Rel Φ Φ' → (A' (s : ℂ)).H (ψ y hy) Φ' = (A (s : ℂ)).H y Φ)
    (κ : ∀ i, blocksOf m₀ j Ω (Lab.ysite (y0 i)) ⊆ T → ι')
    (hκ : ∀ i hi, y0' (κ i hi) = ψ (y0 i) hi)
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', blocksOf m₀ j Ω' (Lab'.ysite (y0' i')) ⊆ T.image σ → ∃ i hi, κ i hi = i')
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hi,
      ∀ Φ Φ', Rel Φ Φ' → G' (κ i hi) (s : ℂ) Φ' = G i (s : ℂ) Φ) :
    gsumCoeff μ' Lab' A' y0' G' (T.image σ) = gsumCoeff μ Lab A y0 G T := by
  classical
  unfold gsumCoeff
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  unfold Gsum
  rw [← Finset.sum_filter_of_ne (p := fun i' => blocksOf m₀ j Ω' (Lab'.ysite (y0' i')) ⊆ T.image σ)
    (fun i' _ h => by_contra fun hn => h (Gst_eq_zero_of_not_subset _ _ _ _ hn)),
    ← Finset.sum_filter_of_ne (p := fun i => blocksOf m₀ j Ω (Lab.ysite (y0 i)) ⊆ T)
    (fun i _ h => by_contra fun hn => h (Gst_eq_zero_of_not_subset _ _ _ _ hn))]
  symm
  refine Finset.sum_bij (fun i hi => κ i (Finset.mem_filter.1 hi).2) (fun i hi => ?_)
    (fun i₁ hi₁ i₂ hi₂ h => hκinj i₁ _ i₂ _ h) (fun i' hi' => ?_) (fun i hi => ?_)
  · have hiT := (Finset.mem_filter.1 hi).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [hκ i hiT, hψb _ hiT]
    exact Finset.image_subset_image hiT
  · obtain ⟨i, hiT, rfl⟩ := hκsurj i' (Finset.mem_filter.1 hi').2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hiT⟩, rfl⟩
  · have hiT := (Finset.mem_filter.1 hi).2
    show Gst μ Lab (A (s : ℂ)).H (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i (s : ℂ)) T =
      Gst μ' Lab' (A' (s : ℂ)).H (blocksOf m₀ j Ω' (Lab'.ysite (y0' (κ i hiT))))
        (G' (κ i hiT) (s : ℂ)) (T.image σ)
    rw [hκ i hiT, hψb _ hiT]
    exact (Gst_transport μ μ' Lab Lab' (A (s : ℂ)).H (A' (s : ℂ)).H (A (s : ℂ)).dep σ T hσ Rel
      hint ψ hψb hψinj hψsurj (hA s hs) hiT (hGdep i _) (hG s hs i hiT)).symm

end GstTransport

/-! ### D4 (d): the interpolation coefficient of the step on two tori -/

section StepCoef

open MeasureTheory Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
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
set_option hygiene false in
local notation "𝔅A" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ
set_option hygiene false in
local notation "𝔅B" => CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))

/-- **D4 (d): the interpolation coefficient of the step on two tori.**  `gsumCoeff_transport`
for the block measures `(S.blockSplit m₀ hp).μ` of the two steps, the correspondence `cubeMap` of
the blocks (base point `bm b`), a set `T` of blocks inside the box of radius `R`, and the relation
"agreement of the block variables at corresponding unit points of the box"; the integral
hypothesis of `gsumCoeff_transport` is `integral_blockSplit_twoTorus`.  What remains as hypotheses
are the correspondence of the labels with blocks in `T`, of their activities, and of the marks
(for the marks of the energy coefficient see `e1MarkGParamG_twoTorus`).  Margin:
`2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem gsumCoeff_blockSplit_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels m₀ (k + 1) Set.univ Lb) (Lab' : CubeLabels m₀ (k + 1) Set.univ Lb')
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (A' : ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kc')
    {ι ι' : Type*} [Fintype ι] [Fintype ι'] (y0 : ι → Lb) (y0' : ι' → Lb')
    (G : ι → ℂ → (∀ c, ((SA).blockSplit m₀ hp).Ωb c) → ℂ)
    (G' : ι' → ℂ → (∀ c, ((SB).blockSplit m₀ hp').Ωb c) → ℂ)
    (hGdep : ∀ i u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i))) (G i u))
    (T : Finset (𝔅A))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L m₀ m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (ψ : ∀ y, blocksOf m₀ (k + 1) Set.univ (Lab.ysite y) ⊆ T → Lb')
    (hψb : ∀ y hy, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (ψ y hy)) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite y)).image (σc))
    (hψinj : ∀ y₁ hy₁ y₂ hy₂, ψ y₁ hy₁ = ψ y₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite y') ⊆ T.image (σc) →
      ∃ y hy, ψ y hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hy,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) →
        (A' (s : ℂ)).H (ψ y hy) Φ' = (A (s : ℂ)).H y Φ)
    (κ : ∀ i, blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i)) ⊆ T → ι')
    (hκ : ∀ i hi, y0' (κ i hi) = ψ (y0 i) hi)
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (y0' i')) ⊆ T.image (σc) →
      ∃ i hi, κ i hi = i')
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hi,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf m₀ (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) →
        G' (κ i hi) (s : ℂ) Φ' = G i (s : ℂ) Φ) :
    gsumCoeff ((SB).blockSplit m₀ hp').μ Lab' A' y0' G' (T.image (σc)) =
      gsumCoeff ((SA).blockSplit m₀ hp).μ Lab A y0 G T := by
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hσ : Set.InjOn (σc) (T : Set (𝔅A)) := by
    intro b₁ hb₁ b₂ hb₂ h
    have hb₁R := hT b₁ hb₁ b₁.1 (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1)))
    have hb₂R := hT b₂ hb₂ b₂.1 (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1)))
    have h1 := congrArg Subtype.val h
    rw [cubeMap_val, cubeMap_val] at h1
    exact Subtype.ext (boxMap_inj (hm' := hm') hb₁R hb₂R h1)
  refine gsumCoeff_transport _ _ Lab Lab' A A' y0 y0' G G' hGdep (σc) T hσ _
    (fun Z hZ F F' hF hFF => ?_) ψ hψb hψinj hψsurj hA κ hκ hκinj hκsurj hG
  exact integral_blockSplit_twoTorus hN2 hk νS β p₁ δ hn hn' hGA hGB hp hp' Z
    (fun b hb => hT b (hZ hb)) hF hFF

end StepCoef

end Balaban.Polymer.TwoTorusStep
