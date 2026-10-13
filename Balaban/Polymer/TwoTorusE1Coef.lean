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

end Balaban.Polymer.TwoTorusStep
