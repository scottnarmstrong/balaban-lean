/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerRootFBound
public import Balaban.Polymer.TwoTorusGapTowerRootFSuppTower

/-!
# The tower's observable terms in Root-F's bound form (blocker 7)

`towerGapScale_resum_fromTowerG_supp_obs` (and the core
`towerGapTerms_twoTorus_fromTowerG_core_supp_obs`) export the separate bound
`‖mObs y i θ C‖ ≤ Co e^{-(3/2) κ_dec dExt C}` with the explicit constant `Co`.  This file combines it
with `obsRate_le_birthScale` and `mObs_rootF_of_rate`.

* `mObs_rootF_of_obsBound`: for every `c₉ > 0` and `0 < δ' < min (s (d-2)) ((d-2)/2)` there is a
  threshold `β₁` such that, for `β ≥ β₁`, every `k` and every `0 ≤ p₁ ≤ pLog A₁ p (β L^{k(d-2)})`,
  a value `v` with `‖v‖ ≤ Co e^{-(3/2) κ_dec dExt C}`, `Co` the explicit constant of the cores,
  on a set `C` of cubes (scale `k + 1`) whose sites form a polymer domain, satisfies Root-F's bound
  `‖v‖ ≤ (c₉ e^{(3/2) κ_dec}) L^{-(k+1)((d-2)/2+δ')} exp(-κ |sitesOf C| / (L^{m₁+1} L^{k+1})^d)`
  with `κ = (3/2) κ_dec / c₁`.
* `towerGapScale_mObs_rootF`: the same for the witnesses `mObs` of
  `towerGapScale_resum_fromTowerG_supp_obs` at `θ ∈ physVq`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited
  Balaban.Inhabited.LevelStep

open Classical in
/-- **The observable bound of the cores in Root-F's form.**  See the module header. -/
theorem mObs_rootF_of_obsBound {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) {c₉ δ' : ℝ} (hc₉ : 0 < c₉)
    (hδ0 : 0 < δ') (hδs : δ' < s * ((d : ℝ) - 2)) (hδd : δ' < ((d : ℝ) - 2) / 2) :
    ∃ β₁ : ℝ, 1 < β₁ ∧ ∀ (k : ℕ) (β : ℝ), β₁ ≤ β → ∀ p₁ : ℝ, 0 ≤ p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ {Co : ℝ},
      Co = (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t /
            lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * p₁ / obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
          ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 *
              (K0 d L T.κ0 + 1)) →
      ∀ {n : ℕ} [NeZero n] (_ : L ∣ n)
        (C : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ)),
        IsPolyDom 1 (k + 1) (sitesOf C) → ∀ {v : ℂ},
        ‖v‖ ≤ Co * Real.exp (-(3 / 2 * T.κdec) * dExt C) →
        ‖v‖ ≤ (c₉ * Real.exp (3 / 2 * T.κdec)) *
            (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) *
          Real.exp (-((3 / 2 * T.κdec) / c1 d L) *
            ((Finset.univ.filter (· ∈ sitesOf C)).card : ℝ) /
            ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d) := by
  obtain ⟨β₁, hβ₁, H⟩ := obsRate_le_birthScale T hA p hCR hc₉ hδ0 hδs hδd
  refine ⟨β₁, hβ₁, fun k β hβ p₁ hp0 hp₁ Co hCo n _ hN C hpoly v hv => ?_⟩
  have hbound := H k β hβ p₁ hp0 hp₁
  rw [← hCo] at hbound
  have hCo0 : 0 ≤ Co := by
    have h0 : 0 ≤ Co * Real.exp (-(3 / 2 * T.κdec) * dExt C) := (norm_nonneg v).trans hv
    exact nonneg_of_mul_nonneg_left h0 (Real.exp_pos _)
  have hc1 : 0 < c1 d L := by
    have := T.hL
    unfold c1
    exact pow_pos (by exact_mod_cast (by omega : 0 < 3 * (2 * L - 1))) d
  have hκ : 0 < (3 / 2 * T.κdec) / c1 d L := by
    have := T.κdec_lower; have := T.κ0_nonneg
    exact div_pos (by linarith) hc1
  exact mObs_rootF_of_rate hN C hpoly hκ (le_of_eq (by field_simp)) hCo0 hbound hv

open Classical in
/-- **The tower's observable terms in Root-F's form.**  The witnesses `mObs` of
`towerGapScale_resum_fromTowerG_supp_obs`, at `θ ∈ physVq`, satisfy Root-F's per-term bound on every
set of cubes carrying a nonzero value. -/
theorem towerGapScale_mObs_rootF {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) {c₉ δ' : ℝ} (hc₉ : 0 < c₉)
    (hδ0 : 0 < δ') (hδs : δ' < s * ((d : ℝ) - 2)) (hδd : δ' < ((d : ℝ) - 2) / 2) :
    ∃ (β₀ : ℝ), 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (ν : ℝ) (_ : 0 < ν) (_ : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ)
        (_ : β₀ ≤ β) (p₁ : ℝ) (_ : 0 < p₁) (_ : p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))))
        (q : ℝ) (_ : 0 < q) (_ : q ≤ 1),
      ∃ mObs : ∀ (n : ℕ) [NeZero n], L ^ T.m₀ ∣ n → 5 < n →
          StepScaleDataG T k hk n ν β p₁ → CTorus d L n T.m₁ (k + 1) → Fin N →
          physParam N (StepTowerG.step T k hk n ν β p₁) →
          Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ,
        ∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n)
          (Dn : StepScaleDataG T k hk n ν β p₁) (y : CTorus d L n T.m₁ (k + 1)) (i : Fin N)
          (C : Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ)),
          ∀ θ ∈ physVq (StepTowerG.step T k hk n ν β p₁) (StepTowerG.step T k hk n ν β p₁).a₁
            (StepTowerG.step T k hk n ν β p₁).ν T.t q, mObs n h3 h5' Dn y i θ C ≠ 0 →
          ‖mObs n h3 h5' Dn y i θ C‖ ≤ (c₉ * Real.exp (3 / 2 * T.κdec)) *
              (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) *
            Real.exp (-((3 / 2 * T.κdec) / c1 d L) *
              ((Finset.univ.filter (· ∈ sitesOf C)).card : ℝ) /
              ((L ^ (T.m₁ + 1) * L ^ (k + 1) : ℕ) : ℝ) ^ d) := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    towerGapTerms_twoTorus_fromTowerG_core_supp_obs.{0, 0, 0, 0} T hm₀ hhull hA p hCR hs0 hs
  obtain ⟨β₁, hβ₁, H₁⟩ := mObs_rootF_of_obsBound T hA p hCR hc₉ hδ0 hδs hδd
  refine ⟨max β₀ β₁, (h3.trans (le_max_left _ _)), fun k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1 => ?_⟩
  obtain ⟨e0, dz, c, mObs, B, Co, -, hCo, -, hS, hobs, -⟩ :=
    H k hk ν hν0 hν β ((le_max_left _ _).trans hβ) p₁ hp0 hp₁ q hq0 hq1
  refine ⟨mObs, fun n _ h3n h5' Dn y i C θ hθ hne => ?_⟩
  have hN : L ∣ n := by have := h3n; rwa [hm₀, pow_one] at this
  exact H₁ k β ((le_max_right _ _).trans hβ) p₁ hp0.le hp₁ hCo hN C
    (hS n h3n h5' Dn y i θ hθ C hne) (hobs n h3n h5' Dn y i C θ hθ)

end Balaban.Polymer.TwoTorusStep
