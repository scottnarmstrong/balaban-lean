/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsFamilyPrefactor
public import Balaban.Inhabited.ObsPrefactorScale
public import Balaban.Fluctuation.RootSupportBridge

/-!
# The prefactor of the tower's observable terms in Root-F's form (blocker 7)

The tower's observable coefficients `mObs` of one step are bounded, in the explicit form of the
step identity, by `Co · e^{-(3/2) κ_dec dExt C}`, where `Co` is the explicit constant of the
observable family (`obs_B1_add_B2_le_prefactorG`).  This file proves, from the landed
estimates, the two facts that turn that bound into the per-term bound of Root-F,
`c₉ L^{-j((d-2)/2+δ)} exp(-κ |X| / (M L^j)^d)` at the birth scale `j = k + 1`:

* `obsRate_le_birthScale`: for every `c₉ > 0` and `0 < δ' < min (s (d-2)) ((d-2)/2)` there is a
  threshold `β₁` (chosen before the scale) such that for `β ≥ β₁` the explicit constant `Co`
  satisfies `Co ≤ c₉ L^{-(k+1)((d-2)/2+δ')}`;
* `mObs_rootF_of_rate`: a bound `‖f C‖ ≤ B e^{-lam dExt C}` on a set `C` of cubes whose sites form
  a polymer domain gives `‖f C‖ ≤ B e^{lam} exp(-κ |sitesOf C| / (L^{m₁+1} L^{k+1})^d)` as soon as
  `c₁ κ ≤ lam`; the number of sites of `C` is the number of fine sites of Root-F's polymer.

The constant `B` of `towerGapTerms_twoTorus_fromTowerG_core(_supp)` is the sum of `|K₀|`, the
determinant constant `Cdz` and `Co`; only `Co` decays in `β` and `k`, and the statements of those
cores do not export it.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

/-- The explicit constant of the observable family bound at the scale `b = β L^{k(d-2)}`
(the sum `B₁ + B₂` of `obs_B1_add_B2_le_prefactorG` with the entropy sum replaced by its bound). -/
theorem obsRate_le_prefactor_one {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 1 < b → ∀ p₁ : ℝ, 0 ≤ p₁ → p₁ ≤ pLog A₁ p b →
      (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t b) *
          (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * p₁ / obsRg CR s (p : ℝ) b) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
          ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (p₁ / lvCpsiG d L N T.κ T.t b) ^ 2 * (K0 d L T.κ0 + 1)) ≤
        C * obsPrefactor p s b := by
  obtain ⟨C, hC, H⟩ := obs_B1_add_B2_le_prefactorG T hA p hCR (s := s)
  refine ⟨C, hC, fun b hb p₁ hp0 hp₁ => ?_⟩
  have hK := K0_pos d L T.κ0
  have hκ0 : 0 < T.κ0 := by have := aEnt_nonneg d L; have := T.κ0_two; linarith
  have h := H b hb p₁ hp0 hp₁ Unit (fun _ => -Real.log (K0 d L T.κ0 + 1) / T.κ0) (by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    refine le_of_eq ?_
    congr 1
    have : -T.κ0 * (-Real.log (K0 d L T.κ0 + 1) / T.κ0) = Real.log (K0 d L T.κ0 + 1) := by
      field_simp
    rw [this, Real.exp_log (by linarith)])
  have hexp : Real.exp (-(T.κ0 * (-Real.log (K0 d L T.κ0 + 1) / T.κ0))) = K0 d L T.κ0 + 1 := by
    have : -(T.κ0 * (-Real.log (K0 d L T.κ0 + 1) / T.κ0)) = Real.log (K0 d L T.κ0 + 1) := by
      field_simp
    rw [this, Real.exp_log (by linarith)]
  simp only [Finset.univ_unique, Finset.sum_singleton, neg_mul, hexp] at h
  exact h

/-- **The observable constant at the birth scale.**  For every `c₉ > 0` and
`0 < δ' < min (s (d-2)) ((d-2)/2)` there is a threshold `β₁`, depending only on the tower and the
constants, such that for `β ≥ β₁`, every `k` and every `0 ≤ p₁ ≤ pLog A₁ p (β L^{k(d-2)})`, the
explicit constant `Co` of the observable family bound is at most
`c₉ L^{-(k+1)((d-2)/2+δ')}`. -/
theorem obsRate_le_birthScale {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) {c₉ δ' : ℝ} (hc₉ : 0 < c₉)
    (hδ0 : 0 < δ') (hδs : δ' < s * ((d : ℝ) - 2)) (hδd : δ' < ((d : ℝ) - 2) / 2) :
    ∃ β₁ : ℝ, 1 < β₁ ∧ ∀ (k : ℕ) (β : ℝ), β₁ ≤ β → ∀ p₁ : ℝ, 0 ≤ p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t /
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
              (K0 d L T.κ0 + 1)) ≤
        c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by
  obtain ⟨C, hC0, hC⟩ := obsRate_le_prefactor_one T hA p hCR (s := s)
  obtain ⟨C', hC'0, hC'⟩ := obsPrefactor_le_birth_scale p T.hd hδs hδd
  have hL2 : 2 ≤ L := by have := T.hL; omega
  have hL0 : (0 : ℝ) < L := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
    linarith
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast T.hd
    linarith
  obtain ⟨β₁, hβ₁, hβ₁c⟩ := birth_const_le_of_large (C := C * C') (c := c₉)
    (e := ((d : ℝ) - 2) / 2 + δ') (q := (((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2)) (L : ℝ) hL0 hc₉
    (div_pos (by positivity) hd2)
  refine ⟨max β₁ 2, lt_of_lt_of_le one_lt_two (le_max_right _ _), fun k β hβ p₁ hp0 hp₁ => ?_⟩
  have hββ₁ : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : 2 ≤ β := (le_max_right _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hb1 : 1 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) :=
      one_le_pow₀ (by have : (2 : ℝ) ≤ L := by exact_mod_cast hL2
                      linarith)
    nlinarith
  refine (hC _ hb1 p₁ hp0 hp₁).trans ?_
  have hpref := (hC' L k β hL2 (by linarith)).2
  have hbirth := hβ₁c β hββ₁
  have hP : 0 ≤ (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by positivity
  calc C * obsPrefactor p s (β * (L : ℝ) ^ (k * (d - 2)))
      ≤ C * ((C' * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ') *
            β ^ (-((((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2)))) *
          (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ')))) := by gcongr
    _ = (C * C') * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ') *
          β ^ (-((((d : ℝ) - 2) / 2 + δ') / ((d : ℝ) - 2))) *
          (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by ring
    _ ≤ c₉ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ'))) := by
        refine mul_le_mul_of_nonneg_right ?_ hP
        exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_abs_self _) (by positivity)) (by positivity)) hbirth

open Classical in
/-- **The tower's observable term in Root-F's shape.**  For a set `C` of cubes (cube index one,
scale `K`) whose sites form a polymer domain, a value `v` bounded by `Bo e^{-lam dExt C}` with
`Bo ≤ c L^{-K e}` and `c₁ κ ≤ lam` is bounded by
`(c e^{lam}) L^{-K e} exp(-κ |sitesOf C| / (L^{m₁+1} L^K)^d)`: the number of sites of `C` is the
number of fine sites of Root-F's polymer, and `L^{m₁+1} L^K = M L^j` at `j = K`. -/
theorem mObs_rootF_of_rate {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (hN : L ∣ N₁)
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ))
    (hpoly : IsPolyDom 1 K (sitesOf C)) {κ lam Bo c e : ℝ} (hκ : 0 < κ) (hlam : c1 d L * κ ≤ lam)
    (hBo0 : 0 ≤ Bo) (hBo : Bo ≤ c * (L : ℝ) ^ (-((K : ℝ) * e))) {v : ℂ}
    (hv : ‖v‖ ≤ Bo * Real.exp (-lam * dExt C)) :
    ‖v‖ ≤ (c * Real.exp lam) * (L : ℝ) ^ (-((K : ℝ) * e)) *
      Real.exp (-κ * ((Finset.univ.filter (· ∈ sitesOf C)).card : ℝ) /
        ((L ^ (m₁ + 1) * L ^ K : ℕ) : ℝ) ^ d) := by
  refine hv.trans ((Fluctuation.rootRate_of_dExt hN C hpoly hκ hlam hBo0).trans ?_)
  have hE : 0 ≤ Real.exp lam := (Real.exp_pos _).le
  have hX : 0 ≤ Real.exp (-κ * ((Finset.univ.filter (· ∈ sitesOf C)).card : ℝ) /
      ((L ^ (m₁ + 1) * L ^ K : ℕ) : ℝ) ^ d) := (Real.exp_pos _).le
  calc Bo * Real.exp lam * _ ≤ (c * (L : ℝ) ^ (-((K : ℝ) * e))) * Real.exp lam * _ := by gcongr
    _ = _ := by ring

end Balaban.Inhabited
