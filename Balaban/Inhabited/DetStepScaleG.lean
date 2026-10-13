/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ScaleActivityFinalG
public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Fluctuation.DetRateGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The activity bound and the localized determinant family at every scale, general `d`, `L`, `N`

`stepActivityBound_detExpansionLocC_scale_general` is the joint statement of `DetStepScale` for
general `d, L ≥ 3`, `N ≥ 2`: one choice of `m₁, t, δ, β₀, C, BG, κ` serves the zero-class activity
bound of `stepActivityBound_zeroClass_direct_physical_scale_cutoff_tower_general` and the
localized determinant family `detExpansionLocC_scale_of_towerG`, both at the step `hatStepKG` of
every scale `k ≥ 1` and every torus `L ∣ N₁`, `5 < N₁`.  The rate floor of the tower is
`2 d L κ' + log 2 + 2 log (detDeg d L + 1) + 1`, which gives the determinant rate condition and
the determinant rate at least `κ'`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

open Classical in
/-- **The zero-class activity bound and the localized determinant family at every scale and on
every torus, general `d`, `L`, `N`, with common constants.**  With `κ₀ = a_Ent + 1`,
`κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1`: there are
`m₁, t, δ, β₀, C, BG, κ` (`β₀ ≥ 2`, `C > 0`) with `e^κ > 2 (detDeg d L + 1)²` and
`κ' ≤ (κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` such that for every scale `k ≥ 1`, every
`N₁` with `L ∣ N₁`, `5 < N₁`, every mass `0 < ν` with `ν · L^{2(k+1)} ≤ 1`, every `β ≥ β₀` and
every cutoff `0 < p₁ ≤ A₁ (log b)^p`, `b = β L^{k(d-2)}`, at the step
`hatStepKG k m₁ (rhoSepG d L m₁) hk ν β p₁ δ`: the zero class has a step activity bound with
`κ_H = 2 κ_dec - 1` and prefactor at most `C (log b)^{3p}/√b`; the datum of the step is a datum of
the chart `Ξ^c(𝔹_{k+1}; 1, t)`; for every `z` the record `DetExpansionLocC` has an element whose
term at `(D, T)` is `∑_{y ∈ B(z)} detActivityBg D y T`, with the rate
`(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` and the constant
`L^d · ½ N covBLogMax d L κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`. -/
theorem stepActivityBound_detExpansionLocC_scale_general {d L N : ℕ} [NeZero L]
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt d L + 1) (hκdecdef : κdec = 100 * (κ0 + c1 d L + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C BG κ : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
      κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        (∃ B : StepActivityBound
            (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ)
            (zeroClass d L N₁ m₁ k N (rhoSepG d L m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
          κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1) ∧
        XiCData (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ).G'
            (compWeight L 1) ν (k + 1) 1 t
            (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ).D' ∧
          ∀ z, ∃ E : DetExpansionLocC
              (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β p₁ δ) 1 z t
              ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
              ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L κ /
                (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
            ∀ D T, E.term D T =
              ∑ y ∈ (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ (rhoSepG d L m₁) hk ν β
                p₁ δ).blockU z,
              detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N BG κ) D y T := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hc1 := one_le_c1 d L
  have hent := aEnt_nonneg d L
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def, hκdecdef]; nlinarith
  obtain ⟨m₁, t, δ, β₀, C, c, BG, κ, c₂, BG₂, δc, hβ₀, hC, ht, hδ, h4, hCn, hmin, hMX, hdm, hα,
    hsmX, h⟩ :=
    stepActivityBound_zeroClass_direct_physical_scale_cutoff_tower_general hd hL hN
      (2 * d * L * κ' + (Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) + 1) hA p hκ0def
      hκdecdef hκ'def
  obtain ⟨hC₀⟩ := hCn
  have hDk : Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) < κ := by
    have : 0 ≤ 2 * (d : ℝ) * L * κ' := by positivity
    linarith
  have hz := detDeg_rate_general d L hDk
  have hrate : κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
      (2 * (d : ℝ) * (L : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine ⟨m₁, t, δ, β₀, C, BG, κ, hβ₀, hC, ht, hδ, hz, hrate, ?_⟩
  intro k hk N₁ _ hLN hN₁ ν hνpos hν β hβ p₁ hp0 hp₁
  exact ⟨h k hk N₁ hLN hN₁ ν hνpos hν β hβ p₁ hp0 hp₁,
    detExpansionLocC_scale_of_towerG hd hL hN h4 ht hC₀ hMX hdm hα hsmX hz k hk N₁ hLN hN₁
      hνpos.le hν β p₁ δ⟩

end Balaban.Inhabited
