/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ScaleActivityFinal
public import Balaban.Inhabited.DetStepScaleG
public import Balaban.Inhabited.DetOutputTermsWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The activity bound and the localized determinant family at every scale, with common constants

`stepActivityBound_zeroClass_direct_physical_scale_cutoff` (`ScaleActivityFinal`) gives the
label-activity bound of the zero class at the step `hatStepK k m₁ hk ν β p₁ δ` of every scale and
every torus, with `m₁, t, δ, β₀, C` fixed before `k`, `N₁`, `ν`.  Its statement concerns the
interaction part of the step only and does not mention the determinant.
`detExpansionLocC_scale` (`DetOutputTermsWitness`) gives the localized determinant family at the
same steps.  Each of the two statements asserts the existence of its own `m₁` and `t`.

`stepActivityBound_detExpansionLocC_scale` is the joint statement: one choice of
`m₁, t, δ, β₀, C, BG, κ` serves both.  For every scale `k ≥ 1`, torus `3 ∣ N₁`, `5 < N₁`, mass
`0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, coupling `β ≥ β₀` and cutoff `0 < p₁ ≤ A₁ (log β_k)^p`:

* the zero class has a step activity bound with `κ_H = 2 κ_dec - 1` and prefactor at most
  `C (log β_k)^{3p} / √β_k` (the landed conclusion, word for word);
* the datum of the step is a datum of the chart `Ξ^c(𝔹_{k+1}; 1, t)`, and for every root `z` the
  record `DetExpansionLocC` has an element whose terms are the sums of the activities
  `detActivityBg`, with the rate `(κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18 ≥ κ'` and the constant
  `27 · covBLogMax 3 3 κ / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)`.

The interaction prefactor tends to `0` as `β → ∞`; the determinant constant does not depend on
`β` and is at least `1` (`one_le_detConstMax_three`).  Neither depends on `k`, `N₁`, `ν`.

The theorem is the case `d = L = 3`, `N = 2` of `stepActivityBound_detExpansionLocC_scale_general`
(`DetStepScaleG`), which carries the proof.

Not proved: marks for `ℰ₁` (`E1MarksC`), so Theorem 3.1 (a) is not instantiated at these steps;
the comparison of the determinant constant with an energy constant of a class; general classes.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The zero-class activity bound and the localized determinant family at every scale and on
every torus, with common constants.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`,
`κ' = (3/2) κ_dec + κ₀ + 1`: there are `m₁, t, δ, β₀, C, BG, κ` (`β₀ ≥ 2`, `C > 0`) with
`e^κ > 2 (detDeg 3 3 + 1)²` and `κ' ≤ (κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18` such that for
every scale `k ≥ 1`, every torus parameter `N₁` with `3 ∣ N₁`, `5 < N₁`, every mass `0 < ν` with
`ν · 3^{2(k+1)} ≤ 1`, every `β ≥ β₀` and every cutoff `0 < p₁ ≤ A₁ (log β_k)^p`, `β_k = β · 3^k`,
at the step `hatStepK k m₁ hk ν β p₁ δ`:

* the zero class has a step activity bound with `κ_H = 2 κ_dec - 1` and prefactor at most
  `C (log β_k)^{3p}/√β_k`, and the rate relations of the landed theorem hold;
* the datum of the step is a datum of the chart `Ξ^c(𝔹_{k+1}; 1, t)`;
* for every `z` the record `DetExpansionLocC` has an element whose term at `(D, T)` is
  `∑_{y ∈ B(z)} detActivityBg D y T`, with the rate `(κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18`
  and the constant `27 · covBLogMax 3 3 κ / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)`.

The constants do not depend on `k`, `N₁`, `ν`; the determinant rate and constant do not depend on
`β` either. -/
theorem stepActivityBound_detExpansionLocC_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10))
    (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t δ β₀ C BG κ : ℝ), 2 ≤ β₀ ∧ 0 < C ∧ 0 < t ∧ 0 < δ ∧
      ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
      κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
        (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        (∃ B : StepActivityBound (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
            (zeroClass 3 3 N₁ m₁ k 2 (rhoSep m₁)) 0,
          B.κH = 2 * κdec - 1 ∧
          B.εH ≤ C * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) ∧
          κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ 2 * κdec - 1 ∧
          ∃ κout : ℝ, κout = 3 / 2 * κdec ∧ κdec ≤ κout ∧ κout ≤ min κ' κ' - κ0 - 1) ∧
        XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
            (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' ∧
          ∀ z, ∃ E : DetExpansionLocC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 z t
              ((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
                (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)))
              (((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
            ∀ D T, E.term D T = ∑ y ∈ (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).blockU z,
              detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 BG κ) D y T := by
  obtain ⟨m₁, t, δ, β₀, C, BG, κ, hβ₀, hC, ht, hδ, hz, hrate, h⟩ :=
    stepActivityBound_detExpansionLocC_scale_general (d := 3) (L := 3) (N := 2) (by norm_num)
      (by norm_num) le_rfl hA p hκ0def hκdecdef hκ'def
  refine ⟨m₁, t, δ, β₀, C, BG, κ, hβ₀, hC, ht, hδ, hz, hrate, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  obtain ⟨hact, hD, hdet⟩ := h k hk N₁ h3N hN ν hνpos (by simpa using hν) β hβ p₁ hp0
    (by rw [e]; exact hp₁)
  rw [rhoSepG_three] at hact hD hdet
  rw [e] at hact
  exact ⟨hact, hD, hdet⟩

end Balaban.Inhabited
