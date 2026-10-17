/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassBirth
public import Balaban.SmallField.XiMassResponseXi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Birth-mass domains of the old terms: the inclusion with the mass response discharged

`xiDom_birth_of_massResponse` (`LocalClassBirth.lean`) takes the level-`j` mass response of
`Ξ^c_j(·; 1, ·)` as a hypothesis.  Here it is supplied by `xiC_massResponse`
(`SmallField/XiMassResponseXi.lean`) for the datum at hand:

* `xiDom_birth`: a chart point of scale `C₀` at the step mass `ν` lies in the birth-mass domain
  `XiDom` at the mass `μ = ν (1 + t)` with the radius `ε_j`, when `e₁ (1 + K_m |t|) ≤ ε_j`,
  `K_m = 1 + 16 (N + 1) K₂`.  The extra premise `hk` is the top-level norm clause
  `ν L^{2k} | |h₀|² - 1 | < e₁²` (D1-top of `notes/phase1/MASS-LEVEL.md`) for the real witness
  `h₀` of the datum; it holds for `j = k`, for `ν = 0` and for a unit witness `|h₀| = 1`
  (`xiDom_birth_of_unit`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The chart points of scale `C₀` lie in the birth-mass domain** (decision D2(b)):
`xiDom_birth_of_massResponse` with the mass response `xiC_massResponse` for the datum `D`. -/
theorem xiDom_birth {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ C₀ e e₁ εj t r : ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (hσ : 1 ≤ C₀) (hrad : C₀ ^ 2 * e ≤ e₁)
    (hε : 0 < e₁) (hsm : (4 * d + 6) * ((2 * d + 1) * e₁) ≤ 1)
    (hc1 : 4 * (xiC1 d * e₁) ≤ bgC1 d L N) (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1)
    (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * e₁) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * e₁ * r ≤ deltaStar d L N)
    (hee : e₁ * (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t|) ≤ εj)
    {D : BgData G N} (hD : Localization.XiCData G A ν j C₀ e D)
    (hk : ∀ h₀ : Fin N → ℝ, (∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
        XiC G A ν j C₀ e Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'') →
      ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * e₁) ^ 2) :
    Def6.XiDom G A μ j εj D.Ψ D.h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hxc, hR⟩ := hD
  have hk' := hk h₀ ⟨Ψ₀, Ψ'', h'', hxc, hR⟩
  refine ⟨Ψ₀, h₀, fun x i => D.Ψ x i - Ψ₀ x i, fun x i => D.h x i - h₀ i,
    fun x i => by ring, fun x i => by ring,
    Def6v2.xiC_mono_eps zero_le_one hee
      (xiC_massResponse H H' hε hsm hc1 hμ ht1 htr hr hK hζ hk'
        (xiC_rescale_of_agree hσ hrad (fun x hx i => ?_) (fun x hx i => ?_) hxc))⟩
  · rw [hR.1 x hx i]; ring
  · rw [hR.2 x hx i]; ring

/-- `xiDom_birth` for unit real witnesses `|h₀| = 1`: the top-level norm clause is trivial. -/
theorem xiDom_birth_of_unit {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ C₀ e e₁ εj t r : ℝ} {j : ℕ} (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (hσ : 1 ≤ C₀) (hrad : C₀ ^ 2 * e ≤ e₁)
    (hε : 0 < e₁) (hsm : (4 * d + 6) * ((2 * d + 1) * e₁) ≤ 1)
    (hc1 : 4 * (xiC1 d * e₁) ≤ bgC1 d L N) (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1)
    (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * e₁) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * e₁ * r ≤ deltaStar d L N)
    (hee : e₁ * (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t|) ≤ εj)
    {D : BgData G N} (hD : Localization.XiCData G A ν j C₀ e D)
    (hunit : ∀ h₀ : Fin N → ℝ, (∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ)
        (Ψ'' h'' : Localization.CTorus d L N₁ m₁ k → Fin N → ℂ),
        XiC G A ν j C₀ e Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h'') →
      ∑ i, h₀ i ^ 2 = 1) :
    Def6.XiDom G A μ j εj D.Ψ D.h :=
  xiDom_birth H H' hσ hrad hε hsm hc1 hμ ht1 htr hr hK hζ hee hD fun h₀ hh => by
    rw [hunit h₀ hh]; simpa using by positivity

/-- `xiDom_birth` at the top level `j = k`: the norm clause is part of the level-`k` class
(`ν L^{2k} | |h₀|² - 1 | < (C₀ e)² ≤ e₁²`). -/
theorem xiDom_birth_top {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {A : ℕ → ℝ}
    {ν μ C₀ e e₁ εj t r : ℝ} (H : BgHyp d L k ϱ A ν) (H' : BgHyp d L k ϱ A μ)
    (hσ : 1 ≤ C₀) (he : 0 < e) (hrad : C₀ ^ 2 * e ≤ e₁)
    (hε : 0 < e₁) (hsm : (4 * d + 6) * ((2 * d + 1) * e₁) ≤ 1)
    (hc1 : 4 * (xiC1 d * e₁) ≤ bgC1 d L N) (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1)
    (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * e₁) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * e₁ * r ≤ deltaStar d L N)
    (hee : e₁ * (1 + (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * |t|) ≤ εj)
    {D : BgData G N} (hD : Localization.XiCData G A ν k C₀ e D) :
    Def6.XiDom G A μ k εj D.Ψ D.h :=
  xiDom_birth H H' hσ hrad hε hsm hc1 hμ ht1 htr hr hK hζ hee hD fun h₀ hh => by
    obtain ⟨Ψ₀, Ψ'', h'', hxc, -⟩ := hh
    obtain ⟨hσ0, hε0, Dr, Dc, ⟨-, -, hbr⟩, -⟩ := hxc
    have h2 : C₀ * e ≤ 1 * e₁ := by nlinarith
    exact hbr.hnorm.trans_le (pow_le_pow_left₀ (by positivity) h2 2)

end Balaban.Fluctuation
