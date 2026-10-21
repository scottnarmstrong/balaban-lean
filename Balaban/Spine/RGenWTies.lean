/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs

/-!
# The constants of the decoupled theory on the generating sets of `R`

The decoupled background fields of the localization expansion of the residual of `R` (P7
(3.22)–(3.25), P3 §4) are taken on the small-field generating sets `𝔹_k(W)` of the step,
transported to the Def-6 torus `CTorus d L N₁ m₁ k` (`SFCtx.genWC`).  Their standing hypotheses
`DGSetting` (`SFCtx.dgSetting_genWC`) need four conditions on the constants of the prefix that
`PrefixInput` does not contain:

* `L^{m₁} ∣ M₁` (the cover cubes of side `L^{j+m₁}` refine the cubes `𝒞_j` of side `L^j M₁` of the
  minimal generating sets), `2 ≤ m₁`;
* `4 L² ≤ L^{m₁}`;
* `4 d L^{m₁} ≤ 5 M₁` (the separation `5 L M₁` dominates the cover size);
* `2 d log L ≤ (agmonRate d / 16) (5 L M₁ - 1)` (Agmon separation).

`PrefixInput` has `M = c M₁ = L^{m₀ + m₁}`, `c ≥ 14` and `R₀(d, L) ≤ 5 L M₁`; the last is the
background theory's separation, which is weaker than the Agmon separation here.

* `RGenWTies`: the four conditions for every `κ, c₉ > 0`;
* `rGenWTies_of_pow`, `rGenWTies_of_choice`: at the choice of the prefix witness
  (`prefixInput_exists_of`: `c = L³`, `M₁ = L^{m₀ + m₁ - 3}`) they hold as soon as `3 ≤ m₀`, `4 ≤ m₁`
  and `R₀(d, L) < L^{m₀-3}` (all monotone in the exponents);
* `rGenWTies_nonempty`: `RGenWTies` holds for a choice of `M₁` (Rule 10).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale

/-- **The conditions on the constants for the decoupled theory on the generating sets of `R`.** -/
def RGenWTies (d : ℕ) (T : ℝ → ℝ → Typing) (C7 : ℝ → ℝ → Consts7) (M1 : ℝ → ℝ → ℕ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    (T κ c₉).L ^ (C7 κ c₉).m₁ ∣ M1 κ c₉ ∧ 2 ≤ (C7 κ c₉).m₁ ∧
    4 * (T κ c₉).L ^ 2 ≤ (T κ c₉).L ^ (C7 κ c₉).m₁ ∧
    4 * d * (T κ c₉).L ^ (C7 κ c₉).m₁ ≤ 5 * M1 κ c₉ ∧
    2 * d * Real.log (T κ c₉).L ≤ agmonRate d / 16 * (minSep (T κ c₉).L (M1 κ c₉) - 1)

/-- **The conditions in combinable form** (the explicit choice of `prefixInput_exists_of`:
`c = L³`, `M₁ = L^{m₀ + m₁ - 3}`): they hold as soon as `3 ≤ m₀`, `4 ≤ m₁` and `R₀(d, L) < L^{m₀-3}`.
The hypotheses are monotone in `m₀` and in `m₁` (eventually true), so they intersect with the other
ties of the constants. -/
theorem rGenWTies_of_pow {d L m₀ m₁ : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hm₀ : 3 ≤ m₀) (hm₁ : 4 ≤ m₁)
    (hR : Background.bgR0 d L < (L : ℝ) ^ (m₀ - 3)) :
    L ^ m₁ ∣ L ^ (m₀ + m₁ - 3) ∧ 2 ≤ m₁ ∧ 4 * L ^ 2 ≤ L ^ m₁ ∧
      4 * d * L ^ m₁ ≤ 5 * L ^ (m₀ + m₁ - 3) ∧
      2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ (m₀ + m₁ - 3)) - 1) := by
  have hag := agmonRate_pos (show 0 < d by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hsplit : (L : ℝ) ^ (m₀ + m₁ - 3) = (L : ℝ) ^ m₁ * (L : ℝ) ^ (m₀ - 3) := by
    rw [← pow_add]; congr 1; omega
  have hpm : (81 : ℝ) ≤ (L : ℝ) ^ m₁ := by
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ (L : ℝ) ^ 4 := by gcongr
      _ ≤ (L : ℝ) ^ m₁ := pow_le_pow_right₀ hL1.le hm₁
  have hb1 : 4 * (d : ℝ) * L ≤ Background.bgR0 d L := le_max_left _ _
  have hb2 : 1 + 2 * d * Real.log L / (agmonRate d / 2 / 2) ≤ Background.bgR0 d L :=
    le_max_right _ _
  have hP : (0 : ℝ) ≤ (L : ℝ) ^ (m₀ - 3) := by positivity
  refine ⟨pow_dvd_pow L (by omega), by omega, ?_, ?_, ?_⟩
  · have h1 : 4 * L ^ 2 ≤ L ^ 4 := by
      have : 4 ≤ L ^ 2 := by nlinarith
      calc 4 * L ^ 2 ≤ L ^ 2 * L ^ 2 := Nat.mul_le_mul_right _ this
        _ = L ^ 4 := by ring
    exact h1.trans (Nat.pow_le_pow_right (by omega) hm₁)
  · have h : ((4 * d * L ^ m₁ : ℕ) : ℝ) ≤ ((5 * L ^ (m₀ + m₁ - 3) : ℕ) : ℝ) := by
      push_cast
      rw [hsplit]
      have hdL : 4 * (d : ℝ) ≤ (L : ℝ) ^ (m₀ - 3) := by nlinarith
      have hpm0 : (0 : ℝ) ≤ (L : ℝ) ^ m₁ := by positivity
      nlinarith
    exact_mod_cast h
  · unfold minSep
    push_cast
    rw [hsplit]
    have hq : 2 * (d : ℝ) * Real.log L / (agmonRate d / 2 / 2) = 8 * d * Real.log L / agmonRate d := by
      field_simp; ring
    rw [hq] at hb2
    have h8 : 8 * (d : ℝ) * Real.log L ≤ agmonRate d * ((L : ℝ) ^ (m₀ - 3) - 1) := by
      have := (div_le_iff₀ hag).1 (by linarith : 8 * (d : ℝ) * Real.log L / agmonRate d ≤
        (L : ℝ) ^ (m₀ - 3) - 1)
      linarith
    have hbig : 4 * ((L : ℝ) ^ (m₀ - 3) - 1) + 1 ≤ 5 * L * ((L : ℝ) ^ m₁ * (L : ℝ) ^ (m₀ - 3)) := by
      have h5 : (L : ℝ) ^ (m₀ - 3) ≤ (L : ℝ) ^ m₁ * (L : ℝ) ^ (m₀ - 3) := by nlinarith
      nlinarith
    have hA : 0 ≤ agmonRate d * ((L : ℝ) ^ (m₀ - 3) - 1) := by
      have : (1 : ℝ) ≤ (L : ℝ) ^ (m₀ - 3) := by
        have : 1 ≤ Background.bgR0 d L := by
          have : (0 : ℝ) ≤ 2 * d * Real.log L / (agmonRate d / 2 / 2) := by positivity
          linarith [hb2]
        linarith
      nlinarith
    nlinarith

/-- **`RGenWTies` at the choice `M₁ = L^{m₀ + m₁ - 3}`** (that of `prefixInput_exists_of`): if, in
every pair `κ, c₉`, the typing has `L ≥ 3`, `M₁ = L^{m₀ + m₁ - 3}` with the cell exponent `m₀ ≥ 3`,
`R₀(d, L) < L^{m₀ - 3}` and the block exponent `m₁ ≥ 4`, then `RGenWTies` holds. -/
theorem rGenWTies_of_choice {d : ℕ} (hd : 3 ≤ d) {T : ℝ → ℝ → Typing} {C7 : ℝ → ℝ → Consts7}
    {M1 : ℝ → ℝ → ℕ} {m₀ : ℝ → ℝ → ℕ}
    (h : ∀ κ c₉, 3 ≤ (T κ c₉).L ∧ M1 κ c₉ = (T κ c₉).L ^ (m₀ κ c₉ + (C7 κ c₉).m₁ - 3) ∧
      3 ≤ m₀ κ c₉ ∧ 4 ≤ (C7 κ c₉).m₁ ∧
      Background.bgR0 d (T κ c₉).L < ((T κ c₉).L : ℝ) ^ (m₀ κ c₉ - 3)) :
    RGenWTies d T C7 M1 := by
  intro κ _ c₉ _
  obtain ⟨hL, hM, hm₀, hm₁, hR⟩ := h κ c₉
  rw [hM]
  exact rGenWTies_of_pow hd hL hm₀ hm₁ hR

/-- **`RGenWTies` is inhabited** (Rule 10): at `L ≥ 3`, `m₁ = 4` and `M₁ = L^{m₀ + 1}` for an `m₀`
with `R₀(d, L) < L^{m₀ - 3}`. -/
theorem rGenWTies_nonempty {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (T : ℝ → ℝ → Typing)
    (hT : ∀ κ c₉, (T κ c₉).L = L) (C7 : ℝ → ℝ → Consts7) (hC7 : ∀ κ c₉, (C7 κ c₉).m₁ = 4) :
    ∃ M1 : ℝ → ℝ → ℕ, RGenWTies d T C7 M1 := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Background.bgR0 d L) hL1
  refine ⟨fun _ _ => L ^ (n + 3 + 4 - 3), rGenWTies_of_choice (m₀ := fun _ _ => n + 3) hd
    fun κ c₉ => ⟨by rw [hT]; exact hL, by rw [hT, hC7], by omega, by rw [hC7], ?_⟩⟩
  rw [hT]
  simpa using hn

end Balaban.RootFSpine
