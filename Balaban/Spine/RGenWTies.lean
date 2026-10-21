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
* `rGenWTies_exists`: they are jointly satisfiable with `M = c M₁ = L^{m₀ + m₁}`, `c ≥ 14`, for
  every `d, L ≥ 3` and every large `m₁` (`M₁ = L^{m₁ + a}`, `c = L^{m₀ - a}`);
* `rGenWTies_nonempty`: `RGenWTies` holds for a choice of `m₁` and `M₁` (Rule 10).
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

/-- The arithmetic of the conditions on `M₁` at one `L ≥ 3` and `m₁`, `M₁ = L^{m₁ + a}`: they hold
as soon as `L^a` dominates `d` and the Agmon constant. -/
theorem rGenWTies_at {d L m₁ : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ a : ℕ, L ^ m₁ ∣ L ^ (m₁ + a) ∧ 4 * d * L ^ m₁ ≤ 5 * L ^ (m₁ + a) ∧
      2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ (m₁ + a)) - 1) := by
  have hag := agmonRate_pos (show 0 < d by omega)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  obtain ⟨a, ha⟩ := pow_unbounded_of_one_lt (4 * (d : ℝ) + 32 * d * Real.log L / agmonRate d + 1) hL1
  refine ⟨a, pow_dvd_pow L (by omega), ?_, ?_⟩
  · have h1 : (4 * d : ℝ) ≤ (L : ℝ) ^ a := by
      have : 0 ≤ 32 * (d : ℝ) * Real.log L / agmonRate d := by positivity
      linarith
    have h2 : ((4 * d * L ^ m₁ : ℕ) : ℝ) ≤ ((5 * L ^ (m₁ + a) : ℕ) : ℝ) := by
      push_cast
      rw [pow_add]
      have hp : (0 : ℝ) ≤ (L : ℝ) ^ m₁ := by positivity
      nlinarith
    exact_mod_cast h2
  · unfold minSep
    have h1 : 32 * (d : ℝ) * Real.log L / agmonRate d ≤ (L : ℝ) ^ a := by
      have : (0 : ℝ) ≤ 4 * d := by positivity
      linarith
    have hpm : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ hL1.le
    have hpa : (0 : ℝ) ≤ (L : ℝ) ^ a := by positivity
    have h2 : 32 * (d : ℝ) * Real.log L ≤ agmonRate d * (L : ℝ) ^ a := by
      rw [div_le_iff₀ hag] at h1; linarith
    have h3 : (L : ℝ) ^ a ≤ 5 * L * (L : ℝ) ^ (m₁ + a) - 1 := by
      rw [pow_add]
      have hpa1 : (1 : ℝ) ≤ (L : ℝ) ^ a := one_le_pow₀ hL1.le
      have hP : (L : ℝ) ^ a ≤ (L : ℝ) ^ m₁ * (L : ℝ) ^ a := le_mul_of_one_le_left hpa hpm
      have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
      have hP0 : (0 : ℝ) ≤ (L : ℝ) ^ m₁ * (L : ℝ) ^ a := by positivity
      have h5 : 15 * ((L : ℝ) ^ m₁ * (L : ℝ) ^ a) ≤ 5 * L * ((L : ℝ) ^ m₁ * (L : ℝ) ^ a) := by
        nlinarith
      nlinarith
    push_cast
    have h4 : agmonRate d * (L : ℝ) ^ a ≤ agmonRate d * (5 * L * (L : ℝ) ^ (m₁ + a) - 1) :=
      mul_le_mul_of_nonneg_left h3 hag.le
    nlinarith

/-- **The four conditions are compatible with `M = c M₁ = L^{m₀ + m₁}`, `c ≥ 14`** (the clauses
of `PrefixInput` on `M`, `c`, `M₁`): for `d, L ≥ 3` and every `m₁` there are `m₀`, `c`, `M₁` with
all of them (the conditions `2 ≤ m₁`, `4 L² ≤ L^{m₁}` concern `m₁` alone). -/
theorem rGenWTies_exists {d L m₁ : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ m₀ c M₁ : ℕ, c * M₁ = L ^ (m₀ + m₁) ∧ 14 ≤ c ∧ 1 ≤ M₁ ∧
      L ^ m₁ ∣ M₁ ∧ 4 * d * L ^ m₁ ≤ 5 * M₁ ∧
      2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M₁ - 1) := by
  obtain ⟨a, hdvd, hcov, hsep⟩ := rGenWTies_at (m₁ := m₁) hd hL
  refine ⟨a + 3, L ^ 3, L ^ (m₁ + a), ?_, ?_, Nat.one_le_pow _ _ (by omega), hdvd, hcov, hsep⟩
  · rw [← pow_add]; congr 1; ring
  · calc 14 ≤ 3 ^ 3 := by norm_num
      _ ≤ L ^ 3 := Nat.pow_le_pow_left hL 3

/-- **`RGenWTies` is inhabited** (Rule 10): for a typing with `L ≥ 3` in every pair, the choice
`m₁ = m` with `4 L² ≤ L^m` and `M₁ = L^{m + a}` of `rGenWTies_at` satisfies it. -/
theorem rGenWTies_nonempty (d : ℕ) (hd : 3 ≤ d) (T : ℝ → ℝ → Typing)
    (hL : ∀ κ c₉, 3 ≤ (T κ c₉).L) (C7 : ℝ → ℝ → Consts7)
    (hm : ∀ κ c₉, 2 ≤ (C7 κ c₉).m₁ ∧ 4 * (T κ c₉).L ^ 2 ≤ (T κ c₉).L ^ (C7 κ c₉).m₁) :
    ∃ M1 : ℝ → ℝ → ℕ, RGenWTies d T C7 M1 := by
  classical
  have h := fun κ c₉ => rGenWTies_at (m₁ := (C7 κ c₉).m₁) hd (hL κ c₉)
  refine ⟨fun κ c₉ => (T κ c₉).L ^ ((C7 κ c₉).m₁ + Classical.choose (h κ c₉)), ?_⟩
  intro κ _ c₉ _
  obtain ⟨hdvd, hcov, hsep⟩ := Classical.choose_spec (h κ c₉)
  exact ⟨hdvd, (hm κ c₉).1, (hm κ c₉).2, hcov, hsep⟩

end Balaban.RootFSpine
