/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelCoversDef
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.LevelRayTower
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower at each scale (`d = L = 3`, `N = 2`)

For a fixed `T : StepTower κmin`, `StepScaleData T k hk N₁ ν β p₁` bundles once the objects that
every landed scale theorem re-derives from its own tower call, for the step
`hatStepK k T.m₁ hk ν β p₁ T.δ`: the transferred `FlCore` on `lvTop/lvLow`, the `XiCData` of the
step, the ray data, the radius inequalities of `scale_C_items`, and the block and source-site
covers of `levelLocalCover`.  The fields are stated directly on the term `hatStepK …`
(`StepTower.step`).

* `StepTower.scale`: one threshold `βray ≥ 2`, chosen before the scale index, after which
  `StepScaleData` is inhabited at every admissible scale.
* `StepTower.scale_instance`: the record at `k = 1`, `N₁ = 6`.
* `detExpansionLocC_scale_fromTower`: the localized determinant family at every scale, as a thin
  wrapper of `detExpansionLocC_scale_of_tower`.

The four remaining endpoints (source activity, chart/determinant, `sourceFamilyRelative`,
`expSourceChart`) are not in this file.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

namespace StepTower

variable {κmin : ℝ}

/-- **The tower at every scale.**  One threshold `βray ≥ 2`, chosen before the scale index, after
which `StepScaleData` is inhabited at every admissible scale. -/
theorem scale (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ βray : ℝ, 2 ≤ βray ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, βray ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      Nonempty (StepScaleData T k hk N₁ ν β p₁) := by
  obtain ⟨βray, h2, h⟩ := StepTowerG.scale T.toG hA p
  refine ⟨βray, h2, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h3 : 3 ^ T.toG.m₀ ∣ N₁ := by simpa using h3N
  obtain ⟨hS⟩ := h k hk N₁ h3 hN ν hν0 (by simpa using hν) β hβ p₁ hp0 (by simpa [hb] using hp₁)
  exact ⟨T.scaleData_of_toG hS⟩

/-- Normalization of the determinant rate denominator. -/
theorem det_rate_den : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num

/-- Normalization of the determinant constant. -/
theorem det_const_eq (c w : ℝ) :
    ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * c / w) = 27 * c / w := by
  push_cast; ring

/-- **Non-vacuity at one scale.**  For every tower, with `k = 1`, `N₁ = 6`, `ν = 0`, `A₁ = 1`,
`p = 0` (so the cutoff is `p₁ = 1`), the record is inhabited at `β = βray`. -/
theorem scale_instance (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧ Nonempty (StepScaleData T 1 le_rfl 6 0 βray 1) := by
  obtain ⟨βray, h2, h⟩ := T.scale (A₁ := 1) one_pos 0
  refine ⟨βray, h2, ?_⟩
  have hb : (1 : ℝ) < βray * 3 ^ 1 := by norm_num; linarith
  exact h 1 le_rfl 6 (by norm_num) (by norm_num) 0 le_rfl (by norm_num) βray le_rfl 1
    one_pos (by simp [pLog])

end StepTower

open Classical in
/-- **The localized determinant family at every scale of the tower `T`.**  No threshold on `β`. -/
theorem detExpansionLocC_scale_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    (∀ z, ∃ E : DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
        ((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18)
        (27 * covBLogMax 3 3 T.κ /
          (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))),
      ∀ D T', E.term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D y T') ∧
    T.κ' ≤ (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18 := by
  refine ⟨?_, T.det_rate⟩
  have h := (detExpansionLocC_scale_of_tower T.m₁_four T.t_pos (Classical.choice T.core)
    T.large_block T.dom_margin T.coer_margin T.δc_small T.det_z k hk N₁ h3N hN hν0 hν β p₁
    T.δ).2
  intro z
  have hz := h z
  rw [StepTower.det_rate_den, StepTower.det_const_eq] at hz
  exact hz

end Balaban.Inhabited
