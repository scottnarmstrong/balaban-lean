/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorSource
public import Balaban.Inhabited.LevelStepSettingGeneral

/-!
# Typing of the local generating set at the low separation index `R₀(d, L)`

The local generating set `localB` of a polymer has separation index any `ϱ ≤ 5 L L ^ m₁`.  At
the index `ϱ = R₀(d, L)` it is typeable once `R₀(d, L) ≤ 5 L L ^ m₁`, which holds for large `m₁`
(for `d = L = 3` as soon as `6 ≤ m₁`), and the background hypotheses `BgHyp` hold at that index.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.LargeField Balaban.Inhabited.LevelStep

/-- **The window is non-empty for large `m₁`**: for `L ≥ 3` there is `m₁*` with
`R₀(d, L) ≤ 5 L L ^ m₁` for all `m₁ ≥ m₁*`. -/
theorem bgR0_le_minSep_of_large (d L : ℕ) (hL : 3 ≤ L) :
    ∃ m₀ : ℕ, ∀ m₁ : ℕ, m₀ ≤ m₁ → bgR0 d L ≤ minSep L ((L ^ m₁ : ℕ)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  obtain ⟨m₀, hm⟩ := pow_unbounded_of_one_lt (bgR0 d L) hL1
  refine ⟨m₀, fun m₁ hm₁ => ?_⟩
  have h1 : (L : ℝ) ^ m₀ ≤ (L : ℝ) ^ m₁ := pow_le_pow_right₀ hL1.le hm₁
  have h2 : (0 : ℝ) ≤ L := by positivity
  unfold minSep
  push_cast
  have h3 : (1 : ℝ) ≤ 5 * L := by nlinarith
  have : (L : ℝ) ^ m₁ ≤ 5 * L * (L : ℝ) ^ m₁ := by
    have : (0 : ℝ) ≤ (L : ℝ) ^ m₁ := by positivity
    nlinarith
  linarith

/-- **Threshold at `d = L = 3`**: `R₀(3, 3) ≤ 15 · 3 ^ m₁` for `6 ≤ m₁`.  (For `m₁ = 5` it fails:
`R₀(3, 3) = 1 + 3456 log 3 > 3645`.) -/
theorem bgR0_three_le_minSep (m₁ : ℕ) (hm : 6 ≤ m₁) :
    bgR0 3 3 ≤ minSep 3 ((3 ^ m₁ : ℕ)) := by
  have hp : (3 : ℝ) ^ 6 ≤ (3 : ℝ) ^ m₁ := pow_le_pow_right₀ (by norm_num) hm
  have hlog : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hc : poincareConst 3 = 1 / 3 := by
    unfold poincareConst; norm_num
  unfold minSep bgR0
  push_cast
  unfold agmonRate
  rw [hc]
  apply max_le
  · norm_num at hp ⊢; linarith
  · norm_num at hp hlog ⊢
    have : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
    nlinarith

/-- **`BgHyp` at the low index.**  The background hypotheses hold at the separation index
`ϱ = R₀(d, L)` itself (the field `hϱ` is `le_rfl`), under the same mass hypotheses as at any
larger index. -/
theorem bgHyp_localB_low {d L k : ℕ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    BgHyp d L (k + 1) (bgR0 d L) (compWeight L 1) ν :=
  bgHyp_lvG hd hL le_rfl hν0 hν

end Balaban.SmallField.GsSpec
