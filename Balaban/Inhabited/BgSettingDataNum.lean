/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Inhabited
public import Balaban.Localization.I5FluctNonempty
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# Joint smallness of the constants of `ChainNum` and `FlNum`

`joint_num_exists`: for the same `ε'` and `δ₃ = A ε'` the conditions `ChainNum` (of `BgSetting`) and
`FlNum` (of `FlSetting`, with `δ₁ = ε'`) hold for all small `ε' > 0`; used by `BgSettingData`.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace BgSettingData

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.Localization.I5Inhabited

section Num

open Filter Topology

/-- The smallness conditions of `ChainNum` and `FlNum` are satisfiable simultaneously with
`δ₁ = ε'` and `δ₃ = A ε'` (`FlNum` for the same `ε'`, `δ₃` as the chain). -/
theorem joint_num_exists (d L N m₁ : ℕ) [NeZero L] (hd : 0 < d) {BG BG₂ : ℝ} (hBG : 0 ≤ BG)
    (hBG₂ : 0 ≤ BG₂) (κ r₀ : ℝ) :
    ∃ eps δ₃ δfl : ℝ, ChainNum d L N m₁ BG κ r₀ eps δ₃ ∧
      FlNum d L N BG BG₂ κ eps δ₃ eps δfl := by
  set A : ℝ := N * composedCloseBound d L N m₁ BG κ (xiC1 d) r₀ with hA
  have hA0 : 0 ≤ A := by
    have := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁) (κ := κ) (r₀ := r₀)
      hBG (by have := one_le_xiC1 d; linarith) hd
    positivity
  have hT : 0 < thm73C1 d L N := by
    unfold thm73C1
    have := bgC1_pos' (d := d) (L := L) (N := N) hd
    have := bgK1_pos d L N
    have : (8:ℝ) ≤ compC4 d := compC4_ge d
    positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd; linarith
  have hk0 := cK2'_nonneg (d := d) (L := L) (N := N) hB0
  have hD1 : 0 < deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) :=
    deltaStar'_pos hB0 (by have := gamma1_pos hd; positivity)
  have hc7 := c7_pos (d := d) (L := L) (N := N) (κ := κ) hd hBG
  have hC1 := bgC1_pos' (d := d) (L := L) (N := N) hd
  have hC0 := bgC0_pos d L N hd
  have hds := deltaStar_pos (d := d) (L := L) (N := N) hd
  have hK1 := bgK1_pos d L N
  set C0 := scaledC0 d with hC0def
  set K2 := xiK2 d L N with hK2def
  set k := cK2' d L N (famConst d L BG₂ κ) with hk
  set D1 := deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8) with hD1def
  set F : ℝ → ℝ := fun e => N * (5 * (k * e) + e) with hF
  have key : ∀ᶠ e : ℝ in 𝓝 0,
      ((4 * d + 6) * ((2 * d + 1) * e) < 1 ∧ xiC1 d * e < thm73C1 d L N ∧
      xiC1 d * e < c7 d L N BG κ ∧
      (4 * d + 6) * ((2 * d + 1) * (C0 ^ 2 * e)) < 1 ∧ A * e < 1 ∧
      xiC1 d * (C0 ^ 2 * e) + 5 * (A * e) < bgC1 d L N ∧ A * e < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (C0 ^ 2 * e)) < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (C0 ^ 2 * e)) + cK2 d L N * (A * e) < bgC0 d L N ∧
      (4 * d + 6) * ((2 * d + 1) * (C0 ^ 2 * e + K2 * (A * e))) < 1 ∧
      xiC1 d * (C0 ^ 2 * e + K2 * (A * e)) < thm73C1 d L N) ∧
      (e < D1 ∧ 2 * (K4 d L N BG κ * (xiC1 d * e)) < D1 ∧
      2 * (K4 d L N BG κ * (xiC1 d * e)) < 1 ∧ (3 + K4 d L N BG κ) * (xiC1 d * e) < 1 / 2 ∧
      F e < 1 ∧
      xiC1 d * (C0 ^ 2 * e + K2 * (A * e)) + 5 * F e < bgC1 d L N ∧ F e < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (C0 ^ 2 * e + K2 * (A * e))) < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * (C0 ^ 2 * e + K2 * (A * e))) + cK2 d L N * F e < bgC0 d L N ∧
      (4 * d + 6) * ((2 * d + 1) * (C0 ^ 2 * e + K2 * (A * e) + K2 * F e)) < 1 ∧
      xiC1 d * (C0 ^ 2 * e + K2 * (A * e) + K2 * F e) < thm73C1 d L N) := by
    refine Filter.Eventually.and ?_ ?_
    · refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hT) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hc7) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hC1) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hds) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hds) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hC0) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
      exact ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hT)
    · have hF0 : F 0 = 0 := by simp [hF]
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hD1) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hD1) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simp) |>.and ?_
      refine ContinuousAt.eventually_lt (by simp only [hF]; fun_prop) (by fun_prop)
        (by rw [hF0]; norm_num) |>.and ?_
      refine ContinuousAt.eventually_lt (by simp only [hF]; fun_prop) (by fun_prop)
        (by simp only [hF0]; simpa using hC1) |>.and ?_
      refine ContinuousAt.eventually_lt (by simp only [hF]; fun_prop) (by fun_prop)
        (by rw [hF0]; exact hds) |>.and ?_
      refine ContinuousAt.eventually_lt (by fun_prop) (by fun_prop) (by simpa using hds) |>.and ?_
      refine ContinuousAt.eventually_lt (by simp only [hF]; fun_prop) (by fun_prop)
        (by simp only [hF0]; simpa using hC0) |>.and ?_
      refine ContinuousAt.eventually_lt (by simp only [hF]; fun_prop) (by fun_prop)
        (by simp only [hF0]; simp) |>.and ?_
      exact ContinuousAt.eventually_lt (by simp only [hF]; fun_prop) (by fun_prop)
        (by simp only [hF0]; simpa using hT)
  have hpos : ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < e := self_mem_nhdsWithin
  obtain ⟨e, ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩,
    ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩⟩, he⟩ :=
    ((key.filter_mono nhdsWithin_le_nhds).and hpos).exists
  have hFe : 0 ≤ F e := by simp only [hF]; positivity
  refine ⟨e, A * e, F e, ⟨he, h1.le, h2.le, h3.le, h4.le, by positivity, h5.le, h6.le, h7.le,
    h8.le, h9, h10.le, h11.le, ?_⟩, ⟨he, g1.le, g2.le, g3.le, g4, le_rfl, hFe, g5.le, g6.le,
    g7.le, g8.le, g9, g10.le, g11.le⟩⟩
  rw [composedCloseBound_linear]
  rw [hA]; nlinarith

end Num

end BgSettingData
end Balaban.Inhabited
