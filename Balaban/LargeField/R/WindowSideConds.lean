/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuPt
public import Balaban.LargeField.Characteristic.RealDomain
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The smallness conditions of the window conversion are constant conditions (blocker 4)

In `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du_consts` the constants `δw`, `δs`, `δm` are
produced before the window point and the data.  Six smallness conditions bound the caller's
`ε_i`, `Δ`, `δl`, `δu`, `m` by them; `WindowSideConds` collects these six conditions, in the form in
which they occur among the hypotheses of the conversion, and `windowSideConds_exists` shows that they
are jointly satisfiable for every positive `δw`, `δs`, `δm` and every size `K_a`, `c_ν`, `Δ`, `η`
of the caller.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.SmallField

universe u

/-- **The six smallness conditions** of the window conversion on the caller's constants: the
sources `ε_i`, the coefficient difference `Δ`, the radii `δl`, `δu` of the piece datum and of the
reference datum, and the mass bound `m`, against the constants `δw`, `δs`, `δm`. -/
def WindowSideConds (d L N : ℕ) [NeZero L] (δw δs δm η Ka cν Δ δl δu m : ℝ) {ι : Type u}
    (ε : ι → ℝ) : Prop :=
  (∀ i, bgK1 d L N * (xiC1 d * ε i) ≤ min (deltaStar d L N) δw) ∧
  (∀ i, ε i * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ min (deltaStar d L N) δw) ∧
  (∀ i, Δ * (2 * ε i) ≤ min (deltaStar d L N) δw) ∧
  bgK1 d L N * (δl + δu) ≤ δs ∧
  bgK1 d L N * δl ≤ min (deltaStar d L N) δm ∧
  m * 2 ≤ min (deltaStar d L N) δm

/-- **The six smallness conditions are jointly satisfiable**: for positive `δw`, `δs`, `δm` and any
sizes `η`, `K_a ≥ 0`, `c_ν ≥ 0`, `Δ ≥ 0` there are `ε* > 0`, radii `δl`, `δu` in `(0, c₁]` and
`m* > 0` such that every `ε` with `ε_i ≤ ε*` and every `0 ≤ m ≤ m*` satisfy them. -/
theorem windowSideConds_exists (d L N : ℕ) [NeZero L] (hd : 0 < d) {δw δs δm : ℝ}
    (hδw : 0 < δw) (hδs : 0 < δs) (hδm : 0 < δm) (η : ℝ) {Ka cν Δ : ℝ} (hKa : 0 ≤ Ka)
    (hcν : 0 ≤ cν) (hΔ : 0 ≤ Δ) :
    ∃ εs δl δu ms : ℝ, 0 < εs ∧ 0 < δl ∧ δl ≤ bgC1 d L N ∧ 0 < δu ∧ δu ≤ bgC1 d L N ∧
      0 < ms ∧ ∀ {ι : Type u} (ε : ι → ℝ) (m : ℝ), (∀ i, ε i ≤ εs) → 0 ≤ m → m ≤ ms →
        WindowSideConds d L N δw δs δm η Ka cν Δ δl δu m ε := by
  have hK := bgK1_pos d L N
  have hx : 0 < xiC1 d := by unfold xiC1; positivity
  have hds := deltaStar_pos (d := d) (L := L) (N := N) hd
  have hc1 := bgC1_pos_of (d := d) (L := L) (N := N) hd
  have hX : 0 < min (deltaStar d L N) δw := lt_min hds hδw
  have hY : 0 < min (deltaStar d L N) δm := lt_min hds hδm
  have he : 0 ≤ 4 * Real.exp (2 * η) * Ka + 24 * cν := by positivity
  set X := min (deltaStar d L N) δw with hXdef
  set Y := min (deltaStar d L N) δm with hYdef
  set D := bgK1 d L N * xiC1 d + (4 * Real.exp (2 * η) * Ka + 24 * cν) + 2 * Δ + 1 with hD
  have hDp : 0 < D := by positivity
  set r := min (bgC1 d L N) (min (δs / (2 * bgK1 d L N)) (Y / bgK1 d L N)) with hr
  have hrp : 0 < r := lt_min hc1 (lt_min (by positivity) (by positivity))
  have hr1 : r ≤ bgC1 d L N := min_le_left _ _
  have hr2 : bgK1 d L N * r ≤ δs / 2 := by
    have : r ≤ δs / (2 * bgK1 d L N) := (min_le_right _ _).trans (min_le_left _ _)
    calc bgK1 d L N * r ≤ bgK1 d L N * (δs / (2 * bgK1 d L N)) := by gcongr
      _ = δs / 2 := by field_simp
  have hr3 : bgK1 d L N * r ≤ Y := by
    have : r ≤ Y / bgK1 d L N := (min_le_right _ _).trans (min_le_right _ _)
    calc bgK1 d L N * r ≤ bgK1 d L N * (Y / bgK1 d L N) := by gcongr
      _ = Y := by field_simp
  refine ⟨X / D, r, r, Y / 2, by positivity, hrp, hr1, hrp, hr1, by positivity, ?_⟩
  intro ι ε m hε hm0 hm
  have key : ∀ a : ℝ, 0 ≤ a → a ≤ D → ∀ t : ℝ, t ≤ X / D → a * t ≤ X := by
    intro a ha haD t ht
    by_cases h0 : t ≤ 0
    · nlinarith
    · have h0' := not_le.1 h0
      calc a * t ≤ a * (X / D) := by gcongr
        _ ≤ D * (X / D) := by gcongr
        _ = X := by field_simp
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_, ?_, ?_⟩
  · have := key (bgK1 d L N * xiC1 d) (by positivity) (by simp only [hD]; nlinarith) (ε i) (hε i)
    calc bgK1 d L N * (xiC1 d * ε i) = bgK1 d L N * xiC1 d * ε i := by ring
      _ ≤ X := this
  · have := key (4 * Real.exp (2 * η) * Ka + 24 * cν) he (by simp only [hD]; nlinarith) (ε i) (hε i)
    linarith
  · have := key (2 * Δ) (by positivity) (by simp only [hD]; nlinarith) (ε i) (hε i)
    calc Δ * (2 * ε i) = 2 * Δ * ε i := by ring
      _ ≤ X := this
  · nlinarith
  · exact hr3
  · linarith

end Balaban.LargeField
