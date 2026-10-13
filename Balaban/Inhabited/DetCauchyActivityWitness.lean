/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LocalizationSettings
public import Balaban.Inhabited.YregBlocksWitness
public import Balaban.Inhabited.DetCauchyGraphWitness
public import Balaban.Fluctuation.DetCauchyActivity
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of `DetCauchyActivity`

On the positive witness geometry of `LocalizationSettings.lean` (`d = L = 3`, `N₁ = 6`, `k = 1`,
`G = GP m₁ (rhoSep m₁)`, constant field `φ ≡ e₀`, `α = 0`) the hypotheses of the resummation,
support and decay theorems of `DetCauchyActivity` hold at the cut radius
`κ = log (2 (detDeg 3 3 + 1)²) + 1`, for which the rate condition `e^κ > 2 (detDeg 3 3 + 1)²`
holds.  (The cut radius `κ = 1` of `DetCauchyGraphWitness` is far too small for the rate condition,
`detDeg 3 3` being of order `10^8`; the instance below takes `m₁` with
`cstarX 3 3 · e^{N₀ κ} ≤ 3^{m₁}`, which is a very large `m₁`.)
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Fluctuation Balaban.Analysis Balaban.SmallField.Def6

/-- **Non-vacuity of the activity theorems at the rate-admissible cut radius.** -/
theorem detCauchyActivity_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ) (y : unitPts G)
      (κ δ : ℝ) (φ : CTorus 3 3 6 m₁ (1 + 1) → Fin 3 → ℂ) (α : G.Ω 1 → ℂ),
      XSetting G (compWeight 3 1) 1 0 ∧ HatConn G ∧ (3 : ℕ) ^ 0 ∣ 6 ∧ 0 < κ ∧
        cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁ ∧ 0 ≤ δ ∧
        δ ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 ∧ IsConstraintFieldStrict G δ φ ∧
        (∀ w, ‖α w‖ < coerciveConst 3 / (2 * (G.spacing (w : CTorus 3 3 6 m₁ (1 + 1))) ^ 2)) ∧
        ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
        rootTrace G (compWeight 3 1) 1 0 (unitQ G) (unitP G) {y} (fun _ => 1) φ α =
          ∑ Y, detActivity 0 (compWeight 3 1) 1 0 φ α y Y ∧
        (∀ Y, detActivity 0 (compWeight 3 1) 1 0 φ α y Y ≠ 0 →
          rootCube (m₀ := 0) (rootIdxOf y) ∈ Y ∧ IsPolyDom 0 (1 + 1) (sitesOf Y)) ∧
        (∀ Y, ‖detActivity 0 (compWeight 3 1) 1 0 φ α y Y‖ ≤
          (1 / 2 : ℝ) * 3 * covBLog 3 3 (compWeight 3 1 1) (1 / (3 : ℝ) ^ 2) κ /
            (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
          Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
            (2 * 3 * 3)) * dExt Y)) := by
  classical
  set Δ : ℝ := ((detDeg 3 3 + 1 : ℕ) : ℝ) with hΔ
  have hΔ1 : (1 : ℝ) ≤ Δ := by rw [hΔ]; exact_mod_cast Nat.le_add_left 1 _
  set κ : ℝ := Real.log (2 * Δ ^ 2) + 1 with hκdef
  have hκ : 0 < κ := by
    have : 0 ≤ Real.log (2 * Δ ^ 2) := Real.log_nonneg (by nlinarith)
    rw [hκdef]; linarith
  have hz : Δ ^ 2 * (2 / Real.exp κ) < 1 := by
    have h1 : Real.exp κ = 2 * Δ ^ 2 * Real.exp 1 := by
      rw [hκdef, Real.exp_add, Real.exp_log (by positivity)]
    have h2 : Δ ^ 2 * (2 / Real.exp κ) = 1 / Real.exp 1 := by
      rw [h1]; field_simp
    rw [h2, div_lt_one (Real.exp_pos _)]
    exact Real.one_lt_exp_iff.2 one_pos
  obtain ⟨m₁, h4, hc⟩ := exists_m₁ (cstarX 3 3 * Real.exp (N0 3 3 * κ))
  have S := xSetting_pos h4
  set G := GP m₁ (rhoSep m₁) with hG
  have hl0 : (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.layer (1 + 1) := by
    rw [hG]; exact (Finset.ext_iff.1 (GP_layer_two (m₁ := m₁) (ϱ := rhoSep m₁)) _).2
      (Finset.mem_univ _)
  set y : unitPts G := ⟨unitBlock (0 : CTorus 3 3 6 m₁ (1 + 1)), (mem_unitPts G).2 ⟨0, hl0, rfl⟩⟩
    with hy
  set c : ℝ := |smallConstX 3 3 κ| with hcdef
  set δ : ℝ := 1 / (2 * (c + 1)) with hδdef
  have hc0 : 0 ≤ c := abs_nonneg _
  have hδpos : 0 < δ := by positivity
  have hsm : δ ^ 2 * smallConstX 3 3 κ ≤ 1 / 4 := by
    have h1 : δ ^ 2 * smallConstX 3 3 κ ≤ δ ^ 2 * c :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have h2 : δ ^ 2 * c = c / (4 * (c + 1) ^ 2) := by
      rw [hδdef]; field_simp; ring
    have h3 : c / (4 * (c + 1) ^ 2) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hφ : IsConstraintFieldStrict G δ (fun _ => (Pi.single 0 1 : Fin 3 → ℂ)) := by
    have hv0 : vn (0 : Fin 3 → ℂ) = 0 := by simp [vn]
    refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · have hs := spacing_pos G (x := x)
      simp only [sub_self, hv0]
      exact ⟨by positivity, by positivity⟩
    · have hs := spacing_pos G (x := x)
      have : (fun i : Fin 3 => ∑ μ : Fin 3, ((Pi.single 0 1 : Fin 3 → ℂ) i +
          (Pi.single 0 1 : Fin 3 → ℂ) i - 2 * (Pi.single 0 1 : Fin 3 → ℂ) i)) = 0 := by
        funext i; simp; ring
      rw [this, hv0]; positivity
    · have : vn (Pi.single 0 1 : Fin 3 → ℂ) = 1 := by
        unfold vn
        show ‖EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ = 1
        simp
      rw [this]; norm_num
    · have : ∑ i : Fin 3, (Pi.single 0 1 : Fin 3 → ℂ) i * (Pi.single 0 1 : Fin 3 → ℂ) i - 1 = 0 := by
        simp [Pi.single_apply]
      rw [this, norm_zero]; exact hδpos
  have hα : ∀ w : G.Ω 1, ‖(0 : G.Ω 1 → ℂ) w‖ <
      coerciveConst 3 / (2 * (G.spacing (w : CTorus 3 3 6 m₁ (1 + 1))) ^ 2) := by
    intro w
    simp only [Pi.zero_apply, norm_zero]
    have := coerciveConst_pos (by norm_num : 0 < 3)
    have hs := spacing_pos G (x := (w : CTorus 3 3 6 m₁ (1 + 1)))
    positivity
  have hN : (3 : ℕ) ^ 0 ∣ 6 := by norm_num
  refine ⟨m₁, rhoSep m₁, G, y, κ, δ, fun _ => Pi.single 0 1, 0, S, GP_hatConn, hN, hκ, hc,
    hδpos.le, hsm, hφ, hα, hz, ?_, ?_, ?_⟩
  · exact sum_detActivity_eq (m₀ := 0) (N := 3) S hκ hc hδpos.le hsm hφ hα y
  · intro Y hY
    exact detActivity_ne_zero_imp (m₀ := 0) S hκ hc hδpos.le hsm hφ hα GP_hatConn hN hY
  · intro Y
    have := norm_detActivity_le (m₀ := 0) (N := 3) S hκ hc hδpos.le hsm hφ hα GP_hatConn hN y hz Y
    simpa [hΔ] using this

end Balaban.Inhabited
