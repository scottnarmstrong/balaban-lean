/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSolveAnalytic
public import Balaban.Localization.DecoupledGeometry
public import Balaban.Localization.BoxConn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-4a (e): locality of the decoupled perturbed system

* Item 0: `HatConn` (the thickened interaction cubes are nearest-neighbour connected inside `Ω₁`)
  holds for the centres of layer `≥ 2`, where `□̂_z ⊂ Ω₁` (`hatConn_of_layer_one`); it remains a
  hypothesis for the centres of layer `1`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Item0

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The thickened interaction cube of a centre of layer `≥ 2` lies in `Ω₁`. -/
theorem hatBox_subset_Omega (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (hq2 : 2 ≤ q.1) {y : CTorus d L N₁ m₁ K} (hy : y ∈ hatBox q) :
    y ∈ G.Ω 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast S.hM
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 :=
    one_le_pow₀ (by linarith)
  have hlam : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ q.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  have key : hatRad L m₁ q.1 + (L : ℝ) ^ (q.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (q.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ q.1)
    rw [hlam] at *
    nlinarith
  have hbox : InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y := by
    unfold hatBox at hy
    exact mem_boxSet.1 hy
  have hdist := torusDist_le_of_inBox hbox
  have h4 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y q.2 ≤ 4 * d * (L : ℝ) ^ (q.1 + m₁) := by
    refine hdist.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left key hd1]
  have hq2Ω : q.2 ∈ G.Ω q.1 := (G.mem_layer.1 hl).1
  have := mem_pred_cube m₁ G S.cover_sep hq2 hmK hq2Ω (by
    rw [Green.torusDist_comm_gen]; exact h4)
  exact G.Ω_antitone le_rfl (by omega) (by omega) this

/-- **Item 0.**  The thickened interaction cubes of the centres of layer `≥ 2` are
nearest-neighbour connected inside `Ω₁` (they lie in `Ω₁` and are boxes); only the centres of
layer `1` need the regularity hypothesis. -/
theorem hatConn_of_layer_one (S : DGSetting G a ν)
    (h1 : ∀ q ∈ cubeIdx G, q.1 = 1 → ConnIn (hatI G q)) : HatConn G := by
  classical
  intro q hq
  by_cases hq1 : q.1 = 1
  · exact h1 q hq hq1
  · obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
    have hq2 : 2 ≤ q.1 := by omega
    have hI : hatI G q = hatBox q := by
      unfold hatI
      exact Finset.filter_true_of_mem fun y hy => hatBox_subset_Omega S hq hq2 hy
    rw [hI]
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
    have hLj : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by linarith)
    have hR : 1 ≤ hatRad L m₁ q.1 := by
      unfold hatRad
      have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
      linarith
    exact boxSet_connected q.2 hR

end Item0

end Balaban.Localization
