/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LocalizationSettings
public import Balaban.Localization.YregBlocks
public import Balaban.Fluctuation.RootDetCutSupport
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of `YregBlocks`

On the positive witness geometry of `LocalizationSettings.lean` (`d = L = 3`, `N₁ = 6`, `k = 1`,
`G = GP m₁ (rhoSep m₁)`, `Ω₁ = Ω₂ = 𝕋`), the cut point that switches on the footprint of the centre
`(2, 0)` has a non-empty `Yreg`, and `Yreg` is a union of nearest-neighbour components (of itself)
that is a union of blocks (`UnionOfBlocks`, obtained from `unionOfBlocks_of_isNnComp`).

Here the generating set has a single layer (the top one), so `UnionOfTopBlocks` and `UnionOfBlocks`
coincide; the witness does not exercise lower layers.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Fluctuation Balaban.Analysis

/-- **Non-vacuity of the components-are-unions-of-blocks theorem.** There is a witness geometry, a
cut point with non-empty `Yreg`, and a union `Y'` of components of it (here `Y' = Yreg`) with
`UnionOfBlocks G Y'`. -/
theorem yregBlocks_nonempty :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ)
      (J : Finset (cubeIdx G)),
      XSetting G (compWeight 3 1) 1 0 ∧ HatConn G ∧
      (Yreg G (extS G (cutPt J))).Nonempty ∧
      IsNnComp (Yreg G (extS G (cutPt J))) (Yreg G (extS G (cutPt J))) ∧
      UnionOfBlocks G (Yreg G (extS G (cutPt J))) := by
  classical
  obtain ⟨m₁, h4, -⟩ := exists_m₁_cstar
  have S := xSetting_pos h4
  set G := GP m₁ (rhoSep m₁) with hG
  have hz : ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) ∈ cubeIdx G := by
    rw [mem_cubeIdx]
    refine ⟨⟨by norm_num, by norm_num⟩, ?_, fun μ => by simp⟩
    show (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.layer 2
    rw [hG, GP_layer_two]; exact Finset.mem_univ _
  have hmem : (0 : CTorus 3 3 6 m₁ (1 + 1)) ∈ hatBox ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1))) := by
    unfold hatBox
    rw [mem_boxSet]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (3 : ℝ) ^ (2 + m₁) := one_le_pow₀ (by norm_num)
    simp only [Int.cast_zero, zero_mul, add_zero]
    unfold hatRad
    have h0 : (((0 : CTorus 3 3 6 m₁ (1 + 1)) μ).val : ℝ) = 0 := by simp
    rw [h0, zero_add, zero_sub, abs_neg, abs_of_nonneg (by push_cast; linarith)]
    push_cast
    have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ 2 := by positivity
    linarith
  have hΩ : ∀ y : G.Ω 1, (y : CTorus 3 3 6 m₁ (1 + 1)) ∈ G.layer (1 + 1) := fun y => by
    exact (Finset.ext_iff.1 (GP_layer_two (m₁ := m₁) (ϱ := rhoSep m₁)) _).2 (Finset.mem_univ _)
  refine ⟨m₁, rhoSep m₁, G, (Qset G ((2 : ℕ), (0 : CTorus 3 3 6 m₁ (1 + 1)))).subtype
    (· ∈ cubeIdx G), S, GP_hatConn, ?_, ⟨Finset.Subset.refl _, fun x hx y hy _ => hy⟩,
    unionOfBlocks_of_isNnComp S.dg GP_hatConn hΩ ⟨Finset.Subset.refl _, fun x hx y hy _ => hy⟩⟩
  refine ⟨0, hatI_subset_Yreg_cutPt hz ?_⟩
  unfold hatI
  rw [Finset.mem_filter]
  exact ⟨hmem, by rw [hG, GP_Ω]; simp⟩

end Balaban.Inhabited
