/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6TopRootedFiber
public import Balaban.Inhabited.P6TopWitness

/-!
# Non-vacuity of the rooted sum on the `m₁ = 2` slab setting

Setting of `P6TopWitness.Cell`: `d = L = 3`, `N₁ = 15 * 100`, `m₁ = 2`, `K = 2`, `m₀ = 1`,
`ϱ = 3`.  Here `D = max (3 · 7³ + 1) (27 · 27) = 1030`, and `κ₂ = 15` gives `z = D² e^{-15} < 1`.
`R` is the single top cell of the fine site `ylow` (in the hole).  The rooted family contains the
non-empty set consisting of one patch touching that cell, so the sum is not only the empty set's
term.  Cover geometry only; nothing is stated about the P6 boundary terms.
-/

@[expose] public section

namespace Balaban.Inhabited.P6TopWitness.Cell

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Slab

theorem topD_eq : topD 3 3 1 = 1030 := by norm_num [topD]

theorem hz_15 : ((topD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-15) < 1 := by
  rw [topD_eq, Real.exp_neg]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h15 : (2.7 : ℝ) ^ 15 < Real.exp 15 := by
    rw [show (15 : ℝ) = (15 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have hp := Real.exp_pos 15
  rw [← div_eq_mul_inv, div_lt_one hp]
  push_cast
  nlinarith [h15]

open Classical in
/-- The rooted family at `R = {top cell of ylow}` is non-empty beyond `∅`, and the rooted sum and
its exponential form hold with `κ₂ = 15`. -/
theorem top_rooted_instance (n1 : ℕ) [NeZero n1] (hn1 : n1 = 100) :
    ∃ P : {P // P ∈ cubeIdx (topCover n1)},
      ({P} : Finset _) ∈ rootedSets (G := mooreGraph (topCover n1))
        (⋃ u ∈ ({ylow n1} : Finset _),
          (topRootNbhd 3 3 (15 * n1) 2 (1 + 1) (3 : ℝ) 1 u : Set _)) ∧
    ∑ C ∈ rootedSets (G := mooreGraph (topCover n1))
        (⋃ u ∈ ({ylow n1} : Finset _),
          (topRootNbhd 3 3 (15 * n1) 2 (1 + 1) (3 : ℝ) 1 u : Set _)), Real.exp (-15 * C.card)
      ≤ Real.exp (-Real.log (1 - ((topD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-15)) * 1) *
        Real.exp (-Real.log (1 - ((topD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-15)) * 1 * 0) := by
  have hN : 3 ^ 1 ∣ 15 * n1 := (by norm_num : 3 ^ 1 ∣ 15).mul_right n1
  have hP : ((1 + 1, ylow n1) : ℕ × _) ∈ cubeIdx (topCover n1) := by
    refine (mem_cubeIdx _).2 ⟨⟨by norm_num, le_rfl⟩, ?_, ?_⟩
    · exact (topCover n1).mem_layer.2 ⟨mem_topGS_Ω le_rfl _, not_mem_topGS_Ω (by omega) _⟩
    · subst hn1
      intro μ
      fin_cases μ <;> decide
  have h0 : ylow n1 ∈ topCell 1 (1 + 1, ylow n1) := mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  have htouch : MooreTouch (topCell 1 (1 + 1, ylow n1)) (Pset 2 ((1 + 1, ylow n1) : ℕ × _)) :=
    ⟨ylow n1, h0, ylow n1, self_mem_Pset (1 + 1, ylow n1),
      ⟨0, fun _ => by simp, by funext μ; simp⟩⟩
  refine ⟨⟨_, hP⟩, ?_, ?_⟩
  · rw [mem_rootedSets_top_iff]
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact ⟨⟨_, hP⟩, WalkIn.refl (Finset.mem_singleton_self _), ylow n1, Finset.mem_singleton_self _,
      htouch⟩
  · exact top_rooted_sum_le_of_rootCount (K := 1 + 1) (ϱ := 3) hN le_rfl (by norm_num)
      {ylow n1} hz_15 (c_R := 1) (Δ := 0) (by simp)

end Balaban.Inhabited.P6TopWitness.Cell
