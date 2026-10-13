/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6FsharpRootedCount
public import Balaban.Inhabited.P6PairWitness

/-!
# The slab setting for the rooted counts of `F♯`

Cover geometry and counting only.  In the slab setting of `Inhabited/P6PairWitness.lean`
(`d = L = 3`, `k + 1 = 2`, `m₁ = 2`, `m₀ = 1`, `n₁ = 100`) the fine site `ustar` is an active top
cell.  We show that its root neighbourhood is nonempty, has at most `3^3 (3^1)^3` patches, all of
layer `2`; that the singleton consisting of the top patch `(2, ustar)` is a rooted set; that the
constant is `D = 1030` and `D² exp (-14) < 1` (so `κ₂ = 14` is admissible); and that the rooted
sum and the layer tail bounds hold with these data.

A rooted set containing a layer-`1` patch has many more than `2` members here: the layer-`1`
patches lie outside the halo, at least one block of side `1215` away from an active cell, while a
patch has side `81`; the bound `k + 1 - j + 1` of the layer tail is only a lower bound.
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6FsharpRootedWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale Balaban.Polymer
open Slab

/-- The cover `F♯` of the slab setting, spelled as `p6FsharpC` (the same term as `Slab.cover`). -/
noncomputable abbrev Fs (n1 : ℕ) [NeZero n1] : GeneratingSet 3 3 ((15 * n1) * 3 ^ 2) (1 + 1) (minSep 3 9) :=
  p6FsharpC (k := 1) (m₁ := 2) (n0 := 3 * n1) (M1 := 9) (c := 15) (n1 := n1) (L := 3)
    (Z := (step n1).Z) rfl P6PairWitness.hρ9 (by norm_num) P6PairWitness.hM9

theorem hD : fsharpD 3 3 1 = 1030 := by norm_num [fsharpD]

/-- `D² exp (-14) < 1` for `D = 1030`. -/
theorem hz14 : ((fsharpD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-14) < 1 := by
  rw [hD, Real.exp_neg]
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : (2.7 : ℝ) ^ 14 < Real.exp 1 ^ 14 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h3 : Real.exp 14 = Real.exp 1 ^ 14 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← h3] at h2
  have h4 : (0 : ℝ) < Real.exp 14 := Real.exp_pos _
  rw [mul_inv_lt_iff₀ h4]
  push_cast
  nlinarith [h2]

open Classical in
/-- **T5.**  The slab instance of the rooted counts for `F♯` at the active cell `ustar`. -/
theorem slab_instance (n1 : ℕ) [NeZero n1] (hn1 : n1 = 100) :
    let N := fsharpRootNbhd (k := 1) (m₁ := 2) (n0 := 3 * n1) (M1 := 9) (c := 15) (n1 := n1)
      (L := 3) rfl P6PairWitness.hρ9 (by norm_num) (step n1).Z P6PairWitness.hM9 1 (ustar n1)
    N.Nonempty ∧ N.card ≤ 3 ^ 3 * (3 ^ 1) ^ 3 ∧ (∀ P ∈ N, P.1.1 = 1 + 1) ∧
    (∃ C ∈ rootedSets (G := mooreGraph (Fs n1)) (⋃ u ∈ ({ustar n1} : Finset _), (N : Set _)),
      C.card = 1) ∧
    (∑ C ∈ rootedSets (G := mooreGraph (Fs n1)) (⋃ u ∈ ({ustar n1} : Finset _), (N : Set _)),
        Real.exp (-14 : ℝ) ^ C.card ≤
      (1 / (1 - ((fsharpD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-14))) ^ 1) ∧
    (∑ C ∈ (rootedSets (G := mooreGraph (Fs n1)) (N : Set _)).filter
        (fun C => ∃ P ∈ C, P.1.1 = 1),
        Real.exp (-14 : ℝ) ^ C.card ≤
      (((fsharpD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-14)) ^ (1 + 1 - 1 + 1) /
        (1 - ((fsharpD 3 3 1 : ℕ) : ℝ) ^ 2 * Real.exp (-14))) := by
  intro N
  have hu : LargeField.torusCast (by rw [p6_side P6PairWitness.hM9] :
        (15 * n1) * 3 ^ 2 * 3 ^ (1 + 1) = 9 * (15 * n1) * 3 ^ (1 + 1)) (ustar n1) ∈
        fineK1 9 15 n1 3 1 (step n1).Omega := by
    rw [mem_fineK1]; exact (ustar_blockMap n1 hn1) ▸ u0_mem_omega n1 hn1
  have hmem : ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)) ∈ cubeIdx (Fs n1) :=
    top_mem_cubeIdx n1 hn1
  have hP : (⟨(1 + 1, ustar n1), hmem⟩ : {P // P ∈ cubeIdx (Fs n1)}) ∈ N := by
    refine (mem_fsharpRootNbhd _ _ _ _ _ _ _).2 ?_
    have h0 : ustar n1 ∈ topCell 1 (1 + 1, ustar n1) := mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
    exact ⟨ustar n1, h0, ustar n1, self_mem_Pset (1 + 1, ustar n1),
      ⟨0, fun _ => by simp, by funext μ; simp⟩⟩
  refine ⟨⟨_, hP⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact card_fsharpRootNbhd_le (m₀ := 1) (step n1) P6PairWitness.hM9 P6PairWitness.hmc15 rfl
      (by norm_num) P6PairWitness.hρ9 (by norm_num) (ustar n1) hu
  · intro P hPN
    exact layer_eq_of_mem_fsharpRootNbhd (m₀ := 1) (step n1) P6PairWitness.hM9
      P6PairWitness.hmc15 rfl (by norm_num) P6PairWitness.hρ9 (by norm_num) (ustar n1) hu hPN
  · refine ⟨{⟨(1 + 1, ustar n1), hmem⟩}, ?_, by simp⟩
    rw [mem_rootedSets]
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv
    exact ⟨_, by simpa using hP, WalkIn.refl (Finset.mem_singleton_self _)⟩
  · have := fsharp_rooted_sum_le (m₀ := 1) (step n1) P6PairWitness.hM9 P6PairWitness.hmc15 rfl
      (by norm_num) P6PairWitness.hρ9 (by norm_num) le_rfl (by norm_num) {ustar n1}
      (by simpa using hu) (Real.exp_pos (-14)).le hz14
    simpa using this
  · exact fsharp_layer_tail_le (m₀ := 1) (step n1) P6PairWitness.hM9 P6PairWitness.hmc15 rfl
      (by norm_num) P6PairWitness.hρ9 (by norm_num) le_rfl (by norm_num) (ustar n1) hu 1
      (Real.exp_pos (-14)).le hz14

end P6FsharpRootedWitness

end Balaban.Inhabited
