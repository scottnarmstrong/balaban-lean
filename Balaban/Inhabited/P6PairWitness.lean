/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6ActiveHalo
public import Balaban.Localization.MooreDegree
public import Balaban.Localization.LedgerPacking

/-!
# A concrete setting for the P6 pair cover `F♯`

This file exhibits one concrete setting in which all numerical and geometric premises of the
theorems about the P6 pair cover `F♯ = p6FsharpC` hold together, and instantiates those theorems.
It is an instance of the cover geometry only: nothing is stated about the P6 boundary terms
themselves.

The data: dimension `d` (arbitrary), `L = 3`, step index `k = 1` (so the cover has top layer
`k + 1 = 2`), `c = 15 = 5 L` (so `L ^ 1 ∣ c`, i.e. `m₀ = 1`), `m₁ = 2`, `M₁ = 9 = L ^ 2`, the old
radius `R_{k-1} = 9` (so `⌊R_{k-1}⌋ = 9 = 3 L`) and new radius `R_k = 0`.  The step is a
`RegionStep` with `P = Q = R = S = ∅` and old large-field region `Z = ∅`.
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6PairWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale

variable (d n1 : ℕ)

/-- The region step: no old large-field region, no new cubes. -/
def stepZ0 : RegionStep d 3 (3 * n1) n1 9 0 where
  Z := ∅
  P := ∅
  Q := ∅
  R := ∅
  S := ∅
  P_sub := Set.empty_subset _
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := Set.empty_subset _

/-- With `Z = ∅` the new active region is the whole torus. -/
theorem omega_stepZ0 : (stepZ0 d n1).Omega = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  have hU : (stepZ0 d n1).Uprime = ∅ := by
    show Region.Uprime 3 n1 _ (∅ : Set (Torus d (3 * n1))) = ∅
    simp [Region.Uprime, Region.U, thick, nbhd_empty]
  refine ⟨y, ⟨fun _ => 0, fun _ => by norm_num, by funext i; simp⟩, ?_, ?_⟩
  · intro z hz
    refine ⟨y, hz, ?_⟩
    show _ ≤ setDist _ (nbhd 3 (stepZ0 d n1).Uprime)
    rw [hU, nbhd_empty, setDist_eq_top_iff.mpr (Or.inr rfl)]
    exact le_top
  · show _ ≤ setDist _ (nbhd 3 (∅ : Set (Torus d n1)))
    rw [nbhd_empty, setDist_eq_top_iff.mpr (Or.inr rfl)]
    exact le_top

variable [NeZero n1]

/-- `⌊R_{k-1}⌋ = 9 = 3 L`. -/
theorem hρ9 : 3 * 3 ≤ ⌊(9 : ℝ)⌋₊ := by norm_num

/-- `M₁ = 9 = L ^ m₁` with `m₁ = 2`. -/
theorem hM9 : (9 : ℕ) = 3 ^ 2 := by norm_num

/-- `L ^ m₀ ∣ c` with `m₀ = 1`, `c = 15`. -/
theorem hmc15 : 3 ^ 1 ∣ 15 := by norm_num

/-- The cover `F♯ = p6FsharpC` of the concrete setting: `L = 3`, `k = 1`, `c = 15`, `m₁ = 2`,
`M₁ = 9`, `Z = ∅`, on the cover torus of side `15 n₁ 3 ^ 2 3 ^ 2`. -/
noncomputable def pairCover : GeneratingSet d 3 ((15 * n1) * 3 ^ 2) (1 + 1) (minSep 3 9) :=
  p6FsharpC (k := 1) (m₁ := 2) (n0 := 3 * n1) (M1 := 9) (c := 15) (n1 := n1) (L := 3)
    (Z := (stepZ0 d n1).Z) rfl hρ9 (by norm_num) hM9

/-- Every fine site of the cover torus lies over the new active region (which is everything). -/
theorem site_over_omega (u : CTorus d 3 (15 * n1) 2 (1 + 1)) :
    LargeField.torusCast (by rw [p6_side hM9] : (15 * n1) * 3 ^ 2 * 3 ^ (1 + 1) =
        9 * (15 * n1) * 3 ^ (1 + 1)) u ∈ fineK1 9 15 n1 3 1 (stepZ0 d n1).Omega := by
  rw [mem_fineK1, omega_stepZ0]
  trivial

/-- `p6_active_top_halo` at the concrete setting, for every site `u` and every `z`. -/
theorem active_top_halo (u z : CTorus d 3 (15 * n1) 2 (1 + 1))
    (hz : MooreTouch (topCell 1 (1 + 1, u)) (topCell 1 (1 + 1, z))) :
    topCell 1 (1 + 1, z) ⊆ ↑((pairCover d n1).Ω (1 + 1)) :=
  p6_active_top_halo (stepZ0 d n1) hM9 hmc15 rfl (by norm_num) hρ9 (by norm_num) u
    (site_over_omega d n1 u) z hz

/-- `p6_touch_active_layer` at the concrete setting. -/
theorem touch_active_layer (u : CTorus d 3 (15 * n1) 2 (1 + 1))
    {P : ℕ × CTorus d 3 (15 * n1) 2 (1 + 1)} (hP : P ∈ cubeIdx (pairCover d n1))
    (hT : MooreTouch (topCell 1 (1 + 1, u)) (Pset 2 P)) : P.1 = 1 + 1 :=
  p6_touch_active_layer (stepZ0 d n1) hM9 hmc15 rfl (by norm_num) hρ9 (by norm_num) u
    (site_over_omega d n1 u) hP hT

open Classical in
/-- `p6_root_patch_count` at the concrete setting. -/
theorem root_patch_count (u : CTorus d 3 (15 * n1) 2 (1 + 1)) :
    ((cubeIdx (pairCover d n1)).filter
        fun P => MooreTouch (topCell 1 (1 + 1, u)) (Pset 2 P)).card ≤ 3 ^ d * (3 ^ 1) ^ d :=
  p6_root_patch_count (stepZ0 d n1) hM9 hmc15 rfl (by norm_num) hρ9 (by norm_num) u
    (site_over_omega d n1 u)

/-- `d < 5 L ^ 3 M₁` once `d < 1215`. -/
theorem moore_dim (hd : d < 1215) : d < 5 * 3 ^ 3 * 9 := by omega

/-- `cubeIdx_moore_layer_gap_p6` at the concrete setting (`d < 1215`). -/
theorem moore_layer_gap (hd : d < 1215) {P Q : ℕ × CTorus d 3 (15 * n1) 2 (1 + 1)}
    (hP : P ∈ cubeIdx (pairCover d n1)) (hQ : Q ∈ cubeIdx (pairCover d n1))
    (h : MooreTouch (Pset 2 P) (Pset 2 Q)) : P.1 ≤ Q.1 + 1 ∧ Q.1 ≤ P.1 + 1 :=
  cubeIdx_moore_layer_gap_p6 (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl hρ9
    (by norm_num) (stepZ0 d n1).Z hM9 le_rfl (moore_dim d hd) hP hQ h

open Classical in
/-- `cubeIdx_moore_degree_p6` at the concrete setting (`d < 1215`). -/
theorem moore_degree (hd : d < 1215) {P : ℕ × CTorus d 3 (15 * n1) 2 (1 + 1)}
    (hP : P ∈ cubeIdx (pairCover d n1)) :
    ((cubeIdx (pairCover d n1)).filter
        fun Q => Q ≠ P ∧ MooreTouch (Pset 2 P) (Pset 2 Q)).card ≤ 3 * (3 + 4) ^ d :=
  cubeIdx_moore_degree_p6 (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl hρ9
    (by norm_num) (stepZ0 d n1).Z hM9 le_rfl (moore_dim d hd) hP

/-- `p6FsharpC_cubeIdx_layer_unique` at the concrete setting. -/
theorem layer_unique {j j' : ℕ} {y : CTorus d 3 (15 * n1) 2 (1 + 1)}
    (h : (j, y) ∈ cubeIdx (pairCover d n1)) (h' : (j', y) ∈ cubeIdx (pairCover d n1)) :
    j = j' :=
  p6FsharpC_cubeIdx_layer_unique (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl hρ9
    (by norm_num) (stepZ0 d n1).Z hM9 h h'

end P6PairWitness

end Balaban.Inhabited
