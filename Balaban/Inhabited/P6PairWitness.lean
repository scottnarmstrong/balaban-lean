/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6ActiveHalo
public import Balaban.Localization.MooreDegree
public import Balaban.Localization.LedgerPacking
import Balaban.LargeField.R.WindowOfHistory

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

/-- The index `(k + 1, 0)` (top layer, site `0`) belongs to `cubeIdx F♯`: the index set of the
cover is nonempty. -/
theorem top_mem_cubeIdx : ((1 + 1, 0) : ℕ × CTorus d 3 (15 * n1) 2 (1 + 1)) ∈ cubeIdx (pairCover d n1) := by
  have h0 : (0 : CTorus d 3 (15 * n1) 2 (1 + 1)) ∈ topCell 1 (1 + 1, (0 : CTorus d 3 (15 * n1) 2 (1 + 1))) :=
    mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  have hΩ : (0 : CTorus d 3 (15 * n1) 2 (1 + 1)) ∈ (pairCover d n1).Ω (1 + 1) :=
    Finset.mem_coe.1 (active_top_halo d n1 0 0 ⟨0, h0, 0, h0, ⟨0, fun _ => by simp, by funext μ; simp⟩⟩ h0)
  refine (mem_cubeIdx _).2 ⟨⟨by norm_num, le_rfl⟩, ?_, fun μ => by simp⟩
  exact (pairCover d n1).mem_layer.2 ⟨hΩ, by rw [(pairCover d n1).top]; simp⟩

open Classical in
/-- The root count of `p6_root_patch_count` is at least `1` at the site `0`: the patch of the
index `(k + 1, 0)` Moore-touches the active top cell of `0`. -/
theorem root_patch_count_pos :
    1 ≤ ((cubeIdx (pairCover d n1)).filter
        fun P => MooreTouch (topCell 1 (1 + 1, (0 : CTorus d 3 (15 * n1) 2 (1 + 1)))) (Pset 2 P)).card := by
  refine Finset.card_pos.2 ⟨(1 + 1, 0), Finset.mem_filter.2 ⟨top_mem_cubeIdx d n1, ?_⟩⟩
  have h0 : (0 : CTorus d 3 (15 * n1) 2 (1 + 1)) ∈ topCell 1 (1 + 1, (0 : CTorus d 3 (15 * n1) 2 (1 + 1))) :=
    mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  exact ⟨0, h0, 0, self_mem_Pset (1 + 1, (0 : CTorus d 3 (15 * n1) 2 (1 + 1))), ⟨0, fun _ => by simp, by funext μ; simp⟩⟩

end P6PairWitness

/-! ### A nonempty old large-field region -/

namespace Slab

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale

variable (n1 : ℕ) [NeZero n1]

/-- The old large-field region `Z`: the slab `{x | |x₀| ≤ 60}` of the torus of side `3 n₁`
(dimension `3`). -/
def slab : Set (Torus 3 (3 * n1)) := {x | cycNorm (3 * n1) (x 0) ≤ 60}

/-- The region step with old region the slab and no new cubes. -/
def step : RegionStep 3 3 (3 * n1) n1 9 0 where
  Z := slab n1
  P := ∅
  Q := ∅
  R := ∅
  S := ∅
  P_sub := Set.empty_subset _
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := Set.empty_subset _

/-- The coordinate-`0` size of a point of `nbhd 3 U'_k` is at most `27` (for `n₁ = 100`). -/
theorem cyc_le_of_mem_nbhd_uprime (hn1 : n1 = 100) {y : Torus 3 n1}
    (hy : y ∈ nbhd 3 (step n1).Uprime) : cycNorm n1 (y 0 - 0) ≤ 27 := by
  subst hn1
  obtain ⟨u', ⟨w, hw, rfl⟩, hyu⟩ := mem_nbhd.1 hy
  have hf : ⌊(9 : ℝ)⌋₊ = 9 := by norm_num
  obtain ⟨z, hz, hwz⟩ := mem_nbhd.1 hw
  have h1 : cycNorm (3 * 100) (w 0 - 0) ≤ 70 := by
    have := cycNorm_sub_le (n := 3 * 100) (w 0) (z 0) 0
    have h2 := cycNorm_le_supDist w z 0
    have h3 : cycNorm (3 * 100) (z 0) ≤ 60 := hz
    have h4 : supDist w z ≤ 10 := by
      have : supDist w z ≤ ⌊(9 : ℝ)⌋₊ + 1 := hwz
      omega
    simp only [sub_zero] at this ⊢
    omega
  have h2 := cycNorm_blockCoord_le (L := 3) (m := 100) rfl (w 0) 0 h1
  have h3 : blockCoord 3 100 (0 : ZMod (3 * 100)) = 0 := by simp [blockCoord]
  rw [h3] at h2
  have h4 := cycNorm_le_supDist y (blockMap 3 100 w) 0
  have h5 := cycNorm_sub_le (n := 100) (y 0) (blockMap 3 100 w 0) 0
  have hb : blockMap 3 100 w 0 = blockCoord 3 100 (w 0) := rfl
  rw [hb] at h4 h5
  simp only [sub_zero] at h2 h5 ⊢
  omega

/-- The coarse point with first coordinate `50`, all others `0`. -/
def u0 : Torus 3 n1 := fun i => if i = 0 then 50 else 0

/-- The point `u0` lies in the new active region `Ω_{k+1}` of the step (for `n₁ = 100`). -/
theorem u0_mem_omega (hn1 : n1 = 100) : u0 n1 ∈ (step n1).Omega := by
  have hf : ⌊(0 : ℝ)⌋₊ = 0 := by norm_num
  refine ⟨u0 n1, ⟨fun _ => 0, fun _ => by norm_num, by funext i; simp⟩, ?_, ?_⟩
  · intro a ha
    refine ⟨u0 n1, ha, ?_⟩
    rw [le_setDist_iff]
    intro a' ha' y hy
    obtain ⟨v, hv, rfl⟩ := ha'
    have h1 := cyc_le_of_mem_nbhd_uprime n1 hn1 hy
    subst hn1
    have h2 := cycNorm_sub_le (n := 100) (u0 100 0 + ((v 0 : ℕ) : ZMod 100)) (y 0) 0
    have h3 : cycNorm 100 (u0 100 0 + ((v 0 : ℕ) : ZMod 100) - y 0) ≤
        supDist (fun i => u0 100 i + (v i : ZMod 100)) y :=
      cycNorm_le_supDist (fun i => u0 100 i + (v i : ZMod 100)) y 0
    have h4 : 48 ≤ cycNorm 100 (u0 100 0 + ((v 0 : ℕ) : ZMod 100) - 0) := by
      have := hv 0
      interval_cases (v 0) <;> simp [u0] <;> decide
    simp only [sub_zero] at h2 h4 h1
    omega
  · rw [le_setDist_iff]
    intro a' _ y hy
    have : (step n1).P = ∅ := rfl
    rw [this, nbhd_empty] at hy
    exact absurd hy (Set.notMem_empty _)

/-- The cover `F♯` of the slab setting. -/
noncomputable def cover : GeneratingSet 3 3 ((15 * n1) * 3 ^ 2) (1 + 1) (minSep 3 9) :=
  p6FsharpC (k := 1) (m₁ := 2) (n0 := 3 * n1) (M1 := 9) (c := 15) (n1 := n1) (L := 3)
    (Z := (step n1).Z) rfl P6PairWitness.hρ9 (by norm_num) P6PairWitness.hM9

/-- The fine site over `u0`: first coordinate `50 · 1215`, all others `0`. -/
def ustar : CTorus 3 3 (15 * n1) 2 (1 + 1) := fun i => if i = 0 then 60750 else 0

omit [NeZero n1] in
/-- The coarse point under the fine site `ustar` is `u0`. -/
theorem ustar_blockMap (hn1 : n1 = 100) : blockMap (3 ^ (1 + 1) * (15 * 9)) n1
      (LargeField.torusCast (by ring : (15 * n1) * 3 ^ 2 * 3 ^ (1 + 1) =
        9 * (15 * n1) * 3 ^ (1 + 1)) (ustar n1)) = u0 n1 := by
  subst hn1
  funext i
  fin_cases i <;> decide

theorem halo (hn1 : n1 = 100) (z : CTorus 3 3 (15 * n1) 2 (1 + 1))
    (hz : MooreTouch (topCell 1 (1 + 1, ustar n1)) (topCell 1 (1 + 1, z))) :
    topCell 1 (1 + 1, z) ⊆ ↑((cover n1).Ω (1 + 1)) :=
  p6_active_top_halo (step n1) P6PairWitness.hM9 P6PairWitness.hmc15 rfl (by norm_num)
    P6PairWitness.hρ9 (by norm_num) (ustar n1)
    (by rw [mem_fineK1]; exact (ustar_blockMap n1 hn1) ▸ u0_mem_omega n1 hn1) z hz

theorem touch_layer (hn1 : n1 = 100) {P : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)}
    (hP : P ∈ cubeIdx (cover n1))
    (hT : MooreTouch (topCell 1 (1 + 1, ustar n1)) (Pset 2 P)) : P.1 = 1 + 1 :=
  p6_touch_active_layer (step n1) P6PairWitness.hM9 P6PairWitness.hmc15 rfl (by norm_num)
    P6PairWitness.hρ9 (by norm_num) (ustar n1)
    (by rw [mem_fineK1]; exact (ustar_blockMap n1 hn1) ▸ u0_mem_omega n1 hn1) hP hT

open Classical in
theorem root_count (hn1 : n1 = 100) :
    ((cubeIdx (cover n1)).filter
        fun P => MooreTouch (topCell 1 (1 + 1, ustar n1)) (Pset 2 P)).card ≤ 3 ^ 3 * (3 ^ 1) ^ 3 :=
  p6_root_patch_count (step n1) P6PairWitness.hM9 P6PairWitness.hmc15 rfl (by norm_num)
    P6PairWitness.hρ9 (by norm_num) (ustar n1)
    (by rw [mem_fineK1]; exact (ustar_blockMap n1 hn1) ▸ u0_mem_omega n1 hn1)

theorem moore_layer_gap {P Q : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)}
    (hP : P ∈ cubeIdx (cover n1)) (hQ : Q ∈ cubeIdx (cover n1))
    (h : MooreTouch (Pset 2 P) (Pset 2 Q)) : P.1 ≤ Q.1 + 1 ∧ Q.1 ≤ P.1 + 1 :=
  cubeIdx_moore_layer_gap_p6 (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl P6PairWitness.hρ9
    (by norm_num) (step n1).Z P6PairWitness.hM9 le_rfl (by norm_num) hP hQ h

open Classical in
theorem moore_degree {P : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)} (hP : P ∈ cubeIdx (cover n1)) :
    ((cubeIdx (cover n1)).filter
        fun Q => Q ≠ P ∧ MooreTouch (Pset 2 P) (Pset 2 Q)).card ≤ 3 * (3 + 4) ^ 3 :=
  cubeIdx_moore_degree_p6 (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl P6PairWitness.hρ9
    (by norm_num) (step n1).Z P6PairWitness.hM9 le_rfl (by norm_num) hP

theorem layer_unique {j j' : ℕ} {y : CTorus 3 3 (15 * n1) 2 (1 + 1)}
    (h : (j, y) ∈ cubeIdx (cover n1)) (h' : (j', y) ∈ cubeIdx (cover n1)) : j = j' :=
  p6FsharpC_cubeIdx_layer_unique (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl
    P6PairWitness.hρ9 (by norm_num) (step n1).Z P6PairWitness.hM9 h h'

omit [NeZero n1] in
theorem ustar_base (hn1 : n1 = 100) : ∀ μ, ((ustar n1) μ).val % 3 ^ (1 + 1 + 2) = 0 := by
  subst hn1
  intro μ
  fin_cases μ <;> decide

theorem top_mem_cubeIdx (hn1 : n1 = 100) :
    ((1 + 1, ustar n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)) ∈ cubeIdx (cover n1) := by
  have h0 : ustar n1 ∈ topCell 1 (1 + 1, ustar n1) := mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  have hΩ : ustar n1 ∈ (cover n1).Ω (1 + 1) :=
    Finset.mem_coe.1 (halo n1 hn1 (ustar n1) ⟨ustar n1, h0, ustar n1, h0,
      ⟨0, fun _ => by simp, by funext μ; simp⟩⟩ h0)
  exact (mem_cubeIdx _).2 ⟨⟨by norm_num, le_rfl⟩,
    (cover n1).mem_layer.2 ⟨hΩ, by rw [(cover n1).top]; simp⟩, ustar_base n1 hn1⟩

open Classical in
theorem root_count_pos (hn1 : n1 = 100) :
    1 ≤ ((cubeIdx (cover n1)).filter
        fun P => MooreTouch (topCell 1 (1 + 1, ustar n1)) (Pset 2 P)).card := by
  refine Finset.card_pos.2 ⟨(1 + 1, ustar n1), Finset.mem_filter.2 ⟨top_mem_cubeIdx n1 hn1, ?_⟩⟩
  have h0 : ustar n1 ∈ topCell 1 (1 + 1, ustar n1) := mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  exact ⟨ustar n1, h0, ustar n1, self_mem_Pset (1 + 1, ustar n1),
    ⟨0, fun _ => by simp, by funext μ; simp⟩⟩

/-! #### An index below the top layer -/

/-- A fine site deep in the old large-field region's collar: first coordinate `41 · 405`. -/
def ylow : CTorus 3 3 (15 * n1) 2 (1 + 1) := fun i => if i = 0 then 16605 else 0

omit [NeZero n1] in
theorem ylow_base (hn1 : n1 = 100) : ∀ μ, ((ylow n1) μ).val % 3 ^ (1 + 2) = 0 := by
  subst hn1
  intro μ
  fin_cases μ <;> decide

theorem ylow_near (hn1 : n1 = 100) :
    blockMap (3 ^ 1 * (15 * 9)) (3 * n1)
      (LargeField.torusCast (by ring : (15 * n1) * 3 ^ 2 * 3 ^ (1 + 1) =
        9 * (15 * n1) * 3 ^ (1 + 1)) (ylow n1)) ∈ nbhd (2 * (⌊(9 : ℝ)⌋₊ + 1)) (step n1).Zᶜ := by
  subst hn1
  have hf : ⌊(9 : ℝ)⌋₊ = 9 := by norm_num
  let zpt : Torus 3 (3 * 100) := fun i => if i = 0 then 61 else 0
  let ppt : Torus 3 (3 * 100) := fun i => if i = 0 then 41 else 0
  have e : blockMap (3 ^ 1 * (15 * 9)) (3 * 100)
      (LargeField.torusCast (by ring : (15 * 100) * 3 ^ 2 * 3 ^ (1 + 1) =
        9 * (15 * 100) * 3 ^ (1 + 1)) (ylow 100)) = ppt := by
    funext i
    fin_cases i <;> decide
  have e1 : ¬ cycNorm (3 * 100) (zpt 0) ≤ 60 := by decide
  have e2 : ∀ i, cycNorm (3 * 100) (ppt i - zpt i) ≤ 20 := by
    intro i
    fin_cases i <;> decide
  rw [e]
  refine mem_nbhd.2 ⟨zpt, e1, ?_⟩
  rw [hf]
  exact supDist_le_iff.2 e2

theorem ylow_mem_Ω_one (hn1 : n1 = 100) : ylow n1 ∈ (cover n1).Ω 1 := by
  unfold cover p6FsharpC
  rw [castN_mem (p6_side P6PairWitness.hM9),
    p6Fsharp_Ω_of_le (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl P6PairWitness.hρ9
      (by norm_num) (step n1).Z (le_refl 1),
    p6Hold_Ω_k (k := 1) (n0 := 3 * n1) (M1 := 9) (c := 15) rfl]
  show _ ∈ fineK 9 15 n1 3 1 (3 * n1) (thick2 _ _)
  rw [mem_fineK, thick2_eq]
  exact ylow_near n1 hn1

end Slab

end Balaban.Inhabited
