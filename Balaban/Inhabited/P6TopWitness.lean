/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6TopPair
public import Balaban.Inhabited.P6PairWitness

/-!
# A concrete setting for the top-only cover `F^top` of the P6 pair

Cover geometry only; nothing is stated about the P6 boundary terms themselves.

* Namespace `Pair`: `L = 3`, `d = 3`, step index `k = 1` (cover top layer `2`), `c = 15`,
  `m₁ = 7` (`M₁ = 3^7`), region step `Slab.step n₁` of `Inhabited/P6PairWitness.lean`, `ν = 0`,
  `a ≡ 1`.  All four statements `Dec2.CoverGeom` and `Dec2.CoverBase` of `p6_coverGeom_top_*` and
  `p6_coverBase_top_*` hold for the landed operator pair `p6OldC`, `p6BoundaryC`.  The scale
  `m₁ = 7` is forced by the landed numerical premise `2 d log L ≤ agmonRate d / 16 (5 L M₁ - 1)`:
  with `d = L = 3` it reads `6 log 3 ≤ (5 · 3 · M₁ - 1) / 2304`, which fails at the `m₁ = 2` of
  the witness `P6PairWitness` (right side `≈ 0.06`) and holds from `m₁ = 7` on.
* Namespace `Cell`: the `m₁ = 2` slab setting of `P6PairWitness.Slab` (`n₁ = 100`).  The top cell
  of the fine site `ylow`, lying over the collar of the old region (so in the new hole), is
  touched by the layer-`1 = k` index `(1, ylow)` of the multiscale cover `F♯`; for the top cover
  `F^top` every index touching it has layer `2`, and the count is between `1` and `3^3 (3^1)^3`.
  (The count does not use the numerical premise of the pair, so the `m₁ = 2` witness applies.)
-/

@[expose] public section

namespace Balaban.Inhabited

namespace P6TopWitness

open Balaban Balaban.LargeField Balaban.Localization Balaban.Multiscale

namespace Pair

variable (n1 : ℕ) [NeZero n1]

theorem hsep7 : 2 * (3 : ℕ) * Real.log (3 : ℕ) ≤ agmonRate 3 / 16 * (minSep 3 (3 ^ 7) - 1) := by
  have h1 : Real.log (3 : ℕ) ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := ((3 : ℕ) : ℝ)) (by norm_num)
    push_cast at this ⊢
    linarith
  have h2 : agmonRate 3 = 1 / 144 := by
    unfold agmonRate poincareConst
    rw [show min (1 / ((3 : ℕ) : ℝ)) (1 / 2) = 1 / 3 by norm_num [min_def]]
    norm_num
  rw [h2]
  unfold minSep
  push_cast at h1 ⊢
  norm_num
  linarith

theorem hM7 : 4 * 3 ^ 2 ≤ 3 ^ 7 := by norm_num

theorem hN15 : 5 < 15 * n1 := by
  have := Nat.pos_of_ne_zero (NeZero.ne n1)
  omega

theorem hadm : IsAdmissibleWeights (1 + 1) (fun _ : ℕ => (1 : ℝ)) := fun _ _ _ => by
  constructor <;> norm_num

theorem hνL0 : (0 : ℝ) * (((3 : ℕ) : ℝ) ^ (1 + 1)) ^ 2 ≤ 1 := by norm_num

/-- `Dec2.CoverGeom (coverOf F^top) H⁻` at the concrete setting. -/
theorem coverGeom_old (Z : Set (Torus 3 (3 * n1))) :
    Dec2.CoverGeom (coverOf (topGS 3 3 (15 * n1) 7 (1 + 1) (3 : ℝ)))
      (p6OldC (k := 1) (n1 := n1) (c := 15) (M1 := 3 ^ 7) (m₁ := 7) rfl 9 Z)
      (fun _ : ℕ => (1 : ℝ)) 0 (Cchi 3 3) :=
  p6_coverGeom_top_old (k := 1) rfl 9 Z (by norm_num) (hM7) (by norm_num) (by norm_num)
    le_rfl hνL0 hadm (by exact_mod_cast hsep7)

/-- `Dec2.CoverGeom (coverOf F^top) H^∂` at the concrete setting. -/
theorem coverGeom_boundary :
    Dec2.CoverGeom (coverOf (topGS 3 3 (15 * n1) 7 (1 + 1) (3 : ℝ)))
      (p6BoundaryC (k := 1) (c := 15) (M1 := 3 ^ 7) (m₁ := 7) (Zp := (Slab.step n1).Omegaᶜ)
        (Slab.step n1) rfl (by norm_num) rfl (by norm_num)
        P6PairWitness.hρ9 subset_rfl)
      (fun _ : ℕ => (1 : ℝ)) 0 (Cchi 3 3) :=
  p6_coverGeom_top_boundary (k := 1) (Zp := (Slab.step n1).Omegaᶜ)
    (Slab.step n1) (by norm_num) rfl (by norm_num) P6PairWitness.hρ9 subset_rfl
    rfl (by norm_num) hM7 (by norm_num) (by norm_num) le_rfl hνL0 hadm (by exact_mod_cast hsep7)

/-- `Dec2.CoverBase (coverOf F^top) H⁻` at the concrete setting. -/
theorem coverBase_old (Z : Set (Torus 3 (3 * n1))) :
    Dec2.CoverBase (coverOf (topGS 3 3 (15 * n1) 7 (1 + 1) (3 : ℝ)))
      (p6OldC (k := 1) (n1 := n1) (c := 15) (M1 := 3 ^ 7) (m₁ := 7) rfl 9 Z)
      (fun _ : ℕ => (1 : ℝ)) 0 (Dec2.mixedKc 3 3) (Cchi 3 3) :=
  p6_coverBase_top_old (k := 1) rfl 9 Z (by norm_num) hM7 (hN15 n1) (by norm_num) (by norm_num)
    le_rfl hνL0 hadm (by exact_mod_cast hsep7)

/-- `Dec2.CoverBase (coverOf F^top) H^∂` at the concrete setting. -/
theorem coverBase_boundary :
    Dec2.CoverBase (coverOf (topGS 3 3 (15 * n1) 7 (1 + 1) (3 : ℝ)))
      (p6BoundaryC (k := 1) (c := 15) (M1 := 3 ^ 7) (m₁ := 7) (Zp := (Slab.step n1).Omegaᶜ)
        (Slab.step n1) rfl (by norm_num) rfl (by norm_num)
        P6PairWitness.hρ9 subset_rfl)
      (fun _ : ℕ => (1 : ℝ)) 0 (Dec2.mixedKc 3 3) (Cchi 3 3) :=
  p6_coverBase_top_boundary (k := 1) (Zp := (Slab.step n1).Omegaᶜ)
    (Slab.step n1) (by norm_num) rfl (by norm_num) P6PairWitness.hρ9 subset_rfl
    rfl (by norm_num) hM7 (hN15 n1) (by norm_num) (by norm_num) le_rfl hνL0 hadm
    (by exact_mod_cast hsep7)

end Pair

namespace Cell

open Slab

/-- The top cover of the slab setting (`m₁ = 2`, `k + 1 = 2`). -/
noncomputable abbrev topCover (n1 : ℕ) [NeZero n1] :=
  topGS 3 3 (15 * n1) 2 (1 + 1) (3 : ℝ)

open Classical in
/-- **T5 at a concrete hole cell.**  The top cell of the fine site `ylow` (over the collar of the
old region) meets at most `3^3 (3^1)^3` patches of `F^top`, all of layer `2`, and at least one. -/
theorem top_count (n1 : ℕ) [NeZero n1] (hn1 : n1 = 100) :
    1 ≤ ((cubeIdx (topCover n1)).filter
        fun P => MooreTouch (topCell 1 (1 + 1, ylow n1)) (Pset 2 P)).card ∧
    ((cubeIdx (topCover n1)).filter
        fun P => MooreTouch (topCell 1 (1 + 1, ylow n1)) (Pset 2 P)).card ≤ 3 ^ 3 * (3 ^ 1) ^ 3 ∧
    ∀ P ∈ cubeIdx (topCover n1), MooreTouch (topCell 1 (1 + 1, ylow n1)) (Pset 2 P) →
      P.1 = 1 + 1 := by
  have h0 : ylow n1 ∈ topCell 1 (1 + 1, ylow n1) := mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  refine ⟨?_, topGS_root_patch_count ((by norm_num : 3 ^ 1 ∣ 15).mul_right n1) _, fun P hP _ => layer_eq_top_of_mem_cubeIdx hP⟩
  refine Finset.card_pos.2 ⟨(1 + 1, ylow n1), Finset.mem_filter.2 ⟨?_, ?_⟩⟩
  · refine (mem_cubeIdx _).2 ⟨⟨by norm_num, le_rfl⟩, ?_, ?_⟩
    · exact (topCover n1).mem_layer.2 ⟨mem_topGS_Ω le_rfl _, not_mem_topGS_Ω (by omega) _⟩
    · subst hn1
      intro μ
      fin_cases μ <;> decide
  · exact ⟨ylow n1, h0, ylow n1, self_mem_Pset (1 + 1, ylow n1),
      ⟨0, fun _ => by simp, by funext μ; simp⟩⟩

/-- **Contrast with `F♯`.**  The same top cell is touched by the layer-`1 = k` index `(1, ylow)` of
the multiscale cover `F♯`, whereas every index of `F^top` touching it has layer `2`. -/
theorem sharp_lower_layer (n1 : ℕ) [NeZero n1] (hn1 : n1 = 100) :
    ((1, ylow n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1)) ∈ cubeIdx (cover n1) ∧
    MooreTouch (topCell 1 (1 + 1, ylow n1)) (Pset 2 ((1, ylow n1) : ℕ × CTorus 3 3 (15 * n1) 2 (1 + 1))) := by
  have h0 : ylow n1 ∈ topCell 1 (1 + 1, ylow n1) := mem_box_cbase (cellSide_pos 1 2 (1 + 1)) _
  exact ⟨low_mem_cubeIdx n1 hn1, ylow n1, h0, ylow n1, self_mem_Pset (1, ylow n1),
    ⟨0, fun _ => by simp, by funext μ; simp⟩⟩

end Cell

end P6TopWitness

end Balaban.Inhabited
