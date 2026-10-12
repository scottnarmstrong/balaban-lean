/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.MooreDegree
public import Balaban.Localization.I5Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the Moore graph of a cover

For the landed cube-aligned generating set `GP m₁ ϱ` of `I5Inhabited` (`d = L = 3`, `N₁ = 6`,
`K = 2`, `Ω_1 = Ω_2` the whole torus, so `cubeIdx` consists of layer-`2` cubes of side
`3 ^ (m₁ + 2)`), with `ϱ = 1` (so `d = 3 ≤ ϱ L² = 9`):
`mooreGraph_GP_adj` shows that the Moore graph has an edge, between the cubes at the origin and
at the neighbouring grid base in the first coordinate.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Localization.I5Inhabited

/-- The numeric premise `d ≤ ϱ L²` holds for `GP m₁ 1` (`d = L = 3`, `ϱ = 1`). -/
theorem GP_moore_premise : ((3 : ℕ) : ℝ) ≤ (1 : ℝ) * ((3 : ℕ) : ℝ) ^ 2 := by norm_num

/-- **T5.**  The Moore graph of the cover `GP m₁ 1` has an edge. -/
theorem mooreGraph_GP_adj {m₁ : ℕ} :
    ∃ P Q : {P // P ∈ cubeIdx (GP m₁ 1)}, (mooreGraph (GP m₁ 1)).Adj P Q := by
  set s : ℕ := 3 ^ (2 + m₁) with hs
  set n : ℕ := (6 * 3 ^ m₁) * 3 ^ 2 with hn
  have hs1 : 1 ≤ s := Nat.one_le_pow _ _ (by norm_num)
  have hsn : s < n := by
    rw [hs, hn, pow_add]
    have : 0 < 3 ^ m₁ := by positivity
    nlinarith
  have hval : ((s : ℕ) : ZMod n).val = s := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hsn]
  have hval' : (((s - 1 : ℕ)) : ZMod n).val = s - 1 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hn0 : NeZero n := ⟨by omega⟩
  let b : CTorus 3 3 6 m₁ 2 := Pi.single (0 : Fin 3) ((s : ℕ) : ZMod n)
  let x : CTorus 3 3 6 m₁ 2 := Pi.single (0 : Fin 3) (((s - 1 : ℕ)) : ZMod n)
  have hP : ((2, (0 : CTorus 3 3 6 m₁ 2)) : ℕ × CTorus 3 3 6 m₁ 2) ∈ cubeIdx (GP m₁ 1) := by
    rw [mem_cubeIdx]
    refine ⟨⟨by norm_num, le_rfl⟩, by rw [GP_layer_two]; exact Finset.mem_univ _, ?_⟩
    intro μ; simp
  have hQ : ((2, b) : ℕ × CTorus 3 3 6 m₁ 2) ∈ cubeIdx (GP m₁ 1) := by
    rw [mem_cubeIdx]
    refine ⟨⟨by norm_num, le_rfl⟩, by rw [GP_layer_two]; exact Finset.mem_univ _, ?_⟩
    intro μ
    by_cases h : μ = 0
    · subst h
      show (ZMod.val ((Pi.single (0 : Fin 3) ((s : ℕ) : ZMod n) : Fin 3 → ZMod n) (0 : Fin 3))) % 3 ^ (2 + m₁) = 0
      rw [Pi.single_eq_same, hval, hs, Nat.mod_self]
    · simp [b, Pi.single_eq_of_ne h]
  refine ⟨⟨_, hP⟩, ⟨_, hQ⟩, ?_, x, ?_, b, self_mem_Pset _, ?_⟩
  · intro h
    have h2 := congrArg (fun P : {P // P ∈ cubeIdx (GP m₁ 1)} => (P.1.2 0).val) h
    simp [b, hval] at h2
    omega
  · intro μ
    by_cases h : μ = 0
    · subst h; simp [x, hval']; omega
    · simp [x, Pi.single_eq_of_ne h]
  · refine near_one_iff.2 ⟨Pi.single 0 1, ?_, ?_⟩
    · intro μ
      by_cases h : μ = 0
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · intro μ
      by_cases h : μ = 0
      · subst h
        have h1 : (((s - 1 : ℕ) : ZMod n)) + 1 = (s : ZMod n) := by
          calc ((s - 1 : ℕ) : ZMod n) + 1 = ((s - 1 + 1 : ℕ) : ZMod n) := by push_cast; rfl
            _ = (s : ZMod n) := by rw [show s - 1 + 1 = s by omega]
        show (Pi.single (0 : Fin 3) ((s : ℕ) : ZMod n) : Fin 3 → ZMod n) (0 : Fin 3) =
          (Pi.single (0 : Fin 3) (((s - 1 : ℕ)) : ZMod n) : Fin 3 → ZMod n) (0 : Fin 3) +
            (((Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) 0 : ℤ) : ZMod n)
        simp only [Pi.single_eq_same, Int.cast_one]
        exact h1.symm
      · simp [b, x, Pi.single_eq_of_ne h]

open Classical in
/-- The degree bound of `mooreGraph_degree_le` applies to `GP m₁ 1` (`m₁ ≥ 2`). -/
theorem mooreGraph_GP_degree_le {m₁ : ℕ} (hm : 2 ≤ m₁) (P : {P // P ∈ cubeIdx (GP m₁ 1)}) :
    (mooreGraph (GP m₁ 1)).degree P ≤ 3 * (3 + 4) ^ 3 :=
  mooreGraph_degree_le (GP_cubeAligned hm) GP_moore_premise P

end Balaban.Localization
