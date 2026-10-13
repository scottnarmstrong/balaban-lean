/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelStepSetting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The level setting of the step for general `d`, `L`, `N`

`LevelStepSetting` fixes `d = L = 3` and `N = 2` spin components.  Here the same objects are
defined for a general dimension `d`, block size `L` and number `N ≥ 2` of components:

* `lvTopG`, `lvLowG`: the whole-lattice generating sets `𝔹_{k+1}` and `𝔹_k` on the torus of side
  `N₁ * L ^ m₁`;
* `hatStepKG`: the step setting at level `k` with the coordinate unit external field;
* `lvTopG_Ω`, `isLevel_lvTopG`, `isLevel_lvLowG`, `hatStepKG_betaU` (the block coupling is
  `β * L ^ (k * (d - 2))`), `action_unit_lvG`, `isMinimizer_unit_lvG`, `bgField_unit_lvG`,
  `massLe_lvG`, `bgHyp_lvG`;
* the reductions `lvTopG_three`, `lvLowG_three`, `hatStepKG_three` to the landed objects.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Finset

namespace LevelStep

section Sets

variable (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ)

/-- `𝔹_{k+1}`: the whole-lattice generating set of level `k + 1` on the step torus, general
`d`, `L`. -/
noncomputable abbrev lvTopG : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ :=
  levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl

/-- `𝔹_k`: the whole-lattice generating set of level `k` on the step torus, general `d`, `L`. -/
noncomputable abbrev lvLowG : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ :=
  stepG d L N₁ m₁ k ϱ

/-- At `d = L = 3` the general top set is the landed one. -/
theorem lvTopG_three : lvTopG 3 3 N₁ m₁ k ϱ = lvTop N₁ m₁ k ϱ := rfl

/-- At `d = L = 3` the general lower set is the landed one. -/
theorem lvLowG_three : lvLowG 3 3 N₁ m₁ k ϱ = lvLow N₁ m₁ k ϱ := rfl

variable {d L N₁ m₁ k ϱ}

theorem lvTopG_Ω (i : ℕ) : (lvTopG d L N₁ m₁ k ϱ).Ω i = if i ≤ k + 1 then Finset.univ else ∅ :=
  rfl

theorem isLevel_lvTopG : IsLevel (lvTopG d L N₁ m₁ k ϱ) (k + 1) :=
  isLevel_levelGS (by omega) le_rfl

theorem isLevel_lvLowG (hk : 1 ≤ k) : IsLevel (lvLowG d L N₁ m₁ k ϱ) k :=
  isLevel_levelGS hk (Nat.le_succ k)

end Sets

section Step

variable {d L N : ℕ} [NeZero L] {N₁ : ℕ} [NeZero N₁]

/-- **The step at scale `k`, general `d`, `L`, `N ≥ 2`**: `G' = 𝔹_{k+1}`, the constant unit block
datum with `h₀` the coordinate unit vector, `a₁ = 1`, mass `ν`, and the parameters `β`, `p₁`, `δ`. -/
noncomputable def hatStepKG (hN : 2 ≤ N) (k m₁ : ℕ) (ϱ : ℝ) (hk : 1 ≤ k) (ν β p₁ δ : ℝ) :
    StepSetting d L N₁ m₁ k N ϱ where
  G' := lvTopG d L N₁ m₁ k ϱ
  hk1 := hk
  hG' := isLevel_lvTopG
  D' := unitBg (lvTopG d L N₁ m₁ k ϱ) (Nat.lt_of_lt_of_le two_pos hN)
    (unitVec (Nat.lt_of_lt_of_le two_pos hN))
  h₀ := unitVec (Nat.lt_of_lt_of_le two_pos hN)
  hh₀ := fun x i => unitBg_h_of_mem (lvTopG d L N₁ m₁ k ϱ) (Nat.lt_of_lt_of_le two_pos hN)
    (unitVec (Nat.lt_of_lt_of_le two_pos hN))
    ((isLevel_lvTopG (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ)).Ω_one ▸
      Finset.mem_univ x) i
  a₁ := 1
  ν := ν
  β := β
  p₁ := p₁
  δ := δ

/-- At `d = L = 3`, `N = 2`, `ϱ = rhoSep m₁` the general step is the landed `hatStepK`. -/
theorem hatStepKG_three (k m₁ : ℕ) (hk : 1 ≤ k) (ν β p₁ δ : ℝ) :
    hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k m₁ (rhoSep m₁) hk ν β p₁ δ =
      hatStepK k m₁ hk ν β p₁ δ := rfl

/-- **The block coupling of the step at level `k`** is `β * L ^ (k * (d - 2))`. -/
theorem hatStepKG_betaU (hN : 2 ≤ N) (hd : 2 ≤ d) (k m₁ : ℕ) (ϱ : ℝ) (hk : 1 ≤ k)
    (ν β p₁ δ : ℝ) :
    (hatStepKG (d := d) (L := L) (N₁ := N₁) hN k m₁ ϱ hk ν β p₁ δ).betaU =
      β * (L : ℝ) ^ (k * (d - 2)) := by
  unfold StepSetting.betaU
  show β * ((L : ℝ) ^ k) ^ d / ((L : ℝ) ^ k) ^ 2 = β * (L : ℝ) ^ (k * (d - 2))
  have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpos : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  have hkd : k * d = k * (d - 2) + k * 2 := by
    rw [← Nat.mul_add]; congr 1; omega
  rw [mul_div_assoc, ← pow_mul, ← pow_mul, hkd, pow_add]
  have : (0 : ℝ) < (L : ℝ) ^ (k * 2) := by positivity
  field_simp

end Step

/-- The weights `compWeight L 1` are non-negative for `L ≥ 3`. -/
theorem compWeight_one_nonneg {L : ℕ} (hL : 3 ≤ L) (n : ℕ) : 0 ≤ compWeight L 1 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold compWeight; simp
  · exact (Background.compWeight_mem_Icc hL (by norm_num) (by norm_num) hn).1.trans' (by norm_num)

section Unit

variable {d L N : ℕ} [NeZero L] {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}

/-- The unit datum has action zero at every mass. -/
theorem action_unit_lvG (hN : 0 < N) (a : ℕ → ℝ) (ν : ℝ) :
    action (lvTopG d L N₁ m₁ k ϱ) a ν (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN))
      (unitPhi (lvTopG d L N₁ m₁ k ϱ) hN) = 0 :=
  action_unitBg_eq_zero_nu isLevel_lvTopG hN a ν

theorem isMinimizer_unit_lvG (hN : 0 < N) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {ν : ℝ} (hν : 0 ≤ ν) :
    IsMinimizer (lvTopG d L N₁ m₁ k ϱ) a ν (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN))
      (unitPhi (lvTopG d L N₁ m₁ k ϱ) hN) :=
  isMinimizer_unitBg_nu isLevel_lvTopG hN ha hν

/-- The background field of the unit datum is the constant unit field at the general mass. -/
theorem bgField_unit_lvG (hN : 0 < N) (hL : 3 ≤ L) {ν : ℝ}
    (H : BgHyp d L (k + 1) ϱ (compWeight L 1) ν)
    (hD : InUnionDomainR (lvTopG d L N₁ m₁ k ϱ) (bgC1 d L N) ν
      (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN))) :
    bgField (lvTopG d L N₁ m₁ k ϱ) (compWeight L 1) ν
        (unitBg (lvTopG d L N₁ m₁ k ϱ) hN (unitVec hN)) =
      unitPhi (lvTopG d L N₁ m₁ k ϱ) hN :=
  bgField_unitBg_nu isLevel_lvTopG hN (compWeight_one_nonneg hL) H hD

end Unit

section Hyp

variable {d L : ℕ} {k : ℕ} {ν : ℝ}

theorem massLe_lvG (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
  rw [← pow_mul, mul_comm (k + 1)]; exact hν

/-- **`BgHyp` at scale `k + 1` with mass `ν`**, general `d`, `L`, `ϱ ≥ R₀(d, L)`. -/
theorem bgHyp_lvG {ϱ : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) :
    BgHyp d L (k + 1) ϱ (compWeight L 1) ν where
  hd := hd
  hL := hL
  hϱ := hϱ
  weights := isAdmissibleWeights_compWeight hL (by norm_num) (by norm_num) _
  mass := hν0
  massLe := massLe_lvG hν

end Hyp

end LevelStep

end Balaban.Inhabited
