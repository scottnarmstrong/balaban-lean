/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepActivityHatWitnessRay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation step at a general scale `k` and torus parameter `N₁`

The landed step `hatStep` lives at the scale `k = 1` on the torus parameter `N₁ = 9`, with the mass
`1/81`.  This file builds the same kind of step at a general scale `k ≥ 1` and a general torus
parameter `N₁` (`d = L = 3`, `N = 2`): the new level is the whole-lattice generating set
`𝔹_{k+1}` of level `k + 1`, the lower level is `𝔹_k`, the block datum is the constant unit datum
and the mass `ν` is a parameter with `0 ≤ ν` and `ν · 3^{2(k+1)} ≤ 1`.

* `hatStepK`: the step setting; `hatStepK_one_nine` says it is the landed `hatStep` at
  `k = 1`, `N₁ = 9`, `ν = 1/81`.
* `isLevel_lvTop`, `isLevel_lvLow`: both generating sets are levels.
* `bgHyp_lv`, `dgSetting_lv`, `opSetting_lv`: the background hypothesis, the decoupling setting of
  `𝔹_{k+1}` and the operator setting of `𝔹_k` under the mass premise, `m₁ ≥ 4`, `5 < N₁`.
* `hatConn_lvTop`: the thickened interaction cubes of the full level are connected.
* `rowInHat_lv`, `coverBase_lv`, `footLocal_lv`, `flCore_lv_nonempty`: the landed generic pair
  lemmas at this pair.

NOT proved here: the local cover for a general torus (the witness uses that one chosen cover
cube fills the torus when `N₁ = 9`), the radius tower and `RayData` at a general scale, and the
activity bound at a general scale.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Finset

namespace LevelStep

section Sets

variable (N₁ m₁ k : ℕ) [NeZero N₁] (ϱ : ℝ)

/-- `𝔹_{k+1}`: the whole-lattice generating set of level `k + 1` on the step torus. -/
noncomputable abbrev lvTop : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ :=
  levelGS (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl

/-- `𝔹_k`: the whole-lattice generating set of level `k` on the step torus. -/
noncomputable abbrev lvLow : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ :=
  stepG 3 3 N₁ m₁ k ϱ

variable {N₁ m₁ k ϱ}

theorem lvTop_Ω (i : ℕ) : (lvTop N₁ m₁ k ϱ).Ω i = if i ≤ k + 1 then Finset.univ else ∅ := rfl

theorem isLevel_lvTop : IsLevel (lvTop N₁ m₁ k ϱ) (k + 1) :=
  isLevel_levelGS (by omega) le_rfl

theorem isLevel_lvLow (hk : 1 ≤ k) : IsLevel (lvLow N₁ m₁ k ϱ) k :=
  isLevel_levelGS hk (Nat.le_succ k)

end Sets

section Step

variable {N₁ : ℕ} [NeZero N₁]

/-- **The step at scale `k`**: `G' = 𝔹_{k+1}`, the constant unit block datum with `h₀` the unit
vector, `a₁ = 1`, mass `ν`, and the parameters `β`, `p₁`, `δ`. -/
noncomputable def hatStepK (k m₁ : ℕ) (hk : 1 ≤ k) (ν β p₁ δ : ℝ) :
    StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁) where
  G' := lvTop N₁ m₁ k (rhoSep m₁)
  hk1 := hk
  hG' := isLevel_lvTop
  D' := unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)
  h₀ := unitVec hN2
  hh₀ := fun x i => unitBg_h_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)
    ((isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁)).Ω_one ▸ Finset.mem_univ x) i
  a₁ := 1
  ν := ν
  β := β
  p₁ := p₁
  δ := δ

end Step

/-- `hatStepK` at `k = 1`, `N₁ = 9`, `ν = 1/81` is the landed `hatStep`. -/
theorem hatStepK_one_nine (m₁ : ℕ) (β p₁ δ : ℝ) :
    hatStepK (N₁ := 9) 1 m₁ le_rfl nuW β p₁ δ = hatStep m₁ β p₁ δ := rfl

theorem hatStepK_betaU (k m₁ : ℕ) {N₁ : ℕ} [NeZero N₁] (hk : 1 ≤ k) (ν β p₁ δ : ℝ) :
    (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).betaU = β * 3 ^ k := by
  unfold StepSetting.betaU
  show β * (((3 : ℕ) : ℝ) ^ k) ^ 3 / (((3 : ℕ) : ℝ) ^ k) ^ 2 = β * 3 ^ k
  have : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  push_cast
  field_simp

section Unit

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}

/-- The unit datum has action zero at every mass (cited: `action_unitBg_eq_zero_nu`, general). -/
theorem action_unit_lv (a : ℕ → ℝ) (ν : ℝ) :
    action (lvTop N₁ m₁ k ϱ) a ν (unitBg (lvTop N₁ m₁ k ϱ) hN2 (unitVec hN2))
      (unitPhi (lvTop N₁ m₁ k ϱ) hN2) = 0 :=
  action_unitBg_eq_zero_nu isLevel_lvTop hN2 a ν

theorem isMinimizer_unit_lv {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {ν : ℝ} (hν : 0 ≤ ν) :
    IsMinimizer (lvTop N₁ m₁ k ϱ) a ν (unitBg (lvTop N₁ m₁ k ϱ) hN2 (unitVec hN2))
      (unitPhi (lvTop N₁ m₁ k ϱ) hN2) :=
  isMinimizer_unitBg_nu isLevel_lvTop hN2 ha hν

/-- The background field of the unit datum is the constant unit field at the general mass. -/
theorem bgField_unit_lv {ν : ℝ} (H : BgHyp 3 3 (k + 1) ϱ (compWeight 3 1) ν)
    (hD : InUnionDomainR (lvTop N₁ m₁ k ϱ) (bgC1 3 3 2) ν
      (unitBg (lvTop N₁ m₁ k ϱ) hN2 (unitVec hN2))) :
    bgField (lvTop N₁ m₁ k ϱ) (compWeight 3 1) ν (unitBg (lvTop N₁ m₁ k ϱ) hN2 (unitVec hN2)) =
      unitPhi (lvTop N₁ m₁ k ϱ) hN2 :=
  bgField_unitBg_nu isLevel_lvTop hN2 (fun n => compWeight_nonneg_three 1 zero_le_one n) H hD

end Unit

section Hyp

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ν : ℝ}

theorem massLe_lv (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    ν * (((3 : ℕ) : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := by
  rw [← pow_mul, mul_comm (k + 1)]; simpa using hν

/-- **`BgHyp` at scale `k + 1` with mass `ν`.** -/
theorem bgHyp_lv (m₁ : ℕ) (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    BgHyp 3 3 (k + 1) (rhoSep m₁) (compWeight 3 1) ν where
  hd := le_rfl
  hL := le_rfl
  hϱ := (bgHyp_rho m₁).hϱ
  weights := isAdmissibleWeights_compWeight le_rfl (by norm_num) (by norm_num) _
  mass := hν0
  massLe := massLe_lv hν

/-- **`DGSetting` of the full level `𝔹_{k+1}`.** -/
theorem dgSetting_lv (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    DGSetting (lvTop N₁ m₁ k (rhoSep m₁)) (compWeight 3 1) ν where
  hd := le_rfl
  hL := le_rfl
  aligned :=
    { two_le := by omega
      dvd := dvd_mul_left _ _
      union := fun j _ hj x x' _ => by simp [lvTop_Ω, hj] }
  hM := by
    calc 4 * 3 ^ 2 = 36 := by norm_num
      _ ≤ 3 ^ 4 := by norm_num
      _ ≤ 3 ^ m₁ := Nat.pow_le_pow_right (by norm_num) h4
  cover_sep := by
    have := rhoSep_ge m₁
    have : (0:ℝ) ≤ 3 ^ m₁ := by positivity
    have := rhoSep_tail_nonneg
    push_cast
    nlinarith
  sep := by
    have h := rhoSep_ge m₁
    have ha := agmon3_pos
    have hq : 6 * Real.log 3 / (agmonRate 3 / 16) ≤ rhoSep m₁ - 1 := by
      have : (0:ℝ) ≤ 3 ^ m₁ := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at hq
    push_cast
    nlinarith
  weights := isAdmissibleWeights_compWeight le_rfl (by norm_num) (by norm_num) _
  mass := hν0
  massLe := massLe_lv hν
  big := hN

/-- **`OpSetting` of the lower level `𝔹_k`.** -/
theorem opSetting_lv (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    Dec2.OpSetting (lvLow N₁ m₁ k (rhoSep m₁)) (compWeight 3 1) ν :=
  { hd := (dgSetting_lv h4 hN hν0 hν).hd, hL := (dgSetting_lv h4 hN hν0 hν).hL,
    mass := hν0, massLe := (dgSetting_lv h4 hN hν0 hν).massLe,
    weights := (dgSetting_lv h4 hN hν0 hν).weights, sep := (dgSetting_lv h4 hN hν0 hν).sep }

end Hyp

section Conn

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}

/-- **`HatConn` of the full level `𝔹_{k+1}`**: every thickened interaction cube lies in `Ω₁`,
which is the whole torus, and is nearest-neighbour connected. -/
theorem hatConn_lvTop : HatConn (lvTop N₁ m₁ k ϱ) := by
  intro q _
  have : hatI (lvTop N₁ m₁ k ϱ) q = hatBox q := by
    unfold hatI
    refine Finset.filter_true_of_mem fun x _ => ?_
    simp [lvTop_Ω]
  rw [this]
  unfold hatBox
  refine boxSet_connected q.2 ?_
  unfold hatRad
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ q.1 := by positivity
  push_cast
  linarith

end Conn

section Pair

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ν : ℝ}

/-- `RowInHat` of the pair `(𝔹_{k+1}, 𝔹_k)`. -/
theorem rowInHat_lv (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    RowInHat (coverOf (lvTop N₁ m₁ k (rhoSep m₁))) (lvLow N₁ m₁ k (rhoSep m₁))
      (compWeight 3 1) ν :=
  rowInHat_level (dgSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk) isLevel_lvTop

/-- `CoverBase` of the pair `(𝔹_{k+1}, 𝔹_k)`. -/
theorem coverBase_lv (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    Dec2.CoverBase (coverOf (lvTop N₁ m₁ k (rhoSep m₁))) (lvLow N₁ m₁ k (rhoSep m₁))
      (compWeight 3 1) ν (levelKc 3 3) (Cchi 3 3) :=
  coverBase_level (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk)
    isLevel_lvTop

/-- `FootLocal` of the pair `(𝔹_{k+1}, 𝔹_k)`. -/
theorem footLocal_lv (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    Dec2.FootLocal (coverOf (lvTop N₁ m₁ k (rhoSep m₁))) (lvLow N₁ m₁ k (rhoSep m₁))
      (compWeight 3 1) ν (levelKc 3 3) (Cchi 3 3) :=
  footLocal_level (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk)
    isLevel_lvTop

/-- **`FlCore` for the pair `(𝔹_{k+1}, 𝔹_k)`** for some small `ε' = δ₁ = t > 0`, given the
decoupling constants `(c, BG, κ)` and `(c₂, BG₂)` with the cover-scale inequalities. -/
theorem flCore_lv_nonempty (N : ℕ) (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {c BG : ℝ} (hS : DecSpecs 3 3 c BG) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs 3 3 (levelKc 3 3) (Cchi 3 3) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (FlCore N (lvTop N₁ m₁ k (rhoSep m₁))
      (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t) :=
  flCore_level_nonempty (N := N) (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν)
    (isLevel_lvLow hk) isLevel_lvTop (bgHyp_lv m₁ hν0 hν) hS hκ hM hS2 hM2

end Pair

end LevelStep

end Balaban.Inhabited
