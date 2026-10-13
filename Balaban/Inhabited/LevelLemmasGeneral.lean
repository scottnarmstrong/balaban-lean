/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelStepSettingGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The remaining lemmas of the level setting for general `d` and `L`

For the whole-lattice generating sets `lvTopG`, `lvLowG` at an arbitrary separation `ϱ`:

* `hatConn_lvTopG`: the thickened interaction cubes of the full level are connected (uses only
  `L ≥ 1`-type facts: `1 ≤ L ^ (j + m₁)`, and `hatRad` is a sum of nonnegative terms);
* `rowInHat_lvG`, `coverBase_lvG`, `footLocal_lvG`, `flCore_lvG_nonempty`: the generic pair
  lemmas, with the decoupling setting of `lvTopG` and the operator setting of `lvLowG` as
  explicit hypotheses.

Each statement specializes at `d = L = 3` to the landed one (`LevelStepSetting`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Finset

namespace LevelStep

section Conn

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **`HatConn` of the full level `𝔹_{k+1}`**, general `d`, `L`: every thickened interaction cube
lies in `Ω₁`, which is the whole torus, and is nearest-neighbour connected. -/
theorem hatConn_lvTopG (hL : 3 ≤ L) : HatConn (lvTopG d L N₁ m₁ k ϱ) := by
  intro q _
  have : hatI (lvTopG d L N₁ m₁ k ϱ) q = hatBox q := by
    unfold hatI
    refine Finset.filter_true_of_mem fun x _ => ?_
    simp [lvTopG_Ω]
  rw [this]
  unfold hatBox
  refine boxSet_connected q.2 ?_
  unfold hatRad
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hLr
  have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
  linarith

end Conn

section Pair

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {ν : ℝ}

/-- `RowInHat` of the pair `(𝔹_{k+1}, 𝔹_k)`, general `d`, `L`. -/
theorem rowInHat_lvG (hk : 1 ≤ k)
    (S : DGSetting (lvTopG d L N₁ m₁ k ϱ) (compWeight L 1) ν) :
    RowInHat (coverOf (lvTopG d L N₁ m₁ k ϱ)) (lvLowG d L N₁ m₁ k ϱ) (compWeight L 1) ν :=
  rowInHat_level S (isLevel_lvLowG hk) isLevel_lvTopG

/-- `CoverBase` of the pair `(𝔹_{k+1}, 𝔹_k)`, general `d`, `L`. -/
theorem coverBase_lvG (hk : 1 ≤ k)
    (S : DGSetting (lvTopG d L N₁ m₁ k ϱ) (compWeight L 1) ν)
    (SH : Dec2.OpSetting (lvLowG d L N₁ m₁ k ϱ) (compWeight L 1) ν) :
    Dec2.CoverBase (coverOf (lvTopG d L N₁ m₁ k ϱ)) (lvLowG d L N₁ m₁ k ϱ)
      (compWeight L 1) ν (levelKc d L) (Cchi d L) :=
  coverBase_level S SH (isLevel_lvLowG hk) isLevel_lvTopG

/-- `FootLocal` of the pair `(𝔹_{k+1}, 𝔹_k)`, general `d`, `L`. -/
theorem footLocal_lvG (hk : 1 ≤ k)
    (S : DGSetting (lvTopG d L N₁ m₁ k ϱ) (compWeight L 1) ν)
    (SH : Dec2.OpSetting (lvLowG d L N₁ m₁ k ϱ) (compWeight L 1) ν) :
    Dec2.FootLocal (coverOf (lvTopG d L N₁ m₁ k ϱ)) (lvLowG d L N₁ m₁ k ϱ)
      (compWeight L 1) ν (levelKc d L) (Cchi d L) :=
  footLocal_level S SH (isLevel_lvLowG hk) isLevel_lvTopG

/-- **`FlCore` for the pair `(𝔹_{k+1}, 𝔹_k)`**, general `d`, `L`, for some small
`ε' = δ₁ = t > 0`. -/
theorem flCore_lvG_nonempty (N : ℕ) (hk : 1 ≤ k) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ)
    (S : DGSetting (lvTopG d L N₁ m₁ k ϱ) (compWeight L 1) ν)
    (SH : Dec2.OpSetting (lvLowG d L N₁ m₁ k ϱ) (compWeight L 1) ν)
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1)
    {c BG : ℝ} (hS : DecSpecs d L c BG) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs d L (levelKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (FlCore N (lvTopG d L N₁ m₁ k ϱ) (lvLowG d L N₁ m₁ k ϱ) 1 ν
      c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t) :=
  flCore_level_nonempty (N := N) S SH (isLevel_lvLowG hk) isLevel_lvTopG
    (bgHyp_lvG hd hL hϱ hν0 hν) hS hκ hM hS2 hM2

end Pair

/-! ### Specialization at `d = L = 3` -/

section Three

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ν : ℝ}

example : HatConn (lvTop N₁ m₁ k (rhoSep m₁)) := hatConn_lvTopG (d := 3) (L := 3) le_rfl

example (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    RowInHat (coverOf (lvTop N₁ m₁ k (rhoSep m₁))) (lvLow N₁ m₁ k (rhoSep m₁))
      (compWeight 3 1) ν :=
  rowInHat_lvG (d := 3) (L := 3) hk (dgSetting_lv h4 hN hν0 hν)

example (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    Dec2.CoverBase (coverOf (lvTop N₁ m₁ k (rhoSep m₁))) (lvLow N₁ m₁ k (rhoSep m₁))
      (compWeight 3 1) ν (levelKc 3 3) (Cchi 3 3) :=
  coverBase_lvG (d := 3) (L := 3) hk (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν)

example (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) :
    Dec2.FootLocal (coverOf (lvTop N₁ m₁ k (rhoSep m₁))) (lvLow N₁ m₁ k (rhoSep m₁))
      (compWeight 3 1) ν (levelKc 3 3) (Cchi 3 3) :=
  footLocal_lvG (d := 3) (L := 3) hk (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν)

example (N : ℕ) (hk : 1 ≤ k) (h4 : 4 ≤ m₁) (hN : 5 < N₁) (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {c BG : ℝ} (hS : DecSpecs 3 3 c BG) {κ : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁) {c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs 3 3 (levelKc 3 3) (Cchi 3 3) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ m₁) :
    ∃ t : ℝ, 0 < t ∧ Nonempty (FlCore N (lvTop N₁ m₁ k (rhoSep m₁))
      (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t) :=
  flCore_lvG_nonempty (d := 3) (L := 3) N hk le_rfl le_rfl (bgHyp_rho m₁).hϱ
    (dgSetting_lv h4 hN hν0 hν) (opSetting_lv h4 hN hν0 hν) hν0 hν hS hκ hM hS2 hM2

end Three

end LevelStep

end Balaban.Inhabited
