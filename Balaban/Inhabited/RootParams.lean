/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.RootBoundsArith
public import Balaban.Green.FinalConstants
public import Balaban.Fluctuation.RootTorusParameters
public import Balaban.Fluctuation.RootSupportBridge
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The constants of Root-F in its quantifier order

The constraints that the landed theorems put on the constants of `Balaban.logPartition_multiscale`
are simultaneously satisfiable in the order `δ`, then `κ, c₉`, then `L, M`, then `β₀`, then
`ν, h`, then `k_f`.

* `δ` depends on `d` only (`δ = (d-2)/8`): `δ ≤ (d-2)/2` (`betaK_inv_sq_le`), and
  `δ < s (d-2)` with `s = 1/4 < 1/2` (the birth-scale bound
  `rootTermFamily_obs_birthScale_fromTowerG_rho`).
* `L = 7` (odd, at least `6`, so `5 < L^{m₀}` with `m₀ = 1`).  The tower of one step has decay
  `(3/2) κ_dec ≥ c₁(d, L) κ` (`rootRate_of_sizeJ`) and `M = L^{m₁+1}`.  The constants `4 p_B e^{p_H κ}`
  and `8 κ 7^d / p_ε` of the last integral (`cutoffInteraction_final_phys`) are at most `L^{m₁}`
  because the tower floor `κ_min` is chosen large: `L^{m₁} ≥ c_* e^{N₀ κ_tower}`
  (`StepTowerG.large_block`).
* `β₀`: the amplitude threshold of `rootBound_of_perTerm`, the cut-radius threshold of
  `cutConst_mul_lt_of_large` and the condition `L^{(d-2)/2+δ} ≤ c₉ β₀²` of `betaK_inv_sq_le`.
  The amplitude and cut constants (`C, C', B, p, R`) are determined by the tower and by `L, M`,
  which are fixed before `β₀`.
* `k_f` from `ν`: `L^{k_f} √ν ≤ L` and `1/2 ≤ L^{k_f+1} √ν`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Green

/-- The scale index `k_f` of Root-F exists for every `ν ∈ (0,1]` and `L ≥ 2`:
`L^{k_f} √ν ≤ L` and `1/2 ≤ L^{k_f+1} √ν`. -/
theorem exists_kf_scale {L : ℕ} (hL : 2 ≤ L) {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν := by
  classical
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hs1 : Real.sqrt ν ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hν1
  have hex : ∃ k : ℕ, 1 / 2 ≤ (L : ℝ) ^ (k + 1) * Real.sqrt ν := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 / 2) / Real.sqrt ν) hL1
    refine ⟨n, ?_⟩
    have h1 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (n + 1) :=
      pow_le_pow_right₀ hL1.le (Nat.le_succ n)
    have h2 : (1 / 2) / Real.sqrt ν < (L : ℝ) ^ (n + 1) := lt_of_lt_of_le hn h1
    rw [div_lt_iff₀ hs] at h2
    exact h2.le
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]
    simp only [pow_zero, one_mul]
    exact hs1.trans hL1.le
  · obtain ⟨k', hk'⟩ : ∃ k', Nat.find hex = k' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hmin := Nat.find_min hex (show k' < Nat.find hex by omega)
    rw [not_le] at hmin
    rw [hk']
    have : (1 : ℝ) / 2 ≤ L := by linarith
    linarith

/-- The tower of one step and the block size `M = L^{m₁+1}`: for `L = 7`, `m₀ = 1` and every
`κ` there are a floor `κ_min` and a tower `T` over it with decay `(3/2) κ_dec ≥ c₁ κ` and
`M = L^{m₁+1}` satisfying the two inequalities of the last integral at `max κ 1`. -/
theorem exists_tower_blockSize (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) (κ : ℝ) :
    ∃ κmin : ℝ, ∃ T : StepTowerThetaG d 7 N κmin, T.m₀ = 1 ∧
      c1 d 7 * κ ≤ 3 / 2 * T.κdec ∧
      4 * (pdB d 7 * Real.exp (pdH d * max κ 1)) ≤ (((7 ^ (T.m₁ + 1) : ℕ)) : ℝ) ∧
      8 * max κ 1 * 7 ^ d ≤ pdEps d 7 * (((7 ^ (T.m₁ + 1) : ℕ)) : ℝ) := by
  have hpe : 0 < pdEps d 7 := pdEps_pos (by omega)
  have hc := cstarX_pos d 7
  have hN0 : (0 : ℝ) < (N0 d 7 : ℝ) := by
    have : 0 < N0 d 7 := by unfold N0; positivity
    exact_mod_cast this
  set K : ℝ := max (4 * (pdB d 7 * Real.exp (pdH d * max κ 1)))
    (8 * max κ 1 * 7 ^ d / pdEps d 7) with hK
  set Y : ℝ := K / cstarX d 7 with hY
  obtain ⟨T, hm, hrate, -⟩ := exists_stepTowerThetaG d 7 N hd (by norm_num) hN 1 le_rfl κ 0
    (max Y 0 / (N0 d 7 : ℝ))
  have hκT : max Y 0 / (N0 d 7 : ℝ) ≤ T.κ := T.κmin_le
  have h1 : max Y 0 ≤ (N0 d 7 : ℝ) * T.κ := by
    rw [div_le_iff₀ hN0] at hκT; linarith
  have h2 : Y ≤ Real.exp ((N0 d 7 : ℝ) * T.κ) := by
    have := Real.add_one_le_exp ((N0 d 7 : ℝ) * T.κ)
    have := le_max_left Y 0
    linarith
  have hlb : K ≤ (7 : ℝ) ^ T.m₁ := by
    have h3 : K ≤ cstarX d 7 * Real.exp ((N0 d 7 : ℝ) * T.κ) := by
      have : K = cstarX d 7 * Y := by rw [hY]; field_simp
      rw [this]; exact mul_le_mul_of_nonneg_left h2 hc.le
    have h4 := T.large_block
    push_cast at h4 ⊢
    linarith
  have hM : (7 : ℝ) ^ T.m₁ ≤ (((7 ^ (T.m₁ + 1) : ℕ)) : ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  refine ⟨_, T, hm, ?_, ?_, ?_⟩
  · simpa using hrate
  · exact (le_max_left _ _).trans (hlb.trans hM)
  · have : 8 * max κ 1 * 7 ^ d / pdEps d 7 ≤ (((7 ^ (T.m₁ + 1) : ℕ)) : ℝ) :=
      (le_max_right _ _).trans (hlb.trans hM)
    rw [div_le_iff₀ hpe] at this
    linarith

/-- **The constants of Root-F in its quantifier order.**  `δ` from `d`; for `κ, c₉`: `L = 7`
and `M = L^{m₁+1}` of a tower of one step; then, for the amplitude and cut constants
`C, C', B, p, R` (fixed by the tower, `L`, `M`), a threshold `β₀`; then for `ν, h` the index
`k_f`. -/
theorem exists_rootParams (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ((d : ℝ) - 2) / 4 ∧
    ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
    ∃ L M : ℕ, 2 ≤ L ∧ 6 ≤ L ∧ Odd L ∧ 1 ≤ M ∧
    ∃ (_ : NeZero L) (κmin : ℝ) (T : StepTowerThetaG d L N κmin),
      T.m₀ = 1 ∧ M = L ^ (T.m₁ + 1) ∧
      (∀ q J K : ℕ, 1 ≤ q → 5 < q * L ^ T.m₀ * L ^ (J - K)) ∧
      c1 d L * κ ≤ 3 / 2 * T.κdec ∧
      4 * (pdB d L * Real.exp (pdH d * max κ 1)) ≤ (M : ℝ) ∧
      8 * max κ 1 * 7 ^ d ≤ pdEps d L * (M : ℝ) ∧
    ∀ C C' B p R : ℝ, 0 < C → 0 < C' → 0 < R →
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ c₉ * β₀ ^ 2 ∧
    ∀ β : ℝ, β₀ ≤ β →
      (C * C' * Real.exp (3 / 2 * T.κdec) * (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) / c₉) ^
          (1 / ((((d : ℝ) - 2) / 2 + δ) / ((d : ℝ) - 2))) ≤ β ∧
      (B * p / R) ^ 2 + 1 ≤ β ∧
    ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
    ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧ 1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν := by
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨((d : ℝ) - 2) / 8, by positivity, by linarith, ?_⟩
  intro κ hκ c₉ hc₉
  obtain ⟨κmin, T, hm, hrate, hMB, hMκ⟩ := exists_tower_blockSize d N hd hN κ
  refine ⟨7, 7 ^ (T.m₁ + 1), by norm_num, by norm_num, by decide, Nat.one_le_pow _ _ (by norm_num),
    inferInstance, κmin, T, hm, rfl, ?_, hrate, hMB, hMκ, ?_⟩
  · intro q J K hq
    exact Fluctuation.five_lt_rootN₁_of_five_lt_pow 7 T.m₀ q J K hq (by rw [hm]; norm_num)
  · intro C C' B p R hC hC' hR
    set e : ℝ := ((d : ℝ) - 2) / 2 + ((d : ℝ) - 2) / 8 with he
    set q : ℝ := e / ((d : ℝ) - 2) with hq
    set A : ℝ := (C * C' * Real.exp (3 / 2 * T.κdec) * (7 : ℝ) ^ e / c₉) ^ (1 / q) with hA
    have hLe : (0 : ℝ) < (7 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
    refine ⟨max 3 (max ((7 : ℝ) ^ e / c₉ + 1) (max A ((B * p / R) ^ 2 + 1))), le_max_left _ _,
      ?_, ?_⟩
    · have h1 : (7 : ℝ) ^ e / c₉ + 1 ≤ max 3 (max ((7 : ℝ) ^ e / c₉ + 1) (max A ((B * p / R) ^ 2 + 1))) :=
        (le_max_left _ _).trans (le_max_right _ _)
      set b := max 3 (max ((7 : ℝ) ^ e / c₉ + 1) (max A ((B * p / R) ^ 2 + 1)))
      have hdiv : (7 : ℝ) ^ e / c₉ > 0 := by positivity
      have hb1 : (1 : ℝ) ≤ b := by linarith
      have : (7 : ℝ) ^ e / c₉ ≤ b ^ 2 := by nlinarith
      rw [div_le_iff₀ hc₉] at this
      push_cast
      linarith
    · intro β hβ
      refine ⟨?_, ?_, ?_⟩
      · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hβ
      · exact (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hβ
      · intro ν hν hν1 h _
        exact exists_kf_scale (by norm_num) hν hν1
