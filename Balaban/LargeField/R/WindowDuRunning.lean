/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuBranch
public import Balaban.SmallField.Def6v2Regime

/-!
# The two mass premises of the window consumer from the flow (blocker 4)

`removedKernel_kerBound_of_hid_action_cl_hS` takes `hbν` (`β_m ν_m L^{-2m} L^{2m} ≤ E` for `m ≤ k₀`) and
`hbeta0` (`β_m > 2E/(L² c₁²)`).  Both are consequences of the flow:

* `window_hbnu_of_running`: `β_m ν_m ≤ e^{2ε}` for `m ≤ k₀ = kZero` (`RunningHyp.beta_mul_nu_le`,
  LFR Lemma IV.3.3 (a)), when `cs.beta = b` and `cs.muAct m = ν_m L^{-2m}` (`Coh.beta_cs`,
  `FieldClauses.muAct_eq`);
* `window_hbeta0_of_flow`: `β_m ≥ β L^{(d-2)m} e^{-η} ≥ β e^{-η}` (the flow bound), so `β > β₀ e^η` with
  `β₀ = 2E/(L² c₁²)` gives `β_m > β₀`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.SmallField Balaban.Multiscale

theorem window_hbnu_of_running {d L : ℕ} {β ν a ε : ℝ} {b n : ℕ → ℝ} {k0 : ℕ} [NeZero L]
    (h : RunningHyp d L β ν a ε b n) (hg : KZeroGenuine β ν) (hk0 : k0 = kZero d L β ν)
    (cs : OpConsts) (hcb : ∀ j, j ≤ k0 → cs.beta j = b j)
    (hmu : ∀ j, j ≤ k0 → cs.muAct j = n j / (L : ℝ) ^ (2 * j)) :
    ∀ m, m ≤ k0 → cs.beta m * (cs.muAct m * (L : ℝ) ^ (2 * m)) ≤ Real.exp (2 * ε) := by
  intro m hm
  have hL : ((L : ℝ) ^ (2 * m)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
  rw [hcb m hm, hmu m hm, div_mul_cancel₀ _ hL]
  exact h.beta_mul_nu_le hg (hk0 ▸ hm)

theorem window_hbeta0_of_flow {L d : ℕ} (hL : 1 ≤ L) {cs : OpConsts} {β η E c : ℝ}
    {m' : ℕ} (hflow : cs.beta m' ≥ β * (L : ℝ) ^ ((d - 2) * m') * Real.exp (-η)) (hc : 0 < c)
    (hE : 0 ≤ E) (hβ : 2 * E * Real.exp η / ((L : ℝ) ^ 2 * c ^ 2) < β) :
    2 * E / ((L : ℝ) ^ 2 * c ^ 2) < cs.beta m' := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hp : (1 : ℝ) ≤ (L : ℝ) ^ ((d - 2) * m') := one_le_pow₀ hL1
  have hex := Real.exp_pos η
  have hexn := Real.exp_pos (-η)
  have h1 : 2 * E / ((L : ℝ) ^ 2 * c ^ 2) < β * Real.exp (-η) := by
    have : 2 * E * Real.exp η / ((L : ℝ) ^ 2 * c ^ 2) * Real.exp (-η) =
        2 * E / ((L : ℝ) ^ 2 * c ^ 2) := by
      rw [mul_div_right_comm, mul_assoc, ← Real.exp_add]; simp
    rw [← this]; exact mul_lt_mul_of_pos_right hβ hexn
  have hb : 0 < β := lt_of_le_of_lt (by positivity) hβ
  calc 2 * E / ((L : ℝ) ^ 2 * c ^ 2) < β * Real.exp (-η) := h1
    _ ≤ β * (L : ℝ) ^ ((d - 2) * m') * Real.exp (-η) := by
        nlinarith [mul_pos hb hexn]
    _ ≤ cs.beta m' := hflow

end Balaban.LargeField
