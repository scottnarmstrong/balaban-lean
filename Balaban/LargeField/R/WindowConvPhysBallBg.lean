/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.WindowConvPhysSwitchLocPhys
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The standing hypotheses of Theorem 5.2 for the window generating set

The window generating set has the separation `winSep = min {L M R_base, 5 L M₁}`.  Since
`M = c M₁` with `c ≥ 14` and `R_base ≥ 2`, `L M R_base ≥ 28 L M₁ ≥ 5 L M₁`, so
`winSep = 5 L M₁ = minSep`.  Hence `bgR0 ≤ winSep` is the single constant condition
`bgR0 ≤ 5 L M₁` (already a premise of the switch: `bgR0 ≤ ϱ_B ≤ minSep`).  The mass condition
`ν_{m'+1} L^{2(m'+1)} ≤ 1` follows from the flow bound `ν L^{2(m'+1)} D_δ ≤ c_ν²` for
`c_ν ≤ 1`.  The admissibility of the weights `a_n ∈ [1/2, 2]` up to the scale `m'+1` is the
typing data of the weights `ak`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {S : Setting} {n : ℕ → ℕ} {R : ℕ → ℝ} {M : ℕ} [NeZero S.L]

/-- The window separation is the minimal-generating-set separation `5 L M₁`. -/
theorem winSep_eq_minSep (g : Geo S n R M) (hRb : 2 ≤ S.Rb) :
    RegionHistory.winSep g = minSep S.L g.M1 := by
  unfold RegionHistory.winSep
  refine min_eq_right ?_
  have hM : (M : ℝ) = (g.c : ℝ) * g.M1 := by exact_mod_cast g.hM
  have hc : (14 : ℝ) ≤ g.c := by exact_mod_cast g.hc
  have hM1 : (1 : ℝ) ≤ g.M1 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne g.M1)
  have hL : (1 : ℝ) ≤ S.L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  unfold minSep
  rw [hM]
  have h1 : 0 ≤ (S.L : ℝ) * g.M1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (show (28 : ℝ) ≤ g.c * S.Rb by nlinarith) h1]

/-- **`BgHyp` for the window generating set** (`ϱ = winSep`) at the weights `ak` and mass `ν`:
the constant condition `bgR0 ≤ 5 L M₁`, admissible weights up to scale `k`, and `0 ≤ ν`,
`ν L^{2k} ≤ 1`. -/
theorem bgHyp_winSep_of_const (g : Geo S n R M) {k : ℕ} {ak : ℕ → ℝ} {ν : ℝ}
    (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) (hRb : 2 ≤ S.Rb)
    (hR0 : bgR0 S.d S.L ≤ minSep S.L g.M1) (hak : IsAdmissibleWeights k ak)
    (hν : 0 ≤ ν) (hνL : ν * ((S.L : ℝ) ^ k) ^ 2 ≤ 1) :
    BgHyp S.d S.L k (RegionHistory.winSep g) ak ν where
  hd := hd3
  hL := hL3
  hϱ := by rw [winSep_eq_minSep g hRb]; exact hR0
  weights := hak
  mass := hν
  massLe := hνL

/-- The mass bound from the flow: `μ = ν δ`, `δ ≤ D_δ`, `ν L^{2k} D_δ ≤ c_ν²` and `c_ν ≤ 1`
give `μ L^{2k} ≤ 1`. -/
theorem mass_le_one_of_flow {ν δ Dδ cν L : ℝ} {k : ℕ} (hν : 0 < ν)
    (hδD : δ ≤ Dδ) (hL : 0 ≤ L) (hcν0 : 0 ≤ cν) (hcν : cν ≤ 1)
    (h : ν * L ^ (2 * k) * Dδ ≤ cν ^ 2) :
    ν * δ * (L ^ k) ^ 2 ≤ 1 := by
  have h1 : ν * δ * (L ^ k) ^ 2 ≤ ν * L ^ (2 * k) * Dδ := by
    rw [← pow_mul, mul_comm k 2]
    have : 0 ≤ ν * L ^ (2 * k) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hδD this]
  have h2 : cν ^ 2 ≤ 1 := by nlinarith
  linarith

end Balaban.LargeField
