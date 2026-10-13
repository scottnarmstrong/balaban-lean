/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGScalars
public import Balaban.Inhabited.StepOutputConsts
public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Fluctuation.DetRateGeneral
public import Balaban.Polymer.LabelRootUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The output constants of one step from the general tower

For a tower `T : StepTowerG d L N κmin` and a hull hypothesis on the interpolation rate `T.κ`
(`2 d L (1 + B) (3/2 κ_dec + c₁ log 2) + log 2 + 2 log (detDeg d L + 1) ≤ κ`), the output
constants of one step exist as a `StepOutputConsts d L` with the rates, the determinant rate and
the label constants of `T`.  The fixed `d = L = 3`, `N = 2` statements of
`StepOutputPhysical` are corollaries through `StepTower.toG`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Polymer

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- **The hull inequality at the general tower** (`kout ≤` collar-hull rate of the determinant). -/
theorem kout_le_hullRate
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) :
    3 / 2 * T.κdec ≤ hullRate d L (detRateG d L T.κ) :=
  hullRate_ge_general (by have := T.hd; omega) (by have := T.hL; omega) hhull

/-- **The output constants of one step from the general tower.** -/
theorem exists_outputConsts
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) :
    ∃ C : StepOutputConsts d L, C.k0 = T.κ0 ∧ C.kdec = T.κdec ∧ C.k' = T.κ' ∧
      C.kout = 3 / 2 * T.κdec ∧ C.kH = 2 * T.κdec - 1 ∧ C.kapp = T.κ ∧
      C.kdet = (T.κ - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L) ∧
      C.Bhull = collarB d L ∧ C.lhull = hullRate d L C.kdet ∧
      C.Kc = 2 * (K0 d L T.κ0 + 1) ∧
      C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0) ∧ C.Ktot = C.Kc + C.Kall := by
  have e : ((detDeg d L + 1 : ℕ) : ℝ) = (detDeg d L : ℝ) + 1 := by push_cast; ring
  have hdet : detRateG d L T.κ =
      (T.κ - Real.log 2 - 2 * Real.log ((detDeg d L : ℝ) + 1)) / (2 * d * L) := by
    unfold detRateG; rw [e]
  have hout := T.kout_le_hullRate hhull
  refine ⟨
    { k0 := T.κ0
      kdec := T.κdec
      k' := T.κ'
      kout := 3 / 2 * T.κdec
      kH := 2 * T.κdec - 1
      kapp := T.κ
      kdet := detRateG d L T.κ
      lhull := hullRate d L (detRateG d L T.κ)
      Bhull := collarB d L
      Kc := 2 * (K0 d L T.κ0 + 1)
      Kall := max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0)
      Ktot := 2 * (K0 d L T.κ0 + 1) + max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0)
      k0_ent := T.κ0_ge
      kdec_ge := T.κdec_lower
      kdec_ge' := T.hκdec
      k'_eq := T.κ'_eq
      kout_eq := rfl
      kH_eq := rfl
      kdec_le_kout := by have := T.κdec_lower; have := T.κ0_nonneg; linarith
      kout_le := by rw [T.κ'_eq]; linarith [T.κ0_nonneg]
      kH_ge := by
        have h1 := T.κdec_eq
        have h2 := T.κ0_nonneg
        have h3 := one_le_c1 d L
        have h4 := T.κ'_eq
        have h5 := T.κdec_lower
        linarith
      kapp_ge := T.κ_lower
      kdet_eq := hdet
      kdet_ge := by
        have := T.det_rate
        rw [hdet]; rw [e] at this; exact this
      z_lt := by
        have h0 := T.det_z
        rw [e] at h0
        rw [Real.exp_neg]
        calc 2 * ((detDeg d L : ℝ) + 1) ^ 2 * (Real.exp T.κ)⁻¹
            = ((detDeg d L : ℝ) + 1) ^ 2 * (2 / Real.exp T.κ) := by ring
          _ < 1 := h0
      Bhull_eq := rfl
      lhull_eq := by
        unfold hullRate; rfl
      lhull_ge := hout
      Kc_eq := rfl
      Kall_ge := le_max_left _ _
      Ktot_eq := rfl }, rfl, rfl, rfl, rfl, rfl, rfl, hdet, rfl, rfl, rfl, rfl, rfl⟩

end StepTowerG

/-- The fixed hull threshold implies the general hull hypothesis at `T.toG`. -/
theorem StepTower.hhull_toG_of_stepHullMin {κmin : ℝ} (T : StepTower κmin)
    (h : detHullThreshold ≤ κmin) :
    2 * (3 : ℕ) * (3 : ℕ) * (1 + collarB 3 3) * (3 / 2 * T.toG.κdec + c1 3 3 * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) ≤ T.toG.κ := by
  unfold detHullThreshold at h
  have := T.κmin_le
  have e : 3 / 2 * T.κdec = 3 / 2 * (100 * (aEnt 3 3 + 2 + 3375 + 10)) := by
    rw [T.κdec_eq, T.κ0_eq, c1_three]
  show _ ≤ T.κ
  rw [collarB_three, c1_three]
  have e2 : T.toG.κdec = T.κdec := rfl
  rw [e2]
  rw [e]
  push_cast at h ⊢
  linarith

end Balaban.Inhabited
