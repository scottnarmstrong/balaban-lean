/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.StepOutputConsts
public import Balaban.Polymer.LabelRootUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The output constants at the shared tower

`notes/phase1/TOWERJOIN.md` §2 (leaf 2).  For a tower `T : StepTower κmin` with
`detHullThreshold ≤ κmin` the record `stepOutputPhysical T h : StepOutputConsts 3 3` has the
rates, the determinant rate and the label constants of `T`:

* `k0 = T.κ0`, `kdec = T.κdec`, `k' = T.κ'`, `kout = 3/2 T.κdec`, `kH = 2 T.κdec - 1`,
  `kapp = T.κ`, `kdet = (T.κ - log 2 - 2 log(detDeg + 1))/18`, `Kc = 2 (K₀ + 1)`;
* `Kall = max (2 K₀) (rootUnionK 3 3 1 T.m₁ T.κ0)`, so `Ktot` pays the all-root label system of
  `LabelAct.extendRootUnion`.

All fields are definitional or arithmetic; the tower was retuned to `κ₀ = a_Ent + 2` (see
`StepTower`) and the hull threshold `detHullThreshold` of `DetPackageFromTower` is the closed
expression `stepHullMin` of the note (`stepHullMin` below is a definitional alias).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Polymer

/-- The closed threshold of `TOWERJOIN.md` §2; a definitional alias of `detHullThreshold`. -/
noncomputable abbrev stepHullMin : ℝ := detHullThreshold

/-- **The hull inequality at the tower** (`kout ≤` collar-hull rate of the determinant). -/
theorem StepTower.kout_le_hullRate {κmin : ℝ} (T : StepTower κmin) (h : stepHullMin ≤ κmin) :
    3 / 2 * T.κdec ≤ hullRate 3 3
      ((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) := by
  have := towerDetHullRate_ge T h
  have e : ((detDeg 3 3 + 1 : ℕ) : ℝ) = (detDeg 3 3 : ℝ) + 1 := by push_cast; ring
  unfold towerDetRate at this
  rw [e] at this
  linarith

/-- The constants of the tower as a `StepOutputConsts 3 3`. -/
noncomputable def stepOutputPhysical {κmin : ℝ} (T : StepTower κmin) (h : stepHullMin ≤ κmin) :
    StepOutputConsts 3 3 where
  k0 := T.κ0
  kdec := T.κdec
  k' := T.κ'
  kout := 3 / 2 * T.κdec
  kH := 2 * T.κdec - 1
  kapp := T.κ
  kdet := towerDetRate T.κ
  lhull := hullRate 3 3 (towerDetRate T.κ)
  Bhull := collarB 3 3
  Kc := 2 * (K0 3 3 T.κ0 + 1)
  Kall := max (2 * K0 3 3 T.κ0) (rootUnionK 3 3 1 T.m₁ T.κ0)
  Ktot := 2 * (K0 3 3 T.κ0 + 1) + max (2 * K0 3 3 T.κ0) (rootUnionK 3 3 1 T.m₁ T.κ0)
  k0_ent := T.κ0_two
  kdec_ge := T.κdec_lower
  kdec_ge' := T.hκdec
  k'_eq := T.κ'_eq
  kout_eq := rfl
  kH_eq := rfl
  kdec_le_kout := by have := T.κdec_lower; have := T.κ0_nonneg; linarith
  kout_le := by rw [T.κ'_eq]; linarith
  kH_ge := by
    have h1 := T.κdec_eq
    have h2 := T.κ0_nonneg
    have h3 := one_le_c1 3 3
    have h4 := T.κ'_eq
    have h5 := T.κdec_lower
    linarith
  kapp_ge := T.κ_lower
  kdet_eq := by
    have e : ((detDeg 3 3 + 1 : ℕ) : ℝ) = (detDeg 3 3 : ℝ) + 1 := by push_cast; ring
    unfold towerDetRate; rw [e]; norm_num
  kdet_ge := T.det_rate
  z_lt := by
    have h0 := T.det_z
    have e : ((detDeg 3 3 + 1 : ℕ) : ℝ) = (detDeg 3 3 : ℝ) + 1 := by push_cast; ring
    rw [e] at h0
    rw [Real.exp_neg]
    calc 2 * ((detDeg 3 3 : ℝ) + 1) ^ 2 * (Real.exp T.κ)⁻¹
        = ((detDeg 3 3 : ℝ) + 1) ^ 2 * (2 / Real.exp T.κ) := by ring
      _ < 1 := h0
  Bhull_eq := rfl
  lhull_eq := rfl
  lhull_ge := by have := towerDetHullRate_ge T h; linarith
  Kc_eq := rfl
  Kall_ge := le_max_left _ _
  Ktot_eq := rfl

/-- The record is inhabited by `stepOutputPhysical`, with the field equations exposed. -/
theorem stepOutput_consts_physical {κmin : ℝ} (T : StepTower κmin) (h : stepHullMin ≤ κmin) :
    ∃ C : StepOutputConsts 3 3, C.k0 = T.κ0 ∧ C.kdec = T.κdec ∧ C.k' = T.κ' ∧
      C.kout = 3 / 2 * T.κdec ∧ C.kH = 2 * T.κdec - 1 ∧ C.kapp = T.κ ∧
      C.kdet = (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18 ∧
      C.Bhull = collarB 3 3 ∧ C.lhull = hullRate 3 3 C.kdet ∧
      C.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧
      C.Kall = max (2 * K0 3 3 T.κ0) (rootUnionK 3 3 1 T.m₁ T.κ0) ∧ C.Ktot = C.Kc + C.Kall := by
  refine ⟨stepOutputPhysical T h, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  have e : ((detDeg 3 3 + 1 : ℕ) : ℝ) = (detDeg 3 3 : ℝ) + 1 := by push_cast; ring
  show towerDetRate T.κ = _
  unfold towerDetRate; rw [e]

/-- `K_tot` of the physical record pays the all-root label constant. -/
theorem rootUnionK_le_stepOutputPhysical {κmin : ℝ} (T : StepTower κmin)
    (h : stepHullMin ≤ κmin) :
    rootUnionK 3 3 1 T.m₁ T.κ0 ≤ (stepOutputPhysical T h).Kall := le_max_right _ _

end Balaban.Inhabited
