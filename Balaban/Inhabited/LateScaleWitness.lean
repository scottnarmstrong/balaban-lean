/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ChiYWitness
public import Balaban.LargeField.History.LateYDirection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Instances of the late-scale direction theorems (`LateScaleWitness`)

These are instances showing that the hypotheses of `parentPsi_direction_of_chiY_ne_zero`,
`parentPsi_norm_of_tested` and `parentPsi_r3_of_tested` are jointly satisfiable: a small-field
context `ctxLate` (the geometry, tolerances and data of `ctxY`) whose cube mass at scale `1` is the
positive running mass `sfBgMassAt L 1 (1/9) = 1/81`, with `χ_1(Y) = 1` at the constant unit field.

At the constant field the conclusions are degenerate (`‖Ψ(s) - h‖ = 0`); the point is only that
all hypotheses hold together (the landed context `ctxY` has cube mass `0`, so none held there).

The late-scale parent-domain theorem is NOT proved, and the mass alignment `r3` at the outer sites
is NOT proved (open; a question to the author is pending).  Nothing here concerns outer sites.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7.Wit
  Balaban.SmallField.Def6v2

/-- The running mass of the instance, `ν₁ = 1/9`. -/
noncomputable def lateNu : ℝ := 1 / 9

/-- The running constants of `csY` with the cube mass `μ_k = ν₁ L^{-2k}` (`sfBgMassAt`). -/
noncomputable def csLate : OpConsts :=
  { csY with mu := fun k => sfBgMassAt wS.L k lateNu }

/-- The small-field context of `ctxY` with the positive cube mass of `csLate`. -/
noncomputable def ctxLate :
    SFCtx wS (sides wS.L 1 nMulti) wR (27 * M1y) 1 2 1 wC7.m₁ (bgR0 3 3) where
  geo := geoY
  hnn := sides_hnn wS.L 1 nMulti
  hkK := le_rfl
  cs := csLate
  m₀ := a1
  sf := wSF wν₀ 3
  N₁ := sfIdx wS.L a1 (sides wS.L 1 nMulti) 1
  hT := sfIdx_hT geoY M_eq_pow_y

theorem ctxLate_mu : ctxLate.cs.mu 1 = sfBgMassAt wS.L 1 lateNu := rfl

theorem ctxLate_delta : ctxLate.cs.delta = csY.delta := rfl

theorem lateNu_pos : 0 < lateNu := by unfold lateNu; norm_num

theorem lateNu_le_one : lateNu ≤ 1 := by unfold lateNu; norm_num

theorem ctxLate_mu_one_val : ctxLate.cs.mu 1 = lateNu * ((3 : ℝ) ^ 1)⁻¹ ^ 2 := by
  rw [ctxLate_mu]; rfl

theorem ctxLate_weights_one : ctxLate.weights 1 = 5 / 4 := ctxY_weights_one

/-- **The cube `BgHyp` with the positive mass**: the solver premise at `k = 1` is
`μ (L^1)^2 = ν₁ = 1/9 ≤ 1`. -/
theorem hbLate : BgHyp wS.d wS.L 1 (minSep wS.L ctxLate.geo.M1) ctxLate.weights
    (ctxLate.cs.mu 1) where
  hd := le_of_eq rfl
  hL := le_of_eq rfl
  hϱ := bgR0_le_minSep_y
  weights := by
    intro j hj1 hj
    obtain rfl : j = 1 := by omega
    rw [ctxLate_weights_one]
    constructor <;> norm_num
  mass := by
    rw [ctxLate_mu]
    unfold sfBgMassAt physMass lateNu
    have : (0 : ℝ) < wS.L := by
      have : wS.L = 3 := rfl
      rw [this]; norm_num
    positivity
  massLe := by
    rw [ctxLate_mu]
    have h := physMass_mul_sq (L := wS.L) 1 lateNu
    unfold sfBgMassAt
    rw [h]
    exact lateNu_le_one

/-- `χ_1(Y) = 1` at the constant unit field in `ctxLate`, for every `Y`, at positive mass. -/
theorem chiY_ctxLate (Y : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :
    ctxLate.chiY Y (fun _ => whv) whv = 1 :=
  chiY_const_eq_one ctxLate Y whv whv_sum_sq hbLate le_rfl csY_delta_one_pos

/-! ### The radius `η < 1` -/

theorem lateExp_ge {l : ℝ} (hl : 11 ≤ l) : 56 ≤ Real.exp (l / 2) := by
  have h1 : 1 + l / 4 + (l / 4) ^ 2 / 2 ≤ Real.exp (l / 4) :=
    Real.quadratic_le_exp_of_nonneg (by linarith)
  have h2 : Real.exp (l / 2) = Real.exp (l / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : (15 / 2 : ℝ) ≤ Real.exp (l / 4) := by nlinarith
  rw [h2]
  nlinarith

theorem csY_delta_one_lt : 16 * csY.delta 1 < 1 := by
  rw [csY_delta_one]
  have h4 : Real.exp (-lam1 / 2) = (Real.exp (lam1 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have h3 := lateExp_ge runLam_one_ge
  have hpos : 0 < Real.exp (lam1 / 2) := Real.exp_pos _
  rw [h4, show 16 * (2 * (Real.exp (lam1 / 2))⁻¹) = 32 / Real.exp (lam1 / 2) by
    field_simp; norm_num, div_lt_one hpos]
  exact lt_of_lt_of_le (by norm_num) h3

theorem csY_delta_zero_le : csY.delta 0 ≤ 2 * Real.exp (-runLam (5 / 4) wβs 0 / 2) := by
  have hb : 0 < wβs 0 * (5 / 4) := by
    have := wβ_pos; simp only [wβs]; positivity
  rw [csY_delta, deltaRun_eq A0y wS.p0 (5 / 4) wβs 0 hb]
  have hl1 : 0 < lam1 := lam1_pos
  have hl0 : 0 ≤ runLam (5 / 4) wβs 0 := by
    unfold runLam
    apply Real.log_nonneg
    have := wβ_pos
    have := wβ_log_ge
    have h : 1 ≤ wβ * (5 / 4) := by
      by_contra hc
      have hc' := (not_le.mp hc).le
      have := Real.log_nonpos (by positivity) hc'
      linarith
    simpa [wβs] using h
  have hle : runLam (5 / 4) wβs 0 ≤ lam1 := by
    unfold runLam lam1 runLam
    refine Real.log_le_log hb ?_
    have := wβ_pos
    simp only [wβs]
    norm_num
    nlinarith
  have hA : A0y * runLam (5 / 4) wβs 0 ^ wS.p0 ≤ 2 := by
    have h2 : A0y * lam1 ^ wS.p0 = 2 := by
      have h0 : lam1 ^ wS.p0 ≠ 0 := pow_ne_zero _ lam1_pos.ne'
      unfold A0y; field_simp
    calc _ ≤ A0y * lam1 ^ wS.p0 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hl0 hle _) A0y_pos.le
      _ = 2 := h2
  calc _ ≤ Real.exp (-runLam (5 / 4) wβs 0 / 2) * 2 :=
        mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
    _ = _ := by ring

theorem csY_delta_zero_lt : 27 * csY.delta 0 < 1 := by
  have hl0 : 11 ≤ runLam (5 / 4) wβs 0 := by
    have := wβ_log_ge
    unfold runLam; simpa [wβs] using this
  have h4 : Real.exp (-runLam (5 / 4) wβs 0 / 2) = (Real.exp (runLam (5 / 4) wβs 0 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have h3 := lateExp_ge hl0
  have hpos : 0 < Real.exp (runLam (5 / 4) wβs 0 / 2) := Real.exp_pos _
  have := csY_delta_zero_le
  rw [h4] at this
  have h5 : 27 * (2 * (Real.exp (runLam (5 / 4) wβs 0 / 2))⁻¹) < 1 := by
    rw [show 27 * (2 * (Real.exp (runLam (5 / 4) wβs 0 / 2))⁻¹) =
      54 / Real.exp (runLam (5 / 4) wβs 0 / 2) by field_simp; norm_num, div_lt_one hpos]
    exact lt_of_lt_of_le (by norm_num) h3
  linarith

theorem lateEta_lt_one :
    max (3 * (wS.d : ℝ) * wS.L * ctxLate.cs.delta 0)
      (4 * ((wS.d : ℝ) + 1) * ctxLate.cs.delta (0 + 1)) < 1 := by
  have hd : (wS.d : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]
  have hL : (wS.L : ℝ) = 3 := by norm_num [wS, setting, typing, typing0]
  rw [hd, hL]
  refine max_lt ?_ ?_
  · have := csY_delta_zero_lt
    show 3 * 3 * 3 * csY.delta 0 < 1
    linarith
  · have := csY_delta_one_lt
    show 4 * (3 + 1) * csY.delta 1 < 1
    linarith

/-- **The late-scale direction theorems have a landed instance.**  In `ctxLate` (cube mass
`sfBgMassAt L 1 (1/9)`, `χ_1(Y) = 1` at the constant unit field), with `Y` the whole torus, there is
a tested site, and at every tested site the three conclusions hold with all hypotheses discharged.
The conclusions are degenerate here (the datum equals `h`). -/
theorem lateDirection_instance :
    ∃ s, s ∈ testedSites ctxLate (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1))) ∧
      ∀ s ∈ testedSites ctxLate (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1))),
        rn (fun i => parentPsi ctxLate (fun _ => whv) s i - whv i) <
            2 * ctxLate.cs.delta 1 / Real.sqrt lateNu ∧
        |rn (parentPsi ctxLate (fun _ => whv) s) - 1| < (wS.d + 1) * ctxLate.cs.delta 1 ∧
        sfBgMassAt wS.L 1 lateNu *
            ((wS.L : ℝ) ^ (ctxLate.genW (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1)))).layerIndex s) ^ 2 *
          |1 - (∑ i, parentPsi ctxLate (fun _ => whv) s i * whv i) /
              rn (parentPsi ctxLate (fun _ => whv) s)| <
          (max (3 * wS.d * wS.L * ctxLate.cs.delta 0)
            (4 * (wS.d + 1) * ctxLate.cs.delta (0 + 1))) ^ 2 := by
  have hne : ctxLate.chiY Set.univ (fun _ => whv) whv ≠ 0 := by
    rw [chiY_ctxLate]; exact one_ne_zero
  refine ⟨(exists_tested_site ctxLate _ (Set.mem_univ _)).choose,
    (exists_tested_site ctxLate _ (Set.mem_univ _)).choose_spec, fun s hs => ?_⟩
  exact ⟨parentPsi_direction_of_chiY_ne_zero ctxLate _ _ whv hne lateNu_pos lateNu_le_one
      ctxLate_mu hs,
    parentPsi_norm_of_tested ctxLate _ _ whv hne hbLate hs,
    parentPsi_r3_of_tested ctxLate _ _ whv hne hbLate whv_norm lateNu_pos lateNu_le_one
      ctxLate_mu lateEta_lt_one hs⟩

end Balaban.LargeField.Def7
