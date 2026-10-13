/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetRotation
public import Balaban.Inhabited.DetOutputTermsWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the spin-rotation invariance of the determinant terms

`d = L = 3`, `N = 2`.  At the step `hatStep m₁ 1 1 1` and the data supplied by the numerical tower
(`directWitness_core_amp`), the rotation by `π/2`, `Q = !![0, -1; 1, 0]` (real, `Qᵀ Q = 1`,
`Q ≠ 1`) maps the datum of the step to a different datum of the chart, and the terms of the
record `DetExpansionLocC` at the rotated datum equal those at the original datum
(`detRotation_witness`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Analysis Balaban.SmallField.Def6 Balaban.Polymer Balaban.Inhabited.LevelStep Matrix

/-- The rotation by `π/2` of the plane. -/
def rotQuarter : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem rotQuarter_transpose_mul : rotQuarterᵀ * rotQuarter = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotQuarter, Matrix.mul_apply, Fin.sum_univ_two]

theorem rotQuarter_ne_one : rotQuarter ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [rotQuarter] at this

open Classical in
/-- **Non-vacuity of `exists_detExpansionLocC_rot_real`.**  At the step `hatStep m₁ 1 1 1` for one
choice of `(m₁, BG, κ, t)`: the quarter rotation `Q = !![0, -1; 1, 0]` satisfies `Qᵀ Q = 1`,
`Q ≠ 1`; the datum `D'` of the step and its rotation are data of the chart; the rotated datum
differs from `D'`; and for every `z` there is a record `E` with a positive rate whose terms are
unchanged by the rotation. -/
theorem detRotation_witness :
    ∃ (m₁ : ℕ) (t : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ 1 1 1 ∧ 0 < t ∧ rotQuarterᵀ * rotQuarter = 1 ∧ rotQuarter ≠ 1 ∧
      XiCData S.G' S.a S.ν (1 + 1) 1 t S.D' ∧
      XiCData S.G' S.a S.ν (1 + 1) 1 t (S.D'.rot (cmat rotQuarter)) ∧
      S.D'.rot (cmat rotQuarter) ≠ S.D' ∧
      ∃ κ'' cdet : ℝ, 0 < κ'' ∧ ∀ z, ∃ E : DetExpansionLocC S 0 z t κ'' cdet,
        ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (1 + 1) 1 t D →
          ∀ T, E.term (D.rot (cmat rotQuarter)) T = E.term D T := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, -⟩ := directWitness_core_amp 2 1
  have hκ57 : (57 : ℝ) ≤ κ := by
    have e : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
    rw [e] at hκ
    linarith
  have hz := detDeg_three_rate hκ57
  have hd0 : 0 < (3 : ℕ) := by norm_num
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin 3 3 2 BG κ (xiC1 3 * t) := by
      have : 0 < K4 3 3 2 BG κ := K4_pos hC.hS.fam.2.1 hd0
      have := one_le_xiC1 3
      unfold decDomMargin; positivity
    linarith
  set S := hatStep m₁ 1 1 1 with hS
  have hD : XiCData S.G' (compWeight 3 1) nuW (1 + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hconn : HatConn S.G' := LevelPair.hatConn
  have hN : (3 : ℕ) ^ 0 ∣ 9 := by norm_num
  have hlam : 0 < κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) := by
    have := log_detDeg_three_lt
    linarith
  refine ⟨m₁, t, S, rfl, ht0, rotQuarter_transpose_mul, rotQuarter_ne_one, hD,
    xiCData_rot rotQuarter_transpose_mul hD, ?_,
    (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)),
    ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLog 3 3 (S.a 1) (S.a₁ / ((3 : ℕ) : ℝ) ^ 2) κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))), by positivity, fun z => ?_⟩
  · intro h
    have := congrArg (fun D : BgData S.G' 2 => D.h 0 0) h
    have e1 : (S.D'.rot (cmat rotQuarter)).h 0 0 = 0 := by
      show (cmat rotQuarter *ᵥ S.D'.h 0) 0 = 0
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, cmat, rotQuarter, S.hh₀, hS, hatStep,
        unitVec]
    have e2 : S.D'.h 0 0 = 1 := by
      rw [S.hh₀]; simp [hS, hatStep, unitVec]
    simp only [e1, e2] at this
    exact zero_ne_one this
  · obtain ⟨E, -, hE⟩ := exists_detExpansionLocC_rot_real (m₀ := 0) S hC hδc hMX hdm hα hsmX
      hconn hN hz z rotQuarter_transpose_mul
    exact ⟨E, hE⟩

end Balaban.Inhabited
