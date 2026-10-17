/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.Flow.MatrixInfty
public import Balaban.Flow.TriangularChart

/-!
# Analytic complex chart for the positive-mass RG matrix

The mass and coupling are complex coordinates, while the lattice sums and
scale parameters are fixed. The rational matrix entries are analytic wherever
`a + v ≠ 0`. Uniform triangular bounds require a smaller open chart, as
provided by `exists_triangular_complex_chart` after strict margins are shown.
-/

@[expose] public section

namespace Balaban.Flow

/-- The diagonal estimate has a strict margin on the positive-mass range;
the landed weak estimate alone would not produce an open complex chart. -/
theorem InftyRange.A33_gt {a v τ c₁ c₂ : ℝ} (h : InftyRange a v τ c₁ c₂) :
    1 / 4 < infA33 a v τ c₁ c₂ := by
  rw [infA33_eq _ _ _ _ _ h.sum_pos]
  have hρ : 4 / 5 ≤ a / (a + v) := h.rho_bounds.1
  have hρ2 : 16 / 25 ≤ (a / (a + v)) ^ 2 := by nlinarith
  have hb : 1 ≤ 1 + v ^ 2 * (c₁ - v * c₂) := by
    nlinarith [sq_nonneg v, h.diff_pos]
  have h1 : 16 / 25 ≤ (a / (a + v)) ^ 2 * (1 + v ^ 2 * (c₁ - v * c₂)) := by
    calc
      (16 / 25 : ℝ) = (16 / 25) * 1 := by ring
      _ ≤ (a / (a + v)) ^ 2 * (1 + v ^ 2 * (c₁ - v * c₂)) := by gcongr
  have h2 : 0 ≤ (a / (a + v)) ^ 2 * (v / (a + v)) * infB1 v τ c₁ := by
    have := h.w_bounds.1
    have := h.B1_bounds.1
    positivity
  linarith

theorem matrixInfty_analyticOnNhd_fixed (τ c₁ c₂ ε : ℂ) (i j : Fin 3) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => matrixInfty p.1 p.2 τ c₁ c₂ ε i j)
      {p | p.1 + p.2 ≠ 0} := by
  intro p hp
  have ha : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) p := analyticAt_fst
  have hv : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) p := analyticAt_snd
  have hs : p.1 + p.2 ≠ 0 := hp
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      matrixInfty_00, matrixInfty_01, matrixInfty_02,
      matrixInfty_10, matrixInfty_11, matrixInfty_12,
      matrixInfty_20, matrixInfty_21, matrixInfty_22] <;>
    first
    | exact analyticAt_const
    | exact ha
    | dsimp [infA31, infA32, infA33, infB1, infB2]; fun_prop (disch := simp [hs])

/-- An actual open complex chart around every positive-mass real reference datum,
with fixed `τ,c₁,c₂,ε` and complex-varying `a,v`. -/
theorem InftyRange.exists_complex_chart {a v τ c₁ c₂ ε : ℝ}
    (h : InftyRange a v τ c₁ c₂) (hε : 0 < ε) :
    ∃ P : Set (ℂ × ℂ), IsOpen P ∧ ((a : ℂ), (v : ℂ)) ∈ P ∧
      P ⊆ {p | p.1 + p.2 ≠ 0} ∧
      (∀ i j, AnalyticOnNhd ℂ
        (fun p : ℂ × ℂ => matrixInfty p.1 p.2 (τ : ℂ) (c₁ : ℂ) (c₂ : ℂ) (ε : ℂ) i j) P) ∧
      ∀ p ∈ P, TriangularBounds
        (matrixInfty p.1 p.2 (τ : ℂ) (c₁ : ℂ) (c₂ : ℂ) (ε : ℂ)) ε := by
  have hmat : matrixInfty (a : ℂ) (v : ℂ) (τ : ℂ) (c₁ : ℂ) (c₂ : ℂ) (ε : ℂ) =
      (matrixInfty a v τ c₁ c₂ ε).map (algebraMap ℝ ℂ) := by
    simpa using (matrixInfty_map (algebraMap ℝ ℂ) a v τ c₁ c₂ ε).symm
  apply exists_triangular_complex_chart
    (U := {p : ℂ × ℂ | p.1 + p.2 ≠ 0})
    (p₀ := ((a : ℂ), (v : ℂ)))
    (A := fun p => matrixInfty p.1 p.2 (τ : ℂ) (c₁ : ℂ) (c₂ : ℂ) (ε : ℂ))
  · exact isOpen_ne_fun (continuous_fst.add continuous_snd) continuous_const
  · change (a : ℂ) + (v : ℂ) ≠ 0
    exact_mod_cast h.sum_pos.ne'
  · exact matrixInfty_analyticOnNhd_fixed _ _ _ _
  · intro p _
    exact ⟨rfl, rfl, rfl⟩
  · intro p _
    constructor
    · simp
    · simpa using hε.le
  · rw [hmat]
    simp only [Matrix.map_apply, matrixInfty_00, Complex.coe_algebraMap,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos h.a_pos]
    linarith [h.a_lo]
  · rw [hmat]
    simp only [Matrix.map_apply, matrixInfty_22, Complex.coe_algebraMap,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith [h.A33_gt])]
    exact h.A33_gt
  · rw [hmat]
    simp only [Matrix.map_apply, matrixInfty_20, Complex.coe_algebraMap,
      Complex.norm_real, Real.norm_eq_abs]
    nlinarith [h.abs_A31_le hε.le]
  · rw [hmat]
    simp only [Matrix.map_apply, matrixInfty_21, Complex.coe_algebraMap,
      Complex.norm_real, Real.norm_eq_abs]
    linarith [h.abs_A32_le]

end Balaban.Flow
