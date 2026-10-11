/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.RGParam

/-!
# The linear part of the renormalization-group system at `λ = ∞`

Balaban P4 (5.21)-(5.22) at `1/λ = 0` (`notes/phase1/SMALLFIELD.md` §3.4, Lemma 3.1).  The
matrix `A` of the system `A ξ + c̃(ξ, p) = f̃(ξ, p)` is lower triangular with entries
`a₁₁ = a`, `a₂₁ = 0`, `a₂₂ = 1` and `a₃₁, a₃₂, a₃₃` explicit rational functions of
`(a, v, τ, c₁, c₂, ε)`; here `a = a_{k+1}`, `v = ν_{k+1}`, `ε = ε_{k+1}`, `τ ∈ [0,1]` is the factor
printed `1 - L^{-2m}` in (5.13), and `c₁ = c₁(v)`, `c₂ = c₂(v)` are the lattice sums of (5.13).

The entries are defined over an arbitrary field, so the same definitions serve real data
(Lemma 3.1) and complex data (analytic dependence on the parameters, conjugation symmetry).

* `matrixInfty`: the matrix;
* `InftyRange`: the parameter range of Lemma 3.1;
* `triangularBounds_matrixInfty` (**Lemma 3.1**): for real parameters in the range and `ε ≥ 0`,
  the matrix satisfies `TriangularBounds` with the parameter `ε`;
* `matrixInfty_map`, `matrixInfty_conj`: compatibility with ring homomorphisms, hence with
  complex conjugation (hypothesis `hAσ` of `rg_solution_real`).
-/

@[expose] public section

namespace Balaban.Flow

section Entries

variable {𝕜 : Type*} [Field 𝕜]

/-- The bracket `1 + (v/12) τ - v² c₁` of (5.21). -/
def infB1 (v τ c₁ : 𝕜) : 𝕜 := 1 + v / 12 * τ - v ^ 2 * c₁

/-- The bracket `-1 + ((a - v)/24) τ - a v c₁ + ½ (a + v) v² c₂` of (5.21). -/
def infB2 (a v τ c₁ c₂ : 𝕜) : 𝕜 :=
  -1 + (a - v) / 24 * τ - a * v * c₁ + (a + v) * v ^ 2 * c₂ / 2

/-- `a₃₁ = ε a²/(a+v)² [1 + …] + ε a³/(a+v)³ [-1 + …]`. -/
def infA31 (a v τ c₁ c₂ ε : 𝕜) : 𝕜 :=
  ε * (a ^ 2 / (a + v) ^ 2 * infB1 v τ c₁) + ε * (a ^ 3 / (a + v) ^ 3 * infB2 a v τ c₁ c₂)

/-- `a₃₂ = a² v/(a+v)³ [-1 + …]`. -/
def infA32 (a v τ c₁ c₂ : 𝕜) : 𝕜 := a ^ 2 * v / (a + v) ^ 3 * infB2 a v τ c₁ c₂

/-- `a₃₃ = ½ a²/(a+v)² [1 + v² c₁ - v³ c₂] + a² v/(a+v)³ [1 + …]`. -/
def infA33 (a v τ c₁ c₂ : 𝕜) : 𝕜 :=
  1 / 2 * (a ^ 2 / (a + v) ^ 2) * (1 + v ^ 2 * c₁ - v ^ 3 * c₂) +
    a ^ 2 * v / (a + v) ^ 3 * infB1 v τ c₁

/-- **The matrix (5.21) at `λ = ∞`.** -/
def matrixInfty (a v τ c₁ c₂ ε : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![a, 0, 0; 0, 1, 0; infA31 a v τ c₁ c₂ ε, infA32 a v τ c₁ c₂, infA33 a v τ c₁ c₂]

@[simp] theorem matrixInfty_00 (a v τ c₁ c₂ ε : 𝕜) : matrixInfty a v τ c₁ c₂ ε 0 0 = a := rfl
@[simp] theorem matrixInfty_01 (a v τ c₁ c₂ ε : 𝕜) : matrixInfty a v τ c₁ c₂ ε 0 1 = 0 := rfl
@[simp] theorem matrixInfty_02 (a v τ c₁ c₂ ε : 𝕜) : matrixInfty a v τ c₁ c₂ ε 0 2 = 0 := rfl
@[simp] theorem matrixInfty_10 (a v τ c₁ c₂ ε : 𝕜) : matrixInfty a v τ c₁ c₂ ε 1 0 = 0 := rfl
@[simp] theorem matrixInfty_11 (a v τ c₁ c₂ ε : 𝕜) : matrixInfty a v τ c₁ c₂ ε 1 1 = 1 := rfl
@[simp] theorem matrixInfty_12 (a v τ c₁ c₂ ε : 𝕜) : matrixInfty a v τ c₁ c₂ ε 1 2 = 0 := rfl
@[simp] theorem matrixInfty_20 (a v τ c₁ c₂ ε : 𝕜) :
    matrixInfty a v τ c₁ c₂ ε 2 0 = infA31 a v τ c₁ c₂ ε := rfl
@[simp] theorem matrixInfty_21 (a v τ c₁ c₂ ε : 𝕜) :
    matrixInfty a v τ c₁ c₂ ε 2 1 = infA32 a v τ c₁ c₂ := rfl
@[simp] theorem matrixInfty_22 (a v τ c₁ c₂ ε : 𝕜) :
    matrixInfty a v τ c₁ c₂ ε 2 2 = infA33 a v τ c₁ c₂ := rfl

/-- The matrix commutes with ring homomorphisms of fields. -/
theorem matrixInfty_map {𝕜' : Type*} [Field 𝕜'] (φ : 𝕜 →+* 𝕜') (a v τ c₁ c₂ ε : 𝕜) :
    (matrixInfty a v τ c₁ c₂ ε).map φ =
      matrixInfty (φ a) (φ v) (φ τ) (φ c₁) (φ c₂) (φ ε) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixInfty, infA31, infA32, infA33, infB1, infB2, Matrix.map_apply, map_ofNat]

/-- Compatibility with complex conjugation (the hypothesis `hAσ` of `rg_solution_real`). -/
theorem matrixInfty_conj (a v τ c₁ c₂ ε : ℂ) :
    (matrixInfty a v τ c₁ c₂ ε).map (starRingEnd ℂ) =
      matrixInfty (starRingEnd ℂ a) (starRingEnd ℂ v) (starRingEnd ℂ τ) (starRingEnd ℂ c₁)
        (starRingEnd ℂ c₂) (starRingEnd ℂ ε) :=
  matrixInfty_map _ _ _ _ _ _ _

end Entries

section Range

/-- The parameter range of Lemma 3.1: `a ∈ [9/10, 3/2]`, `0 < v ≤ 7/32`, `τ ∈ [0,1]`,
`0 < cᵢ < 1/20`, `0 < c₁ - v c₂ < c₁`. -/
structure InftyRange (a v τ c₁ c₂ : ℝ) : Prop where
  a_lo : 9 / 10 ≤ a
  a_hi : a ≤ 3 / 2
  v_pos : 0 < v
  v_hi : v ≤ 7 / 32
  τ_nonneg : 0 ≤ τ
  τ_le : τ ≤ 1
  c₁_pos : 0 < c₁
  c₁_lt : c₁ < 1 / 20
  c₂_pos : 0 < c₂
  c₂_lt : c₂ < 1 / 20
  diff_pos : 0 < c₁ - v * c₂
  diff_lt : c₁ - v * c₂ < c₁

namespace InftyRange

variable {a v τ c₁ c₂ : ℝ} (h : InftyRange a v τ c₁ c₂)
include h

theorem a_pos : 0 < a := by linarith [h.a_lo]

theorem sum_pos : 0 < a + v := by linarith [h.a_lo, h.v_pos]

theorem v2c₁_le : v ^ 2 * c₁ ≤ 1 / 300 := by
  have hv : v ^ 2 ≤ 49 / 1024 := by nlinarith [h.v_pos, h.v_hi]
  nlinarith [h.c₁_pos, h.c₁_lt, sq_nonneg v]

/-- `B₁ = 1 + (v/12) τ - v² c₁ ∈ (0, 51/50]`. -/
theorem B1_bounds : 0 < infB1 v τ c₁ ∧ infB1 v τ c₁ ≤ 51 / 50 := by
  have := h.v2c₁_le
  unfold infB1
  constructor <;> nlinarith [h.τ_nonneg, h.τ_le, h.v_pos, h.v_hi, mul_nonneg h.v_pos.le h.τ_nonneg,
    mul_le_mul h.v_hi h.τ_le h.τ_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 32),
    mul_nonneg (sq_nonneg v) h.c₁_pos.le]

/-- `B₂ ∈ [-51/50, 0)`. -/
theorem B2_bounds : -(51 / 50) ≤ infB2 a v τ c₁ c₂ ∧ infB2 a v τ c₁ c₂ < 0 := by
  unfold infB2
  have hav : a * v ≤ 3 / 2 * (7 / 32) := mul_le_mul h.a_hi h.v_hi h.v_pos.le (by norm_num)
  have h1 : a * v * c₁ ≤ 3 / 2 * (7 / 32) * (1 / 20) :=
    mul_le_mul hav h.c₁_lt.le h.c₁_pos.le (by norm_num)
  have h1' : 0 ≤ a * v * c₁ := by have := h.a_pos; have := h.v_pos; have := h.c₁_pos; positivity
  have hv2 : v ^ 2 ≤ 49 / 1024 := by nlinarith [h.v_pos, h.v_hi]
  have hs : a + v ≤ 3 / 2 + 7 / 32 := by linarith [h.a_hi, h.v_hi]
  have h2 : (a + v) * v ^ 2 ≤ (3 / 2 + 7 / 32) * (49 / 1024) :=
    mul_le_mul hs hv2 (sq_nonneg v) (by norm_num)
  have h2' : (a + v) * v ^ 2 * c₂ ≤ (3 / 2 + 7 / 32) * (49 / 1024) * (1 / 20) :=
    mul_le_mul h2 h.c₂_lt.le h.c₂_pos.le (by norm_num)
  have h2'' : 0 ≤ (a + v) * v ^ 2 * c₂ := by
    have := h.sum_pos; have := h.c₂_pos; positivity
  have h3 : (a - v) / 24 * τ ≤ 3 / 2 / 24 := by
    have : (a - v) / 24 * τ ≤ (a - v) / 24 := by
      have : 0 ≤ (a - v) / 24 := by linarith [h.a_lo, h.v_hi]
      nlinarith [h.τ_le, h.τ_nonneg]
    linarith [h.a_hi, h.v_pos]
  have h3' : 0 ≤ (a - v) / 24 * τ :=
    mul_nonneg (by linarith [h.a_lo, h.v_hi]) h.τ_nonneg
  constructor <;> nlinarith

/-- `ρ = a/(a+v) ∈ [4/5, 1]`. -/
theorem rho_bounds : 4 / 5 ≤ a / (a + v) ∧ a / (a + v) ≤ 1 := by
  have hs := h.sum_pos
  constructor
  · rw [le_div_iff₀ hs]; nlinarith [h.a_lo, h.v_hi]
  · rw [div_le_one hs]; linarith [h.v_pos]

theorem w_bounds : 0 < v / (a + v) ∧ v / (a + v) ≤ 1 := by
  have hs := h.sum_pos
  exact ⟨div_pos h.v_pos hs, (div_le_one hs).mpr (by linarith [h.a_pos])⟩

end InftyRange

end Range

section Lemma31

open InftyRange

variable {a v τ c₁ c₂ : ℝ}

theorem infA31_eq (a v τ c₁ c₂ ε : ℝ) :
    infA31 a v τ c₁ c₂ ε = ε * ((a / (a + v)) ^ 2 * infB1 v τ c₁ + (a / (a + v)) ^ 3 *
      infB2 a v τ c₁ c₂) := by
  unfold infA31; rw [div_pow, div_pow]; ring

theorem infA32_eq (a v τ c₁ c₂ : ℝ) (hs : 0 < a + v) :
    infA32 a v τ c₁ c₂ = (a / (a + v)) ^ 2 * (v / (a + v)) * infB2 a v τ c₁ c₂ := by
  unfold infA32; field_simp

theorem infA33_eq (a v τ c₁ c₂ : ℝ) (hs : 0 < a + v) :
    infA33 a v τ c₁ c₂ = 1 / 2 * (a / (a + v)) ^ 2 * (1 + v ^ 2 * (c₁ - v * c₂)) +
      (a / (a + v)) ^ 2 * (v / (a + v)) * infB1 v τ c₁ := by
  unfold infA33; rw [div_pow]; field_simp; ring

/-- Real `a₃₁`: `|a₃₁| ≤ (51/25) ε`. -/
theorem InftyRange.abs_A31_le (h : InftyRange a v τ c₁ c₂) {ε : ℝ} (hε : 0 ≤ ε) :
    |infA31 a v τ c₁ c₂ ε| ≤ 51 / 25 * ε := by
  rw [infA31_eq _ _ _ _ _ _]
  obtain ⟨r1, r2⟩ := h.rho_bounds
  obtain ⟨b1, b1'⟩ := h.B1_bounds
  obtain ⟨b2, b2'⟩ := h.B2_bounds
  set ρ := a / (a + v)
  have hρ0 : 0 ≤ ρ := by linarith
  have e1 : |ρ ^ 2 * infB1 v τ c₁| ≤ 51 / 50 := by
    rw [abs_mul, abs_of_pos b1, abs_of_nonneg (by positivity)]
    calc ρ ^ 2 * infB1 v τ c₁ ≤ 1 * (51 / 50) :=
          mul_le_mul (pow_le_one₀ hρ0 r2) b1' b1.le (by norm_num)
      _ = 51 / 50 := one_mul _
  have e2 : |ρ ^ 3 * infB2 a v τ c₁ c₂| ≤ 51 / 50 := by
    rw [abs_mul, abs_of_neg b2', abs_of_nonneg (by positivity)]
    calc ρ ^ 3 * -infB2 a v τ c₁ c₂ ≤ 1 * (51 / 50) :=
          mul_le_mul (pow_le_one₀ hρ0 r2) (by linarith) (by linarith) (by norm_num)
      _ = 51 / 50 := one_mul _
  rw [abs_mul, abs_of_nonneg hε]
  have := (abs_add_le _ _).trans (add_le_add e1 e2)
  nlinarith

theorem InftyRange.abs_A32_le (h : InftyRange a v τ c₁ c₂) :
    |infA32 a v τ c₁ c₂| ≤ 51 / 50 := by
  rw [infA32_eq _ _ _ _ _ h.sum_pos]
  obtain ⟨r1, r2⟩ := h.rho_bounds
  obtain ⟨w1, w2⟩ := h.w_bounds
  obtain ⟨b2, b2'⟩ := h.B2_bounds
  set ρ := a / (a + v)
  have hρ0 : 0 ≤ ρ := by linarith
  rw [abs_mul, abs_of_neg b2', abs_of_nonneg (by positivity)]
  have : ρ ^ 2 * (v / (a + v)) ≤ 1 :=
    (mul_le_mul (pow_le_one₀ hρ0 r2) w2 w1.le (by norm_num)).trans (by norm_num)
  nlinarith [mul_nonneg (by positivity : 0 ≤ ρ ^ 2 * (v / (a + v))) (by linarith : 0 ≤ -infB2 a v τ c₁ c₂)]

theorem InftyRange.A33_ge (h : InftyRange a v τ c₁ c₂) : 1 / 4 ≤ infA33 a v τ c₁ c₂ := by
  rw [infA33_eq _ _ _ _ _ h.sum_pos]
  obtain ⟨r1, r2⟩ := h.rho_bounds
  obtain ⟨w1, w2⟩ := h.w_bounds
  obtain ⟨b1, b1'⟩ := h.B1_bounds
  set ρ := a / (a + v)
  have h1 : 16 / 25 ≤ ρ ^ 2 := by nlinarith
  have h2 : 1 ≤ 1 + v ^ 2 * (c₁ - v * c₂) := by
    nlinarith [sq_nonneg v, h.diff_pos]
  have h3 : 0 ≤ ρ ^ 2 * (v / (a + v)) * infB1 v τ c₁ := by positivity
  nlinarith

end Lemma31

section Triangular

open InftyRange

/-- **Lemma 3.1** (coefficient bounds at `λ = ∞`, P4 (5.22)).  For `(a, v, τ, c₁, c₂)` in the
range `InftyRange` and `0 ≤ ε`, the matrix (5.21) satisfies the hypotheses `TriangularBounds`
of the landed small-field theorem: `|a₁₁| ≥ 1/2`, `a₂₂ = 1`, `a₃₃ ≥ 1/4`, `a₂₁ = 0`,
`|a₃₁| ≤ (51/25) ε ≤ (5/2) ε`, `|a₃₂| ≤ 51/50 ≤ 3/2`. -/
theorem triangularBounds_matrixInfty {a v τ c₁ c₂ : ℝ} (h : InftyRange a v τ c₁ c₂) {ε : ℝ}
    (hε : 0 ≤ ε) :
    TriangularBounds ((matrixInfty a v τ c₁ c₂ ε).map (algebraMap ℝ ℂ)) ε where
  upper01 := by simp [Matrix.map_apply]
  upper02 := by simp [Matrix.map_apply]
  upper12 := by simp [Matrix.map_apply]
  d0 := by
    simp only [Matrix.map_apply, matrixInfty_00, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos h.a_pos]; linarith [h.a_lo]
  d1 := by simp [Matrix.map_apply]
  d2 := by
    simp only [Matrix.map_apply, matrixInfty_22, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos (by linarith [h.A33_ge])]; exact h.A33_ge
  l10 := by simp [Matrix.map_apply, hε]
  l20 := by
    simp only [Matrix.map_apply, matrixInfty_20, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    nlinarith [h.abs_A31_le hε]
  l21 := by
    simp only [Matrix.map_apply, matrixInfty_21, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    linarith [h.abs_A32_le]

end Triangular

end Balaban.Flow
