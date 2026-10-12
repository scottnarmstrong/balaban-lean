/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.MatrixInfty

/-!
# The linear part of the renormalization-group system for `ν`-free backgrounds

`notes/phase1/SMALLFIELD.md` v3 §3.7, Lemma 3.1′ (steps `k < k₀`, P5 (1.9)).  With `a = a_{k+1}`,
`m = ν_{k+1}`, `ε = ε_{k+1}`, `τ ∈ [0,1]`, and `r` the explicit `mζ` coefficient `ϱ₃₁` of `a₃₁`
(not yet computed; it enters only through the hypothesis `|r| ≤ C_ϱ`, `m C_ϱ ≤ 2.4`):

* `matrixFree`: the matrix; `triangularBounds_matrixFree` (**Lemma 3.1′**);
* `matrixFree_map`, `matrixFree_conj`, `matrixFree_analyticOnNhd`;
* `matrixSel`: the convention selector (`k < k₀`: `ν`-free, else `matrixInfty`) and
  `triangularBounds_matrixSel`.

The step theorem `Balaban.Flow.rg_step_infty` is stated for an arbitrary matrix family with
`TriangularBounds`, so it applies verbatim to `matrixFree`; no separate analogue is needed.
-/

@[expose] public section

namespace Balaban.Flow

section Entries

variable {𝕜 : Type*} [Field 𝕜]

/-- **The `ν`-free matrix** (`k < k₀`). -/
def matrixFree (a m τ r ε : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![a, 0, 0; 0, 1, 0; ε * (a * τ / 24 + m * r), m / a * (-1 + a * τ / 24), 1 / 2]

@[simp] theorem matrixFree_00 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 0 0 = a := rfl
@[simp] theorem matrixFree_01 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 0 1 = 0 := rfl
@[simp] theorem matrixFree_02 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 0 2 = 0 := rfl
@[simp] theorem matrixFree_10 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 1 0 = 0 := rfl
@[simp] theorem matrixFree_11 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 1 1 = 1 := rfl
@[simp] theorem matrixFree_12 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 1 2 = 0 := rfl
@[simp] theorem matrixFree_20 (a m τ r ε : 𝕜) :
    matrixFree a m τ r ε 2 0 = ε * (a * τ / 24 + m * r) := rfl
@[simp] theorem matrixFree_21 (a m τ r ε : 𝕜) :
    matrixFree a m τ r ε 2 1 = m / a * (-1 + a * τ / 24) := rfl
@[simp] theorem matrixFree_22 (a m τ r ε : 𝕜) : matrixFree a m τ r ε 2 2 = 1 / 2 := rfl

/-- The matrix commutes with ring homomorphisms of fields. -/
theorem matrixFree_map {𝕜' : Type*} [Field 𝕜'] (φ : 𝕜 →+* 𝕜') (a m τ r ε : 𝕜) :
    (matrixFree a m τ r ε).map φ = matrixFree (φ a) (φ m) (φ τ) (φ r) (φ ε) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixFree, Matrix.map_apply, map_ofNat, map_div₀]

/-- Compatibility with complex conjugation (the hypothesis `hAσ` of `rg_solution_real`). -/
theorem matrixFree_conj (a m τ r ε : ℂ) :
    (matrixFree a m τ r ε).map (starRingEnd ℂ) =
      matrixFree (starRingEnd ℂ a) (starRingEnd ℂ m) (starRingEnd ℂ τ) (starRingEnd ℂ r)
        (starRingEnd ℂ ε) :=
  matrixFree_map _ _ _ _ _ _

end Entries

/-- Analyticity of every entry in the parameters `(a, m, r)` on `{a ≠ 0}` (for (L1)). -/
theorem matrixFree_analyticOnNhd (τ ε : ℂ) (i j : Fin 3) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ => matrixFree p.1 p.2.1 τ p.2.2 ε i j)
      {p | p.1 ≠ 0} := by
  intro p hp
  have h1 : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) p := analyticAt_fst
  have h2 : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) p := analyticAt_fst.comp analyticAt_snd
  have h3 : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) p := analyticAt_snd.comp analyticAt_snd
  have h1' : p.1 ≠ 0 := hp
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    matrixFree_00, matrixFree_01, matrixFree_02, matrixFree_10, matrixFree_11, matrixFree_12,
    matrixFree_20, matrixFree_21, matrixFree_22] <;> first
    | exact analyticAt_const
    | exact h1
    | exact analyticAt_const.mul (((h1.mul analyticAt_const).div analyticAt_const
        (by norm_num)).add (h2.mul h3))
    | exact (h2.div h1 h1').mul (analyticAt_const.add ((h1.mul analyticAt_const).div
        analyticAt_const (by norm_num)))

section Lemma31'

/-- **Lemma 3.1′** (coefficient bounds, `ν`-free matrix).  For `a ∈ [9/10, 3/2]`,
`0 ≤ m ≤ 7/32`, `τ ∈ [0,1]`, `|r| ≤ C` with `m C ≤ 2.4`, and `0 ≤ ε`, the matrix satisfies
`TriangularBounds` with parameter `ε`. -/
theorem triangularBounds_matrixFree {a m τ r C ε : ℝ} (ha1 : 9 / 10 ≤ a) (ha2 : a ≤ 3 / 2)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 7 / 32) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hr : |r| ≤ C)
    (hmC : m * C ≤ 12 / 5) (hε : 0 ≤ ε) :
    TriangularBounds ((matrixFree a m τ r ε).map (algebraMap ℝ ℂ)) ε where
  upper01 := by simp [Matrix.map_apply]
  upper02 := by simp [Matrix.map_apply]
  upper12 := by simp [Matrix.map_apply]
  d0 := by
    simp only [Matrix.map_apply, matrixFree_00, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]; linarith
  d1 := by simp [Matrix.map_apply]
  d2 := by
    simp only [Matrix.map_apply, matrixFree_22, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
  l10 := by simp [Matrix.map_apply, hε]
  l20 := by
    simp only [Matrix.map_apply, matrixFree_20, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    have hmr : |m * r| ≤ 12 / 5 := by
      rw [abs_mul, abs_of_nonneg hm0]
      exact (mul_le_mul_of_nonneg_left hr hm0).trans hmC
    have hat : 0 ≤ a * τ / 24 := by positivity
    have hat' : a * τ / 24 ≤ 1 / 16 := by
      have : a * τ ≤ 3 / 2 := by nlinarith
      linarith
    have : |a * τ / 24 + m * r| ≤ 5 / 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg hat]; linarith
    rw [abs_mul, abs_of_nonneg hε]
    nlinarith
  l21 := by
    simp only [Matrix.map_apply, matrixFree_21, Complex.coe_algebraMap, Complex.norm_real,
      Real.norm_eq_abs]
    have hapos : 0 < a := by linarith
    have hq : m / a ≤ 1 := by
      rw [div_le_one hapos]; linarith
    have hq0 : 0 ≤ m / a := by positivity
    have hb : |-1 + a * τ / 24| ≤ 1 := by
      have : 0 ≤ a * τ / 24 := by positivity
      have : a * τ / 24 ≤ 1 / 16 := by nlinarith
      rw [abs_le]; constructor <;> linarith
    rw [abs_mul, abs_of_nonneg hq0]
    nlinarith [abs_nonneg (-1 + a * τ / 24)]

end Lemma31'

section Selector

/-- The convention selector: the `ν`-free matrix for `k < k₀`, the complete one (`matrixInfty`)
for `k ≥ k₀`. -/
def matrixSel {𝕜 : Type*} [Field 𝕜] (k k₀ : ℕ) (a v τ c₁ c₂ r ε : 𝕜) :
    Matrix (Fin 3) (Fin 3) 𝕜 :=
  if k < k₀ then matrixFree a v τ r ε else matrixInfty a v τ c₁ c₂ ε

theorem matrixSel_of_lt {𝕜 : Type*} [Field 𝕜] {k k₀ : ℕ} (h : k < k₀) (a v τ c₁ c₂ r ε : 𝕜) :
    matrixSel k k₀ a v τ c₁ c₂ r ε = matrixFree a v τ r ε := by simp [matrixSel, h]

theorem matrixSel_of_ge {𝕜 : Type*} [Field 𝕜] {k k₀ : ℕ} (h : k₀ ≤ k) (a v τ c₁ c₂ r ε : 𝕜) :
    matrixSel k k₀ a v τ c₁ c₂ r ε = matrixInfty a v τ c₁ c₂ ε := by simp [matrixSel, not_lt.mpr h]

theorem matrixSel_conj (k k₀ : ℕ) (a v τ c₁ c₂ r ε : ℂ) :
    (matrixSel k k₀ a v τ c₁ c₂ r ε).map (starRingEnd ℂ) =
      matrixSel k k₀ (starRingEnd ℂ a) (starRingEnd ℂ v) (starRingEnd ℂ τ) (starRingEnd ℂ c₁)
        (starRingEnd ℂ c₂) (starRingEnd ℂ r) (starRingEnd ℂ ε) := by
  unfold matrixSel
  split_ifs
  · exact matrixFree_conj _ _ _ _ _
  · exact matrixInfty_conj _ _ _ _ _ _

/-- Both conventions satisfy `TriangularBounds`: the `ν`-free parameters for `k < k₀`, the
`InftyRange` for `k ≥ k₀`. -/
theorem triangularBounds_matrixSel {k k₀ : ℕ} {a v τ c₁ c₂ r C ε : ℝ}
    (hfree : k < k₀ → 9 / 10 ≤ a ∧ a ≤ 3 / 2 ∧ 0 ≤ v ∧ v ≤ 7 / 32 ∧ 0 ≤ τ ∧ τ ≤ 1 ∧ |r| ≤ C ∧
      v * C ≤ 12 / 5)
    (hinf : k₀ ≤ k → InftyRange a v τ c₁ c₂) (hε : 0 ≤ ε) :
    TriangularBounds ((matrixSel k k₀ a v τ c₁ c₂ r ε).map (algebraMap ℝ ℂ)) ε := by
  by_cases h : k < k₀
  · rw [matrixSel_of_lt h]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hfree h
    exact triangularBounds_matrixFree h1 h2 h3 h4 h5 h6 h7 h8 hε
  · rw [matrixSel_of_ge (not_lt.mp h)]
    exact triangularBounds_matrixInfty (hinf (not_lt.mp h)) hε

end Selector

end Balaban.Flow
