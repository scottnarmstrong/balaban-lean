/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Coercive
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Combes–Thomas bounds for exponentially decaying, non-Hermitian matrices

Let `ι` be a finite pseudometric space and `A : Matrix ι ι ℂ` with entries
`‖A x y‖ ≤ c₀ exp (-δ₀ dist x y)`, such that the "ball sums"
`∑ y, exp (-(δ₀ / 4) dist x y)` are bounded by `κ` uniformly in `x`, and such that
`Re ⟨v, A v⟩ ≥ γ₀ ‖v‖²` (`IsCoercive A γ₀`, no Hermitian hypothesis).  Then for every real
`t ≥ 0` the matrix `A + t` is invertible and
`‖(A + t)⁻¹ x y‖ ≤ 2 (γ₀ + t)⁻¹ exp (-δ₁ dist x y)` with the explicit rate
`δ₁ = ctRate c₀ δ₀ γ₀ κ` (`Balaban.Green.combesThomas`).

Method: conjugate by `exp (ε dist x y₀)` (`conjMat`); the conjugation changes `A` by a matrix
whose entries are `≤ (4 c₀ ε / δ₀) exp (-(δ₀/4) dist x y)`, so by the Schur test
(`reQuad_ge_of_entry_bound`) the conjugated matrix is still `γ₀/2`-coercive for small `ε`;
an entry bound for right inverses of coercive matrices then gives the decay.

The route follows `FroehlichSpencer.Infra.Green.CombesThomas` (Armstrong–Loher; public repository
`scottnarmstrong/Frohlich-Spencer`, commit b47bc3d), generalized from range-one Hermitian kernels to
exponentially weighted row and column sums and non-Hermitian coercive operators.  This is
G-4 of the Balaban roadmap.  A matrix on `ι × Fin n` handles vector-valued fields.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation of a matrix by the diagonal weight `exp (a x)`: entries
`exp (a x - a y) * B x y`. -/
noncomputable def conjMat (a : ι → ℝ) (B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun x y => ((Real.exp (a x - a y) : ℝ) : ℂ) * B x y

omit [Fintype ι] [DecidableEq ι] in
lemma conjMat_add (a : ι → ℝ) (B C : Matrix ι ι ℂ) :
    conjMat a (B + C) = conjMat a B + conjMat a C := by
  ext x y; simp [conjMat, mul_add]

omit [Fintype ι] in
lemma conjMat_one (a : ι → ℝ) : conjMat a (1 : Matrix ι ι ℂ) = 1 := by
  ext x y
  by_cases h : x = y
  · subst h; simp [conjMat]
  · simp [conjMat, Matrix.one_apply_ne h]

omit [Fintype ι] in
lemma conjMat_smul_one (a : ι → ℝ) (t : ℂ) :
    conjMat a (t • (1 : Matrix ι ι ℂ)) = t • 1 := by
  ext x y
  by_cases h : x = y
  · subst h; simp [conjMat]
  · simp [conjMat, Matrix.one_apply_ne h]

omit [DecidableEq ι] in
lemma conjMat_mul (a : ι → ℝ) (B G : Matrix ι ι ℂ) :
    conjMat a (B * G) = conjMat a B * conjMat a G := by
  ext x z
  simp only [conjMat, Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : Real.exp (a x - a z) = Real.exp (a x - a y) * Real.exp (a y - a z) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; push_cast; ring

/-- Elementary estimate behind the conjugation error: if `|s| ≤ ε d` and `ε ≤ δ₀ / 2`, then
`|exp s - 1| * nA ≤ (4 c₀ ε / δ₀) exp (-(δ₀/4) d)` whenever `nA ≤ c₀ exp (-δ₀ d)`. -/
lemma conj_error_bound {c₀ δ₀ ε d s nA : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hε : 0 ≤ ε)
    (hε2 : ε ≤ δ₀ / 2) (hd : 0 ≤ d) (hs : |s| ≤ ε * d) (hnA : 0 ≤ nA)
    (hA : nA ≤ c₀ * Real.exp (-δ₀ * d)) :
    |Real.exp s - 1| * nA ≤ (4 * c₀ * ε / δ₀) * Real.exp (-(δ₀ / 4) * d) := by
  have hεd : 0 ≤ ε * d := mul_nonneg hε hd
  have hs' := abs_le.1 hs
  have h1 : |Real.exp s - 1| ≤ Real.exp (ε * d) - 1 := by
    rw [abs_le]
    constructor
    · have a1 := Real.add_one_le_exp (-(ε * d))
      have a2 := Real.add_one_le_exp (ε * d)
      have a3 : Real.exp (-(ε * d)) ≤ Real.exp s := Real.exp_le_exp.2 (by linarith)
      linarith
    · have := Real.exp_le_exp.2 hs'.2
      linarith
  have h2 : Real.exp (ε * d) - 1 ≤ ε * d * Real.exp (ε * d) := by
    have a1 := Real.add_one_le_exp (-(ε * d))
    have a2 : Real.exp (-(ε * d)) * Real.exp (ε * d) = 1 := by
      rw [← Real.exp_add]; simp
    have a3 := Real.exp_pos (ε * d)
    nlinarith
  have e1 : Real.exp (ε * d) * Real.exp (-δ₀ * d) ≤ Real.exp (-(δ₀ / 2) * d) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have e2 : d * Real.exp (-(δ₀ / 2) * d) ≤ (4 / δ₀) * Real.exp (-(δ₀ / 4) * d) := by
    have a1 := Real.add_one_le_exp (δ₀ / 4 * d)
    have a2 : d ≤ (4 / δ₀) * Real.exp (δ₀ / 4 * d) := by
      have : d = (4 / δ₀) * (δ₀ / 4 * d) := by field_simp
      nlinarith [div_pos (by norm_num : (0:ℝ) < 4) hδ]
    have a3 : Real.exp (δ₀ / 4 * d) * Real.exp (-(δ₀ / 2) * d) = Real.exp (-(δ₀ / 4) * d) := by
      rw [← Real.exp_add]; ring_nf
    calc d * Real.exp (-(δ₀ / 2) * d)
        ≤ ((4 / δ₀) * Real.exp (δ₀ / 4 * d)) * Real.exp (-(δ₀ / 2) * d) :=
          mul_le_mul_of_nonneg_right a2 (Real.exp_pos _).le
      _ = (4 / δ₀) * Real.exp (-(δ₀ / 4) * d) := by rw [mul_assoc, a3]
  have hexp := (Real.exp_pos (ε * d)).le
  calc |Real.exp s - 1| * nA ≤ (ε * d * Real.exp (ε * d)) * (c₀ * Real.exp (-δ₀ * d)) :=
        mul_le_mul (h1.trans h2) hA hnA (by positivity)
    _ = ε * c₀ * (d * (Real.exp (ε * d) * Real.exp (-δ₀ * d))) := by ring
    _ ≤ ε * c₀ * (d * Real.exp (-(δ₀ / 2) * d)) := by
        gcongr
    _ ≤ ε * c₀ * ((4 / δ₀) * Real.exp (-(δ₀ / 4) * d)) := by gcongr
    _ = (4 * c₀ * ε / δ₀) * Real.exp (-(δ₀ / 4) * d) := by ring

/-- The decay rate in the Combes–Thomas estimate. -/
noncomputable def ctRate (c₀ δ₀ γ₀ κ : ℝ) : ℝ :=
  min (δ₀ / 2) (γ₀ / (2 * (4 * c₀ * κ / δ₀ + 1)))

lemma ctRate_pos {c₀ δ₀ γ₀ κ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀) (hκ : 0 ≤ κ) :
    0 < ctRate c₀ δ₀ γ₀ κ := by
  unfold ctRate
  have : 0 < 4 * c₀ * κ / δ₀ + 1 := by positivity
  exact lt_min (by positivity) (by positivity)

lemma ctRate_le_half {c₀ δ₀ γ₀ κ : ℝ} : ctRate c₀ δ₀ γ₀ κ ≤ δ₀ / 2 := min_le_left _ _

lemma ctRate_mul_le {c₀ δ₀ γ₀ κ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀) (hκ : 0 ≤ κ) :
    ctRate c₀ δ₀ γ₀ κ * (4 * c₀ * κ / δ₀) ≤ γ₀ / 2 := by
  set M := 4 * c₀ * κ / δ₀ with hM
  have hM0 : 0 ≤ M := by positivity
  have h := min_le_right (δ₀ / 2) (γ₀ / (2 * (M + 1)))
  calc ctRate c₀ δ₀ γ₀ κ * M ≤ (γ₀ / (2 * (M + 1))) * M := by
        exact mul_le_mul_of_nonneg_right h hM0
    _ = γ₀ / 2 * (M / (M + 1)) := by field_simp
    _ ≤ γ₀ / 2 * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
    _ = γ₀ / 2 := mul_one _

variable [PseudoMetricSpace ι]

omit [DecidableEq ι] in
/-- Conjugating a decaying coercive matrix by `exp (ε dist x y₀)` keeps half of its
coercivity, for `ε` as in `ctRate`. -/
theorem isCoercive_conjMat {A : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀)
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hcoer : IsCoercive A γ₀) {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ≤ δ₀ / 2)
    (hεM : ε * (4 * c₀ * κ / δ₀) ≤ γ₀ / 2) (y₀ : ι) :
    IsCoercive (conjMat (fun x => ε * dist x y₀) A) (γ₀ / 2) := by
  set D : Matrix ι ι ℂ := Matrix.of fun x y =>
    (((Real.exp (ε * dist x y₀ - ε * dist y y₀) - 1 : ℝ)) : ℂ) * A x y with hD
  have hsplit : conjMat (fun x => ε * dist x y₀) A = A + D := by
    ext x y; simp only [conjMat, hD, Matrix.add_apply, Matrix.of_apply]; push_cast; ring
  set E : ι → ι → ℝ := fun x y => (4 * c₀ * ε / δ₀) * Real.exp (-(δ₀ / 4) * dist x y) with hE
  have hDE : ∀ x y, ‖D x y‖ ≤ E x y := by
    intro x y
    simp only [hD, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine conj_error_bound hc hδ hε hε2 dist_nonneg ?_ (norm_nonneg _) (hA x y)
    have := abs_dist_sub_le x y y₀
    rw [← mul_sub, abs_mul, abs_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left this hε
  have hS : ∀ x, ∑ y, E x y ≤ γ₀ / 2 := by
    intro x
    simp only [hE, ← Finset.mul_sum]
    have h0 : 0 ≤ 4 * c₀ * ε / δ₀ := by positivity
    calc (4 * c₀ * ε / δ₀) * ∑ y, Real.exp (-(δ₀ / 4) * dist x y)
        ≤ (4 * c₀ * ε / δ₀) * κ := mul_le_mul_of_nonneg_left (hK x) h0
      _ = ε * (4 * c₀ * κ / δ₀) := by ring
      _ ≤ γ₀ / 2 := hεM
  have hS' : ∀ y, ∑ x, E x y ≤ γ₀ / 2 := by
    intro y
    have := hS y
    simpa only [hE, dist_comm] using this
  intro v
  rw [hsplit, reQuad_add]
  have h1 := hcoer v
  have h2 := reQuad_ge_of_entry_bound D E hDE hS hS' v
  linarith

variable {c₀ δ₀ γ₀ κ : ℝ}

/-- **Combes–Thomas estimate** for a (non-Hermitian) coercive matrix with exponentially decaying
entries.  For `t ≥ 0`, `A + t` is invertible and its inverse decays with the rate
`ctRate c₀ δ₀ γ₀ κ`, which depends only on `c₀, δ₀, γ₀` and the ball-sum bound `κ` at
exponent `δ₀ / 4`. -/
theorem combesThomas {A : Matrix ι ι ℂ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) (hγ : 0 < γ₀)
    (hκ : 0 ≤ κ)
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hcoer : IsCoercive A γ₀) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) ∧
      ∀ x y, ‖(A + (t : ℂ) • (1 : Matrix ι ι ℂ))⁻¹ x y‖ ≤
        2 * (γ₀ + t)⁻¹ * Real.exp (-(ctRate c₀ δ₀ γ₀ κ) * dist x y) := by
  have hcoer' := hcoer.add_smul_one t
  have hU : IsUnit (A + (t : ℂ) • (1 : Matrix ι ι ℂ)) :=
    isUnit_of_isCoercive (by linarith) hcoer'
  refine ⟨hU, fun x y₀ => ?_⟩
  set ε := ctRate c₀ δ₀ γ₀ κ with hε
  have hε0 : 0 < ε := ctRate_pos hc hδ hγ hκ
  have hconj := isCoercive_conjMat hc hδ hA hK hcoer hε0.le ctRate_le_half
    (ctRate_mul_le hc hδ hγ hκ) y₀
  set a : ι → ℝ := fun x => ε * dist x y₀ with ha
  set B := A + (t : ℂ) • (1 : Matrix ι ι ℂ) with hB
  set G := B⁻¹ with hG
  have hBG : B * G = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  have hcB : conjMat a B = conjMat a A + (t : ℂ) • 1 := by
    rw [hB, conjMat_add, conjMat_smul_one]
  have hcoer2 : IsCoercive (conjMat a B) (γ₀ / 2 + t) := by
    rw [hcB]; exact hconj.add_smul_one t
  have hprod : conjMat a B * conjMat a G = 1 := by
    rw [← conjMat_mul, hBG, conjMat_one]
  have hb := norm_entry_le_of_mul_eq_one (by linarith) hcoer2 hprod x y₀
  have hy0 : a y₀ = 0 := by simp [ha]
  simp only [conjMat, Matrix.of_apply, hy0, sub_zero, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hb
  have hexp : Real.exp (-ε * dist x y₀) * Real.exp (a x) = 1 := by
    rw [← Real.exp_add]; simp [ha]
  have h3 : ‖G x y₀‖ ≤ (γ₀ / 2 + t)⁻¹ * Real.exp (-ε * dist x y₀) := by
    have hp := Real.exp_pos (a x)
    have h5 : ‖G x y₀‖ = (Real.exp (a x) * ‖G x y₀‖) * Real.exp (-ε * dist x y₀) := by
      linear_combination (-‖G x y₀‖) * hexp
    calc ‖G x y₀‖ = (Real.exp (a x) * ‖G x y₀‖) * Real.exp (-ε * dist x y₀) := h5
      _ ≤ (γ₀ / 2 + t)⁻¹ * Real.exp (-ε * dist x y₀) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have h4 : (γ₀ / 2 + t)⁻¹ ≤ 2 * (γ₀ + t)⁻¹ := by
    rw [show 2 * (γ₀ + t)⁻¹ = (γ₀ / 2 + t / 2)⁻¹ by field_simp]
    apply inv_anti₀ (by positivity); linarith
  calc ‖G x y₀‖ ≤ (γ₀ / 2 + t)⁻¹ * Real.exp (-ε * dist x y₀) := h3
    _ ≤ 2 * (γ₀ + t)⁻¹ * Real.exp (-ε * dist x y₀) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le

end Balaban.Green
