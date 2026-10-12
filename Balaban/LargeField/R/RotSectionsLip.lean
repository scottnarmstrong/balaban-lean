/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RotSections

/-!
# Lemma III.9.3 (c): the Lipschitz bound for the chart sections

LF-RECONSTRUCTION Lemma III.9.3 (c): for real `u₀` with `|u₀| = 1`, `σ u₀·e₁ ≥ 0`, and `u` on the quadric with
`|u − u₀| ≤ ε' ≤ 1/4`, `|R_σ(u) − R_σ(u₀)| ≤ C_rot ε'`. The norm used here is the entrywise supremum norm of the
matrix, and `|u − u₀|` is the Euclidean norm, written `∑ k, ‖u k − u₀ k‖^2 ≤ ε'^2`. The source constant is
`C(N)`; the entrywise bound holds with the explicit, dimension-free constant `17` (`secRotConst`), and it gives
the operator-norm bound `≤ 17 N ε'` (not stated here). (P7 pp. 520-525.)
-/

@[expose] public section

open Matrix

namespace Balaban.LargeField

variable {N : ℕ}

private theorem mul_le_one' {x y : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) (h0 : 0 ≤ y) :
    x * y ≤ 1 := by nlinarith

/-- The scalar estimate behind **Lemma III.9.3 (c)**: the `(i,j)` entry of `R₊` on the quadric is
`δ_{ij} + (p b − a q) + (c p b + c a q − p q − a b)/(1 + c)` with `p = u i`, `q = u j`, `c = u·e₁`,
`a = (e₁) i`, `b = (e₁) j`; its change under `‖u − u₀‖ ≤ ε ≤ 1/4` is at most `17 ε`. -/
theorem sec_lip_scalar (p q p₀ q₀ c c₀ a b : ℂ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hp : ‖p - p₀‖ ≤ ε) (hq : ‖q - q₀‖ ≤ ε) (hc : ‖c - c₀‖ ≤ ε)
    (hp1 : ‖p‖ ≤ 5/4) (hq1 : ‖q‖ ≤ 5/4)
    (hp0 : ‖p₀‖ ≤ 1) (hq0 : ‖q₀‖ ≤ 1) (hc0 : ‖c₀‖ ≤ 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hs : 3/4 ≤ ‖1 + c‖) (hs0 : 1 ≤ ‖1 + c₀‖) :
    ‖((p * b - a * q) + (c * p * b + c * a * q - p * q - a * b) / (1 + c)) -
      ((p₀ * b - a * q₀) + (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b) / (1 + c₀))‖ ≤ 17 * ε := by
  have hs' : (1 + c) ≠ 0 := norm_pos_iff.mp (by linarith)
  have hs0' : (1 + c₀) ≠ 0 := norm_pos_iff.mp (by linarith)
  -- products
  have hcp : ‖c * p - c₀ * p₀‖ ≤ 9/4 * ε := by
    have : c * p - c₀ * p₀ = (c - c₀) * p + c₀ * (p - p₀) := by ring
    rw [this]
    calc _ ≤ ‖(c - c₀) * p‖ + ‖c₀ * (p - p₀)‖ := norm_add_le _ _
      _ ≤ ε * (5/4) + 1 * ε := by
        rw [norm_mul, norm_mul]
        gcongr
      _ = 9/4 * ε := by ring
  have hcq : ‖c * q - c₀ * q₀‖ ≤ 9/4 * ε := by
    have : c * q - c₀ * q₀ = (c - c₀) * q + c₀ * (q - q₀) := by ring
    rw [this]
    calc _ ≤ ‖(c - c₀) * q‖ + ‖c₀ * (q - q₀)‖ := norm_add_le _ _
      _ ≤ ε * (5/4) + 1 * ε := by
        rw [norm_mul, norm_mul]
        gcongr
      _ = 9/4 * ε := by ring
  have hpq : ‖p * q - p₀ * q₀‖ ≤ 9/4 * ε := by
    have : p * q - p₀ * q₀ = (p - p₀) * q + p₀ * (q - q₀) := by ring
    rw [this]
    calc _ ≤ ‖(p - p₀) * q‖ + ‖p₀ * (q - q₀)‖ := norm_add_le _ _
      _ ≤ ε * (5/4) + 1 * ε := by
        rw [norm_mul, norm_mul]
        gcongr
      _ = 9/4 * ε := by ring
  have hN : ‖(c * p * b + c * a * q - p * q - a * b) - (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b)‖
      ≤ 27/4 * ε := by
    have : (c * p * b + c * a * q - p * q - a * b) - (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b)
        = (c * p - c₀ * p₀) * b + a * (c * q - c₀ * q₀) - (p * q - p₀ * q₀) := by ring
    rw [this]
    calc _ ≤ ‖(c * p - c₀ * p₀) * b‖ + ‖a * (c * q - c₀ * q₀)‖ + ‖p * q - p₀ * q₀‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ 9/4 * ε + 9/4 * ε + 9/4 * ε := by
        rw [norm_mul, norm_mul]
        have h1 : ‖c * p - c₀ * p₀‖ * ‖b‖ ≤ 9/4 * ε := by
          calc _ ≤ ‖c * p - c₀ * p₀‖ * 1 := by gcongr
            _ ≤ _ := by linarith
        have h2 : ‖a‖ * ‖c * q - c₀ * q₀‖ ≤ 9/4 * ε := by
          calc _ ≤ 1 * ‖c * q - c₀ * q₀‖ := by gcongr
            _ ≤ _ := by linarith
        linarith
      _ = 27/4 * ε := by ring
  have hN0 : ‖c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b‖ ≤ 4 := by
    calc _ ≤ ‖c₀ * p₀ * b‖ + ‖c₀ * a * q₀‖ + ‖p₀ * q₀‖ + ‖a * b‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _))
      _ ≤ 1 + 1 + 1 + 1 := by
        simp only [norm_mul]
        have : ‖c₀‖ * ‖p₀‖ * ‖b‖ ≤ 1 :=
          mul_le_one' (mul_le_one' hc0 hp0 (norm_nonneg _)) hb (norm_nonneg _)
        have h2 : ‖c₀‖ * ‖a‖ * ‖q₀‖ ≤ 1 :=
          mul_le_one' (mul_le_one' hc0 ha (norm_nonneg _)) hq0 (norm_nonneg _)
        have h3 : ‖p₀‖ * ‖q₀‖ ≤ 1 := mul_le_one' hp0 hq0 (norm_nonneg _)
        have h4 : ‖a‖ * ‖b‖ ≤ 1 := mul_le_one' ha hb (norm_nonneg _)
        linarith
      _ = 4 := by norm_num
  have hinv : ‖(1 + c)⁻¹‖ ≤ 4/3 := by
    rw [norm_inv]
    calc _ ≤ (3/4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs
      _ = 4/3 := by norm_num
  have hinv2 : ‖(1 + c)⁻¹ - (1 + c₀)⁻¹‖ ≤ 4/3 * ε := by
    have : (1 + c)⁻¹ - (1 + c₀)⁻¹ = (1 + c)⁻¹ * ((1 + c₀) - (1 + c)) * (1 + c₀)⁻¹ := by
      field_simp
    rw [this, norm_mul, norm_mul]
    have h1 : ‖(1 + c₀) - (1 + c)‖ ≤ ε := by
      have : (1 + c₀) - (1 + c) = -(c - c₀) := by ring
      rw [this, norm_neg]; exact hc
    have h2 : ‖(1 + c₀)⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ hs0
    calc _ ≤ 4/3 * ε * 1 := by gcongr
      _ = _ := by ring
  -- assemble
  have key : ((p * b - a * q) + (c * p * b + c * a * q - p * q - a * b) / (1 + c)) -
      ((p₀ * b - a * q₀) + (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b) / (1 + c₀))
      = ((p - p₀) * b - a * (q - q₀))
        + (((c * p * b + c * a * q - p * q - a * b) - (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b)) * (1 + c)⁻¹
        + (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b) * ((1 + c)⁻¹ - (1 + c₀)⁻¹)) := by
    field_simp
    ring
  rw [key]
  have hA : ‖(p - p₀) * b - a * (q - q₀)‖ ≤ 2 * ε := by
    calc _ ≤ ‖(p - p₀) * b‖ + ‖a * (q - q₀)‖ := norm_sub_le _ _
      _ ≤ ε + ε := by
        rw [norm_mul, norm_mul]
        have h1 : ‖p - p₀‖ * ‖b‖ ≤ ε := by
          calc _ ≤ ‖p - p₀‖ * 1 := by gcongr
            _ ≤ ε := by linarith
        have h2 : ‖a‖ * ‖q - q₀‖ ≤ ε := by
          calc _ ≤ 1 * ‖q - q₀‖ := by gcongr
            _ ≤ ε := by linarith
        linarith
      _ = 2 * ε := by ring
  have hB : ‖((c * p * b + c * a * q - p * q - a * b) - (c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b)) * (1 + c)⁻¹‖ ≤ 9 * ε := by
    rw [norm_mul]
    calc _ ≤ 27/4 * ε * (4/3) := by gcongr
      _ = 9 * ε := by ring
  have hC : ‖(c₀ * p₀ * b + c₀ * a * q₀ - p₀ * q₀ - a * b) * ((1 + c)⁻¹ - (1 + c₀)⁻¹)‖ ≤ 16/3 * ε := by
    rw [norm_mul]
    calc _ ≤ 4 * (4/3 * ε) := by gcongr
      _ = 16/3 * ε := by ring
  calc _ ≤ ‖(p - p₀) * b - a * (q - q₀)‖ + ‖_ + _‖ := norm_add_le _ _
    _ ≤ 2 * ε + (9 * ε + 16/3 * ε) := by
        gcongr
        exact (norm_add_le _ _).trans (by linarith)
    _ ≤ 17 * ε := by linarith


/-- The explicit constant of **Lemma III.9.3 (c)** for the entrywise supremum norm: `C_rot = 17`. -/
def secRotConst : ℝ := 17

theorem secPlus_apply_quadric (i₀ : Fin N) (u : Fin N → ℂ) (hu : u ⬝ᵥ u = 1) (i j : Fin N) :
    secPlus i₀ u i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + (u i * eVec i₀ j - eVec i₀ i * u j)
      + (u i₀ * u i * eVec i₀ j + u i₀ * eVec i₀ i * u j - u i * u j - eVec i₀ i * eVec i₀ j) / (1 + u i₀) := by
  unfold secPlus
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Aof_sq i₀ u hu]
  simp only [Aof, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  field_simp

theorem eVec_norm_le (i₀ i : Fin N) : ‖(eVec i₀ : Fin N → ℂ) i‖ ≤ 1 := by
  by_cases h : i = i₀ <;> simp [eVec, h]

theorem sec_lip_plus (i₀ : Fin N) (u : Fin N → ℂ) (u₀ : Fin N → ℝ) (hu : u ⬝ᵥ u = 1)
    (hu₀ : u₀ ⬝ᵥ u₀ = 1) (h0 : 0 ≤ u₀ i₀) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hd : ∑ k, ‖u k - (u₀ k : ℂ)‖ ^ 2 ≤ ε ^ 2) (i j : Fin N) :
    ‖secPlus i₀ u i j - secPlus i₀ (fun k => (u₀ k : ℂ)) i j‖ ≤ secRotConst * ε := by
  have hU0 : (fun k => (u₀ k : ℂ)) ⬝ᵥ (fun k => (u₀ k : ℂ)) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hu₀
    simpa [dotProduct] using this
  have hw : ∀ k, ‖u k - (u₀ k : ℂ)‖ ≤ ε := by
    intro k
    have h1 : ‖u k - (u₀ k : ℂ)‖ ^ 2 ≤ ε ^ 2 :=
      (Finset.single_le_sum (f := fun k => ‖u k - (u₀ k : ℂ)‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ k)).trans hd
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε0 two_ne_zero).mp h1
  have hb0 : ∀ k, ‖((u₀ k : ℝ) : ℂ)‖ ≤ 1 := by
    intro k
    have h1 : u₀ k * u₀ k ≤ 1 := by
      rw [← hu₀]
      exact Finset.single_le_sum (f := fun k => u₀ k * u₀ k) (fun _ _ => mul_self_nonneg _)
        (Finset.mem_univ k)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (u₀ k), sq_abs (u₀ k)]
  have hb : ∀ k, ‖u k‖ ≤ 5 / 4 := by
    intro k
    calc ‖u k‖ = ‖(u k - (u₀ k : ℂ)) + (u₀ k : ℂ)‖ := by ring_nf
      _ ≤ ‖u k - (u₀ k : ℂ)‖ + ‖(u₀ k : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := add_le_add (hw k |>.trans hε) (hb0 k)
      _ = 5 / 4 := by norm_num
  have hs0 : 1 ≤ ‖1 + (u₀ i₀ : ℂ)‖ := by
    have : (1 + (u₀ i₀ : ℂ)) = ((1 + u₀ i₀ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hs : 3 / 4 ≤ ‖1 + u i₀‖ := by
    have h1 : ‖1 + (u₀ i₀ : ℂ)‖ ≤ ‖1 + u i₀‖ + ‖u i₀ - (u₀ i₀ : ℂ)‖ := by
      calc ‖1 + (u₀ i₀ : ℂ)‖ = ‖(1 + u i₀) - (u i₀ - (u₀ i₀ : ℂ))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    linarith [hw i₀]
  rw [secPlus_apply_quadric i₀ u hu, secPlus_apply_quadric i₀ _ hU0]
  have := sec_lip_scalar (u i) (u j) (u₀ i : ℂ) (u₀ j : ℂ) (u i₀) (u₀ i₀ : ℂ) (eVec i₀ i) (eVec i₀ j) ε hε0
    (hw i) (hw j) (hw i₀) (hb i) (hb j) (hb0 i) (hb0 j) (hb0 i₀)
    (eVec_norm_le i₀ i) (eVec_norm_le i₀ j) hs hs0
  unfold secRotConst
  convert this using 2
  ring

theorem sec_lip_minus (i₀ j₀ : Fin N) (u : Fin N → ℂ) (u₀ : Fin N → ℝ) (hu : u ⬝ᵥ u = 1)
    (hu₀ : u₀ ⬝ᵥ u₀ = 1) (h0 : u₀ i₀ ≤ 0) (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hd : ∑ k, ‖u k - (u₀ k : ℂ)‖ ^ 2 ≤ ε ^ 2) (i j : Fin N) :
    ‖secMinus i₀ j₀ u i j - secMinus i₀ j₀ (fun k => (u₀ k : ℂ)) i j‖ ≤ secRotConst * ε := by
  have hu' : (-u) ⬝ᵥ (-u) = 1 := by simpa using hu
  have hu₀' : (-u₀) ⬝ᵥ (-u₀) = 1 := by simpa using hu₀
  have hd' : ∑ k, ‖(-u) k - ((-u₀) k : ℂ)‖ ^ 2 ≤ ε ^ 2 := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) hd
    have : (-u) k - (((-u₀) k : ℝ) : ℂ) = -(u k - (u₀ k : ℂ)) := by simp; ring
    rw [this, norm_neg]
  have key := sec_lip_plus i₀ (-u) (-u₀) hu' hu₀' (by simpa using h0) ε hε0 hε hd' i j
  have hm : ∀ v : Fin N → ℂ, secMinus i₀ j₀ v i j =
      secPlus i₀ (-v) i j * (if j = i₀ ∨ j = j₀ then -1 else 1) := by
    intro v
    rw [secMinus_eq]
    simp [Dmat, Matrix.mul_apply, Matrix.diagonal_apply]
  have hneg : (-(fun k => (u₀ k : ℂ))) = fun k => (((-u₀) k : ℝ) : ℂ) := by
    ext k; simp
  rw [hm, hm, hneg, ← sub_mul, norm_mul]
  have hd1 : ‖(if j = i₀ ∨ j = j₀ then (-1 : ℂ) else 1)‖ = 1 := by
    split_ifs <;> simp
  rw [hd1, mul_one]
  exact key

/-- The chart section `R_σ` for a sign `σ` (`true` is `+`). -/
noncomputable def secSigma (i₀ j₀ : Fin N) (σ : Bool) (u : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  if σ then secPlus i₀ u else secMinus i₀ j₀ u

/-- **LF-RECONSTRUCTION Lemma III.9.3 (c)**: if `u₀` is real, `|u₀| = 1`, `σ u₀·e₁ ≥ 0`, `u·u = 1` and
`|u − u₀| ≤ ε' ≤ 1/4`, then every entry of `R_σ(u) − R_σ(u₀)` is at most `C_rot ε'` in modulus, with the
explicit dimension-free constant `C_rot = 17`. -/
theorem sec_lip (i₀ j₀ : Fin N) (σ : Bool) (u : Fin N → ℂ) (u₀ : Fin N → ℝ) (hu : u ⬝ᵥ u = 1)
    (hu₀ : u₀ ⬝ᵥ u₀ = 1) (hσ : if σ then 0 ≤ u₀ i₀ else u₀ i₀ ≤ 0) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 4) (hd : ∑ k, ‖u k - (u₀ k : ℂ)‖ ^ 2 ≤ ε ^ 2) (i j : Fin N) :
    ‖secSigma i₀ j₀ σ u i j - secSigma i₀ j₀ σ (fun k => (u₀ k : ℂ)) i j‖ ≤ secRotConst * ε := by
  cases σ
  · simp only [secSigma, Bool.false_eq_true, ↓reduceIte]
    exact sec_lip_minus i₀ j₀ u u₀ hu hu₀ (by simpa using hσ) ε hε0 hε hd i j
  · simp only [secSigma, ↓reduceIte]
    exact sec_lip_plus i₀ u u₀ hu hu₀ (by simpa using hσ) ε hε0 hε hd i j

end Balaban.LargeField
