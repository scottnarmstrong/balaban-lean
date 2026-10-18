/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6RotFrames
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex invariance on the anisotropic polydisc: a two-stage Cayley path

The anisotropic domain of the frame bridges constrains the longitudinal field coordinate to
`|b_{i₀} - ν| < r²`, quadratically in the radius, so the single polar path of `Def6RotFrames`
does not stay in it.  For a complex orthogonal `M` with `v = M e` close to the real unit vector `e`
the path has two stages: first `T = cay(A)` with the rank-two antisymmetric
`A = (v eᵀ - e vᵀ) / (1 + e·v)`, which satisfies `T e = v`, then the polar path of `T⁻¹ M`, which
fixes `e` (so `cay e = e`, and the longitudinal coordinate is unchanged exactly).  This file
contains the linear algebra of the first stage.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField Balaban.SmallField.Def6 Matrix Filter Topology

section Algebra

variable {N : ℕ}

/-- **The Cayley transform of an antisymmetric matrix is orthogonal** (complex parameter `s`, with
`1 - sS` invertible; then `1 + sS = (1 - sS)ᵀ` is invertible as well). -/
theorem cayMat_transpose_mul {S : Matrix (Fin N) (Fin N) ℂ} (hS : S.transpose = -S) {s : ℂ}
    (h1 : IsUnit (1 - s • S).det) :
    (RotFrames.cayMat S s).transpose * RotFrames.cayMat S s = 1 := by
  set A : Matrix (Fin N) (Fin N) ℂ := 1 - s • S with hA
  set B : Matrix (Fin N) (Fin N) ℂ := 1 + s • S with hB
  have hAT : A.transpose = B := by
    rw [hA, hB, transpose_sub, transpose_one, transpose_smul, hS, smul_neg, sub_neg_eq_add]
  have hBT : B.transpose = A := by
    rw [hA, hB, transpose_add, transpose_one, transpose_smul, hS, smul_neg, sub_eq_add_neg]
  have h2 : IsUnit B.det := by rw [← hAT, det_transpose]; exact h1
  have hAB : A * B = B * A := by
    have hX : ∀ X : Matrix (Fin N) (Fin N) ℂ, (1 - X) * (1 + X) = (1 + X) * (1 - X) :=
      fun X => by noncomm_ring
    exact hX _
  have hinvc : B⁻¹ * A⁻¹ = A⁻¹ * B⁻¹ := by
    rw [← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hAB]
  have hAu : A * A⁻¹ = 1 := mul_nonsing_inv _ h1
  have hBu' : B⁻¹ * B = 1 := nonsing_inv_mul _ h2
  have hRT : (RotFrames.cayMat S s).transpose = A * B⁻¹ := by
    unfold RotFrames.cayMat
    rw [← hA, ← hB, transpose_mul, hBT, transpose_nonsing_inv, hAT]
  rw [hRT]
  unfold RotFrames.cayMat
  rw [← hA, ← hB]
  calc A * B⁻¹ * (A⁻¹ * B) = A * (B⁻¹ * A⁻¹) * B := by simp only [Matrix.mul_assoc]
    _ = A * (A⁻¹ * B⁻¹) * B := by rw [hinvc]
    _ = (A * A⁻¹) * (B⁻¹ * B) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hAu, hBu', Matrix.one_mul]

/-- **The rank-two antisymmetric matrix** `A = (v eᵀ - e vᵀ) / (1 + v_{i₀})`, `e = e_{i₀}`. -/
noncomputable def aniA (i₀ : Fin N) (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    (1 + v i₀)⁻¹ * ((if j = i₀ then v i else 0) - (if i = i₀ then v j else 0))

theorem aniA_transpose (i₀ : Fin N) (v : Fin N → ℂ) : (aniA i₀ v).transpose = -aniA i₀ v := by
  ext i j
  simp only [transpose_apply, aniA, of_apply, Matrix.neg_apply]
  ring

theorem aniA_mulVec (i₀ : Fin N) (v x : Fin N → ℂ) (i : Fin N) :
    (aniA i₀ v *ᵥ x) i = (1 + v i₀)⁻¹ *
      (v i * x i₀ - (if i = i₀ then ∑ j, v j * x j else 0)) := by
  have key : ∀ j, (aniA i₀ v) i j * x j = (1 + v i₀)⁻¹ *
      ((if j = i₀ then v i * x j else 0) - (if i = i₀ then v j * x j else 0)) := by
    intro j
    simp only [aniA, of_apply]
    split_ifs <;> ring
  simp only [mulVec, dotProduct, key, ← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  by_cases hi : i = i₀ <;> simp [hi]

/-- `A (e + v) = v - e` when `(1 + v_{i₀}) ≠ 0` and `v · v = 1`. -/
theorem aniA_mulVec_add (i₀ : Fin N) (v : Fin N → ℂ) (hc : 1 + v i₀ ≠ 0)
    (hvv : ∑ j, v j * v j = 1) :
    aniA i₀ v *ᵥ ((Pi.single i₀ 1 : Fin N → ℂ) + v) = v - (Pi.single i₀ 1 : Fin N → ℂ) := by
  funext i
  rw [aniA_mulVec]
  have h1 : ∑ j, v j * ((Pi.single i₀ 1 : Fin N → ℂ) + v) j = 1 + v i₀ := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hvv]
    simp [Pi.single_apply]
    ring
  rw [h1]
  by_cases hi : i = i₀
  · subst hi; simp; field_simp
  · simp [hi]; field_simp

end Algebra

section Estimates

variable {N : ℕ} {i₀ : Fin N} {v : Fin N → ℂ} {re : ℝ}

theorem aniA_entry (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1) (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re) (hre : 0 ≤ re)
    (i j : Fin N) : ‖aniA i₀ v i j‖ ≤ re := by
  simp only [aniA, of_apply]
  by_cases hj : j = i₀ <;> by_cases hi : i = i₀
  · simp only [hj, hi, ↓reduceIte, sub_self, mul_zero, norm_zero]; exact hre
  · simp only [hj, hi, ↓reduceIte, sub_zero, norm_mul]
    calc ‖(1 + v i₀)⁻¹‖ * ‖v i‖ ≤ 1 * re :=
          mul_le_mul hκ (hv i hi) (norm_nonneg _) zero_le_one
      _ = re := one_mul _
  · simp only [hj, hi, ↓reduceIte, zero_sub, norm_mul, norm_neg]
    calc ‖(1 + v i₀)⁻¹‖ * ‖v j‖ ≤ 1 * re :=
          mul_le_mul hκ (hv j hj) (norm_nonneg _) zero_le_one
      _ = re := one_mul _
  · simp only [hj, hi, ↓reduceIte, sub_self, mul_zero, norm_zero]; exact hre

theorem aniA_mulVec_norm_le (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1) (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re)
    (hre : 0 ≤ re) {x : Fin N → ℂ} {M : ℝ} (hM : ∀ j, ‖x j‖ ≤ M) (i : Fin N) :
    ‖(aniA i₀ v *ᵥ x) i‖ ≤ N * re * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i)
  calc ‖(aniA i₀ v *ᵥ x) i‖ = ‖∑ j, aniA i₀ v i j * x j‖ := rfl
    _ ≤ ∑ j, ‖aniA i₀ v i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin N, re * M := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (aniA_entry hκ hv hre i j) (hM j) (norm_nonneg _) hre
    _ = N * re * M := by simp [mul_assoc]

theorem aniA_isUnit (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1) (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re) (hre : 0 ≤ re)
    (hN : (N : ℝ) * re ≤ 1 / 4) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    IsUnit (1 - σ • aniA i₀ v).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  have : Nonempty (Fin N) := ⟨i₀⟩
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  obtain ⟨i, hi⟩ := Finite.exists_max (fun j => ‖x j‖)
  have hxe : x = σ • (aniA i₀ v *ᵥ x) := by
    have := hx
    rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_zero] at this
    exact this
  have h1 : ‖x i‖ ≤ 1 / 4 * ‖x i‖ := by
    calc ‖x i‖ = ‖σ‖ * ‖(aniA i₀ v *ᵥ x) i‖ := by
          conv_lhs => rw [hxe]
          simp
      _ ≤ 1 * (N * re * ‖x i‖) :=
          mul_le_mul hσ (aniA_mulVec_norm_le hκ hv hre hi i) (norm_nonneg _) zero_le_one
      _ ≤ 1 / 4 * ‖x i‖ := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hN (norm_nonneg _)
  have h0 : ‖x i‖ = 0 := by nlinarith [norm_nonneg (x i)]
  apply hx0
  funext j
  have := hi j
  rw [h0] at this
  exact norm_le_zero_iff.1 this

/-- **The coordinates of `z` with `z + σ A z = y`.**  For `y` with `|y_{i₀}| ≤ p`, `|y_j| ≤ q`
(`j ≠ i₀`): `|z_{i₀}| ≤ 2 (p + q)`, `|z_j - y_j| ≤ 2 re (p + q)` and
`|z_{i₀} - y_{i₀}| ≤ N re (q + 2 re (p + q))` (the longitudinal change is quadratic in `re`). -/
theorem aniA_est (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1) (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re) (hre : 0 ≤ re)
    (hN : (N : ℝ) * re ≤ 1 / 4) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) {y z : Fin N → ℂ}
    (hz : z + σ • (aniA i₀ v *ᵥ z) = y) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hy0 : ‖y i₀‖ ≤ p) (hy : ∀ j, j ≠ i₀ → ‖y j‖ ≤ q) :
    ‖z i₀‖ ≤ 2 * (p + q) ∧ (∀ j, j ≠ i₀ → ‖z j - y j‖ ≤ 2 * re * (p + q)) ∧
      (∀ j, j ≠ i₀ → ‖z j‖ ≤ q + 2 * re * (p + q)) ∧
      ‖z i₀ - y i₀‖ ≤ N * re * (q + 2 * re * (p + q)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hre1 : re ≤ 1 / 4 := by nlinarith
  set W : ℝ := ‖z i₀‖ with hW
  have hW0 : 0 ≤ W := norm_nonneg _
  have hzy : ∀ i, z i - y i = -(σ * (aniA i₀ v *ᵥ z) i) := fun i => by
    have := congrFun hz i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]; ring
  have hoff : ∀ i, i ≠ i₀ → ‖z i - y i‖ ≤ re * W := fun i hi => by
    rw [hzy, norm_neg, norm_mul, aniA_mulVec]
    simp only [hi, ↓reduceIte, sub_zero, norm_mul]
    calc ‖σ‖ * (‖(1 + v i₀)⁻¹‖ * (‖v i‖ * ‖z i₀‖)) ≤ 1 * (1 * (re * W)) :=
          mul_le_mul hσ (mul_le_mul hκ (mul_le_mul (hv i hi) le_rfl hW0 hre) (by positivity)
            zero_le_one) (by positivity) zero_le_one
      _ = re * W := by ring
  have hoffz : ∀ i, i ≠ i₀ → ‖z i‖ ≤ q + re * W := fun i hi => by
    have h1 := hoff i hi
    have h2 : ‖z i‖ ≤ ‖y i‖ + ‖z i - y i‖ := by
      calc ‖z i‖ = ‖y i + (z i - y i)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith [hy i hi]
  have hlong : ‖z i₀ - y i₀‖ ≤ N * re * (q + re * W) := by
    rw [hzy, norm_neg, norm_mul, aniA_mulVec]
    simp only [↓reduceIte]
    have hsum : ∑ j, v j * z j = v i₀ * z i₀ + ∑ j ∈ Finset.univ.erase i₀, v j * z j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    rw [hsum, show v i₀ * z i₀ - (v i₀ * z i₀ + ∑ j ∈ Finset.univ.erase i₀, v j * z j) =
      -∑ j ∈ Finset.univ.erase i₀, v j * z j by ring, norm_mul, norm_neg]
    have hS : ‖∑ j ∈ Finset.univ.erase i₀, v j * z j‖ ≤ N * (re * (q + re * W)) := by
      calc ‖∑ j ∈ Finset.univ.erase i₀, v j * z j‖
          ≤ ∑ j ∈ Finset.univ.erase i₀, ‖v j * z j‖ := norm_sum_le _ _
        _ ≤ ∑ _j ∈ Finset.univ.erase i₀, re * (q + re * W) := Finset.sum_le_sum fun j hj => by
            rw [norm_mul]
            exact mul_le_mul (hv j (Finset.ne_of_mem_erase hj)) (hoffz j (Finset.ne_of_mem_erase hj))
              (norm_nonneg _) hre
        _ = (Finset.univ.erase i₀).card * (re * (q + re * W)) := by simp
        _ ≤ N * (re * (q + re * W)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : (Finset.univ.erase i₀).card ≤ N := by
              calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
                _ = N := by simp
            exact_mod_cast this
    calc ‖σ‖ * (‖(1 + v i₀)⁻¹‖ * ‖∑ j ∈ Finset.univ.erase i₀, v j * z j‖)
        ≤ 1 * (1 * (N * (re * (q + re * W)))) :=
          mul_le_mul hσ (mul_le_mul hκ hS (norm_nonneg _) zero_le_one) (by positivity) zero_le_one
      _ = N * re * (q + re * W) := by ring
  have hW2 : W ≤ 2 * (p + q) := by
    have h1 : W ≤ p + N * re * (q + re * W) := by
      calc W = ‖y i₀ + (z i₀ - y i₀)‖ := by rw [hW, add_sub_cancel]
        _ ≤ ‖y i₀‖ + ‖z i₀ - y i₀‖ := norm_add_le _ _
        _ ≤ p + N * re * (q + re * W) := add_le_add hy0 hlong
    have h2 : (N : ℝ) * re * (re * W) ≤ 1 / 16 * W := by
      have : (N : ℝ) * re * re ≤ 1 / 4 * (1 / 4) := mul_le_mul hN hre1 hre (by norm_num)
      nlinarith
    have h3 : (N : ℝ) * re * q ≤ 1 / 4 * q := mul_le_mul_of_nonneg_right hN hq
    nlinarith
  refine ⟨hW2, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · calc ‖z j - y j‖ ≤ re * W := hoff j hj
      _ ≤ re * (2 * (p + q)) := mul_le_mul_of_nonneg_left hW2 hre
      _ = 2 * re * (p + q) := by ring
  · have := hoffz j hj
    nlinarith [mul_le_mul_of_nonneg_left hW2 hre]
  · calc ‖z i₀ - y i₀‖ ≤ N * re * (q + re * W) := hlong
      _ ≤ N * re * (q + re * (2 * (p + q))) :=
          mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hW2 hre])
            (by positivity)
      _ = N * re * (q + 2 * re * (p + q)) := by ring

end Estimates

section Stage

variable {N : ℕ} {i₀ : Fin N} {v : Fin N → ℂ} {re : ℝ}

/-- `cay(-σA) y = 2 z - y` with `(1 + σA) z = y`. -/
theorem cayNeg_mulVec (σ : ℂ) (hU : IsUnit (1 + σ • aniA i₀ v).det) (y : Fin N → ℂ) :
    ∃ z : Fin N → ℂ, z + σ • (aniA i₀ v *ᵥ z) = y ∧
      RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y = (2 : ℂ) • z - y := by
  set A := aniA i₀ v with hA
  refine ⟨(1 + σ • A)⁻¹ *ᵥ y, ?_, ?_⟩
  · have h := Matrix.mul_nonsing_inv _ hU
    have h2 : (1 + σ • A) *ᵥ ((1 + σ • A)⁻¹ *ᵥ y) = y := by
      rw [mulVec_mulVec, h, one_mulVec]
    rw [add_mulVec, one_mulVec, smul_mulVec] at h2
    exact h2
  · have e1 : RotFrames.cayMat (-A) σ = (1 + σ • A)⁻¹ * (1 - σ • A) := by
      unfold RotFrames.cayMat
      rw [smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
    have h := Matrix.nonsing_inv_mul _ hU
    rw [e1, ← mulVec_mulVec]
    have e2 : (1 - σ • A) *ᵥ y = (2 : ℂ) • y - (1 + σ • A) *ᵥ y := by
      rw [add_mulVec, sub_mulVec, one_mulVec, smul_mulVec]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [e2, mulVec_sub, mulVec_smul, mulVec_mulVec, h, one_mulVec]

/-- **The deviation along the first stage.**  For `y` with `|y_{i₀}| ≤ p`, `|y_j| ≤ q`
(`j ≠ i₀`) and `σ` of modulus at most `1`, `R = cay(-σA)` moves the coordinates by at most
`4 re (p + q)` (transverse) and `2 N re (q + 2 re (p + q))` (longitudinal). -/
theorem cayNeg_dev (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1) (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re) (hre : 0 ≤ re)
    (hN : (N : ℝ) * re ≤ 1 / 4) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (y : Fin N → ℂ) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hy0 : ‖y i₀‖ ≤ p) (hy : ∀ j, j ≠ i₀ → ‖y j‖ ≤ q) :
    (∀ j, j ≠ i₀ → ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) j - y j‖ ≤ 4 * re * (p + q)) ∧
      ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i₀ - y i₀‖ ≤
        2 * (N * re * (q + 2 * re * (p + q))) := by
  have hU : IsUnit (1 + σ • aniA i₀ v).det := by
    have := aniA_isUnit hκ hv hre hN (σ := -σ) (by rwa [norm_neg])
    simpa [neg_smul, sub_neg_eq_add] using this
  obtain ⟨z, hz, hR⟩ := cayNeg_mulVec σ hU y
  obtain ⟨-, h2, -, h4⟩ := aniA_est hκ hv hre hN hσ hz hp hq hy0 hy
  have key : ∀ i, (RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i - y i = 2 * (z i - y i) := fun i => by
    rw [hR]; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [key, norm_mul]
    have := h2 j hj
    norm_num
    nlinarith
  · rw [key, norm_mul]
    norm_num
    nlinarith

end Stage

section Frame

variable {N : ℕ}

theorem aniso_v_props {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) (i₀ : Fin N)
    {re : ℝ} (hre0 : 0 ≤ re) (hN : (N : ℝ) * re ≤ 1 / 4)
    (hMe : ∀ i, ‖(M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ re) :
    ‖(1 + (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i₀)⁻¹‖ ≤ 1 ∧
      (∀ i, i ≠ i₀ → ‖(M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i‖ ≤ re) ∧
      ∑ j, (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) j * (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) j = 1 ∧
      1 + (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i₀ ≠ 0 := by
  set E : Fin N → ℂ := Pi.single i₀ 1 with hE
  set v := M *ᵥ E with hv
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hre1 : re ≤ 1 / 4 := by nlinarith
  have h0 : ‖v i₀ - 1‖ ≤ re := by simpa [hE] using hMe i₀
  have hge : (3 : ℝ) / 2 ≤ ‖1 + v i₀‖ := by
    have : ‖(2 : ℂ)‖ ≤ ‖1 + v i₀‖ + ‖v i₀ - 1‖ := by
      calc ‖(2 : ℂ)‖ = ‖(1 + v i₀) - (v i₀ - 1)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have hne : 1 + v i₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hge; linarith
  refine ⟨?_, fun i hi => ?_, ?_, hne⟩
  · rw [norm_inv]
    exact inv_le_one_of_one_le₀ (by linarith)
  · simpa [hE, Pi.single_apply, hi] using hMe i
  · have h1 : ∑ j, v j * v j = v ⬝ᵥ v := rfl
    rw [h1]
    calc v ⬝ᵥ v = v ⬝ᵥ (M *ᵥ E) := rfl
      _ = (v ᵥ* M) ⬝ᵥ E := dotProduct_mulVec _ _ _
      _ = (M.transpose *ᵥ v) ⬝ᵥ E := by rw [mulVec_transpose]
      _ = ((M.transpose * M) *ᵥ E) ⬝ᵥ E := by rw [hv, mulVec_mulVec]
      _ = 1 := by rw [hM, one_mulVec]; simp [hE, dotProduct, Pi.single_apply]

/-- **The second-stage matrix**: `M' = cay(-A) M` is complex orthogonal and fixes `e`. -/
theorem aniso_Mprime_props {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1)
    (i₀ : Fin N) {re : ℝ} (hre0 : 0 ≤ re) (hN : (N : ℝ) * re ≤ 1 / 4)
    (hMe : ∀ i, ‖(M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ re) :
    (RotFrames.cayMat (-aniA i₀ (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))) 1 * M).transpose *
        (RotFrames.cayMat (-aniA i₀ (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))) 1 * M) = 1 ∧
      (RotFrames.cayMat (-aniA i₀ (M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ))) 1 * M) *ᵥ
        (Pi.single i₀ 1 : Fin N → ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) := by
  obtain ⟨hκ, hv, hvv, hne⟩ := aniso_v_props hM i₀ hre0 hN hMe
  set E : Fin N → ℂ := Pi.single i₀ 1 with hE
  set v := M *ᵥ E with hvdef
  set A := aniA i₀ v with hA
  have hU1 : IsUnit (1 - A).det := by
    have := aniA_isUnit hκ hv hre0 hN (σ := 1) (by simp)
    simpa [hA] using this
  have hU2 : IsUnit (1 + A).det := by
    have := aniA_isUnit hκ hv hre0 hN (σ := -1) (by simp)
    simpa [hA, neg_smul, sub_neg_eq_add] using this
  have hAT : A.transpose = -A := aniA_transpose i₀ v
  have hcayT : RotFrames.cayMat A 1 = (1 - A)⁻¹ * (1 + A) := by
    unfold RotFrames.cayMat; simp
  have hcayT' : RotFrames.cayMat (-A) 1 = (1 + A)⁻¹ * (1 - A) := by
    unfold RotFrames.cayMat; simp [sub_eq_add_neg]
  have hTE : ((1 - A)⁻¹ * (1 + A)) *ᵥ E = v := by
    have h1 : (1 + A) *ᵥ E = (1 - A) *ᵥ v := by
      have h := aniA_mulVec_add i₀ v hne hvv
      rw [← hE, ← hA, mulVec_add] at h
      rw [add_mulVec, sub_mulVec, one_mulVec, one_mulVec]
      funext i
      have := congrFun h i
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      linear_combination this
    rw [← mulVec_mulVec, h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hU1, one_mulVec]
  have hTT : ((1 + A)⁻¹ * (1 - A)) * ((1 - A)⁻¹ * (1 + A)) = 1 := by
    calc ((1 + A)⁻¹ * (1 - A)) * ((1 - A)⁻¹ * (1 + A))
        = (1 + A)⁻¹ * ((1 - A) * (1 - A)⁻¹) * (1 + A) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hU1, Matrix.mul_one, Matrix.nonsing_inv_mul _ hU2]
  have hortho : (RotFrames.cayMat (-A) 1).transpose * RotFrames.cayMat (-A) 1 = 1 := by
    refine cayMat_transpose_mul (S := -A) (by rw [transpose_neg, hAT]) (s := 1) ?_
    simpa [sub_neg_eq_add] using hU2
  constructor
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (RotFrames.cayMat (-A) 1).transpose, hortho,
      Matrix.one_mul, hM]
  · rw [← mulVec_mulVec, ← hvdef, hcayT', ← hTE, mulVec_mulVec, hTT, one_mulVec]

end Frame

section Field

open Balaban.Multiscale

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

theorem nu_mul_norm {ν : ℝ} (hν : 0 < ν) (a : ℂ) : ν * ‖a‖ = ‖(ν : ℂ) * a‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]

/-- **The first stage on a spin vector**: `cay(-σA)` moves a vector within `r'` of `e` to within
`2 r' + 8 re` of `e`. -/
theorem cayNeg_spin {i₀ : Fin N} {v : Fin N → ℂ} {re r' : ℝ} (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1)
    (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re) (hre : 0 ≤ re) (hN : (N : ℝ) * re ≤ 1 / 4)
    (hr0 : 0 ≤ r') (hr : r' ≤ 1 / 2) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) (y : Fin N → ℂ)
    (hy : ∀ i, ‖y i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r') (i : Fin N) :
    ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      2 * r' + 8 * re := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hy0 : ‖y i₀‖ ≤ 1 + r' := by
    have := hy i₀
    simp only [Pi.single_apply, ite_true] at this
    calc ‖y i₀‖ = ‖(y i₀ - 1) + 1‖ := by ring_nf
      _ ≤ ‖y i₀ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + r' := by simp at this ⊢; linarith
  have hyj : ∀ j, j ≠ i₀ → ‖y j‖ ≤ r' := fun j hj => by
    simpa [Pi.single_apply, hj] using hy j
  obtain ⟨h1, h2⟩ := cayNeg_dev hκ hv hre hN hσ y (p := 1 + r') (q := r') (by linarith) hr0 hy0 hyj
  by_cases hi : i = i₀
  · subst hi
    have := h2
    have hdev : ‖(RotFrames.cayMat (-aniA i (v)) σ *ᵥ y) i - 1‖ ≤ r' + 2 * (N * re * (r' + 2 * re * (1 + r' + r'))) := by
      calc ‖(RotFrames.cayMat (-aniA i v) σ *ᵥ y) i - 1‖
          = ‖((RotFrames.cayMat (-aniA i v) σ *ᵥ y) i - y i) + (y i - 1)‖ := by ring_nf
        _ ≤ ‖(RotFrames.cayMat (-aniA i v) σ *ᵥ y) i - y i‖ + ‖y i - 1‖ := norm_add_le _ _
        _ ≤ _ := by
            have hh := hy i
            simp only [Pi.single_apply, ite_true] at hh
            linarith
    simp only [Pi.single_apply, ite_true]
    have e1 : (N : ℝ) * re * (r' + 2 * re * (1 + r' + r')) ≤ r' / 4 + re := by
      have a1 : (N : ℝ) * re * r' ≤ 1 / 4 * r' := mul_le_mul_of_nonneg_right hN hr0
      have a2 : (N : ℝ) * re * (2 * re * (1 + r' + r')) ≤ 1 / 4 * (2 * (1 + r' + r') * re) := by
        have : (N : ℝ) * re * (2 * re * (1 + r' + r')) = ((N : ℝ) * re) * (2 * (1 + r' + r') * re) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hN (by positivity)
      nlinarith
    nlinarith
  · simp only [Pi.single_apply, hi, ite_false, sub_zero]
    have hj := h1 i hi
    calc ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i‖
        = ‖((RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i - y i) + y i‖ := by ring_nf
      _ ≤ ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i - y i‖ + ‖y i‖ := norm_add_le _ _
      _ ≤ 4 * re * (1 + r' + r') + r' := add_le_add hj (hyj i hi)
      _ ≤ 2 * r' + 8 * re := by nlinarith

/-- **The first stage on the field vector** (`ν` times the field `g`, `g` within the weighted
radii `rb'`, `rl' ≤ rb'` of `e`): all coordinates of `ν (cay(-σA) g - e)` are at most
`2 rb' + 4 re (ν + rl' + rb')`, and the longitudinal one at most
`rl' + 2 N re (rb' + 2 re (ν + rl' + rb'))`. -/
theorem cayNeg_field {i₀ : Fin N} {v : Fin N → ℂ} {re rb' rl' ν : ℝ} (hν : 0 < ν)
    (hκ : ‖(1 + v i₀)⁻¹‖ ≤ 1) (hv : ∀ i, i ≠ i₀ → ‖v i‖ ≤ re) (hre : 0 ≤ re)
    (hN : (N : ℝ) * re ≤ 1 / 4) (hrl0 : 0 ≤ rl') (hrl : rl' ≤ rb') {σ : ℂ} (hσ : ‖σ‖ ≤ 1)
    (g : Fin N → ℂ) (hg : ∀ i, ν * ‖g i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ rb')
    (hgl : ν * ‖g i₀ - 1‖ ≤ rl') :
    (∀ i, ν * ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ g) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
        2 * rb' + 4 * re * (ν + rl' + rb')) ∧
      ν * ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ g) i₀ - 1‖ ≤
        rl' + 2 * (N * re * (rb' + 2 * re * ((ν + rl') + rb'))) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hrb0 : 0 ≤ rb' := hrl0.trans hrl
  set y : Fin N → ℂ := (ν : ℂ) • g with hy
  have hRy : ∀ i, (RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i =
      (ν : ℂ) * (RotFrames.cayMat (-aniA i₀ v) σ *ᵥ g) i := fun i => by
    rw [hy, mulVec_smul]; rfl
  have hy0 : ‖y i₀‖ ≤ ν + rl' := by
    have e : y i₀ = (ν : ℂ) * ((g i₀ - 1) + 1) := by simp [hy]
    rw [e, ← nu_mul_norm hν]
    calc ν * ‖(g i₀ - 1) + 1‖ ≤ ν * (‖g i₀ - 1‖ + 1) := by
          gcongr; exact (norm_add_le _ _).trans (by simp)
      _ ≤ ν + rl' := by linarith
  have hyj : ∀ j, j ≠ i₀ → ‖y j‖ ≤ rb' := fun j hj => by
    have := hg j
    simp only [Pi.single_apply, hj, ite_false, sub_zero] at this
    simpa [hy, norm_mul, Complex.norm_real, abs_of_pos hν] using this
  obtain ⟨h1, h2⟩ := cayNeg_dev hκ hv hre hN hσ y (p := ν + rl') (q := rb')
    (by linarith) (by linarith) hy0 hyj
  have hl : ν * ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ g) i₀ - 1‖ ≤
      rl' + 2 * (N * re * (rb' + 2 * re * ((ν + rl') + rb'))) := by
    have e : ν * ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ g) i₀ - 1‖ =
        ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i₀ - (ν : ℂ)‖ := by
      rw [nu_mul_norm hν, mul_sub, mul_one, ← hRy]
    have e2 : y i₀ - (ν : ℂ) = (ν : ℂ) * (g i₀ - 1) := by simp [hy]; ring
    rw [e]
    calc ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i₀ - (ν : ℂ)‖
        = ‖((RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i₀ - y i₀) + (y i₀ - (ν : ℂ))‖ := by ring_nf
      _ ≤ ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i₀ - y i₀‖ + ‖y i₀ - (ν : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ 2 * (N * re * (rb' + 2 * re * ((ν + rl') + rb'))) + rl' := by
          refine add_le_add h2 ?_
          rw [e2, ← nu_mul_norm hν]; exact hgl
      _ = _ := by ring
  refine ⟨fun i => ?_, hl⟩
  by_cases hi : i = i₀
  · subst hi
    have hP : 0 ≤ ν + rl' + rb' := by linarith
    have a1 : (N : ℝ) * re * rb' ≤ 1 / 4 * rb' :=
      mul_le_mul_of_nonneg_right hN (by linarith)
    have a2 : (N : ℝ) * re * (2 * re * (ν + rl' + rb')) ≤ 1 / 4 * (2 * re * (ν + rl' + rb')) :=
      mul_le_mul_of_nonneg_right hN (by nlinarith)
    have e : ν * ‖(RotFrames.cayMat (-aniA i v) σ *ᵥ g) i - (Pi.single i 1 : Fin N → ℂ) i‖ =
        ν * ‖(RotFrames.cayMat (-aniA i v) σ *ᵥ g) i - 1‖ := by simp
    rw [e]
    refine hl.trans ?_
    nlinarith
  · have e : ν * ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ g) i -
        (Pi.single i₀ 1 : Fin N → ℂ) i‖ = ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i‖ := by
      simp only [Pi.single_apply, hi, ite_false, sub_zero]
      rw [nu_mul_norm hν, hRy]
    rw [e]
    calc ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i‖
        = ‖((RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i - y i) + y i‖ := by ring_nf
      _ ≤ ‖(RotFrames.cayMat (-aniA i₀ v) σ *ᵥ y) i - y i‖ + ‖y i‖ := norm_add_le _ _
      _ ≤ 4 * re * ((ν + rl') + rb') + rb' := add_le_add (h1 i hi) (hyj i hi)
      _ ≤ 2 * rb' + 4 * re * (ν + rl' + rb') := by nlinarith [hrl]

end Field

section Main

open Balaban.Multiscale

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **Complex invariance on the anisotropic polydisc** (abstract form).  Let `F` be analytic on a
set `D` of pairs of fields and invariant under the real orthogonal matrices, `M` a complex orthogonal
matrix, `e = e_{i₀}`, and `(Ψ, h)`, `(MΨ, Mh)` two pairs of a class `P'` (closed under all
matrices; here block-constant `Ψ` and constant `h = g`) within the radii
`|Ψ - e| ≤ r`, `|MΨ - e| ≤ r'`, `ν |g - e| ≤ rb`, `ν |g_{i₀} - 1| ≤ rl`, and the same for `Mg`
(`rb'`, `rl'`), with `|M e - e| ≤ re`, `N re ≤ 1/4`.  Let `D` contain the pairs of `P'` in the box
of radii `ρs` (spins), `ρb` (all coordinates of `ν (g - e)`), `ρl` (the longitudinal one).  Then
`F (MΨ) (Mh) = F Ψ h`.  The path has two stages (module docstring); the longitudinal coordinate
changes only by `O(re (r + re))` in the first stage and not at all in the second. -/
theorem rotE_of_near_aniso_within
    (F : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → ℂ)
    (D : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N))
    (hF : AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F p.1 p.2) D)
    (hreal : ∀ Q : Matrix (Fin N) (Fin N) ℂ, IsRot Q → ∀ Ψ h, (Ψ, h) ∈ D →
      (Def6.rotField Q Ψ, Def6.rotField Q h) ∈ D →
      F (Def6.rotField Q Ψ) (Def6.rotField Q h) = F Ψ h)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) (i₀ : Fin N) {ν : ℝ} (hν : 0 < ν)
    {r r' rb rb' rl rl' re ρs ρb ρl : ℝ} (hr0 : 0 ≤ r) (hr'0 : 0 ≤ r') (hr' : r' ≤ 1 / 2)
    (hrb0 : 0 ≤ rb) (hrl0' : 0 ≤ rl') (hrl' : rl' ≤ rb')
    (hre0 : 0 ≤ re) (hNre : (N : ℝ) * re ≤ 1 / 4)
    (hMe : ∀ i, ‖(M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ re)
    (hρs : Real.sqrt N * (r + (2 * r' + 8 * re)) ≤ ρs)
    (hρb : Real.sqrt N * (rb + (2 * rb' + 4 * re * (ν + rl' + rb'))) ≤ ρb)
    (hρl : rl ≤ ρl)
    (hρl' : rl' + 2 * (N * re * (rb' + 2 * re * ((ν + rl') + rb'))) ≤ ρl)
    (P' : Fld d L N₁ m₁ k N → Fld d L N₁ m₁ k N → Prop)
    (hP : ∀ (R : Matrix (Fin N) (Fin N) ℂ) Ψ h, P' Ψ h →
      P' (Def6.rotField R Ψ) (Def6.rotField R h))
    (hDm : ∀ Ψ' h', P' Ψ' h' →
      (∀ x i, ‖Ψ' x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs) →
      (∀ x i, ν * ‖h' x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρb) →
      (∀ x, ν * ‖h' x i₀ - 1‖ ≤ ρl) → (Ψ', h') ∈ D)
    {Ψ h : Fld d L N₁ m₁ k N} (hPΨ : P' Ψ h) (hh : ∀ x y, h x = h y)
    (hDn : D ∈ 𝓝[{p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2}] (Ψ, h))
    (hDn' : D ∈ 𝓝[{p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2}]
      (Def6.rotField M Ψ, Def6.rotField M h))
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (hΨM : ∀ x i, ‖M.mulVec (Ψ x) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r')
    (hb : ∀ x i, ν * ‖h x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ rb)
    (hbl : ∀ x, ν * ‖h x i₀ - 1‖ ≤ rl)
    (hbM : ∀ x i, ν * ‖M.mulVec (h x) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ rb')
    (hbMl : ∀ x, ν * ‖M.mulVec (h x) i₀ - 1‖ ≤ rl') :
    F (Def6.rotField M Ψ) (Def6.rotField M h) = F Ψ h := by
  classical
  set E : Fin N → ℂ := Pi.single i₀ 1 with hE
  have he : ∀ i, star (E i) = E i := fun i => by
    by_cases hi : i = i₀ <;> simp [hE, hi]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hs1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  obtain ⟨hκ, hv, hvv, hne⟩ := aniso_v_props hM i₀ hre0 hNre hMe
  obtain ⟨hM'o, hM'E⟩ := aniso_Mprime_props hM i₀ hre0 hNre hMe
  set v := M *ᵥ E with hvdef
  set A := aniA i₀ v with hA
  set T := RotFrames.cayMat (-A) 1 with hT
  set M' := T * M with hM'
  obtain ⟨C, hC0, hMb'⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ i j, ‖M' i j‖ ≤ C :=
    ⟨∑ i, ∑ j, ‖M' i j‖, by positivity, fun i j =>
      (Finset.single_le_sum (f := fun j => ‖M' i j‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M' i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))⟩
  have hη : vn (M' *ᵥ E - E) ≤ 0 := by rw [hM'E, sub_self]; simp [vn]
  obtain ⟨Q, S2, hQ, hS2, hunit2, hMQ, hpathv⟩ := exists_cay_path_near hM'o hC0 hMb' he hη
  -- second stage: `cay(sS₂) e = e`, orthogonality, and the longitudinal coordinate
  have hCE : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → RotFrames.cayMat S2 (s : ℂ) *ᵥ E = E := fun s h0 h1 => by
    have := hpathv s h0 h1 0 0 E (by simp [vn]) (by rw [hM'E, sub_self]; simp [vn])
    funext i
    have h2 : ‖(RotFrames.cayMat S2 (s : ℂ) *ᵥ E - E) i‖ ≤ 0 :=
      (norm_le_vn _ i).trans (by simpa using this)
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  have hCrow : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ y : Fin N → ℂ,
      (RotFrames.cayMat S2 (s : ℂ) *ᵥ y) i₀ = y i₀ := fun s h0 h1 y => by
    have horth := cayMat_transpose_mul hS2 (hunit2 s h0 h1)
    have hTE : (RotFrames.cayMat S2 (s : ℂ)).transpose *ᵥ E = E := by
      conv_lhs => rw [← hCE s h0 h1]
      rw [mulVec_mulVec, horth, one_mulVec]
    have : E ⬝ᵥ (RotFrames.cayMat S2 (s : ℂ) *ᵥ y) = (E ᵥ* RotFrames.cayMat S2 (s : ℂ)) ⬝ᵥ y :=
      dotProduct_mulVec _ _ _
    rw [← mulVec_transpose, hTE] at this
    simpa [hE, dotProduct, Pi.single_apply] using this
  -- the data
  set g : Fin N → ℂ := h 0 with hg
  have hhx : ∀ x, h x = g := fun x => hh x 0
  have hrb'0 : 0 ≤ rb' := hrl0'.trans hrl'
  set s1 : ℝ := 2 * r' + 8 * re with hs1def
  set b1 : ℝ := 2 * rb' + 4 * re * (ν + rl' + rb') with hb1def
  have hs1pos : 0 ≤ s1 := by positivity
  have hb1pos : 0 ≤ b1 := by
    have : 0 ≤ ν + rl' + rb' := by linarith
    positivity
  have hs1ρ : r + s1 ≤ ρs := by
    have := mul_le_mul_of_nonneg_right hs1 (add_nonneg hr0 hs1pos)
    linarith
  have hb1ρ : rb + b1 ≤ ρb := by
    have := mul_le_mul_of_nonneg_right hs1 (add_nonneg hrb0 hb1pos)
    linarith
  have hσn : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ‖(σ : ℂ)‖ ≤ 1 := fun σ h0 h1 => by
    simpa [Complex.norm_real, abs_of_nonneg h0] using h1
  have hgM : ∀ x, M.mulVec (h x) = M *ᵥ g := fun x => by rw [hhx x]
  -- the first stage on the data of the second pair
  have spin1 : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 → ∀ y : Fin N → ℂ, (∀ i, ‖y i - E i‖ ≤ r') →
      ∀ i, ‖(RotFrames.cayMat (-A) (σ : ℂ) *ᵥ y) i - E i‖ ≤ s1 :=
    fun σ h0 h1 y hy i => cayNeg_spin hκ hv hre0 hNre hr'0 hr' (hσn σ h0 h1) y hy i
  have fld1 := fun σ (h0 : 0 ≤ σ) (h1 : σ ≤ 1) =>
    cayNeg_field (ν := ν) hν hκ hv hre0 hNre hrl0' hrl' (hσn σ h0 h1) (M *ᵥ g)
      (fun i => by simpa [hgM] using hbM 0 i) (by simpa [hgM] using hbMl 0)
  have hT1 : RotFrames.cayMat (-A) ((1 : ℝ) : ℂ) = T := by simp [hT]
  -- memberships along the first stage
  have hP1 : P' (Def6.rotField M Ψ) (Def6.rotField M h) := hP M Ψ h hPΨ
  have hmem1 : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      (Def6.rotField (RotFrames.cayMat (-A) (σ : ℂ)) (Def6.rotField M Ψ),
        Def6.rotField (RotFrames.cayMat (-A) (σ : ℂ)) (Def6.rotField M h)) ∈ D := by
    intro σ h0 h1
    refine hDm _ _ (hP _ _ _ hP1) (fun x i => ?_) (fun x i => ?_) (fun x => ?_)
    · exact (spin1 σ h0 h1 (M.mulVec (Ψ x)) (hΨM x) i).trans (by linarith)
    · show ν * ‖(RotFrames.cayMat (-A) (σ : ℂ) *ᵥ (M *ᵥ h x)) i - E i‖ ≤ ρb
      rw [hhx x]
      exact ((fld1 σ h0 h1).1 i).trans (by linarith)
    · show ν * ‖(RotFrames.cayMat (-A) (σ : ℂ) *ᵥ (M *ᵥ h x)) i₀ - 1‖ ≤ ρl
      rw [hhx x]
      exact (fld1 σ h0 h1).2.trans hρl'
  have hend1 : (Def6.rotField (1 * T) (Def6.rotField M Ψ), Def6.rotField (1 * T) (Def6.rotField M h))
      ∈ D := by
    have := hmem1 1 zero_le_one le_rfl
    rw [hT1] at this
    rwa [Matrix.one_mul]
  have hS1 : (-A).transpose = -(-A) := by rw [transpose_neg, hA, aniA_transpose]
  have hunit1 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → IsUnit (1 - (s : ℂ) • (-A)).det := fun s h0 h1 => by
    have := aniA_isUnit hκ hv hre0 hNre (σ := -(s : ℂ)) (by rw [norm_neg]; exact hσn s h0 h1)
    simpa [hA, neg_smul, sub_neg_eq_add, smul_neg] using this
  have hIsRot1 : IsRot (1 : Matrix (Fin N) (Fin N) ℂ) :=
    ⟨by simp, fun i j => by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]⟩
  have stage1 := rotE_eq_of_cay_path_within F D hF hreal hIsRot1 hS1 hunit1
    {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2} hDn'
    (fun R => hP R _ _ hP1) hmem1 hend1
  -- the second stage
  have hsupvn : ∀ w : Fin N → ℂ, ∀ i, ‖w i‖ ≤ vn w := fun w i => norm_le_vn w i
  have hmem2 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (Def6.rotField (RotFrames.cayMat S2 (s : ℂ)) Ψ,
        Def6.rotField (RotFrames.cayMat S2 (s : ℂ)) h) ∈ D := by
    intro s h0 h1
    refine hDm _ _ (hP _ _ _ hPΨ) (fun x i => ?_) (fun x i => ?_) (fun x => ?_)
    · have hv1 : vn (Ψ x - E) ≤ Real.sqrt N * r :=
        vn_le_sqrt_card_mul hr0 (fun i => hΨ x i)
      have hv2 : vn (M' *ᵥ Ψ x - E) ≤ Real.sqrt N * s1 :=
        vn_le_sqrt_card_mul hs1pos (fun i => by
          have e : M' *ᵥ Ψ x = RotFrames.cayMat (-A) ((1 : ℝ) : ℂ) *ᵥ (M *ᵥ Ψ x) := by
            rw [hM', ← mulVec_mulVec, hT1]
          rw [e]
          exact spin1 1 zero_le_one le_rfl _ (hΨM x) i)
      have := hpathv s h0 h1 _ _ (Ψ x) hv1 hv2
      refine (hsupvn _ i).trans (this.trans ?_)
      nlinarith
    · have hgE : ∀ i, ‖g i - E i‖ ≤ rb / ν := fun i => by
        rw [le_div_iff₀ hν, mul_comm]; simpa [hhx 0] using hb 0 i
      have hv1 : vn (g - E) ≤ Real.sqrt N * (rb / ν) :=
        vn_le_sqrt_card_mul (by positivity) (fun i => hgE i)
      have hgE2 : ∀ i, ‖(M' *ᵥ g - E) i‖ ≤ b1 / ν := fun i => by
        have e : M' *ᵥ g = RotFrames.cayMat (-A) ((1 : ℝ) : ℂ) *ᵥ (M *ᵥ g) := by
          rw [hM', ← mulVec_mulVec, hT1]
        rw [le_div_iff₀ hν, mul_comm]
        show ν * ‖(M' *ᵥ g) i - E i‖ ≤ b1
        rw [e]
        exact (fld1 1 zero_le_one le_rfl).1 i
      have hv2 : vn (M' *ᵥ g - E) ≤ Real.sqrt N * (b1 / ν) :=
        vn_le_sqrt_card_mul (by positivity) hgE2
      have := hpathv s h0 h1 _ _ g hv1 hv2
      have hx : Def6.rotField (RotFrames.cayMat S2 (s : ℂ)) h x = RotFrames.cayMat S2 (s : ℂ) *ᵥ g := by
        show RotFrames.cayMat S2 (s : ℂ) *ᵥ h x = _
        rw [hhx x]
      rw [hx]
      have h3 : ‖(RotFrames.cayMat S2 (s : ℂ) *ᵥ g) i - E i‖ ≤
          Real.sqrt N * (rb / ν) + Real.sqrt N * (b1 / ν) := by
        refine (hsupvn (RotFrames.cayMat S2 (s : ℂ) *ᵥ g - E) i).trans (this.trans ?_)
        simp
      calc ν * ‖(RotFrames.cayMat S2 (s : ℂ) *ᵥ g) i - E i‖
          ≤ ν * (Real.sqrt N * (rb / ν) + Real.sqrt N * (b1 / ν)) :=
            mul_le_mul_of_nonneg_left h3 hν.le
        _ = Real.sqrt N * (rb + b1) := by field_simp
        _ ≤ ρb := by nlinarith
    · have hx : Def6.rotField (RotFrames.cayMat S2 (s : ℂ)) h x = RotFrames.cayMat S2 (s : ℂ) *ᵥ g := by
        show RotFrames.cayMat S2 (s : ℂ) *ᵥ h x = _
        rw [hhx x]
      rw [hx, hCrow s h0 h1 g]
      exact (hbl 0).trans hρl |> fun h' => by simpa [hhx 0] using h'
  have hend2 : (Def6.rotField (Q * RotFrames.cayMat S2 1) Ψ,
      Def6.rotField (Q * RotFrames.cayMat S2 1) h) ∈ D := by
    rw [← hMQ, hM', rotField_mul, rotField_mul]
    rwa [Matrix.one_mul] at hend1
  have stage2 := rotE_eq_of_cay_path_within F D hF hreal hQ hS2 hunit2
    {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | P' p.1 p.2} hDn
    (fun R => hP R _ _ hPΨ) hmem2 hend2
  calc F (Def6.rotField M Ψ) (Def6.rotField M h)
      = F (Def6.rotField (1 * T) (Def6.rotField M Ψ)) (Def6.rotField (1 * T) (Def6.rotField M h)) :=
        stage1.symm
    _ = F (Def6.rotField (Q * RotFrames.cayMat S2 1) Ψ)
          (Def6.rotField (Q * RotFrames.cayMat S2 1) h) := by
        rw [← hMQ, hM', Matrix.one_mul, rotField_mul, rotField_mul]
    _ = F Ψ h := stage2

end Main

section Radii

/-- **The constant of the anisotropic radius condition**: the polydisc of radius `r` is admissible
when `r · aniK N B νb ≤ δ` (`B` the entry bound of the rotations, `νb` an upper bound of the mass
`ν_j`). -/
noncomputable def aniK (N : ℕ) (B νb : ℝ) : ℝ :=
  4 * N * Real.sqrt N * (1 + N * B) ^ 2 * (4 * |νb| + 11)

theorem aniK_pos {N : ℕ} (i₀ : Fin N) {B : ℝ} (hB : 0 ≤ B) (νb : ℝ) : 0 < aniK N B νb := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  unfold aniK
  positivity

/-- The elementary inequalities for the constant `K = 4 n s a² (4 m + 11)`. -/
theorem aniK_facts {n s a m : ℝ} (hn : 1 ≤ n) (hs : 1 ≤ s) (ha : 1 ≤ a) (hm : 0 ≤ m) :
    44 * n * a ≤ 4 * n * s * a ^ 2 * (4 * m + 11) ∧
      4 * n * s * (11 + 10 * (a - 1)) ≤ 4 * n * s * a ^ 2 * (4 * m + 11) ∧
      2 * n * s * (3 + 4 * a * (m + 2)) ≤ 4 * n * s * a ^ 2 * (4 * m + 11) ∧
      2 * (1 + 2 * n * a * (1 + 2 * a * (m + 2))) ≤ 4 * n * s * a ^ 2 * (4 * m + 11) := by
  have hn0 : 0 ≤ n := by linarith
  have ha2 : a ≤ a ^ 2 := by nlinarith
  have hsa2 : a ≤ s * a ^ 2 := by
    calc a ≤ a ^ 2 := ha2
      _ = 1 * a ^ 2 := by ring
      _ ≤ s * a ^ 2 := by gcongr
  have hc : 11 ≤ 4 * m + 11 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc 44 * n * a = 4 * n * 11 * a := by ring
      _ ≤ 4 * n * 11 * (s * a ^ 2) := by gcongr
      _ = 4 * n * s * a ^ 2 * 11 := by ring
      _ ≤ 4 * n * s * a ^ 2 * (4 * m + 11) := by gcongr
  · have h1 : (11 + 10 * (a - 1) : ℝ) ≤ a ^ 2 * (4 * m + 11) := by
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg a)]
    calc 4 * n * s * (11 + 10 * (a - 1)) ≤ 4 * n * s * (a ^ 2 * (4 * m + 11)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * n * s * a ^ 2 * (4 * m + 11) := by ring
  · have h1 : (3 + 4 * a * (m + 2) : ℝ) ≤ 2 * (a ^ 2 * (4 * m + 11)) := by
      have h3 : a * m ≤ a ^ 2 * m := mul_le_mul_of_nonneg_right ha2 hm
      nlinarith
    calc 2 * n * s * (3 + 4 * a * (m + 2)) ≤ 2 * n * s * (2 * (a ^ 2 * (4 * m + 11))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * n * s * a ^ 2 * (4 * m + 11) := by ring
  · have e1 : (1 : ℝ) ≤ n * a ^ 2 := by nlinarith
    have e2 : n * a ≤ n * a ^ 2 := mul_le_mul_of_nonneg_left ha2 hn0
    have e3 : 0 ≤ n * a ^ 2 * m := by positivity
    have h1 : 2 * (1 + 2 * n * a * (1 + 2 * a * (m + 2))) ≤ 4 * n * (a ^ 2 * (4 * m + 11)) := by
      nlinarith
    calc 2 * (1 + 2 * n * a * (1 + 2 * a * (m + 2))) ≤ 4 * n * (a ^ 2 * (4 * m + 11)) := h1
      _ = 4 * n * 1 * a ^ 2 * (4 * m + 11) := by ring
      _ ≤ 4 * n * s * a ^ 2 * (4 * m + 11) := by gcongr

/-- **The radii of the box of the two-stage path** (arithmetic).  For `0 < r ≤ 1`, `0 ≤ B`,
`0 < ν ≤ ν̄`, `r · aniK N B ν̄ ≤ δ ≤ 1/16`, with `r' = re = r (1 + N B)`: the numbers
`N re ≤ 1/4`, `r' ≤ 1/2`, and the box radii `ρs`, `ρb`, `ρl` satisfy `4 N ρs ≤ δ`, `2 N ρb ≤ δ`,
`ρl < δ²`. -/
theorem aniso_box_arith {N : ℕ} (i₀ : Fin N) {r B ν νb δ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hB : 0 ≤ B) (hνb : ν ≤ νb) (hrδ : r * aniK N B νb ≤ δ) (hδ : δ ≤ 1 / 16) :
    (N : ℝ) * (r * (1 + N * B)) ≤ 1 / 4 ∧ r * (1 + N * B) ≤ 1 / 2 ∧
      4 * N * (Real.sqrt N * (r + (2 * (r * (1 + N * B)) + 8 * (r * (1 + N * B))))) ≤ δ ∧
      2 * N * (Real.sqrt N * (r + (2 * r + 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r)))) ≤ δ ∧
      r ^ 2 * (1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (νb + 2))) < δ ^ 2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hs : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hn
  have ha : (1 : ℝ) ≤ 1 + N * B := by nlinarith
  have hνa : 0 ≤ |νb| := abs_nonneg _
  obtain ⟨k1, k3, k4, kl⟩ := aniK_facts hn hs ha hνa
  have hKd : aniK N B νb = 4 * N * Real.sqrt N * (1 + N * B) ^ 2 * (4 * |νb| + 11) := rfl
  rw [hKd] at hrδ
  have hrK : r * (4 * N * Real.sqrt N * (1 + N * B) ^ 2 * (4 * |νb| + 11)) ≤ 1 / 16 := hrδ.trans hδ
  have hKpos : 0 < 4 * (N : ℝ) * Real.sqrt N * (1 + N * B) ^ 2 * (4 * |νb| + 11) := by positivity
  have e1 : (N : ℝ) * (r * (1 + N * B)) ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left k1 hr0.le
    nlinarith
  refine ⟨e1, ?_, ?_, ?_, ?_⟩
  · have : r * (1 + N * B) ≤ N * (r * (1 + N * B)) := by nlinarith [mul_pos hr0 (by linarith : (0:ℝ) < 1 + N * B)]
    linarith
  · have := mul_le_mul_of_nonneg_left k3 hr0.le
    have e : 4 * (N : ℝ) * (Real.sqrt N * (r + (2 * (r * (1 + N * B)) + 8 * (r * (1 + N * B))))) =
        r * (4 * N * Real.sqrt N * (11 + 10 * ((1 + N * B) - 1))) := by ring
    rw [e]; exact this.trans hrδ
  · have hν2 : ν + r ^ 2 + r ≤ |νb| + 2 := by
      have : ν ≤ |νb| := hνb.trans (le_abs_self _)
      nlinarith
    have e2 : 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r) ≤ 4 * (r * (1 + N * B)) * (|νb| + 2) :=
      mul_le_mul_of_nonneg_left hν2 (by positivity)
    have e3 : 2 * (N : ℝ) * (Real.sqrt N * (r + (2 * r + 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r)))) ≤
        r * (2 * N * Real.sqrt N * (3 + 4 * (1 + N * B) * (|νb| + 2))) := by
      have h0 : (0 : ℝ) ≤ 2 * N * Real.sqrt N := by positivity
      calc 2 * (N : ℝ) * (Real.sqrt N * (r + (2 * r + 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r))))
          = (2 * N * Real.sqrt N) * (r + (2 * r + 4 * (r * (1 + N * B)) * (ν + r ^ 2 + r))) := by ring
        _ ≤ (2 * N * Real.sqrt N) * (r + (2 * r + 4 * (r * (1 + N * B)) * (|νb| + 2))) :=
            mul_le_mul_of_nonneg_left (by linarith) h0
        _ = r * (2 * N * Real.sqrt N * (3 + 4 * (1 + N * B) * (|νb| + 2))) := by ring
    exact e3.trans ((mul_le_mul_of_nonneg_left k4 hr0.le).trans hrδ)
  · have hl1 : 1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (νb + 2)) ≤
        1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (|νb| + 2)) := by
      have : νb ≤ |νb| := le_abs_self _
      gcongr
    set Kc : ℝ := 4 * (N : ℝ) * Real.sqrt N * (1 + N * B) ^ 2 * (4 * |νb| + 11) with hKc
    set X : ℝ := 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (|νb| + 2)) with hX
    have hX0 : 0 ≤ X := by positivity
    have hK2 : 2 ≤ Kc := by linarith
    have hrK2 : (r * Kc) ^ 2 ≤ δ ^ 2 := by
      have h0 : 0 ≤ r * Kc := by positivity
      nlinarith
    have hA : 1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (νb + 2)) ≤ Kc / 2 := by
      have : 2 * (1 + X) ≤ Kc := kl
      linarith
    have h1 : r ^ 2 * (1 + 2 * N * (1 + N * B) * (1 + 2 * (1 + N * B) * (νb + 2))) ≤
        r ^ 2 * (Kc / 2) := mul_le_mul_of_nonneg_left hA (by positivity)
    have h3 : r ^ 2 * (Kc / 2) < (r * Kc) ^ 2 := by
      have : 0 < r ^ 2 * Kc := by positivity
      nlinarith
    linarith

end Radii

section Term

open Balaban.Multiscale

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/-- **Complex invariance of the energy terms on the anisotropic polydisc** (term-clause form):
`rotE_of_near_aniso_within` for `F = ℰ(y, X)` and the domain `Dom`, with the block-constant fields
with a constant `h` as the class `P'`.  The box membership `hbox` and the openness relative to the
block-constant pairs `hopen` are the facts about the domain (`xiDom_eventually`). -/
theorem SFTermClauses.rotE_of_near_aniso {P : Consts} {ϱ : ℝ}
    {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}
    (hT : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) {y X}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.transpose * M = 1) (i₀ : Fin N) {ν : ℝ} (hν : 0 < ν)
    {r r' rb rb' rl rl' re ρs ρb ρl : ℝ} (hr0 : 0 ≤ r) (hr'0 : 0 ≤ r') (hr' : r' ≤ 1 / 2)
    (hrb0 : 0 ≤ rb) (hrl0' : 0 ≤ rl') (hrl' : rl' ≤ rb') (hre0 : 0 ≤ re)
    (hNre : (N : ℝ) * re ≤ 1 / 4)
    (hMe : ∀ i, ‖(M *ᵥ (Pi.single i₀ 1 : Fin N → ℂ)) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ re)
    (hρs : Real.sqrt N * (r + (2 * r' + 8 * re)) ≤ ρs)
    (hρb : Real.sqrt N * (rb + (2 * rb' + 4 * re * (ν + rl' + rb'))) ≤ ρb)
    (hρl : rl ≤ ρl)
    (hρl' : rl' + 2 * (N * re * (rb' + 2 * re * ((ν + rl') + rb'))) ≤ ρl)
    (hbox : ∀ Ψ' h' : Fld d L N₁ m₁ k N, Def6.IsBlockConstFld j Ψ' → (∀ x x', h' x = h' x') →
      (∀ x i, ‖Ψ' x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs) →
      (∀ x i, ν * ‖h' x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρb) →
      (∀ x, ν * ‖h' x i₀ - 1‖ ≤ ρl) → Dom.dom j (Tm.gs j X) Ψ' h')
    (hopen : ∀ Ψ' h' : Fld d L N₁ m₁ k N, Def6.IsBlockConstFld j Ψ' → (∀ x x', h' x = h' x') →
      Dom.dom j (Tm.gs j X) Ψ' h' →
      {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N | Dom.dom j (Tm.gs j X) p.1 p.2} ∈
        𝓝[{p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N |
          Def6.IsBlockConstFld j p.1 ∧ ∀ x x', p.2 x = p.2 x'}] (Ψ', h'))
    {Ψ h : Fld d L N₁ m₁ k N} (hΨb : Def6.IsBlockConstFld j Ψ) (hh : ∀ x x', h x = h x')
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r)
    (hΨM : ∀ x i, ‖M.mulVec (Ψ x) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r')
    (hb : ∀ x i, ν * ‖h x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ rb)
    (hbl : ∀ x, ν * ‖h x i₀ - 1‖ ≤ rl)
    (hbM : ∀ x i, ν * ‖M.mulVec (h x) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ rb')
    (hbMl : ∀ x, ν * ‖M.mulVec (h x) i₀ - 1‖ ≤ rl') :
    Tm.E j y X (Def6.rotField M Ψ) (Def6.rotField M h) = Tm.E j y X Ψ h := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hs1 : (1 : ℝ) ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN1
  have hrb'0 : 0 ≤ rb' := hrl0'.trans hrl'
  have hP0 : 0 ≤ ν + rl' + rb' := by linarith
  have hr1 : r ≤ ρs := by
    have := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ r + (2 * r' + 8 * re))
    linarith
  have hr1' : r' ≤ ρs := by
    have := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ r + (2 * r' + 8 * re))
    linarith
  have hq : 0 ≤ 4 * re * (ν + rl' + rb') := by positivity
  have hb1 : rb ≤ ρb := by
    have := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ rb + (2 * rb' + 4 * re * (ν + rl' + rb')))
    linarith
  have hb1' : rb' ≤ ρb := by
    have := mul_le_mul_of_nonneg_right hs1 (by positivity : 0 ≤ rb + (2 * rb' + 4 * re * (ν + rl' + rb')))
    linarith
  have hl1' : rl' ≤ ρl := by
    have : 0 ≤ 2 * ((N : ℝ) * re * (rb' + 2 * re * ((ν + rl') + rb'))) := by positivity
    linarith
  have hconst : ∀ (R : Matrix (Fin N) (Fin N) ℂ) (h' : Fld d L N₁ m₁ k N), (∀ x x', h' x = h' x') →
      ∀ x x', Def6.rotField R h' x = Def6.rotField R h' x' := fun R h' hh' x x' => by
    simp only [Def6.rotField]; rw [hh' x x']
  have hblock : ∀ (R : Matrix (Fin N) (Fin N) ℂ) (Ψ' : Fld d L N₁ m₁ k N),
      Def6.IsBlockConstFld j Ψ' → Def6.IsBlockConstFld j (Def6.rotField R Ψ') :=
    fun R Ψ' hΨ' x x' hxx => by simp only [Def6.rotField]; rw [hΨ' x x' hxx]
  have hboxP : ∀ Ψ' h' : Fld d L N₁ m₁ k N, Def6.IsBlockConstFld j Ψ' → (∀ x x', h' x = h' x') →
      (∀ x i, ‖Ψ' x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρs) →
      (∀ x i, ν * ‖h' x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρb) →
      (∀ x, ν * ‖h' x i₀ - 1‖ ≤ ρl) → Dom.dom j (Tm.gs j X) Ψ' h' := hbox
  refine rotE_of_near_aniso_within (fun Ψ h => Tm.E j y X Ψ h)
    {p | Dom.dom j (Tm.gs j X) p.1 p.2} (hT.analyticE j hj1 hjk y X hX hy)
    (fun Q hQ Ψ h h1 h2 => hT.rotE j hj1 hjk y X hX hy Q hQ Ψ h h1 h2) hM i₀ hν hr0 hr'0 hr'
    hrb0 hrl0' hrl' hre0 hNre hMe hρs hρb hρl hρl'
    (fun Ψ' h' => Def6.IsBlockConstFld j Ψ' ∧ ∀ x x', h' x = h' x')
    (fun R Ψ' h' hP1 => ⟨hblock R Ψ' hP1.1, hconst R h' hP1.2⟩)
    (fun Ψ' h' hP1 hs hb' hl' => hbox Ψ' h' hP1.1 hP1.2 hs hb' hl') ⟨hΨb, hh⟩ hh ?_ ?_ hΨ hΨM hb hbl
    hbM hbMl
  · exact hopen Ψ h hΨb hh (hbox Ψ h hΨb hh (fun x i => (hΨ x i).trans hr1)
      (fun x i => (hb x i).trans hb1) (fun x => (hbl x).trans hρl))
  · exact hopen (Def6.rotField M Ψ) (Def6.rotField M h) (hblock M Ψ hΨb) (hconst M h hh)
      (hbox _ _ (hblock M Ψ hΨb) (hconst M h hh) (fun x i => (hΨM x i).trans hr1')
        (fun x i => (hbM x i).trans hb1') (fun x => (hbMl x).trans hl1'))

end Term

end Balaban.SmallField.Def6v2
