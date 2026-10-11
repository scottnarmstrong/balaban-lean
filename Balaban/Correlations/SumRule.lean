module

public import Balaban.Gaussian.Prolongation
public import Balaban.Lattice.Laplacian
import Mathlib.Tactic.Ring

/-!
# The sum rule on the torus

CORRELATIONS.md §3.4, "The sum rule on the torus". On `Torus d ℓ`, `ℓ = L ^ k * m`, let
`A₀ = -Δ + ν` (`latticeLaplacian`), and let `T_j = fluctTerm k A₀ a j` (`j < k`) be the terms of
the exact multiscale decomposition (`laplacian_inv_eq_multiscale`), with an arbitrary positive
scale sequence `a` (the free flow is `Balaban.freeSeq`). Writing `P_k = prolong k A₀ a`,
`A_k = effOp k A₀ a` and `Q_{(k)} = compositeAvg d L m k`:

* `(-Δ + ν)⁻¹ = ∑_{j<k} T_j + P_k A_k⁻¹ P_kᵀ` (`latticeLaplacian_inv_eq_sum_add_remainder`);
* `A₀ (P_k A_k⁻¹ P_kᵀ) = Q_{(k)}ᵀ P_kᵀ` (`latticeLaplacian_mul_remainder`, from (3.2));
* `A₀ ∑_{j<k} T_j + Q_{(k)}ᵀ P_kᵀ = 1` (`sum_rule_matrix`);
* the entries of `Q_{(k)}ᵀ P_kᵀ` are `(L ^ k)^{-d} P_k(y, u_k(x))` (`compositeAvg_transpose_mul_transpose_apply`)
  and the sum rule in kernel form (`sum_rule_apply`, `sum_rule_apply_abs_le`): for every `x, y`,
  `((-Δ_x + ν) ∑_{j<k} T_j)(x, y) = δ_{xy} - L^{-kd} P_k(y, u_k(x))`.
-/

@[expose] public section

namespace Balaban

open Matrix

variable {d L m : ℕ} [NeZero L] [NeZero m]

/-- The remainder `P_k A_k⁻¹ P_kᵀ` of the multiscale decomposition after `k` steps. -/
noncomputable def multiscaleRemainder (k : ℕ) (A : Matrix (Level d L m k) (Level d L m k) ℝ)
    (a : ℕ → ℝ) : Matrix (Level d L m k) (Level d L m k) ℝ :=
  prolong k A a * (effOp k A a)⁻¹ * (prolong k A a)ᵀ

/-- `A⁻¹ = ∑_{j<k} T_j + remainder`. -/
theorem latticeLaplacian_inv_eq_sum_add_remainder (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ}
    (ha : ∀ j, 0 < a j) :
    (latticeLaplacian d (L ^ k * m) ν)⁻¹ =
      ∑ j ∈ Finset.range k, fluctTerm k (latticeLaplacian d (L ^ k * m) ν) a j +
        multiscaleRemainder k (latticeLaplacian d (L ^ k * m) ν) a := by
  rw [← fluct_eq_sum_fluctTerm]
  exact laplacian_inv_eq_multiscale k hν ha

/-- `A₀ (P_k A_k⁻¹ P_kᵀ) = Q_{(k)}ᵀ P_kᵀ`. -/
theorem latticeLaplacian_mul_remainder (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ}
    (ha : ∀ j, 0 < a j) :
    latticeLaplacian d (L ^ k * m) ν * multiscaleRemainder k (latticeLaplacian d (L ^ k * m) ν) a =
      (compositeAvg d L m k)ᵀ * (prolong k (latticeLaplacian d (L ^ k * m) ν) a)ᵀ := by
  have hE := laplacian_effOp_posDef (d := d) (L := L) (m := m) k hν ha
  have hEu : (effOp k (latticeLaplacian d (L ^ k * m) ν) a) *
      (effOp k (latticeLaplacian d (L ^ k * m) ν) a)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hE.det_pos.ne')
  unfold multiscaleRemainder
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_prolong k (latticeLaplacian_posDef hν) ha,
    Matrix.mul_assoc _ (effOp k _ a), hEu, Matrix.mul_one]

/-- The sum rule: `A₀ ∑_{j<k} T_j + Q_{(k)}ᵀ P_kᵀ = 1`. -/
theorem sum_rule_matrix (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) :
    latticeLaplacian d (L ^ k * m) ν * fluct k (latticeLaplacian d (L ^ k * m) ν) a +
      (compositeAvg d L m k)ᵀ * (prolong k (latticeLaplacian d (L ^ k * m) ν) a)ᵀ = 1 := by
  have hA : IsUnit (latticeLaplacian d (L ^ k * m) ν).det :=
    isUnit_iff_ne_zero.mpr (latticeLaplacian_posDef hν).det_pos.ne'
  have h1 := latticeLaplacian_mul_remainder (d := d) (L := L) (m := m) k hν ha
  have h2 := laplacian_inv_eq_multiscale (d := d) (L := L) (m := m) k hν ha
  rw [← h1]
  have h3 := Matrix.mul_nonsing_inv _ hA
  rw [← Matrix.mul_add, ← h3, h2]
  rfl

/-- The entries of `Q_{(k)}ᵀ P_kᵀ`: `L^{-kd} P_k(y, u_k(x))`. -/
theorem compositeAvg_transpose_mul_transpose_apply (k : ℕ)
    (P : Matrix (Level d L m k) (Level d L m 0) ℝ) (x y : Level d L m k) :
    ((compositeAvg d L m k)ᵀ * Pᵀ) x y =
      (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * P y (blockMap (L ^ k) (L ^ 0 * m) x) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, compositeAvg_apply]
  rw [Finset.sum_eq_single (blockMap (L ^ k) (L ^ 0 * m) x)]
  · simp only [eq_self, ↓reduceIte]
  · intro u _ hu
    have : ¬ blockMap (L ^ k) (L ^ 0 * m) x = u := fun h => hu h.symm
    simp only [this, ↓reduceIte, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The sum rule in kernel form: for `S = ∑_{j<k} T_j = fluct k A₀ a` and all sites `x, y`,
`((-Δ_x + ν) S)(x, y) = δ_{xy} - L^{-kd} P_k(y, u_k(x))`, where `u_k(x)` is the `L^k`-block of
`x`. -/
theorem sum_rule_apply (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    (x y : Level d L m k) :
    ∑ μ : Fin d,
        (2 * fluct k (latticeLaplacian d (L ^ k * m) ν) a x y -
          fluct k (latticeLaplacian d (L ^ k * m) ν) a (x + Pi.single μ 1) y -
          fluct k (latticeLaplacian d (L ^ k * m) ν) a (x - Pi.single μ 1) y) +
      ν * fluct k (latticeLaplacian d (L ^ k * m) ν) a x y =
    (if x = y then 1 else 0) -
      (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ *
        prolong k (latticeLaplacian d (L ^ k * m) ν) a y (blockMap (L ^ k) (L ^ 0 * m) x) := by
  have h := congrFun (congrFun (sum_rule_matrix (d := d) (L := L) (m := m) k hν ha) x) y
  rw [Matrix.add_apply, compositeAvg_transpose_mul_transpose_apply, Matrix.one_apply] at h
  have h2 : (latticeLaplacian d (L ^ k * m) ν * fluct k (latticeLaplacian d (L ^ k * m) ν) a) x y =
      (latticeLaplacian d (L ^ k * m) ν *ᵥ
        fun z => fluct k (latticeLaplacian d (L ^ k * m) ν) a z y) x := rfl
  rw [h2, latticeLaplacian_mulVec] at h
  linarith

/-- Quantitative form of the sum rule: if the prolongation kernel is bounded by `C`, then
`|((-Δ_x + ν) ∑_{j<k} T_j)(x, y) - δ_{xy}| ≤ C L^{-kd}`. -/
theorem sum_rule_apply_abs_le (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    {C : ℝ} (hC : ∀ y u, |prolong k (latticeLaplacian d (L ^ k * m) ν) a y u| ≤ C)
    (x y : Level d L m k) :
    |(∑ μ : Fin d,
        (2 * fluct k (latticeLaplacian d (L ^ k * m) ν) a x y -
          fluct k (latticeLaplacian d (L ^ k * m) ν) a (x + Pi.single μ 1) y -
          fluct k (latticeLaplacian d (L ^ k * m) ν) a (x - Pi.single μ 1) y) +
      ν * fluct k (latticeLaplacian d (L ^ k * m) ν) a x y) - (if x = y then 1 else 0)| ≤
      C * (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ := by
  rw [sum_rule_apply k hν ha x y, sub_sub_cancel_left, abs_neg, abs_mul,
    abs_of_nonneg (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC _ _) (by positivity)

end Balaban
