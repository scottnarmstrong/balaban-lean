/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTorusClose
public import Balaban.Green.FinalMassGreen
public import Balaban.Green.KF0WalkTorus
public import Balaban.Green.TranslationInvariant

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closeness of the final operator on two tori, uniformly in the scale (W807, blocker 7)

Entries of `finalOp d L m k v a` on two tori `m, m'` at sites of a cube differ by
`C exp(-c (Rm - Rc))` with `C, c` depending on `d, L` only (`finalOp_entry_close_unif`).
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section Woodbury

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem blockProjMatrix_eq_pull_mul_avg :
    blockProjMatrix d ℓ N m = blockPullbackMatrix d ℓ N m * unitBlockAverageMatrix d ℓ N m := by
  ext x x'
  simp only [Matrix.mul_apply, blockProjMatrix, blockPullbackMatrix, unitBlockAverageMatrix]
  by_cases h : blockMap N m x = blockMap N m x'
  · simp [h]
  · simp only [h, ite_false]
    refine (Finset.sum_eq_zero fun y _ => ?_).symm
    by_cases h1 : blockMap N m x = y
    · have : blockMap N m x' ≠ y := fun h2 => h (h1.trans h2.symm)
      simp [this]
    · simp [h1]

theorem avg_eq_smul_pull_transpose :
    unitBlockAverageMatrix d ℓ N m = ((N : ℝ) ^ d)⁻¹ • (blockPullbackMatrix d ℓ N m)ᵀ := by
  ext y x
  simp only [unitBlockAverageMatrix, blockPullbackMatrix, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul]
  split_ifs <;> simp

theorem fineHamiltonian_zero_isUnit (_hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (hN : 0 < N) :
    IsUnit (fineHamiltonian d ℓ N m ν 0) := by
  have hc : 0 < (N : ℝ) ^ 2 := by positivity
  have e : fineHamiltonian d ℓ N m ν 0 = ((N : ℝ) ^ 2) • latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2) := by
    unfold fineHamiltonian; rw [zero_smul, add_zero]
  rw [e]
  have h : (((N : ℝ) ^ 2) • latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2)).PosDef :=
    (latticeLaplacian_posDef (by positivity)).smul hc
  exact (Matrix.isUnit_iff_isUnit_det _).2 h.det_pos.ne'.isUnit

theorem fineHamiltonian_zero_inv_posDef (_hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (hN : 0 < N) :
    ((fineHamiltonian d ℓ N m ν 0)⁻¹).PosDef := by
  have hc : 0 < (N : ℝ) ^ 2 := by positivity
  have e : fineHamiltonian d ℓ N m ν 0 = ((N : ℝ) ^ 2) • latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2) := by
    unfold fineHamiltonian; rw [zero_smul, add_zero]
  rw [e]
  exact ((latticeLaplacian_posDef (by positivity)).smul hc).inv

theorem fineHamiltonian_isUnit (hℓ : ℓ = N * m) (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    (hN : 0 < N) : IsUnit (fineHamiltonian d ℓ N m ν a) := by
  have hc : 0 < (N : ℝ) ^ 2 := by positivity
  rw [fineHamiltonian_eq hN]
  have h := (blockHamiltonian_posDef hℓ hN hd (ν := ν / (N : ℝ) ^ 2) (a := a / (N : ℝ) ^ 2)
    (by positivity) (by positivity)).smul hc
  exact (Matrix.isUnit_iff_isUnit_det _).2 h.det_pos.ne'.isUnit

/-- **Woodbury identity** for the final operator: with `X = H₀⁻¹`, `Y = H⁻¹`,
`(1 + a Q X Q*) (1 - a Q Y Q*) = 1`. -/
theorem woodbury_final (hℓ : ℓ = N * m) (hd : 0 < d) {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a)
    (hN : 0 < N) :
    ((1 : Matrix (Torus d m) (Torus d m) ℝ) + a • (unitBlockAverageMatrix d ℓ N m *
        (fineHamiltonian d ℓ N m ν 0)⁻¹ * blockPullbackMatrix d ℓ N m)) *
      (1 - a • (unitBlockAverageMatrix d ℓ N m * (fineHamiltonian d ℓ N m ν a)⁻¹ *
        blockPullbackMatrix d ℓ N m)) = 1 := by
  set Q := unitBlockAverageMatrix d ℓ N m with hQ
  set Qs := blockPullbackMatrix d ℓ N m with hQs
  set X := (fineHamiltonian d ℓ N m ν 0)⁻¹ with hX
  set Y := (fineHamiltonian d ℓ N m ν a)⁻¹ with hY
  have hU0 := fineHamiltonian_zero_isUnit (d := d) (ℓ := ℓ) (N := N) (m := m) hd hν hN
  have hU := fineHamiltonian_isUnit (d := d) hℓ hd hν.le ha hN
  have hXH : X * fineHamiltonian d ℓ N m ν 0 = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hU0)
  have hHY : fineHamiltonian d ℓ N m ν a * Y = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  have hH : fineHamiltonian d ℓ N m ν a = fineHamiltonian d ℓ N m ν 0 + a • (Qs * Q) := by
    unfold fineHamiltonian
    rw [zero_smul, add_zero, add_comm]
    simp only [← blockProjMatrix_eq_pull_mul_avg, hQ, hQs]
    abel_nf
  have hXY : X - Y = a • (X * (Qs * Q) * Y) := by
    have : X * fineHamiltonian d ℓ N m ν a * Y =
        X * fineHamiltonian d ℓ N m ν 0 * Y + a • (X * (Qs * Q) * Y) := by
      rw [hH]; simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [Matrix.mul_assoc, hHY, Matrix.mul_one, hXH, Matrix.one_mul] at this
    exact sub_eq_iff_eq_add'.2 this
  have key : Q * (X - Y - a • (X * (Qs * Q) * Y)) * Qs = 0 := by
    rw [hXY, sub_self, Matrix.mul_zero, Matrix.zero_mul]
  have e : ((1 : Matrix (Torus d m) (Torus d m) ℝ) + a • (Q * X * Qs)) * (1 - a • (Q * Y * Qs)) =
      1 + a • (Q * (X - Y - a • (X * (Qs * Q) * Y)) * Qs) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_sub, smul_add, smul_smul,
      Matrix.mul_assoc]
    abel
  rw [e, key, smul_zero, add_zero]

/-- The matrix `1 + a Q X Q*` is coercive with constant `1`. -/
theorem psi_coercive (hd : 0 < d) {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a) (hN : 0 < N)
    (φ : Torus d m → ℝ) :
    ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ ((1 : Matrix (Torus d m) (Torus d m) ℝ) + a • (unitBlockAverageMatrix d ℓ N m *
        (fineHamiltonian d ℓ N m ν 0)⁻¹ * blockPullbackMatrix d ℓ N m)) *ᵥ φ := by
  have hX := (fineHamiltonian_zero_inv_posDef (d := d) (ℓ := ℓ) (N := N) (m := m) hd hν hN).posSemidef
  have h1 := hX.dotProduct_mulVec_nonneg (blockPullbackMatrix d ℓ N m *ᵥ φ)
  simp only [star_trivial] at h1
  have e : φ ⬝ᵥ (unitBlockAverageMatrix d ℓ N m * (fineHamiltonian d ℓ N m ν 0)⁻¹ *
      blockPullbackMatrix d ℓ N m) *ᵥ φ = ((N : ℝ) ^ d)⁻¹ *
      ((blockPullbackMatrix d ℓ N m *ᵥ φ) ⬝ᵥ (fineHamiltonian d ℓ N m ν 0)⁻¹ *ᵥ
        (blockPullbackMatrix d ℓ N m *ᵥ φ)) := by
    rw [avg_eq_smul_pull_transpose, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, ← Matrix.mulVec_mulVec]
  rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, e, Matrix.one_mulVec,
    smul_eq_mul]
  have : ∑ x, φ x ^ 2 = φ ⬝ᵥ φ := by simp [dotProduct, sq]
  rw [this]
  have h2 : 0 ≤ ((N : ℝ) ^ d)⁻¹ := by positivity
  nlinarith [mul_nonneg ha.le (mul_nonneg h2 h1)]

theorem unitOperator_eq_smul_inv_psi (hℓ : ℓ = N * m) (hd : 0 < d) {ν a : ℝ} (hν : 0 < ν)
    (ha : 0 < a) (hN : 0 < N) :
    unconstrainedUnitOperator d ℓ N m ν a =
      a • ((1 : Matrix (Torus d m) (Torus d m) ℝ) + a • (unitBlockAverageMatrix d ℓ N m *
        (fineHamiltonian d ℓ N m ν 0)⁻¹ * blockPullbackMatrix d ℓ N m))⁻¹ := by
  have hW := woodbury_final (d := d) hℓ hd hν ha hN
  rw [Matrix.inv_eq_right_inv hW]
  unfold unconstrainedUnitOperator
  rw [smul_sub, smul_smul, pow_two]

end Woodbury

section PsiDecay

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- Entry decay of `Ψ = 1 + a Q X Q*` (it is `a U⁻¹`), uniformly in `k ≥ 1`. -/
theorem psi_entry_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (x y : Torus d N₀) :
    |((1 : Matrix (Torus d N₀) (Torus d N₀) ℝ) + a • (unitBlockAverageMatrix d (N₀ * L ^ k) (L ^ k) N₀ *
        (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ v 0)⁻¹ *
        blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) N₀)) x y| ≤
      4 / finalGap d L * Real.exp (-finalRate d L * torusDist d N₀ x y) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hg := finalGap_pos (d := d) hL
  have hL2 : (0 : ℝ) < ((L : ℝ) ^ 2)⁻¹ := by positivity
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hmass.le
  have ha : 0 < a := by linarith
  set Ψ := ((1 : Matrix (Torus d N₀) (Torus d N₀) ℝ) + a • (unitBlockAverageMatrix d (N₀ * L ^ k) (L ^ k) N₀ *
        (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ v 0)⁻¹ *
        blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) N₀)) with hΨ
  have hW := woodbury_final (d := d) (ℓ := N₀ * L ^ k) (N := L ^ k) (m := N₀) (mul_comm _ _) hd hv ha hN
  have hU := unitOperator_eq_smul_inv_psi (d := d) (ℓ := N₀ * L ^ k) (N := L ^ k) (m := N₀)
    (mul_comm _ _) hd hv ha hN
  have hΞ : Ψ⁻¹ * Ψ = 1 := by
    rw [Matrix.inv_eq_right_inv hW]
    exact mul_eq_one_comm.1 hW
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ,
      Z = (a⁻¹ • Ψ).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hprod : finalOp d L N₀ k v a * Z = 1 := by
    rw [hZ]
    unfold finalOp
    rw [hU]
    show ((a • Ψ⁻¹).map (algebraMap ℝ ℂ)) * ((a⁻¹ • Ψ).map (algebraMap ℝ ℂ)) = 1
    rw [← Matrix.map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha.ne',
      one_smul, hΞ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv := Matrix.inv_eq_right_inv hprod
  have h := finalMass_inverse_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass x y
  rw [hinv, hZ] at h
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.coe_algebraMap,
    Complex.norm_real, Real.norm_eq_abs] at h
  have e : dist (show L1Torus d N₀ from x) (show L1Torus d N₀ from y) = torusDist d N₀ x y := rfl
  rw [e, abs_mul, abs_of_pos (inv_pos.2 ha)] at h
  have h2 : |Ψ x y| ≤ a * (2 / finalGap d L * Real.exp (-finalRate d L * torusDist d N₀ x y)) := by
    have := mul_le_mul_of_nonneg_left h ha.le
    rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at this
  refine h2.trans ?_
  have hE : 0 ≤ 2 / finalGap d L * Real.exp (-finalRate d L * torusDist d N₀ x y) := by positivity
  calc a * (2 / finalGap d L * Real.exp (-finalRate d L * torusDist d N₀ x y))
      ≤ 2 * (2 / finalGap d L * Real.exp (-finalRate d L * torusDist d N₀ x y)) :=
        mul_le_mul_of_nonneg_right ha2 hE
    _ = _ := by ring

end PsiDecay

section Walks

variable {d : ℕ}

theorem step_exp_sum (l : ℝ) (μ₀ : Fin d) :
    ∑ s : Fin d × Bool, Real.exp (l * ((stepVec d s μ₀ : ℤ) : ℝ)) =
      2 * (d : ℝ) - 2 + Real.exp l + Real.exp (-l) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  have h1 : ∀ μ : Fin d, Real.exp (l * ((stepVec d (μ, true) μ₀ : ℤ) : ℝ)) +
      Real.exp (l * ((stepVec d (μ, false) μ₀ : ℤ) : ℝ)) =
      2 + (if μ = μ₀ then Real.exp l + Real.exp (-l) - 2 else 0) := by
    intro μ
    by_cases h : μ = μ₀
    · subst h; simp [stepVec]
    · simp [stepVec, h, Ne.symm h]; norm_num
  rw [Finset.sum_congr rfl fun μ _ => h1 μ, Finset.sum_add_distrib, Finset.sum_ite_eq' ]
  simp only [Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem exp_moment_stepSum (n : ℕ) (l : ℝ) (μ₀ : Fin d) :
    ∑ w : Fin n → Fin d × Bool, Real.exp (l * ((stepSum w μ₀ : ℤ) : ℝ)) =
      (2 * (d : ℝ) - 2 + Real.exp l + Real.exp (-l)) ^ n := by
  rw [← step_exp_sum l μ₀, Finset.sum_pow' Finset.univ, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Real.exp_sum]
  congr 1
  unfold stepSum
  rw [Finset.sum_apply]
  push_cast
  rw [Finset.mul_sum]

/-- Chernoff bound for the number of walks of length `n` whose endpoint has a coordinate of
size at least `D`. -/
theorem sum_bad_walks_le (n : ℕ) {l : ℝ} (hl : 0 ≤ l) (D : ℝ) :
    ∑ w : Fin n → Fin d × Bool, (if ∃ μ, D ≤ |((stepSum w μ : ℤ) : ℝ)| then (1 : ℝ) else 0) ≤
      2 * (d : ℝ) * Real.exp (-l * D) * (2 * (d : ℝ) - 2 + Real.exp l + Real.exp (-l)) ^ n := by
  have hpt : ∀ w : Fin n → Fin d × Bool,
      (if ∃ μ, D ≤ |((stepSum w μ : ℤ) : ℝ)| then (1 : ℝ) else 0) ≤
        ∑ μ : Fin d, Real.exp (-l * D) *
          (Real.exp (l * ((stepSum w μ : ℤ) : ℝ)) + Real.exp (-l * ((stepSum w μ : ℤ) : ℝ))) := by
    intro w
    have hnn : ∀ μ : Fin d, 0 ≤ Real.exp (-l * D) *
        (Real.exp (l * ((stepSum w μ : ℤ) : ℝ)) + Real.exp (-l * ((stepSum w μ : ℤ) : ℝ))) :=
      fun μ => by positivity
    split_ifs with h
    · obtain ⟨μ, hμ⟩ := h
      refine le_trans ?_ (Finset.single_le_sum (f := fun μ : Fin d => Real.exp (-l * D) *
        (Real.exp (l * ((stepSum w μ : ℤ) : ℝ)) + Real.exp (-l * ((stepSum w μ : ℤ) : ℝ))))
        (fun μ _ => hnn μ) (Finset.mem_univ μ))
      rcases le_abs'.1 hμ with h1 | h1
      · have : Real.exp (-l * D) * Real.exp (-l * ((stepSum w μ : ℤ) : ℝ)) ≥ 1 := by
          rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
        nlinarith [Real.exp_pos (-l * D), Real.exp_pos (l * ((stepSum w μ : ℤ) : ℝ))]
      · have : Real.exp (-l * D) * Real.exp (l * ((stepSum w μ : ℤ) : ℝ)) ≥ 1 := by
          rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith
        nlinarith [Real.exp_pos (-l * D), Real.exp_pos (-l * ((stepSum w μ : ℤ) : ℝ))]
    · exact Finset.sum_nonneg fun μ _ => hnn μ
  refine (Finset.sum_le_sum fun w _ => hpt w).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  have : ∀ μ : Fin d, ∑ w : Fin n → Fin d × Bool, Real.exp (-l * D) *
      (Real.exp (l * ((stepSum w μ : ℤ) : ℝ)) + Real.exp (-l * ((stepSum w μ : ℤ) : ℝ))) =
      2 * (Real.exp (-l * D) * (2 * (d : ℝ) - 2 + Real.exp l + Real.exp (-l)) ^ n) := by
    intro μ
    simp_rw [← Finset.mul_sum, Finset.sum_add_distrib]
    rw [exp_moment_stepSum n l μ]
    have h2 := exp_moment_stepSum n (-l) μ
    simp only [neg_mul] at h2 ⊢
    rw [h2, neg_neg]
    have e : 2 * (d : ℝ) - 2 + Real.exp (-l) + Real.exp l =
        2 * (d : ℝ) - 2 + Real.exp l + Real.exp (-l) := by ring
    rw [e]; ring
  rw [Finset.sum_congr rfl fun μ _ => this μ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem castTorus_add_intToTorus (s : ℕ) [NeZero s] (u v : Fin d → ℤ) :
    castTorus s u + intToTorus d s v = castTorus s (u + v) := by
  funext μ
  simp [castTorus, intToTorus_apply]

/-- A walk whose endpoint has all coordinates of size `< D`, between points at distance `≤ B`
on a torus of side `ℓ ≥ B + D`, ends at the target on the torus iff it does so in `ℤ^d`. -/
theorem walk_end_iff {ℓ : ℕ} [NeZero ℓ] {B D : ℕ} (hBD : B + D ≤ ℓ) {u u' : Fin d → ℤ}
    (hB : ∀ μ, |u' μ - u μ| ≤ B) {n : ℕ} (w : Fin n → Fin d × Bool)
    (hw : ∀ μ, |stepSum w μ| < D) :
    castTorus ℓ u + intToTorus d ℓ (stepSum w) = castTorus ℓ u' ↔ stepSum w = u' - u := by
  rw [castTorus_add_intToTorus]
  have hlt : ∀ μ, |(u + stepSum w) μ - u' μ| < ℓ := by
    intro μ
    have h1 := hB μ
    have h2 := hw μ
    have h3 : ((B + D : ℕ) : ℤ) ≤ ℓ := by exact_mod_cast hBD
    push_cast at h3
    simp only [Pi.add_apply]
    rw [abs_lt] at h2 ⊢
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [castTorus_eq_iff hlt]
  constructor
  · intro h; rw [← h]; ext μ; simp
  · intro h; rw [h]; ext μ; simp

theorem walk_indicator_diff_le {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] {B D : ℕ} (hBD : B + D ≤ ℓ)
    (hBD' : B + D ≤ ℓ') {u : Fin d → ℤ} {S : Finset (Fin d → ℤ)}
    (hS : ∀ u' ∈ S, ∀ μ, |u' μ - u μ| ≤ B) (hinj : Set.InjOn (castTorus (d := d) ℓ) S)
    (hinj' : Set.InjOn (castTorus (d := d) ℓ') S) {n : ℕ} (w : Fin n → Fin d × Bool) :
    ∑ u' ∈ S, |(if castTorus ℓ u + intToTorus d ℓ (stepSum w) = castTorus ℓ u' then (1 : ℝ)
          else 0) -
        (if castTorus ℓ' u + intToTorus d ℓ' (stepSum w) = castTorus ℓ' u' then (1 : ℝ) else 0)| ≤
      2 * (if ∃ μ, (D : ℝ) ≤ |((stepSum w μ : ℤ) : ℝ)| then (1 : ℝ) else 0) := by
  by_cases hb : ∃ μ, (D : ℝ) ≤ |((stepSum w μ : ℤ) : ℝ)|
  · simp only [hb, ↓reduceIte]
    have hle : ∀ (s : ℕ) [NeZero s], Set.InjOn (castTorus (d := d) s) S →
        ∑ u' ∈ S, (if castTorus s u + intToTorus d s (stepSum w) = castTorus s u' then (1 : ℝ)
          else 0) ≤ 1 := by
      intro s _ hi
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have : (S.filter fun u' => castTorus s u + intToTorus d s (stepSum w) = castTorus s u').card
          ≤ 1 := by
        refine Finset.card_le_one.2 fun a ha b hb' => ?_
        rw [Finset.mem_filter] at ha hb'
        exact hi ha.1 hb'.1 (ha.2.symm.trans hb'.2)
      exact_mod_cast this
    have h1 := hle ℓ hinj
    have h2 := hle ℓ' hinj'
    calc _ ≤ ∑ u' ∈ S, ((if castTorus ℓ u + intToTorus d ℓ (stepSum w) = castTorus ℓ u' then
            (1 : ℝ) else 0) + (if castTorus ℓ' u + intToTorus d ℓ' (stepSum w) =
              castTorus ℓ' u' then (1 : ℝ) else 0)) := by
          refine Finset.sum_le_sum fun u' _ => ?_
          split_ifs <;> simp
      _ ≤ 2 * 1 := by rw [Finset.sum_add_distrib]; linarith
  · simp only [hb, ↓reduceIte, mul_zero]
    push Not at hb
    have hw : ∀ μ, |stepSum w μ| < D := by
      intro μ
      have := hb μ
      have h3 : ((|stepSum w μ| : ℤ) : ℝ) < (D : ℝ) := by simpa using this
      exact_mod_cast h3
    refine le_of_eq (Finset.sum_eq_zero fun u' hu' => ?_)
    simp only [walk_end_iff hBD (hS u' hu') w hw, walk_end_iff hBD' (hS u' hu') w hw, sub_self,
      abs_zero]

theorem exp_add_exp_neg_sub_two_le {l : ℝ} (hl : |l| ≤ 1 / 2) :
    Real.exp l + Real.exp (-l) - 2 ≤ 8 / 7 * l ^ 2 := by
  have h1 := Real.cosh_le_exp_half_sq l
  rw [Real.cosh_eq] at h1
  set x := l ^ 2 / 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 8 := by
    have : l ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg l, sq_abs l]
    rw [hx]; linarith
  have h2 : Real.exp x - 1 ≤ x * Real.exp x := by
    have a1 := Real.add_one_le_exp (-x)
    have a2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have a3 := Real.exp_pos x
    nlinarith
  have h3 : Real.exp x ≤ 8 / 7 := by
    rcases hx0.eq_or_lt with h | h
    · rw [← h]; simp; norm_num
    · have := Real.exp_bound_div_one_sub_of_interval' h (by linarith)
      refine this.le.trans ?_
      rw [div_le_iff₀ (by linarith)]; linarith
  nlinarith [Real.exp_pos x]

end Walks

section Green0

variable {d : ℕ}

theorem X_entry_hasSum {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] {ν : ℝ} (hν : 0 < ν) (hN : 0 < N)
    (x y : Torus d ℓ) :
    HasSum (fun n : ℕ => ((N : ℝ) ^ 2)⁻¹ * (((2 * (d : ℝ) + ν / (N : ℝ) ^ 2) ^ (n + 1))⁻¹ *
        ∑ w : Fin n → Fin d × Bool,
          if x + intToTorus d ℓ (stepSum w) = y then (1 : ℝ) else 0))
      ((fineHamiltonian d ℓ N m ν 0)⁻¹ x y) := by
  have hc : 0 < (N : ℝ) ^ 2 := by positivity
  have hν' : 0 < ν / (N : ℝ) ^ 2 := by positivity
  have hdet : IsUnit (latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2)).det :=
    (latticeLaplacian_posDef hν').det_pos.ne'.isUnit
  have e : fineHamiltonian d ℓ N m ν 0 = ((N : ℝ) ^ 2) • latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2) := by
    unfold fineHamiltonian; rw [zero_smul, add_zero]
  have hinv : (fineHamiltonian d ℓ N m ν 0)⁻¹ =
      ((N : ℝ) ^ 2)⁻¹ • (latticeLaplacian d ℓ (ν / (N : ℝ) ^ 2))⁻¹ := by
    rw [e]
    have : Invertible ((N : ℝ) ^ 2) := invertibleOfNonzero hc.ne'
    rw [Matrix.inv_smul (k := (N : ℝ) ^ 2) (h := hdet), invOf_eq_inv]
  have hs := kf0_neumann_hasSum (d := d) (m := ℓ) hν' (le_refl (0 : ℝ)) x y
  simp only [zero_smul, add_zero] at hs
  have hs2 := hs.mul_left (((N : ℝ) ^ 2)⁻¹)
  rw [hinv, Matrix.smul_apply, smul_eq_mul]
  convert hs2 using 1
  ext n
  rw [kf0Adj_pow_eq_count]

/-- **Two-torus agreement of the massive Green function, summed over a block.**  For `u` and a
set `S` of sites within distance `B` of `u`, injective under the casts to both tori, the
block sums of the entries of `(N² (-Δ) + ν)⁻¹` on tori of sides `ℓ, ℓ' ≥ B + D` differ by at most
`6 d / ν · exp(-(√ν/(2N)) D)`. -/
theorem X_sum_close {ℓ ℓ' N m m' : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero m] [NeZero m'] {ν : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hN : 0 < N) {B D : ℕ} (hBD : B + D ≤ ℓ) (hBD' : B + D ≤ ℓ')
    {u : Fin d → ℤ} {S : Finset (Fin d → ℤ)} (hS : ∀ u' ∈ S, ∀ μ, |u' μ - u μ| ≤ B)
    (hinj : Set.InjOn (castTorus (d := d) ℓ) S) (hinj' : Set.InjOn (castTorus (d := d) ℓ') S) :
    |∑ u' ∈ S, ((fineHamiltonian d ℓ N m ν 0)⁻¹ (castTorus ℓ u) (castTorus ℓ u') -
        (fineHamiltonian d ℓ' N m' ν 0)⁻¹ (castTorus ℓ' u) (castTorus ℓ' u'))| ≤
      6 * d / ν * Real.exp (-(Real.sqrt ν / (2 * N)) * D) := by
  have hNr : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set l : ℝ := Real.sqrt ν / (2 * N) with hl
  have hsq : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have hsq1 : Real.sqrt ν ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hν1
  have hl0 : 0 ≤ l := by positivity
  have hl2 : l ^ 2 = ν / (4 * (N : ℝ) ^ 2) := by
    rw [hl, div_pow, hsq]; ring
  have hlhalf : |l| ≤ 1 / 2 := by
    rw [abs_of_nonneg hl0, hl, div_le_iff₀ (by positivity)]
    nlinarith [Real.sqrt_nonneg ν]
  have hcosh := exp_add_exp_neg_sub_two_le hlhalf
  have hge : 2 ≤ Real.exp l + Real.exp (-l) := by
    have := Real.add_one_le_exp l
    have h2 := Real.add_one_le_exp (-l)
    nlinarith [Real.exp_pos l, Real.exp_pos (-l), Real.exp_add l (-l), sq_nonneg (Real.exp l - Real.exp (-l))]
  set b : ℝ := 2 * (d : ℝ) + ν / (N : ℝ) ^ 2 with hb
  set r : ℝ := 2 * (d : ℝ) - 2 + Real.exp l + Real.exp (-l) with hr
  have hb0 : 0 < b := by rw [hb]; positivity
  have hrle : N ^ 2 * (Real.exp l + Real.exp (-l) - 2) ≤ 2 * ν / 7 := by
    have : (N : ℝ) ^ 2 * (8 / 7 * l ^ 2) = 2 * ν / 7 := by rw [hl2]; field_simp; ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hcosh hN2.le
  have hbr : (5 / 7) * ν ≤ (N : ℝ) ^ 2 * (b - r) := by
    have : (N : ℝ) ^ 2 * (b - r) = ν - (N : ℝ) ^ 2 * (Real.exp l + Real.exp (-l) - 2) := by
      rw [hb, hr]; field_simp; ring
    rw [this]; linarith
  have hbr0 : 0 < b - r := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hN2.le h]
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  set q : ℝ := r / b with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hb0]; linarith
  set K : ℝ := ((N : ℝ) ^ 2)⁻¹ * b⁻¹ * (4 * d * Real.exp (-l * D)) with hK
  have hg : HasSum (fun n : ℕ => ((N : ℝ) ^ 2)⁻¹ * ((b ^ (n + 1))⁻¹ *
      (2 * (2 * (d : ℝ) * Real.exp (-l * D) * r ^ n)))) (K * (1 - q)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left K
    convert this using 1
    ext n
    rw [hK, hq, div_pow, pow_succ]
    field_simp
    ring
  set f1 : ∀ n : ℕ, (Fin n → Fin d × Bool) → (Fin d → ℤ) → ℝ := fun n w u' =>
    if castTorus ℓ u + intToTorus d ℓ (stepSum w) = castTorus ℓ u' then 1 else 0 with hf1
  set f2 : ∀ n : ℕ, (Fin n → Fin d × Bool) → (Fin d → ℤ) → ℝ := fun n w u' =>
    if castTorus ℓ' u + intToTorus d ℓ' (stepSum w) = castTorus ℓ' u' then 1 else 0 with hf2
  set c : ℕ → ℝ := fun n => ((N : ℝ) ^ 2)⁻¹ * (b ^ (n + 1))⁻¹ with hc
  have hs1 : ∀ u' : Fin d → ℤ, HasSum (fun n : ℕ => c n * ∑ w, f1 n w u')
      ((fineHamiltonian d ℓ N m ν 0)⁻¹ (castTorus ℓ u) (castTorus ℓ u')) := by
    intro u'
    have := X_entry_hasSum (d := d) (ℓ := ℓ) (N := N) (m := m) hν hN (castTorus ℓ u)
      (castTorus ℓ u')
    convert this using 2 with n
    simp only [hc, hf1]; ring
  have hs2 : ∀ u' : Fin d → ℤ, HasSum (fun n : ℕ => c n * ∑ w, f2 n w u')
      ((fineHamiltonian d ℓ' N m' ν 0)⁻¹ (castTorus ℓ' u) (castTorus ℓ' u')) := by
    intro u'
    have := X_entry_hasSum (d := d) (ℓ := ℓ') (N := N) (m := m') hν hN (castTorus ℓ' u)
      (castTorus ℓ' u')
    convert this using 2 with n
    simp only [hc, hf2]; ring
  have hdiff := hasSum_sum (s := S) fun u' _ => (hs1 u').sub (hs2 u')
  have hbound : ∀ n : ℕ, ‖∑ u' ∈ S, (c n * ∑ w, f1 n w u' - c n * ∑ w, f2 n w u')‖ ≤
      ((N : ℝ) ^ 2)⁻¹ * ((b ^ (n + 1))⁻¹ * (2 * (2 * (d : ℝ) * Real.exp (-l * D) * r ^ n))) := by
    intro n
    have hc0 : 0 ≤ c n := by positivity
    have e : ∑ u' ∈ S, (c n * ∑ w, f1 n w u' - c n * ∑ w, f2 n w u') =
        c n * ∑ w : Fin n → Fin d × Bool, ∑ u' ∈ S, (f1 n w u' - f2 n w u') := by
      calc ∑ u' ∈ S, (c n * ∑ w, f1 n w u' - c n * ∑ w, f2 n w u')
          = ∑ u' ∈ S, c n * ∑ w : Fin n → Fin d × Bool, (f1 n w u' - f2 n w u') :=
            Finset.sum_congr rfl fun u' _ => by rw [← mul_sub, ← Finset.sum_sub_distrib]
        _ = c n * ∑ u' ∈ S, ∑ w : Fin n → Fin d × Bool, (f1 n w u' - f2 n w u') :=
            (Finset.mul_sum _ _ _).symm
        _ = _ := by rw [Finset.sum_comm]
    rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
    have h1 : |∑ w : Fin n → Fin d × Bool, ∑ u' ∈ S, (f1 n w u' - f2 n w u')| ≤
        ∑ w : Fin n → Fin d × Bool, 2 * (if ∃ μ, (D : ℝ) ≤ |((stepSum w μ : ℤ) : ℝ)| then (1 : ℝ)
          else 0) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact walk_indicator_diff_le hBD hBD' hS hinj hinj' w
    have h2 := sum_bad_walks_le (d := d) n hl0 D
    rw [← Finset.mul_sum] at h1
    calc c n * |∑ w : Fin n → Fin d × Bool, ∑ u' ∈ S, (f1 n w u' - f2 n w u')|
        ≤ c n * (2 * (2 * (d : ℝ) * Real.exp (-l * D) * r ^ n)) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hc0
          linarith
      _ = _ := by simp only [hc]; ring
  have hnorm := tsum_of_norm_bounded hg hbound
  have htsum := hdiff.tsum_eq
  rw [htsum] at hnorm
  have hE : 0 ≤ Real.exp (-l * D) := (Real.exp_pos _).le
  have e1 : K * (1 - q)⁻¹ = 4 * d * Real.exp (-l * D) / ((N : ℝ) ^ 2 * (b - r)) := by
    have hb' : b ≠ 0 := hb0.ne'
    have hbr' : b - r ≠ 0 := hbr0.ne'
    rw [hK, hq]
    have : 1 - r / b = (b - r) / b := by field_simp
    rw [this]
    field_simp
  have e2 : 4 * d * Real.exp (-l * D) / ((N : ℝ) ^ 2 * (b - r)) ≤
      6 * d / ν * Real.exp (-l * D) := by
    rw [div_le_iff₀ (by positivity)]
    have h5 : (5 / 7) * ν ≤ (N : ℝ) ^ 2 * (b - r) := hbr
    have : 6 * d / ν * Real.exp (-l * D) * ((N : ℝ) ^ 2 * (b - r)) ≥
        6 * d / ν * Real.exp (-l * D) * ((5 / 7) * ν) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h6 : 6 * (d : ℝ) / ν * Real.exp (-l * D) * ((5 / 7) * ν) =
        30 / 7 * d * Real.exp (-l * D) := by field_simp; ring
    have h7 : (0 : ℝ) ≤ d * Real.exp (-l * D) := mul_nonneg hd0 hE
    nlinarith
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm.trans (e1.le.trans e2)

theorem avg_mul_pull_castTorus {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (M : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) (y y' : Fin d → ℤ) :
    (unitBlockAverageMatrix d ℓ N m * M * blockPullbackMatrix d ℓ N m) (castTorus m y)
        (castTorus m y') =
      ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ intFibre N y, ∑ x'' ∈ intFibre N y',
        M (castTorus ℓ x) (castTorus ℓ x'') := by
  have h1 : (unitBlockAverageMatrix d ℓ N m * M * blockPullbackMatrix d ℓ N m) (castTorus m y)
      (castTorus m y') = ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m (castTorus m y),
        (M * blockPullbackMatrix d ℓ N m) x (castTorus m y') := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [unitBlockAverageMatrix, ite_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    congr 2
  rw [h1, sum_blockFibre_castTorus hℓ hN y]
  congr 1
  exact Finset.sum_congr rfl fun x _ => mul_blockPullbackMatrix_castTorus hℓ hN M _ y'

/-- **Two-torus agreement of `Ψ = 1 + a Q X Q*`** at sites of a cube, with the constant `6 d a / ν`
independent of the block side `N`. -/
theorem psi_entry_close {N m m' R Rm : ℕ} [NeZero m] [NeZero m'] [NeZero N] {ν a : ℝ}
    (hν : 0 < ν) (hν1 : ν ≤ 1) (ha : 0 ≤ a) (hm : 2 * Rm + 1 < m) (hm' : 2 * Rm + 1 < m')
    (hR : R ≤ Rm) {y y' : Fin d → ℤ} (hy : y ∈ sqBox d R) (hy' : y' ∈ sqBox d R) :
    |((1 : Matrix (Torus d m) (Torus d m) ℝ) + a • (unitBlockAverageMatrix d (m * N) N m *
          (fineHamiltonian d (m * N) N m ν 0)⁻¹ * blockPullbackMatrix d (m * N) N m))
          (castTorus m y) (castTorus m y') -
      ((1 : Matrix (Torus d m') (Torus d m') ℝ) + a • (unitBlockAverageMatrix d (m' * N) N m' *
          (fineHamiltonian d (m' * N) N m' ν 0)⁻¹ * blockPullbackMatrix d (m' * N) N m'))
          (castTorus m' y) (castTorus m' y')| ≤
      a * (6 * d / ν) * Real.exp (-Real.sqrt ν * ((Rm : ℝ) - R)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmpos' : 0 < m' := Nat.pos_of_ne_zero (NeZero.ne m')
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc2 : ∀ {s : ℕ}, 2 * Rm + 1 < s → ∀ μ, |y μ - y' μ| < s := by
    intro s hs μ
    have h1 := abs_le.1 (mem_sqBox.1 hy μ)
    have h2 := abs_le.1 (mem_sqBox.1 hy' μ)
    have h5 : ((2 * Rm + 1 : ℕ) : ℤ) < s := by exact_mod_cast hs
    have h6 : (R : ℤ) ≤ Rm := by exact_mod_cast hR
    push_cast at h5
    rw [abs_lt]; constructor <;> linarith
  have hind : (castTorus m y = castTorus m y') ↔ (castTorus m' y = castTorus m' y') := by
    rw [castTorus_eq_iff (hc2 hm), castTorus_eq_iff (hc2 hm')]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hind]
  rw [avg_mul_pull_castTorus (mul_comm m N) hN, avg_mul_pull_castTorus (mul_comm m' N) hN]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hR
  set F := intFibre N y with hF
  set F' := intFibre N y' with hF'
  have hB : ∀ u ∈ F, ∀ u' ∈ F', ∀ μ, |u' μ - u μ| ≤ ((2 * N * (R + 1) : ℕ) : ℤ) := by
    intro u hu u' hu' μ
    have h1 := mem_sqBox.1 (intFibre_subset_sqBox (N := N) hy hu) μ
    have h2 := mem_sqBox.1 (intFibre_subset_sqBox (N := N) hy' hu') μ
    have := abs_sub (u' μ) (u μ)
    push_cast at h1 h2 ⊢
    nlinarith
  have hBD : ∀ {s : ℕ}, 2 * (R + t) + 1 < s → 2 * N * (R + 1) + 2 * N * t ≤ s * N := by
    intro s hs
    have h2 : 2 * (R + t + 1) ≤ s := by omega
    nlinarith
  have hsum : ∀ u ∈ F, |∑ u' ∈ F', ((fineHamiltonian d (m * N) N m ν 0)⁻¹ (castTorus (m * N) u)
        (castTorus (m * N) u') - (fineHamiltonian d (m' * N) N m' ν 0)⁻¹ (castTorus (m' * N) u)
        (castTorus (m' * N) u'))| ≤
      6 * d / ν * Real.exp (-Real.sqrt ν * ((t : ℝ))) := by
    intro u hu
    have hX := X_sum_close (d := d) (ℓ := m * N) (ℓ' := m' * N) (N := N) (m := m) (m' := m')
      hν hν1 hN (B := 2 * N * (R + 1)) (D := 2 * N * t) (hBD hm) (hBD hm') (u := u) (S := F')
      (hB u hu) (castTorus_injOn (mul_comm m N) hmpos y') (castTorus_injOn (mul_comm m' N) hmpos' y')
    refine hX.trans (le_of_eq ?_)
    congr 2
    push_cast
    field_simp
  set X1 := fun x x'' : Fin d → ℤ => (fineHamiltonian d (m * N) N m ν 0)⁻¹ (castTorus (m * N) x)
    (castTorus (m * N) x'') with hX1
  set X2 := fun x x'' : Fin d → ℤ => (fineHamiltonian d (m' * N) N m' ν 0)⁻¹ (castTorus (m' * N) x)
    (castTorus (m' * N) x'') with hX2
  have hNd : (0 : ℝ) < ((N : ℝ) ^ d)⁻¹ := by positivity
  have e : ((if castTorus m' y = castTorus m' y' then (1 : ℝ) else 0) +
          a * (((N : ℝ) ^ d)⁻¹ * ∑ x ∈ F, ∑ x'' ∈ F', X1 x x'')) -
        ((if castTorus m' y = castTorus m' y' then (1 : ℝ) else 0) +
          a * (((N : ℝ) ^ d)⁻¹ * ∑ x ∈ F, ∑ x'' ∈ F', X2 x x'')) =
      a * (((N : ℝ) ^ d)⁻¹ * ∑ x ∈ F, ∑ x'' ∈ F', (X1 x x'' - X2 x x'')) := by
    simp only [Finset.sum_sub_distrib]; ring
  rw [e, abs_mul, abs_of_nonneg ha, abs_mul, abs_of_pos hNd]
  have hs : |∑ x ∈ F, ∑ x'' ∈ F', (X1 x x'' - X2 x x'')| ≤
      (N : ℝ) ^ d * (6 * d / ν * Real.exp (-Real.sqrt ν * ((t : ℝ)))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ F, |∑ x'' ∈ F', (X1 x x'' - X2 x x'')| ≤
          ∑ _x ∈ F, 6 * d / ν * Real.exp (-Real.sqrt ν * ((t : ℝ))) :=
          Finset.sum_le_sum fun x hx => hsum x hx
      _ = (N : ℝ) ^ d * (6 * d / ν * Real.exp (-Real.sqrt ν * ((t : ℝ)))) := by
          rw [Finset.sum_const, hF, card_intFibre, nsmul_eq_mul]; push_cast; ring
  have hcast : ((R + t : ℕ) : ℝ) - R = t := by push_cast; ring
  rw [hcast]
  calc a * (((N : ℝ) ^ d)⁻¹ * |∑ x ∈ F, ∑ x'' ∈ F', (X1 x x'' - X2 x x'')|)
      ≤ a * (((N : ℝ) ^ d)⁻¹ * ((N : ℝ) ^ d * (6 * d / ν * Real.exp (-Real.sqrt ν * (t : ℝ))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hNd.le) ha
    _ = _ := by field_simp

end Green0

section TwoTorus

variable {d : ℕ}

/-- Perturbation of right inverses of matrices, entrywise, with the sums of the entries of the
inverses instead of the cardinality of the index set. -/
theorem entry_diff_le_weighted {κ : Type*} [Fintype κ] [DecidableEq κ]
    {T₁ T₂ G₁ G₂ : Matrix κ κ ℂ} {ε : ℝ} (e1 : T₁ * G₁ = 1) (e2 : T₂ * G₂ = 1)
    (hε : ∀ a b, ‖T₁ a b - T₂ a b‖ ≤ ε) (x y : κ) :
    ‖G₁ x y - G₂ x y‖ ≤ ε * (∑ a, ‖G₁ x a‖) * (∑ b, ‖G₂ b y‖) := by
  have e1' : G₁ * T₁ = 1 := mul_eq_one_comm.1 e1
  have hid : G₁ - G₂ = G₁ * (T₂ - T₁) * G₂ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, e2, Matrix.mul_one, e1', Matrix.one_mul]
  have hentry : (G₁ - G₂) x y = ∑ a, ∑ b, G₁ x a * (T₂ - T₁) a b * G₂ b y := by
    rw [hid]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [Matrix.sub_apply] at hentry
  rw [hentry]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a : κ, ‖∑ b, G₁ x a * (T₂ - T₁) a b * G₂ b y‖ ≤
      ε * ‖G₁ x a‖ * ∑ b, ‖G₂ b y‖ := by
    intro a
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_mul, norm_mul]
    have d1 : ‖(T₂ - T₁) a b‖ ≤ ε := by
      rw [Matrix.sub_apply, norm_sub_rev]; exact hε a b
    calc ‖G₁ x a‖ * ‖(T₂ - T₁) a b‖ * ‖G₂ b y‖ ≤ ‖G₁ x a‖ * ε * ‖G₂ b y‖ := by gcongr
      _ = ε * ‖G₁ x a‖ * ‖G₂ b y‖ := by ring
  refine (Finset.sum_le_sum fun a _ => hterm a).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- The sums of the entries of the Dirichlet Green function of a cube, along a row. -/
theorem boxGreen_row_sum_le {s : ℕ} [NeZero s] {c₀ δ₀ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀)
    {A : Matrix (Torus d s) (Torus d s) ℝ}
    (hdec : ∀ x y, |A x y| ≤ c₀ * Real.exp (-δ₀ * torusDist d s x y))
    (hcoer : ∀ φ : Torus d s → ℝ, 1 * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ) {R : ℕ} (hs : 2 * R < s)
    (x : L1Torus d s) :
    (∑ a : sqBox d R, ‖greenFn (cplxOp A) 0 (boxImage d s R) x (castL1 s (a : Fin d → ℤ))‖) ≤
      2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) ∧
    (∑ a : sqBox d R, ‖greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s (a : Fin d → ℤ)) x‖) ≤
      2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) := by
  have hcoerc := cplxOp_coercive hcoer
  have hκ : 0 ≤ ballConst d (δ₀ / 4) := ballConst_nonneg (by positivity)
  have hρ := ctRate_pos hc hδ one_pos hκ
  have hA : ∀ x y : L1Torus d s, ‖cplxOp A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y) := by
    intro x y
    have e : ‖cplxOp A x y‖ = |A x y| := by
      show ‖algebraMap ℝ ℂ (A x y)‖ = |A x y|
      simp
    rw [e, dist_L1Torus]
    exact hdec x y
  have hK : ∀ x : L1Torus d s, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ ballConst d (δ₀ / 4) :=
    fun x => ballSum_L1Torus d s (by positivity) x
  have key : ∀ x y : L1Torus d s, ‖greenFn (cplxOp A) 0 (boxImage d s R) x y‖ ≤
      2 * Real.exp (-(ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) * dist x y) := by
    intro x y
    have := norm_greenFn_le hc hδ one_pos hκ hA hK hcoerc (boxImage d s R) (t := 0) le_rfl x y
    simpa using this
  have hinj := castL1_injOn (d := d) (R := R) hs
  have hsum : ∀ g : L1Torus d s → ℝ, (∀ z, 0 ≤ g z) →
      ∑ a : sqBox d R, g (castL1 s (a : Fin d → ℤ)) ≤ ∑ z, g z := by
    intro g hg
    rw [Finset.sum_coe_sort (sqBox d R) (fun a => g (castL1 s a))]
    rw [← Finset.sum_image (f := g) (g := castL1 s) (fun a ha b hb h => hinj ha hb h)]
    exact Finset.sum_le_univ_sum_of_nonneg hg
  have hball : ∀ x : L1Torus d s, ∑ z, 2 * Real.exp (-(ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) *
      dist x z) ≤ 2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) := by
    intro x
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ballSum_L1Torus d s hρ x) (by norm_num)
  set g : L1Torus d s → ℝ := fun z =>
    2 * Real.exp (-(ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) * dist x z) with hg
  have hg0 : ∀ z, 0 ≤ g z := fun z => by positivity
  have hmain := (hsum g hg0).trans (hball x)
  constructor
  · have h1 : ∑ a : sqBox d R, ‖greenFn (cplxOp A) 0 (boxImage d s R) x (castL1 s (a : Fin d → ℤ))‖ ≤
        ∑ a : sqBox d R, g (castL1 s (a : Fin d → ℤ)) :=
      Finset.sum_le_sum fun a _ => key x (castL1 s a)
    exact h1.trans hmain
  · have h1 : ∑ a : sqBox d R, ‖greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s (a : Fin d → ℤ)) x‖ ≤
        ∑ a : sqBox d R, g (castL1 s (a : Fin d → ℤ)) := by
      refine Finset.sum_le_sum fun a _ => (key (castL1 s a) x).trans (le_of_eq ?_)
      simp only [hg]
      rw [dist_comm]
    exact h1.trans hmain

/-- **Quantitative two-torus closeness of inverses.**  Let `A, A'` be real operators on tori of
sides `s, s'`, coercive with constant `1`, with entries decaying like `c₀ exp(-δ₀ dist)`, whose
entries differ by at most `ε` at the sites of the cube of radius `R`.  Then their inverses differ
at the sites of the cube of radius `R₀ ≤ R` by the sum of two domain differences and `ε` times
the squared ball sum of the Combes–Thomas rate. -/
theorem inv_close_two_torus {c₀ δ₀ : ℝ} (hc : 0 ≤ c₀) (hδ : 0 < δ₀) {s s' : ℕ} [NeZero s]
    [NeZero s'] {A : Matrix (Torus d s) (Torus d s) ℝ} {A' : Matrix (Torus d s') (Torus d s') ℝ}
    (hdec : ∀ x y, |A x y| ≤ c₀ * Real.exp (-δ₀ * torusDist d s x y))
    (hdec' : ∀ x y, |A' x y| ≤ c₀ * Real.exp (-δ₀ * torusDist d s' x y))
    (hcoer : ∀ φ : Torus d s → ℝ, 1 * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A *ᵥ φ)
    (hcoer' : ∀ φ : Torus d s' → ℝ, 1 * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ A' *ᵥ φ) {R₀ R : ℕ} (hR : R₀ ≤ R)
    (hs : 2 * R < s) (hs' : 2 * R < s') {ε : ℝ}
    (hent : ∀ u ∈ sqBox d R, ∀ u' ∈ sqBox d R,
      |A (castTorus s u) (castTorus s u') - A' (castTorus s' u) (castTorus s' u')| ≤ ε)
    {u u' : Fin d → ℤ} (hu : u ∈ sqBox d R₀) (hu' : u' ∈ sqBox d R₀) :
    |A⁻¹ (castTorus s u) (castTorus s u') - A'⁻¹ (castTorus s' u) (castTorus s' u')| ≤
      2 * (ctDiff d c₀ δ₀ 1 * Real.exp (-ctDecay d c₀ δ₀ 1 * (2 * ((R : ℝ) + 1 - R₀)))) +
        ε * (2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4)))) ^ 2 := by
  have hmem := sqBox_mono (d := d) hR
  have c₁ := inv_sub_boxGreen_le hc hδ one_pos hdec hcoer hR hs hu hu'
  have c₂ := inv_sub_boxGreen_le hc hδ one_pos hdec' hcoer' hR hs' hu hu'
  have hent' : ∀ a b : sqBox d R, ‖boxMat A R a b - boxMat A' R a b‖ ≤ ε := by
    intro a b
    have := hent a a.2 b b.2
    have e : boxMat A R a b - boxMat A' R a b =
        ((A (castTorus s a) (castTorus s b) - A' (castTorus s' a) (castTorus s' b) : ℝ) : ℂ) := by
      simp [boxMat, cplxOp, castL1]
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    exact this
  have hg := entry_diff_le_weighted (boxMat_mul_boxGreen one_pos hcoer hs)
    (boxMat_mul_boxGreen one_pos hcoer' hs') hent' ⟨u, hmem hu⟩ ⟨u', hmem hu'⟩
  have r1 := (boxGreen_row_sum_le hc hδ hdec hcoer hs (castL1 s u)).1
  have r2 := (boxGreen_row_sum_le hc hδ hdec' hcoer' hs' (castL1 s' u')).2
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hent' ⟨u, hmem hu⟩ ⟨u', hmem hu'⟩)
  have hg' : ‖greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s u) (castL1 s u') -
      greenFn (cplxOp A') 0 (boxImage d s' R) (castL1 s' u) (castL1 s' u')‖ ≤
      ε * (2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4)))) ^ 2 := by
    refine hg.trans ?_
    have hS1 : ∑ a : sqBox d R, ‖boxGreen A R ⟨u, hmem hu⟩ a‖ ≤
        2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) := r1
    have hS2 : ∑ b : sqBox d R, ‖boxGreen A' R b ⟨u', hmem hu'⟩‖ ≤
        2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4))) := r2
    have hS1' : 0 ≤ ∑ a : sqBox d R, ‖boxGreen A R ⟨u, hmem hu⟩ a‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hS2' : 0 ≤ ∑ b : sqBox d R, ‖boxGreen A' R b ⟨u', hmem hu'⟩‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc ε * (∑ a : sqBox d R, ‖boxGreen A R ⟨u, hmem hu⟩ a‖) *
          (∑ b : sqBox d R, ‖boxGreen A' R b ⟨u', hmem hu'⟩‖)
        ≤ ε * (2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4)))) *
          (2 * ballConst d (ctRate c₀ δ₀ 1 (ballConst d (δ₀ / 4)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hS1 hε0) hS2 hS2'
            (mul_nonneg hε0 (hS1'.trans hS1))
      _ = _ := by ring
  set x₁ : ℝ := A⁻¹ (castTorus s u) (castTorus s u') with hx₁
  set x₂ : ℝ := A'⁻¹ (castTorus s' u) (castTorus s' u') with hx₂
  have e1 : |x₁ - x₂| = ‖(x₁ : ℂ) - (x₂ : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [e1]
  set g₁ := greenFn (cplxOp A) 0 (boxImage d s R) (castL1 s u) (castL1 s u')
  set g₂ := greenFn (cplxOp A') 0 (boxImage d s' R) (castL1 s' u) (castL1 s' u')
  calc ‖(x₁ : ℂ) - (x₂ : ℂ)‖ = ‖((x₁ : ℂ) - g₁) + (g₁ - g₂) - ((x₂ : ℂ) - g₂)‖ := by
        congr 1; ring
    _ ≤ ‖(x₁ : ℂ) - g₁‖ + ‖g₁ - g₂‖ + ‖(x₂ : ℂ) - g₂‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by linarith

theorem sqrt_ge_of_mass {L : ℕ} (hL : 0 < L) {v : ℝ} (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) :
    1 / (2 * (L : ℝ)) ≤ Real.sqrt v := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  apply Real.le_sqrt_of_sq_le
  have h2 : (1 / (2 * (L : ℝ))) ^ 2 = (1 / 4) * ((L : ℝ) ^ 2)⁻¹ := by
    field_simp; norm_num
  rw [h2]
  have : (0 : ℝ) < ((L : ℝ) ^ 2)⁻¹ := by positivity
  linarith

theorem inv_mass_le {L : ℕ} (hL : 0 < L) {v : ℝ} (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) :
    1 / v ≤ 8 * (L : ℝ) ^ 2 / 7 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hmass.le
  rw [div_le_iff₀ hv]
  have h3 : (L : ℝ) ^ 2 * ((7 / 8) * ((L : ℝ) ^ 2)⁻¹) = 7 / 8 := by field_simp
  have h4 := mul_lt_mul_of_pos_left hmass (by positivity : (0 : ℝ) < (L : ℝ) ^ 2)
  rw [h3] at h4
  have : 8 * (L : ℝ) ^ 2 / 7 * v = 8 / 7 * ((L : ℝ) ^ 2 * v) := by ring
  rw [this]
  linarith

/-- The exponents and the constants of `finalOp_entry_close_unif`. -/
theorem unif_numeric {d L : ℕ} (hL : 0 < L) {v a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {Rm Rc R : ℕ} (hR1 : 2 * R ≤ Rm + Rc)
    (hR2 : Rm + Rc ≤ 2 * R + 1) (hRc : Rc + 1 ≤ Rm) (hRm : R ≤ Rm) {μ D1 κ2 : ℝ} (hμ0 : 0 < μ)
    (hD1 : 0 ≤ D1) :
    a * (2 * (D1 * Real.exp (-μ * (2 * ((R : ℝ) + 1 - Rc)))) +
        (a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R))) * κ2 ^ 2) ≤
      (2 * (2 * D1 + 12 * d * (8 * (L : ℝ) ^ 2 / 7) * κ2 ^ 2) + 1) *
        Real.exp (-(min μ (1 / (4 * L))) * ((Rm : ℝ) - Rc)) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hmass.le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set c : ℝ := min μ (1 / (4 * L)) with hc
  have hc0 : 0 < c := lt_min hμ0 (by positivity)
  set T : ℝ := (Rm : ℝ) - Rc with hT
  have hT1 : 1 ≤ T := by
    have : ((Rc + 1 : ℕ) : ℝ) ≤ Rm := by exact_mod_cast hRc
    push_cast at this; rw [hT]; linarith
  set E : ℝ := Real.exp (-c * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hR1' : 2 * (R : ℝ) ≤ Rm + Rc := by exact_mod_cast hR1
  have hR2' : (Rm : ℝ) + Rc ≤ 2 * R + 1 := by exact_mod_cast hR2
  have hcμ : c ≤ μ := min_le_left _ _
  have hc4 : c ≤ 1 / (4 * L) := min_le_right _ _
  have h1 : Real.exp (-μ * (2 * ((R : ℝ) + 1 - Rc))) ≤ E := by
    apply Real.exp_le_exp.2
    have h5 : T ≤ 2 * ((R : ℝ) + 1 - Rc) := by rw [hT]; linarith
    have h6 : c * T ≤ μ * (2 * ((R : ℝ) + 1 - Rc)) :=
      mul_le_mul hcμ h5 (by linarith) hμ0.le
    linarith
  have hsq := sqrt_ge_of_mass hL hmass
  have h2 : Real.exp (-Real.sqrt v * ((Rm : ℝ) - R)) ≤ E := by
    apply Real.exp_le_exp.2
    have hdiff : T ≤ 2 * ((Rm : ℝ) - R) := by rw [hT]; linarith
    have hpos : 0 ≤ (Rm : ℝ) - R := by
      have : (R : ℝ) ≤ Rm := by exact_mod_cast hRm
      linarith
    have a1 : 1 / (4 * (L : ℝ)) * T ≤ Real.sqrt v * ((Rm : ℝ) - R) := by
      have e : 1 / (4 * (L : ℝ)) * T = 1 / (2 * (L : ℝ)) * (T / 2) := by field_simp; ring
      rw [e]
      exact mul_le_mul hsq (by linarith) (by linarith) (Real.sqrt_nonneg _)
    have a2 : c * T ≤ 1 / (4 * (L : ℝ)) * T := mul_le_mul_of_nonneg_right hc4 (by linarith)
    linarith
  have hinvv := inv_mass_le hL hmass
  have hε' : a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R)) ≤
      12 * d * (8 * (L : ℝ) ^ 2 / 7) * E := by
    have e6 : a * (6 * d / v) = a * (6 * d) * (1 / v) := by ring
    have h4 : a * (6 * d) ≤ 2 * (6 * d) := by nlinarith
    have e7 : a * (6 * d) * (1 / v) ≤ 2 * (6 * d) * (8 * (L : ℝ) ^ 2 / 7) :=
      mul_le_mul h4 hinvv (by positivity) (by positivity)
    calc a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R))
        ≤ (2 * (6 * d) * (8 * (L : ℝ) ^ 2 / 7)) * E := by
          rw [e6]; exact mul_le_mul e7 h2 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hL7 : 0 ≤ 12 * (d : ℝ) * (8 * (L : ℝ) ^ 2 / 7) := by positivity
  have hk2 : 0 ≤ κ2 ^ 2 := sq_nonneg _
  have hstep : 2 * (D1 * Real.exp (-μ * (2 * ((R : ℝ) + 1 - Rc)))) +
        (a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R))) * κ2 ^ 2 ≤
      (2 * D1 + 12 * d * (8 * (L : ℝ) ^ 2 / 7) * κ2 ^ 2) * E := by
    have t1 : 2 * (D1 * Real.exp (-μ * (2 * ((R : ℝ) + 1 - Rc)))) ≤ 2 * D1 * E := by
      have := mul_le_mul_of_nonneg_left h1 hD1
      linarith
    have t2 : (a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R))) * κ2 ^ 2 ≤
        12 * d * (8 * (L : ℝ) ^ 2 / 7) * E * κ2 ^ 2 := mul_le_mul_of_nonneg_right hε' hk2
    nlinarith
  have hpos : 0 ≤ 2 * D1 + 12 * d * (8 * (L : ℝ) ^ 2 / 7) * κ2 ^ 2 := by positivity
  calc _ ≤ 2 * ((2 * D1 + 12 * d * (8 * (L : ℝ) ^ 2 / 7) * κ2 ^ 2) * E) := by
        have hin : 0 ≤ 2 * (D1 * Real.exp (-μ * (2 * ((R : ℝ) + 1 - Rc)))) +
          (a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R))) * κ2 ^ 2 := by positivity
        have := mul_le_mul ha2 hstep hin (by norm_num)
        linarith
    _ ≤ _ := by nlinarith [mul_nonneg hpos hE0.le]

/-- **Entries of the final operator on two tori, uniformly in the scale.**  The constants depend
on `d` and `L` only (not on `k ≥ 1`, the tori or the cube). -/
theorem finalOp_entry_close_unif {L : ℕ} [NeZero L] (hd : 0 < d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a →
      a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {Rm Rc : ℕ}, 2 * Rm + 1 < m → 2 * Rm + 1 < m' →
      Rc + 1 ≤ Rm → ∀ {y y' : Fin d → ℤ}, y ∈ sqBox d Rc → y' ∈ sqBox d Rc →
      ‖finalOp d L m k v a (castL1 m y) (castL1 m y') -
          finalOp d L m' k v a (castL1 m' y) (castL1 m' y')‖ ≤
        C * Real.exp (-c * ((Rm : ℝ) - Rc)) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hg := finalGap_pos (d := d) hL
  have hr := finalRate_pos (L := L) hd
  set c₀ : ℝ := 4 / finalGap d L with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set D1 := ctDiff d c₀ (finalRate d L) 1 with hD1
  set μ := ctDecay d c₀ (finalRate d L) 1 with hμ
  set κ2 := 2 * ballConst d (ctRate c₀ (finalRate d L) 1 (ballConst d (finalRate d L / 4))) with hκ2
  have hμ0 : 0 < μ := ctDecay_pos (d := d) hc₀0 hr one_pos
  have hD10 : 0 ≤ D1 := ctDiff_nonneg (d := d) hc₀0 hr one_pos
  have hκ20 : 0 ≤ κ2 := by
    have : 0 ≤ ballConst d (finalRate d L / 4) := ballConst_nonneg (by positivity)
    have h2 := ctRate_pos hc₀0 hr one_pos this
    rw [hκ2]; have := ballConst_nonneg (d := d) h2; positivity
  set c : ℝ := min μ (1 / (4 * L)) with hc
  have hc0 : 0 < c := lt_min hμ0 (by positivity)
  refine ⟨2 * (2 * D1 + 12 * d * (8 * (L : ℝ) ^ 2 / 7) * κ2 ^ 2) + 1, c, by positivity, hc0, ?_⟩
  intro k hk v a hv0 hv1 ha1 ha2 hmass m m' _ _ Rm Rc hm hm' hRc y y' hy hy'
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hL2 : (0 : ℝ) < ((L : ℝ) ^ 2)⁻¹ := by positivity
  have hv : 0 < v := lt_of_lt_of_le (by positivity) hmass.le
  have ha : 0 < a := by linarith
  set R : ℕ := (Rm + Rc) / 2 with hR
  have hR1 : 2 * R ≤ Rm + Rc := by omega
  have hR2 : Rm + Rc ≤ 2 * R + 1 := by omega
  have hRc' : Rc ≤ R := by omega
  have hRm : R ≤ Rm := by omega
  have hs : 2 * R < m := by omega
  have hs' : 2 * R < m' := by omega
  have hyR : y ∈ sqBox d R := sqBox_mono hRc' hy
  have hyR' : y' ∈ sqBox d R := sqBox_mono hRc' hy'
  -- the representation of the final operator
  have hfin : ∀ (s : ℕ) [NeZero s] (z z' : Fin d → ℤ),
      finalOp d L s k v a (castL1 s z) (castL1 s z') =
        ((a * ((1 : Matrix (Torus d s) (Torus d s) ℝ) + a • (unitBlockAverageMatrix d (s * L ^ k)
          (L ^ k) s * (fineHamiltonian d (s * L ^ k) (L ^ k) s v 0)⁻¹ *
          blockPullbackMatrix d (s * L ^ k) (L ^ k) s))⁻¹ (castTorus s z) (castTorus s z') : ℝ) :
            ℂ) := by
    intro s _ z z'
    have hU := unitOperator_eq_smul_inv_psi (d := d) (ℓ := s * L ^ k) (N := L ^ k) (m := s)
      (mul_comm _ _) hd hv ha hN
    show ((unconstrainedUnitOperator d (s * L ^ k) (L ^ k) s v a (castTorus s z) (castTorus s z') :
      ℝ) : ℂ) = _
    rw [hU]
    simp
  have hdecs : ∀ (s : ℕ) [NeZero s] (x y : Torus d s),
      |((1 : Matrix (Torus d s) (Torus d s) ℝ) + a • (unitBlockAverageMatrix d (s * L ^ k)
          (L ^ k) s * (fineHamiltonian d (s * L ^ k) (L ^ k) s v 0)⁻¹ *
          blockPullbackMatrix d (s * L ^ k) (L ^ k) s)) x y| ≤
        c₀ * Real.exp (-finalRate d L * torusDist d s x y) := fun s _ x y =>
    psi_entry_decay (L := L) (N₀ := s) (k := k) hd hk hv0 hv1 ha1 ha2 hmass x y
  have hcoers : ∀ (s : ℕ) [NeZero s] (φ : Torus d s → ℝ),
      1 * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ ((1 : Matrix (Torus d s) (Torus d s) ℝ) + a • (unitBlockAverageMatrix d
          (s * L ^ k) (L ^ k) s * (fineHamiltonian d (s * L ^ k) (L ^ k) s v 0)⁻¹ *
          blockPullbackMatrix d (s * L ^ k) (L ^ k) s)) *ᵥ φ := fun s _ φ => by
    rw [one_mul]; exact psi_coercive (d := d) (ℓ := s * L ^ k) (N := L ^ k) (m := s) hd hv ha hN φ
  set ε : ℝ := a * (6 * d / v) * Real.exp (-Real.sqrt v * ((Rm : ℝ) - R)) with hε
  have hent : ∀ u ∈ sqBox d R, ∀ u' ∈ sqBox d R,
      |((1 : Matrix (Torus d m) (Torus d m) ℝ) + a • (unitBlockAverageMatrix d (m * L ^ k)
          (L ^ k) m * (fineHamiltonian d (m * L ^ k) (L ^ k) m v 0)⁻¹ *
          blockPullbackMatrix d (m * L ^ k) (L ^ k) m)) (castTorus m u) (castTorus m u') -
        ((1 : Matrix (Torus d m') (Torus d m')  ℝ) + a • (unitBlockAverageMatrix d (m' * L ^ k)
          (L ^ k) m' * (fineHamiltonian d (m' * L ^ k) (L ^ k) m' v 0)⁻¹ *
          blockPullbackMatrix d (m' * L ^ k) (L ^ k) m')) (castTorus m' u) (castTorus m' u')| ≤ ε :=
    fun u hu u' hu' => psi_entry_close (d := d) (N := L ^ k) hv hv1 ha.le hm hm' hRm hu hu'
  have hmain := inv_close_two_torus (d := d) hc₀0 hr (hdecs m) (hdecs m') (hcoers m) (hcoers m')
    hRc' hs hs' hent hy hy'
  rw [hfin m y y', hfin m' y y', ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    ← mul_sub, abs_mul, abs_of_pos ha]
  exact (mul_le_mul_of_nonneg_left hmain ha.le).trans
    (unif_numeric (d := d) hL ha ha2 hmass hR1 hR2 hRc hRm hμ0 hD10)

end TwoTorus

end Balaban.Green
