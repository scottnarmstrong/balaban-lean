/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRWhite
public import Balaban.Green.KF0WalkTorus
import Mathlib.Tactic.Linarith

/-!
# `KF0FRKernelTorus`: the defect of the whitening on two tori (route FR, (T))

`notes/phase1/KF0-FR.md` (T). With `K = (2d+ν) - A` and `C_R = ∑_{n ≤ R} w_n A^n`, the defect
`Q_R = C_R K C_R - 1` is a polynomial of degree `2R + 1` in the adjacency matrix
(`frQ_apply_eq`). Hence on two tori of sides larger than `4R + 2` it takes the same value at pairs
with the same centred displacement (`frQ_torus_eq`), as `C_R` does (`kf0CR_torus_eq`).
-/

@[expose] public section

open Matrix Balaban.Green

namespace Balaban.LargeField.KF0FR

noncomputable section

variable {d m : ℕ} [NeZero m]

/-- **The defect as a polynomial in the adjacency matrix.** -/
theorem frQ_apply_eq (ν : ℝ) (R : ℕ) (x y : Torus d m) :
    frQ d m ν R x y = ∑ n ∈ Finset.range (R + 1), ∑ n' ∈ Finset.range (R + 1),
      walkWeight d ν n * walkWeight d ν n' *
        ((2 * d + ν) * (kf0Adj d m ^ (n + n')) x y - (kf0Adj d m ^ (n + n' + 1)) x y) -
      (1 : Matrix (Torus d m) (Torus d m) ℝ) x y := by
  have hK : latticeLaplacian d m ν = (2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) -
      kf0Adj d m := by
    rw [kf0Adj_eq ν]; abel
  have hM : kf0CR d m ν R * latticeLaplacian d m ν * kf0CR d m ν R =
      ∑ n ∈ Finset.range (R + 1), ∑ n' ∈ Finset.range (R + 1),
        (walkWeight d ν n * walkWeight d ν n') •
          ((2 * d + ν) • kf0Adj d m ^ (n + n') - kf0Adj d m ^ (n + n' + 1)) := by
    rw [hK, kf0CR, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.mul_sub, Matrix.sub_mul,
      mul_smul_comm, Matrix.mul_one, smul_mul_assoc, ← pow_add, ← pow_succ, ← pow_add,
      show n + 1 + n' = n + n' + 1 by omega]
  unfold frQ
  rw [hM, Matrix.sub_apply, Matrix.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun n' _ => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]

omit [NeZero m] in
theorem torusDisp_eq_zero_iff {x y : Torus d m} : torusDisp x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext μ
    have := congrFun h μ
    simp only [torusDisp, Pi.zero_apply] at this
    rw [ZMod.valMinAbs_eq_zero] at this
    exact (sub_eq_zero.1 this).symm
  · rintro rfl
    funext μ
    simp [torusDisp]

variable {m' : ℕ} [NeZero m']

/-- **The defect agrees on two tori** at pairs with the same centred displacement. -/
theorem frQ_torus_eq (ν : ℝ) {R : ℕ} (hm : 2 * (2 * R + 1) < m) (hm' : 2 * (2 * R + 1) < m')
    {x y : Torus d m} {x' y' : Torus d m'} (h : torusDisp x y = torusDisp x' y') :
    frQ d m ν R x y = frQ d m' ν R x' y' := by
  rw [frQ_apply_eq, frQ_apply_eq]
  have hone : (1 : Matrix (Torus d m) (Torus d m) ℝ) x y =
      (1 : Matrix (Torus d m') (Torus d m') ℝ) x' y' := by
    by_cases hxy : x = y
    · have : x' = y' := torusDisp_eq_zero_iff.1 (h ▸ torusDisp_eq_zero_iff.2 hxy)
      rw [hxy, this, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · have : x' ≠ y' := fun h' => hxy (torusDisp_eq_zero_iff.1 (h.symm ▸ torusDisp_eq_zero_iff.2 h'))
      rw [Matrix.one_apply_ne hxy, Matrix.one_apply_ne this]
  rw [hone]
  congr 1
  refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun n' hn' => ?_
  have h1 : n ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have h2 : n' ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
  rw [kf0Adj_pow_torus_eq (n := n + n') (by omega) (by omega) h,
    kf0Adj_pow_torus_eq (n := n + n' + 1) (by omega) (by omega) h]

end

end Balaban.LargeField.KF0FR
