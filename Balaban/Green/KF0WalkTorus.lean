/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkTruncation
public import Balaban.LargeField.Base.KF0SqrtReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0WalkTorus`: the walk coefficients of `K_ν^{-1/2}` do not depend on the torus

This is the coefficient-level torus agreement.  The agreement of the localized terms of the
expansion and the one-scale theorem are NOT proved here.

* `kf0C_eq_kf0SqrtR`: the walk series `kf0C` and the real integral square root `kf0SqrtR` of the
  unit-torus operator `-Δ + ν` are the same matrix (both complexify to `sqrtMat (kf0Op d m ν)`).
* `zAdjCount d n v`: the number of nearest-neighbour paths of length `n` in `ℤ^d` with
  displacement `v`; a path is a sequence of `n` steps `±e_μ`.
* `kf0Adj_pow_eq_zAdjCount`: if `2n < m`, the `(x, y)` entry of `kf0Adj d m ^ n` equals
  `zAdjCount d n v`, where `v` is the centred representative (`ZMod.valMinAbs`) of `y - x`.
  Hence it depends only on the displacement, not on the side `m`
  (`kf0Adj_pow_torus_eq`).
* `kf0CR_torus_eq`, `abs_kf0C_sub_le`: the truncated kernels `kf0CR` agree on two tori when
  `2R` is smaller than both sides, and the full kernels agree up to the walk tail.
-/

@[expose] public section

namespace Balaban.Green

open Matrix

variable {d m : ℕ} [NeZero m]

/-! ### T1: the two square roots coincide -/

/-- The walk series and the real integral square root of `-Δ + ν` on the unit torus coincide. -/
theorem kf0C_eq_kf0SqrtR {ν : ℝ} (hν : 0 < ν) : kf0C d m ν = kf0SqrtR d m ν := by
  ext x y
  have h1 := congrFun (congrFun (kf0C_map_eq_sqrtMat (d := d) (m := m) hν) x) y
  have h2 := congrFun (congrFun (kf0SqrtR_map (d := d) (m := m) hν) x) y
  have h3 := h1.trans h2.symm
  exact Complex.ofReal_injective (by simpa using h3)

theorem kf0C_posDef {ν : ℝ} (hν : 0 < ν) : (kf0C d m ν).PosDef := by
  rw [kf0C_eq_kf0SqrtR hν]; exact kf0SqrtR_posDef hν

theorem kf0SqrtR_hasSum {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    HasSum (fun n : ℕ => walkWeight d ν n * (kf0Adj d m ^ n) x y) (kf0SqrtR d m ν x y) := by
  rw [← kf0C_eq_kf0SqrtR hν]; exact kf0C_hasSum hν x y

/-- Entrywise walk tail for the real square root: `0 ≤ S - C_R ≤ (2d+ν)^{-1/2} q^{R+1}/(1-q)`. -/
theorem kf0SqrtR_sub_kf0CR {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x y : Torus d m) :
    0 ≤ kf0SqrtR d m ν x y - kf0CR d m ν R x y ∧
      kf0SqrtR d m ν x y - kf0CR d m ν R x y ≤
        (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) := by
  rw [← kf0C_eq_kf0SqrtR hν]; exact kf0C_sub_kf0CR hν R x y

/-! ### Paths in `ℤ^d` -/

/-- The steps `±e_μ` of `ℤ^d`, indexed by `Fin d × Bool`. -/
def stepVec (d : ℕ) (s : Fin d × Bool) : Fin d → ℤ :=
  if s.2 then Pi.single s.1 1 else -Pi.single s.1 1

/-- The endpoint of a path given by `n` steps. -/
def stepSum {d n : ℕ} (w : Fin n → Fin d × Bool) : Fin d → ℤ := ∑ i, stepVec d (w i)

/-- The number of nearest-neighbour paths of length `n` in `ℤ^d` with displacement `v`. -/
def zAdjCount (d n : ℕ) (v : Fin d → ℤ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Fin d × Bool => stepSum w = v).card

/-- Reduction mod `m` of an integer vector, as an additive map to the torus. -/
def intToTorus (d m : ℕ) : (Fin d → ℤ) →+ Torus d m :=
  AddMonoidHom.compLeft (Int.castAddHom (ZMod m)) (Fin d)

omit [NeZero m] in
theorem intToTorus_apply (v : Fin d → ℤ) (μ : Fin d) : intToTorus d m v μ = (v μ : ZMod m) := rfl

theorem abs_stepVec_le (s : Fin d × Bool) (μ : Fin d) : |stepVec d s μ| ≤ 1 := by
  unfold stepVec
  by_cases h : s.2 <;> by_cases h2 : s.1 = μ <;> simp [h, h2]

theorem abs_stepSum_le {n : ℕ} (w : Fin n → Fin d × Bool) (μ : Fin d) : |stepSum w μ| ≤ n := by
  unfold stepSum
  rw [Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |stepVec d (w i) μ| ≤ ∑ _i : Fin n, (1 : ℤ) :=
        Finset.sum_le_sum fun i _ => abs_stepVec_le _ μ
    _ = n := by simp

theorem kf0Adj_apply_steps (x z : Torus d m) :
    kf0Adj d m x z = ∑ s : Fin d × Bool, if z = x + intToTorus d m (stepVec d s) then 1 else 0 := by
  rw [kf0Adj_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Fintype.sum_bool]
  have e1 : intToTorus d m (stepVec d (μ, true)) = Pi.single μ 1 := by
    ext ν; by_cases h : ν = μ <;> simp [stepVec, intToTorus_apply, h]
  have e2 : intToTorus d m (stepVec d (μ, false)) = -Pi.single μ 1 := by
    ext ν; by_cases h : ν = μ <;> simp [stepVec, intToTorus_apply, h]
  rw [e1, e2]
  have e3 : (x = z + Pi.single μ 1) ↔ (z = x + -Pi.single μ 1) := by
    constructor <;> (intro h; rw [h]; abel)
  simp only [e3]

/-- `(A^n)(x,y)` is the number of step sequences of length `n` leading from `x` to `y`. -/
theorem kf0Adj_pow_eq_count (n : ℕ) (x y : Torus d m) :
    (kf0Adj d m ^ n) x y =
      ∑ w : Fin n → Fin d × Bool, if x + intToTorus d m (stepSum w) = y then (1 : ℝ) else 0 := by
  induction n generalizing x with
  | zero => simp [stepSum, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [kf0Adj_apply_steps, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ih]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d × Bool)),
      ]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun w _ => ?_
    have : stepSum (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d × Bool) ((a, b), w)) =
        stepVec d (a, b) + stepSum w := by
      simp [stepSum, Fin.sum_univ_succ, Fin.consEquiv]
    rw [this, map_add, add_assoc]

omit [NeZero m] in
/-- On a torus of side `m > 2n`, equality of reductions of two vectors, one with entries in
`[-n, n]` and the other with `2|v| ≤ m`, forces equality of the vectors. -/
theorem eq_of_intToTorus_eq {n : ℕ} (hm : 2 * n < m) {u v : Fin d → ℤ}
    (hu : ∀ μ, |u μ| ≤ n) (hv : ∀ μ, 2 * |v μ| ≤ m) (h : intToTorus d m u = intToTorus d m v) :
    u = v := by
  ext μ
  have h1 := congrFun h μ
  rw [intToTorus_apply, intToTorus_apply] at h1
  have h2 : ((u μ - v μ : ℤ) : ZMod m) = 0 := by push_cast; rw [h1]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have h3 : |u μ - v μ| < (m : ℤ) := by
    have := hu μ; have := hv μ
    have := abs_sub (u μ) (v μ)
    have hm' : (2 * n : ℤ) < m := by exact_mod_cast hm
    linarith
  have := Int.eq_zero_of_abs_lt_dvd h2 h3
  linarith

/-- **Path counts on the torus are the `ℤ^d` counts.**  If `2n < m` and `y = x + (v mod m)` with
`2|v_μ| ≤ m`, then `(A^n)(x,y) = zAdjCount d n v`. -/
theorem kf0Adj_pow_eq_zAdjCount {n : ℕ} (hm : 2 * n < m) {v : Fin d → ℤ}
    (hv : ∀ μ, 2 * |v μ| ≤ m) (x y : Torus d m) (hy : y = x + intToTorus d m v) :
    (kf0Adj d m ^ n) x y = zAdjCount d n v := by
  rw [kf0Adj_pow_eq_count, zAdjCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have : (x + intToTorus d m (stepSum w) = y) ↔ stepSum w = v := by
    rw [hy]
    constructor
    · intro h
      exact eq_of_intToTorus_eq hm (abs_stepSum_le w) hv (add_left_cancel h)
    · intro h; rw [h]
  simp only [this]
  split_ifs <;> simp

/-- The centred representative of `y - x`. -/
def torusDisp (x y : Torus d m) : Fin d → ℤ := fun μ => (y μ - x μ).valMinAbs

theorem two_abs_torusDisp_le (x y : Torus d m) (μ : Fin d) : 2 * |torusDisp x y μ| ≤ m := by
  have h := ZMod.natAbs_valMinAbs_le (y μ - x μ)
  have h2 : (|torusDisp x y μ|) = ((torusDisp x y μ).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [h2]
  unfold torusDisp
  omega

omit [NeZero m] in
theorem torusDisp_spec (x y : Torus d m) : y = x + intToTorus d m (torusDisp x y) := by
  ext μ
  show y μ = x μ + ((torusDisp x y μ : ℤ) : ZMod m)
  rw [torusDisp, ZMod.coe_valMinAbs]; ring

/-- Path counts through centred displacements: for `2n < m`, `(A^n)(x,y)` is `zAdjCount` of the
centred representative of `y - x`. -/
theorem kf0Adj_pow_eq_zAdjCount_disp {n : ℕ} (hm : 2 * n < m) (x y : Torus d m) :
    (kf0Adj d m ^ n) x y = zAdjCount d n (torusDisp x y) :=
  kf0Adj_pow_eq_zAdjCount hm (two_abs_torusDisp_le x y) x y (torusDisp_spec x y)

variable {m' : ℕ} [NeZero m']

/-! ### T2: agreement of path counts -/

/-- **Path counts agree on two tori.**  If `2n < m`, `2n < m'` and the centred displacements agree,
then `(A_m^n)(x,y) = (A_{m'}^n)(x',y')`. -/
theorem kf0Adj_pow_torus_eq {n : ℕ} (hm : 2 * n < m) (hm' : 2 * n < m')
    {x y : Torus d m} {x' y' : Torus d m'} (h : torusDisp x y = torusDisp x' y') :
    (kf0Adj d m ^ n) x y = (kf0Adj d m' ^ n) x' y' := by
  rw [kf0Adj_pow_eq_zAdjCount_disp hm, kf0Adj_pow_eq_zAdjCount_disp hm', h]

/-! ### T3: coefficients -/

/-- **Truncated kernels agree on two tori.** -/
theorem kf0CR_torus_eq (ν : ℝ) {R : ℕ} (hm : 2 * R < m) (hm' : 2 * R < m')
    {x y : Torus d m} {x' y' : Torus d m'} (h : torusDisp x y = torusDisp x' y') :
    kf0CR d m ν R x y = kf0CR d m' ν R x' y' := by
  rw [kf0CR_apply, kf0CR_apply]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [kf0Adj_pow_torus_eq (by omega) (by omega) h]

/-- **Full kernels agree on two tori up to the walk tail** (the tail at `R`, with
`2R < min(m, m')`; the difference of two numbers in `[0, tail]` is at most `tail`, so the bound
is even better than twice the tail). -/
theorem abs_kf0C_sub_le {ν : ℝ} (hν : 0 < ν) {R : ℕ} (hm : 2 * R < m) (hm' : 2 * R < m')
    {x y : Torus d m} {x' y' : Torus d m'} (h : torusDisp x y = torusDisp x' y') :
    |kf0C d m ν x y - kf0C d m' ν x' y'| ≤
      (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
        (1 - 2 * d / (2 * d + ν)) := by
  have a := kf0C_sub_kf0CR hν R x y
  have b := kf0C_sub_kf0CR hν R x' y'
  have c := kf0CR_torus_eq ν hm hm' h
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-! ### T4: an explicit instance -/

/-- `d = 3`, sides `9` and `27`, `R = 1`, displacement `e₀`: the truncated kernels agree and
their common value is positive. -/
theorem kf0CR_torus_instance {ν : ℝ} (hν : 0 < ν) :
    haveI : NeZero 9 := ⟨by norm_num⟩
    haveI : NeZero 27 := ⟨by norm_num⟩
    kf0CR 3 9 ν 1 0 (intToTorus 3 9 (Pi.single 0 1)) =
        kf0CR 3 27 ν 1 0 (intToTorus 3 27 (Pi.single 0 1)) ∧
      0 < kf0CR 3 9 ν 1 0 (intToTorus 3 9 (Pi.single 0 1)) := by
  have : NeZero 9 := ⟨by norm_num⟩
  have : NeZero 27 := ⟨by norm_num⟩
  have hd : ∀ M : ℕ, [NeZero M] → 2 * 1 < M → ∀ μ : Fin 3,
      2 * |(Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) μ| ≤ (M : ℤ) := by
    intro M _ hM μ
    by_cases h : μ = 0 <;> simp [h]; omega
  have c1 : ∀ (M : ℕ) [NeZero M], 2 * 1 < M →
      (kf0Adj 3 M ^ 1) 0 (intToTorus 3 M (Pi.single 0 1)) = zAdjCount 3 1 (Pi.single 0 1) :=
    fun M _ hM => kf0Adj_pow_eq_zAdjCount (by omega) (hd M hM) 0 _ (by simp)
  have hz : 1 ≤ zAdjCount 3 1 (Pi.single (0 : Fin 3) (1 : ℤ)) := by
    refine Finset.card_pos.2 ⟨fun _ => (0, true), ?_⟩
    simp [stepSum, stepVec]
  have hdisp : torusDisp (0 : Torus 3 9) (intToTorus 3 9 (Pi.single 0 1)) =
      torusDisp (0 : Torus 3 27) (intToTorus 3 27 (Pi.single 0 1)) := by
    ext μ
    have e9 : (1 : ZMod 9).valMinAbs = 1 := by decide
    have e27 : (1 : ZMod 27).valMinAbs = 1 := by decide
    by_cases h : μ = 0 <;> simp [torusDisp, intToTorus_apply, h, e9, e27]
  refine ⟨kf0CR_torus_eq ν (by norm_num) (by norm_num) hdisp, ?_⟩
  rw [kf0CR_apply]
  have hle : walkWeight 3 ν 1 * (kf0Adj 3 9 ^ 1) 0 (intToTorus 3 9 (Pi.single 0 1)) ≤
      ∑ n ∈ Finset.range (1 + 1), walkWeight 3 ν n *
        (kf0Adj 3 9 ^ n) 0 (intToTorus 3 9 (Pi.single 0 1)) :=
    Finset.single_le_sum (f := fun n => walkWeight 3 ν n *
      (kf0Adj 3 9 ^ n) 0 (intToTorus 3 9 (Pi.single 0 1)))
      (fun n _ => mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n _ _))
      (by simp)
  have hpos : 0 < walkWeight 3 ν 1 * (kf0Adj 3 9 ^ 1) 0 (intToTorus 3 9 (Pi.single 0 1)) := by
    rw [c1 9 (by norm_num)]
    exact mul_pos (walkWeight_pos hν 1) (by exact_mod_cast hz)
  exact lt_of_lt_of_le hpos hle

end Balaban.Green
