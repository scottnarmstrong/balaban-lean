/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0GoodGaussian
public import Balaban.LargeField.Base.KF0SqrtReal
public import Balaban.Green.KF0WalkTruncation
public import Balaban.Green.KF0WalkTorus
public import Balaban.Green.KF0DetWalks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The square root on a region with holes as a killed-walk series

Fixed bad set `D ⊂ (ℤ/m)^d` and good sites `G = Dᶜ`.  With `A_G = kwAdjG d m D` (the adjacency
matrix with the rows and columns of `D` removed) and the weights `w_n = walkWeight d ν n` of
`KF0WalkSeries`, the killed-walk series is
`kwC = ∑_n w_n A_G^n` (entrywise, on the whole torus).

* `kwC` has nonnegative entries, is symmetric, has row sums at most `ν^{-1/2}`, and its restriction
  to the good sites squares to `K_G⁻¹` (`K_G = kwOpSub d m ν D`) and is positive definite
  (`kwCSub_mul_self`, `kwCSub_posDef`).
* `kwSqrt_eq_kwCSub`: the landed `kwSqrt ν D = CFC.sqrt K_G⁻¹` equals the restriction of `kwC`
  (uniqueness of the positive semidefinite square root, `CFC.sqrt_unique`).  Corollaries:
  nonnegative entries, row sums, entrywise decay beyond the `ℓ¹` distance.
* Hole-walk identity: for all sites `x, y`
  `kf0C x y - kwC x y = ∑_n w_n ((A^n)(x,y) - (A_G^n)(x,y))`, every term is nonnegative, the term
  of order `n` vanishes unless some site `z ∈ D` has `dist x z + dist z y ≤ n`, and the difference
  is bounded by the geometric tail beyond that order.  The difference of the `n`-th powers is the
  number of `n`-step walks from `x` to `y` that visit `D` (`kf0Adj_pow_sub_kwAdjG_pow_eq_count`).
* Loop occupancy: the inclusion–exclusion identity for "the walk meets the bad set"
  (`one_sub_prod_one_sub_eq`) applied to the landed loop terms `kwTraceDiff`.

This concerns a fixed bad set only.  The integrated collar potential, the linked expansion and the
one-scale theorem are NOT proved here.
-/

@[expose] public section

namespace Balaban.Green

open Matrix MeasureTheory Set Filter Topology Balaban Balaban.LargeField
open scoped ComplexOrder

variable {d m : ℕ} [NeZero m]

/-! ### Generic: a real matrix given by the resolvent integral is `sqrtMat` -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem posDef_resolvent_gen {K : Matrix ι ι ℝ} (hK : K.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (t • (1 : Matrix ι ι ℝ) + K).PosDef := by
  have h1 : (t • (1 : Matrix ι ι ℝ)).PosSemidef :=
    (Matrix.PosSemidef.one (n := ι) (R := ℝ)).smul ht
  simpa [add_comm] using hK.add_posSemidef h1

theorem resolvent_complex_gen {K : Matrix ι ι ℝ} (hK : K.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    ((t : ℂ) • (1 : Matrix ι ι ℂ) + K.map (algebraMap ℝ ℂ))⁻¹ =
      (((t • (1 : Matrix ι ι ℝ) + K)⁻¹).map (algebraMap ℝ ℂ)) := by
  have hB : (t • (1 : Matrix ι ι ℝ) + K).map (algebraMap ℝ ℂ) =
      (t : ℂ) • (1 : Matrix ι ι ℂ) + K.map (algebraMap ℝ ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have := map_inv_ofReal ((Matrix.isUnit_iff_isUnit_det _).1
    (posDef_resolvent_gen hK ht).isUnit)
  rw [hB] at this
  exact this

theorem map_eq_sqrtMat_of_integral [Nonempty ι] {K R : Matrix ι ι ℝ} (hK : K.PosDef)
    (hR : ∀ x y, R x y = (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      (((t • (1 : Matrix ι ι ℝ) + K)⁻¹) x y)) :
    R.map (algebraMap ℝ ℂ) = Localization.sqrtMat (K.map (algebraMap ℝ ℂ)) := by
  ext x y
  have e : Localization.sqrtMat (K.map (algebraMap ℝ ℂ)) x y = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((t : ℂ) • (1 : Matrix ι ι ℂ) + K.map (algebraMap ℝ ℂ))⁻¹) x y) := rfl
  rw [e]
  have h2 : ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((t : ℂ) • (1 : Matrix ι ι ℂ) + K.map (algebraMap ℝ ℂ))⁻¹) x y) =
      ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
        (((t • (1 : Matrix ι ι ℝ) + K)⁻¹) x y) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [resolvent_complex_gen hK (le_of_lt ht)]
    simp
  rw [h2]
  simp [hR x y]

theorem real_sqrt_of_integral [Nonempty ι] {K R : Matrix ι ι ℝ} (hK : K.PosDef)
    (hR : ∀ x y, R x y = (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      (((t • (1 : Matrix ι ι ℝ) + K)⁻¹) x y)) :
    R * R = K⁻¹ ∧ R.PosDef := by
  have hmap := map_eq_sqrtMat_of_integral hK hR
  have hKc : (K.map (algebraMap ℝ ℂ)).PosDef := posDef_map_ofReal hK
  have hs : Localization.sqrtMat (K.map (algebraMap ℝ ℂ)) =
      Localization.invSqrtMat hKc := Localization.resolvent_sqrt_eq hKc
  have hC := Localization.invSqrtMat_posDef hKc
  rw [← hs, ← hmap] at hC
  refine ⟨?_, ?_⟩
  · apply Matrix.map_injective (f := algebraMap ℝ ℂ) Complex.ofReal_injective
    show (R * R).map (algebraMap ℝ ℂ) = (K⁻¹).map (algebraMap ℝ ℂ)
    rw [Matrix.map_mul, hmap]
    have h := Localization.sqrtMat_mul_self (Localization.resOK_of_posDef hKc)
    rw [map_inv_ofReal ((Matrix.isUnit_iff_isUnit_det _).1 hK.isUnit)] at h
    exact h
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · ext i j
      have := hC.isHermitian.apply i j
      simpa [Matrix.conjTranspose_apply, Matrix.map_apply] using this
    · intro x hx
      have hxC : (fun i => (x i : ℂ)) ≠ 0 := by
        intro h0
        apply hx
        funext i
        simpa using congrFun h0 i
      have := hC.dotProduct_mulVec_pos hxC
      have e : star (fun i => (x i : ℂ)) ⬝ᵥ (R.map (algebraMap ℝ ℂ) *ᵥ fun i => (x i : ℂ)) =
          ((star x ⬝ᵥ (R *ᵥ x) : ℝ) : ℂ) := by
        simp [dotProduct, Matrix.mulVec]
      exact Complex.zero_lt_real.1 (lt_of_lt_of_eq this e)

end Generic

/-! ### T1: the killed-walk series -/

/-- The killed-walk series `C_G = ∑_n w_n A_G^n`, entrywise on the whole torus (`A_G` the adjacency
matrix with the rows and columns of the bad set `D` removed). -/
noncomputable def kwC (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  fun x y => ∑' n : ℕ, walkWeight d ν n * (kwAdjG d m D ^ n) x y

/-- The restriction of `kwC` to the good sites `G = Dᶜ`. -/
noncomputable def kwCSub (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) :
    Matrix (Good D) (Good D) ℝ :=
  (kwC d m ν D).submatrix Subtype.val Subtype.val

variable (D : Finset (Torus d m))

theorem kwAdjG_pow_le (n : ℕ) (x y : Torus d m) : (kwAdjG d m D ^ n) x y ≤ (2 * d : ℝ) ^ n :=
  calc (kwAdjG d m D ^ n) x y ≤ ∑ z, (kwAdjG d m D ^ n) x z :=
        Finset.single_le_sum (f := fun z => (kwAdjG d m D ^ n) x z)
          (fun z _ => KW.pow_entry_nonneg (kwAdjG_nonneg D) n x z) (Finset.mem_univ y)
    _ ≤ (2 * d : ℝ) ^ n :=
        KW.pow_rowSum_le (kwAdjG_nonneg D) (by positivity) (kwAdjG_rowSum_le D) n x

theorem kwAdjG_pow_symm (n : ℕ) (x y : Torus d m) :
    (kwAdjG d m D ^ n) x y = (kwAdjG d m D ^ n) y x := by
  have h : (kwAdjG d m D)ᵀ = kwAdjG d m D := by
    ext a b; exact kwAdjG_symm D b a
  have h2 : (kwAdjG d m D ^ n)ᵀ = kwAdjG d m D ^ n := by rw [Matrix.transpose_pow, h]
  exact (congrFun (congrFun h2 x) y).symm

variable {D}

theorem kwC_hasSum {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    HasSum (fun n : ℕ => walkWeight d ν n * (kwAdjG d m D ^ n) x y) (kwC d m ν D x y) := by
  have h := hasSum_coeff_walkWeight (d := d) hν (fun n => (kwAdjG d m D ^ n) x y)
    (fun n => KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y) (fun n => kwAdjG_pow_le D n x y)
  have hs : Summable (fun n : ℕ => walkWeight d ν n * (kwAdjG d m D ^ n) x y) :=
    h.summable.congr (fun n => mul_comm _ _)
  exact hs.hasSum

theorem kwC_nonneg {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) : 0 ≤ kwC d m ν D x y :=
  (kwC_hasSum hν x y).nonneg fun n =>
    mul_nonneg (walkWeight_pos hν n).le (KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y)

theorem kwC_symm (ν : ℝ) (x y : Torus d m) : kwC d m ν D x y = kwC d m ν D y x := by
  unfold kwC
  exact tsum_congr fun n => by rw [kwAdjG_pow_symm]

/-- Row sums of the killed-walk series are at most `ν^{-1/2}`. -/
theorem kwC_rowSum_le {ν : ℝ} (hν : 0 < ν) (x : Torus d m) :
    ∑ y, kwC d m ν D x y ≤ (Real.sqrt ν)⁻¹ := by
  have h1 := hasSum_sum (s := (Finset.univ : Finset (Torus d m)))
    (fun y _ => kwC_hasSum (D := D) hν x y)
  refine hasSum_le (fun n => ?_) h1 (hasSum_walkWeight_row (d := d) hν)
  rw [← Finset.mul_sum, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (KW.pow_rowSum_le (kwAdjG_nonneg D) (by positivity) (kwAdjG_rowSum_le D) n x)
    (walkWeight_pos hν n).le

/-- The integral form: `C_G(x,y) = π⁻¹ ∫₀^∞ t^{-1/2} (K_G^{(ν+t)})⁻¹(x,y) dt` with the padded
operator at mass `ν + t`. -/
theorem kwC_eq_integral {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    kwC d m ν D x y = (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      (kwOp d m (ν + t) D)⁻¹ x y := by
  have h := hasSum_coeff_walkWeight (d := d) hν (fun n => (kwAdjG d m D ^ n) x y)
    (fun n => KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y) (fun n => kwAdjG_pow_le D n x y)
  have h' : HasSum (fun n : ℕ => walkWeight d ν n * (kwAdjG d m D ^ n) x y)
      ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
        t ^ (-(1 / 2 : ℝ)) * ∑' n, (kwAdjG d m D ^ n) x y * ((2 * d + ν + t) ^ (n + 1))⁻¹) := by
    simpa only [mul_comm] using h
  rw [(kwC_hasSum hν x y).unique h']
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  congr 1
  have hs := kwOp_inv_hasSum (show 0 < ν + t by linarith) D x y
  rw [← hs.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [inv_pow, add_assoc, mul_comm]

theorem kwOpSub_add_smul_one (ν t : ℝ) :
    t • (1 : Matrix (Good D) (Good D) ℝ) + kwOpSub d m ν D = kwOpSub d m (ν + t) D := by
  have e : latticeLaplacian d m (ν + t) =
      latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ) := by
    unfold latticeLaplacian
    simp only [add_smul]
    abel
  ext x y
  rw [kwOpSub_apply, e]
  by_cases hxy : x = y
  · subst hxy; simp [kwOpSub_apply, add_comm]
  · have : (x : Torus d m) ≠ y := fun h => hxy (Subtype.ext h)
    simp [kwOpSub_apply, hxy, this]

theorem kwCSub_eq_integral {ν : ℝ} (hν : 0 < ν) (x y : Good D) :
    kwCSub d m ν D x y = (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      (((t • (1 : Matrix (Good D) (Good D) ℝ) + kwOpSub d m ν D)⁻¹) x y) := by
  rw [kwCSub, Matrix.submatrix_apply, kwC_eq_integral hν]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [kwOpSub_add_smul_one, kwOpSub_inv (show 0 < ν + t by linarith) D, Matrix.submatrix_apply]

theorem kwCSub_mul_self_and_posDef {ν : ℝ} (hν : 0 < ν) :
    kwCSub d m ν D * kwCSub d m ν D = (kwOpSub d m ν D)⁻¹ ∧ (kwCSub d m ν D).PosDef := by
  rcases isEmpty_or_nonempty (Good D) with hE | hE
  · refine ⟨?_, ?_⟩
    · ext x; exact isEmptyElim x
    · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
      · ext x; exact isEmptyElim x
      · intro v hv; exact absurd (funext fun x => isEmptyElim x) hv
  · exact real_sqrt_of_integral (kwOpSub_posDef ν D hν) (kwCSub_eq_integral hν)

/-- `C_G * C_G = K_G⁻¹` on the good sites. -/
theorem kwCSub_mul_self {ν : ℝ} (hν : 0 < ν) :
    kwCSub d m ν D * kwCSub d m ν D = (kwOpSub d m ν D)⁻¹ :=
  (kwCSub_mul_self_and_posDef hν).1

/-- `C_G` is positive definite on the good sites. -/
theorem kwCSub_posDef {ν : ℝ} (hν : 0 < ν) : (kwCSub d m ν D).PosDef :=
  (kwCSub_mul_self_and_posDef hν).2

theorem kwCSub_posSemidef {ν : ℝ} (hν : 0 < ν) : (kwCSub d m ν D).PosSemidef :=
  (kwCSub_posDef hν).posSemidef

/-! ### T2: identification with the landed `kwSqrt` -/

open scoped MatrixOrder in
/-- **Uniqueness of the positive semidefinite square root.**  The landed `kwSqrt`, defined by the
continuous functional calculus square root of `K_G⁻¹`, is the restriction of the killed-walk
series to the good sites. -/
theorem kwSqrt_eq_kwCSub {ν : ℝ} (hν : 0 < ν) : kwSqrt ν D = kwCSub d m ν D := by
  unfold kwSqrt
  exact CFC.sqrt_unique (kwCSub_mul_self hν)
    (Matrix.nonneg_iff_posSemidef.mpr (kwCSub_posSemidef hν))

theorem kwSqrt_apply_eq {ν : ℝ} (hν : 0 < ν) (x y : Good D) :
    kwSqrt ν D x y = kwC d m ν D x y := by
  rw [kwSqrt_eq_kwCSub hν]; rfl

theorem kwSqrt_nonneg_entry {ν : ℝ} (hν : 0 < ν) (x y : Good D) : 0 ≤ kwSqrt ν D x y := by
  rw [kwSqrt_apply_eq hν]; exact kwC_nonneg (D := D) hν (x : Torus d m) (y : Torus d m)

/-- Row sums of the landed `kwSqrt` (over the good sites) are at most `ν^{-1/2}`. -/
theorem kwSqrt_rowSum_le {ν : ℝ} (hν : 0 < ν) (x : Good D) :
    ∑ y, kwSqrt ν D x y ≤ (Real.sqrt ν)⁻¹ := by
  have h1 : ∑ y : Good D, kwC d m ν D x y ≤ ∑ y : Torus d m, kwC d m ν D x y := by
    have := Fintype.sum_subtype_add_sum_subtype (fun z : Torus d m => z ∉ D)
      (fun y => kwC d m ν D x y)
    have h2 : 0 ≤ ∑ y : {z : Torus d m // ¬ z ∉ D}, kwC d m ν D x y :=
      Finset.sum_nonneg fun y _ => kwC_nonneg (D := D) hν (x : Torus d m) (y : Torus d m)
    linarith
  calc ∑ y, kwSqrt ν D x y = ∑ y : Good D, kwC d m ν D x y :=
        Finset.sum_congr rfl fun y _ => kwSqrt_apply_eq hν x y
    _ ≤ _ := h1.trans (kwC_rowSum_le (D := D) hν x)

/-- Entrywise decay of the killed-walk series: beyond `ℓ¹` distance `R`,
`C_G(x,y) ≤ (2d+ν)^{-1/2} q^{R+1}/(1-q)`, `q = 2d/(2d+ν)`. -/
theorem kwC_le_of_lt_dist {ν : ℝ} (hν : 0 < ν) {R : ℕ} {x y : Torus d m}
    (h : (R : ℝ) < torusDist d m x y) :
    kwC d m ν D x y ≤ (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  have hq1 : 2 * (d : ℝ) / (2 * d + ν) < 1 := by rw [div_lt_one ha]; linarith
  have hq0 : 0 ≤ 2 * (d : ℝ) / (2 * d + ν) := by positivity
  have := tail_bound _ (kwC_hasSum (D := D) hν x y) hq0 hq1
    (K := (Real.sqrt (2 * d + ν))⁻¹) (fun n => mul_nonneg (walkWeight_pos hν n).le (KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y))
    (fun n => ?_) R
  · have h0 : ∑ n ∈ Finset.range (R + 1), walkWeight d ν n * (kwAdjG d m D ^ n) x y = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnR : (n : ℝ) ≤ R := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [kwAdjG_pow_eq_zero_of_lt D n x y (by linarith), mul_zero]
    rw [h0, sub_zero] at this
    exact this.2
  · calc walkWeight d ν n * (kwAdjG d m D ^ n) x y ≤ walkWeight d ν n * (2 * d : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (kwAdjG_pow_le D n x y) (walkWeight_pos hν n).le
      _ ≤ (((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹) * (2 * d : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (walkWeight_le hν n) (by positivity)
      _ = _ := by rw [div_pow]; field_simp

theorem kwSqrt_le_of_lt_dist {ν : ℝ} (hν : 0 < ν) {R : ℕ} {x y : Good D}
    (h : (R : ℝ) < torusDist d m x y) :
    kwSqrt ν D x y ≤ (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) := by
  rw [kwSqrt_apply_eq hν]; exact kwC_le_of_lt_dist hν h

/-! ### T3: the hole-walk identity -/

theorem kwAdjG_pow_le_kf0Adj_pow (n : ℕ) (x y : Torus d m) :
    (kwAdjG d m D ^ n) x y ≤ (kf0Adj d m ^ n) x y :=
  KW.pow_entry_mono (kwAdjG_nonneg D) (kwAdjG_le D) n x y

theorem kwC_le_kf0C {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) : kwC d m ν D x y ≤ kf0C d m ν x y :=
  hasSum_le (fun n => mul_le_mul_of_nonneg_left (kwAdjG_pow_le_kf0Adj_pow n x y)
    (walkWeight_pos hν n).le) (kwC_hasSum hν x y) (kf0C_hasSum hν x y)

/-- **Hole-walk identity.**  `C_Λ(x,y) - C_G(x,y) = ∑_n w_n ((A^n)(x,y) - (A_G^n)(x,y))`. -/
theorem kf0C_sub_kwC_hasSum {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    HasSum (fun n : ℕ => walkWeight d ν n * ((kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y))
      (kf0C d m ν x y - kwC d m ν D x y) := by
  have := (kf0C_hasSum hν x y).sub (kwC_hasSum (D := D) hν x y)
  simpa only [mul_sub] using this

/-- Every term of the hole-walk series is nonnegative. -/
theorem walkWeight_mul_pow_sub_nonneg {ν : ℝ} (hν : 0 < ν) (n : ℕ) (x y : Torus d m) :
    0 ≤ walkWeight d ν n * ((kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y) :=
  mul_nonneg (walkWeight_pos hν n).le (sub_nonneg.2 (kwAdjG_pow_le_kf0Adj_pow n x y))

/-- If the `n`-th powers differ at `(x,y)`, some site `z` of `D` satisfies
`dist x z + dist z y ≤ n`: a walk from `x` to `y` that visits `D` has length at least that. -/
theorem exists_mem_dist_of_pow_sub_ne_zero {n : ℕ} {x y : Torus d m}
    (h : (kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y ≠ 0) :
    ∃ z ∈ D, torusDist d m x z + torusDist d m z y ≤ n := by
  cases n with
  | zero => simp at h
  | succ n =>
    have e := KW.pow_sub_pow_telescope (kf0Adj d m) (kwAdjG d m D) n
    have h' : ((kf0Adj d m ^ (n + 1) - kwAdjG d m D ^ (n + 1)) x y) ≠ 0 := by
      simpa [Matrix.sub_apply] using h
    rw [e, Matrix.sum_apply] at h'
    obtain ⟨i, hi, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Matrix.mul_apply] at hi0
    obtain ⟨v, _, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi0
    have h1 := left_ne_zero_of_mul hv
    have h2 := right_ne_zero_of_mul hv
    rw [Matrix.mul_apply] at h1
    obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
    have h3 := left_ne_zero_of_mul hu
    have h4 := right_ne_zero_of_mul hu
    have d1 : torusDist d m x u ≤ i := kf0Adj_pow_dist h3
    have d2 : torusDist d m v y ≤ ((n - i : ℕ) : ℝ) := by
      by_contra hc
      exact h2 (kwAdjG_pow_eq_zero_of_lt D (n - i) v y (not_le.1 hc))
    have hsub : ((n - i : ℕ) : ℝ) = n - i := Nat.cast_sub hi'
    have hcase : u ∈ D ∨ v ∈ D := by
      by_contra hc
      apply h4
      simp only [Matrix.sub_apply, kwAdjG, Matrix.of_apply, hc, ite_false]
      exact sub_self _
    have hA : kwAdj d m u v ≠ 0 := by
      intro h0
      apply h4
      rw [Matrix.sub_apply]
      have := kwAdjG_nonneg D u v
      have := kwAdjG_le D u v
      show kwAdj d m u v - kwAdjG d m D u v = 0
      linarith
    have d3 := kwAdj_dist_le_one hA
    have t1 := torusDist_triangle' (d := d) (m := m) x u v
    have t2 := torusDist_triangle' (d := d) (m := m) u v y
    rcases hcase with hu' | hv'
    · refine ⟨u, hu', ?_⟩
      push_cast
      linarith
    · refine ⟨v, hv', ?_⟩
      push_cast
      linarith

/-- The difference of the full and the good-region square roots is nonnegative. -/
theorem kf0C_sub_kwC_nonneg {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    0 ≤ kf0C d m ν x y - kwC d m ν D x y :=
  sub_nonneg.2 (kwC_le_kf0C hν x y)

/-- **Tail bound for the hole-walk series.**  If every site `z` of `D` satisfies
`R < dist x z + dist z y`, then `0 ≤ C_Λ(x,y) - C_G(x,y) ≤ (2d+ν)^{-1/2} q^{R+1}/(1-q)`. -/
theorem kf0C_sub_kwC_le {ν : ℝ} (hν : 0 < ν) {R : ℕ} {x y : Torus d m}
    (h : ∀ z ∈ D, (R : ℝ) < torusDist d m x z + torusDist d m z y) :
    0 ≤ kf0C d m ν x y - kwC d m ν D x y ∧
      kf0C d m ν x y - kwC d m ν D x y ≤
        (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  have hq1 : 2 * (d : ℝ) / (2 * d + ν) < 1 := by rw [div_lt_one ha]; linarith
  have hq0 : 0 ≤ 2 * (d : ℝ) / (2 * d + ν) := by positivity
  have := tail_bound _ (kf0C_sub_kwC_hasSum (D := D) hν x y) hq0 hq1
    (K := (Real.sqrt (2 * d + ν))⁻¹)
    (fun n => walkWeight_mul_pow_sub_nonneg hν n x y) (fun n => ?_) R
  · have h0 : ∑ n ∈ Finset.range (R + 1), walkWeight d ν n *
        ((kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnR : (n : ℝ) ≤ R := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have : (kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y = 0 := by
        by_contra hne
        obtain ⟨z, hz, hz2⟩ := exists_mem_dist_of_pow_sub_ne_zero hne
        linarith [h z hz]
      rw [this, mul_zero]
    rw [h0, sub_zero] at this
    exact this
  · calc walkWeight d ν n * ((kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y)
        ≤ walkWeight d ν n * (2 * d : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_left ?_ (walkWeight_pos hν n).le
          have := kf0Adj_pow_le (d := d) (m := m) n x y
          have := KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y
          linarith
      _ ≤ (((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹) * (2 * d : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (walkWeight_le hν n) (by positivity)
      _ = _ := by rw [div_pow]; field_simp

/-- The tail from the order `dist x D`: if every site of `D` is farther than `R` from `x`, the
difference is bounded by the geometric tail beyond `R`. -/
theorem kf0C_sub_kwC_le_of_far {ν : ℝ} (hν : 0 < ν) {R : ℕ} {x y : Torus d m}
    (h : ∀ z ∈ D, (R : ℝ) < torusDist d m x z) :
    0 ≤ kf0C d m ν x y - kwC d m ν D x y ∧
      kf0C d m ν x y - kwC d m ν D x y ≤
        (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) :=
  kf0C_sub_kwC_le hν fun z hz => by
    have := torusDist_nonneg' (d := d) (m := m) z y
    linarith [h z hz]

/-- For the landed `kwSqrt` on the good sites: `0 ≤ K_Λ^{-1/2}(x,y) - K_G^{-1/2}(x,y)`. -/
theorem kf0SqrtR_sub_kwSqrt_nonneg {ν : ℝ} (hν : 0 < ν) (x y : Good D) :
    0 ≤ kf0SqrtR d m ν x y - kwSqrt ν D x y := by
  rw [← kf0C_eq_kf0SqrtR hν, kwSqrt_apply_eq hν]
  exact kf0C_sub_kwC_nonneg (D := D) hν (x : Torus d m) (y : Torus d m)

/-! ### Walks that visit `D` -/

variable (D) in
/-- The site reached from `x` after the first `k` steps of the step sequence `w`. -/
def walkPos (x : Torus d m) {n : ℕ} (w : Fin n → Fin d × Bool) (k : ℕ) : Torus d m :=
  x + intToTorus d m (∑ i : Fin n, if (i : ℕ) < k then stepVec d (w i) else 0)

/-- The step sequence `w` started at `x` visits the set `D` (at some time `k ≤ n`, the start
included). -/
abbrev WalkMeets (D : Finset (Torus d m)) (x : Torus d m) {n : ℕ} (w : Fin n → Fin d × Bool) :
    Prop :=
  ∃ k ∈ Finset.range (n + 1), walkPos x w k ∈ D

theorem stepSum_cons {n : ℕ} (s : Fin d × Bool) (w : Fin n → Fin d × Bool) :
    stepSum (Fin.cons s w : Fin (n + 1) → Fin d × Bool) = stepVec d s + stepSum w := by
  simp [stepSum, Fin.sum_univ_succ]

omit [NeZero m] in
theorem walkPos_cons_succ {n : ℕ} (x : Torus d m) (s : Fin d × Bool) (w : Fin n → Fin d × Bool)
    (k : ℕ) : walkPos x (Fin.cons s w : Fin (n + 1) → Fin d × Bool) (k + 1) =
      walkPos (x + intToTorus d m (stepVec d s)) w k := by
  simp only [walkPos, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, Nat.succ_pos, ite_true, Nat.succ_lt_succ_iff, map_add, add_assoc]

omit [NeZero m] in
theorem walkPos_zero {n : ℕ} (x : Torus d m) (w : Fin n → Fin d × Bool) : walkPos x w 0 = x := by
  simp [walkPos]

omit [NeZero m] in
theorem walkMeets_cons {n : ℕ} (D : Finset (Torus d m)) (x : Torus d m) (s : Fin d × Bool)
    (w : Fin n → Fin d × Bool) :
    WalkMeets D x (Fin.cons s w : Fin (n + 1) → Fin d × Bool) ↔
      x ∈ D ∨ WalkMeets D (x + intToTorus d m (stepVec d s)) w := by
  constructor
  · rintro ⟨k, hk, hD⟩
    cases k with
    | zero => left; simpa [walkPos_zero] using hD
    | succ k =>
      right
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_range] at hk ⊢; omega
      · rwa [walkPos_cons_succ] at hD
  · rintro (h | ⟨k, hk, hD⟩)
    · exact ⟨0, by simp, by simpa [walkPos_zero] using h⟩
    · refine ⟨k + 1, ?_, ?_⟩
      · simp only [Finset.mem_range] at hk ⊢; omega
      · rwa [walkPos_cons_succ]

omit [NeZero m] in
theorem walkMeets_of_mem (D : Finset (Torus d m)) {x : Torus d m} (hx : x ∈ D) {n : ℕ}
    (w : Fin n → Fin d × Bool) : WalkMeets D x w :=
  ⟨0, by simp, by simpa [walkPos_zero] using hx⟩

/-- The `n`-th power of the killed adjacency matrix counts the step sequences from `x` to `y`
that never visit `D` (for `x` outside `D`). -/
theorem kwAdjG_pow_eq_count (n : ℕ) : ∀ x : Torus d m, x ∉ D → ∀ y : Torus d m,
    (kwAdjG d m D ^ n) x y =
      ∑ w : Fin n → Fin d × Bool,
        if x + intToTorus d m (stepSum w) = y ∧ ¬ WalkMeets D x w then (1 : ℝ) else 0 := by
  induction n with
  | zero =>
    intro x hx y
    simp [stepSum, Matrix.one_apply, WalkMeets, walkPos, hx]
  | succ n ih =>
    intro x hx y
    rw [pow_succ', Matrix.mul_apply]
    have hL : ∀ z, kwAdjG d m D x z * (kwAdjG d m D ^ n) z y =
        ∑ s : Fin d × Bool, if z = x + intToTorus d m (stepVec d s) then
          (if z ∈ D then 0 else (kwAdjG d m D ^ n) z y) else 0 := by
      intro z
      by_cases hz : z ∈ D
      · simp [kwAdjG, hz]
      · have : kwAdjG d m D x z = kwAdj d m x z := by simp [kwAdjG, hx, hz]
        rw [this, kwAdj_eq_kf0Adj, kf0Adj_apply_steps, Finset.sum_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases h : z = x + intToTorus d m (stepVec d s)
        · subst h; simp [hz]
        · simp [h]
    simp_rw [hL]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d × Bool))]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : x + intToTorus d m (stepVec d s) ∈ D
    · simp only [hs, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero fun w _ => ?_
      have : WalkMeets D x (Fin.cons s w : Fin (n + 1) → Fin d × Bool) :=
        (walkMeets_cons D x s w).2 (Or.inr (walkMeets_of_mem D hs w))
      simp [Fin.consEquiv, this]
    · simp only [hs, ↓reduceIte]
      rw [ih _ hs y]
      refine Finset.sum_congr rfl fun w _ => ?_
      have e1 : x + intToTorus d m (stepSum (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d × Bool)
          (s, w))) = x + intToTorus d m (stepVec d s) + intToTorus d m (stepSum w) := by
        simp only [Fin.consEquiv, Equiv.coe_fn_mk, stepSum_cons, map_add, add_assoc]
      have e2 : WalkMeets D x (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d × Bool) (s, w)) ↔
          WalkMeets D (x + intToTorus d m (stepVec d s)) w := by
        simp only [Fin.consEquiv, Equiv.coe_fn_mk]
        rw [walkMeets_cons]
        simp [hx]
      simp only [e1]
      simp only [e2]

/-- **The difference of the powers counts walks that visit `D`** (for `n ≥ 1`):
`(A^n)(x,y) - (A_G^n)(x,y)` is the number of step sequences of length `n` from `x` to `y`
that pass through a site of `D`. -/
theorem kf0Adj_pow_sub_kwAdjG_pow_eq_count {n : ℕ} (hn : 0 < n) (x y : Torus d m) :
    (kf0Adj d m ^ n) x y - (kwAdjG d m D ^ n) x y =
      ∑ w : Fin n → Fin d × Bool,
        if x + intToTorus d m (stepSum w) = y ∧ WalkMeets D x w then (1 : ℝ) else 0 := by
  rw [kf0Adj_pow_eq_count]
  by_cases hx : x ∈ D
  · have h0 : (kwAdjG d m D ^ n) x y = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ', Matrix.mul_apply]
      exact Finset.sum_eq_zero fun z _ => by simp [kwAdjG, hx]
    rw [h0, sub_zero]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [walkMeets_of_mem D hx w]
  · rw [kwAdjG_pow_eq_count (D := D) n x hx y, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hP : x + intToTorus d m (stepSum w) = y <;> by_cases hM : WalkMeets D x w <;>
      simp [hP, hM]

/-! ### T4: loop occupancy (inclusion–exclusion) -/

/-- **Inclusion–exclusion.**  For commutative-ring elements `b_i` (indicators of bad blocks),
`1 - ∏_{i ∈ s} (1 - b_i) = ∑_{∅ ≠ I ⊆ s} (-1)^{|I|+1} ∏_{i ∈ I} b_i`. -/
theorem one_sub_prod_one_sub_eq {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (b : ι → R) :
    1 - ∏ i ∈ s, (1 - b i) =
      ∑ I ∈ s.powerset.filter Finset.Nonempty, (-1) ^ (I.card + 1) * ∏ i ∈ I, b i := by
  have h1 : ∏ i ∈ s, (1 - b i) = ∑ I ∈ s.powerset, (-1) ^ I.card * ∏ i ∈ I, b i := by
    simp_rw [sub_eq_add_neg]
    rw [Finset.prod_one_add]
    exact Finset.sum_congr rfl fun I _ => Finset.prod_neg _
  have h2 := Finset.sum_filter_add_sum_filter_not s.powerset Finset.Nonempty
    (fun I => (-1 : R) ^ I.card * ∏ i ∈ I, b i)
  have h3 : s.powerset.filter (fun I => ¬ I.Nonempty) = {∅} := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h3, Finset.sum_singleton] at h2
  rw [h1, ← h2]
  simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one]
  rw [sub_add_eq_sub_sub, sub_sub_cancel_left, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun I _ => by rw [pow_succ]; ring

/-- For indicators `b_i = [P i]` the left side of the inclusion–exclusion identity is the
indicator that some `i ∈ s` is bad: `1 - ∏ (1 - [P i]) = [∃ i ∈ s, P i]`. -/
theorem one_sub_prod_one_sub_ite {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (P : ι → Prop) [DecidablePred P] :
    1 - ∏ i ∈ s, (1 - (if P i then (1 : R) else 0)) = if ∃ i ∈ s, P i then 1 else 0 := by
  have h : ∀ i, (1 - (if P i then (1 : R) else 0)) = if P i then 0 else 1 := fun i => by
    by_cases hi : P i <;> simp [hi]
  simp_rw [h]
  have h2 : ∏ i ∈ s, (if P i then (0 : R) else 1) = if ∀ i ∈ s, ¬ P i then 1 else 0 := by
    rw [← Finset.prod_boole]
    exact Finset.prod_congr rfl fun i _ => by by_cases hi : P i <;> simp [hi]
  rw [h2]
  by_cases hex : ∃ i ∈ s, P i
  · have : ¬ ∀ i ∈ s, ¬ P i := by
      push Not; exact hex
    simp [hex, this]
  · have : ∀ i ∈ s, ¬ P i := by
      push Not at hex; exact hex
    have e : (if ∀ i ∈ s, ¬ P i then (1 : R) else 0) = 1 :=
      ite_eq_left_of_eq_true _ _ (eq_true this)
    rw [e]
    simp [hex]

omit [NeZero m] in
theorem walkMeets_iff_exists_fin {n : ℕ} (D : Finset (Torus d m)) (x : Torus d m)
    (w : Fin n → Fin d × Bool) :
    WalkMeets D x w ↔ ∃ k ∈ (Finset.univ : Finset (Fin (n + 1))), walkPos x w k ∈ D := by
  constructor
  · rintro ⟨k, hk, hD⟩
    exact ⟨⟨k, Finset.mem_range.1 hk⟩, Finset.mem_univ _, hD⟩
  · rintro ⟨k, -, hD⟩
    exact ⟨k, Finset.mem_range.2 k.2, hD⟩

/-- The landed loop term `tr A^n - tr A_G^n` counts the closed `n`-step walks (rooted anywhere)
that visit `D`. -/
theorem kwTraceDiff_eq_count {n : ℕ} (hn : 0 < n) :
    kwTraceDiff d m D n = ∑ x : Torus d m, ∑ w : Fin n → Fin d × Bool,
      if x + intToTorus d m (stepSum w) = x ∧ WalkMeets D x w then (1 : ℝ) else 0 := by
  unfold kwTraceDiff
  rw [kwAdj_eq_kf0Adj]
  simp only [Matrix.trace, Matrix.diag, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => kf0Adj_pow_sub_kwAdjG_pow_eq_count hn x x

/-- **Loop occupancy** (L38.5) for the loop terms: the indicator that the closed walk `w` from `x`
meets the bad set is expanded by inclusion–exclusion over the times `k ∈ {0,…,n}`,
`[w meets D] = ∑_{∅ ≠ I ⊆ {0..n}} (-1)^{|I|+1} ∏_{k ∈ I} [walkPos x w k ∈ D]`. -/
theorem kwTraceDiff_eq_inclExcl {n : ℕ} (hn : 0 < n) :
    kwTraceDiff d m D n = ∑ x : Torus d m, ∑ w : Fin n → Fin d × Bool,
      (if x + intToTorus d m (stepSum w) = x then (1 : ℝ) else 0) *
        ∑ I ∈ (Finset.univ : Finset (Fin (n + 1))).powerset.filter Finset.Nonempty,
          (-1) ^ (I.card + 1) * ∏ k ∈ I, (if walkPos x w k ∈ D then (1 : ℝ) else 0) := by
  rw [kwTraceDiff_eq_count hn]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => ?_
  rw [← one_sub_prod_one_sub_eq, one_sub_prod_one_sub_ite]
  have hiff := walkMeets_iff_exists_fin D x w
  by_cases hP : x + intToTorus d m (stepSum w) = x
  · by_cases hM : WalkMeets D x w
    · have hM' := hiff.1 hM
      simp only [hP, hM, hM', and_self, ↓reduceIte, mul_one]
    · have hM' : ¬ ∃ k ∈ (Finset.univ : Finset (Fin (n + 1))), walkPos x w k ∈ D :=
        fun h => hM (hiff.2 h)
      simp only [hP, hM, hM', and_false, ↓reduceIte, mul_zero]
  · simp [hP]

end Balaban.Green
