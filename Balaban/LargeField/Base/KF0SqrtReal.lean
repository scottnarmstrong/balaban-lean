/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0Reference
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The real inverse square root of `K_ν = -Δ + ν` on the unit torus (package K2b `KF0ProductCutoff`)

`kf0SqrtR d m ν` is the real matrix `π⁻¹ ∫₀^∞ t^{-1/2} (t + K_ν)⁻¹ dt` on `(ℤ/m)^d`, where
`K_ν = latticeLaplacian d m ν` is the real matrix of `-Δ + ν`.  For `ν > 0` it is the following.

* `kf0SqrtR_map`: its complexification is the landed `Localization.sqrtMat (kf0Op d m ν)` (the
  principal inverse square root of the complexified `K_ν`), so the latter has real entries and the
  landed entry decay transfers (`kf0SqrtR_decay`).
* `kf0SqrtR_mul_self`, `kf0SqrtR_transpose`, `kf0SqrtR_posDef`: `S * S = K_ν⁻¹`, `S` symmetric,
  `S` positive definite.  (No uniqueness of the positive square root is claimed or used.)
* `kf0SqrtR_nonneg`: all entries are nonnegative.  The resolvents `(t + K_ν)⁻¹`, `t ≥ 0`, have
  nonnegative entries (`inv_apply_nonneg_of_posDef_offDiag_nonpos`: the inverse of a positive
  definite real matrix with nonpositive off-diagonal entries is entrywise nonnegative).
* `kf0SqrtR_row_sum`: `∑_y S(x,y) = ν^{-1/2}` exactly, since `S 1 - ν^{-1/2} 1` is annihilated by
  the positive definite `S + ν^{-1/2}`.  With the sign of the entries the absolute row sum is the
  same (`kf0SqrtR_abs_row_sum`).

Uniform in the torus size `m`.  Source: `notes/phase1/LF-BASE-KF0.md` §F ((F.2), the row-sum
fact behind (F.6)); this file contains only the real square root and its elementary properties.
-/

@[expose] public section

open Matrix MeasureTheory Set
open scoped ComplexOrder

namespace Balaban.Green

section MMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive definite real matrix with nonpositive off-diagonal entries (a symmetric
M-matrix) has an entrywise nonnegative inverse. -/
theorem inv_apply_nonneg_of_posDef_offDiag_nonpos {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (hoff : ∀ i j, i ≠ j → A i j ≤ 0) (i j : ι) : 0 ≤ A⁻¹ i j := by
  set u : ι → ℝ := fun k => A⁻¹ k j with hu
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit)
  have hAu : A *ᵥ u = Pi.single j 1 := by
    funext k
    have := congrFun (congrFun hAA k) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.mulVec, dotProduct, hu, this]
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [hkj]
  set n : ι → ℝ := fun k => max (-(u k)) 0 with hn
  set p : ι → ℝ := fun k => max (u k) 0 with hp
  have hn0 : ∀ k, 0 ≤ n k := fun k => le_max_right _ _
  have hp0 : ∀ k, 0 ≤ p k := fun k => le_max_right _ _
  have hup : u = p - n := by
    funext k
    simp only [hn, hp, Pi.sub_apply]
    rcases le_total 0 (u k) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hnp : ∀ k, n k * p k = 0 := by
    intro k
    simp only [hn, hp]
    rcases le_total 0 (u k) with h | h
    · rw [max_eq_right (by linarith : -(u k) ≤ 0)]; simp
    · rw [max_eq_right h]; simp
  have h1 : n ⬝ᵥ (A *ᵥ u) = n j := by
    rw [hAu]; simp [dotProduct, Pi.single_apply]
  have h2 : n ⬝ᵥ (A *ᵥ p) ≤ 0 := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_nonpos fun k _ => Finset.sum_nonpos fun l _ => ?_
    by_cases hkl : k = l
    · subst hkl
      have : n k * (A k k * p k) = A k k * (n k * p k) := by ring
      rw [this, hnp]; simp
    · have := hoff k l hkl
      have e : n k * (A k l * p l) = A k l * (n k * p l) := by ring
      rw [e]
      exact mul_nonpos_of_nonpos_of_nonneg this (mul_nonneg (hn0 k) (hp0 l))
  have h3 : n ⬝ᵥ (A *ᵥ u) = n ⬝ᵥ (A *ᵥ p) - n ⬝ᵥ (A *ᵥ n) := by
    rw [hup, Matrix.mulVec_sub, dotProduct_sub]
  have h4 : n ⬝ᵥ (A *ᵥ n) ≤ 0 := by
    have : 0 ≤ n j := hn0 j
    linarith
  have hn_zero : n = 0 := by
    by_contra hne
    have := hA.dotProduct_mulVec_pos hne
    simp only [star_trivial] at this
    linarith
  have := congrFun hn_zero i
  simp only [hn, Pi.zero_apply] at this
  have hui : 0 ≤ u i := by
    by_contra hneg
    push Not at hneg
    rw [max_eq_left (by linarith)] at this
    linarith
  exact hui

end MMatrix

section Complexify

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The complexification of a real positive definite matrix is positive definite. -/
theorem posDef_map_ofReal {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (A.map (algebraMap ℝ ℂ)).PosDef := by
  have hsym : ∀ i j, A i j = A j i := fun i j => by
    have := hA.isHermitian.apply j i
    simpa using this
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply, hsym i j]
  · intro v hv
    set a : ι → ℝ := fun i => (v i).re with ha
    set b : ι → ℝ := fun i => (v i).im with hb
    have hterm : ∀ i j, star (v i) * ((A i j : ℂ) * v j) =
        ((A i j * (a i * a j + b i * b j) : ℝ) : ℂ) +
          ((A i j * (a i * b j - b i * a j) : ℝ) : ℂ) * Complex.I := by
      intro i j
      apply Complex.ext <;> simp [ha, hb] <;> ring
    have hQ : ∑ i, ∑ j, A i j * (a i * b j - b i * a j) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsym j i]; ring
    have key : star v ⬝ᵥ ((A.map (algebraMap ℝ ℂ)) *ᵥ v) = ((a ⬝ᵥ A *ᵥ a + b ⬝ᵥ A *ᵥ b : ℝ) : ℂ) := by
      have e1 : star v ⬝ᵥ ((A.map (algebraMap ℝ ℂ)) *ᵥ v) =
          ∑ i, ∑ j, star (v i) * ((A i j : ℂ) * v j) := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [e1]
      simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, hQ]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.ofReal_zero, zero_mul, add_zero,
        ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [key, Complex.zero_lt_real]
    have hs := hA.posSemidef
    have hnn : ∀ w : ι → ℝ, 0 ≤ w ⬝ᵥ A *ᵥ w := fun w => by
      have := hs.dotProduct_mulVec_nonneg w
      simpa using this
    by_cases ha0 : a = 0
    · have hb0 : b ≠ 0 := by
        intro hb0
        apply hv
        funext i
        apply Complex.ext
        · simpa [ha] using congrFun ha0 i
        · simpa [hb] using congrFun hb0 i
      have := hA.dotProduct_mulVec_pos hb0
      simp only [star_trivial] at this
      linarith [hnn a]
    · have := hA.dotProduct_mulVec_pos ha0
      simp only [star_trivial] at this
      linarith [hnn b]

end Complexify

section Real

variable {d m : ℕ} [NeZero m]

theorem latticeLaplacian_offDiag_nonpos (ν : ℝ) {x y : Torus d m} (hxy : x ≠ y) :
    latticeLaplacian d m ν x y ≤ 0 := by
  unfold latticeLaplacian
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.add_apply, Matrix.transpose_apply, shiftMatrix, smul_eq_mul, hxy, ite_false, mul_zero,
    zero_sub, neg_nonpos]
  refine Finset.sum_nonneg fun μ _ => ?_
  split_ifs <;> norm_num

theorem latticeLaplacian_mulVec_one (ν : ℝ) :
    latticeLaplacian d m ν *ᵥ (fun _ => (1 : ℝ)) = fun _ => ν := by
  funext x
  rw [latticeLaplacian_mulVec]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The real inverse square root `K_ν^{-1/2} = π⁻¹ ∫₀^∞ t^{-1/2} (t + K_ν)⁻¹ dt`, `K_ν = -Δ + ν`
(`latticeLaplacian d m ν`) on the torus `(ℤ/m)^d`, as a real matrix; meaningful for `ν > 0`. -/
noncomputable def kf0SqrtR (d m : ℕ) [NeZero m] (ν : ℝ) : Matrix (Torus d m) (Torus d m) ℝ :=
  Matrix.of fun x y => (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
    (((t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν)⁻¹) x y)

theorem posDef_resolvent {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    (t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν).PosDef := by
  have h1 : (t • (1 : Matrix (Torus d m) (Torus d m) ℝ)).PosSemidef :=
    (Matrix.PosSemidef.one (n := Torus d m) (R := ℝ)).smul ht
  simpa [add_comm] using (latticeLaplacian_posDef (d := d) (ℓ := m) hν).add_posSemidef h1

theorem resolvent_apply_nonneg {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x y : Torus d m) :
    0 ≤ ((t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν)⁻¹) x y := by
  refine inv_apply_nonneg_of_posDef_offDiag_nonpos (posDef_resolvent hν ht) ?_ x y
  intro i j hij
  have := latticeLaplacian_offDiag_nonpos (d := d) (m := m) ν hij
  simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hij] using this

/-- **Entries of the inverse square root are nonnegative.** -/
theorem kf0SqrtR_nonneg {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) : 0 ≤ kf0SqrtR d m ν x y := by
  unfold kf0SqrtR
  simp only [Matrix.of_apply]
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (resolvent_apply_nonneg hν (le_of_lt ht) x y)

theorem kf0SqrtR_transpose (ν : ℝ) : (kf0SqrtR d m ν)ᵀ = kf0SqrtR d m ν := by
  ext x y
  simp only [Matrix.transpose_apply, kf0SqrtR, Matrix.of_apply]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with t
  congr 1
  have hK : (latticeLaplacian d m ν)ᵀ = latticeLaplacian d m ν :=
    (latticeLaplacian_isHermitian ν).eq
  have : ((t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν)⁻¹)ᵀ =
      (t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_one, hK]
  have h := congrFun (congrFun this x) y
  simpa using h


theorem kf0Op_posDef {ν : ℝ} (hν : 0 < ν) : (kf0Op d m ν).PosDef :=
  posDef_map_ofReal (ι := L1Torus d m) (latticeLaplacian_posDef (d := d) (ℓ := m) hν)

omit [NeZero m] in
theorem map_inv_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ}
    (hB : IsUnit B.det) : (B.map (algebraMap ℝ ℂ))⁻¹ = (B⁻¹).map (algebraMap ℝ ℂ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hB]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem resolvent_complex {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    ((t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν)⁻¹ =
      (((t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν)⁻¹).map
        (algebraMap ℝ ℂ) : Matrix (L1Torus d m) (L1Torus d m) ℂ) := by
  have hB : (t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν).map
      (algebraMap ℝ ℂ) =
      (t : ℂ) • (1 : Matrix (Torus d m) (Torus d m) ℂ) +
        (latticeLaplacian d m ν).map (algebraMap ℝ ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have := map_inv_ofReal ((Matrix.isUnit_iff_isUnit_det _).1
    (posDef_resolvent (d := d) (m := m) hν ht).isUnit)
  rw [hB] at this
  exact this

/-- **Identification with the landed square root.** The complexification of `kf0SqrtR` is the
landed `Localization.sqrtMat (kf0Op d m ν)` (the principal inverse square root of the complexified
`K_ν`); in particular `sqrtMat (kf0Op)` has real entries. -/
theorem kf0SqrtR_map {ν : ℝ} (hν : 0 < ν) :
    (kf0SqrtR d m ν).map (algebraMap ℝ ℂ) =
      (Localization.sqrtMat (kf0Op d m ν) : Matrix (L1Torus d m) (L1Torus d m) ℂ) := by
  ext x y
  have e : Localization.sqrtMat (kf0Op d m ν) x y = ((1 / Real.pi : ℝ) : ℂ) *
      ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν)⁻¹) x y) := rfl
  rw [e]
  have h2 : ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((((t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν)⁻¹) x y) =
      ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
        (((t • (1 : Matrix (Torus d m) (Torus d m) ℝ) + latticeLaplacian d m ν)⁻¹) x y) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [resolvent_complex hν (le_of_lt ht)]
    simp
  rw [h2]
  simp [kf0SqrtR]

theorem kf0SqrtR_mul_self {ν : ℝ} (hν : 0 < ν) :
    kf0SqrtR d m ν * kf0SqrtR d m ν = (latticeLaplacian d m ν)⁻¹ := by
  apply Matrix.map_injective (f := algebraMap ℝ ℂ) Complex.ofReal_injective
  show (kf0SqrtR d m ν * kf0SqrtR d m ν).map (algebraMap ℝ ℂ) = ((latticeLaplacian d m ν)⁻¹).map (algebraMap ℝ ℂ)
  rw [Matrix.map_mul, kf0SqrtR_map hν]
  have : Nonempty (L1Torus d m) := ⟨(0 : Torus d m)⟩
  have h := Localization.sqrtMat_mul_self (Localization.resOK_of_posDef (kf0Op_posDef (d := d) (m := m) hν))
  rw [kf0Op_inv hν] at h
  exact h

theorem kf0SqrtR_posDef {ν : ℝ} (hν : 0 < ν) : (kf0SqrtR d m ν).PosDef := by
  have hP := kf0Op_posDef (d := d) (m := m) hν
  have hs : Localization.sqrtMat (kf0Op d m ν) = Localization.invSqrtMat hP :=
    Localization.resolvent_sqrt_eq hP
  have hC := Localization.invSqrtMat_posDef hP
  rw [← hs, ← kf0SqrtR_map hν] at hC
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · have := kf0SqrtR_transpose (d := d) (m := m) ν
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  · intro x hx
    have hxC : (fun i => (x i : ℂ)) ≠ 0 := by
      intro h0
      apply hx
      funext i
      simpa using congrFun h0 i
    have := hC.dotProduct_mulVec_pos hxC
    have e : star (fun i => (x i : ℂ)) ⬝ᵥ ((kf0SqrtR d m ν).map (algebraMap ℝ ℂ) *ᵥ fun i => (x i : ℂ)) =
        ((star x ⬝ᵥ (kf0SqrtR d m ν *ᵥ x) : ℝ) : ℂ) := by
      simp [dotProduct, Matrix.mulVec]
    exact Complex.zero_lt_real.1 (lt_of_lt_of_eq this e)


/-- **Row sums of the inverse square root** (T2): `K_ν^{-1/2} 1 = ν^{-1/2} 1` (the constant
function is an eigenvector of `-Δ + ν` with eigenvalue `ν`). -/
theorem kf0SqrtR_mulVec_one {ν : ℝ} (hν : 0 < ν) :
    kf0SqrtR d m ν *ᵥ (fun _ => (1 : ℝ)) = fun _ => (Real.sqrt ν)⁻¹ := by
  set S := kf0SqrtR d m ν with hS
  set K := latticeLaplacian d m ν with hK
  set c : ℝ := (Real.sqrt ν)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hν)
  have hc2 : c * c = ν⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hν.le]
  have hKinv : K⁻¹ *ᵥ (fun _ => (1 : ℝ)) = fun _ => ν⁻¹ := by
    have hKu : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 (latticeLaplacian_posDef hν).isUnit
    have h1 : K *ᵥ (fun _ => ν⁻¹) = fun _ => (1 : ℝ) := by
      have : (fun _ : Torus d m => ν⁻¹) = ν⁻¹ • (fun _ => (1 : ℝ)) := by
        funext x; simp
      rw [this, Matrix.mulVec_smul, hK, latticeLaplacian_mulVec_one]
      funext x; simp [hν.ne']
    calc K⁻¹ *ᵥ (fun _ => (1 : ℝ)) = K⁻¹ *ᵥ (K *ᵥ (fun _ => ν⁻¹)) := by rw [h1]
      _ = (K⁻¹ * K) *ᵥ (fun _ => ν⁻¹) := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [Matrix.nonsing_inv_mul K hKu, Matrix.one_mulVec]
  have hSS : S *ᵥ (S *ᵥ (fun _ => (1 : ℝ))) = fun _ => ν⁻¹ := by
    rw [Matrix.mulVec_mulVec, hS, kf0SqrtR_mul_self hν]; exact hKinv
  have hpd : (S + c • (1 : Matrix (Torus d m) (Torus d m) ℝ)).PosDef := by
    have h1 : (c • (1 : Matrix (Torus d m) (Torus d m) ℝ)).PosSemidef :=
      (Matrix.PosSemidef.one (n := Torus d m) (R := ℝ)).smul hc0.le
    exact (kf0SqrtR_posDef (d := d) (m := m) hν).add_posSemidef h1
  have key : (S + c • (1 : Matrix (Torus d m) (Torus d m) ℝ)) *ᵥ (S *ᵥ (fun _ => (1 : ℝ)) - fun _ => c)
      = (S + c • (1 : Matrix (Torus d m) (Torus d m) ℝ)) *ᵥ (0 : Torus d m → ℝ) := by
    rw [Matrix.mulVec_zero, Matrix.mulVec_sub, Matrix.add_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, hSS]
    funext x
    have hSc : (S *ᵥ fun _ : Torus d m => (c : ℝ)) = c • (S *ᵥ fun _ => (1 : ℝ)) := by
      rw [← Matrix.mulVec_smul]; congr 1; funext y; simp
    rw [hSc]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have := hc2
    linarith [this]
  have := hpd.mulVec_injective key
  funext x
  have hx := congrFun this x
  simp only [Pi.sub_apply, Pi.zero_apply] at hx
  linarith

/-- **Row sums** (T2): `∑_y (K_ν^{-1/2})(x,y) = ν^{-1/2}`. -/
theorem kf0SqrtR_row_sum {ν : ℝ} (hν : 0 < ν) (x : Torus d m) :
    ∑ y, kf0SqrtR d m ν x y = (Real.sqrt ν)⁻¹ := by
  have := congrFun (kf0SqrtR_mulVec_one (d := d) (m := m) hν) x
  simpa [Matrix.mulVec, dotProduct] using this

/-- **Absolute row sums** (T2): since the entries are nonnegative, `∑_y |S(x,y)| = ν^{-1/2}`. -/
theorem kf0SqrtR_abs_row_sum {ν : ℝ} (hν : 0 < ν) (x : Torus d m) :
    ∑ y, |kf0SqrtR d m ν x y| = (Real.sqrt ν)⁻¹ := by
  rw [← kf0SqrtR_row_sum hν x]
  exact Finset.sum_congr rfl fun y _ => abs_of_nonneg (kf0SqrtR_nonneg hν x y)

/-- **Entry decay transferred** from the landed bound for `sqrtMat (kf0Op)`:
`0 ≤ S(x,y) ≤ 2 g^{-1/2} exp(-r dist x y)` for `0 < g ≤ ν ≤ 1`, `r = kf0RateAt d g`. -/
theorem kf0SqrtR_decay {ν g : ℝ} (hg0 : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1) (x y : L1Torus d m) :
    kf0SqrtR d m ν x y ≤ 2 / Real.sqrt g * Real.exp (-kf0RateAt d g * dist x y) := by
  have hν : 0 < ν := lt_of_lt_of_le hg0 hgν
  have h := kf0_sqrt_decay (d := d) (m := m) hg0 hgν hν1 x y
  have e : Localization.sqrtMat (kf0Op d m ν) x y = ((kf0SqrtR d m ν x y : ℝ) : ℂ) := by
    exact (congrFun (congrFun (kf0SqrtR_map (d := d) (m := m) hν) x) y).symm
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kf0SqrtR_nonneg hν x y)] at h
  exact h


/-! ### Non-vacuity -/

/-- **Instance** (`d = 3`, `m = 3`, `ν = 1/8`): the real inverse square root exists, squares to
`K_ν⁻¹`, is positive definite with nonnegative entries and has all row sums `√8 = ν^{-1/2}`. -/
theorem kf0SqrtR_instance :
    kf0SqrtR 3 3 (1 / 8 : ℝ) * kf0SqrtR 3 3 (1 / 8 : ℝ) = (latticeLaplacian 3 3 (1 / 8 : ℝ))⁻¹ ∧
      (kf0SqrtR 3 3 (1 / 8 : ℝ)).PosDef ∧
      (∀ x y, 0 ≤ kf0SqrtR 3 3 (1 / 8 : ℝ) x y) ∧
      (∀ x : Torus 3 3, ∑ y, kf0SqrtR 3 3 (1 / 8 : ℝ) x y = Real.sqrt 8) := by
  have hν : (0 : ℝ) < 1 / 8 := by norm_num
  refine ⟨kf0SqrtR_mul_self hν, kf0SqrtR_posDef hν, kf0SqrtR_nonneg hν, fun x => ?_⟩
  rw [kf0SqrtR_row_sum hν x, one_div, Real.sqrt_inv, inv_inv]

end Real

end Balaban.Green
