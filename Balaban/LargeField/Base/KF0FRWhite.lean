/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0Gaussian
public import Balaban.Green.KF0WalkTruncation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRWhite`: whitening with a finite-range square root (route FR of `notes/phase1/KF0-FR.md`)

On the unit torus `Λ = (ℤ/m)^d` let `K = -Δ + ν` (`latticeLaplacian`), `C = K^{-1/2}` its walk
series (`kf0C`) and `C_R` the walk truncation at length `R` (`kf0CR`, Lemma H.1: entries in `[0, C]`,
range `R`, positive definite). The finite-range whitening `u = β^{-1/2} C_R ψ` turns the Gaussian
weight `exp(-(β/2)⟨u, K u⟩)` into `exp(-½|ψ|² - ½⟨ψ, Q_R ψ⟩)` with the defect `Q_R = C_R K C_R - 1`.
This file proves the facts on `Q_R` used by the polymer expansion:

* `kf0C_lap_kf0C`: `C K C = 1` (the full square root whitens exactly);
* `frQ_eq`: `Q_R = (C_R - C) K C_R + C K (C_R - C)`;
* `frQ_eq_zero_of_lt`: `Q_R(x,y) = 0` when the `ℓ¹` torus distance exceeds `2R + 1` (finite range);
* `frQ_rowAbs_le`: `∑_y |Q_R(x,y)| ≤ 2 (4d + ν) ν^{-1/2} τ_R`, `τ_R = (2d+ν)^{-1/2} q^{R+1}/(1-q)`,
  `q = 2d/(2d+ν)` (the defect is small for `R` large);
* `tangentQuad_matAct_gen`: `⟨Sψ, K Sψ⟩ = ∑_i ψ_iᵀ (Sᵀ K S) ψ_i` for tangent fields, the identity
  behind the change of variables.
-/

@[expose] public section

namespace Balaban.LargeField.KF0FR

open Matrix Balaban.Green Balaban.LargeField.SphereChart

variable {d m : ℕ} [NeZero m]

/-- The defect of the finite-range whitening, `Q_R = C_R K C_R - 1`. -/
noncomputable def frQ (d m : ℕ) [NeZero m] (ν : ℝ) (R : ℕ) : Matrix (Torus d m) (Torus d m) ℝ :=
  kf0CR d m ν R * latticeLaplacian d m ν * kf0CR d m ν R - 1

/-- **The full square root whitens exactly**: `C K C = 1`, since `C² = K⁻¹` and `C` commutes with
`C² = K⁻¹`, hence with `K`. -/
theorem kf0C_lap_kf0C {ν : ℝ} (hν : 0 < ν) :
    kf0C d m ν * latticeLaplacian d m ν * kf0C d m ν = 1 := by
  set C := kf0C d m ν
  set K := latticeLaplacian d m ν
  have hKu : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 (latticeLaplacian_posDef hν).isUnit
  have hCC : C * C = K⁻¹ := kf0C_mul_self hν
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K hKu
  have hKK' : K⁻¹ * K = 1 := Matrix.nonsing_inv_mul K hKu
  -- `C` commutes with `K⁻¹ = C * C`
  have hcomm : C * K⁻¹ = K⁻¹ * C := by rw [← hCC, Matrix.mul_assoc]
  -- hence with `K`
  have hcommK : C * K = K * C := by
    calc C * K = (K * K⁻¹) * (C * K) := by rw [hKK, Matrix.one_mul]
      _ = K * (K⁻¹ * C) * K := by simp only [Matrix.mul_assoc]
      _ = K * (C * K⁻¹) * K := by rw [hcomm]
      _ = K * C * (K⁻¹ * K) := by simp only [Matrix.mul_assoc]
      _ = K * C := by rw [hKK', Matrix.mul_one]
  rw [hcommK, Matrix.mul_assoc, hCC, hKK]

/-- `Q_R = (C_R - C) K C_R + C K (C_R - C)`. -/
theorem frQ_eq {ν : ℝ} (hν : 0 < ν) (R : ℕ) :
    frQ d m ν R = (kf0CR d m ν R - kf0C d m ν) * latticeLaplacian d m ν * kf0CR d m ν R +
      kf0C d m ν * latticeLaplacian d m ν * (kf0CR d m ν R - kf0C d m ν) := by
  unfold frQ
  rw [← kf0C_lap_kf0C (d := d) (m := m) hν]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem frQ_symm (ν : ℝ) (R : ℕ) (x y : Torus d m) : frQ d m ν R x y = frQ d m ν R y x := by
  have hC : (kf0CR d m ν R)ᵀ = kf0CR d m ν R := by
    ext a b; exact kf0CR_symm ν R b a
  have hK : (latticeLaplacian d m ν)ᵀ = latticeLaplacian d m ν :=
    (latticeLaplacian_isHermitian (d := d) (ℓ := m) ν).eq
  have hQ : (frQ d m ν R)ᵀ = frQ d m ν R := by
    unfold frQ
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hC, hK,
      Matrix.transpose_one, Matrix.mul_assoc]
  exact (congrFun (congrFun hQ y) x)

/-! ### Finite range -/

theorem kf0CR_ne_zero_dist {ν : ℝ} {R : ℕ} {x y : Torus d m} (h : kf0CR d m ν R x y ≠ 0) :
    torusDist d m x y ≤ R := by
  by_contra hlt
  exact h (kf0CR_eq_zero_of_lt (not_le.1 hlt))

/-- **Finite range of the defect**: `Q_R(x,y) = 0` when `|x - y|₁ > 2R + 1`. -/
theorem frQ_eq_zero_of_lt {ν : ℝ} {R : ℕ} {x y : Torus d m}
    (h : (2 * R + 1 : ℝ) < torusDist d m x y) : frQ d m ν R x y = 0 := by
  have hxy : x ≠ y := by
    rintro rfl
    have : torusDist d m x x = 0 := dist_self (show L1Torus d m from x)
    rw [this] at h
    linarith
  unfold frQ
  rw [Matrix.sub_apply, Matrix.one_apply_ne hxy, sub_zero, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_contra hne
  have h1 : kf0CR d m ν R x z ≠ 0 := fun h0 => hne (by rw [h0]; ring)
  have h2 : latticeLaplacian d m ν z w ≠ 0 := fun h0 => hne (by rw [h0]; ring)
  have h3 : kf0CR d m ν R w y ≠ 0 := fun h0 => hne (by rw [h0]; ring)
  have d1 := kf0CR_ne_zero_dist h1
  have d2 := torusDist_le_one_of_ne_zero h2
  have d3 := kf0CR_ne_zero_dist h3
  have t1 : torusDist d m x y ≤ torusDist d m x z + torusDist d m z y :=
    dist_triangle (show L1Torus d m from x) (show L1Torus d m from z) (show L1Torus d m from y)
  have t2 : torusDist d m z y ≤ torusDist d m z w + torusDist d m w y :=
    dist_triangle (show L1Torus d m from z) (show L1Torus d m from w) (show L1Torus d m from y)
  linarith

/-! ### Row sums of absolute values -/

/-- Row sums of the absolute values of a product. -/
theorem rowAbs_mul_le {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℝ) {b : ℝ}
    (hB : ∀ z, ∑ y, |B z y| ≤ b) (x : ι) :
    ∑ y, |(A * B) x y| ≤ (∑ z, |A x z|) * b := by
  calc ∑ y, |(A * B) x y| = ∑ y, |∑ z, A x z * B z y| := by simp [Matrix.mul_apply]
    _ ≤ ∑ y, ∑ z, |A x z| * |B z y| := Finset.sum_le_sum fun y _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by simp [abs_mul]))
    _ = ∑ z, |A x z| * ∑ y, |B z y| := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
    _ ≤ ∑ z, |A x z| * b := Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
    _ = (∑ z, |A x z|) * b := by rw [Finset.sum_mul]

theorem lap_rowAbs_le {ν : ℝ} (hν : 0 ≤ ν) (x : Torus d m) :
    ∑ y, |latticeLaplacian d m ν x y| ≤ 4 * d + ν := by
  have hK : latticeLaplacian d m ν = (2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) -
      kf0Adj d m := by rw [kf0Adj_eq ν]; abel
  have hpt : ∀ y, |latticeLaplacian d m ν x y| ≤
      (2 * d + ν) * (1 : Matrix (Torus d m) (Torus d m) ℝ) x y + kf0Adj d m x y := by
    intro y
    rw [hK, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (le_of_eq ?_) (le_of_eq (abs_of_nonneg (kf0Adj_nonneg x y))))
    rw [abs_of_nonneg]
    exact mul_nonneg (by positivity) (by rw [Matrix.one_apply]; split_ifs <;> norm_num)
  calc ∑ y, |latticeLaplacian d m ν x y|
      ≤ ∑ y, ((2 * d + ν) * (1 : Matrix (Torus d m) (Torus d m) ℝ) x y + kf0Adj d m x y) :=
        Finset.sum_le_sum fun y _ => hpt y
    _ = (2 * d + ν) + 2 * d := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, kf0Adj_rowSum]
        simp [Matrix.one_apply]
    _ = 4 * d + ν := by ring

theorem kf0CR_rowAbs_le {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x : Torus d m) :
    ∑ y, |kf0CR d m ν R x y| ≤ (Real.sqrt ν)⁻¹ := by
  simp_rw [abs_of_nonneg (kf0CR_nonneg hν R x _)]
  exact kf0CR_rowSum_le hν R x

theorem kf0C_rowAbs_eq {ν : ℝ} (hν : 0 < ν) (x : Torus d m) :
    ∑ y, |kf0C d m ν x y| = (Real.sqrt ν)⁻¹ := by
  simp_rw [abs_of_nonneg (kf0C_nonneg hν x _)]
  exact kf0C_rowSum hν x

/-- The walk tail `τ_R = (2d+ν)^{-1/2} q^{R+1}/(1-q)`, `q = 2d/(2d+ν)`. -/
noncomputable def frTail (d : ℕ) (ν : ℝ) (R : ℕ) : ℝ :=
  (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) / (1 - 2 * d / (2 * d + ν))

theorem kf0CR_sub_rowAbs_le {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x : Torus d m) :
    ∑ y, |(kf0CR d m ν R - kf0C d m ν) x y| ≤ frTail d ν R := by
  have e : ∀ y, |(kf0CR d m ν R - kf0C d m ν) x y| = kf0C d m ν x y - kf0CR d m ν R x y := by
    intro y
    rw [Matrix.sub_apply, abs_sub_comm, abs_of_nonneg (kf0C_sub_kf0CR hν R x y).1]
  simp_rw [e]
  exact (kf0C_sub_kf0CR_rowSum hν R x).2

/-- **The defect is small**: `∑_y |Q_R(x,y)| ≤ 2 (4d + ν) ν^{-1/2} τ_R`. -/
theorem frQ_rowAbs_le {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x : Torus d m) :
    ∑ y, |frQ d m ν R x y| ≤ 2 * (4 * d + ν) * (Real.sqrt ν)⁻¹ * frTail d ν R := by
  have hτ : 0 ≤ frTail d ν R := by
    have : 0 ≤ ∑ y, |(kf0CR d m ν R - kf0C d m ν) x y| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact this.trans (kf0CR_sub_rowAbs_le hν R x)
  have hs : 0 ≤ (Real.sqrt ν)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [frQ_eq hν R]
  have h1 : ∀ z, ∑ y, |(latticeLaplacian d m ν * kf0CR d m ν R) z y| ≤
      (4 * d + ν) * (Real.sqrt ν)⁻¹ := fun z =>
    (rowAbs_mul_le _ _ (kf0CR_rowAbs_le hν R) z).trans
      (mul_le_mul_of_nonneg_right (lap_rowAbs_le hν.le z) hs)
  have h2 : ∀ z, ∑ y, |(latticeLaplacian d m ν * (kf0CR d m ν R - kf0C d m ν)) z y| ≤
      (4 * d + ν) * frTail d ν R := fun z =>
    (rowAbs_mul_le _ _ (kf0CR_sub_rowAbs_le hν R) z).trans
      (mul_le_mul_of_nonneg_right (lap_rowAbs_le hν.le z) hτ)
  have a1 : ∑ y, |((kf0CR d m ν R - kf0C d m ν) * latticeLaplacian d m ν * kf0CR d m ν R) x y| ≤
      frTail d ν R * ((4 * d + ν) * (Real.sqrt ν)⁻¹) := by
    rw [Matrix.mul_assoc]
    exact (rowAbs_mul_le _ _ h1 x).trans
      (mul_le_mul_of_nonneg_right (kf0CR_sub_rowAbs_le hν R x) (by positivity))
  have a2 : ∑ y, |(kf0C d m ν * latticeLaplacian d m ν * (kf0CR d m ν R - kf0C d m ν)) x y| ≤
      (Real.sqrt ν)⁻¹ * ((4 * d + ν) * frTail d ν R) := by
    rw [Matrix.mul_assoc]
    exact (rowAbs_mul_le _ _ h2 x).trans
      (mul_le_mul_of_nonneg_right (le_of_eq (kf0C_rowAbs_eq hν x)) (by positivity))
  calc ∑ y, |(((kf0CR d m ν R - kf0C d m ν) * latticeLaplacian d m ν * kf0CR d m ν R) +
        (kf0C d m ν * latticeLaplacian d m ν * (kf0CR d m ν R - kf0C d m ν))) x y|
      ≤ ∑ y, (|((kf0CR d m ν R - kf0C d m ν) * latticeLaplacian d m ν * kf0CR d m ν R) x y| +
          |(kf0C d m ν * latticeLaplacian d m ν * (kf0CR d m ν R - kf0C d m ν)) x y|) :=
        Finset.sum_le_sum fun y _ => by rw [Matrix.add_apply]; exact abs_add_le _ _
    _ ≤ frTail d ν R * ((4 * d + ν) * (Real.sqrt ν)⁻¹) +
          (Real.sqrt ν)⁻¹ * ((4 * d + ν) * frTail d ν R) := by
        rw [Finset.sum_add_distrib]; exact add_le_add a1 a2
    _ = 2 * (4 * d + ν) * (Real.sqrt ν)⁻¹ * frTail d ν R := by ring

/-! ### The quadratic form in the whitened variables -/

variable {N : ℕ} {h : EuclideanSpace ℝ (Fin N)}

/-- The `i`-th coordinate field of a tangent field. -/
noncomputable def coordField (ψ : Torus d m → perp h) (i : Fin N) : Torus d m → ℝ :=
  fun y => ((ψ y : perp h) : EuclideanSpace ℝ (Fin N)) i

/-- **The Gaussian form after a linear change of the site index**: for any matrix `S`,
`⟨Sψ, K Sψ⟩ = ∑_i ψ_iᵀ (Sᵀ K S) ψ_i` on tangent fields. -/
theorem tangentQuad_matAct_gen (ν : ℝ) (S : Matrix (Torus d m) (Torus d m) ℝ)
    (ψ : Torus d m → perp h) :
    tangentQuad ν (matAct S ψ) =
      ∑ i : Fin N, coordField ψ i ⬝ᵥ (Sᵀ * latticeLaplacian d m ν * S) *ᵥ coordField ψ i := by
  unfold tangentQuad
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoord : (fun x => ((matAct S ψ x : perp h) : EuclideanSpace ℝ (Fin N)) i) =
      S *ᵥ coordField ψ i := by
    funext x; exact coord_matAct S ψ x i
  rw [hcoord]
  have hT : ∀ u : Torus d m → ℝ, (S *ᵥ coordField ψ i) ⬝ᵥ u = coordField ψ i ⬝ᵥ (Sᵀ *ᵥ u) :=
    fun u => by rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- `∑_i ψ_iᵀ M ψ_i = ∑_{x,y} M(x,y) ⟨ψ_x, ψ_y⟩`. -/
theorem sum_coord_form (M : Matrix (Torus d m) (Torus d m) ℝ) (ψ : Torus d m → perp h) :
    ∑ i : Fin N, coordField ψ i ⬝ᵥ M *ᵥ coordField ψ i =
      ∑ x, ∑ y, M x y * inner ℝ (ψ x : EuclideanSpace ℝ (Fin N)) (ψ y : EuclideanSpace ℝ (Fin N)) := by
  have hin : ∀ x y : Torus d m, inner ℝ (ψ x : EuclideanSpace ℝ (Fin N)) (ψ y : EuclideanSpace ℝ (Fin N)) =
      ∑ i : Fin N, coordField ψ i x * coordField ψ i y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [coordField, dotProduct, mul_comm]
  simp_rw [hin, Finset.mul_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∑_i |ψ_i|² = ∑_x ‖ψ_x‖²`. -/
theorem sum_coord_sq (ψ : Torus d m → perp h) :
    ∑ i : Fin N, coordField ψ i ⬝ᵥ coordField ψ i = ∑ x, ‖ψ x‖ ^ 2 := by
  have hn : ∀ u : perp h, ‖u‖ ^ 2 = ∑ i : Fin N, ((u : EuclideanSpace ℝ (Fin N)) i) ^ 2 := by
    intro u
    rw [← norm_coe_perp, EuclideanSpace.norm_sq_eq]
    simp
  simp_rw [hn]
  simp only [dotProduct, coordField]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring

/-- The whitened field `u = β^{-1/2} C_R ψ`. -/
noncomputable def frField (d m : ℕ) [NeZero m] (β ν : ℝ) (R : ℕ) (ψ : Torus d m → perp h) :
    Torus d m → perp h :=
  matAct ((Real.sqrt β)⁻¹ • kf0CR d m ν R) ψ

/-- **The Gaussian weight in the whitened variables**: with `u = β^{-1/2} C_R ψ`,
`β ⟨u, K u⟩ = ∑_x ‖ψ_x‖² + ∑_{x,y} Q_R(x,y) ⟨ψ_x, ψ_y⟩`. -/
theorem tangentQuad_frField {β : ℝ} (hβ : 0 < β) (ν : ℝ) (R : ℕ) (ψ : Torus d m → perp h) :
    β * tangentQuad ν (frField d m β ν R ψ) =
      ∑ x, ‖ψ x‖ ^ 2 + ∑ x, ∑ y, frQ d m ν R x y *
        inner ℝ (ψ x : EuclideanSpace ℝ (Fin N)) (ψ y : EuclideanSpace ℝ (Fin N)) := by
  have hC : (kf0CR d m ν R)ᵀ = kf0CR d m ν R := by
    ext a b; exact kf0CR_symm ν R b a
  have hS : ((Real.sqrt β)⁻¹ • kf0CR d m ν R)ᵀ * latticeLaplacian d m ν *
      ((Real.sqrt β)⁻¹ • kf0CR d m ν R) = β⁻¹ • (1 + frQ d m ν R) := by
    rw [Matrix.transpose_smul, hC, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hb : (Real.sqrt β)⁻¹ * (Real.sqrt β)⁻¹ = β⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hβ.le]
    rw [hb]
    unfold frQ
    abel_nf
  unfold frField
  rw [tangentQuad_matAct_gen, hS]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Finset.mul_sum]
  rw [← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, Finset.sum_add_distrib]
  rw [sum_coord_sq, sum_coord_form]

end Balaban.LargeField.KF0FR
