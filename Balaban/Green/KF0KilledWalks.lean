/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0Reference
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Dirichlet-type good-region operator and its killed-walk expansion (package H37-3, part 1)

For a set `D` of sites of the torus `(ℤ/mℤ)^d` (the bad sites) and `G = Dᶜ`, the good-region
operator of the one-scale problem is the principal submatrix `K_G` of `K_Λ = -Δ + ν`
(`latticeLaplacian d m ν`) on `G`; `K_G = a_ν 1_G - A_G` with `a_ν = 2d + ν`, `A_G` the nearest
neighbour adjacency matrix restricted to `G`.  Every bond from a site of `G` to a site of `D`
contributes to the diagonal through `a_ν = 2d + ν`.

These are facts about the Dirichlet-type reference operator on a region with holes.  The
conditional integral with boundary data, the linked expansion and Root-F are NOT treated here.

## Representations

* `kwOp d m ν D` is the *padded* form: a matrix on the whole torus equal to `K_Λ` on `G × G`,
  to `a_ν` on the diagonal of `D`, and to `0` elsewhere (rows and columns of `D` of the adjacency
  matrix are removed, `kwAdjG`).  Its inverse is `K_G⁻¹` on `G` and `a_ν⁻¹` on `D`.
  The padded form is used for the walk expansion, the decay and locality statements, and for the
  trace calculus of `KF0DetWalks`.
* `kwOpSub d m ν D` is the principal submatrix on the subtype `{x // x ∉ D}` (the literal `K_G`);
  `kwOp_det` relates the two: `det (kwOp) = a_ν^{|D|} det (kwOpSub)`.

## Main results

* `kwOp_form_ge`: `⟨u, K_G u⟩ = ⟨ũ, K_Λ ũ⟩ ≥ ∑_{x∈G} (D_∂(x) + ν) u_x²` for `u` vanishing on `D`
  (`D_∂(x) = ∑_{y∈D} A(x,y)`).
* `kwOp_inv_hasSum`: `K_G⁻¹ = ∑_n a_ν^{-(n+1)} A_G^n` entrywise, with nonnegative entries
  (`kwOp_inv_nonneg`), row sums at most `1/ν` (`kwOp_inv_rowSum_le`), and `K_G⁻¹ ≤ K_Λ⁻¹`
  (`kwOp_inv_le_full`).
* `kwOp_inv_mulVec_decay`: inward decay `|(K_G⁻¹ J)(x)| ≤ (B/ν) q^t`, `q = 2d/(2d+ν)`, when `J`
  vanishes at all sites at `ℓ¹` torus distance `< t` from `x` and `|J| ≤ B`.
* `kwAdjG_pow_locality`: the `n`-th walk term at `x` depends only on `D ∩ ball(x, n)`;
  `kwTrunc_tail_rowSum_le`: the truncation at length `R` has row tail at most `q^R/ν`, and its
  entries vanish at distance `≥ R`.
-/

@[expose] public section

open Matrix Finset Balaban.Green

namespace Balaban

namespace KW

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pow_entry_nonneg {M : Matrix ι ι ℝ} (hM : ∀ x y, 0 ≤ M x y) (n : ℕ) (x y : ι) :
    0 ≤ (M ^ n) x y := by
  induction n generalizing x y with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih _ _) (hM _ _)

theorem pow_rowSum_le {M : Matrix ι ι ℝ} {r : ℝ} (hM : ∀ x y, 0 ≤ M x y) (hr : 0 ≤ r)
    (hrow : ∀ x, ∑ y, M x y ≤ r) (n : ℕ) (x : ι) : ∑ y, (M ^ n) x y ≤ r ^ n := by
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true, le_refl]
  | succ n ih =>
    simp_rw [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc ∑ z, ∑ y, M x z * (M ^ n) z y = ∑ z, M x z * ∑ y, (M ^ n) z y := by
          simp_rw [← Finset.mul_sum]
      _ ≤ ∑ z, M x z * r ^ n :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ih z) (hM _ _)
      _ = (∑ z, M x z) * r ^ n := by rw [Finset.sum_mul]
      _ ≤ r * r ^ n := mul_le_mul_of_nonneg_right (hrow x) (by positivity)

theorem pow_entry_mono {A B : Matrix ι ι ℝ} (hB : ∀ x y, 0 ≤ B x y) (hAB : ∀ x y, B x y ≤ A x y)
    (n : ℕ) (x y : ι) : (B ^ n) x y ≤ (A ^ n) x y := by
  have hA : ∀ x y, 0 ≤ A x y := fun x y => (hB x y).trans (hAB x y)
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_le_sum fun z _ =>
      mul_le_mul (ih _ _) (hAB _ _) (hB _ _) (pow_entry_nonneg hA n _ _)

/-- Eigenvalue bound of a symmetric matrix from its absolute row sums. -/
theorem abs_eigenvalue_le {T : Matrix ι ι ℝ} (hT : T.IsHermitian) {q : ℝ}
    (hrow : ∀ x, ∑ y, |T x y| ≤ q) (i : ι) : |hT.eigenvalues i| ≤ q := by
  set v : ι → ℝ := ⇑(hT.eigenvectorBasis i) with hv
  have hev : T *ᵥ v = hT.eigenvalues i • v := hT.mulVec_eigenvectorBasis i
  have hne : v ≠ 0 := by
    intro h0
    have h1 := hT.eigenvectorBasis.orthonormal.1 i
    have h2 : (hT.eigenvectorBasis i) = 0 := by
      ext j; exact congrFun h0 j
    simp [h2] at h1
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ (fun y => |v y|) ⟨i, Finset.mem_univ _⟩
  have hvx : 0 < |v x| := by
    by_contra hcon
    apply hne
    funext y
    have := hx y (Finset.mem_univ _)
    have h0 : |v x| = 0 := le_antisymm (not_lt.1 hcon) (abs_nonneg _)
    have : |v y| ≤ 0 := h0 ▸ this
    exact abs_nonpos_iff.1 this
  have hx' := congrFun hev x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx'
  have : |hT.eigenvalues i| * |v x| ≤ q * |v x| := by
    calc |hT.eigenvalues i| * |v x| = |∑ y, T x y * v y| := by rw [hx', abs_mul]
      _ ≤ ∑ y, |T x y * v y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |T x y| * |v x| := Finset.sum_le_sum fun y _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx y (Finset.mem_univ _)) (abs_nonneg _)
      _ = (∑ y, |T x y|) * |v x| := by rw [Finset.sum_mul]
      _ ≤ q * |v x| := mul_le_mul_of_nonneg_right (hrow x) hvx.le
  exact le_of_mul_le_mul_right this hvx

/-- `log det (1 - T) = -∑_{n ≥ 1} tr(T^n)/n` for a symmetric `T` with absolute row sums at most
`q < 1`; in particular `det (1 - T) > 0`. -/
theorem logdet_series {T : Matrix ι ι ℝ} (hT : T.IsHermitian) {q : ℝ} (hq : q < 1)
    (hrow : ∀ x, ∑ y, |T x y| ≤ q) :
    0 < (1 - T).det ∧
      HasSum (fun n : ℕ => (T ^ (n + 1)).trace / ((n : ℝ) + 1)) (-Real.log (1 - T).det) := by
  have hev := abs_eigenvalue_le hT hrow
  have hlt : ∀ i, |hT.eigenvalues i| < 1 := fun i => (hev i).trans_lt hq
  set U : Matrix ι ι ℝ := (hT.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set D : Matrix ι ι ℝ := diagonal hT.eigenvalues with hD
  have hspec : T = U * D * star U := by
    have := hT.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD] using this
  have hpow : ∀ n : ℕ, T ^ n = U * D ^ n * star U := by
    intro n
    induction n with
    | zero => simp [hUU']
    | succ n ih =>
      rw [pow_succ, ih]
      conv_lhs => rw [hspec]
      calc U * D ^ n * star U * (U * D * star U) = U * D ^ n * (star U * U) * D * star U := by
            simp only [Matrix.mul_assoc]
        _ = U * D ^ (n + 1) * star U := by
            rw [hUU, Matrix.mul_one, pow_succ]; simp only [Matrix.mul_assoc]
  have hone : 1 - T = U * (1 - D) * star U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU', ← hspec]
  have hdet : (1 - T).det = ∏ i, (1 - hT.eigenvalues i) := by
    rw [hone, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hUU,
      Matrix.det_one]
    have : (1 - D) = diagonal (fun i => 1 - hT.eigenvalues i) := by
      rw [hD, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    rw [this, Matrix.det_diagonal, one_mul]
  have htr : ∀ n : ℕ, (T ^ n).trace = ∑ i, hT.eigenvalues i ^ n := by
    intro n
    rw [hpow, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, hD, diagonal_pow,
      Matrix.trace_diagonal]
    rfl
  have hpos : ∀ i, 0 < 1 - hT.eigenvalues i := fun i => by
    have := (abs_lt.1 (hlt i)).2; linarith
  have hdpos : 0 < (1 - T).det := by rw [hdet]; exact Finset.prod_pos fun i _ => hpos i
  refine ⟨hdpos, ?_⟩
  have hs := hasSum_sum (s := Finset.univ)
    (fun i _ => Real.hasSum_pow_div_log_of_abs_lt_one (hlt i))
  have e1 : ∑ i, -Real.log (1 - hT.eigenvalues i) = -Real.log (1 - T).det := by
    rw [hdet, Real.log_prod (fun i _ => (hpos i).ne'), Finset.sum_neg_distrib]
  rw [e1] at hs
  convert hs using 1
  funext n
  rw [htr, Finset.sum_div]

end Generic

end KW

variable {d m : ℕ} [NeZero m]

/-! ### The adjacency matrix, the killed adjacency matrix and the two forms of `K_G` -/

/-- The nearest-neighbour adjacency matrix of the torus (with adjacency multiplicity):
`A = ∑_μ (S_μ + S_μᵀ)`, so that `-Δ + ν = (2d + ν) 1 - A` (`latticeLaplacian_eq_kwAdj`).
(Also defined, under another name, by the parallel file `KF0WalkSeries`; duplication noted.) -/
def kwAdj (d m : ℕ) [NeZero m] : Matrix (Torus d m) (Torus d m) ℝ :=
  ∑ μ : Fin d, (shiftMatrix μ + (shiftMatrix μ)ᵀ)

/-- The killed adjacency matrix: the adjacency matrix with the rows and columns of the bad sites
`D` removed (walks killed on leaving `G = Dᶜ`). -/
def kwAdjG (d m : ℕ) [NeZero m] (D : Finset (Torus d m)) : Matrix (Torus d m) (Torus d m) ℝ :=
  Matrix.of fun x y => if x ∈ D ∨ y ∈ D then 0 else kwAdj d m x y

/-- The padded good-region operator `a_ν 1 - A_G` on the whole torus. -/
def kwOp (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ)) - kwAdjG d m D

/-- The good-region operator as the principal submatrix of `-Δ + ν` on the subtype `G = Dᶜ`. -/
def kwOpSub (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) :
    Matrix {x : Torus d m // x ∉ D} {x : Torus d m // x ∉ D} ℝ :=
  (latticeLaplacian d m ν).submatrix Subtype.val Subtype.val

/-- The crossing degree `D_∂(x) = ∑_{y ∈ D} A(x, y)` (number of bonds from `x` to `D`). -/
def kwBdry (d m : ℕ) [NeZero m] (D : Finset (Torus d m)) (x : Torus d m) : ℝ :=
  ∑ y ∈ D, kwAdj d m x y

theorem latticeLaplacian_eq_kwAdj (ν : ℝ) :
    latticeLaplacian d m ν = ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ)) - kwAdj d m :=
  rfl

theorem kwAdj_apply (x y : Torus d m) :
    kwAdj d m x y = ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then 1 else 0)) := by
  simp [kwAdj, Matrix.sum_apply, shiftMatrix]

theorem kwAdj_nonneg (x y : Torus d m) : 0 ≤ kwAdj d m x y := by
  rw [kwAdj_apply]
  exact Finset.sum_nonneg fun μ _ => add_nonneg (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num)

theorem kwAdj_symm (x y : Torus d m) : kwAdj d m x y = kwAdj d m y x := by
  rw [kwAdj_apply, kwAdj_apply]
  exact Finset.sum_congr rfl fun μ _ => add_comm _ _

theorem kwAdj_rowSum (x : Torus d m) : ∑ y, kwAdj d m x y = 2 * d := by
  simp_rw [kwAdj_apply]
  rw [Finset.sum_comm]
  have h1 : ∀ μ : Fin d, ∑ y : Torus d m, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then 1 else 0)) = 2 := by
    intro μ
    rw [Finset.sum_add_distrib]
    have e2 : ∀ y : Torus d m, (x = y + Pi.single μ 1) ↔ (y = x - Pi.single μ 1) := fun y => by
      rw [eq_sub_iff_add_eq, eq_comm]
    simp only [e2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    norm_num
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem kwAdjG_nonneg (D : Finset (Torus d m)) (x y : Torus d m) : 0 ≤ kwAdjG d m D x y := by
  simp only [kwAdjG, Matrix.of_apply]
  split_ifs
  · exact le_refl _
  · exact kwAdj_nonneg x y

theorem kwAdjG_le (D : Finset (Torus d m)) (x y : Torus d m) : kwAdjG d m D x y ≤ kwAdj d m x y := by
  simp only [kwAdjG, Matrix.of_apply]
  split_ifs
  · exact kwAdj_nonneg x y
  · exact le_refl _

theorem kwAdjG_symm (D : Finset (Torus d m)) (x y : Torus d m) :
    kwAdjG d m D x y = kwAdjG d m D y x := by
  simp only [kwAdjG, Matrix.of_apply, kwAdj_symm x y, or_comm]

theorem kwAdjG_rowSum_le (D : Finset (Torus d m)) (x : Torus d m) :
    ∑ y, kwAdjG d m D x y ≤ 2 * d := by
  rw [← kwAdj_rowSum x]
  exact Finset.sum_le_sum fun y _ => kwAdjG_le D x y

theorem kwAdjG_empty : kwAdjG d m (∅ : Finset (Torus d m)) = kwAdj d m := by
  ext x y; simp [kwAdjG]

theorem kwOp_empty (ν : ℝ) : kwOp d m ν (∅ : Finset (Torus d m)) = latticeLaplacian d m ν := by
  rw [kwOp, kwAdjG_empty]; rfl

theorem kwOp_apply (ν : ℝ) (D : Finset (Torus d m)) (x y : Torus d m) :
    kwOp d m ν D x y = (if x = y then 2 * d + ν else 0) - kwAdjG d m D x y := by
  simp [kwOp, Matrix.one_apply]

/-- On `G × G` the padded operator is `-Δ + ν`. -/
theorem kwOp_apply_of_mem (ν : ℝ) {D : Finset (Torus d m)} {x y : Torus d m} (hx : x ∉ D)
    (hy : y ∉ D) : kwOp d m ν D x y = latticeLaplacian d m ν x y := by
  simp [kwOp, kwAdjG, hx, hy, latticeLaplacian_eq_kwAdj]

/-- The padded operator on the diagonal of `D` is `a_ν`, and has no other entries in `D` rows. -/
theorem kwOp_apply_of_mem_left (ν : ℝ) {D : Finset (Torus d m)} {x : Torus d m} (hx : x ∈ D)
    (y : Torus d m) : kwOp d m ν D x y = if x = y then 2 * d + ν else 0 := by
  simp [kwOp_apply, kwAdjG, hx]

theorem kwOpSub_apply (ν : ℝ) (D : Finset (Torus d m)) (x y : {x : Torus d m // x ∉ D}) :
    kwOpSub d m ν D x y = latticeLaplacian d m ν x y := rfl

/-- The padded operator is block diagonal for `G ⊕ D`, with blocks `K_G` and `a_ν 1_D`; hence
`det (kwOp) = a_ν^{|D|} det (kwOpSub)`. -/
theorem kwOp_det (ν : ℝ) (D : Finset (Torus d m)) :
    (kwOp d m ν D).det = (2 * d + ν) ^ D.card * (kwOpSub d m ν D).det := by
  classical
  let e := Equiv.sumCompl (fun x : Torus d m => x ∉ D)
  have hblock : (kwOp d m ν D).submatrix e e =
      Matrix.fromBlocks (kwOpSub d m ν D) 0 0
        ((2 * d + ν) • (1 : Matrix {x : Torus d m // ¬ x ∉ D} {x : Torus d m // ¬ x ∉ D} ℝ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [e, kwOpSub_apply, kwOp_apply_of_mem ν i.2 j.2]
    · have hj : (j : Torus d m) ∈ D := not_not.1 j.2
      have : (i : Torus d m) ≠ j := fun h => i.2 (h ▸ hj)
      simp [e, kwOp_apply, kwAdjG, hj, this]
    · have hi : (i : Torus d m) ∈ D := not_not.1 i.2
      have : (i : Torus d m) ≠ j := fun h => j.2 (h ▸ hi)
      simp [e, kwOp_apply, kwAdjG, hi, this]
    · have hi : (i : Torus d m) ∈ D := not_not.1 i.2
      simp [e, kwOp_apply, kwAdjG, hi, Matrix.one_apply, Subtype.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self e, hblock, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_one, mul_one, mul_comm]
  congr 2
  simp only [Fintype.card_subtype, not_not]
  congr 1
  ext x; simp

/-! ### T1: the quadratic form and the lower bound `K_G ≥ D_∂ + ν` -/

theorem kwAdjG_form_eq (D : Finset (Torus d m)) {u : Torus d m → ℝ} (hu : ∀ x ∈ D, u x = 0) :
    u ⬝ᵥ kwAdjG d m D *ᵥ u = u ⬝ᵥ kwAdj d m *ᵥ u := by
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : x ∈ D ∨ y ∈ D
  · rcases h with h | h
    · simp [hu x h]
    · simp [hu y h]
  · simp [kwAdjG, h]

/-- `⟨u, K_G u⟩ = ⟨ũ, K_Λ ũ⟩` for `u` vanishing on `D` (the extension by zero). -/
theorem kwOp_form (ν : ℝ) (D : Finset (Torus d m)) {u : Torus d m → ℝ}
    (hu : ∀ x ∈ D, u x = 0) :
    u ⬝ᵥ kwOp d m ν D *ᵥ u = u ⬝ᵥ latticeLaplacian d m ν *ᵥ u := by
  have h := kwAdjG_form_eq D hu
  simp only [kwOp, latticeLaplacian_eq_kwAdj, Matrix.sub_mulVec, dotProduct_sub, h]

theorem kwAdjG_form_le (D : Finset (Torus d m)) (u : Torus d m → ℝ) :
    u ⬝ᵥ kwAdjG d m D *ᵥ u ≤ ∑ x, (∑ y, kwAdjG d m D x y) * u x ^ 2 := by
  have h1 : u ⬝ᵥ kwAdjG d m D *ᵥ u = ∑ x, ∑ y, kwAdjG d m D x y * (u x * u y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have h2 : ∑ x, (∑ y, kwAdjG d m D x y) * u x ^ 2 = ∑ x, ∑ y, kwAdjG d m D x y * u x ^ 2 := by
    simp only [Finset.sum_mul]
  have h3 : ∑ x, ∑ y, kwAdjG d m D x y * u x ^ 2 = ∑ x, ∑ y, kwAdjG d m D x y * u y ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [kwAdjG_symm D y x]
  have h4 : ∑ x, ∑ y, kwAdjG d m D x y * (u x * u y) ≤
      ∑ x, ∑ y, kwAdjG d m D x y * ((u x ^ 2 + u y ^ 2) / 2) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (u x - u y)]) (kwAdjG_nonneg D x y)
  have h5 : ∑ x, ∑ y, kwAdjG d m D x y * ((u x ^ 2 + u y ^ 2) / 2) =
      (∑ x, ∑ y, kwAdjG d m D x y * u x ^ 2 + ∑ x, ∑ y, kwAdjG d m D x y * u y ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [h1, h2]
  linarith

theorem kwAdjG_rowSum_of_not_mem (D : Finset (Torus d m)) {x : Torus d m} (hx : x ∉ D) :
    ∑ y, kwAdjG d m D x y = 2 * d - kwBdry d m D x := by
  have h := Finset.sum_add_sum_compl D (fun y => kwAdj d m x y)
  rw [kwAdj_rowSum] at h
  have h2 : ∑ y, kwAdjG d m D x y = ∑ y ∈ Dᶜ, kwAdj d m x y := by
    rw [← Finset.sum_add_sum_compl D (fun y => kwAdjG d m D x y)]
    have a1 : ∑ y ∈ D, kwAdjG d m D x y = 0 :=
      Finset.sum_eq_zero fun y hy => by simp [kwAdjG, hy]
    have a2 : ∑ y ∈ Dᶜ, kwAdjG d m D x y = ∑ y ∈ Dᶜ, kwAdj d m x y :=
      Finset.sum_congr rfl fun y hy => by
        simp [kwAdjG, hx, (Finset.mem_compl.1 hy)]
    rw [a1, a2, zero_add]
  rw [h2, kwBdry]
  linarith

/-- **`K_G ≥ D_∂ + ν`** (H37 §1): for `u` vanishing on `D`,
`⟨u, K_G u⟩ = ⟨ũ, K_Λ ũ⟩ ≥ ∑_x (D_∂(x) + ν) u_x²`, `D_∂(x) = ∑_{y∈D} A(x,y)`. -/
theorem kwOp_form_ge (ν : ℝ) (D : Finset (Torus d m)) {u : Torus d m → ℝ}
    (hu : ∀ x ∈ D, u x = 0) :
    ∑ x, (kwBdry d m D x + ν) * u x ^ 2 ≤ u ⬝ᵥ kwOp d m ν D *ᵥ u := by
  have h1 : u ⬝ᵥ kwOp d m ν D *ᵥ u = (2 * d + ν) * ∑ x, u x ^ 2 - u ⬝ᵥ kwAdjG d m D *ᵥ u := by
    simp only [kwOp, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
    congr 1
    simp [dotProduct, sq]
  have h2 := kwAdjG_form_le D u
  have h3 : ∑ x, (kwBdry d m D x + ν) * u x ^ 2 =
      (2 * d + ν) * ∑ x, u x ^ 2 - ∑ x, (∑ y, kwAdjG d m D x y) * u x ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ D
    · simp [hu x hx]
    · rw [kwAdjG_rowSum_of_not_mem D hx]; ring
  rw [h1, h3]
  linarith

/-! ### T2: the killed-walk expansion -/

/-- The decay ratio `q = 2d/(2d + ν)`. -/
noncomputable def kwQ (d : ℕ) (ν : ℝ) : ℝ := 2 * d / (2 * d + ν)

/-- The `n`-th term of the killed-walk expansion, `a_ν^{-(n+1)} A_G^n`. -/
noncomputable def kwTerm (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) (n : ℕ) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  ((2 * d + ν)⁻¹) ^ (n + 1) • (kwAdjG d m D) ^ n

/-- The truncation at length `R` of the killed-walk expansion. -/
noncomputable def kwTrunc (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) (R : ℕ) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  ∑ n ∈ Finset.range R, kwTerm d m ν D n

section T2

variable {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m))

include hν

theorem kw_a_pos : 0 < (2 * d + ν : ℝ) := by positivity

theorem kwQ_nonneg : 0 ≤ kwQ d ν := by unfold kwQ; positivity

theorem kwQ_lt_one : kwQ d ν < 1 := by
  unfold kwQ
  rw [div_lt_one (kw_a_pos hν)]; linarith

theorem one_sub_kwQ : 1 - kwQ d ν = ν / (2 * d + ν) := by
  unfold kwQ; have := (kw_a_pos (d := d) hν).ne'; field_simp; ring

/-- The normalized killed adjacency matrix `T = A_G / a_ν`. -/
noncomputable def kwT (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) :
    Matrix (Torus d m) (Torus d m) ℝ := (2 * d + ν)⁻¹ • kwAdjG d m D

omit hν in
theorem kwT_apply (D : Finset (Torus d m)) (x y : Torus d m) :
    kwT d m ν D x y = (2 * d + ν)⁻¹ * kwAdjG d m D x y := rfl

theorem kwT_nonneg (x y : Torus d m) : 0 ≤ kwT d m ν D x y := by
  rw [kwT_apply]; exact mul_nonneg (inv_nonneg.2 (kw_a_pos hν).le) (kwAdjG_nonneg D x y)

theorem kwT_rowSum_le (x : Torus d m) : ∑ y, kwT d m ν D x y ≤ kwQ d ν := by
  simp_rw [kwT_apply, ← Finset.mul_sum]
  unfold kwQ
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (kwAdjG_rowSum_le D x) (inv_nonneg.2 (kw_a_pos hν).le)

omit hν in
theorem kwT_isHermitian : (kwT d m ν D).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, kwT_apply, kwAdjG_symm D i j]

theorem kwOp_eq_smul : kwOp d m ν D = (2 * d + ν) • (1 - kwT d m ν D) := by
  rw [kwT, smul_sub, smul_smul, mul_inv_cancel₀ (kw_a_pos hν).ne', one_smul, kwOp]

omit hν in
theorem kwTerm_eq (n : ℕ) : kwTerm d m ν D n = (2 * d + ν)⁻¹ • kwT d m ν D ^ n := by
  rw [kwTerm, kwT, smul_pow, smul_smul, pow_succ']

theorem kwT_absRow_le (x : Torus d m) : ∑ y, |kwT d m ν D x y| ≤ kwQ d ν := by
  simp_rw [abs_of_nonneg (kwT_nonneg hν D _ _)]
  exact kwT_rowSum_le hν D x

theorem one_sub_kwT_det_pos : 0 < (1 - kwT d m ν D).det :=
  (KW.logdet_series (kwT_isHermitian D) (kwQ_lt_one hν) (kwT_absRow_le hν D)).1

theorem kwOp_det_pos : 0 < (kwOp d m ν D).det := by
  have h := one_sub_kwT_det_pos hν D
  rw [kwOp_eq_smul hν, Matrix.det_smul]
  exact mul_pos (pow_pos (kw_a_pos hν) _) h

theorem kwOp_isUnit : IsUnit (kwOp d m ν D) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact (kwOp_det_pos hν D).ne'.isUnit

theorem kwOp_mul_trunc (R : ℕ) :
    kwOp d m ν D * kwTrunc d m ν D R = 1 - kwT d m ν D ^ R := by
  have h : kwTrunc d m ν D R = (2 * d + ν)⁻¹ • ∑ n ∈ Finset.range R, kwT d m ν D ^ n := by
    rw [kwTrunc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun n _ => kwTerm_eq D n
  rw [h, kwOp_eq_smul hν, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ (kw_a_pos hν).ne', one_smul, mul_neg_geom_sum]

theorem kwT_pow_entry_le (n : ℕ) (x y : Torus d m) : (kwT d m ν D ^ n) x y ≤ kwQ d ν ^ n := by
  refine le_trans ?_ (KW.pow_rowSum_le (kwT_nonneg hν D) (kwQ_nonneg hν) (kwT_rowSum_le hν D) n x)
  exact Finset.single_le_sum (f := fun y => (kwT d m ν D ^ n) x y)
    (fun y _ => KW.pow_entry_nonneg (kwT_nonneg hν D) n x y) (Finset.mem_univ y)

theorem kwOp_det_isUnit : IsUnit (kwOp d m ν D).det := (kwOp_det_pos hν D).ne'.isUnit

theorem kwTrunc_eq (R : ℕ) :
    kwTrunc d m ν D R = (kwOp d m ν D)⁻¹ - (kwOp d m ν D)⁻¹ * kwT d m ν D ^ R := by
  have := congrArg (fun M => (kwOp d m ν D)⁻¹ * M) (kwOp_mul_trunc hν D R)
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (kwOp_det_isUnit hν D), Matrix.one_mul,
    Matrix.mul_sub, Matrix.mul_one] at this
  exact this

theorem kwTrunc_tendsto (x y : Torus d m) :
    Filter.Tendsto (fun R => kwTrunc d m ν D R x y) Filter.atTop
      (nhds ((kwOp d m ν D)⁻¹ x y)) := by
  set K := (kwOp d m ν D)⁻¹ with hK
  have hb : ∀ R, ‖kwTrunc d m ν D R x y - K x y‖ ≤ (∑ z, |K x z|) * kwQ d ν ^ R := by
    intro R
    rw [kwTrunc_eq hν D R, Matrix.sub_apply, sub_sub_cancel_left, norm_neg, Matrix.mul_apply,
      Real.norm_eq_abs]
    calc |∑ z, K x z * (kwT d m ν D ^ R) z y| ≤ ∑ z, |K x z * (kwT d m ν D ^ R) z y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, |K x z| * kwQ d ν ^ R := Finset.sum_le_sum fun z _ => by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_of_nonneg (KW.pow_entry_nonneg (kwT_nonneg hν D) R z y)]
          exact kwT_pow_entry_le hν D R z y
      _ = _ := by rw [Finset.sum_mul]
  have h0 : Filter.Tendsto (fun R : ℕ => (∑ z, |K x z|) * kwQ d ν ^ R) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (kwQ_nonneg hν)
      (kwQ_lt_one hν)).const_mul (∑ z, |K x z|)
  exact tendsto_sub_nhds_zero_iff.1 (squeeze_zero_norm hb h0)

omit hν in
theorem kwTrunc_apply (R : ℕ) (x y : Torus d m) :
    kwTrunc d m ν D R x y =
      ∑ n ∈ Finset.range R, ((2 * d + ν)⁻¹) ^ (n + 1) * (kwAdjG d m D ^ n) x y := by
  simp [kwTrunc, kwTerm, Matrix.sum_apply]

theorem kwTerm_entry_nonneg (n : ℕ) (x y : Torus d m) :
    0 ≤ ((2 * d + ν)⁻¹) ^ (n + 1) * (kwAdjG d m D ^ n) x y :=
  mul_nonneg (pow_nonneg (inv_nonneg.2 (kw_a_pos hν).le) _)
    (KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y)

/-- **Killed-walk expansion** (a): `K_G⁻¹ = ∑_n a_ν^{-(n+1)} A_G^n`, entrywise. -/
theorem kwOp_inv_hasSum (x y : Torus d m) :
    HasSum (fun n : ℕ => ((2 * d + ν)⁻¹) ^ (n + 1) * (kwAdjG d m D ^ n) x y)
      ((kwOp d m ν D)⁻¹ x y) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (kwTerm_entry_nonneg hν D · x y)]
  have h := kwTrunc_tendsto hν D x y
  simp only [kwTrunc_apply] at h
  exact h

theorem kwOp_inv_nonneg (x y : Torus d m) : 0 ≤ (kwOp d m ν D)⁻¹ x y :=
  (kwOp_inv_hasSum hν D x y).nonneg (kwTerm_entry_nonneg hν D · x y)

/-- The geometric series with the walk weights: `∑_n c a^{-(n+t+1)} (2d)^{n+t} = c q^t/ν`. -/
theorem kw_geom_hasSum (c : ℝ) (t : ℕ) :
    HasSum (fun n : ℕ => c * (((2 * d + ν)⁻¹) ^ (n + t + 1) * (2 * d : ℝ) ^ (n + t)))
      (c * kwQ d ν ^ t / ν) := by
  have ha := (kw_a_pos (d := d) hν).ne'
  have hg := (hasSum_geometric_of_lt_one (kwQ_nonneg (d := d) hν) (kwQ_lt_one (d := d) hν)).mul_left
    (c * (2 * d + ν)⁻¹ * kwQ d ν ^ t)
  convert hg using 1
  · funext n
    simp only [kwQ, div_eq_mul_inv]
    ring
  · rw [one_sub_kwQ hν]
    field_simp

theorem kwOp_inv_rowSum_le (x : Torus d m) : ∑ y, (kwOp d m ν D)⁻¹ x y ≤ 1 / ν := by
  have h1 := hasSum_sum (s := Finset.univ) fun y _ => kwOp_inv_hasSum hν D x y
  have h2 := kw_geom_hasSum (d := d) hν 1 0
  simp only [add_zero, one_mul, kwQ, pow_zero, mul_one] at h2
  refine hasSum_le (fun n => ?_) h1 h2
  simp_rw [← Finset.mul_sum]
  calc ((2 * d + ν)⁻¹) ^ (n + 1) * ∑ y, (kwAdjG d m D ^ n) x y
      ≤ ((2 * d + ν)⁻¹) ^ (n + 1) * (2 * d : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left (KW.pow_rowSum_le (kwAdjG_nonneg D) (by positivity)
          (kwAdjG_rowSum_le D) n x) (pow_nonneg (inv_nonneg.2 (kw_a_pos hν).le) _)
    _ = _ := by ring

/-- Comparison with the full torus. -/
theorem kwOp_inv_le_full (x y : Torus d m) :
    (kwOp d m ν D)⁻¹ x y ≤ (latticeLaplacian d m ν)⁻¹ x y := by
  rw [← kwOp_empty ν]
  refine hasSum_le (fun n => ?_) (kwOp_inv_hasSum hν D x y)
    (kwOp_inv_hasSum hν (∅ : Finset (Torus d m)) x y)
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (inv_nonneg.2 (kw_a_pos hν).le) _)
  rw [kwAdjG_empty]
  exact KW.pow_entry_mono (kwAdjG_nonneg D) (kwAdjG_le D) n x y

end T2

/-! ### T3: distance, path locality, inward decay, truncations -/

theorem torusDist_triangle' (x y z : Torus d m) :
    torusDist d m x z ≤ torusDist d m x y + torusDist d m y z :=
  dist_triangle (show L1Torus d m from x) y z

theorem torusDist_self' (x : Torus d m) : torusDist d m x x = 0 :=
  dist_self (show L1Torus d m from x)

theorem torusDist_nonneg' (x y : Torus d m) : 0 ≤ torusDist d m x y :=
  dist_nonneg (x := (show L1Torus d m from x)) (y := y)

/-- A nonzero entry of the adjacency matrix joins sites at `ℓ¹` distance at most `1`. -/
theorem kwAdj_dist_le_one {x y : Torus d m} (h : kwAdj d m x y ≠ 0) : torusDist d m x y ≤ 1 := by
  by_cases hxy : x = y
  · subst hxy; rw [torusDist_self']; norm_num
  · refine torusDist_le_one_of_ne_zero (ν := 0) ?_
    rw [latticeLaplacian_eq_kwAdj]
    simpa [Matrix.one_apply, hxy] using h

theorem kwAdjG_dist_le_one {D : Finset (Torus d m)} {x y : Torus d m}
    (h : kwAdjG d m D x y ≠ 0) : torusDist d m x y ≤ 1 := by
  refine kwAdj_dist_le_one fun h0 => h ?_
  simp [kwAdjG, h0]

/-- Walks of length `n` in `G` join sites at distance at most `n`. -/
theorem kwAdjG_pow_eq_zero_of_lt (D : Finset (Torus d m)) (n : ℕ) :
    ∀ x y : Torus d m, (n : ℝ) < torusDist d m x y → (kwAdjG d m D ^ n) x y = 0 := by
  induction n with
  | zero =>
    intro x y h
    have : x ≠ y := by
      rintro rfl; rw [torusDist_self'] at h; simp at h
    simp [this]
  | succ n ih =>
    intro x y h
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : kwAdjG d m D x z = 0
    · rw [hz, zero_mul]
    · have h1 := kwAdjG_dist_le_one hz
      have h2 := torusDist_triangle' x z y
      rw [ih z y (by push_cast at h; linarith), mul_zero]

/-- **Path locality** (c): the `n`-th walk term at `x` depends only on `D ∩ ball(x, n)`. -/
theorem kwAdjG_pow_locality (D D' : Finset (Torus d m)) (n : ℕ) :
    ∀ x : Torus d m, (∀ z, torusDist d m x z ≤ n → (z ∈ D ↔ z ∈ D')) →
      ∀ y, (kwAdjG d m D ^ n) x y = (kwAdjG d m D' ^ n) x y := by
  induction n with
  | zero => intro x _ y; simp
  | succ n ih =>
    intro x h y
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hA : kwAdj d m x z = 0
    · simp [kwAdjG, hA]
    · have h1 := torusDist_triangle' x z
      have hxz : torusDist d m x z ≤ 1 := kwAdj_dist_le_one hA
      have hxz' : torusDist d m x z ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hx : x ∈ D ↔ x ∈ D' := h x (by rw [torusDist_self']; positivity)
      have hz' : z ∈ D ↔ z ∈ D' := h z hxz'
      have e1 : kwAdjG d m D x z = kwAdjG d m D' x z := by simp [kwAdjG, hx, hz']
      rw [e1, ih z (fun w hw => h w (by
        have := h1 w; push_cast; linarith)) y]

section T3

variable {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m))

include hν

/-- **Inward decay** (b) (H37.3): if `|J| ≤ B` and `J` vanishes at all sites at distance `< t`
from `x`, then `|(K_G⁻¹ J)(x)| ≤ (B/ν) q^t`, `q = 2d/(2d+ν)`. -/
theorem kwOp_inv_mulVec_decay (J : Torus d m → ℝ) {B : ℝ} (hJ : ∀ y, |J y| ≤ B) (x : Torus d m)
    (t : ℕ) (hsupp : ∀ y, J y ≠ 0 → (t : ℝ) ≤ torusDist d m x y) :
    |((kwOp d m ν D)⁻¹ *ᵥ J) x| ≤ B / ν * kwQ d ν ^ t := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hJ x)
  have hs := hasSum_sum (s := Finset.univ) fun y _ =>
    (kwOp_inv_hasSum hν D x y).mul_right (J y)
  simp only [Matrix.mulVec, dotProduct]
  set f : ℕ → ℝ := fun n => ∑ y, ((2 * d + ν)⁻¹) ^ (n + 1) * (kwAdjG d m D ^ n) x y * J y with hf
  have hf0 : ∀ n, n < t → f n = 0 := by
    intro n hn
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : J y = 0
    · rw [hy, mul_zero]
    · rw [kwAdjG_pow_eq_zero_of_lt D n x y (lt_of_lt_of_le (by exact_mod_cast hn) (hsupp y hy))]
      simp
  have hshift := (hasSum_nat_add_iff' t (f := f)).2 hs
  rw [Finset.sum_eq_zero (fun n hn => hf0 n (Finset.mem_range.1 hn)), sub_zero] at hshift
  have hg := kw_geom_hasSum (d := d) hν B t
  rw [show B / ν * kwQ d ν ^ t = B * kwQ d ν ^ t / ν by ring]
  refine hshift.norm_le_of_bounded hg fun n => ?_
  rw [Real.norm_eq_abs]
  set c : Torus d m → ℝ := fun y => ((2 * d + ν)⁻¹) ^ (n + t + 1) * (kwAdjG d m D ^ (n + t)) x y
    with hc
  have hc0 : ∀ y, 0 ≤ c y := fun y => kwTerm_entry_nonneg hν D (n + t) x y
  have hcs : ∑ y, c y ≤ ((2 * d + ν)⁻¹) ^ (n + t + 1) * (2 * d : ℝ) ^ (n + t) := by
    simp only [hc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (KW.pow_rowSum_le (kwAdjG_nonneg D) (by positivity)
      (kwAdjG_rowSum_le D) (n + t) x) (pow_nonneg (inv_nonneg.2 (kw_a_pos hν).le) _)
  show |∑ y, c y * J y| ≤ _
  calc |∑ y, c y * J y| ≤ ∑ y, |c y * J y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, c y * B := Finset.sum_le_sum fun y _ => by
        rw [abs_mul, abs_of_nonneg (hc0 y)]
        exact mul_le_mul_of_nonneg_left (hJ y) (hc0 y)
    _ = (∑ y, c y) * B := by rw [Finset.sum_mul]
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hcs hB

/-- Inward decay from a support set: `J` vanishes outside `S`, `|J| ≤ B`, `dist(x, S) ≥ t`. -/
theorem kwOp_inv_mulVec_decay_of_support (J : Torus d m → ℝ) {B : ℝ} (hJ : ∀ y, |J y| ≤ B)
    (S : Set (Torus d m)) (hJS : ∀ y, y ∉ S → J y = 0) (x : Torus d m) (t : ℕ)
    (hxS : ∀ y ∈ S, (t : ℝ) ≤ torusDist d m x y) :
    |((kwOp d m ν D)⁻¹ *ᵥ J) x| ≤ B / ν * kwQ d ν ^ t :=
  kwOp_inv_mulVec_decay hν D J hJ x t fun y hy => hxS y (by
    by_contra h; exact hy (hJS y h))

omit hν in
/-- The truncation at length `R` has entries vanishing at distance `≥ R`. -/
theorem kwTrunc_apply_eq_zero (R : ℕ) {x y : Torus d m} (h : (R : ℝ) ≤ torusDist d m x y) :
    kwTrunc d m ν D R x y = 0 := by
  rw [kwTrunc_apply]
  refine Finset.sum_eq_zero fun n hn => ?_
  have : (n : ℝ) < torusDist d m x y :=
    lt_of_lt_of_le (by exact_mod_cast Finset.mem_range.1 hn) h
  rw [kwAdjG_pow_eq_zero_of_lt D n x y this, mul_zero]

theorem kwOp_inv_sub_trunc_hasSum (R : ℕ) (x y : Torus d m) :
    HasSum (fun n : ℕ => ((2 * d + ν)⁻¹) ^ (n + R + 1) * (kwAdjG d m D ^ (n + R)) x y)
      ((kwOp d m ν D)⁻¹ x y - kwTrunc d m ν D R x y) := by
  have h := (hasSum_nat_add_iff' R (f := fun n : ℕ =>
    ((2 * d + ν)⁻¹) ^ (n + 1) * (kwAdjG d m D ^ n) x y)).2 (kwOp_inv_hasSum hν D x y)
  rw [← kwTrunc_apply] at h
  exact h

theorem kwOp_inv_sub_trunc_nonneg (R : ℕ) (x y : Torus d m) :
    0 ≤ (kwOp d m ν D)⁻¹ x y - kwTrunc d m ν D R x y :=
  (kwOp_inv_sub_trunc_hasSum hν D R x y).nonneg fun n => kwTerm_entry_nonneg hν D (n + R) x y

/-- **Truncation tail** (c): the row sums of `K_G⁻¹ - ∑_{n<R} a_ν^{-(n+1)} A_G^n` are at most
`q^R/ν`. -/
theorem kwTrunc_tail_rowSum_le (R : ℕ) (x : Torus d m) :
    ∑ y, ((kwOp d m ν D)⁻¹ x y - kwTrunc d m ν D R x y) ≤ kwQ d ν ^ R / ν := by
  have h1 := hasSum_sum (s := Finset.univ) fun y _ => kwOp_inv_sub_trunc_hasSum hν D R x y
  have h2 := kw_geom_hasSum (d := d) hν 1 R
  simp only [one_mul] at h2
  refine hasSum_le (fun n => ?_) h1 h2
  simp_rw [← Finset.mul_sum]
  calc ((2 * d + ν)⁻¹) ^ (n + R + 1) * ∑ y, (kwAdjG d m D ^ (n + R)) x y
      ≤ ((2 * d + ν)⁻¹) ^ (n + R + 1) * (2 * d : ℝ) ^ (n + R) :=
        mul_le_mul_of_nonneg_left (KW.pow_rowSum_le (kwAdjG_nonneg D) (by positivity)
          (kwAdjG_rowSum_le D) (n + R) x) (pow_nonneg (inv_nonneg.2 (kw_a_pos hν).le) _)
    _ = _ := by ring

/-- The padded inverse restricted to `G` is the inverse of the principal submatrix `K_G`. -/
theorem kwOpSub_inv :
    (kwOpSub d m ν D)⁻¹ = (kwOp d m ν D)⁻¹.submatrix Subtype.val Subtype.val := by
  classical
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  have h1 : (kwOp d m ν D * (kwOp d m ν D)⁻¹) i j = (1 : Matrix (Torus d m) (Torus d m) ℝ) i j := by
    rw [Matrix.mul_nonsing_inv _ (kwOp_det_isUnit hν D)]
  rw [Matrix.mul_apply] at h1
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x : Torus d m => x ∉ D)] at h1
  have h2 : ∑ z : {x : Torus d m // ¬ x ∉ D}, kwOp d m ν D i z * (kwOp d m ν D)⁻¹ z j = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    have hz : (z : Torus d m) ∈ D := not_not.1 z.2
    have : kwOp d m ν D i z = 0 := by
      have hne : (i : Torus d m) ≠ z := fun h => i.2 (h ▸ hz)
      simp [kwOp_apply, kwAdjG, hz, hne]
    rw [this, zero_mul]
  rw [h2, add_zero] at h1
  rw [Matrix.mul_apply]
  simp only [Matrix.one_apply, Subtype.ext_iff] at h1 ⊢
  rw [← h1]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [kwOpSub_apply, Matrix.submatrix_apply, kwOp_apply_of_mem ν i.2 z.2]

end T3

end Balaban
