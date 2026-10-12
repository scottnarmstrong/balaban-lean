/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovariance
public import Balaban.Multiscale.ConstraintPerturb
public import Balaban.Localization.DecoupledXClose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The decoupled constrained covariance `C_x(s)` and its bound (I-4c (i), (ii))

LOCALIZATION.md §3.4. On the unit lattice (index type `κι`, `N`-vector fields `κι × Fin N`)

`A_{k,x} = (a_k + x)⁻¹ (1 - P) + (a_k + x + b)⁻¹ P`  (`covA`, `b = a L⁻²`, `P` the `L`-block
projection of the unit lattice, `Q*Q = P_k` and `A_{k,x} = (a_k + x + b P)⁻¹`),

`C_x(s) = A_{k,x} + a_k² L^{-2k} A_{k,x} Q (Ĝ_{k,x,s} - Π_{x,s}) Q* A_{k,x}`  (`decCov`).

(The factor `L^{-2k}` is the unit conversion of the fine lattice: `Q` is a partial isometry, so
`Q Ĝ Q*` is of size `L^{2k+2}` for the fine-unit Green's function.)

* `IsUnitLattice`: the typing data of the unit lattice (support of `Q` in the top layer, `Q` and
  `Q*` are `ℓ²` contractions, `P` an orthogonal projection);
* `sqNorm_covA_le`: `‖A_{k,x}‖ ≤ (a_k + x)⁻¹`;
* `decCov_sub_le`: **I-4c (ii)**, `‖C_x(s) - A_{k,x}‖² ≤ B₄² (a_k + x)⁻⁴`, uniformly in `x ≥ 0`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

/-! ### Euclidean norms -/

section SqNorm

variable {ι : Type*} [Fintype ι]

theorem sqNorm_add_le (u v : ι → ℂ) :
    Green.sqNorm (u + v) ≤ 2 * Green.sqNorm u + 2 * Green.sqNorm v := by
  unfold Green.sqNorm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (u i) (v i)
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖), norm_nonneg (u i), norm_nonneg (v i),
    norm_nonneg (u i + v i)]

theorem sqNorm_sub_le (u v : ι → ℂ) :
    Green.sqNorm (u - v) ≤ 2 * Green.sqNorm u + 2 * Green.sqNorm v := by
  unfold Green.sqNorm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_sub_le (u i) (v i)
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖), norm_nonneg (u i), norm_nonneg (v i),
    norm_nonneg (u i - v i)]

theorem sqNorm_smul (c : ℂ) (v : ι → ℂ) : Green.sqNorm (c • v) = ‖c‖ ^ 2 * Green.sqNorm v := by
  unfold Green.sqNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_pow]

theorem sqNorm_nonneg' (v : ι → ℂ) : 0 ≤ Green.sqNorm v := Green.sqNorm_nonneg v

theorem sqNorm_eq_re_dot (v : ι → ℂ) : Green.sqNorm v = (star v ⬝ᵥ v).re := by
  unfold Green.sqNorm
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  rw [this, Complex.ofReal_re]

end SqNorm

section Orth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sqNorm_add_of_orth (u w : ι → ℂ) (h1 : star u ⬝ᵥ w = 0) (h2 : star w ⬝ᵥ u = 0) :
    Green.sqNorm (u + w) = Green.sqNorm u + Green.sqNorm w := by
  rw [sqNorm_eq_re_dot, sqNorm_eq_re_dot, sqNorm_eq_re_dot, star_add, add_dotProduct,
    dotProduct_add, dotProduct_add, h1, h2]
  simp

omit [DecidableEq ι] in
theorem star_mulVec_dot_eq_zero (A B : Matrix ι ι ℂ) (h : ι → ℂ) (hAB : Aᴴ * B = 0) :
    star (A *ᵥ h) ⬝ᵥ (B *ᵥ h) = 0 := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hAB,
    Matrix.zero_mulVec, dotProduct_zero]

/-- Pythagoras for an orthogonal projection. -/
theorem sqNorm_proj {P : Matrix ι ι ℂ} (hh : Pᴴ = P) (hi : P * P = P) (h : ι → ℂ) :
    Green.sqNorm (P *ᵥ h) + Green.sqNorm ((1 - P) *ᵥ h) = Green.sqNorm h := by
  have h1 : Pᴴ * (1 - P) = 0 := by rw [hh, Matrix.mul_sub, Matrix.mul_one, hi, sub_self]
  have h2 : (1 - P)ᴴ * P = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh, Matrix.sub_mul, Matrix.one_mul,
      hi, sub_self]
  have hsum : h = P *ᵥ h + (1 - P) *ᵥ h := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  conv_rhs => rw [hsum]
  rw [sqNorm_add_of_orth _ _ (star_mulVec_dot_eq_zero P (1 - P) h h1)
    (star_mulVec_dot_eq_zero (1 - P) P h h2)]

end Orth

/-! ### The unit lattice -/

section UnitLattice

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- Componentwise lift of a rectangular matrix to `N`-vector fields. -/
def liftRect (N : ℕ) {ι : Type*} (Q : Matrix κι ι ℂ) : Matrix (κι × Fin N) (ι × Fin N) ℂ :=
  fun p q => if p.2 = q.2 then Q p.1 q.1 else 0

omit [Fintype κι] [DecidableEq κι] in
theorem liftRect_mulVec {ι : Type*} [Fintype ι] (Q : Matrix κι ι ℂ) (v : ι × Fin N → ℂ)
    (b : κι) (i : Fin N) : (liftRect N Q *ᵥ v) (b, i) = (Q *ᵥ fun y => v (y, i)) b := by
  simp only [mulVec, dotProduct, liftRect, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

omit [Fintype κι] [DecidableEq κι] in
theorem liftRect_transpose {ι : Type*} (Q : Matrix κι ι ℂ) :
    (liftRect N Q)ᵀ = liftRect N Qᵀ := by
  ext p q
  simp only [transpose_apply, liftRect]
  by_cases h : q.2 = p.2
  · simp [h]
  · simp [h, Ne.symm h]

theorem sqNorm_prod {ι : Type*} [Fintype ι] (v : ι × Fin N → ℂ) :
    Green.sqNorm v = ∑ i, Green.sqNorm (fun y => v (y, i)) := by
  unfold Green.sqNorm
  rw [Fintype.sum_prod_type, Finset.sum_comm]

omit [DecidableEq κι] in
theorem sqNorm_liftRect_le {ι : Type*} [Fintype ι] {Q : Matrix κι ι ℂ}
    (hQ : ∀ f : ι → ℂ, Green.sqNorm (Q *ᵥ f) ≤ Green.sqNorm f) (v : ι × Fin N → ℂ) :
    Green.sqNorm (liftRect N Q *ᵥ v) ≤ Green.sqNorm v := by
  rw [sqNorm_prod, sqNorm_prod (v := v)]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (fun b => (liftRect N Q *ᵥ v) (b, i)) = Q *ᵥ fun y => v (y, i) := by
    funext b; exact liftRect_mulVec Q v b i
  rw [this]
  exact hQ _

variable (G) in
/-- The typing data of the unit lattice: `Q` (block average, a partial isometry) is supported on
the top layer `Ω_{k+1}` and `Q`, `Q*` are `ℓ²` contractions; `P` (the `L`-block projection of the
unit lattice) is an orthogonal projection. -/
structure IsUnitLattice (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) : Prop where
  layer : ∀ b y, Q b y ≠ 0 → (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1)
  contr : ∀ f : G.Ω 1 → ℂ, Green.sqNorm (Q *ᵥ f) ≤ Green.sqNorm f
  contrT : ∀ h : κι → ℂ, Green.sqNorm (Qᵀ *ᵥ h) ≤ Green.sqNorm h
  herm : Pᴴ = P
  idem : P * P = P

end UnitLattice

/-! ### The covariance `A_{k,x}` -/

section CovA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A = (c + x)⁻¹ (1 - P) + (c + x + b)⁻¹ P`, the inverse of `(c + x) + b P`. -/
noncomputable def covA (c b x : ℝ) (P : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((c : ℂ) + x)⁻¹ • (1 - P) + ((c : ℂ) + x + b)⁻¹ • P

theorem covA_mul_T {c b x : ℝ} (hcx : 0 < c + x) (hb : 0 ≤ b) {P : Matrix ι ι ℂ}
    (hi : P * P = P) :
    (((c : ℂ) + x) • (1 : Matrix ι ι ℂ) + (b : ℂ) • P) * covA c b x P = 1 := by
  have h1 : (c : ℂ) + x ≠ 0 := by exact_mod_cast hcx.ne'
  have h2 : (c : ℂ) + x + b ≠ 0 := by
    have : 0 < c + x + b := by linarith
    exact_mod_cast this.ne'
  exact projection_mul_inv (c : ℂ) x b P hi h1 h2

theorem norm_inv_cx {c x : ℝ} (hcx : 0 < c + x) : ‖((c : ℂ) + x)⁻¹‖ = (c + x)⁻¹ := by
  rw [norm_inv, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg hcx.le]

theorem norm_inv_cxb {c b x : ℝ} (hcx : 0 < c + x) (hb : 0 ≤ b) :
    ‖((c : ℂ) + x + b)⁻¹‖ = (c + x + b)⁻¹ := by
  have : 0 ≤ c + x + b := by linarith
  rw [norm_inv, ← Complex.ofReal_add, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg this]

/-- `‖A_{k,x}‖ ≤ (c + x)⁻¹` for an orthogonal projection `P`. -/
theorem sqNorm_covA_le {c b x : ℝ} (hcx : 0 < c + x) (hb : 0 ≤ b) {P : Matrix ι ι ℂ}
    (hh : Pᴴ = P) (hi : P * P = P) (h : ι → ℂ) :
    Green.sqNorm (covA c b x P *ᵥ h) ≤ ((c + x)⁻¹) ^ 2 * Green.sqNorm h := by
  unfold covA
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
  have h1 : Pᴴ * (1 - P) = 0 := by rw [hh, Matrix.mul_sub, Matrix.mul_one, hi, sub_self]
  have h2 : (1 - P)ᴴ * P = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hh, Matrix.sub_mul, Matrix.one_mul,
      hi, sub_self]
  have o1 := star_mulVec_dot_eq_zero P (1 - P) h h1
  have o2 := star_mulVec_dot_eq_zero (1 - P) P h h2
  rw [add_comm, sqNorm_add_of_orth]
  · rw [sqNorm_smul, sqNorm_smul, norm_inv_cx hcx, norm_inv_cxb hcx hb]
    have hP := sqNorm_proj hh hi h
    have hα : (c + x + b)⁻¹ ≤ (c + x)⁻¹ := by
      apply inv_anti₀ hcx; linarith
    have hα0 : 0 ≤ (c + x + b)⁻¹ := inv_nonneg.2 (by linarith)
    have hα2 : ((c + x + b)⁻¹) ^ 2 ≤ ((c + x)⁻¹) ^ 2 := pow_le_pow_left₀ hα0 hα 2
    have hu := sqNorm_nonneg' (P *ᵥ h)
    have hw := sqNorm_nonneg' ((1 - P) *ᵥ h)
    nlinarith [mul_le_mul_of_nonneg_right hα2 hu]
  · rw [star_smul, smul_dotProduct, dotProduct_smul, o1]; simp
  · rw [star_smul, smul_dotProduct, dotProduct_smul, o2]; simp

end CovA

/-! ### The chain of weighted bounds -/

section Chain

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

theorem XData.weight_zero (D : XData G a aT ν x α κ s) : XWeight G 0 (fun _ => 0) := by
  refine ⟨isAgmonWeight_zero G, le_rfl, ?_⟩
  have hd : 0 < d := by have := D.st.dg.hd; omega
  exact (xAgmonRate_pos hd D.st.dg.hL).le

theorem vecM0_sub_le (u v : G.Ω 1 × Fin N → ℂ) :
    vecM G 0 (fun _ => 0) (u - v) ≤
      2 * vecM G 0 (fun _ => 0) u + 2 * vecM G 0 (fun _ => 0) v := by
  rw [vecM0_eq, vecM0_eq, vecM0_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_sub_le (u (y, i)) (v (y, i))
  have h2 : ‖u (y, i) - v (y, i)‖ ^ 2 ≤ 2 * ‖u (y, i)‖ ^ 2 + 2 * ‖v (y, i)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖u (y, i)‖ - ‖v (y, i)‖), norm_nonneg (u (y, i)), norm_nonneg (v (y, i)),
      norm_nonneg (u (y, i) - v (y, i))]
  have h0 : 0 ≤ ((G.spacing y) ^ 2)⁻¹ := by positivity
  simp only [Pi.sub_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

variable {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

theorem vecSrc0_le_of_supp (w : G.Ω 1 × Fin N → ℂ)
    (hw : ∀ y i, w (y, i) ≠ 0 → (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1)) :
    vecSrc G 0 (fun _ => 0) w ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * Green.sqNorm w := by
  rw [vecSrc0_eq]
  unfold Green.sqNorm
  rw [Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun y _ => ?_
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h0 : w (y, i) = 0
  · simp [h0]
  · have hy := hw y i h0
    rw [G.spacing_eq (by omega) le_rfl hy]

omit [DecidableEq κι] in
theorem sqNorm_Q_le (hU : IsUnitLattice G Q P) (f : G.Ω 1 → ℂ) :
    Green.sqNorm (Q *ᵥ f) ≤
      ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ y : G.Ω 1, ((G.spacing y) ^ 2)⁻¹ * ‖f y‖ ^ 2 := by
  classical
  set f' : G.Ω 1 → ℂ := fun y =>
    if (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) then f y else 0 with hf'
  have hQf : Q *ᵥ f = Q *ᵥ f' := by
    funext b
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1)
    · simp [hf', hy]
    · have : Q b y = 0 := by
        by_contra hne
        exact hy (hU.layer b y hne)
      simp [this]
  rw [hQf]
  refine (hU.contr f').trans ?_
  unfold Green.sqNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1)
  · simp only [hf', hy, ite_true]
    rw [G.spacing_eq (by omega) le_rfl hy]
    have : (0 : ℝ) < ((L : ℝ) ^ (k + 1)) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    field_simp
    exact le_rfl
  · simp only [hf', hy, ite_false, norm_zero]
    have : (0 : ℝ) ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * (((G.spacing y) ^ 2)⁻¹ * ‖f y‖ ^ 2) := by
      have := spacing_pos G (x := (y : CTorus d L N₁ m₁ (k + 1)))
      positivity
    simpa using this

omit [DecidableEq κι] in
theorem sqNorm_liftRect_le_vecM0 (hU : IsUnitLattice G Q P) (u : G.Ω 1 × Fin N → ℂ) :
    Green.sqNorm (liftRect N Q *ᵥ u) ≤
      ((L : ℝ) ^ (k + 1)) ^ 2 * vecM G 0 (fun _ => 0) u := by
  rw [sqNorm_prod, vecM0_eq, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (fun b => (liftRect N Q *ᵥ u) (b, i)) = Q *ᵥ fun y => u (y, i) := by
    funext b; exact liftRect_mulVec Q u b i
  rw [this]
  exact sqNorm_Q_le hU _

/-! ### The covariance `C_x(s)` and its bound -/

variable (G) in
/-- **The decoupled constrained covariance**
`C_x(s) = A + a_k² L^{-2k} A Q (Ĝ_{k,x,s} - Π_{x,s}) Q* A` on `N`-vector fields of the unit lattice. -/
noncomputable def decCov (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) +
    (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
        (liftOp N (Gsx G a aT x ν α s) - decPi G a aT x ν α s φ) * (liftRect N Q)ᵀ *
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))

/-- The squared constant `B₄²` of I-4c (ii). -/
noncomputable def covBsq (d L : ℕ) (ak κ : ℝ) : ℝ :=
  ak ^ 4 * (L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2))

theorem covBsq_nonneg (d L : ℕ) (ak κ : ℝ) : 0 ≤ covBsq d L ak κ := by
  unfold covBsq valConstX; positivity

omit [DecidableEq κι] in
theorem liftOp_herm_idem (hU : IsUnitLattice G Q P) :
    (liftOp N P)ᴴ = liftOp N P ∧ liftOp N P * liftOp N P = liftOp N P := by
  refine ⟨?_, ?_⟩
  · rw [liftOp_conjTranspose, hU.herm]
  · rw [← liftOp_mul, hU.idem]

omit [DecidableEq κι] in
theorem decCov_sub_covA (Av : Matrix (κι × Fin N) (κι × Fin N) ℂ) (cs : ℂ)
    (X : Matrix (κι × Fin N) (κι × Fin N) ℂ) (h : κι × Fin N → ℂ) :
    ((Av + cs • (Av * X)) - Av) *ᵥ h = cs • (Av *ᵥ (X *ᵥ h)) := by
  rw [add_sub_cancel_left, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

section Main

variable (D : XData G a aT ν x α κ s)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hU : IsUnitLattice G Q P)
include D hφ hδ hsm hU

/-- **I-4c (ii).** `‖C_x(s) - A_{k,x}‖² ≤ B₄² (a_k + x)⁻⁴`, uniformly in `x ≥ 0`. -/
theorem decCov_sub_le (h : κι × Fin N → ℂ) :
    Green.sqNorm ((decCov G a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) *ᵥ h) ≤
      covBsq d L (a k) κ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm h := by
  have hk := D.st.hk
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := D.st.ha k hk le_rfl
  have hcx : 0 < a k + x := by have := D.x0; linarith [hak.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  obtain ⟨hPh, hPi⟩ := liftOp_herm_idem (N := N) hU
  set Av := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) with hAv
  set cs : ℂ := (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) with hcs
  set T := liftOp N (Gsx G a aT x ν α s) - decPi G a aT x ν α s φ with hT
  have hrw : (decCov G a aT x ν α s φ Q P - Av) *ᵥ h =
      cs • (Av *ᵥ (liftRect N Q *ᵥ (T *ᵥ ((liftRect N Q)ᵀ *ᵥ (Av *ᵥ h))))) := by
    have : decCov G a aT x ν α s φ Q P = Av + cs • (Av * (liftRect N Q * T * (liftRect N Q)ᵀ * Av)) := by
      unfold decCov
      simp only [Matrix.mul_assoc]
      rfl
    rw [this, decCov_sub_covA]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hrw, sqNorm_smul]
  set Λ : ℝ := (L : ℝ) ^ (k + 1) with hΛ
  set z := Av *ᵥ h with hz
  have s1 : Green.sqNorm z ≤ ((a k + x)⁻¹) ^ 2 * Green.sqNorm h := sqNorm_covA_le hcx hb hPh hPi h
  set w := (liftRect N Q)ᵀ *ᵥ z with hw
  have hw_supp : ∀ y i, w (y, i) ≠ 0 → (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) := by
    intro y i hne
    by_contra hy
    apply hne
    rw [hw, liftRect_transpose, liftRect_mulVec]
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : Q b y = 0 := by
      by_contra hne'
      exact hy (hU.layer b y hne')
    simp [this]
  have s2 : Green.sqNorm w ≤ Green.sqNorm z := by
    rw [hw, liftRect_transpose]; exact sqNorm_liftRect_le hU.contrT z
  have s3 : vecSrc G 0 (fun _ => 0) w ≤ Λ ^ 2 * Green.sqNorm w := vecSrc0_le_of_supp w hw_supp
  set u := T *ᵥ w with hu
  have hW0 := D.weight_zero
  obtain ⟨hM1, -⟩ := Gsx_vec_bounds D hW0 w
  obtain ⟨hM2, -⟩ := decPi_weighted_bounds D hW0 hφ hδ hsm w
  have hV : 0 ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 := by unfold valConstX; positivity
  have s4 : vecM G 0 (fun _ => 0) u ≤
      92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * vecSrc G 0 (fun _ => 0) w := by
    have := vecM0_sub_le (liftOp N (Gsx G a aT x ν α s) *ᵥ w) (decPi G a aT x ν α s φ *ᵥ w)
    have e : u = liftOp N (Gsx G a aT x ν α s) *ᵥ w - decPi G a aT x ν α s φ *ᵥ w := by
      rw [hu, hT, Matrix.sub_mulVec]
    rw [e]
    nlinarith
  have s5 : Green.sqNorm (liftRect N Q *ᵥ u) ≤ Λ ^ 2 * vecM G 0 (fun _ => 0) u :=
    sqNorm_liftRect_le_vecM0 hU u
  have s6 : Green.sqNorm (Av *ᵥ (liftRect N Q *ᵥ u)) ≤
      ((a k + x)⁻¹) ^ 2 * Green.sqNorm (liftRect N Q *ᵥ u) := sqNorm_covA_le hcx hb hPh hPi _
  have hα0 : 0 ≤ ((a k + x)⁻¹) ^ 2 := by positivity
  have hΛ0 : 0 ≤ Λ ^ 2 := by positivity
  have hcs2 : ‖cs‖ ^ 2 * Λ ^ 2 * Λ ^ 2 = (a k) ^ 4 * (L : ℝ) ^ 4 := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have : ‖cs‖ = (a k) ^ 2 / (L : ℝ) ^ (2 * k) := by
      rw [hcs, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [this, hΛ]
    field_simp
    ring
  have hcs0 : 0 ≤ ‖cs‖ ^ 2 := by positivity
  have hsw := sqNorm_nonneg' w
  have hsh := sqNorm_nonneg' h
  have hsv : 0 ≤ vecSrc G 0 (fun _ => 0) w := vecSrc_nonneg G 0 _ w
  calc ‖cs‖ ^ 2 * Green.sqNorm (Av *ᵥ (liftRect N Q *ᵥ u))
      ≤ ‖cs‖ ^ 2 * (((a k + x)⁻¹) ^ 2 * (Λ ^ 2 * vecM G 0 (fun _ => 0) u)) := by
        refine mul_le_mul_of_nonneg_left (s6.trans ?_) hcs0
        exact mul_le_mul_of_nonneg_left s5 hα0
    _ ≤ ‖cs‖ ^ 2 * (((a k + x)⁻¹) ^ 2 * (Λ ^ 2 *
          (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2) * (Λ ^ 2 * (((a k + x)⁻¹) ^ 2 *
            Green.sqNorm h))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (s4.trans ?_) hΛ0) hα0) hcs0
        refine mul_le_mul_of_nonneg_left (s3.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left (s2.trans s1) hΛ0
    _ = covBsq d L (a k) κ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm h := by
        unfold covBsq
        rw [← hcs2]
        ring

end Main

end Chain

end Balaban.Localization
