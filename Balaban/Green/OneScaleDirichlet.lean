/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalMassGreen
public import Balaban.Green.Restriction
public import Balaban.Green.Summation
public import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The single-scale Dirichlet problem on a set of fine sites (shared)

For a real matrix `A` on a finite type and a finite set `V` of sites, `dirichletSol A V F` is
the solution of the Dirichlet problem of `A` on `V` with source `F`: the zero extension of
`(A_V)⁻¹ F|_V`, `A_V` the principal submatrix of `A` on `V`.

**General facts** (any real symmetric `A` with nonnegative form, `V ⊆ W`):
* `mulVec_dirichletSol`, `eq_dirichletSol`: the equation `A y = F` on `V`, and uniqueness;
* `dirichlet_pair_identity`: with `e_f = z_f - y_f` (`y` the solutions on `V`, `z` on `W`),
  `e_f · A e_g = f · z_g - f · y_g`;
* `dirichlet_principle`: `e_f · A e_f ≤ φ · A φ` for every `φ` equal to `z_f` off `V`;
* `sq_dotProduct_mulVec_le`: the Cauchy–Schwarz inequality of a nonnegative symmetric form.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

section Dirichlet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The solution of the Dirichlet problem of `A` on `V` with source `F`: the zero extension of
`(A_V)⁻¹ F|_V`, where `A_V` is the principal submatrix of `A` on `V`. -/
noncomputable def dirichletSol (A : Matrix ι ι ℝ) (V : Finset ι) (F : ι → ℝ) : ι → ℝ :=
  fun x => if h : x ∈ V then
    ((A.submatrix ((↑) : V → ι) ((↑) : V → ι))⁻¹ *ᵥ fun i : V => F i) ⟨x, h⟩ else 0

omit [Fintype ι] in
theorem dirichletSol_of_not_mem (A : Matrix ι ι ℝ) (V : Finset ι) (F : ι → ℝ) {x : ι}
    (hx : x ∉ V) : dirichletSol A V F x = 0 := by
  simp [dirichletSol, hx]

omit [Fintype ι] in
theorem dirichletSol_coe (A : Matrix ι ι ℝ) (V : Finset ι) (F : ι → ℝ) (i : V) :
    dirichletSol A V F i = ((A.submatrix ((↑) : V → ι) ((↑) : V → ι))⁻¹ *ᵥ fun i : V => F i) i := by
  simp [dirichletSol, i.2]

omit [DecidableEq ι] in
/-- `A w` at a site of `V`, for `w` vanishing off `V`, is the principal block applied to `w|_V`. -/
theorem mulVec_apply_of_supp (A : Matrix ι ι ℝ) (V : Finset ι) {w : ι → ℝ}
    (hw : ∀ x, x ∉ V → w x = 0) (x : V) :
    (A *ᵥ w) x = (A.submatrix ((↑) : V → ι) ((↑) : V → ι) *ᵥ fun i : V => w i) x := by
  show ∑ y, A x y * w y = ∑ i : V, A x i * w i
  exact sum_eq_sum_subtype V _ fun y hy => by rw [hw y hy, mul_zero]

/-- The Dirichlet solution satisfies the equation on `V`. -/
theorem mulVec_dirichletSol (A : Matrix ι ι ℝ) (V : Finset ι) (F : ι → ℝ)
    (hA : IsUnit (A.submatrix ((↑) : V → ι) ((↑) : V → ι))) {x : ι} (hx : x ∈ V) :
    (A *ᵥ dirichletSol A V F) x = F x := by
  have h := mulVec_apply_of_supp A V (fun y hy => dirichletSol_of_not_mem A V F hy) ⟨x, hx⟩
  have e : (fun i : V => dirichletSol A V F i) =
      (A.submatrix ((↑) : V → ι) ((↑) : V → ι))⁻¹ *ᵥ fun i : V => F i :=
    funext fun i => dirichletSol_coe A V F i
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA),
    Matrix.one_mulVec] at h
  exact h

omit [Fintype ι] in
theorem mem_of_dirichletSol_ne_zero {A : Matrix ι ι ℝ} {V : Finset ι} {F : ι → ℝ} {x : ι}
    (hx : dirichletSol A V F x ≠ 0) : x ∈ V := by
  by_contra h; exact hx (dirichletSol_of_not_mem A V F h)

/-- Uniqueness of the Dirichlet solution. -/
theorem eq_dirichletSol (A : Matrix ι ι ℝ) (V : Finset ι) (F : ι → ℝ)
    (hA : IsUnit (A.submatrix ((↑) : V → ι) ((↑) : V → ι))) {w : ι → ℝ} (hw0 : ∀ x, x ∉ V → w x = 0)
    (hw : ∀ x ∈ V, (A *ᵥ w) x = F x) : w = dirichletSol A V F := by
  have h1 : A.submatrix ((↑) : V → ι) ((↑) : V → ι) *ᵥ (fun i : V => w i) = fun i : V => F i :=
    funext fun i => (mulVec_apply_of_supp A V hw0 i).symm.trans (hw i i.2)
  have hres : (fun i : V => w i) = (A.submatrix ((↑) : V → ι) ((↑) : V → ι))⁻¹ *ᵥ fun i : V => F i := by
    rw [← h1, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hA), Matrix.one_mulVec]
  funext x
  by_cases hx : x ∈ V
  · exact (congrFun hres ⟨x, hx⟩).trans (dirichletSol_coe A V F ⟨x, hx⟩).symm
  · rw [hw0 x hx, dirichletSol_of_not_mem A V F hx]

/-- The matrix elements of `A' (A_V)⁻¹ C` (columns of `A'`, rows of `C` restricted to `V`) through
the Dirichlet solution. -/
theorem submatrix_mul_inv_mul_apply {α β : Type*} (A : Matrix ι ι ℝ) (V : Finset ι)
    (A' : Matrix α ι ℝ) (C : Matrix ι β ℝ) (a : α) (b : β) :
    (A'.submatrix id ((↑) : V → ι) * (A.submatrix ((↑) : V → ι) ((↑) : V → ι))⁻¹ *
        C.submatrix ((↑) : V → ι) id) a b = ∑ x, A' a x * dirichletSol A V (fun x => C x b) x := by
  rw [sum_eq_sum_subtype V _ fun x hx => by rw [dirichletSol_of_not_mem _ _ _ hx, mul_zero],
    Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dirichletSol_coe]
  rfl

end Dirichlet

section Variational

variable {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)

theorem dotProduct_eq_of_supp {u g h : ι → ℝ} (H : ∀ x, u x ≠ 0 → g x = h x) :
    u ⬝ᵥ g = u ⬝ᵥ h :=
  Finset.sum_congr rfl fun x _ => by
    by_cases hx : u x = 0
    · simp [hx]
    · rw [H x hx]

theorem dotProduct_mulVec_comm (hA : Aᵀ = A) (u v : ι → ℝ) :
    u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]

variable {A} {V W : Finset ι}

/-- **Pair identity.**  Let `y_g` solve `A y = g` on `V` (vanishing off `V`), `z_f, z_g` solve
`A z = f, g` on `W ⊇ V` (vanishing off `W`), and `y_f` vanish off `V`.  Then
`(z_f - y_f) · A (z_g - y_g) = f · z_g - f · y_g`. -/
theorem dirichlet_pair_identity (hA : Aᵀ = A) (hVW : V ⊆ W) {f g yf yg zf zg : ι → ℝ}
    (hyf0 : ∀ x, x ∉ V → yf x = 0) (hyg0 : ∀ x, x ∉ V → yg x = 0) (hyg : ∀ x ∈ V, (A *ᵥ yg) x = g x)
    (hzf0 : ∀ x, x ∉ W → zf x = 0) (hzf : ∀ x ∈ W, (A *ᵥ zf) x = f x)
    (hzg0 : ∀ x, x ∉ W → zg x = 0) (hzg : ∀ x ∈ W, (A *ᵥ zg) x = g x) :
    (zf - yf) ⬝ᵥ A *ᵥ (zg - yg) = f ⬝ᵥ zg - f ⬝ᵥ yg := by
  have mV : ∀ {u : ι → ℝ}, (∀ x, x ∉ V → u x = 0) → ∀ x, u x ≠ 0 → x ∈ V :=
    fun hu x hx => by by_contra h; exact hx (hu x h)
  have mW : ∀ {u : ι → ℝ}, (∀ x, x ∉ W → u x = 0) → ∀ x, u x ≠ 0 → x ∈ W :=
    fun hu x hx => by by_contra h; exact hx (hu x h)
  have h1 : zf ⬝ᵥ A *ᵥ zg = zf ⬝ᵥ g :=
    dotProduct_eq_of_supp fun x hx => hzg x (mW hzf0 x hx)
  have h2 : zf ⬝ᵥ A *ᵥ yg = yg ⬝ᵥ f := by
    rw [dotProduct_mulVec_comm A hA]
    exact dotProduct_eq_of_supp fun x hx => hzf x (hVW (mV hyg0 x hx))
  have h3 : yf ⬝ᵥ A *ᵥ zg = yf ⬝ᵥ g :=
    dotProduct_eq_of_supp fun x hx => hzg x (hVW (mV hyf0 x hx))
  have h4 : yf ⬝ᵥ A *ᵥ yg = yf ⬝ᵥ g :=
    dotProduct_eq_of_supp fun x hx => hyg x (mV hyf0 x hx)
  have h5 : zf ⬝ᵥ g = f ⬝ᵥ zg := by
    rw [← h1, dotProduct_mulVec_comm A hA, dotProduct_comm f]
    exact dotProduct_eq_of_supp fun x hx => hzf x (mW hzg0 x hx)
  have h6 : yg ⬝ᵥ f = f ⬝ᵥ yg := dotProduct_comm _ _
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, h2, h3, h4, h5, h6]
  ring

/-- **Dirichlet principle.**  With `y_f, z_f` as in `dirichlet_pair_identity`, for a symmetric `A`
with nonnegative form, `(z_f - y_f) · A (z_f - y_f) ≤ φ · A φ` for every `φ` equal to `z_f` off
`V`. -/
theorem dirichlet_principle (hA : Aᵀ = A) (hpsd : ∀ u, 0 ≤ u ⬝ᵥ A *ᵥ u) (hVW : V ⊆ W)
    {f yf zf : ι → ℝ} (hyf0 : ∀ x, x ∉ V → yf x = 0) (hyf : ∀ x ∈ V, (A *ᵥ yf) x = f x)
    (hzf : ∀ x ∈ W, (A *ᵥ zf) x = f x) {φ : ι → ℝ} (hφ : ∀ x, x ∉ V → φ x = zf x) :
    (zf - yf) ⬝ᵥ A *ᵥ (zf - yf) ≤ φ ⬝ᵥ A *ᵥ φ := by
  set e := zf - yf with he
  set h := φ - e with hh
  have hAe : ∀ x, h x ≠ 0 → (A *ᵥ e) x = (0 : ι → ℝ) x := by
    intro x hx
    have hxV : x ∈ V := by
      by_contra hn
      apply hx
      simp only [hh, he, Pi.sub_apply, hφ x hn, hyf0 x hn, sub_zero, sub_self]
    rw [he, Matrix.mulVec_sub, Pi.sub_apply, hzf x (hVW hxV), hyf x hxV, sub_self, Pi.zero_apply]
  have hhe : h ⬝ᵥ A *ᵥ e = 0 := by
    rw [dotProduct_eq_of_supp hAe, dotProduct_zero]
  have hφe : φ = e + h := by rw [hh, add_sub_cancel]
  rw [hφe, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    dotProduct_mulVec_comm A hA e h, hhe]
  linarith [hpsd h]

/-- **Cauchy–Schwarz** for the form of a symmetric matrix with nonnegative form. -/
theorem sq_dotProduct_mulVec_le (hA : Aᵀ = A) (hpsd : ∀ u, 0 ≤ u ⬝ᵥ A *ᵥ u) (u v : ι → ℝ) :
    (u ⬝ᵥ A *ᵥ v) ^ 2 ≤ (u ⬝ᵥ A *ᵥ u) * (v ⬝ᵥ A *ᵥ v) := by
  have hc := dotProduct_mulVec_comm A hA v u
  have h := discrim_le_zero (a := v ⬝ᵥ A *ᵥ v) (b := 2 * (u ⬝ᵥ A *ᵥ v)) (c := u ⬝ᵥ A *ᵥ u)
    fun t => by
      have h := hpsd (u + t • v)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, hc] at h
      simp only [smul_eq_mul] at h
      linarith
  unfold discrim at h
  nlinarith

end Variational

/-! ### The Dirichlet Schur complement on a set of fine sites -/

/-- The coarse kernel `Q_V (H_V)⁻¹ Q_V*` of the Dirichlet problem on the set `V` of fine sites:
`H_V` the principal submatrix on `V` of the unit-lattice operator
`H = fineHamiltonian d ℓ N m ν a`, `Q_V`, `Q_V*` the block average and the pull-back restricted to
`V`. -/
noncomputable def dirichletBlockKernel (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] (V : Finset (Torus d ℓ))
    (ν a : ℝ) : Matrix (Torus d m) (Torus d m) ℝ :=
  (unitBlockAverageMatrix d ℓ N m).submatrix id ((↑) : V → Torus d ℓ) *
    ((fineHamiltonian d ℓ N m ν a).submatrix ((↑) : V → Torus d ℓ) ((↑) : V → Torus d ℓ))⁻¹ *
    (blockPullbackMatrix d ℓ N m).submatrix ((↑) : V → Torus d ℓ) id

/-- **The Dirichlet Schur complement** `a - a² Q_V (H_V)⁻¹ Q_V*` on the set `V` of fine sites (the
final Hessian of the massive problem with the fine field restricted to `V`); for `V` the whole
torus this is `unconstrainedUnitOperator` (`dirichletUnitOperator_univ`). -/
noncomputable def dirichletUnitOperator (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m]
    (V : Finset (Torus d ℓ)) (ν a : ℝ) : Matrix (Torus d m) (Torus d m) ℝ :=
  a • (1 : Matrix (Torus d m) (Torus d m) ℝ) - (a ^ 2) • dirichletBlockKernel d ℓ N m V ν a

section Kernel

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem dirichletBlockKernel_apply (V : Finset (Torus d ℓ)) (ν a : ℝ) (y y' : Torus d m) :
    dirichletBlockKernel d ℓ N m V ν a y y' = ((N : ℝ) ^ d)⁻¹ *
      ∑ x ∈ blockFibre N m y, dirichletSol (fineHamiltonian d ℓ N m ν a) V
        (blockIndicator N m y') x := by
  unfold dirichletBlockKernel
  rw [submatrix_mul_inv_mul_apply]
  simp only [unitBlockAverageMatrix, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl

/-- The quadratic form of the Dirichlet kernel: `ψ · K_V ψ = N⁻ᵈ (f · y_f)`, `f = Q* ψ`,
`y_f` the Dirichlet solution on `V` with source `f`. -/
theorem dirichletBlockKernel_quad (V : Finset (Torus d ℓ)) (ν a : ℝ) (ψ : Torus d m → ℝ) :
    ψ ⬝ᵥ dirichletBlockKernel d ℓ N m V ν a *ᵥ ψ = ((N : ℝ) ^ d)⁻¹ *
      ((blockPullbackMatrix d ℓ N m *ᵥ ψ) ⬝ᵥ
        dirichletSol (fineHamiltonian d ℓ N m ν a) V (blockPullbackMatrix d ℓ N m *ᵥ ψ)) := by
  set f := blockPullbackMatrix d ℓ N m *ᵥ ψ with hf
  set sol := dirichletSol (fineHamiltonian d ℓ N m ν a) V f with hsol
  have e1 : dirichletBlockKernel d ℓ N m V ν a *ᵥ ψ =
      (unitBlockAverageMatrix d ℓ N m).submatrix id ((↑) : V → Torus d ℓ) *ᵥ
        (fun i : V => sol i) := by
    unfold dirichletBlockKernel
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    rw [hsol, dirichletSol_coe]
    rfl
  have e2 : ψ ᵥ* (unitBlockAverageMatrix d ℓ N m).submatrix id ((↑) : V → Torus d ℓ) =
      fun i : V => ((N : ℝ) ^ d)⁻¹ * f i := by
    funext i
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, id, unitBlockAverageMatrix, hf,
      Matrix.mulVec, blockPullbackMatrix, mul_ite, mul_zero, ite_mul, zero_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  rw [e1, Matrix.dotProduct_mulVec, e2]
  show ∑ i : V, ((N : ℝ) ^ d)⁻¹ * f i * sol i = ((N : ℝ) ^ d)⁻¹ * ∑ x, f x * sol x
  rw [sum_eq_sum_subtype V (fun x => f x * sol x)
    (fun x hx => by rw [hsol, dirichletSol_of_not_mem _ _ _ hx, mul_zero]), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem fineHamiltonian_transpose (ν a : ℝ) :
    (fineHamiltonian d ℓ N m ν a)ᵀ = fineHamiltonian d ℓ N m ν a := by
  have h1 := latticeLaplacian_isHermitian (d := d) (ℓ := ℓ) (ν / (N : ℝ) ^ 2)
  have h2 := blockProjMatrix_isHermitian (d := d) (ℓ := ℓ) (N := N) (m := m)
  unfold Matrix.IsHermitian at h1 h2
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2
  unfold fineHamiltonian
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, h1, h2]

/-- The form of the unit-lattice operator: `φ · H φ ≤ N² E(φ) + (ν + a) ‖φ‖²`. -/
theorem fineHamiltonian_quad_le (hℓ : ℓ = N * m) (hN : 0 < N) {ν a : ℝ} (ha : 0 ≤ a)
    (φ : Torus d ℓ → ℝ) :
    φ ⬝ᵥ fineHamiltonian d ℓ N m ν a *ᵥ φ ≤
      (N : ℝ) ^ 2 * latticeEnergy φ + (ν + a) * ∑ x, φ x ^ 2 := by
  have e : φ ⬝ᵥ fineHamiltonian d ℓ N m ν a *ᵥ φ =
      (N : ℝ) ^ 2 * (latticeEnergy φ + ν / (N : ℝ) ^ 2 * ∑ x, φ x ^ 2) +
        a * ∑ x, (blockProjection N m φ x) ^ 2 := by
    unfold fineHamiltonian
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      latticeLaplacian_quadratic, Matrix.smul_mulVec, dotProduct_smul,
      blockProj_quadratic (m := ℓ) (L := N) (M := m) hℓ hN φ]
    rfl
  have hP := sum_sq_eq_sum_sq_sub_add hℓ hN φ
  have hV : 0 ≤ ∑ x, (φ x - blockProjection N m φ x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN2 : (N : ℝ) ^ 2 ≠ 0 := by positivity
  rw [e, mul_add, show (N : ℝ) ^ 2 * (ν / (N : ℝ) ^ 2 * ∑ x, φ x ^ 2) = ν * ∑ x, φ x ^ 2 by
    field_simp]
  nlinarith

omit [NeZero m] in
theorem sum_blockFibre_eq_dotProduct (y : Torus d m) (s : Torus d ℓ → ℝ) :
    ∑ x ∈ (blockFibre N m y : Finset (Torus d ℓ)), s x = blockIndicator N m y ⬝ᵥ s := by
  simp only [dotProduct, blockIndicator, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  rfl

end Kernel

section Torus

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

theorem fineHamiltonian_quad_nonneg (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    (u : Torus d (N₀ * L ^ k) → ℝ) :
    0 ≤ u ⬝ᵥ fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a *ᵥ u := by
  have := (fineHamiltonian_posDef (mul_comm N₀ (L ^ k))
    (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))) hd hν ha).posSemidef
    |>.dotProduct_mulVec_nonneg u
  simpa using this

theorem fineHamiltonian_submatrix_isUnit (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    (V : Finset (Torus d (N₀ * L ^ k))) :
    IsUnit ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a).submatrix
      ((↑) : V → Torus d (N₀ * L ^ k)) ((↑) : V → Torus d (N₀ * L ^ k))) :=
  ((fineHamiltonian_posDef (mul_comm N₀ (L ^ k)) (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L)))
    hd hν ha).submatrix Subtype.val_injective).isUnit

/-- The Dirichlet solution of the unit-lattice operator satisfies the equation on `V`. -/
theorem fineDirichlet_eq (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    (V : Finset (Torus d (N₀ * L ^ k))) (F : Torus d (N₀ * L ^ k) → ℝ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ V) :
    (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a *ᵥ
      dirichletSol (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a) V F) x = F x :=
  mulVec_dirichletSol _ V F (fineHamiltonian_submatrix_isUnit hd hν ha V) hx

/-- **Block decay of the Dirichlet kernel**, with the constants of the whole-torus kernel:
`|Q_V (H_V)⁻¹ Q_V*(y, y')| ≤ C₀ e^{-δ₀ dist(y, y')}`, for every set `V` of fine sites. -/
theorem dirichletBlockKernel_decay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (V : Finset (Torus d (N₀ * L ^ k))) (y y' : Torus d N₀) :
    |dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ V ν a y y'| ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  rw [dirichletBlockKernel_apply]
  exact abs_blockAvg_le_of_eq hd hk hν ha1 ha2
    (fun x hx => fineDirichlet_eq hd hν (by linarith) V _ (mem_of_dirichletSol_ne_zero hx)) y

/-- **Entry decay of the Dirichlet Schur complement**, with the constants of `Δ_tr`. -/
theorem dirichletUnitOperator_decay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (V : Finset (Torus d (N₀ * L ^ k))) (y y' : Torus d N₀) :
    |dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ V ν a y y'| ≤
      (2 + 4 * blockDecayConst d L) * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) :=
  schurEntry_decay hd ha1 ha2 (dirichletBlockKernel_decay hd hk hν ha1 ha2 V) y y'

theorem fineDirichlet_univ (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    (F : Torus d (N₀ * L ^ k) → ℝ) :
    dirichletSol (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a) Finset.univ F =
      (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F := by
  have hU := (fineHamiltonian_posDef (mul_comm N₀ (L ^ k)) (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L)))
    hd hν ha).isUnit
  refine (eq_dirichletSol _ Finset.univ F (fineHamiltonian_submatrix_isUnit hd hν ha _)
    (fun x hx => absurd (Finset.mem_univ x) hx) (fun x _ => ?_)).symm
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
    Matrix.one_mulVec]

theorem dirichletBlockKernel_univ (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a) :
    dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ Finset.univ ν a =
      blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a := by
  ext y y'
  rw [dirichletBlockKernel_apply, blockGreenKernel_apply, fineDirichlet_univ hd hν ha]
  congr 1

/-- For `V` the whole fine torus the Dirichlet Schur complement is `Δ_tr`. -/
theorem dirichletUnitOperator_univ (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a) :
    dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ Finset.univ ν a =
      unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν a := by
  unfold dirichletUnitOperator
  rw [dirichletBlockKernel_univ hd hν ha]
  rfl

/-- **Monotonicity in the domain**: `V ⊆ W` gives `ψ · K_V ψ ≤ ψ · K_W ψ`. -/
theorem dirichletBlockKernel_quad_mono (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    {V W : Finset (Torus d (N₀ * L ^ k))} (hVW : V ⊆ W) (ψ : Torus d N₀ → ℝ) :
    ψ ⬝ᵥ dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ V ν a *ᵥ ψ ≤
      ψ ⬝ᵥ dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ W ν a *ᵥ ψ := by
  rw [dirichletBlockKernel_quad, dirichletBlockKernel_quad]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set H := fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a
  set f := blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) N₀ *ᵥ ψ
  have hid := dirichlet_pair_identity (fineHamiltonian_transpose ν a) hVW (f := f) (g := f)
    (yf := dirichletSol H V f) (yg := dirichletSol H V f) (zf := dirichletSol H W f)
    (zg := dirichletSol H W f) (fun x hx => dirichletSol_of_not_mem H V f hx)
    (fun x hx => dirichletSol_of_not_mem H V f hx) (fun x hx => fineDirichlet_eq hd hν ha V f hx)
    (fun x hx => dirichletSol_of_not_mem H W f hx) (fun x hx => fineDirichlet_eq hd hν ha W f hx)
    (fun x hx => dirichletSol_of_not_mem H W f hx) (fun x hx => fineDirichlet_eq hd hν ha W f hx)
  have := fineHamiltonian_quad_nonneg (L := L) (N₀ := N₀) (k := k) hd hν ha
    (dirichletSol H W f - dirichletSol H V f)
  linarith

/-- **Variational comparison**: `V ⊆ W` gives `ψ · U_W ψ ≤ ψ · U_V ψ` for the Dirichlet Schur
complements. -/
theorem dirichletUnitOperator_quad_mono (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a)
    {V W : Finset (Torus d (N₀ * L ^ k))} (hVW : V ⊆ W) (ψ : Torus d N₀ → ℝ) :
    ψ ⬝ᵥ dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ W ν a *ᵥ ψ ≤
      ψ ⬝ᵥ dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ V ν a *ᵥ ψ := by
  have h := dirichletBlockKernel_quad_mono (L := L) (N₀ := N₀) (k := k) hd hν ha hVW ψ
  unfold dirichletUnitOperator
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  nlinarith [sq_nonneg a]

/-- **Gap of the Dirichlet Schur complement**: in the mass window of `finalMass_real_lower`,
`ψ · U_V ψ ≥ g_* ‖ψ‖²` for every set `V` of fine sites (`U_V ⪰ Δ_tr`). -/
theorem dirichletUnitOperator_lower (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (V : Finset (Torus d (N₀ * L ^ k)))
    (ψ : Torus d N₀ → ℝ) :
    finalGap d L * ∑ x, ψ x ^ 2 ≤
      ψ ⬝ᵥ dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ V v a *ᵥ ψ := by
  have ha0 : 0 < a := by linarith
  refine (finalMass_real_lower (k := k) hd hv0 hv1 ha hmass ψ).trans ?_
  rw [← dirichletUnitOperator_univ hd hv0 ha0]
  exact dirichletUnitOperator_quad_mono hd hv0 ha0 (Finset.subset_univ V) ψ

/-- The Dirichlet Schur complement on `V` as a complex matrix on the `ℓ¹` coarse torus (the
analogue of `finalOp`, which is the case `V = univ`). -/
noncomputable abbrev dirichletFinalOp (d L N₀ k : ℕ) [NeZero N₀] [NeZero L]
    (V : Finset (Torus d (N₀ * L ^ k))) (v a : ℝ) : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  (dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ V v a).map (algebraMap ℝ ℂ)

theorem dirichletFinalOp_univ (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (ha : 0 < a) :
    dirichletFinalOp d L N₀ k Finset.univ v a = finalOp d L N₀ k v a := by
  unfold dirichletFinalOp finalOp
  rw [dirichletUnitOperator_univ hd hv0 ha]

/-- **Gap** of `dirichletFinalOp`: `g_* = finalGap d L`, the gap of `finalOp`. -/
theorem dirichletFinalOp_isCoercive (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (V : Finset (Torus d (N₀ * L ^ k))) :
    IsCoercive (dirichletFinalOp d L N₀ k V v a) (finalGap d L) :=
  isCoercive_map_of_real _ (dirichletUnitOperator_lower hd hv0 hv1 ha hmass V)

/-- **Entry decay** of `dirichletFinalOp`, with the constants `finalDecayC`, `blockDecayRate` of
`finalOp`. -/
theorem dirichletFinalOp_entry_decay (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (V : Finset (Torus d (N₀ * L ^ k))) (x y : L1Torus d N₀) :
    ‖dirichletFinalOp d L N₀ k V v a x y‖ ≤
      finalDecayC d L * Real.exp (-blockDecayRate d * dist x y) :=
  map_entry_decay_of_abs (dirichletUnitOperator_decay hd hk hv0 ha1 ha2 V) x y

end Torus

/-! ### Comparison of Dirichlet kernels deep inside the smaller domain -/

/-- The union of the blocks of the coarse set `Bc`: the fine sites `x` with `blockMap x ∈ Bc`. -/
def blockFibreSet {d ℓ : ℕ} [NeZero ℓ] (N m : ℕ) (Bc : Finset (Torus d m)) : Finset (Torus d ℓ) :=
  Finset.univ.filter fun x => blockMap N m x ∈ Bc

/-- The cutoff `θ(x) = max 0 (1 - dist(x, Vᶜ) / N)` (fine `ℓ¹` distance, `N = L ^ k`): `θ = 1` off
`V`, `0 ≤ θ ≤ 1`, `θ` is `1/N`-Lipschitz and vanishes at fine distance `≥ N` from `Vᶜ`. -/
noncomputable def fineCut (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (V : Finset (Torus d (N₀ * L ^ k)))
    (x : Torus d (N₀ * L ^ k)) : ℝ :=
  max 0 (1 - @setDist (L1Torus d (N₀ * L ^ k)) _
    ((↑(Finset.univ \ V) : Set (Torus d (N₀ * L ^ k)))) x / (L : ℝ) ^ k)

/-- The coarse blocks within fine distance `N + 1` of the complement of `V`. -/
noncomputable def boundaryBlocks (d L N₀ k : ℕ) [NeZero N₀] [NeZero L]
    (V : Finset (Torus d (N₀ * L ^ k))) : Finset (Torus d N₀) := by
  classical
  exact Finset.univ.filter fun Y => ∃ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))),
    ∃ u, u ∉ V ∧ torusDist d (N₀ * L ^ k) x u < (L : ℝ) ^ k + 1

/-- The constant of the deep comparison:
`(2 + 2d + ν + a) C₀² e^{δ₀ (d + 2)} B(δ₀)`, `B` the ball-sum constant. -/
noncomputable def dirichletCompConst (d L : ℕ) (ν a : ℝ) : ℝ :=
  (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 * Real.exp (blockDecayRate d * (d + 2)) *
    ballConst d (blockDecayRate d)

section Comparison

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

theorem fineCut_nonneg (V : Finset (Torus d (N₀ * L ^ k))) (x : Torus d (N₀ * L ^ k)) :
    0 ≤ fineCut d L N₀ k V x :=
  le_max_left _ _

theorem fineCut_le_one (V : Finset (Torus d (N₀ * L ^ k))) (x : Torus d (N₀ * L ^ k)) :
    fineCut d L N₀ k V x ≤ 1 := by
  have hN : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  have h0 := setDist_nonneg (ι := L1Torus d (N₀ * L ^ k))
    ((↑(Finset.univ \ V) : Set (Torus d (N₀ * L ^ k)))) x
  exact max_le zero_le_one (by linarith [div_nonneg h0 hN.le])

theorem fineCut_of_not_mem {V : Finset (Torus d (N₀ * L ^ k))} {x : Torus d (N₀ * L ^ k)}
    (hx : x ∉ V) : fineCut d L N₀ k V x = 1 := by
  set X : Set (L1Torus d (N₀ * L ^ k)) := ((↑(Finset.univ \ V) : Set (Torus d (N₀ * L ^ k))))
  have hmem : (x : L1Torus d (N₀ * L ^ k)) ∈ X :=
    Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hx⟩)
  have h0 : setDist X x = 0 := setDist_eq_zero_of_mem hmem
  show max 0 (1 - setDist X x / (L : ℝ) ^ k) = 1
  rw [h0, zero_div, sub_zero, max_eq_right zero_le_one]

theorem abs_fineCut_sub_le (V : Finset (Torus d (N₀ * L ^ k))) (x y : Torus d (N₀ * L ^ k)) :
    |fineCut d L N₀ k V x - fineCut d L N₀ k V y| ≤
      torusDist d (N₀ * L ^ k) x y / (L : ℝ) ^ k := by
  have hN : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  set X : Set (L1Torus d (N₀ * L ^ k)) := ((↑(Finset.univ \ V) : Set (Torus d (N₀ * L ^ k))))
  have h1 : setDist X x ≤ torusDist d (N₀ * L ^ k) x y + setDist X y :=
    setDist_le_dist_add X (x : L1Torus d (N₀ * L ^ k)) y
  have h2 : setDist X y ≤ torusDist d (N₀ * L ^ k) y x + setDist X x :=
    setDist_le_dist_add X (y : L1Torus d (N₀ * L ^ k)) x
  have hc : torusDist d (N₀ * L ^ k) y x = torusDist d (N₀ * L ^ k) x y :=
    dist_comm (α := L1Torus d (N₀ * L ^ k)) y x
  show |max 0 (1 - setDist X x / (L : ℝ) ^ k) - max 0 (1 - setDist X y / (L : ℝ) ^ k)| ≤ _
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have e : (1 - setDist X x / (L : ℝ) ^ k) - (1 - setDist X y / (L : ℝ) ^ k) =
      (setDist X y - setDist X x) / (L : ℝ) ^ k := by ring
  rw [e, abs_div, abs_of_pos hN]
  refine div_le_div_of_nonneg_right ?_ hN.le
  rw [abs_le]
  constructor <;> linarith

theorem exists_of_fineCut_ne_zero {V : Finset (Torus d (N₀ * L ^ k))} (hne : ∃ u, u ∉ V)
    {x : Torus d (N₀ * L ^ k)} (h : fineCut d L N₀ k V x ≠ 0) :
    ∃ u, u ∉ V ∧ torusDist d (N₀ * L ^ k) x u < (L : ℝ) ^ k := by
  have hN : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  set X : Set (L1Torus d (N₀ * L ^ k)) := ((↑(Finset.univ \ V) : Set (Torus d (N₀ * L ^ k))))
  have hlt : setDist X x < (L : ℝ) ^ k := by
    by_contra hge
    have hge := not_lt.1 hge
    apply h
    show max 0 (1 - setDist X x / (L : ℝ) ^ k) = 0
    refine max_eq_left ?_
    have : 1 ≤ setDist X x / (L : ℝ) ^ k := by rw [le_div_iff₀ hN]; linarith
    linarith
  obtain ⟨u₀, hu₀⟩ := hne
  have hX : X.Nonempty :=
    ⟨u₀, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hu₀⟩)⟩
  obtain ⟨u, hu, hdu⟩ := (Metric.infDist_lt_iff hX).1 hlt
  have hu' : u ∈ ((↑(Finset.univ \ V) : Set (Torus d (N₀ * L ^ k)))) := hu
  exact ⟨u, (Finset.mem_sdiff.1 (Finset.mem_coe.1 hu')).2, hdu⟩

/-- Pointwise bond bound for the cut-off field `θ z`:
`(θ z)(x + e_μ) - (θ z)(x)` squared is at most `2 (∂_μ z)² + 2 z(x)² / N²`. -/
theorem fineCut_bond_le (V : Finset (Torus d (N₀ * L ^ k))) (z : Torus d (N₀ * L ^ k) → ℝ)
    (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    (fineCut d L N₀ k V (x + Pi.single μ 1) * z (x + Pi.single μ 1) -
        fineCut d L N₀ k V x * z x) ^ 2 ≤
      2 * (z (x + Pi.single μ 1) - z x) ^ 2 + 2 * z x ^ 2 / ((L : ℝ) ^ k) ^ 2 := by
  have hN : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  set x' := x + Pi.single μ 1 with hx'
  set p := fineCut d L N₀ k V x'
  set q := fineCut d L N₀ k V x
  have hp0 : 0 ≤ p := fineCut_nonneg V x'
  have hp1 : p ≤ 1 := fineCut_le_one V x'
  have h1 : torusDist d (N₀ * L ^ k) x' x ≤ 1 := by
    have hc : torusDist d (N₀ * L ^ k) x' x = torusDist d (N₀ * L ^ k) x x' :=
      dist_comm (α := L1Torus d (N₀ * L ^ k)) x' x
    rw [hc, hx']
    exact Multiscale.torusDist_add_single_le x μ
  have hpq : |p - q| ≤ 1 / (L : ℝ) ^ k :=
    (abs_fineCut_sub_le V x' x).trans (div_le_div_of_nonneg_right h1 hN.le)
  have hpq2 : (p - q) ^ 2 ≤ 1 / ((L : ℝ) ^ k) ^ 2 := by
    rw [← sq_abs, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (abs_nonneg _) hpq 2
  have e : p * z x' - q * z x = p * (z x' - z x) + (p - q) * z x := by ring
  rw [e]
  have h2 : (p * (z x' - z x) + (p - q) * z x) ^ 2 ≤
      2 * (p * (z x' - z x)) ^ 2 + 2 * ((p - q) * z x) ^ 2 := by
    nlinarith [sq_nonneg (p * (z x' - z x) - (p - q) * z x)]
  have h3 : (p * (z x' - z x)) ^ 2 ≤ (z x' - z x) ^ 2 := by
    rw [mul_pow]; exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hp0 hp1)
  have h4 : ((p - q) * z x) ^ 2 ≤ z x ^ 2 / ((L : ℝ) ^ k) ^ 2 := by
    rw [mul_pow, div_eq_mul_one_div, mul_comm (z x ^ 2)]
    exact mul_le_mul_of_nonneg_right hpq2 (sq_nonneg _)
  calc _ ≤ 2 * (p * (z x' - z x)) ^ 2 + 2 * ((p - q) * z x) ^ 2 := h2
    _ ≤ 2 * (z x' - z x) ^ 2 + 2 * (z x ^ 2 / ((L : ℝ) ^ k) ^ 2) := by linarith
    _ = _ := by ring

/-- **Trial energy.**  For `V` with nonempty complement, the energy of `θ z` (`θ = fineCut`) is at
most the sum, over the fine sites within distance `N + 1` of `Vᶜ`, of
`2 N² Σ_μ (∂_μ z)² + (2d + ν + a) z²`. -/
theorem fineCut_trial_le {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a) {V : Finset (Torus d (N₀ * L ^ k))}
    (hne : ∃ u, u ∉ V) (z : Torus d (N₀ * L ^ k) → ℝ) :
    (fun x => fineCut d L N₀ k V x * z x) ⬝ᵥ fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a *ᵥ
        (fun x => fineCut d L N₀ k V x * z x) ≤
      ∑ x, if (∃ u, u ∉ V ∧ torusDist d (N₀ * L ^ k) x u < (L : ℝ) ^ k + 1) then
        2 * ((L : ℝ) ^ k) ^ 2 * ∑ μ : Fin d, (z (x + Pi.single μ 1) - z x) ^ 2 +
          (2 * d + ν + a) * z x ^ 2 else 0 := by
  classical
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN0 : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hN : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  set θ := fineCut d L N₀ k V with hθ
  have hq := fineHamiltonian_quad_le (d := d) (ℓ := N₀ * L ^ k) (N := L ^ k) (m := N₀) (ν := ν)
    hℓ hN0 ha (fun x => θ x * z x)
  push_cast at hq
  refine hq.trans ?_
  unfold latticeEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with hS
  · have hb := fun μ => fineCut_bond_le V z x μ
    have hsum : ((L : ℝ) ^ k) ^ 2 * ∑ μ : Fin d,
        (θ (x + Pi.single μ 1) * z (x + Pi.single μ 1) - θ x * z x) ^ 2 ≤
        2 * ((L : ℝ) ^ k) ^ 2 * ∑ μ : Fin d, (z (x + Pi.single μ 1) - z x) ^ 2 +
          2 * d * z x ^ 2 := by
      calc _ ≤ ((L : ℝ) ^ k) ^ 2 * ∑ μ : Fin d,
            (2 * (z (x + Pi.single μ 1) - z x) ^ 2 + 2 * z x ^ 2 / ((L : ℝ) ^ k) ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => hb μ) (sq_nonneg _)
        _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have hθx : (θ x * z x) ^ 2 ≤ z x ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _)
        (pow_le_one₀ (fineCut_nonneg V x) (fineCut_le_one V x))
    have hνa : 0 ≤ ν + a := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hθx hνa]
  · have hθx : θ x = 0 := by
      by_contra h
      obtain ⟨u, hu, hdu⟩ := exists_of_fineCut_ne_zero hne h
      exact hS ⟨u, hu, by linarith⟩
    have hθe : ∀ μ : Fin d, θ (x + Pi.single μ 1) = 0 := by
      intro μ
      by_contra h
      obtain ⟨u, hu, hdu⟩ := exists_of_fineCut_ne_zero hne h
      set x' := x + Pi.single μ 1 with hx'
      have ht : torusDist d (N₀ * L ^ k) x u ≤
          torusDist d (N₀ * L ^ k) x x' + torusDist d (N₀ * L ^ k) x' u :=
        dist_triangle (α := L1Torus d (N₀ * L ^ k)) x x' u
      have h1 : torusDist d (N₀ * L ^ k) x x' ≤ 1 := by
        rw [hx']; exact Multiscale.torusDist_add_single_le x μ
      exact hS ⟨u, hu, by linarith⟩
    simp [hθx, hθe]

/-- Grouping a sum over fine sites into the blocks of a set `T` of coarse sites containing the
blocks of all sites where the summand is switched on. -/
theorem sum_ite_le_sum_blocks {P : Torus d (N₀ * L ^ k) → Prop} [DecidablePred P]
    {g : Torus d (N₀ * L ^ k) → ℝ} (hg : ∀ x, 0 ≤ g x) (T : Finset (Torus d N₀))
    (hT : ∀ x, P x → blockMap (L ^ k) N₀ x ∈ T) :
    ∑ x, (if P x then g x else 0) ≤
      ∑ Y ∈ T, ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))), g x := by
  calc ∑ x, (if P x then g x else 0)
      = ∑ Y, ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))),
          (if P x then g x else 0) :=
        (Finset.sum_fiberwise Finset.univ (blockMap (L ^ k) N₀)
          (fun x => if P x then g x else 0)).symm
    _ = ∑ Y ∈ T, ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))),
          (if P x then g x else 0) := by
        refine (Finset.sum_subset (Finset.subset_univ T) fun Y _ hY => ?_).symm
        refine Finset.sum_eq_zero fun x hx => ?_
        have hnP : ¬ P x := fun hP => hY (mem_blockFibre.1 hx ▸ hT x hP)
        simp only [hnP, ite_false]
    _ ≤ _ := Finset.sum_le_sum fun Y _ => Finset.sum_le_sum fun x _ => by
        split_ifs
        · exact le_rfl
        · exact hg x

/-- **Block energy bound.**  If `(H w)(x) = 1_y(x)` wherever `w(x) ≠ 0`, then on the block `Y`,
`Σ (2 N² Σ_μ (∂_μ w)² + (2d + ν + a) w²) ≤ N^d (2 + 2d + ν + a) C₀² e^{-2 δ₀ dist(Y, y)}`. -/
theorem block_energy_le (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) {w : Torus d (N₀ * L ^ k) → ℝ} {y : Torus d N₀}
    (hw : ∀ x, w x ≠ 0 → (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a *ᵥ w) x =
      blockIndicator (L ^ k) N₀ y x) (Y : Torus d N₀) :
    ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))),
        (2 * ((L : ℝ) ^ k) ^ 2 * ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2 +
          (2 * d + ν + a) * w x ^ 2) ≤
      ((L ^ k : ℕ) : ℝ) ^ d * ((2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 *
        Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y))) := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN0 : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hN : (0 : ℝ) < (L : ℝ) ^ k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) k
  have hh := oneScale_blockDecay_fun hd hk hν ha1 ha2 hw
    (fun x hx => blockIndicator_support y x hx) Y
  rw [blockL2_blockIndicator hℓ hN0, mul_one] at hh
  unfold blockL2 at hh
  set c : ℝ := (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set G := ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))),
    ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2 with hG
  set Z := ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))), w x ^ 2 with hZ
  set E := blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ Y y)) with hE
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs1 := Real.sqrt_nonneg (c * G)
  have hs2 := Real.sqrt_nonneg (c * Z)
  have hgr : (L : ℝ) ^ k * Real.sqrt (c * G) ≤ E := by nlinarith
  have hnr : Real.sqrt (c * Z) ≤ E := by nlinarith
  have hgr2 : ((L : ℝ) ^ k) ^ 2 * (c * G) ≤ E ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hgr 2
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at this
  have hnr2 : c * Z ≤ E ^ 2 := by
    have := pow_le_pow_left₀ hs2 hnr 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have hE2 : E ^ 2 = blockDecayConst d L ^ 2 *
      Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y)) := by
    rw [hE, mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  have e : ∑ x ∈ (blockFibre (L ^ k) N₀ Y : Finset (Torus d (N₀ * L ^ k))),
      (2 * ((L : ℝ) ^ k) ^ 2 * ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2 +
        (2 * d + ν + a) * w x ^ 2) = 2 * ((L : ℝ) ^ k) ^ 2 * G + (2 * d + ν + a) * Z := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hcinv : ((L ^ k : ℕ) : ℝ) ^ d = c⁻¹ := by rw [hc, inv_inv]
  have hE2' : (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 *
      Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y)) = (2 + 2 * d + ν + a) * E ^ 2 := by
    rw [hE2]; ring
  rw [e, hcinv, hE2']
  have hc' : 0 ≤ 2 * (d : ℝ) + ν + a := by positivity
  have key : c * (2 * ((L : ℝ) ^ k) ^ 2 * G + (2 * d + ν + a) * Z) ≤
      (2 + 2 * d + ν + a) * E ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hnr2 hc']
  rw [le_inv_mul_iff₀ hc0]
  linarith

/-- **Deep comparison of the Dirichlet kernels** (general form).  For `V ⊆ W`,
`|K_W(y, y') - K_V(y, y')| ≤ (2 + 2d + ν + a) C₀² (S_V(y) S_V(y'))^{1/2}`, where
`S_V(y) = Σ_{Y ∈ boundaryBlocks V} e^{-2 δ₀ dist(Y, y)}` sums over the coarse blocks within fine
distance `N + 1` of `Vᶜ`.  Route: the pair identity writes the difference as `N⁻ᵈ e_y · H e_{y'}`,
Cauchy–Schwarz splits it, and the Dirichlet principle bounds `e_y · H e_y` by the energy of
`θ z_y` (`θ = fineCut`), which the block decay of `z_y = (H_W)⁻¹ 1_y` controls block by block. -/
theorem dirichletBlockKernel_sub_le (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {V W : Finset (Torus d (N₀ * L ^ k))} (hVW : V ⊆ W)
    (y y' : Torus d N₀) :
    |dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ W ν a y y' -
        dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ V ν a y y'| ≤
      (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 *
        Real.sqrt ((∑ Y ∈ boundaryBlocks d L N₀ k V,
            Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y))) *
          ∑ Y ∈ boundaryBlocks d L N₀ k V,
            Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y'))) := by
  classical
  have ha0 : 0 < a := by linarith
  set κ := (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  by_cases hne : ∃ u, u ∉ V
  swap
  · have hV : V = Finset.univ := Finset.eq_univ_of_forall fun u => by
      by_contra h; exact hne ⟨u, h⟩
    have hW : W = Finset.univ := Finset.eq_univ_of_forall fun u => hVW (hV ▸ Finset.mem_univ u)
    rw [hV, hW, sub_self, abs_zero]
    positivity
  set H := fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a with hH
  have hsym : Hᵀ = H := fineHamiltonian_transpose ν a
  have hpsd : ∀ u, 0 ≤ u ⬝ᵥ H *ᵥ u := fineHamiltonian_quad_nonneg hd hν ha0
  set c : ℝ := ((L ^ k : ℕ) : ℝ) ^ d with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) :=
      by exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
    positivity
  have henergy : ∀ z : Torus d N₀,
      (dirichletSol H W (blockIndicator (L ^ k) N₀ z) -
          dirichletSol H V (blockIndicator (L ^ k) N₀ z)) ⬝ᵥ H *ᵥ
        (dirichletSol H W (blockIndicator (L ^ k) N₀ z) -
          dirichletSol H V (blockIndicator (L ^ k) N₀ z)) ≤
      c * (κ * ∑ Y ∈ boundaryBlocks d L N₀ k V,
        Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y z))) := by
    intro z
    set f := blockIndicator (L ^ k) N₀ z (ℓ := N₀ * L ^ k) with hf
    set zf := dirichletSol H W f with hzf
    have h1 := dirichlet_principle hsym hpsd hVW (f := f) (yf := dirichletSol H V f) (zf := zf)
      (fun x hx => dirichletSol_of_not_mem H V f hx)
      (fun x hx => fineDirichlet_eq hd hν ha0 V f hx)
      (fun x hx => fineDirichlet_eq hd hν ha0 W f hx)
      (φ := fun x => fineCut d L N₀ k V x * zf x)
      (fun x hx => by rw [fineCut_of_not_mem hx, one_mul])
    have h2 := fineCut_trial_le (ν := ν) (a := a) hν ha0.le hne zf
    refine h1.trans (h2.trans ((sum_ite_le_sum_blocks (fun x => by positivity)
      (boundaryBlocks d L N₀ k V) (fun x hP => ?_)).trans ?_))
    · unfold boundaryBlocks
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x, mem_blockFibre.2 rfl, hP⟩
    · calc _ ≤ ∑ Y ∈ boundaryBlocks d L N₀ k V, c * ((2 + 2 * d + ν + a) *
            blockDecayConst d L ^ 2 * Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y z))) :=
          Finset.sum_le_sum fun Y _ => block_energy_le hd hk hν ha1 ha2 (w := zf) (y := z)
            (fun x hx => fineDirichlet_eq hd hν ha0 W f (mem_of_dirichletSol_ne_zero hx)) Y
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  set f := blockIndicator (L ^ k) N₀ y (ℓ := N₀ * L ^ k) with hf
  set g := blockIndicator (L ^ k) N₀ y' (ℓ := N₀ * L ^ k) with hg
  have hid := dirichlet_pair_identity hsym hVW (f := f) (g := g) (yf := dirichletSol H V f)
    (yg := dirichletSol H V g) (zf := dirichletSol H W f) (zg := dirichletSol H W g)
    (fun x hx => dirichletSol_of_not_mem H V f hx) (fun x hx => dirichletSol_of_not_mem H V g hx)
    (fun x hx => fineDirichlet_eq hd hν ha0 V g hx) (fun x hx => dirichletSol_of_not_mem H W f hx)
    (fun x hx => fineDirichlet_eq hd hν ha0 W f hx) (fun x hx => dirichletSol_of_not_mem H W g hx)
    (fun x hx => fineDirichlet_eq hd hν ha0 W g hx)
  have key : dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ W ν a y y' -
      dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ V ν a y y' =
      c⁻¹ * ((dirichletSol H W f - dirichletSol H V f) ⬝ᵥ H *ᵥ
        (dirichletSol H W g - dirichletSol H V g)) := by
    rw [dirichletBlockKernel_apply, dirichletBlockKernel_apply, sum_blockFibre_eq_dotProduct,
      sum_blockFibre_eq_dotProduct, hid, mul_sub]
  set Sy := ∑ Y ∈ boundaryBlocks d L N₀ k V,
    Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y)) with hSy
  set Sy' := ∑ Y ∈ boundaryBlocks d L N₀ k V,
    Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y')) with hSy'
  have hSy0 : 0 ≤ Sy := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hSy0' : 0 ≤ Sy' := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hB := Real.abs_le_sqrt (sq_dotProduct_mulVec_le hsym hpsd
    (dirichletSol H W f - dirichletSol H V f) (dirichletSol H W g - dirichletSol H V g))
  have hEE := mul_le_mul (henergy y) (henergy y') (hpsd _) (by positivity)
  have hsq : Real.sqrt ((c * (κ * Sy)) * (c * (κ * Sy'))) = c * κ * Real.sqrt (Sy * Sy') := by
    rw [show (c * (κ * Sy)) * (c * (κ * Sy')) = (c * κ) ^ 2 * (Sy * Sy') by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [key, abs_mul, abs_of_pos (inv_pos.2 hc0)]
  calc c⁻¹ * |(dirichletSol H W f - dirichletSol H V f) ⬝ᵥ H *ᵥ
        (dirichletSol H W g - dirichletSol H V g)|
      ≤ c⁻¹ * (c * κ * Real.sqrt (Sy * Sy')) :=
        mul_le_mul_of_nonneg_left (hB.trans ((Real.sqrt_le_sqrt hEE).trans_eq hsq))
          (inv_nonneg.2 hc0.le)
    _ = κ * Real.sqrt (Sy * Sy') := by field_simp

/-- For `V` the union of the blocks of a coarse set `Bc`, every boundary block lies within coarse
distance `d + 2` of a block outside `Bc`. -/
theorem exists_of_mem_boundaryBlocks {Bc : Finset (Torus d N₀)} {Y : Torus d N₀}
    (hY : Y ∈ boundaryBlocks d L N₀ k (blockFibreSet (L ^ k) N₀ Bc)) :
    ∃ Z, Z ∉ Bc ∧ torusDist d N₀ Y Z ≤ d + 2 := by
  classical
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN0 : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hN1 : (1 : ℝ) ≤ (L : ℝ) ^ k :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  unfold boundaryBlocks at hY
  obtain ⟨-, x, hx, u, hu, hdu⟩ := Finset.mem_filter.1 hY
  have hZ : blockMap (L ^ k) N₀ u ∉ Bc := fun h =>
    hu (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  refine ⟨_, hZ, ?_⟩
  have h1 := torusDist_coarse_le (d := d) hℓ hN0 (mem_blockFibre.1 hx) (rfl : blockMap (L ^ k) N₀ u = _)
  push_cast at h1
  have h2 : torusDist d (N₀ * L ^ k) x u / (L : ℝ) ^ k ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  linarith

/-- The boundary sum of a union of blocks: `S_V(y) ≤ e^{δ₀ (d + 2)} B(δ₀) e^{-δ₀ dist(y, Bcᶜ)}`. -/
theorem boundary_sum_le {Bc : Finset (Torus d N₀)} (hd : 0 < d) (y : Torus d N₀) :
    ∑ Y ∈ boundaryBlocks d L N₀ k (blockFibreSet (L ^ k) N₀ Bc),
        Real.exp (-(2 * blockDecayRate d * torusDist d N₀ Y y)) ≤
      Real.exp (blockDecayRate d * (d + 2)) * ballConst d (blockDecayRate d) *
        Real.exp (-(blockDecayRate d *
          @setDist (L1Torus d N₀) _ ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) y)) := by
  have hδ := blockDecayRate_pos hd
  set δ := blockDecayRate d with hδdef
  set X : Set (L1Torus d N₀) := ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) with hX
  set sy := setDist X y with hsy
  have hterm : ∀ Y ∈ boundaryBlocks d L N₀ k (blockFibreSet (L ^ k) N₀ Bc),
      Real.exp (-(2 * δ * torusDist d N₀ Y y)) ≤
        Real.exp (δ * (d + 2)) * Real.exp (-(δ * sy)) * Real.exp (-δ * torusDist d N₀ y Y) := by
    intro Y hY
    obtain ⟨Z, hZ, hYZ⟩ := exists_of_mem_boundaryBlocks hY
    have hZX : (Z : L1Torus d N₀) ∈ X :=
      Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hZ⟩)
    have hs : sy ≤ torusDist d N₀ y Z := setDist_le_dist hZX
    have ht : torusDist d N₀ y Z ≤ torusDist d N₀ y Y + torusDist d N₀ Y Z :=
      dist_triangle (α := L1Torus d N₀) y Y Z
    have hc : torusDist d N₀ Y y = torusDist d N₀ y Y := dist_comm (α := L1Torus d N₀) Y y
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [hc]
    have hs2 : sy ≤ torusDist d N₀ y Y + (d + 2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hs2 hδ.le]
  have hball : ∑ Y : Torus d N₀, Real.exp (-δ * torusDist d N₀ y Y) ≤ ballConst d δ :=
    ballSum_torus d N₀ hδ y
  have hA : 0 ≤ Real.exp (δ * (d + 2)) * Real.exp (-(δ * sy)) := by positivity
  calc _ ≤ ∑ Y ∈ boundaryBlocks d L N₀ k (blockFibreSet (L ^ k) N₀ Bc),
        Real.exp (δ * (d + 2)) * Real.exp (-(δ * sy)) * Real.exp (-δ * torusDist d N₀ y Y) :=
        Finset.sum_le_sum hterm
    _ = Real.exp (δ * (d + 2)) * Real.exp (-(δ * sy)) *
          ∑ Y ∈ boundaryBlocks d L N₀ k (blockFibreSet (L ^ k) N₀ Bc),
            Real.exp (-δ * torusDist d N₀ y Y) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (δ * (d + 2)) * Real.exp (-(δ * sy)) *
          ∑ Y : Torus d N₀, Real.exp (-δ * torusDist d N₀ y Y) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le) hA
    _ ≤ Real.exp (δ * (d + 2)) * Real.exp (-(δ * sy)) * ballConst d δ :=
        mul_le_mul_of_nonneg_left hball hA
    _ = _ := by ring

/-- **Deep comparison of the Dirichlet Schur complements.**  Let `V` be the union of the blocks of
a coarse set `Bc` and `W ⊇ V` any set of fine sites.  Then
`|U_V(y, y') - U_W(y, y')| ≤ a² C e^{-(δ₀/2)(dist(y, Bcᶜ) + dist(y', Bcᶜ))}`,
`C = dirichletCompConst d L ν a`, `δ₀ = blockDecayRate d` (coarse `ℓ¹` distances). -/
theorem dirichletUnitOperator_sub_le (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {Bc : Finset (Torus d N₀)} {W : Finset (Torus d (N₀ * L ^ k))}
    (hVW : blockFibreSet (L ^ k) N₀ Bc ⊆ W) (y y' : Torus d N₀) :
    |dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ (blockFibreSet (L ^ k) N₀ Bc) ν a y y' -
        dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ W ν a y y'| ≤
      a ^ 2 * dirichletCompConst d L ν a *
        Real.exp (-(blockDecayRate d / 2 *
          (@setDist (L1Torus d N₀) _ ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) y +
            @setDist (L1Torus d N₀) _ ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) y'))) := by
  have hδ := blockDecayRate_pos hd
  set δ := blockDecayRate d with hδdef
  set X : Set (L1Torus d N₀) := ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) with hX
  set V := blockFibreSet (L ^ k) N₀ Bc (ℓ := N₀ * L ^ k) with hV
  have e : dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ V ν a y y' -
      dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ W ν a y y' =
      a ^ 2 * (dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ W ν a y y' -
        dirichletBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ V ν a y y') := by
    simp only [dirichletUnitOperator, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg a), mul_assoc]
  refine mul_le_mul_of_nonneg_left ((dirichletBlockKernel_sub_le hd hk hν ha1 ha2 hVW y y').trans ?_)
    (sq_nonneg a)
  set A := Real.exp (δ * (d + 2)) * ballConst d δ with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; exact mul_nonneg (Real.exp_pos _).le (ballConst_decay_nonneg hδ)
  have h1 := boundary_sum_le (L := L) (k := k) (Bc := Bc) hd y
  have h2 := boundary_sum_le (L := L) (k := k) (Bc := Bc) hd y'
  have hS0 : 0 ≤ ∑ Y ∈ boundaryBlocks d L N₀ k V,
      Real.exp (-(2 * δ * torusDist d N₀ Y y)) := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hprod := mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
    (by positivity)
  have hsq : Real.sqrt ((A * Real.exp (-(δ * setDist X y))) * (A * Real.exp (-(δ * setDist X y')))) =
      A * Real.exp (-(δ / 2 * (setDist X y + setDist X y'))) := by
    rw [show (A * Real.exp (-(δ * setDist X y))) * (A * Real.exp (-(δ * setDist X y'))) =
        A ^ 2 * Real.exp (-(δ * (setDist X y + setDist X y'))) by
          rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, ← Real.exp_half]
    ring_nf
  have hκ0 : 0 ≤ (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 := by positivity
  calc (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 * Real.sqrt _
      ≤ (2 + 2 * d + ν + a) * blockDecayConst d L ^ 2 *
          (A * Real.exp (-(δ / 2 * (setDist X y + setDist X y')))) := by
        refine mul_le_mul_of_nonneg_left ?_ hκ0
        rw [← hsq]
        exact Real.sqrt_le_sqrt (by simpa only [hA, mul_assoc] using hprod)
    _ = _ := by rw [hA]; unfold dirichletCompConst; ring

/-- The deep comparison for the complex operators `dirichletFinalOp`. -/
theorem dirichletFinalOp_sub_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {Bc : Finset (Torus d N₀)} {W : Finset (Torus d (N₀ * L ^ k))}
    (hVW : blockFibreSet (L ^ k) N₀ Bc ⊆ W) (x y : L1Torus d N₀) :
    ‖dirichletFinalOp d L N₀ k (blockFibreSet (L ^ k) N₀ Bc) v a x y -
        dirichletFinalOp d L N₀ k W v a x y‖ ≤
      a ^ 2 * dirichletCompConst d L v a *
        Real.exp (-(blockDecayRate d / 2 *
          (@setDist (L1Torus d N₀) _ ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) x +
            @setDist (L1Torus d N₀) _ ((↑(Finset.univ \ Bc) : Set (Torus d N₀))) y))) := by
  have h := dirichletUnitOperator_sub_le hd hk hv0 ha1 ha2 hVW x y
  have e : dirichletFinalOp d L N₀ k (blockFibreSet (L ^ k) N₀ Bc) v a x y -
      dirichletFinalOp d L N₀ k W v a x y =
      (((dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ (blockFibreSet (L ^ k) N₀ Bc) v a x y -
        dirichletUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ W v a x y : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sub]; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact h

end Comparison

end Balaban.Green
