/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkOrdinary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KernelSeriesGeneral`: path-majorant estimates for an abstract graded kernel

An abstract estimate.  A kernel `C = ∑_n c n` on a finite set `ι` is given as a sum of real
matrices `c n` (the piece of grade `n`) with the weighted absolute row bound
`∑_{(n,y)} e^{γ n} |c n x y| ≤ A` for every row `x`.  Nothing else is assumed: no sign condition
and no adjacency structure.  For a scale factor `s ≥ 0` and the field `u = s • (C ψ)` the file
proves, on the event `sup_y ‖ψ_y‖ ≤ p`:

* (T1) the kernel is well defined, its entries and row sums are at most `A`, and the linear
  substitution `(C ψ)_x = ∑_{(n,y)} c n x y • ψ y` converges absolutely with weight `e^{γ n}`
  and total at most `p A`;
* (T2) the monomial `∏_i ℓ_i(u_{x_i})` expands into a family of terms indexed by tuples of
  pairs `(n_i, y_i)`; each depends on `ψ` only at the endpoints `y_i`, the weighted
  sup-norm total is at most `(s p A)^{|κ|}`, and the terms sum to the monomial;
* (T3) the same for a power series with finite absolute majorant;
* (T4) under a range hypothesis (`c n x y ≠ 0 → dist x y ≤ n`) each term is supported on, and
  depends on `ψ` only inside, the union of the balls `B(x_i, n_i)`;
* (T5) the truncated kernel `C_R = ∑_{n ≤ R} c n` has row tail at most `A e^{-γ (R+1)}`
  and entries vanishing beyond distance `R`;
* (T6) the walk kernel of the bare lattice operator is an instance, and the general bound
  reproduces `kf0TermBound_summable`.

The construction of range-graded pieces for the inverse square root of the stopped Hessian and
the last-integral theorems are NOT proved here; this file is generator-neutral.  No block count
is proved.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Filter Topology Balaban.LargeField

set_option linter.unusedSectionVars false

/-! ### Definitions -/

section Defs

variable {ι : Type} [Fintype ι]

/-- The kernel `C x y = ∑_n c n x y`. -/
noncomputable def genKernel (c : ℕ → Matrix ι ι ℝ) : Matrix ι ι ℝ := fun x y => ∑' n, c n x y

/-- The truncation `C_R = ∑_{n ≤ R} c n`. -/
noncomputable def genKernelTrunc (c : ℕ → Matrix ι ι ℝ) (R : ℕ) : Matrix ι ι ℝ :=
  ∑ n ∈ range (R + 1), c n

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {𝕜 : Type} [RCLike 𝕜]
  {κ : Type} [Fintype κ]

/-- The term of the product expansion of `∏_i ℓ_i(s (C ψ)_{x_i})` indexed by the tuple
`τ i = (n_i, y_i)`: `∏_i s c_{n_i}(x_i, y_i) ℓ_i(ψ_{y_i})`. -/
noncomputable def genTerm (c : ℕ → Matrix ι ι ℝ) (s : ℝ) (x : κ → ι) (ℓ : κ → W →L[ℝ] 𝕜)
    (τ : κ → ℕ × ι) (ψ : ι → W) : 𝕜 :=
  ∏ i, ((s * c (τ i).1 (x i) (τ i).2 : ℝ) : 𝕜) * ℓ i (ψ (τ i).2)

/-- The majorant `∏_i e^{γ n_i} (s |c_{n_i}(x_i, y_i)| p)`. -/
noncomputable def genTermBound (c : ℕ → Matrix ι ι ℝ) (s γ p : ℝ) (x : κ → ι)
    (τ : κ → ℕ × ι) : ℝ :=
  ∏ i, (Real.exp (γ * (τ i).1) * (s * |c (τ i).1 (x i) (τ i).2| * p))

/-- The factor slots of the monomial with exponent `α`: `α j` slots for the coordinate `j`. -/
abbrev GenSlot {D : ℕ} (α : Fin D → ℕ) : Type := Σ j : Fin D, Fin (α j)

/-- The index set of the expanded series. -/
abbrev GenSeriesIndex (ι : Type) (D : ℕ) : Type := Σ α : Fin D → ℕ, (GenSlot α → ℕ × ι)

/-- The term `a_α · ∏_{slots} s c ℓ(ψ)` of the expanded series. -/
noncomputable def genSeriesTerm {D : ℕ} (c : ℕ → Matrix ι ι ℝ) (s : ℝ) (x : Fin D → ι)
    (ℓ : Fin D → W →L[ℝ] 𝕜) (a : (Fin D → ℕ) → 𝕜) (ψ : ι → W) :
    GenSeriesIndex ι D → 𝕜 := fun t =>
  a t.1 * genTerm c s (fun k : GenSlot t.1 => x k.1) (fun k => ℓ k.1) t.2 ψ

/-- The majorant `‖a_α‖ θ^{|α|} ∏ ...` of the weighted terms. -/
noncomputable def genSeriesBound {D : ℕ} (c : ℕ → Matrix ι ι ℝ) (s γ p θ : ℝ)
    (x : Fin D → ι) (a : (Fin D → ℕ) → 𝕜) : GenSeriesIndex ι D → ℝ := fun t =>
  ‖a t.1‖ * θ ^ (∑ j, t.1 j) * genTermBound c s γ p (fun k : GenSlot t.1 => x k.1) t.2

end Defs

/-! ### T1: the kernel -/

section Kernel

variable {ι : Type} [Fintype ι] {c : ℕ → Matrix ι ι ℝ} {γ A : ℝ}

theorem gen_sum_tsum_fiber (G : ℕ × ι → ℝ) (hG : Summable G) :
    ∑ y, ∑' n, G (n, y) = ∑' q, G q := by
  have h1 : ∀ y, Summable fun n => G (n, y) := fun y =>
    hG.comp_injective (i := fun n : ℕ => (n, y)) fun a b h => by simpa using congrArg Prod.fst h
  rw [hG.tsum_prod' (fun n => Summable.of_finite)]
  simp_rw [tsum_fintype]
  rw [← Summable.tsum_finsetSum (fun y _ => h1 y)]

theorem gen_entry_summable (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|) (x y : ι) :
    Summable fun n => c n x y := by
  have h1 : Summable fun n : ℕ => Real.exp (γ * n) * |c n x y| :=
    (hS x).comp_injective (i := fun n : ℕ => (n, y)) fun a b h => by
      simpa using congrArg Prod.fst h
  refine Summable.of_norm_bounded h1 fun n => ?_
  rw [Real.norm_eq_abs]
  have : 1 ≤ Real.exp (γ * n) := Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
  nlinarith [abs_nonneg (c n x y)]

theorem gen_kernel_hasSum (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|) (x y : ι) :
    HasSum (fun n => c n x y) (genKernel c x y) :=
  (gen_entry_summable hγ hS x y).hasSum

/-- **(T1, tail row sum)** `∑_y |C x y - ∑_{n<k} c n x y| ≤ e^{-γ k} A`. -/
theorem gen_tail_rowsum_le (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A) (k : ℕ) (x : ι) :
    ∑ y, |genKernel c x y - ∑ n ∈ range k, c n x y| ≤ Real.exp (-γ * k) * A := by
  set F : ℕ × ι → ℝ := fun q => Real.exp (γ * q.1) * |c q.1 x q.2| with hF
  have hG : Summable fun q : ℕ × ι => F (q.1 + k, q.2) :=
    (hS x).comp_injective (i := fun q : ℕ × ι => (q.1 + k, q.2)) fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (by omega) h.2
  have hGy : ∀ y, Summable fun i : ℕ => F (i + k, y) := fun y =>
    hG.comp_injective (i := fun i : ℕ => (i, y)) fun a b h => by
      simpa using congrArg Prod.fst h
  have hy : ∀ y, |genKernel c x y - ∑ n ∈ range k, c n x y| ≤
      ∑' i : ℕ, Real.exp (-γ * k) * F (i + k, y) := by
    intro y
    have hes := gen_entry_summable hγ hS x y
    have e : genKernel c x y - ∑ n ∈ range k, c n x y = ∑' i, c (i + k) x y := by
      have := Summable.sum_add_tsum_nat_add k hes
      rw [genKernel]; linarith
    rw [e]
    have hg := (hGy y).mul_left (Real.exp (-γ * k))
    have := tsum_of_norm_bounded hg.hasSum (f := fun i : ℕ => c (i + k) x y) (fun i => by
      rw [Real.norm_eq_abs]
      simp only [hF]
      have e1 : Real.exp (-γ * k) * Real.exp (γ * ((i + k : ℕ) : ℝ)) = Real.exp (γ * i) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [← mul_assoc, e1]
      have : 1 ≤ Real.exp (γ * i) := Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
      nlinarith [abs_nonneg (c (i + k) x y)])
    simpa using this
  calc ∑ y, |genKernel c x y - ∑ n ∈ range k, c n x y|
      ≤ ∑ y, ∑' i : ℕ, Real.exp (-γ * k) * F (i + k, y) := Finset.sum_le_sum fun y _ => hy y
    _ = Real.exp (-γ * k) * ∑ y, ∑' i : ℕ, F (i + k, y) := by
        simp_rw [tsum_mul_left]; rw [Finset.mul_sum]
    _ = Real.exp (-γ * k) * ∑' q : ℕ × ι, F (q.1 + k, q.2) := by
        rw [gen_sum_tsum_fiber (fun q => F (q.1 + k, q.2)) hG]
    _ ≤ Real.exp (-γ * k) * ∑' q, F q := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact tsum_comp_le_tsum_of_inj (f := F) (hS x) (fun q => mul_nonneg (Real.exp_pos _).le
          (abs_nonneg _)) (i := fun q : ℕ × ι => (q.1 + k, q.2)) (fun a b h => by
            simp only [Prod.mk.injEq] at h
            exact Prod.ext (by omega) h.2)
    _ ≤ Real.exp (-γ * k) * A := mul_le_mul_of_nonneg_left (hA x) (Real.exp_pos _).le

/-- **(T1)** Row sums of the kernel: `∑_y |C x y| ≤ A`. -/
theorem gen_kernel_rowsum_le (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A) (x : ι) :
    ∑ y, |genKernel c x y| ≤ A := by
  simpa using gen_tail_rowsum_le hγ hS hA 0 x

/-- **(T1)** Entries of the kernel: `|C x y| ≤ A`. -/
theorem gen_kernel_abs_le (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A) (x y : ι) :
    |genKernel c x y| ≤ A :=
  (Finset.single_le_sum (f := fun y => |genKernel c x y|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ y)).trans (gen_kernel_rowsum_le hγ hS hA x)

/-- **(T1, truncation)** `∑_y |C x y - C_R x y| ≤ A e^{-γ (R+1)}` (T5). -/
theorem gen_trunc_tail_le (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A) (R : ℕ) (x : ι) :
    ∑ y, |genKernel c x y - genKernelTrunc c R x y| ≤ A * Real.exp (-γ * (R + 1)) := by
  have h := gen_tail_rowsum_le hγ hS hA (R + 1) x
  have e : ∀ y, genKernelTrunc c R x y = ∑ n ∈ range (R + 1), c n x y := fun y => by
    simp [genKernelTrunc, Matrix.sum_apply]
  simp only [e]
  push_cast at h
  linarith

/-- **(T5)** Under the range hypothesis, `C_R x y = 0` beyond distance `R`. -/
theorem genKernelTrunc_eq_zero {dist : ι → ι → ℝ} (hr : ∀ n x y, c n x y ≠ 0 → dist x y ≤ n)
    (R : ℕ) {x y : ι} (h : (R : ℝ) < dist x y) : genKernelTrunc c R x y = 0 := by
  simp only [genKernelTrunc, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun n hn => ?_
  by_contra hne
  have h1 := hr n x y hne
  have h2 : n ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have : (n : ℝ) ≤ R := by exact_mod_cast h2
  linarith

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **(T1, identity)** `(C ψ)_x = ∑_{(n,y)} c n x y • ψ y`. -/
theorem gen_substitution_hasSum (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (ψ : ι → W) (x : ι) :
    HasSum (fun q : ℕ × ι => c q.1 x q.2 • ψ q.2) (∑ y, genKernel c x y • ψ y) := by
  classical
  let G : ι → ℕ × ι → W := fun y q => if q.2 = y then c q.1 x y • ψ y else 0
  have hG : ∀ y, HasSum (G y) (genKernel c x y • ψ y) := by
    intro y
    have h0 : HasSum (fun n : ℕ => c n x y • ψ y) (genKernel c x y • ψ y) :=
      (gen_kernel_hasSum hγ hS x y).smul_const (ψ y)
    have hinj : Function.Injective (fun n : ℕ => (n, y)) := fun a b h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def, G] using h0
    · intro q hq
      have : q.2 ≠ y := fun h => hq ⟨q.1, Prod.ext rfl h.symm⟩
      simp [G, this]
  have hsum := hasSum_sum (s := (Finset.univ : Finset ι)) (fun y _ => hG y)
  have e1 : (fun b : ℕ × ι => ∑ y, G y b) = fun q : ℕ × ι => c q.1 x q.2 • ψ q.2 := by
    ext q : 1
    simp [G]
  rw [e1] at hsum
  exact hsum

/-- **(T1, weighted bound)** On the event `sup ‖ψ‖ ≤ p`,
`∑_{(n,y)} e^{γ n} ‖c n x y • ψ y‖ ≤ p A`. -/
theorem gen_substitution_weighted
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A)
    (ψ : ι → W) {p : ℝ} (hp0 : 0 ≤ p) (hp : ∀ y, ‖ψ y‖ ≤ p) (x : ι) :
    Summable (fun q : ℕ × ι => Real.exp (γ * q.1) * ‖c q.1 x q.2 • ψ q.2‖) ∧
      ∑' q : ℕ × ι, Real.exp (γ * q.1) * ‖c q.1 x q.2 • ψ q.2‖ ≤ p * A := by
  have hle : ∀ q : ℕ × ι, Real.exp (γ * q.1) * ‖c q.1 x q.2 • ψ q.2‖ ≤
      p * (Real.exp (γ * q.1) * |c q.1 x q.2|) := by
    intro q
    rw [norm_smul, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left (hp q.2)
      (mul_nonneg (Real.exp_pos (γ * q.1)).le (abs_nonneg (c q.1 x q.2)))
    nlinarith [this]
  have hnn : ∀ q : ℕ × ι, 0 ≤ Real.exp (γ * q.1) * ‖c q.1 x q.2 • ψ q.2‖ :=
    fun q => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hs := Summable.of_nonneg_of_le hnn hle ((hS x).mul_left p)
  refine ⟨hs, ?_⟩
  calc _ ≤ ∑' q : ℕ × ι, p * (Real.exp (γ * q.1) * |c q.1 x q.2|) :=
        hs.tsum_le_tsum hle ((hS x).mul_left p)
    _ = p * ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| := tsum_mul_left
    _ ≤ p * A := mul_le_mul_of_nonneg_left (hA x) hp0

end Kernel

/-! ### T2: monomials -/

section Monomial

variable {ι : Type} [Fintype ι] {c : ℕ → Matrix ι ι ℝ} {γ A : ℝ}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {𝕜 : Type} [RCLike 𝕜]
  {κ : Type} [Fintype κ]

/-- Each term depends on `ψ` only through the endpoints `y_i`. -/
theorem genTerm_congr (c : ℕ → Matrix ι ι ℝ) (s : ℝ) (x : κ → ι)
    (ℓ : κ → W →L[ℝ] 𝕜) (τ : κ → ℕ × ι) {ψ ψ' : ι → W}
    (h : ∀ i, ψ (τ i).2 = ψ' (τ i).2) :
    genTerm c s x ℓ τ ψ = genTerm c s x ℓ τ ψ' := by
  unfold genTerm
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

theorem genTermBound_nonneg {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (x : κ → ι) (τ : κ → ℕ × ι) :
    0 ≤ genTermBound c s γ p x τ :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (mul_nonneg hs (abs_nonneg _)) hp0)

/-- **(T2, sup bound)** `e^{γ ∑ n_i} |t_τ(ψ)|` is at most `genTermBound` for `sup ‖ψ‖ ≤ p`. -/
theorem genTerm_weighted_le {s : ℝ} (hs : 0 ≤ s) (γ p : ℝ) (x : κ → ι)
    (ℓ : κ → W →L[ℝ] 𝕜) (hℓ : ∀ i, ‖ℓ i‖ ≤ 1) (τ : κ → ℕ × ι)
    (ψ : ι → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Real.exp (γ * ∑ i, ((τ i).1 : ℝ)) * ‖genTerm c s x ℓ τ ψ‖ ≤
      genTermBound c s γ p x τ := by
  unfold genTerm genTermBound
  rw [norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  rw [norm_mul, RCLike.norm_ofReal, abs_mul, abs_of_nonneg hs]
  have h1 : ‖ℓ i (ψ (τ i).2)‖ ≤ p :=
    ((ℓ i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hℓ i) (norm_nonneg _)).trans
      (by simpa using hp _))
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs (abs_nonneg (c (τ i).1 (x i) (τ i).2)))
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- **(T2, total sup-norm)** The majorant is summable over tuples, with total at most
`(s p A)^{|κ|}`. -/
theorem genTermBound_summable
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A)
    {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) (x : κ → ι) :
    Summable (genTermBound c s γ p x) ∧
      ∑' τ, genTermBound c s γ p x τ ≤ (s * p * A) ^ Fintype.card κ := by
  let f : κ → ℕ × ι → ℝ := fun i q =>
    Real.exp (γ * q.1) * (s * |c q.1 (x i) q.2| * p)
  have hnn : ∀ i q, 0 ≤ f i q := fun i q =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hs (abs_nonneg _)) hp0)
  have hfe : ∀ i, f i = fun q => (s * p) * (Real.exp (γ * q.1) * |c q.1 (x i) q.2|) := by
    intro i; ext q; simp only [f]; ring
  have hsum : ∀ i, Summable fun q => ‖f i q‖ := by
    intro i
    refine ((hS (x i)).mul_left (s * p)).congr fun q => ?_
    rw [Real.norm_of_nonneg (hnn i q), hfe i]
  obtain ⟨_, h2⟩ := pi_prod_summable_hasSum (𝕜 := ℝ) κ f hsum
  have hB : ∀ i, ∑' q, f i q ≤ s * p * A := by
    intro i
    rw [hfe i, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hA (x i)) (mul_nonneg hs hp0)
  have e : genTermBound c s γ p x = fun τ => ∏ i, f i (τ i) := rfl
  rw [e]
  refine ⟨h2.summable, ?_⟩
  rw [h2.tsum_eq]
  calc ∏ i, ∑' q, f i q ≤ ∏ _i : κ, s * p * A :=
        Finset.prod_le_prod₀ (fun i _ => tsum_nonneg (hnn i)) fun i _ => hB i
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

/-- **(T2, identity)** The sum of the terms is the monomial `∏_i ℓ_i(s (C ψ)_{x_i})`,
absolutely convergent on the event `sup ‖ψ‖ ≤ p`. -/
theorem genTerm_hasSum (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p)
    (x : κ → ι) (ℓ : κ → W →L[ℝ] 𝕜) (hℓ : ∀ i, ‖ℓ i‖ ≤ 1)
    (ψ : ι → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun τ : κ → ℕ × ι => ‖genTerm c s x ℓ τ ψ‖) ∧
      HasSum (fun τ => genTerm c s x ℓ τ ψ)
        (∏ i, ℓ i (s • ∑ y, genKernel c (x i) y • ψ y)) := by
  let f : κ → ℕ × ι → 𝕜 := fun i q =>
    ((s * c q.1 (x i) q.2 : ℝ) : 𝕜) * ℓ i (ψ q.2)
  have hbd : ∀ i q, ‖f i q‖ ≤ (s * p) * (Real.exp (γ * q.1) * |c q.1 (x i) q.2|) := by
    intro i q
    have h1 : ‖ℓ i (ψ q.2)‖ ≤ p :=
      ((ℓ i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hℓ i) (norm_nonneg _)).trans
        (by simpa using hp _))
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hs (abs_nonneg (c q.1 (x i) q.2)))
    have h3 : 1 ≤ Real.exp (γ * q.1) :=
      Real.one_le_exp (mul_nonneg hγ (Nat.cast_nonneg _))
    simp only [f, norm_mul, RCLike.norm_ofReal, abs_mul, abs_of_nonneg hs]
    nlinarith [mul_nonneg (mul_nonneg hs (abs_nonneg (c q.1 (x i) q.2))) hp0]
  have hsum : ∀ i, Summable fun q => ‖f i q‖ := fun i =>
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) (hbd i) ((hS (x i)).mul_left (s * p))
  obtain ⟨h1, h2⟩ := pi_prod_summable_hasSum (𝕜 := 𝕜) κ f hsum
  have hval : ∀ i, ∑' q, f i q = ℓ i (s • ∑ y, genKernel c (x i) y • ψ y) := by
    intro i
    have h := (ℓ i).hasSum ((gen_substitution_hasSum hγ hS ψ (x i)).const_smul s)
    have e : f i = fun b : ℕ × ι => ℓ i (s • (c b.1 (x i) b.2 • ψ b.2)) := by
      ext q
      simp [f, RCLike.real_smul_eq_coe_mul, mul_assoc]
    rw [e]
    exact h.tsum_eq
  refine ⟨h1.congr fun τ => by unfold genTerm; exact (norm_prod _ _).symm, ?_⟩
  rw [Finset.prod_congr rfl fun i _ => hval i] at h2
  exact h2

/-! ### T4: range and support -/

/-- **(T4, support)** If `c n x y ≠ 0 → dist x y ≤ n`, a term with nonzero value has every
endpoint `y_i` within distance `n_i` of its anchor `x_i`. -/
theorem genTerm_endpoint_dist {dist : ι → ι → ℝ} (hr : ∀ n x y, c n x y ≠ 0 → dist x y ≤ n)
    {s : ℝ} (x : κ → ι) (ℓ : κ → W →L[ℝ] 𝕜) (τ : κ → ℕ × ι) (ψ : ι → W)
    (h : genTerm c s x ℓ τ ψ ≠ 0) (i : κ) : dist (x i) (τ i).2 ≤ (τ i).1 := by
  unfold genTerm at h
  have hi := (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)
  have : ((s * c (τ i).1 (x i) (τ i).2 : ℝ) : 𝕜) ≠ 0 := left_ne_zero_of_mul hi
  have h2 : s * c (τ i).1 (x i) (τ i).2 ≠ 0 := by exact_mod_cast this
  exact hr _ _ _ (right_ne_zero_of_mul h2)

/-- **(T4, locality)** Under the range hypothesis a term depends on `ψ` only on the union of
the balls `B(x_i, n_i) = {y | dist (x i) y ≤ n_i}`. -/
theorem genTerm_congr_of_ball {dist : ι → ι → ℝ} (hr : ∀ n x y, c n x y ≠ 0 → dist x y ≤ n)
    (s : ℝ) (x : κ → ι) (ℓ : κ → W →L[ℝ] 𝕜) (τ : κ → ℕ × ι) {ψ ψ' : ι → W}
    (h : ∀ y, (∃ i, dist (x i) y ≤ ((τ i).1 : ℝ)) → ψ y = ψ' y) :
    genTerm c s x ℓ τ ψ = genTerm c s x ℓ τ ψ' := by
  by_cases hz : genTerm c s x ℓ τ ψ = 0 ∧ genTerm c s x ℓ τ ψ' = 0
  · rw [hz.1, hz.2]
  · by_cases h0 : genTerm c s x ℓ τ ψ = 0
    · exfalso
      refine hz ⟨h0, ?_⟩
      by_contra h1
      have hd := genTerm_endpoint_dist hr x ℓ τ ψ' h1
      rw [genTerm_congr c s x ℓ τ (ψ' := ψ) (fun i => (h _ ⟨i, hd i⟩).symm)] at h1
      exact h1 h0
    · refine genTerm_congr c s x ℓ τ fun i => h _ ⟨i, ?_⟩
      exact genTerm_endpoint_dist hr x ℓ τ ψ h0 i

end Monomial

/-! ### T3: power series -/

section Series

variable {ι : Type} [Fintype ι] {c : ℕ → Matrix ι ι ℝ} {γ A : ℝ}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {𝕜 : Type} [RCLike 𝕜] {D : ℕ}

theorem card_genSlot (α : Fin D → ℕ) : Fintype.card (GenSlot α) = ∑ j, α j := by
  simp [Fintype.card_sigma]

/-- Termwise: `e^{γ n_tot} θ^{|α|} ‖a_α t‖ ≤ genSeriesBound`. -/
theorem genSeriesTerm_weighted_le {s : ℝ} (hs : 0 ≤ s) (γ p θ : ℝ) (x : Fin D → ι)
    (ℓ : Fin D → W →L[ℝ] 𝕜) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1) (a : (Fin D → ℕ) → 𝕜)
    (hθ : 0 ≤ θ) (ψ : ι → W) (hp : ∀ y, ‖ψ y‖ ≤ p) (t : GenSeriesIndex ι D) :
    Real.exp (γ * ∑ k, ((t.2 k).1 : ℝ)) * (θ ^ (∑ j, t.1 j) *
      ‖genSeriesTerm c s x ℓ a ψ t‖) ≤ genSeriesBound c s γ p θ x a t := by
  have h := genTerm_weighted_le (c := c) hs γ p (fun k : GenSlot t.1 => x k.1)
    (fun k => ℓ k.1) (fun k => hℓ k.1) t.2 ψ hp
  simp only [genSeriesTerm, genSeriesBound, norm_mul]
  calc _ = (‖a t.1‖ * θ ^ (∑ j, t.1 j)) * (Real.exp (γ * ∑ k, ((t.2 k).1 : ℝ)) *
        ‖genTerm c s (fun k : GenSlot t.1 => x k.1) (fun k => ℓ k.1) t.2 ψ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem genSeriesBound_fiber
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A)
    {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) {θ : ℝ} (hθ : 0 ≤ θ) (x : Fin D → ι)
    (a : (Fin D → ℕ) → 𝕜) (α : Fin D → ℕ) :
    Summable (fun τ : GenSlot α → ℕ × ι => genSeriesBound c s γ p θ x a ⟨α, τ⟩) ∧
      ∑' τ : GenSlot α → ℕ × ι, genSeriesBound c s γ p θ x a ⟨α, τ⟩ ≤
        ‖a α‖ * (θ * (s * p * A)) ^ (∑ j, α j) := by
  obtain ⟨h1, h2⟩ := genTermBound_summable (c := c) hS hA hs hp0 (fun k : GenSlot α => x k.1)
  rw [card_genSlot] at h2
  have h1' := h1.mul_left (‖a α‖ * θ ^ (∑ j, α j))
  refine ⟨h1'.congr fun τ => rfl, ?_⟩
  have : ∑' τ : GenSlot α → ℕ × ι, genSeriesBound c s γ p θ x a ⟨α, τ⟩ =
      (‖a α‖ * θ ^ (∑ j, α j)) * ∑' τ, genTermBound c s γ p
        (fun k : GenSlot α => x k.1) τ := by
    rw [← tsum_mul_left]; rfl
  rw [this, mul_pow]
  calc _ ≤ (‖a α‖ * θ ^ (∑ j, α j)) * (s * p * A) ^ (∑ j, α j) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- **(T3, total weighted norm)** -/
theorem genSeriesBound_summable
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A)
    {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) {θ : ℝ} (hθ : 0 ≤ θ) (x : Fin D → ι)
    (a : (Fin D → ℕ) → 𝕜)
    (hM : Summable fun α : Fin D → ℕ => ‖a α‖ * (θ * (s * p * A)) ^ (∑ j, α j)) :
    Summable (genSeriesBound c s γ p θ x a) ∧
      ∑' t, genSeriesBound c s γ p θ x a t ≤
        ∑' α : Fin D → ℕ, ‖a α‖ * (θ * (s * p * A)) ^ (∑ j, α j) := by
  have hfib := fun α => genSeriesBound_fiber (c := c) hS hA hs hp0 hθ x a α
  have hnn : ∀ t, 0 ≤ genSeriesBound c s γ p θ x a t := fun t =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hθ _))
      (genTermBound_nonneg hs hp0 _ _)
  have hfnn : ∀ α, 0 ≤ ∑' τ : GenSlot α → ℕ × ι,
      genSeriesBound c s γ p θ x a ⟨α, τ⟩ := fun α => tsum_nonneg fun τ => hnn _
  have hS' : Summable (genSeriesBound c s γ p θ x a) :=
    (summable_sigma_of_nonneg hnn).2 ⟨fun α => (hfib α).1,
      Summable.of_nonneg_of_le hfnn (fun α => (hfib α).2) hM⟩
  refine ⟨hS', ?_⟩
  rw [hS'.tsum_sigma']
  · exact (Summable.of_nonneg_of_le hfnn (fun α => (hfib α).2) hM).tsum_le_tsum
      (fun α => (hfib α).2) hM
  · exact fun α => (hfib α).1

/-- **(T3, identity)** On the event `sup ‖ψ‖ ≤ p`, the family `a_α t_τ(ψ)` is absolutely
summable and sums to the series `∑_α a_α ∏_j (ℓ_j u_{x_j})^{α_j}` at `u = s (C ψ)`. -/
theorem genSeriesTerm_hasSum (hγ : 0 ≤ γ)
    (hS : ∀ x, Summable fun q : ℕ × ι => Real.exp (γ * q.1) * |c q.1 x q.2|)
    (hA : ∀ x, ∑' q : ℕ × ι, Real.exp (γ * q.1) * |c q.1 x q.2| ≤ A)
    {s p : ℝ} (hs : 0 ≤ s) (hp0 : 0 ≤ p) {θ : ℝ} (hθ : 1 ≤ θ) (x : Fin D → ι)
    (ℓ : Fin D → W →L[ℝ] 𝕜) (hℓ : ∀ j, ‖ℓ j‖ ≤ 1) (a : (Fin D → ℕ) → 𝕜)
    (hM : Summable fun α : Fin D → ℕ => ‖a α‖ * (θ * (s * p * A)) ^ (∑ j, α j))
    (ψ : ι → W) (hp : ∀ y, ‖ψ y‖ ≤ p) :
    Summable (fun t => ‖genSeriesTerm c s x ℓ a ψ t‖) ∧
      HasSum (genSeriesTerm c s x ℓ a ψ)
        (∑' α : Fin D → ℕ, a α * ∏ j, (ℓ j (s • ∑ y, genKernel c (x j) y • ψ y)) ^ (α j)) := by
  have hθ0 : 0 ≤ θ := by linarith
  obtain ⟨hB, -⟩ := genSeriesBound_summable (c := c) hS hA hs hp0 hθ0 x a hM
  have hle : ∀ t, ‖genSeriesTerm c s x ℓ a ψ t‖ ≤ genSeriesBound c s γ p θ x a t := by
    intro t
    refine le_trans ?_ (genSeriesTerm_weighted_le hs γ p θ x ℓ hℓ a hθ0 ψ hp t)
    have h1 : 1 ≤ Real.exp (γ * ∑ k, ((t.2 k).1 : ℝ)) :=
      Real.one_le_exp (mul_nonneg hγ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _))
    have h2 : 1 ≤ θ ^ (∑ j, t.1 j) := one_le_pow₀ hθ
    have h3 := norm_nonneg (genSeriesTerm c s x ℓ a ψ t)
    have h4 : 1 ≤ Real.exp (γ * ∑ k, ((t.2 k).1 : ℝ)) * θ ^ (∑ j, t.1 j) :=
      one_le_mul_of_one_le_of_one_le h1 h2
    have h5 := mul_le_mul_of_nonneg_right h4 h3
    linarith [mul_assoc (Real.exp (γ * ∑ k, ((t.2 k).1 : ℝ))) (θ ^ (∑ j, t.1 j))
      ‖genSeriesTerm c s x ℓ a ψ t‖]
  have hsn : Summable (fun t => ‖genSeriesTerm c s x ℓ a ψ t‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hB
  refine ⟨hsn, ?_⟩
  have hfibv : ∀ α : Fin D → ℕ,
      HasSum (fun τ : GenSlot α → ℕ × ι => genSeriesTerm c s x ℓ a ψ ⟨α, τ⟩)
        (a α * ∏ j, (ℓ j (s • ∑ y, genKernel c (x j) y • ψ y)) ^ (α j)) := by
    intro α
    obtain ⟨-, h⟩ := genTerm_hasSum (c := c) hγ hS hs hp0
      (fun k : GenSlot α => x k.1) (fun k => ℓ k.1) (fun k => hℓ k.1) ψ hp
    have h' := h.mul_left (a α)
    have e : (∏ k : GenSlot α, ℓ k.1 (s • ∑ y, genKernel c (x k.1) y • ψ y)) =
        ∏ j, (ℓ j (s • ∑ y, genKernel c (x j) y • ψ y)) ^ (α j) := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp
    rw [e] at h'
    exact h'
  have hnorm : ∀ α : Fin D → ℕ, ‖a α * ∏ j, (ℓ j (s • ∑ y, genKernel c (x j) y • ψ y)) ^ (α j)‖ ≤
      ‖a α‖ * (θ * (s * p * A)) ^ (∑ j, α j) := by
    intro α
    obtain ⟨hs', hb⟩ := genSeriesBound_fiber (c := c) hS hA hs hp0 hθ0 x a α
    have := tsum_of_norm_bounded hs'.hasSum (fun τ => hle ⟨α, τ⟩)
    rw [(hfibv α).tsum_eq] at this
    exact this.trans hb
  have hgs : Summable (fun α : Fin D → ℕ =>
      a α * ∏ j, (ℓ j (s • ∑ y, genKernel c (x j) y • ψ y)) ^ (α j)) :=
    Summable.of_norm_bounded hM hnorm
  exact hgs.hasSum.sigma_of_hasSum hfibv hsn.of_norm

end Series

/-! ### T6: the walk kernel as an instance -/

section WalkInstance

variable {d m : ℕ} [NeZero m]

/-- The graded pieces `c n = w_n A^n` of the walk series. -/
noncomputable def walkPieces (d m : ℕ) [NeZero m] (ν : ℝ) (n : ℕ) :
    Matrix (Torus d m) (Torus d m) ℝ := walkWeight d ν n • kf0Adj d m ^ n

theorem walkPieces_apply (ν : ℝ) (n : ℕ) (x y : Torus d m) :
    walkPieces d m ν n x y = walkWeight d ν n * (kf0Adj d m ^ n) x y := by
  simp [walkPieces, Matrix.smul_apply]

theorem walkPieces_nonneg {ν : ℝ} (hν : 0 < ν) (n : ℕ) (x y : Torus d m) :
    0 ≤ walkPieces d m ν n x y := by
  rw [walkPieces_apply]
  exact mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n x y)

theorem genKernel_walkPieces (ν : ℝ) : genKernel (walkPieces d m ν) = kf0C d m ν := by
  ext x y
  simp only [genKernel, kf0C, walkPieces_apply]

/-- The weighted row bound (H) for the walk pieces, with `A = kf0WalkA d g γ`. -/
theorem walkPieces_rowBound {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) {γ : ℝ}
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (x : Torus d m) :
    Summable (fun q : ℕ × Torus d m => Real.exp (γ * q.1) * |walkPieces d m ν q.1 x q.2|) ∧
      ∑' q : ℕ × Torus d m, Real.exp (γ * q.1) * |walkPieces d m ν q.1 x q.2| ≤
        kf0WalkA d g γ := by
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  have e : (fun q : ℕ × Torus d m => Real.exp (γ * q.1) * |walkPieces d m ν q.1 x q.2|) =
      fun q => Real.exp (γ * q.1) * (walkWeight d ν q.1 * (kf0Adj d m ^ q.1) x q.2) := by
    ext q
    rw [abs_of_nonneg (walkPieces_nonneg hν _ _ _), walkPieces_apply]
  rw [e]
  exact kf0_weighted_row_summable hg hgν hq x

/-- The range hypothesis for the walk pieces, with the lattice distance. -/
theorem walkPieces_range (ν : ℝ) (n : ℕ) (x y : Torus d m) (h : walkPieces d m ν n x y ≠ 0) :
    torusDist d m x y ≤ n := by
  rw [walkPieces_apply] at h
  exact kf0Adj_pow_dist (right_ne_zero_of_mul h)

theorem kf0TermBound_eq_genTermBound {ι : Type} [Fintype ι] {ν : ℝ} (hν : 0 < ν) (β γ p : ℝ)
    (x : ι → Torus d m) :
    kf0TermBound d m ν β γ p x = genTermBound (walkPieces d m ν) (Real.sqrt β)⁻¹ γ p x := by
  ext τ
  unfold kf0TermBound genTermBound
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_of_nonneg (walkPieces_nonneg hν _ _ _), walkPieces_apply, kf0WalkCoeff]

/-- **(T6)** Consistency: the general bound for the walk pieces gives the landed
`kf0TermBound_summable`. -/
theorem genTermBound_walkPieces_summable {ι : Type} [Fintype ι] {ν g : ℝ} (hg : 0 < g)
    (hgν : g ≤ ν) {γ : ℝ} (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1)
    (β : ℝ) {p : ℝ} (hp0 : 0 ≤ p) (x : ι → Torus d m) :
    Summable (genTermBound (walkPieces d m ν) (Real.sqrt β)⁻¹ γ p x) ∧
      ∑' τ, genTermBound (walkPieces d m ν) (Real.sqrt β)⁻¹ γ p x τ ≤
        (p * kf0WalkA d g γ / Real.sqrt β) ^ Fintype.card ι := by
  have _ := hγ
  obtain ⟨h1, h2⟩ := genTermBound_summable (c := walkPieces d m ν) (γ := γ)
    (A := kf0WalkA d g γ) (fun x => (walkPieces_rowBound hg hgν hq x).1)
    (fun x => (walkPieces_rowBound hg hgν hq x).2)
    (inv_nonneg.2 (Real.sqrt_nonneg β)) hp0 x
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [div_eq_mul_inv]; ring_nf

end WalkInstance

end Balaban.Green
