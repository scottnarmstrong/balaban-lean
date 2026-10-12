/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventAbs
public import Balaban.Green.CombesThomas
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Localization.DecoupledIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Block Schur test and exponential decay of the base resolvent (BASE-KERNEL-3 (1.7))

For a matrix `B` on `ι × Fin N` with `N × N` blocks `blockOf B z w`: the Schur test for the quadratic
form with block operator norms (`reQuad_ge_of_block_bound`), and, for a coercive `B` with block row
and column sums at most `J` and range `R`, the decay `‖((B + x)⁻¹)(z,w)‖_op ≤ (γ/2 + x)⁻¹ e^{-g δ(z,w)}`
when `J (e^{gR} - 1) ≤ γ/2` (`resolvent_block_decay`), and the corresponding bound for the Stieltjes
inverse square root (`sqrtMat_block_decay`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban.Green
open scoped Matrix.Norms.L2Operator

section Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The `z`-th component of a field on `ι × Fin N`. -/
def slice (f : ι × Fin N → ℂ) (z : ι) : Fin N → ℂ := fun i => f (z, i)

/-- The `N × N` block `(z, w)` of a matrix on `ι × Fin N`. -/
def blockOf (B : Matrix (ι × Fin N) (ι × Fin N) ℂ) (z w : ι) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => B (z, i) (w, j)

omit [DecidableEq ι] in
theorem sqNorm_eq_sum_slice (f : ι × Fin N → ℂ) : sqNorm f = ∑ z, sqNorm (slice f z) := by
  unfold sqNorm slice
  rw [Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem star_dot_mulVec_eq_blocks (D : Matrix (ι × Fin N) (ι × Fin N) ℂ) (v : ι × Fin N → ℂ) :
    star v ⬝ᵥ (D *ᵥ v) = ∑ z, ∑ w, star (slice v z) ⬝ᵥ (blockOf D z w *ᵥ slice v w) := by
  simp only [dotProduct, Matrix.mulVec, slice, blockOf, Matrix.of_apply, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem norm_star_dot_le {n : Type*} [Fintype n] (a c : n → ℂ) :
    ‖star a ⬝ᵥ c‖ ≤ Real.sqrt (sqNorm a) * Real.sqrt (sqNorm c) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a) (WithLp.toLp 2 c)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  simp only [PiLp.inner_apply] at h
  convert h using 2
  · simp [dotProduct, mul_comm]
  · simp [sqNorm]
  · simp [sqNorm]

theorem norm_star_dot_block_le (M : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N → ℂ) :
    ‖star a ⬝ᵥ (M *ᵥ b)‖ ≤ Real.sqrt (sqNorm a) * (‖M‖ * Real.sqrt (sqNorm b)) := by
  refine (norm_star_dot_le a _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq (norm_nonneg M), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (sqNorm_mulVec_le_opNorm M b)

omit [DecidableEq ι] in
/-- **Schur test for the quadratic form, with `N × N` block operator norms.** -/
theorem reQuad_ge_of_block_bound (D : Matrix (ι × Fin N) (ι × Fin N) ℂ) (E : ι → ι → ℝ)
    (hDE : ∀ z w, ‖blockOf D z w‖ ≤ E z w) {S : ℝ}
    (hrow : ∀ z, ∑ w, E z w ≤ S) (hcol : ∀ w, ∑ z, E z w ≤ S) (v : ι × Fin N → ℂ) :
    -(S * sqNorm v) ≤ reQuad D v := by
  have hE : ∀ z w, 0 ≤ E z w := fun z w => (norm_nonneg _).trans (hDE z w)
  set n : ι → ℝ := fun z => Real.sqrt (sqNorm (slice v z)) with hn
  have hn2 : ∀ z, n z ^ 2 = sqNorm (slice v z) := fun z => Real.sq_sqrt (sqNorm_nonneg _)
  have hn0 : ∀ z, 0 ≤ n z := fun z => Real.sqrt_nonneg _
  have h1 : |reQuad D v| ≤ ∑ z, ∑ w, E z w * ((n z ^ 2 + n w ^ 2) / 2) := by
    rw [reQuad_eq_dot, star_dot_mulVec_eq_blocks]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    refine (norm_star_dot_block_le _ _ _).trans ?_
    have h2 : n z * n w ≤ (n z ^ 2 + n w ^ 2) / 2 := by
      nlinarith [sq_nonneg (n z - n w)]
    calc n z * (‖blockOf D z w‖ * n w) = ‖blockOf D z w‖ * (n z * n w) := by ring
      _ ≤ E z w * ((n z ^ 2 + n w ^ 2) / 2) :=
        mul_le_mul (hDE z w) h2 (mul_nonneg (hn0 z) (hn0 w)) (hE z w)
  have h2 : ∑ z, ∑ w, E z w * ((n z ^ 2 + n w ^ 2) / 2) ≤ S * sqNorm v := by
    have e : ∑ z, ∑ w, E z w * ((n z ^ 2 + n w ^ 2) / 2)
        = (1 / 2) * (∑ z, n z ^ 2 * ∑ w, E z w) + (1 / 2) * (∑ w, n w ^ 2 * ∑ z, E z w) := by
      have : ∑ w, n w ^ 2 * ∑ z, E z w = ∑ z, ∑ w, n w ^ 2 * E z w := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
      rw [this]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
      ring
    have hsq : sqNorm v = ∑ z, n z ^ 2 := by
      rw [sqNorm_eq_sum_slice]; exact Finset.sum_congr rfl fun z _ => (hn2 z).symm
    have a1 : ∑ z, n z ^ 2 * ∑ w, E z w ≤ S * sqNorm v := by
      rw [hsq, Finset.mul_sum]
      exact Finset.sum_le_sum fun z _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hrow z) (sq_nonneg _)
    have a2 : ∑ w, n w ^ 2 * ∑ z, E z w ≤ S * sqNorm v := by
      rw [hsq, Finset.mul_sum]
      exact Finset.sum_le_sum fun w _ => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hcol w) (sq_nonneg _)
    rw [e]; linarith
  linarith [neg_abs_le (reQuad D v)]

theorem abs_exp_sub_one_le (t : ℝ) : |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
  · rw [abs_of_nonpos h, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 h])]
    have h1 := Real.add_one_le_exp t
    have h2 := Real.add_one_le_exp (-t)
    linarith

variable (δ : ι → ι → ℝ)

/-- **Combes–Thomas decay with block row sums and finite range** (BASE-KERNEL-3 (1.7)).
`δ` is a metric on the sites, `B` is `γ`-coercive, its blocks vanish beyond range `R` and have
block-operator-norm row and column sums at most `J`; if `J (e^{gR} - 1) ≤ γ/2` then for `x ≥ 0`
`B + x` is invertible and the `(z,w)` block of its inverse has operator norm at most
`(γ/2 + x)⁻¹ e^{-g δ(z,w)}`. -/
theorem resolvent_block_decay (hδ0 : ∀ z, δ z z = 0)
    (hδs : ∀ z w, δ z w = δ w z) (hδt : ∀ z y w, δ z w ≤ δ z y + δ y w)
    {B : Matrix (ι × Fin N) (ι × Fin N) ℂ} {γ J R g x : ℝ} (hγ : 0 < γ) (hcoer : IsCoercive B γ)
    (hx : 0 ≤ x) (hR : ∀ z y, blockOf B z y ≠ 0 → δ z y ≤ R) (hR0 : 0 ≤ R)
    (hrow : ∀ z, ∑ y, ‖blockOf B z y‖ ≤ J) (hcol : ∀ y, ∑ z, ‖blockOf B z y‖ ≤ J)
    (hg : 0 ≤ g) (hJ : J * (Real.exp (g * R) - 1) ≤ γ / 2) :
    IsUnit (B + (x : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ)) ∧
      ∀ z w, ‖blockOf (B + (x : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ))⁻¹ z w‖ ≤
        (γ / 2 + x)⁻¹ * Real.exp (-g * δ z w) := by
  have hcx := hcoer.add_smul_one x
  have hγx : 0 < γ + x := by linarith
  have hU := isUnit_of_isCoercive hγx hcx
  refine ⟨hU, fun z w0 => ?_⟩
  set Bx := B + (x : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) with hBx
  set a : ι × Fin N → ℝ := fun p => g * δ p.1 w0 with ha
  have hJ0 : 0 ≤ J :=
    (Finset.sum_nonneg fun y _ => norm_nonneg (blockOf B z y)).trans (hrow z)
  have hexpR : 0 ≤ Real.exp (g * R) - 1 := by
    have := Real.add_one_le_exp (g * R); nlinarith [mul_nonneg hg hR0]
  -- the conjugation error is small
  set Dm : Matrix (ι × Fin N) (ι × Fin N) ℂ := conjMat a B - B with hDm
  have hDblk : ∀ z y, ‖blockOf Dm z y‖ ≤ (Real.exp (g * R) - 1) * ‖blockOf B z y‖ := by
    intro z y
    by_cases h0 : blockOf B z y = 0
    · have : blockOf Dm z y = 0 := by
        ext i j
        have := congrFun (congrFun h0 i) j
        simp only [blockOf, Matrix.of_apply, Matrix.zero_apply] at this ⊢
        simp [hDm, conjMat, this]
      rw [this, norm_zero]; exact mul_nonneg hexpR (norm_nonneg _)
    · have hr := hR z y h0
      have hfac : blockOf Dm z y = ((Real.exp (g * δ z w0 - g * δ y w0) - 1 : ℝ) : ℂ) •
          blockOf B z y := by
        ext i j
        simp only [blockOf, Matrix.of_apply, Matrix.smul_apply, hDm, Matrix.sub_apply, conjMat,
          ha, smul_eq_mul]
        push_cast
        ring
      rw [hfac, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ((abs_exp_sub_one_le _).trans ?_) (norm_nonneg _)
      have h1 : |g * δ z w0 - g * δ y w0| ≤ g * R := by
        have a1 := hδt z y w0
        have a2 := hδt y z w0
        rw [hδs y z] at a2
        rw [abs_le]
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left hr hg]
      have := Real.exp_le_exp.2 h1
      linarith
  set E : ι → ι → ℝ := fun z y => (Real.exp (g * R) - 1) * ‖blockOf B z y‖ with hE
  have hS : ∀ z, ∑ y, E z y ≤ γ / 2 := by
    intro z
    simp only [hE, ← Finset.mul_sum]
    calc (Real.exp (g * R) - 1) * ∑ y, ‖blockOf B z y‖ ≤ (Real.exp (g * R) - 1) * J :=
          mul_le_mul_of_nonneg_left (hrow z) hexpR
      _ ≤ γ / 2 := by linarith
  have hS' : ∀ y, ∑ z, E z y ≤ γ / 2 := by
    intro y
    simp only [hE, ← Finset.mul_sum]
    calc (Real.exp (g * R) - 1) * ∑ z, ‖blockOf B z y‖ ≤ (Real.exp (g * R) - 1) * J :=
          mul_le_mul_of_nonneg_left (hcol y) hexpR
      _ ≤ γ / 2 := by linarith
  have hconjc : IsCoercive (conjMat a B) (γ / 2) := by
    intro v
    have h1 := hcoer v
    have h2 := reQuad_ge_of_block_bound Dm E hDblk hS hS' v
    have : conjMat a B = B + Dm := by rw [hDm]; abel
    rw [this, reQuad_add]
    linarith
  have hcxc : IsCoercive (conjMat a Bx) (γ / 2 + x) := by
    have : conjMat a Bx = conjMat a B + (x : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) := by
      rw [hBx, conjMat_add, conjMat_smul_one]
    rw [this]; exact hconjc.add_smul_one x
  have hγ' : 0 < γ / 2 + x := by linarith
  have hG : Bx * Bx⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU)
  set Gc := conjMat a Bx⁻¹ with hGc
  have hprod : conjMat a Bx * Gc = 1 := by rw [hGc, ← conjMat_mul, hG, conjMat_one]
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun f => ?_
  set F : ι × Fin N → ℂ := fun p => if p.1 = w0 then f p.2 else 0 with hF
  set v := Gc *ᵥ F with hv
  have hBv : conjMat a Bx *ᵥ v = F := by
    rw [hv, Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec]
  have hNF : sqNorm F = sqNorm f := by
    unfold sqNorm
    rw [Fintype.sum_prod_type, Finset.sum_eq_single w0]
    · simp [hF]
    · intro y _ hy; simp [hF, hy]
    · simp
  have hq := hcxc v
  have hre : reQuad (conjMat a Bx) v ≤ Real.sqrt (sqNorm v) * Real.sqrt (sqNorm F) := by
    rw [reQuad_eq_dot, hBv]
    exact (Complex.re_le_norm _).trans (norm_star_dot_le v F)
  have hsq : (γ / 2 + x) ^ 2 * sqNorm v ≤ sqNorm F := by
    have hNv := sqNorm_nonneg v
    have hNF0 := sqNorm_nonneg F
    rcases hNv.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hNF0
    · set s := Real.sqrt (sqNorm v) with hs
      set t := Real.sqrt (sqNorm F) with ht
      have hs2 : s ^ 2 = sqNorm v := Real.sq_sqrt hNv
      have ht2 : t ^ 2 = sqNorm F := Real.sq_sqrt hNF0
      have hspos : 0 < s := Real.sqrt_pos.2 hpos
      have h1 : (γ / 2 + x) * s ^ 2 ≤ s * t := by
        rw [hs2]; exact hq.trans hre
      have h2 : (γ / 2 + x) * s ≤ t := by
        by_contra hc
        push Not at hc
        nlinarith
      have h3 : ((γ / 2 + x) * s) ^ 2 ≤ t ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
      rw [← hs2, ← ht2]; nlinarith
  -- the slice of `v` at `z`
  have hslice : ∀ i, v (z, i) = ((Real.exp (g * δ z w0) : ℝ) : ℂ) *
      (blockOf Bx⁻¹ z w0 *ᵥ f) i := by
    intro i
    simp only [hv, hGc, Matrix.mulVec, dotProduct, conjMat, Matrix.of_apply, hF, blockOf]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single w0]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha, hδ0, mul_zero, sub_zero, ite_true]
      ring
    · intro y _ hy
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hy]
    · simp
  have hsl : sqNorm (slice v z) =
      Real.exp (g * δ z w0) ^ 2 * sqNorm (blockOf Bx⁻¹ z w0 *ᵥ f) := by
    unfold sqNorm slice
    simp only [hslice, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, Finset.mul_sum]
  have hle : sqNorm (slice v z) ≤ sqNorm v := by
    rw [sqNorm_eq_sum_slice v]
    exact Finset.single_le_sum (f := fun z => sqNorm (slice v z)) (fun _ _ => sqNorm_nonneg _)
      (Finset.mem_univ z)
  set Y := sqNorm (blockOf Bx⁻¹ z w0 *ᵥ f) with hY
  set E := Real.exp (g * δ z w0) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hexp : Real.exp (-g * δ z w0) = E⁻¹ := by
    rw [hEdef, ← Real.exp_neg]; congr 1; ring
  rw [hexp]
  have key : (γ / 2 + x) ^ 2 * (E ^ 2 * Y) ≤ sqNorm f := by
    calc (γ / 2 + x) ^ 2 * (E ^ 2 * Y) ≤ (γ / 2 + x) ^ 2 * sqNorm v := by
          rw [← hsl]; exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ sqNorm F := hsq
      _ = sqNorm f := hNF
  have hden : 0 < ((γ / 2 + x) * E) ^ 2 := by positivity
  calc Y = ((γ / 2 + x) ^ 2 * (E ^ 2 * Y)) / ((γ / 2 + x) * E) ^ 2 := by field_simp
    _ ≤ sqNorm f / ((γ / 2 + x) * E) ^ 2 := by gcongr
    _ = ((γ / 2 + x)⁻¹ * E⁻¹) ^ 2 * sqNorm f := by field_simp

open MeasureTheory Set in
/-- **Decay of the Stieltjes inverse square root** (BASE-KERNEL-3 (1.7), second estimate):
`‖(B^{-1/2})(z,w)‖_op ≤ (γ/2)^{-1/2} e^{-g δ(z,w)}`. -/
theorem sqrtMat_block_decay [Nonempty (ι × Fin N)] (hδ0 : ∀ z, δ z z = 0)
    (hδs : ∀ z w, δ z w = δ w z) (hδt : ∀ z y w, δ z w ≤ δ z y + δ y w)
    {B : Matrix (ι × Fin N) (ι × Fin N) ℂ} {γ J R g : ℝ} (hγ : 0 < γ) (hcoer : IsCoercive B γ)
    (hR : ∀ z y, blockOf B z y ≠ 0 → δ z y ≤ R) (hR0 : 0 ≤ R)
    (hrow : ∀ z, ∑ y, ‖blockOf B z y‖ ≤ J) (hcol : ∀ y, ∑ z, ‖blockOf B z y‖ ≤ J)
    (hg : 0 ≤ g) (hJ : J * (Real.exp (g * R) - 1) ≤ γ / 2) (z w : ι) :
    ‖blockOf (Balaban.Localization.sqrtMat B) z w‖ ≤
      (Real.sqrt (γ / 2))⁻¹ * Real.exp (-g * δ z w) := by
  have hdec := fun x (hx : 0 ≤ x) =>
    resolvent_block_decay δ hδ0 hδs hδt hγ hcoer hx hR hR0 hrow hcol hg hJ
  have hA : Balaban.Localization.ResOK B := fun x hx => by
    have := (hdec x hx).1
    rwa [add_comm] at this
  have hκ : 0 < γ / 2 := by positivity
  set E := Real.exp (-g * δ z w) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  -- the scalar bound for every pair of test vectors
  have hbound : ∀ a b : Fin N → ℂ, ‖star a ⬝ᵥ (blockOf (Balaban.Localization.sqrtMat B) z w *ᵥ b)‖ ≤
      (Real.sqrt (γ / 2))⁻¹ * E * (Real.sqrt (sqNorm a) * Real.sqrt (sqNorm b)) := by
    intro a b
    set Rx : ℝ → Matrix (ι × Fin N) (ι × Fin N) ℂ :=
      fun y => ((y : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) + B)⁻¹ with hRx
    set φ : ℝ → ℂ := fun y => ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      (star a ⬝ᵥ (blockOf (Rx y) z w *ᵥ b)) with hφ
    have hint : ∀ i j, Integrable (fun y : ℝ => ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Rx y (z, i) (w, j))
        (volume.restrict (Ioi (0 : ℝ))) :=
      fun i j => Balaban.Localization.integrable_sqrt_entry hA (z, i) (w, j)
    have hφ_eq : ∀ y, φ y = ∑ i, ∑ j, (star (a i) * b j) *
        (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Rx y (z, i) (w, j)) := by
      intro y
      simp only [hφ, dotProduct, Matrix.mulVec, blockOf, Matrix.of_apply, Pi.star_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hφint : Integrable φ (volume.restrict (Ioi (0 : ℝ))) := by
      have : φ = fun y => ∑ i, ∑ j, (star (a i) * b j) *
          (((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Rx y (z, i) (w, j)) := funext hφ_eq
      rw [this]
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hint i j).const_mul _
    have hS : star a ⬝ᵥ (blockOf (Balaban.Localization.sqrtMat B) z w *ᵥ b) =
        ((1 / Real.pi : ℝ) : ℂ) * ∫ y in Ioi (0 : ℝ), φ y := by
      have h1 : ∫ y in Ioi (0 : ℝ), φ y = ∑ i, ∑ j, (star (a i) * b j) *
          ∫ y in Ioi (0 : ℝ), ((y ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Rx y (z, i) (w, j) := by
        simp_rw [hφ_eq]
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hint i j).const_mul _]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
      rw [h1]
      simp only [dotProduct, Matrix.mulVec, blockOf, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Balaban.Localization.sqrtMat, Balaban.Localization.intMat, Matrix.smul_apply,
        smul_eq_mul]
      ring
    have hg_int : Integrable (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (γ / 2 + y)⁻¹)
        (volume.restrict (Ioi (0 : ℝ))) := Balaban.Localization.integrableOn_rpow_inv_add hκ
    have hnorm : ‖∫ y in Ioi (0 : ℝ), φ y‖ ≤ ∫ y in Ioi (0 : ℝ),
        (E * (Real.sqrt (sqNorm a) * Real.sqrt (sqNorm b))) *
          (y ^ (-(1 / 2 : ℝ)) * (γ / 2 + y)⁻¹) := by
      refine norm_integral_le_of_norm_le (hg_int.const_mul _) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
      have hy0 : 0 < y := hy
      have h3 : 0 < y ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hy0 _
      have hb := (hdec y hy0.le).2 z w
      have hcomm : B + (y : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) =
          (y : ℂ) • (1 : Matrix (ι × Fin N) (ι × Fin N) ℂ) + B := add_comm _ _
      rw [hcomm] at hb
      simp only [hφ, norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      have h4 := norm_star_dot_block_le (blockOf (Rx y) z w) a b
      calc y ^ (-(1 / 2 : ℝ)) * ‖star a ⬝ᵥ (blockOf (Rx y) z w *ᵥ b)‖
          ≤ y ^ (-(1 / 2 : ℝ)) * (Real.sqrt (sqNorm a) *
              (‖blockOf (Rx y) z w‖ * Real.sqrt (sqNorm b))) :=
            mul_le_mul_of_nonneg_left h4 h3.le
        _ ≤ y ^ (-(1 / 2 : ℝ)) * (Real.sqrt (sqNorm a) *
              (((γ / 2 + y)⁻¹ * E) * Real.sqrt (sqNorm b))) := by
            gcongr
        _ = _ := by ring
    rw [hS, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [integral_const_mul, Balaban.Localization.integral_rpow_inv_add hκ] at hnorm
    have hsqrt : 0 < Real.sqrt (γ / 2) := Real.sqrt_pos.2 hκ
    calc 1 / Real.pi * ‖∫ y in Ioi (0 : ℝ), φ y‖
        ≤ 1 / Real.pi * ((E * (Real.sqrt (sqNorm a) * Real.sqrt (sqNorm b))) *
            (Real.pi / Real.sqrt (γ / 2))) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = _ := by field_simp
  refine l2_opNorm_le_of_sqNorm _ (by positivity) fun b => ?_
  set M := blockOf (Balaban.Localization.sqrtMat B) z w with hM
  set K := (Real.sqrt (γ / 2))⁻¹ * E with hK
  have hK0 : 0 ≤ K := by positivity
  set c := M *ᵥ b with hc
  have h1 := hbound c b
  have h2 : ‖star c ⬝ᵥ c‖ = sqNorm c := by
    have : star c ⬝ᵥ c = ((sqNorm c : ℝ) : ℂ) := by
      simp only [dotProduct, sqNorm, Pi.star_apply, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (sqNorm_nonneg _)]
  rw [hc] at h1
  rw [h2] at h1
  have hc0 := sqNorm_nonneg c
  have hb0 := sqNorm_nonneg b
  set sc := Real.sqrt (sqNorm c)
  set sb := Real.sqrt (sqNorm b)
  have hsc2 : sc ^ 2 = sqNorm c := Real.sq_sqrt hc0
  have hsb2 : sb ^ 2 = sqNorm b := Real.sq_sqrt hb0
  have hsc0 : 0 ≤ sc := Real.sqrt_nonneg _
  have hsb0 : 0 ≤ sb := Real.sqrt_nonneg _
  have h3 : sc ^ 2 ≤ K * (sc * sb) := by rw [hsc2]; exact h1
  have h4 : sc ≤ K * sb := by
    rcases hsc0.eq_or_lt with h | h
    · rw [← h]; positivity
    · nlinarith
  rw [← hsc2, ← hsb2]
  nlinarith

end Blocks
