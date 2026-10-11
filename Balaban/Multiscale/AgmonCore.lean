/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PathMetricBounds
public import Balaban.Multiscale.Coercivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The conjugated real form (GREEN.md §4.2, Proposition 4.5, steps (2) and (3))

Real core of the Agmon estimate.  For a positive weight `w` on the fine torus and a real field `φ`
supported in `Ω₁` we compare the form `∑ w² φ (A φ)` of `A = -Δ + ν + Q* a Q` with the form
`vᵀ A v` of `v = w φ`.  The Laplacian and block terms differ by errors that are quadratic in the
logarithmic oscillation of `w`:

* Laplacian (`Balaban.Multiscale.lap_error_le`): `∑_b (w_b - w_a)² φ_a φ_b ≤ 4 d ε² ‖ℓ⁻¹ v‖²`;
* blocks (`Balaban.Multiscale.avg_diff_ge`): the block terms differ by at most
  `(e^{2εd} - 1)² ‖ℓ⁻¹ v‖²`.

Both follow from the pair identity `w_a² φ_a φ_b + w_b² φ_a φ_b - 2 w_a w_b φ_a φ_b =
(w_a - w_b)² φ_a φ_b` (a symmetrization), so no first-order error term occurs.  The weight is
`w = exp (ε r)` for a function `r` which is `1/ℓ(b)`-Lipschitz along bonds of `Ω₁` and has
oscillation `≤ 2 d` on the blocks of its layer (`Balaban.Multiscale.GeneratingSet.IsAgmonWeight`).

Main result: `Balaban.Multiscale.weighted_core`.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

section Bilinear

variable {d ℓ : ℕ} [NeZero ℓ]

/-- Bilinear form of `-Δ + ν`: `gᵀ (-Δ + ν) φ = ∑_b ∂g ∂φ + ν ∑ g φ`. -/
theorem latticeLaplacian_bilinear (ν : ℝ) (g φ : Torus d ℓ → ℝ) :
    g ⬝ᵥ latticeLaplacian d ℓ ν *ᵥ φ =
      ∑ x, ∑ μ : Fin d, (g (x + Pi.single μ 1) - g x) * (φ (x + Pi.single μ 1) - φ x) +
        ν * ∑ x, g x * φ x := by
  have hs : ∀ μ : Fin d, ∑ x, g (x + Pi.single μ 1) * φ (x + Pi.single μ 1) = ∑ x, g x * φ x :=
    fun μ => sum_shift (Pi.single μ 1) (fun x => g x * φ x)
  have hm : ∀ μ : Fin d, ∑ x, g x * φ (x - Pi.single μ 1) =
      ∑ x, g (x + Pi.single μ 1) * φ x := by
    intro μ
    refine (sum_shift (Pi.single μ 1) (fun x => g x * φ (x - Pi.single μ 1))).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  have hsh : ∀ μ : Fin d, ∑ x, g (x + Pi.single μ 1) * φ x =
      ∑ x, g x * φ (x - Pi.single μ 1) := fun μ => (hm μ).symm
  simp only [dotProduct, latticeLaplacian_mulVec]
  have hμ : ∀ μ : Fin d, ∑ x, g x * (2 * φ x - φ (x + Pi.single μ 1) - φ (x - Pi.single μ 1)) =
      ∑ x, (g (x + Pi.single μ 1) - g x) * (φ (x + Pi.single μ 1) - φ x) := by
    intro μ
    have e1 : ∑ x, g x * (2 * φ x - φ (x + Pi.single μ 1) - φ (x - Pi.single μ 1)) =
        2 * (∑ x, g x * φ x) - (∑ x, g x * φ (x + Pi.single μ 1)) -
          (∑ x, g x * φ (x - Pi.single μ 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    have e2 : ∑ x : Torus d ℓ, (g (x + Pi.single μ 1) - g x) * (φ (x + Pi.single μ 1) - φ x) =
        (∑ x : Torus d ℓ, g (x + Pi.single μ 1) * φ (x + Pi.single μ 1)) +
          (∑ x : Torus d ℓ, g x * φ x) -
          (∑ x : Torus d ℓ, g (x + Pi.single μ 1) * φ x) -
          (∑ x : Torus d ℓ, g x * φ (x + Pi.single μ 1)) := by
      have hx : ∀ x : Torus d ℓ, (g (x + Pi.single μ 1) - g x) * (φ (x + Pi.single μ 1) - φ x) =
          g (x + Pi.single μ 1) * φ (x + Pi.single μ 1) + g x * φ x -
            g (x + Pi.single μ 1) * φ x - g x * φ (x + Pi.single μ 1) := fun x => by ring
      simp only [hx, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [e1, e2, hs, hsh]
    ring
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun μ _ => hμ μ, Finset.sum_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => by ring

end Bilinear

section Exp

/-- `e^s - 1 ≤ 2 s` for `0 ≤ s ≤ 1/2`. -/
theorem exp_sub_one_le_two_mul {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) : Real.exp s - 1 ≤ 2 * s := by
  have h := Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  have hs : 0 < 1 - s := by linarith
  have : 1 / (1 - s) ≤ 1 + 2 * s := by
    rw [div_le_iff₀ hs]; nlinarith
  linarith

/-- `(e^t - 1)²`-type bound for the oscillation of an exponential weight:
`(e^{ε r} - e^{ε r'})² ≤ (e^{ε c} - 1)² e^{2 ε r}` when `|r - r'| ≤ c`. -/
theorem exp_sq_sub_le {ε c r r' : ℝ} (hε : 0 ≤ ε) (h : |r - r'| ≤ c) :
    (Real.exp (ε * r) - Real.exp (ε * r')) ^ 2 ≤
      (Real.exp (ε * c) - 1) ^ 2 * Real.exp (ε * r) ^ 2 := by
  set t := ε * (r' - r) with ht
  have hc : 0 ≤ c := (abs_nonneg _).trans h
  have habs : |t| ≤ ε * c := by
    rw [ht, abs_mul, abs_of_nonneg hε, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left h hε
  have hr' : Real.exp (ε * r') = Real.exp (ε * r) * Real.exp t := by
    rw [← Real.exp_add]; congr 1; rw [ht]; ring
  have key : (1 - Real.exp t) ^ 2 ≤ (Real.exp (ε * c) - 1) ^ 2 := by
    have hec : 0 ≤ Real.exp (ε * c) - 1 := by
      have := Real.add_one_le_exp (ε * c); nlinarith [mul_nonneg hε hc]
    apply sq_le_sq'
    · -- `-(e^{εc} - 1) ≤ 1 - e^t`
      have hmono : Real.exp t ≤ Real.exp (ε * c) := Real.exp_le_exp.2 (le_of_abs_le habs)
      linarith
    · -- `1 - e^t ≤ e^{εc} - 1`
      have hmono : Real.exp (-(ε * c)) ≤ Real.exp t := Real.exp_le_exp.2 (by
        have := neg_abs_le t; linarith)
      have h1 := Real.add_one_le_exp (ε * c)
      have h2 := Real.add_one_le_exp (-(ε * c))
      have h3 : Real.exp (ε * c) * Real.exp (-(ε * c)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (ε * c), Real.exp_pos (-(ε * c)), sq_nonneg (Real.exp (ε * c) - 1)]
  rw [hr']
  calc (Real.exp (ε * r) - Real.exp (ε * r) * Real.exp t) ^ 2
      = Real.exp (ε * r) ^ 2 * (1 - Real.exp t) ^ 2 := by ring
    _ ≤ Real.exp (ε * r) ^ 2 * (Real.exp (ε * c) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_left key (sq_nonneg _)
    _ = _ := by ring

end Exp


section Block

variable {ι : Type*} [Fintype ι]

/-- The symmetrization identity behind the block error: for a symmetric kernel `M` with unit row
sums and weights `w` whose oscillation along the support of `M` is `(w x - w x')² ≤ B w x²`,
`ψᵀ-form of w²ψ` against `Mψ` is at least that of `wψ` against `M (wψ)` minus `½ B ‖wψ‖²`. -/
theorem block_diff_ge (M : Matrix ι ι ℝ) (hsym : ∀ x x', M x x' = M x' x)
    (hnn : ∀ x x', 0 ≤ M x x') (hrow : ∀ x, ∑ x', M x x' = 1) (w ψ : ι → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x x', M x x' ≠ 0 → ψ x ≠ 0 → ψ x' ≠ 0 → (w x - w x') ^ 2 ≤ B * w x ^ 2) :
    -(1 / 2 * B * ∑ x, (w x * ψ x) ^ 2) ≤
      (fun x => w x ^ 2 * ψ x) ⬝ᵥ M *ᵥ ψ -
        (fun x => w x * ψ x) ⬝ᵥ M *ᵥ (fun x => w x * ψ x) := by
  classical
  have hD : (fun x => w x ^ 2 * ψ x) ⬝ᵥ M *ᵥ ψ -
        (fun x => w x * ψ x) ⬝ᵥ M *ᵥ (fun x => w x * ψ x) =
      ∑ x, ∑ x', M x x' * ((w x ^ 2 - w x * w x') * (ψ x * ψ x')) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  have hsymm : ∑ x, ∑ x', M x x' * ((w x ^ 2 - w x * w x') * (ψ x * ψ x')) =
      ∑ x, ∑ x', M x x' * ((w x' ^ 2 - w x * w x') * (ψ x * ψ x')) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [hsym x' x]; ring
  have hpair : ∀ x x', -(1 / 2 * B * (M x x' * ((w x * ψ x) ^ 2 + (w x' * ψ x') ^ 2))) ≤
      M x x' * ((w x - w x') ^ 2 * (ψ x * ψ x')) := by
    intro x x'
    by_cases hM : M x x' = 0
    · simp [hM]
    by_cases h1 : ψ x = 0
    · simp only [h1, mul_zero, zero_mul, mul_zero]
      have : 0 ≤ M x x' * ((w x * 0) ^ 2 + (w x' * ψ x') ^ 2) := by
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
        exact mul_nonneg (hnn x x') (sq_nonneg _)
      nlinarith [mul_nonneg hB0 this]
    by_cases h2 : ψ x' = 0
    · simp only [h2, mul_zero]
      have : 0 ≤ M x x' * ((w x * ψ x) ^ 2 + (w x' * 0) ^ 2) := by
        simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
        exact mul_nonneg (hnn x x') (sq_nonneg _)
      nlinarith [mul_nonneg hB0 this]
    have hM' : M x' x ≠ 0 := by rw [← hsym x x']; exact hM
    have hb1 := hB x x' hM h1 h2
    have hb2 := hB x' x hM' h2 h1
    have hb2' : (w x - w x') ^ 2 ≤ B * w x' ^ 2 := by
      have : (w x' - w x) ^ 2 = (w x - w x') ^ 2 := by ring
      rwa [this] at hb2
    have hMnn := hnn x x'
    have hineq : -(1 / 2 * B * ((w x * ψ x) ^ 2 + (w x' * ψ x') ^ 2)) ≤
        (w x - w x') ^ 2 * (ψ x * ψ x') := by
      nlinarith [mul_le_mul_of_nonneg_right hb1 (sq_nonneg (ψ x)),
        mul_le_mul_of_nonneg_right hb2' (sq_nonneg (ψ x')),
        mul_nonneg (sq_nonneg (w x - w x')) (sq_nonneg (ψ x + ψ x'))]
    calc -(1 / 2 * B * (M x x' * ((w x * ψ x) ^ 2 + (w x' * ψ x') ^ 2)))
        = M x x' * (-(1 / 2 * B * ((w x * ψ x) ^ 2 + (w x' * ψ x') ^ 2))) := by ring
      _ ≤ M x x' * ((w x - w x') ^ 2 * (ψ x * ψ x')) := mul_le_mul_of_nonneg_left hineq hMnn
  have hsum : ∑ x, ∑ x', M x x' * ((w x * ψ x) ^ 2 + (w x' * ψ x') ^ 2) =
      2 * ∑ x, (w x * ψ x) ^ 2 := by
    simp only [mul_add, Finset.sum_add_distrib]
    have e1 : ∑ x, ∑ x', M x x' * (w x * ψ x) ^ 2 = ∑ x, (w x * ψ x) ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_mul, hrow x, one_mul]
    have e2 : ∑ x, ∑ x', M x x' * (w x' * ψ x') ^ 2 = ∑ x, (w x * ψ x) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x' _ => ?_
      have : ∑ x, M x x' * (w x' * ψ x') ^ 2 = (∑ x, M x' x) * (w x' * ψ x') ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [hsym x x']
      rw [this, hrow x', one_mul]
    rw [e1, e2]; ring
  have hlow : -(1 / 2 * B * (2 * ∑ x, (w x * ψ x) ^ 2)) ≤
      ∑ x, ∑ x', M x x' * ((w x - w x') ^ 2 * (ψ x * ψ x')) := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun x' _ => hpair x x'
  have hcomb : 2 * ∑ x, ∑ x', M x x' * ((w x ^ 2 - w x * w x') * (ψ x * ψ x')) =
      ∑ x, ∑ x', M x x' * ((w x - w x') ^ 2 * (ψ x * ψ x')) := by
    have : 2 * ∑ x, ∑ x', M x x' * ((w x ^ 2 - w x * w x') * (ψ x * ψ x')) =
        (∑ x, ∑ x', M x x' * ((w x ^ 2 - w x * w x') * (ψ x * ψ x'))) +
          ∑ x, ∑ x', M x x' * ((w x' ^ 2 - w x * w x') * (ψ x * ψ x')) := by
      rw [← hsymm]; ring
    rw [this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x' _ => by ring
  rw [hD]
  linarith

end Block

namespace Multiscale

open Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `ℓ(x)⁻²` is nonnegative. -/
theorem invSqSpacing_nonneg (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    0 ≤ invSqSpacing G x := by
  unfold invSqSpacing
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

/-- `‖ℓ⁻¹ v‖²` for a real field on the torus. -/
noncomputable def wsq (G : GeneratingSet d L N₀ k ϱ) (v : Torus d (N₀ * L ^ k) → ℝ) : ℝ :=
  ∑ x, invSqSpacing G x * v x ^ 2

theorem wsq_nonneg (G : GeneratingSet d L N₀ k ϱ) (v : Torus d (N₀ * L ^ k) → ℝ) :
    0 ≤ wsq G v :=
  Finset.sum_nonneg fun x _ => mul_nonneg (invSqSpacing_nonneg G x) (sq_nonneg _)

/-- `‖ℓ⁻¹ v‖²` as a sum over the layers. -/
theorem wsq_eq_sum_layers (G : GeneratingSet d L N₀ k ϱ) (v : Torus d (N₀ * L ^ k) → ℝ) :
    wsq G v = ∑ j ∈ Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ x, (layerPart G j v x) ^ 2 := by
  unfold wsq invSqSpacing
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x ∈ G.layer j <;> simp [layerPart, h]

/-- Admissible weight exponents `r` (to be exponentiated): `1/ℓ(b)`-Lipschitz along bonds of `Ω₁`
and of oscillation `≤ 2 d` on the `j`-blocks of layer `j`.  An example is the (truncated) path
distance to a point (`Balaban.Multiscale.GeneratingSet.distTo`, GREEN.md Lemma 4.3 (b), (c)). -/
structure IsAgmonWeight (G : GeneratingSet d L N₀ k ϱ) (r : Torus d (N₀ * L ^ k) → ℝ) : Prop where
  bond : ∀ x x', x ∈ G.Ω 1 → x' ∈ G.Ω 1 → Adj x x' → |r x - r x'| ≤ G.bondCost x x'
  block : ∀ j, 1 ≤ j → j ≤ k → ∀ x x', x ∈ G.layer j →
    jBlock d L N₀ k j x' = jBlock d L N₀ k j x → |r x - r x'| ≤ 2 * d

/-- Bilinear form of the layer matrix. -/
theorem layerProjMatrix_bilinear (G : GeneratingSet d L N₀ k ϱ) (j : ℕ)
    (g φ : Torus d (N₀ * L ^ k) → ℝ) :
    g ⬝ᵥ layerProjMatrix G j *ᵥ φ =
      layerPart G j g ⬝ᵥ blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) *ᵥ
        layerPart G j φ := by
  simp only [dotProduct, Matrix.mulVec, layerProjMatrix, layerPart]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ G.layer j
  · simp only [hx, true_and, ite_true]
    congr 1
    refine Finset.sum_congr rfl fun x' _ => ?_
    by_cases hx' : x' ∈ G.layer j <;> simp [hx']
  · simp [hx]

theorem avgMatrix_bilinear (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
    (g φ : Torus d (N₀ * L ^ k) → ℝ) :
    g ⬝ᵥ avgMatrix G a *ᵥ φ =
      ∑ j ∈ Icc 1 k, (a j / ((L : ℝ) ^ j) ^ 2) *
        (layerPart G j g ⬝ᵥ blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) *ᵥ
          layerPart G j φ) := by
  unfold avgMatrix
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, layerProjMatrix_bilinear]

theorem blockProjMatrix_symm (j : ℕ) (x x' : Torus d (N₀ * L ^ k)) :
    blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) x x' =
      blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) x' x := by
  unfold blockProjMatrix
  simp only [eq_comm]

theorem blockProjMatrix_nonneg (j : ℕ) (x x' : Torus d (N₀ * L ^ k)) :
    0 ≤ blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) x x' := by
  unfold blockProjMatrix
  split_ifs
  · positivity
  · exact le_rfl

theorem blockProjMatrix_row {j : ℕ} (hjk : j ≤ k) (x : Torus d (N₀ * L ^ k)) :
    ∑ x', blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)) x x' = 1 := by
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hcard := card_blockFibre (d := d) (N := L ^ j) (m := N₀ * L ^ (k - j)) (side_eq hjk)
    (blockMap (L ^ j) (N₀ * L ^ (k - j)) x)
  unfold blockProjMatrix
  rw [← Finset.sum_filter, Finset.sum_const]
  have : (Finset.univ.filter fun x' : Torus d (N₀ * L ^ k) =>
      blockMap (L ^ j) (N₀ * L ^ (k - j)) x = blockMap (L ^ j) (N₀ * L ^ (k - j)) x') =
      blockFibre (L ^ j) (N₀ * L ^ (k - j)) (blockMap (L ^ j) (N₀ * L ^ (k - j)) x) := by
    ext x'
    simp [blockFibre, eq_comm]
  rw [this, hcard, nsmul_eq_mul]
  have : ((L : ℝ) ^ j) ^ d ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  push_cast
  field_simp


/-! ### The Laplacian error -/

theorem exp_sub_one_sq_le {ε c s : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (hc1 : ε * c ≤ 1 / 2)
    (hcs : c ≤ 1 / s) : (Real.exp (ε * c) - 1) ^ 2 ≤ 4 * ε ^ 2 * (s ^ 2)⁻¹ := by
  have h0 : 0 ≤ Real.exp (ε * c) - 1 := by
    have := Real.add_one_le_exp (ε * c); have := mul_nonneg hε hc; linarith
  have h1 := exp_sub_one_le_two_mul (mul_nonneg hε hc) hc1
  have h2 : (Real.exp (ε * c) - 1) ^ 2 ≤ (2 * (ε * c)) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : c ^ 2 ≤ (1 / s) ^ 2 := pow_le_pow_left₀ hc hcs 2
  calc (Real.exp (ε * c) - 1) ^ 2 ≤ (2 * (ε * c)) ^ 2 := h2
    _ = 4 * ε ^ 2 * c ^ 2 := by ring
    _ ≤ 4 * ε ^ 2 * (1 / s) ^ 2 := by gcongr
    _ = 4 * ε ^ 2 * (s ^ 2)⁻¹ := by rw [one_div, inv_pow]

variable (G : GeneratingSet d L N₀ k ϱ)

theorem bond_term_le {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ k) → ℝ}
    (hφ : ∀ x, x ∉ G.Ω 1 → φ x = 0) (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
        (φ x * φ (x + Pi.single μ 1)) ≤
      2 * ε ^ 2 * (invSqSpacing G x * (Real.exp (ε * r x) * φ x) ^ 2 +
        invSqSpacing G (x + Pi.single μ 1) *
          (Real.exp (ε * r (x + Pi.single μ 1)) * φ (x + Pi.single μ 1)) ^ 2) := by
  set b := x + Pi.single μ 1 with hb
  have hnn : 0 ≤ 2 * ε ^ 2 * (invSqSpacing G x * (Real.exp (ε * r x) * φ x) ^ 2 +
        invSqSpacing G b * (Real.exp (ε * r b) * φ b) ^ 2) := by
    have := invSqSpacing_nonneg G x
    have := invSqSpacing_nonneg G b
    positivity
  by_cases hxm : x ∈ G.Ω 1
  swap
  · calc _ = 0 := by rw [hφ x hxm]; ring
      _ ≤ _ := hnn
  by_cases hbm : b ∈ G.Ω 1
  swap
  · calc _ = 0 := by rw [hφ b hbm]; ring
      _ ≤ _ := hnn
  have hadj : Adj x b := ⟨μ, Or.inl rfl⟩
  have hbc := hr.bond x b hxm hbm hadj
  have hc0 := G.bondCost_nonneg x b
  have hc1 : G.bondCost x b ≤ 1 := G.bondCost_le_one hxm b
  have hεc : ε * G.bondCost x b ≤ 1 / 2 := by nlinarith
  set c := G.bondCost x b with hc
  have hBa := exp_sub_one_sq_le hε0 hc0 hεc (G.bondCost_le_inv_left x b)
  have hBb := exp_sub_one_sq_le hε0 hc0 hεc (G.bondCost_le_inv_right x b)
  rw [← invSqSpacing_eq G hxm] at hBa
  rw [← invSqSpacing_eq G hbm] at hBb
  have h1 := exp_sq_sub_le hε0 hbc
  have h2 := exp_sq_sub_le hε0 (show |r b - r x| ≤ c by rwa [abs_sub_comm])
  set B := (Real.exp (ε * c) - 1) ^ 2 with hB
  set Ex := Real.exp (ε * r x)
  set Eb := Real.exp (ε * r b)
  have h1' : (Eb - Ex) ^ 2 ≤ B * Ex ^ 2 := by
    have : (Eb - Ex) ^ 2 = (Ex - Eb) ^ 2 := by ring
    rwa [this]
  have e1 : (Eb - Ex) ^ 2 * (φ x * φ b) ≤
      1 / 2 * ((Eb - Ex) ^ 2 * φ x ^ 2 + (Eb - Ex) ^ 2 * φ b ^ 2) := by
    nlinarith [mul_nonneg (sq_nonneg (Eb - Ex)) (sq_nonneg (φ x - φ b))]
  have e2 : (Eb - Ex) ^ 2 * φ x ^ 2 ≤ B * (Ex * φ x) ^ 2 := by
    calc (Eb - Ex) ^ 2 * φ x ^ 2 ≤ (B * Ex ^ 2) * φ x ^ 2 :=
          mul_le_mul_of_nonneg_right h1' (sq_nonneg _)
      _ = B * (Ex * φ x) ^ 2 := by ring
  have e3 : (Eb - Ex) ^ 2 * φ b ^ 2 ≤ B * (Eb * φ b) ^ 2 := by
    calc (Eb - Ex) ^ 2 * φ b ^ 2 ≤ (B * Eb ^ 2) * φ b ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = B * (Eb * φ b) ^ 2 := by ring
  have e4 : B * (Ex * φ x) ^ 2 ≤ 4 * ε ^ 2 * invSqSpacing G x * (Ex * φ x) ^ 2 :=
    mul_le_mul_of_nonneg_right hBa (sq_nonneg _)
  have e5 : B * (Eb * φ b) ^ 2 ≤ 4 * ε ^ 2 * invSqSpacing G b * (Eb * φ b) ^ 2 :=
    mul_le_mul_of_nonneg_right hBb (sq_nonneg _)
  nlinarith [e1, e2, e3, e4, e5]

/-- **Laplacian error.** `∑_b (w_b - w_a)² φ_a φ_b ≤ 4 d ε² ‖ℓ⁻¹ (w φ)‖²`. -/
theorem lap_error_le {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ k) → ℝ}
    (hφ : ∀ x, x ∉ G.Ω 1 → φ x = 0) :
    ∑ x, ∑ μ : Fin d, (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
        (φ x * φ (x + Pi.single μ 1)) ≤
      4 * d * ε ^ 2 * wsq G (fun x => Real.exp (ε * r x) * φ x) := by
  set F : Torus d (N₀ * L ^ k) → ℝ := fun x => invSqSpacing G x * (Real.exp (ε * r x) * φ x) ^ 2
    with hF
  have hshift : ∀ μ : Fin d, ∑ x, F (x + Pi.single μ 1) = ∑ x, F x := fun μ =>
    sum_shift (Pi.single μ 1) F
  calc _ ≤ ∑ x, ∑ μ : Fin d, 2 * ε ^ 2 * (F x + F (x + Pi.single μ 1)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => bond_term_le G hr hε0 hε1 hφ x μ
    _ = ∑ μ : Fin d, 2 * ε ^ 2 * (∑ x, F x + ∑ x, F (x + Pi.single μ 1)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        rfl
    _ = 4 * d * ε ^ 2 * wsq G (fun x => Real.exp (ε * r x) * φ x) := by
        simp only [hshift]
        have hw : wsq G (fun x => Real.exp (ε * r x) * φ x) = ∑ x, F x := rfl
        rw [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem lap_diff (r : Torus d (N₀ * L ^ k) → ℝ) (ε ν : ℝ) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ latticeLaplacian d (N₀ * L ^ k) ν *ᵥ φ =
      (fun x => Real.exp (ε * r x) * φ x) ⬝ᵥ latticeLaplacian d (N₀ * L ^ k) ν *ᵥ
          (fun x => Real.exp (ε * r x) * φ x) -
        ∑ x, ∑ μ : Fin d, (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
          (φ x * φ (x + Pi.single μ 1)) := by
  rw [latticeLaplacian_bilinear, latticeLaplacian_bilinear]
  have h1 : ∑ x, Real.exp (ε * r x) ^ 2 * φ x * φ x =
      ∑ x, Real.exp (ε * r x) * φ x * (Real.exp (ε * r x) * φ x) :=
    Finset.sum_congr rfl fun x _ => by ring
  have h2 : ∀ x : Torus d (N₀ * L ^ k),
      ∑ μ : Fin d, (Real.exp (ε * r (x + Pi.single μ 1)) ^ 2 * φ (x + Pi.single μ 1) -
          Real.exp (ε * r x) ^ 2 * φ x) * (φ (x + Pi.single μ 1) - φ x) =
        ∑ μ : Fin d, ((Real.exp (ε * r (x + Pi.single μ 1)) * φ (x + Pi.single μ 1) -
          Real.exp (ε * r x) * φ x) * (Real.exp (ε * r (x + Pi.single μ 1)) *
            φ (x + Pi.single μ 1) - Real.exp (ε * r x) * φ x) -
          (Real.exp (ε * r (x + Pi.single μ 1)) - Real.exp (ε * r x)) ^ 2 *
            (φ x * φ (x + Pi.single μ 1))) :=
    fun x => Finset.sum_congr rfl fun μ _ => by ring
  simp only [h2, Finset.sum_sub_distrib]
  rw [h1]
  ring

/-! ### The block error -/

theorem avg_diff_ge {a : ℕ → ℝ} (ha : IsAdmissibleWeights k a) {r : Torus d (N₀ * L ^ k) → ℝ}
    (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    -((Real.exp (ε * (2 * d)) - 1) ^ 2 * wsq G (fun x => Real.exp (ε * r x) * φ x)) ≤
      (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ avgMatrix G a *ᵥ φ -
        (fun x => Real.exp (ε * r x) * φ x) ⬝ᵥ avgMatrix G a *ᵥ
          (fun x => Real.exp (ε * r x) * φ x) := by
  set w : Torus d (N₀ * L ^ k) → ℝ := fun x => Real.exp (ε * r x) with hw
  set B := (Real.exp (ε * (2 * d)) - 1) ^ 2 with hB
  have hB0 : 0 ≤ B := sq_nonneg _
  rw [avgMatrix_bilinear, avgMatrix_bilinear, ← Finset.sum_sub_distrib, wsq_eq_sum_layers,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj1 := (Finset.mem_Icc.1 hj).1
  have hjk := (Finset.mem_Icc.1 hj).2
  have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hlg : layerPart G j (fun x => w x ^ 2 * φ x) = fun x => w x ^ 2 * layerPart G j φ x := by
    funext x; by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  have hlv : layerPart G j (fun x => w x * φ x) = fun x => w x * layerPart G j φ x := by
    funext x; by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  rw [hlg, hlv]
  beta_reduce
  have hblock := block_diff_ge (blockProjMatrix d (N₀ * L ^ k) (L ^ j) (N₀ * L ^ (k - j)))
    (blockProjMatrix_symm j) (blockProjMatrix_nonneg j) (blockProjMatrix_row hjk) w
    (layerPart G j φ) hB0 (by
      intro x x' hM hψ _
      have hbm : blockMap (L ^ j) (N₀ * L ^ (k - j)) x = blockMap (L ^ j) (N₀ * L ^ (k - j)) x' := by
        by_contra hne
        exact hM (by simp [blockProjMatrix, hne])
      have hx : x ∈ G.layer j := by
        by_contra hne; exact hψ (by simp [layerPart, hne])
      exact exp_sq_sub_le hε0 (hr.block j hj1 hjk x x' hx hbm.symm))
  have hsq : 0 ≤ ∑ x, (w x * layerPart G j φ x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha2 := (ha j hj1 hjk).2
  have ha1 := (ha j hj1 hjk).1
  rw [← mul_sub]
  have hcoef : 0 ≤ a j / ((L : ℝ) ^ j) ^ 2 := div_nonneg (by linarith) hLj.le
  have hstep := hblock
  have hS0 := mul_nonneg hB0 hsq
  calc -(B * ((((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ x, (w x * layerPart G j φ x) ^ 2))
      ≤ (a j / ((L : ℝ) ^ j) ^ 2) *
          (-(1 / 2 * B * ∑ x, (w x * layerPart G j φ x) ^ 2)) := by
        have : a j / ((L : ℝ) ^ j) ^ 2 * (1 / 2) ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ := by
          rw [div_eq_mul_inv]
          nlinarith [inv_pos.2 hLj]
        nlinarith [mul_le_mul_of_nonneg_right this hS0]
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep hcoef

/-! ### The conjugated form -/

/-- **The conjugated real form** (GREEN.md Prop. 4.5, steps (2), (3)).  For `w = exp (ε r)` and a
real field `φ` supported in `Ω₁`, with `v = w φ` and `κ = 4 d ε² + (e^{2εd} - 1)²`,
`½ E(v) + (c - κ) ‖ℓ⁻¹ v‖² ≤ ∑ w² φ (A φ)`, where `c = poincareConst d` and
`A = -Δ + ν + Q* a Q`. -/
theorem weighted_core (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    {r : Torus d (N₀ * L ^ k) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) {φ : Torus d (N₀ * L ^ k) → ℝ} (hφ : ∀ x, x ∉ G.Ω 1 → φ x = 0) :
    (1 / 2) * latticeEnergy (fun x => Real.exp (ε * r x) * φ x) +
        (poincareConst d - (4 * d * ε ^ 2 + (Real.exp (ε * (2 * d)) - 1) ^ 2)) *
          wsq G (fun x => Real.exp (ε * r x) * φ x) ≤
      (fun x => Real.exp (ε * r x) ^ 2 * φ x) ⬝ᵥ fullMatrix G a ν *ᵥ φ := by
  set v : Torus d (N₀ * L ^ k) → ℝ := fun x => Real.exp (ε * r x) * φ x with hv
  have hcore := core_real G hd hν ha v
  have hlap := lap_diff r ε ν φ
  have hlapE := lap_error_le G hr hε0 hε1 hφ
  have havg := avg_diff_ge G ha hr hε0 φ
  have hwsq : ∑ x, invSqSpacing G x * v x ^ 2 = wsq G v := rfl
  rw [hwsq] at hcore
  have hsplit : ∀ ψ : Torus d (N₀ * L ^ k) → ℝ, ∀ g : Torus d (N₀ * L ^ k) → ℝ,
      g ⬝ᵥ fullMatrix G a ν *ᵥ ψ =
        g ⬝ᵥ latticeLaplacian d (N₀ * L ^ k) ν *ᵥ ψ + g ⬝ᵥ avgMatrix G a *ᵥ ψ := by
    intro ψ g
    unfold fullMatrix
    rw [Matrix.add_mulVec, dotProduct_add]
  rw [hsplit] at hcore ⊢
  rw [hlap]
  nlinarith [hcore, hlapE, havg]

end Multiscale

end Balaban
