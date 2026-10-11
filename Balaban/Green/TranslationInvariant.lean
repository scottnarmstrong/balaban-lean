/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BlockNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# G-5(a), fine-to-block part: translation-invariant one-scale operators

On the torus `Torus d (N₀ * L ^ k)` (blocks of side `N = L ^ k`, `N₀` blocks per side; any
volume) let `H = fineHamiltonian d ℓ N N₀ ν a = N² (-Δ_unit) + ν + a Q* Q` be the unit-lattice
operator of GREEN.md (`ν` the mass in unit-lattice units) and `G = H⁻¹`.

* `Balaban.Green.oneScale_blockDecay`: for `F` supported in the block `y'`,
  `‖G F‖_{y} ≤ C₀ e^{-δ₀ dist(y, y')} ‖F‖_{y'}` (`blockL2`; `y, y'` coarse sites);
* `Balaban.Green.fineToBlockKernel ν a = a G Q*` (a matrix indexed by fine × coarse sites), and
  `Balaban.Green.fineToBlockKernel_decay`: its column `y'` has block norm on the block of `y`
  at most `a C₀ e^{-δ₀ dist(y, y')}`.  This is G-5(a)'s `|a_j G_j Q_j^*(x, y)| ≤ c e^{-δ|x-y|}` in
  the norm `blockL2` in `x` (the pointwise bound needs G-2(ii)); the constants depend on
  `d, L` only;
* `Balaban.Green.blockGreenKernel_decay`: the coarse matrix elements `Q G Q*(y, y')` satisfy
  `|Q G Q*(y, y')| ≤ C₀ e^{-δ₀ dist(y, y')}`, hence the entries of
  `Δ_tr = a - a² Q G Q*` decay (`unconstrainedUnitOperator_decay`).

All bounds hold for every `ν ≥ 0` and `a ∈ [1/2, 2]`, `k ≥ 1`, `N₀ ≥ 1`.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-! ### The inverse of the unit-lattice operator -/

section Inverse

variable {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem blockHamiltonian_mul_inv (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) :
    blockHamiltonian d ℓ N m ν a * (blockHamiltonian d ℓ N m ν a)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
    (blockHamiltonian_posDef hℓ hN hd hν ha).isUnit)

theorem fineHamiltonian_inv (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha : 0 < a) :
    (fineHamiltonian d ℓ N m ν a)⁻¹ =
      ((N : ℝ) ^ 2)⁻¹ • (blockHamiltonian d ℓ N m (ν / (N : ℝ) ^ 2) (a / (N : ℝ) ^ 2))⁻¹ := by
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hdet : IsUnit (blockHamiltonian d ℓ N m (ν / (N : ℝ) ^ 2) (a / (N : ℝ) ^ 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1
      (blockHamiltonian_posDef hℓ hN hd (by positivity) (by positivity)).isUnit
  rw [fineHamiltonian_eq hN]
  have : Invertible ((N : ℝ) ^ 2) := invertibleOfNonzero hc
  rw [Matrix.inv_smul (k := (N : ℝ) ^ 2) (h := hdet), invOf_eq_inv]

end Inverse

/-! ### Block decay for the unit-lattice Green's function -/

/-- **Single-scale block decay (G-2(i), single layer).**  For `F` supported in the block `y'`,
`‖H⁻¹ F‖_y ≤ C₀ e^{-δ₀ dist(y, y')} ‖F‖_{y'}`. -/
theorem oneScale_blockDecay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (F : Torus d (N₀ * L ^ k) → ℝ) {y' : Torus d N₀}
    (hF : ∀ x, F x ≠ 0 → blockMap (L ^ k) N₀ x = y') (y : Torus d N₀) :
    blockL2 (L ^ k) N₀ y ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F) ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        blockL2 (L ^ k) N₀ y' F := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have ha0 : 0 < a := by linarith
  have hc : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by push_cast; rfl
  set c : ℝ := ((L : ℝ) ^ k) ^ 2 with hcdef
  set B := blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ (ν / c) (a / c) with hB
  set v := (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F with hv
  have hinv := fineHamiltonian_inv hℓ hN hd hν ha0
  rw [hcast] at hinv
  have hBv : B *ᵥ v = fun x => c⁻¹ * F x := by
    rw [hv, hinv, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      blockHamiltonian_mul_inv hℓ hN hd (by positivity) (by positivity), Matrix.one_mulVec]
 
    funext x; simp [hcdef]
  have hF' : ∀ x, c⁻¹ * F x ≠ 0 → blockMap (L ^ k) N₀ x = y' := by
    intro x hx
    exact hF x (fun h0 => hx (by rw [h0, mul_zero]))
  have core := oneScale_core hd hk hν ha1 ha2 (w := v) (F := fun x => c⁻¹ * F x) hBv hF' (y := y)
  -- normalise
  have hsq : Real.sqrt (∑ x, (c⁻¹ * F x) ^ 2) = c⁻¹ * Real.sqrt (∑ x, F x ^ 2) := by
    have : ∑ x, (c⁻¹ * F x) ^ 2 = (c⁻¹) ^ 2 * ∑ x, F x ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hc.le)]
  rw [hsq, ← hcdef] at core
  have hsupp : ∑ x, F x ^ 2 = ∑ x ∈ blockFibre (L ^ k) N₀ y', F x ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    by_contra hne
    exact hx (mem_blockFibre.2 (hF x (fun h0 => hne (by rw [h0]; norm_num))))
  have h1 : Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, v x ^ 2) ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        Real.sqrt (∑ x, F x ^ 2) := by
    refine core.trans (le_of_eq ?_)
    field_simp
  unfold blockL2
  have hs0 : 0 ≤ ((((L ^ k : ℕ) : ℝ)) ^ d)⁻¹ := by positivity
  rw [Real.sqrt_mul hs0, Real.sqrt_mul hs0, ← hsupp]
  calc Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, v x ^ 2)
      ≤ Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * (blockDecayConst d L *
          Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) * Real.sqrt (∑ x, F x ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = _ := by ring

/-! ### Kernels -/

section Kernels

variable {ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The indicator of the block `y'` as a field on the fine torus (`Q* δ_{y'}`). -/
def blockIndicator (N m : ℕ) (y' : Torus d m) : Torus d ℓ → ℝ :=
  fun x => if blockMap N m x = y' then 1 else 0

/-- The fine-to-block kernel `a G Q*` of G-5(a): `(x, y') ↦ a (G Q*)(x, y')` for a fine site `x`
and a coarse site `y'`, where `G = H⁻¹`, `H = fineHamiltonian d ℓ N m ν a`. -/
noncomputable def fineToBlockKernel (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] (ν a : ℝ) :
    Matrix (Torus d ℓ) (Torus d m) ℝ :=
  a • ((fineHamiltonian d ℓ N m ν a)⁻¹ * blockPullbackMatrix d ℓ N m)

/-- The coarse block-to-block kernel `Q G Q*`. -/
noncomputable def blockGreenKernel (d ℓ N m : ℕ) [NeZero ℓ] [NeZero m] (ν a : ℝ) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  unitBlockAverageMatrix d ℓ N m * (fineHamiltonian d ℓ N m ν a)⁻¹ *
    blockPullbackMatrix d ℓ N m

theorem mul_blockPullbackMatrix_apply (M : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) (x : Torus d ℓ)
    (y' : Torus d m) : (M * blockPullbackMatrix d ℓ N m) x y' = (M *ᵥ blockIndicator N m y') x := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, blockPullbackMatrix, blockIndicator]

theorem blockL2_blockIndicator (hℓ : ℓ = N * m) (hN : 0 < N) (y' : Torus d m) :
    blockL2 N m y' (blockIndicator (ℓ := ℓ) N m y') = 1 := by
  unfold blockL2
  have : ∑ x ∈ blockFibre N m y', (blockIndicator (ℓ := ℓ) N m y' x) ^ 2 = (N : ℝ) ^ d := by
    have h1 : ∀ x ∈ blockFibre N m y', (blockIndicator (ℓ := ℓ) N m y' x) ^ 2 = 1 := by
      intro x hx
      simp [blockIndicator, mem_blockFibre.1 hx]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, card_blockFibre hℓ]
    simp
  rw [this, inv_mul_cancel₀ (by positivity), Real.sqrt_one]

omit [NeZero ℓ] [NeZero m] in
theorem blockIndicator_support (y' : Torus d m) (x : Torus d ℓ)
    (hx : blockIndicator (ℓ := ℓ) N m y' x ≠ 0) : blockMap N m x = y' := by
  by_contra h
  exact hx (by simp [blockIndicator, h])

theorem torusDist_self_eq_zero (y : Torus d m) : torusDist d m y y = 0 := by
  have := dist_self (show L1Torus d m from y)
  exact this

/-- **G-5(a), fine-to-block part.**  The column `y'` of the kernel `a G Q*` has, on the block of
`y`, `L²`-norm at most `a C₀ e^{-δ₀ dist(y, y')}` (unit-lattice measure and distance;
constants depend on `d, L` only; uniform in `k ≥ 1`, `N₀`, `ν ≥ 0`, `a ∈ [1/2, 2]`). -/
theorem fineToBlockKernel_decay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    blockL2 (L ^ k) N₀ y (fun x => fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a x y') ≤
      a * blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have h := oneScale_blockDecay (L := L) (N₀ := N₀) (k := k) hd hk hν ha1 ha2
    (blockIndicator (L ^ k) N₀ y') (fun x hx => blockIndicator_support y' x hx) y
  rw [blockL2_blockIndicator hℓ hN] at h
  have e : (fun x => fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a x y') =
      fun x => a * ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ
        blockIndicator (L ^ k) N₀ y') x := by
    funext x
    simp only [fineToBlockKernel, Matrix.smul_apply, smul_eq_mul]
    rw [mul_blockPullbackMatrix_apply]
  rw [e, blockL2_smul, abs_of_pos (by linarith : 0 < a)]
  calc a * _ ≤ a * (blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        1) := mul_le_mul_of_nonneg_left h (by linarith)
    _ = _ := by ring

theorem blockGreenKernel_apply (y y' : Torus d m) (ν a : ℝ) :
    blockGreenKernel d ℓ N m ν a y y' =
      ((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m y,
        ((fineHamiltonian d ℓ N m ν a)⁻¹ * blockPullbackMatrix d ℓ N m) x y' := by
  unfold blockGreenKernel
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [unitBlockAverageMatrix, ite_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 2

/-- **G-5(a), block-to-block matrix elements.**  `|Q G Q*(y, y')| ≤ C₀ e^{-δ₀ dist(y, y')}`. -/
theorem blockGreenKernel_decay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    |blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a y y'| ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have h := oneScale_blockDecay (L := L) (N₀ := N₀) (k := k) hd hk hν ha1 ha2
    (blockIndicator (L ^ k) N₀ y') (fun x hx => blockIndicator_support y' x hx) y
  rw [blockL2_blockIndicator hℓ hN, mul_one] at h
  rw [blockGreenKernel_apply]
  refine (abs_blockAvg_le_blockL2 hℓ hN y _).trans ?_
  have e : (fun x => ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *
      blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) N₀) x y') =
      (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ blockIndicator (L ^ k) N₀ y' :=
    funext fun x => mul_blockPullbackMatrix_apply _ x y'
  rw [e]
  exact h

end Kernels

end Balaban.Green
