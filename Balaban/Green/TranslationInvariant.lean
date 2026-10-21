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

theorem fineHamiltonian_posDef (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a) :
    (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a).PosDef := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hN' : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) := by exact_mod_cast hN
  have hc : (0 : ℝ) < ((L ^ k : ℕ) : ℝ) ^ 2 := by positivity
  rw [fineHamiltonian_eq hN]
  exact (blockHamiltonian_posDef hℓ hN hd (div_nonneg hν hc.le) (div_pos ha hc)).smul hc

theorem fineHamiltonian_isUnit (hd : 0 < d) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 < a) :
    IsUnit (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a) :=
  (fineHamiltonian_posDef hd hν ha).isUnit

theorem norm_ofReal_sub_sq (r s : ℝ) : ‖(r : ℂ) - (s : ℂ)‖ ^ 2 = (r - s) ^ 2 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Single-scale block decay, gradient form (shared core).**  Let `w, F` be real fields on the
fine torus with `(H w)(x) = F(x)` at every site where `w(x) ≠ 0`, for the unit-lattice operator
`H = fineHamiltonian d ℓ N N₀ ν a`, and `F` supported in the block `y'`.  Then
`N ‖∂w‖_y + ‖w‖_y ≤ C₀ e^{-δ₀ dist(y, y')} ‖F‖_{y'}` (`N = L ^ k`; `‖·‖_y` the block norm
`blockL2`, `∂` the forward differences at the sites of the block).  The equation is required only
where `w ≠ 0`, so this covers the Dirichlet problem of `H` on any set of fine sites. -/
theorem oneScale_blockDecay_fun (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) {w F : Torus d (N₀ * L ^ k) → ℝ}
    (hw : ∀ x, w x ≠ 0 → (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a *ᵥ w) x = F x)
    {y' : Torus d N₀} (hF : ∀ x, F x ≠ 0 → blockMap (L ^ k) N₀ x = y') (y : Torus d N₀) :
    (L : ℝ) ^ k * Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre (L ^ k) N₀ y,
        ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2) + blockL2 (L ^ k) N₀ y w ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        blockL2 (L ^ k) N₀ y' F := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hc : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hcast : ((L ^ k : ℕ) : ℝ) = (L : ℝ) ^ k := by push_cast; rfl
  set c : ℝ := ((L : ℝ) ^ k) ^ 2 with hcdef
  set B := blockHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ (ν / c) (a / c) with hB
  have hH := fineHamiltonian_eq (d := d) (ℓ := N₀ * L ^ k) (m := N₀) hN ν a
  rw [hcast] at hH
  have hBw : ∀ x, (fun x => (w x : ℂ)) x ≠ 0 →
      (B.map (algebraMap ℝ ℂ) *ᵥ fun x => (w x : ℂ)) x = (fun x => ((c⁻¹ * F x : ℝ) : ℂ)) x := by
    intro x hx
    have hx' : w x ≠ 0 := fun h0 => hx (by simp [h0])
    have h1 := hw x hx'
    rw [hH, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul] at h1
    have h1' : c * (B *ᵥ w) x = F x := h1
    have h2 : (B.map (algebraMap ℝ ℂ) *ᵥ fun x => (w x : ℂ)) x = (((B *ᵥ w) x : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.ofReal_sum,
        Complex.ofReal_mul, Complex.coe_algebraMap]
    rw [h2]
    show (((B *ᵥ w) x : ℝ) : ℂ) = ((c⁻¹ * F x : ℝ) : ℂ)
    rw [← h1']; congr 1; field_simp
  have core := oneScale_core_fun hd hk hν ha1 ha2 hBw (y := y)
    (fun x hx => hF x (fun h0 => hx (by simp [h0])))
  simp only [norm_ofReal_sub_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs] at core
  have hsq : Real.sqrt (∑ x, (c⁻¹ * F x) ^ 2) = c⁻¹ * Real.sqrt (∑ x, F x ^ 2) := by
    have : ∑ x, (c⁻¹ * F x) ^ 2 = (c⁻¹) ^ 2 * ∑ x, F x ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hc.le)]
  rw [hsq] at core
  have hsupp : ∑ x, F x ^ 2 = ∑ x ∈ blockFibre (L ^ k) N₀ y', F x ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    by_contra hne
    exact hx (mem_blockFibre.2 (hF x (fun h0 => hne (by rw [h0]; norm_num))))
  have h1 : (L : ℝ) ^ k * Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, ∑ μ : Fin d,
        (w (x + Pi.single μ 1) - w x) ^ 2) +
      Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2) ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        Real.sqrt (∑ x, F x ^ 2) := by
    refine core.trans (le_of_eq ?_)
    have hL0 : (L : ℝ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))
    rw [hcdef]; field_simp
  unfold blockL2
  have hs0 : 0 ≤ ((((L ^ k : ℕ) : ℝ)) ^ d)⁻¹ := by positivity
  rw [Real.sqrt_mul hs0, Real.sqrt_mul hs0, Real.sqrt_mul hs0, ← hsupp]
  have hs1 := Real.sqrt_nonneg ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹)
  calc (L : ℝ) ^ k * (Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y,
          ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2)) +
        Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2)
      = Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * ((L : ℝ) ^ k * Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y,
          ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2) +
        Real.sqrt (∑ x ∈ blockFibre (L ^ k) N₀ y, w x ^ 2)) := by ring
    _ ≤ Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹) * (blockDecayConst d L *
          Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) * Real.sqrt (∑ x, F x ^ 2)) :=
        mul_le_mul_of_nonneg_left h1 hs1
    _ = _ := by ring

/-- **Single-scale block decay (G-2(i), single layer).**  For `F` supported in the block `y'`,
`‖H⁻¹ F‖_y ≤ C₀ e^{-δ₀ dist(y, y')} ‖F‖_{y'}`. -/
theorem oneScale_blockDecay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (F : Torus d (N₀ * L ^ k) → ℝ) {y' : Torus d N₀}
    (hF : ∀ x, F x ≠ 0 → blockMap (L ^ k) N₀ x = y') (y : Torus d N₀) :
    blockL2 (L ^ k) N₀ y ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F) ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) *
        blockL2 (L ^ k) N₀ y' F := by
  have hU := fineHamiltonian_isUnit (L := L) (N₀ := N₀) (k := k) hd hν (by linarith : 0 < a)
  have h := oneScale_blockDecay_fun hd hk hν ha1 ha2
    (w := (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F) (fun x _ => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
        Matrix.one_mulVec]) hF y
  have h0 : 0 ≤ (L : ℝ) ^ k * Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ *
      ∑ x ∈ blockFibre (L ^ k) N₀ y, ∑ μ : Fin d,
        (((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F) (x + Pi.single μ 1) -
          ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ F) x) ^ 2) := by positivity
  linarith

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

/-- **Block averages of single-scale solutions (shared core).**  If `(H w)(x) = 1_{y'}(x)` at
every site where `w(x) ≠ 0` (`1_{y'}` the indicator of the block `y'`), then the average of `w` over
the block `y` is at most `C₀ e^{-δ₀ dist(y, y')}` in absolute value. -/
theorem abs_blockAvg_le_of_eq (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) {w : Torus d (N₀ * L ^ k) → ℝ} {y' : Torus d N₀}
    (hw : ∀ x, w x ≠ 0 → (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a *ᵥ w) x =
      blockIndicator (L ^ k) N₀ y' x) (y : Torus d N₀) :
    |(((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre (L ^ k) N₀ y, w x| ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have h := oneScale_blockDecay_fun hd hk hν ha1 ha2 hw
    (fun x hx => blockIndicator_support y' x hx) y
  rw [blockL2_blockIndicator hℓ hN, mul_one] at h
  have h0 : 0 ≤ (L : ℝ) ^ k * Real.sqrt ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ *
      ∑ x ∈ blockFibre (L ^ k) N₀ y, ∑ μ : Fin d, (w (x + Pi.single μ 1) - w x) ^ 2) := by
    positivity
  exact (abs_blockAvg_le_blockL2 hℓ hN y w).trans (by linarith)

/-- **G-5(a), block-to-block matrix elements.**  `|Q G Q*(y, y')| ≤ C₀ e^{-δ₀ dist(y, y')}`. -/
theorem blockGreenKernel_decay (hd : 0 < d) (hk : 1 ≤ k) {ν a : ℝ} (hν : 0 ≤ ν)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    |blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν a y y'| ≤
      blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y y')) := by
  have hU := fineHamiltonian_isUnit (L := L) (N₀ := N₀) (k := k) hd hν (by linarith : 0 < a)
  rw [blockGreenKernel_apply]
  have e : (fun x => ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *
      blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) N₀) x y') =
      (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ blockIndicator (L ^ k) N₀ y' :=
    funext fun x => mul_blockPullbackMatrix_apply _ x y'
  have e2 : ∑ x ∈ blockFibre (L ^ k) N₀ y, ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *
      blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) N₀) x y' =
      ∑ x ∈ blockFibre (L ^ k) N₀ y, ((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν a)⁻¹ *ᵥ
        blockIndicator (L ^ k) N₀ y') x :=
    Finset.sum_congr rfl fun x _ => congrFun e x
  rw [e2]
  exact abs_blockAvg_le_of_eq hd hk hν ha1 ha2 (fun x _ => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU),
      Matrix.one_mulVec]) y

end Kernels

end Balaban.Green
