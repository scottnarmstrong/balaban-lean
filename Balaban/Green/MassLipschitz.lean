/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.CoarseOperator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# G-5(b): Lipschitz dependence on the mass `ν`

For `H_ν = fineHamiltonian d ℓ N m ν a = N² (-Δ_unit) + ν + a Q*Q` one has
`H_ν₁ - H_ν₂ = (ν₁ - ν₂)` and hence the resolvent identity
`G_ν₁ - G_ν₂ = (ν₂ - ν₁) G_ν₁ G_ν₂` (`Balaban.Green.inv_sub_inv`).  Combining it with the
single-scale block decay `oneScale_blockDecay` (applied twice, summing over intermediate blocks
with the ball sum of the coarse torus) gives, for `ν₁, ν₂ ≥ 0`:

* `Balaban.Green.fineToBlockKernel_lipschitz`: the fine-to-block kernel `a G Q*` is Lipschitz in
  `ν` in the block norm `blockL2`, with the halved decay rate `δ₀ / 2`;
* `Balaban.Green.blockGreenKernel_lipschitz`, `Balaban.Green.unconstrainedUnitOperator_lipschitz`
  (entries of `Δ_tr`);
* `Balaban.Green.coarseGreen_lipschitz`: the entries of `C_tr` (the resolvent identity at the
  coarse level, with the kernel decay of `coarseGreen_decay`).

Lipschitz constants depend on `d, L` only.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban

/-! ### Convolution of exponentially decaying kernels on the torus -/

section Convolution

variable {d m : ℕ} [NeZero m]

theorem torusDist_comm_gen (x y : Torus d m) : torusDist d m x y = torusDist d m y x := by
  have := dist_comm (show L1Torus d m from x) y
  exact this

theorem torusDist_triangle_gen (x y z : Torus d m) :
    torusDist d m x z ≤ torusDist d m x y + torusDist d m y z := by
  have := dist_triangle (show L1Torus d m from x) y z
  exact this

omit [NeZero m] in
theorem torusDist_nonneg_gen (x y : Torus d m) : 0 ≤ torusDist d m x y :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- `∑_b e^{-r d(y,b)} e^{-r d(b,y')} ≤ ballConst(r/2) e^{-(r/2) d(y,y')}`. -/
theorem sum_exp_conv_le {r : ℝ} (hr : 0 < r) (y y' : Torus d m) :
    ∑ b : Torus d m, Real.exp (-r * torusDist d m y b) * Real.exp (-r * torusDist d m b y') ≤
      ballConst d (r / 2) * Real.exp (-(r / 2) * torusDist d m y y') := by
  have h1 : ∀ b : Torus d m, Real.exp (-r * torusDist d m y b) *
      Real.exp (-r * torusDist d m b y') ≤
      Real.exp (-(r / 2) * torusDist d m y b) * Real.exp (-(r / 2) * torusDist d m y y') := by
    intro b
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have t := torusDist_triangle_gen y b y'
    have n1 := torusDist_nonneg_gen y b
    have n2 := torusDist_nonneg_gen b y'
    nlinarith
  calc _ ≤ ∑ b : Torus d m, Real.exp (-(r / 2) * torusDist d m y b) *
        Real.exp (-(r / 2) * torusDist d m y y') := Finset.sum_le_sum fun b _ => h1 b
    _ = (∑ b : Torus d m, Real.exp (-(r / 2) * torusDist d m y b)) *
        Real.exp (-(r / 2) * torusDist d m y y') := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (ballSum_torus d m (by positivity) y) (Real.exp_pos _).le

end Convolution

/-! ### The resolvent identity in the mass -/

section Resolvent

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem fineHamiltonian_sub (hN : 0 < N) (ν₁ ν₂ a : ℝ) :
    fineHamiltonian d ℓ N m ν₁ a - fineHamiltonian d ℓ N m ν₂ a =
      (ν₁ - ν₂) • (1 : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) := by
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  unfold fineHamiltonian latticeLaplacian
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> field_simp <;> ring

theorem fineHamiltonian_mul_inv (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) :
    fineHamiltonian d ℓ N m ν a * (fineHamiltonian d ℓ N m ν a)⁻¹ = 1 := by
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  rw [fineHamiltonian_inv hℓ hN hd hν ha, fineHamiltonian_eq hN, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul,
    blockHamiltonian_mul_inv hℓ hN hd (by positivity) (by positivity), mul_inv_cancel₀ hc,
    one_smul]

theorem fineHamiltonian_inv_mul (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) :
    (fineHamiltonian d ℓ N m ν a)⁻¹ * fineHamiltonian d ℓ N m ν a = 1 := by
  have hc : (N : ℝ) ^ 2 ≠ 0 := by positivity
  have hdet : IsUnit (blockHamiltonian d ℓ N m (ν / (N : ℝ) ^ 2) (a / (N : ℝ) ^ 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1
      (blockHamiltonian_posDef hℓ hN hd (by positivity) (by positivity)).isUnit
  rw [fineHamiltonian_inv hℓ hN hd hν ha, fineHamiltonian_eq hN, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ hdet, inv_mul_cancel₀ hc, one_smul]

/-- **Resolvent identity in the mass**: `G_ν₁ - G_ν₂ = (ν₂ - ν₁) G_ν₁ G_ν₂`. -/
theorem inv_sub_inv (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d) {ν₁ ν₂ a : ℝ} (hν₁ : 0 ≤ ν₁)
    (hν₂ : 0 ≤ ν₂) (ha : 0 < a) :
    (fineHamiltonian d ℓ N m ν₁ a)⁻¹ - (fineHamiltonian d ℓ N m ν₂ a)⁻¹ =
      (ν₂ - ν₁) • ((fineHamiltonian d ℓ N m ν₁ a)⁻¹ * (fineHamiltonian d ℓ N m ν₂ a)⁻¹) := by
  set H₁ := fineHamiltonian d ℓ N m ν₁ a
  set H₂ := fineHamiltonian d ℓ N m ν₂ a
  have e1 : H₁⁻¹ * H₂ * H₂⁻¹ = H₁⁻¹ := by
    rw [Matrix.mul_assoc, fineHamiltonian_mul_inv hℓ hN hd hν₂ ha, Matrix.mul_one]
  have e2 : H₁⁻¹ * H₁ * H₂⁻¹ = H₂⁻¹ := by
    rw [fineHamiltonian_inv_mul hℓ hN hd hν₁ ha, Matrix.one_mul]
  have e3 : H₂ - H₁ = (ν₂ - ν₁) • (1 : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) :=
    fineHamiltonian_sub hN ν₂ ν₁ a
  calc H₁⁻¹ - H₂⁻¹ = H₁⁻¹ * (H₂ - H₁) * H₂⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
    _ = _ := by rw [e3, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

end Resolvent

/-! ### Lipschitz dependence of the kernels -/

section Kernels

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- Decomposition of a field into its restrictions to the blocks. -/
theorem mulVec_blockDecomp {ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (G : Matrix (Torus d ℓ) (Torus d ℓ) ℝ)
    (g : Torus d ℓ → ℝ) (x : Torus d ℓ) :
    (G *ᵥ g) x = ∑ b : Torus d m, (G *ᵥ fun x' => if blockMap N m x' = b then g x' else 0) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp

/-- **Block norm of the mass difference of Green's functions.** -/
theorem green_diff_blockL2 (hd : 0 < d) (hk : 1 ≤ k) {ν₁ ν₂ a : ℝ} (hν₁ : 0 ≤ ν₁)
    (hν₂ : 0 ≤ ν₂) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    blockL2 (L ^ k) N₀ y (((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ -
        (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹) *ᵥ
          blockIndicator (L ^ k) N₀ y') ≤
      |ν₁ - ν₂| * (blockDecayConst d L) ^ 2 * ballConst d (blockDecayRate d / 2) *
        Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ y y') := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have ha0 : 0 < a := by linarith
  have hδ := blockDecayRate_pos hd
  have hC := blockDecayConst_pos (L := L) hd
  set G₁ := (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ with hG₁
  set G₂ := (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹ with hG₂
  set ind := blockIndicator (ℓ := N₀ * L ^ k) (L ^ k) N₀ y' with hind
  have hres := inv_sub_inv hℓ hN hd hν₁ hν₂ ha0
  rw [← hG₁, ← hG₂] at hres
  set g := G₂ *ᵥ ind with hg
  have hvec : (G₁ - G₂) *ᵥ ind = fun x => (ν₂ - ν₁) * (G₁ *ᵥ g) x := by
    have hm : (G₁ * G₂) *ᵥ ind = G₁ *ᵥ g := by rw [hg, Matrix.mulVec_mulVec]
    rw [hres, Matrix.smul_mulVec, hm]
    funext x; simp
  rw [hvec, blockL2_smul, abs_sub_comm]
  -- bound the block norm of `G₁ g`
  have hdec : (fun x => (G₁ *ᵥ g) x) =
      fun x => ∑ b : Torus d N₀, (G₁ *ᵥ fun x' => if blockMap (L ^ k) N₀ x' = b then g x' else 0) x :=
    funext fun x => mulVec_blockDecomp G₁ g x
  have hsum : blockL2 (L ^ k) N₀ y (fun x => (G₁ *ᵥ g) x) ≤
      ∑ b : Torus d N₀, blockL2 (L ^ k) N₀ y
        (fun x => (G₁ *ᵥ fun x' => if blockMap (L ^ k) N₀ x' = b then g x' else 0) x) := by
    rw [hdec]; exact blockL2_sum_le y _ _
  have hterm : ∀ b : Torus d N₀, blockL2 (L ^ k) N₀ y
      (fun x => (G₁ *ᵥ fun x' => if blockMap (L ^ k) N₀ x' = b then g x' else 0) x) ≤
      blockDecayConst d L ^ 2 * (Real.exp (-blockDecayRate d * torusDist d N₀ y b) *
        Real.exp (-blockDecayRate d * torusDist d N₀ b y')) := by
    intro b
    have h1 := oneScale_blockDecay (L := L) hd hk hν₁ ha1 ha2
      (fun x' => if blockMap (L ^ k) N₀ x' = b then g x' else 0) (y' := b)
      (fun x hx => by
        by_contra hne
        exact hx (by simp [hne])) y
    have hbb : blockL2 (L ^ k) N₀ b (fun x' => if blockMap (L ^ k) N₀ x' = b then g x' else 0) =
        blockL2 (L ^ k) N₀ b g := by
      unfold blockL2
      congr 2
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [mem_blockFibre.1 hx]
    have h2 := oneScale_blockDecay (L := L) hd hk hν₂ ha1 ha2 ind
      (fun x hx => blockIndicator_support y' x hx) b
    rw [blockL2_blockIndicator hℓ hN, mul_one] at h2
    rw [hbb] at h1
    have h3 : blockL2 (L ^ k) N₀ b g ≤ blockDecayConst d L *
        Real.exp (-(blockDecayRate d * torusDist d N₀ b y')) := h2
    calc _ ≤ blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y b)) *
          blockL2 (L ^ k) N₀ b g := h1
      _ ≤ blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ y b)) *
          (blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d N₀ b y'))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by rw [neg_mul, neg_mul]; ring
  have hconv := sum_exp_conv_le (m := N₀) hδ y y'
  calc |ν₁ - ν₂| * blockL2 (L ^ k) N₀ y (fun x => (G₁ *ᵥ g) x)
      ≤ |ν₁ - ν₂| * ∑ b : Torus d N₀, blockDecayConst d L ^ 2 *
          (Real.exp (-blockDecayRate d * torusDist d N₀ y b) *
            Real.exp (-blockDecayRate d * torusDist d N₀ b y')) :=
        mul_le_mul_of_nonneg_left (hsum.trans (Finset.sum_le_sum fun b _ => hterm b))
          (abs_nonneg _)
    _ = |ν₁ - ν₂| * (blockDecayConst d L ^ 2 * ∑ b : Torus d N₀,
          Real.exp (-blockDecayRate d * torusDist d N₀ y b) *
            Real.exp (-blockDecayRate d * torusDist d N₀ b y')) := by rw [← Finset.mul_sum]
    _ ≤ |ν₁ - ν₂| * (blockDecayConst d L ^ 2 * (ballConst d (blockDecayRate d / 2) *
          Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ y y'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hconv (by positivity))
          (abs_nonneg _)
    _ = _ := by ring

/-- The Lipschitz constant in the mass for the block-level kernels. -/
noncomputable def massLipConst (d L : ℕ) : ℝ :=
  blockDecayConst d L ^ 2 * ballConst d (blockDecayRate d / 2)

theorem massLipConst_nonneg {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 ≤ massLipConst d L := by
  unfold massLipConst ballConst
  have hq : 0 < Real.exp (-(blockDecayRate d / 2)) ∧ Real.exp (-(blockDecayRate d / 2)) < 1 :=
    exp_one_sub_pos (by have := blockDecayRate_pos hd; positivity)
  have h1 : 0 < 1 - Real.exp (-(blockDecayRate d / 2)) := by linarith [hq.2]
  have h2 : 0 < 1 + Real.exp (-(blockDecayRate d / 2)) := by linarith [hq.1]
  positivity

/-- **G-5(b), fine-to-block kernel.**  `ν ↦ a G_ν Q*` is Lipschitz in the block norm:
`‖(a G_ν₁ Q* - a G_ν₂ Q*)(·, y')‖_y ≤ a |ν₁ - ν₂| C e^{-(δ₀/2) dist(y, y')}`. -/
theorem fineToBlockKernel_lipschitz (hd : 0 < d) (hk : 1 ≤ k) {ν₁ ν₂ a : ℝ} (hν₁ : 0 ≤ ν₁)
    (hν₂ : 0 ≤ ν₂) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    blockL2 (L ^ k) N₀ y (fun x => fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a x y' -
        fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a x y') ≤
      a * (|ν₁ - ν₂| * massLipConst d L *
        Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ y y')) := by
  have ha0 : 0 < a := by linarith
  have h := green_diff_blockL2 (L := L) hd hk hν₁ hν₂ ha1 ha2 y y'
  have e : (fun x => fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a x y' -
        fineToBlockKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a x y') =
      fun x => a * (((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ -
        (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹) *ᵥ
          blockIndicator (L ^ k) N₀ y') x := by
    funext x
    simp only [fineToBlockKernel, Matrix.smul_apply, smul_eq_mul, Matrix.sub_mulVec,
      Pi.sub_apply, mul_blockPullbackMatrix_apply]
    ring
  rw [e, blockL2_smul, abs_of_pos ha0]
  unfold massLipConst
  calc a * _ ≤ a * (|ν₁ - ν₂| * blockDecayConst d L ^ 2 * ballConst d (blockDecayRate d / 2) *
        Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ y y')) :=
        mul_le_mul_of_nonneg_left h ha0.le
    _ = _ := by ring

/-- **G-5(b), block-to-block kernel.** -/
theorem blockGreenKernel_lipschitz (hd : 0 < d) (hk : 1 ≤ k) {ν₁ ν₂ a : ℝ} (hν₁ : 0 ≤ ν₁)
    (hν₂ : 0 ≤ ν₂) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    |blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a y y' -
        blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a y y'| ≤
      |ν₁ - ν₂| * massLipConst d L *
        Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ y y') := by
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have h := green_diff_blockL2 (L := L) hd hk hν₁ hν₂ ha1 ha2 y y'
  have e : blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a y y' -
        blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a y y' =
      ((((L ^ k : ℕ) : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre (L ^ k) N₀ y,
        (((fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a)⁻¹ -
          (fineHamiltonian d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a)⁻¹) *ᵥ
            blockIndicator (L ^ k) N₀ y') x) := by
    rw [blockGreenKernel_apply, blockGreenKernel_apply, ← mul_sub, ← Finset.sum_sub_distrib]
    simp only [Matrix.sub_mulVec, Pi.sub_apply, mul_blockPullbackMatrix_apply]
  rw [e]
  unfold massLipConst
  refine (abs_blockAvg_le_blockL2 hℓ hN y _).trans (h.trans (le_of_eq ?_))
  ring

/-- **G-5(b), `Δ_tr`.**  The entries of `Δ_tr = a - a² Q G Q*` are Lipschitz in `ν`. -/
theorem unconstrainedUnitOperator_lipschitz (hd : 0 < d) (hk : 1 ≤ k) {ν₁ ν₂ a : ℝ}
    (hν₁ : 0 ≤ ν₁) (hν₂ : 0 ≤ ν₂) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (y y' : Torus d N₀) :
    |unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a y y' -
        unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a y y'| ≤
      4 * (|ν₁ - ν₂| * massLipConst d L *
        Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ y y')) := by
  have h := blockGreenKernel_lipschitz (L := L) hd hk hν₁ hν₂ ha1 ha2 y y'
  have e : unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a y y' -
        unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a y y' =
      -(a ^ 2 * (blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a y y' -
        blockGreenKernel d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a y y')) := by
    simp only [unconstrainedUnitOperator, blockGreenKernel, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg a)]
  have : a ^ 2 ≤ 4 := by nlinarith
  calc a ^ 2 * _ ≤ 4 * _ := mul_le_mul this h (abs_nonneg _) (by norm_num)
    _ = _ := by ring

end Kernels

/-! ### Lipschitz dependence of `C_tr` -/

section CoarseGreen

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] [NeZero M]

/-- The decay rate of the Lipschitz estimate for `C_tr`. -/
noncomputable def lipRate (d L : ℕ) : ℝ := min (trRate d L) (blockDecayRate d / 2)

theorem lipRate_pos {d L : ℕ} [NeZero L] (hd : 0 < d) : 0 < lipRate d L :=
  lt_min (trRate_pos hd) (by have := blockDecayRate_pos hd; positivity)

/-- The Lipschitz constant of `C_tr` in the mass. -/
noncomputable def coarseLipConst (d L : ℕ) : ℝ :=
  (2 * (trGamma d L)⁻¹) ^ 2 * (4 * massLipConst d L) *
    (ballConst d (lipRate d L / 2) * ballConst d (lipRate d L / 4))

theorem ballConst_nonneg {d : ℕ} {r : ℝ} (hr : 0 < r) : 0 ≤ ballConst d r := by
  unfold ballConst
  have hq : 0 < Real.exp (-r) ∧ Real.exp (-r) < 1 := exp_one_sub_pos hr
  have h1 : 0 < 1 - Real.exp (-r) := by linarith [hq.2]
  have h2 : 0 < 1 + Real.exp (-r) := by linarith [hq.1]
  positivity

/-- **G-5(b), `C_tr`.**  `ν ↦ C_tr = (Δ_tr + (a'/L²) Q*Q)⁻¹` is Lipschitz on `[0, ∞)` in the kernel
norm: `|C_tr(ν₁) - C_tr(ν₂)|(y, y') ≤ K |ν₁ - ν₂| e^{-(r/4) dist(y, y')}`, with `r = lipRate d L`
and `K = coarseLipConst d L` depending on `d, L` only. -/
theorem coarseGreen_lipschitz_of_nonneg (hd : 0 < d) (hk : 1 ≤ k) (hm : N₀ = L * M) {ν₁ ν₂ a a' : ℝ}
    (hν₁0 : 0 ≤ ν₁) (hν₂0 : 0 ≤ ν₂) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2) (y y' : Torus d N₀) :
    |(coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν₁ a a')⁻¹ y y' -
        (coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν₂ a a')⁻¹ y y'| ≤
      |ν₁ - ν₂| * coarseLipConst d L * Real.exp (-(lipRate d L / 4) * torusDist d N₀ y y') := by
  have hN : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hℓ : N₀ * L ^ k = L ^ k * N₀ := mul_comm _ _
  set A₁ := coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν₁ a a' with hA₁
  set A₂ := coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν₂ a a' with hA₂
  have hu₁ : IsUnit A₁.det := coarseOperator_det_isUnit_of_nonneg hd hℓ hN hm hν₁0 ha1 ha'1
  have hu₂ : IsUnit A₂.det := coarseOperator_det_isUnit_of_nonneg hd hℓ hN hm hν₂0 ha1 ha'1
  have hr := lipRate_pos (L := L) hd
  set r := lipRate d L with hrdef
  have hr1 : r ≤ trRate d L := min_le_left _ _
  have hr2 : r ≤ blockDecayRate d / 2 := min_le_right _ _
  have hγ := trGamma_pos (L := L) hd
  -- identity
  have hid : A₁⁻¹ - A₂⁻¹ = A₁⁻¹ * (A₂ - A₁) * A₂⁻¹ := by
    have e1 : A₁⁻¹ * A₂ * A₂⁻¹ = A₁⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu₂, Matrix.mul_one]
    have e2 : A₁⁻¹ * A₁ * A₂⁻¹ = A₂⁻¹ := by
      rw [Matrix.nonsing_inv_mul _ hu₁, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]
  -- decay of the two inverses
  have hC₁ : ∀ u v : Torus d N₀, |A₁⁻¹ u v| ≤
      2 * (trGamma d L)⁻¹ * Real.exp (-(r) * torusDist d N₀ u v) := by
    intro u v
    refine (coarseGreen_decay_of_nonneg (L := L) (M := M) hd hk hm hν₁0 ha1 ha2 ha'1 ha'2 u v).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := mul_le_mul_of_nonneg_right hr1 (torusDist_nonneg_gen (m := N₀) u v)
    nlinarith
  have hC₂ : ∀ u v : Torus d N₀, |A₂⁻¹ u v| ≤
      2 * (trGamma d L)⁻¹ * Real.exp (-(r) * torusDist d N₀ u v) := by
    intro u v
    refine (coarseGreen_decay_of_nonneg (L := L) (M := M) hd hk hm hν₂0 ha1 ha2 ha'1 ha'2 u v).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have := mul_le_mul_of_nonneg_right hr1 (torusDist_nonneg_gen (m := N₀) u v)
    nlinarith
  -- the difference
  set ε := 4 * (|ν₁ - ν₂| * massLipConst d L) with hε
  have hD : ∀ z w : Torus d N₀, |(A₂ - A₁) z w| ≤ ε * Real.exp (-(r) * torusDist d N₀ z w) := by
    intro z w
    have h := unconstrainedUnitOperator_lipschitz (L := L) hd hk hν₂0 hν₁0 ha1 ha2 z w
    have e : (A₂ - A₁) z w =
        unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν₂ a z w -
          unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ ν₁ a z w := by
      simp only [hA₁, hA₂, coarseOperator, Matrix.sub_apply, Matrix.add_apply]
      ring
    rw [e]
    refine h.trans ?_
    rw [abs_sub_comm ν₂ ν₁, hε]
    have hm0 := massLipConst_nonneg (L := L) hd
    have : Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ z w) ≤
        Real.exp (-(r) * torusDist d N₀ z w) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_right hr2 (torusDist_nonneg_gen (m := N₀) z w)
      nlinarith
    calc 4 * (|ν₁ - ν₂| * massLipConst d L * Real.exp (-(blockDecayRate d / 2) * torusDist d N₀ z w))
        ≤ 4 * (|ν₁ - ν₂| * massLipConst d L * Real.exp (-(r) * torusDist d N₀ z w)) := by gcongr
      _ = _ := by ring
  -- the double sum
  have hε0 : 0 ≤ ε := by
    have := massLipConst_nonneg (L := L) hd
    rw [hε]; positivity
  have hconv1 : ∀ z : Torus d N₀, ∑ w : Torus d N₀, Real.exp (-(r) * torusDist d N₀ z w) *
      Real.exp (-(r) * torusDist d N₀ w y') ≤
      ballConst d (r / 2) * Real.exp (-(r / 2) * torusDist d N₀ z y') :=
    fun z => sum_exp_conv_le hr z y'
  have hconv2 : ∑ z : Torus d N₀, Real.exp (-(r / 2) * torusDist d N₀ y z) *
      Real.exp (-(r / 2) * torusDist d N₀ z y') ≤
      ballConst d (r / 4) * Real.exp (-(r / 4) * torusDist d N₀ y y') := by
    have := sum_exp_conv_le (m := N₀) (by positivity : 0 < r / 2) y y'
    rwa [show r / 2 / 2 = r / 4 by ring] at this
  have hb2 := ballConst_nonneg (d := d) (by positivity : 0 < r / 2)
  have e : A₁⁻¹ y y' - A₂⁻¹ y y' = ∑ z, ∑ w, A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y' := by
    rw [← Matrix.sub_apply, hid]
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  set K := 2 * (trGamma d L)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hterm : ∀ z w : Torus d N₀, |A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y'| ≤
      K ^ 2 * ε * (Real.exp (-(r) * torusDist d N₀ y z) *
        (Real.exp (-(r) * torusDist d N₀ z w) * Real.exp (-(r) * torusDist d N₀ w y'))) := by
    intro z w
    rw [abs_mul, abs_mul]
    have h1 := hC₁ y z
    have h2 := hD z w
    have h3 := hC₂ w y'
    calc |A₁⁻¹ y z| * |(A₂ - A₁) z w| * |A₂⁻¹ w y'|
        ≤ (K * Real.exp (-(r) * torusDist d N₀ y z)) *
          (ε * Real.exp (-(r) * torusDist d N₀ z w)) *
          (K * Real.exp (-(r) * torusDist d N₀ w y')) := by
          gcongr
      _ = _ := by ring
  have hinner : ∀ z : Torus d N₀, ∑ w : Torus d N₀, |A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y'| ≤
      K ^ 2 * ε * ballConst d (r / 2) *
        (Real.exp (-(r / 2) * torusDist d N₀ y z) * Real.exp (-(r / 2) * torusDist d N₀ z y')) := by
    intro z
    have hz := hconv1 z
    have hyz : Real.exp (-(r) * torusDist d N₀ y z) ≤
        Real.exp (-(r / 2) * torusDist d N₀ y z) := by
      apply Real.exp_le_exp.2
      have := torusDist_nonneg_gen (m := N₀) y z
      nlinarith
    calc ∑ w : Torus d N₀, |A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y'|
        ≤ ∑ w : Torus d N₀, K ^ 2 * ε * (Real.exp (-(r) * torusDist d N₀ y z) *
          (Real.exp (-(r) * torusDist d N₀ z w) * Real.exp (-(r) * torusDist d N₀ w y'))) :=
          Finset.sum_le_sum fun w _ => hterm z w
      _ = K ^ 2 * ε * (Real.exp (-(r) * torusDist d N₀ y z) *
          ∑ w : Torus d N₀, (Real.exp (-(r) * torusDist d N₀ z w) *
            Real.exp (-(r) * torusDist d N₀ w y'))) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ K ^ 2 * ε * (Real.exp (-(r) * torusDist d N₀ y z) *
          (ballConst d (r / 2) * Real.exp (-(r / 2) * torusDist d N₀ z y'))) := by
          gcongr
      _ ≤ K ^ 2 * ε * (Real.exp (-(r / 2) * torusDist d N₀ y z) *
          (ballConst d (r / 2) * Real.exp (-(r / 2) * torusDist d N₀ z y'))) := by
          gcongr
      _ = _ := by ring
  rw [e]
  have hfinal : |∑ z, ∑ w, A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y'| ≤
      K ^ 2 * ε * ballConst d (r / 2) * (ballConst d (r / 4) *
        Real.exp (-(r / 4) * torusDist d N₀ y y')) := by
    calc _ ≤ ∑ z, |∑ w, A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z, ∑ w, |A₁⁻¹ y z * (A₂ - A₁) z w * A₂⁻¹ w y'| :=
          Finset.sum_le_sum fun z _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ z : Torus d N₀, K ^ 2 * ε * ballConst d (r / 2) *
          (Real.exp (-(r / 2) * torusDist d N₀ y z) *
            Real.exp (-(r / 2) * torusDist d N₀ z y')) :=
          Finset.sum_le_sum fun z _ => hinner z
      _ = K ^ 2 * ε * ballConst d (r / 2) * ∑ z : Torus d N₀,
          (Real.exp (-(r / 2) * torusDist d N₀ y z) *
            Real.exp (-(r / 2) * torusDist d N₀ z y')) := by rw [← Finset.mul_sum]
      _ ≤ _ := by gcongr
  refine hfinal.trans (le_of_eq ?_)
  unfold coarseLipConst
  rw [hε, hK]
  ring


/-- **G-5(b), `C_tr`**, the case `ν₁, ν₂ ∈ [0, 2]` of `coarseGreen_lipschitz_of_nonneg`. -/
theorem coarseGreen_lipschitz (hd : 0 < d) (hk : 1 ≤ k) (hm : N₀ = L * M) {ν₁ ν₂ a a' : ℝ}
    (hν₁0 : 0 ≤ ν₁) (_hν₁2 : ν₁ ≤ 2) (hν₂0 : 0 ≤ ν₂) (_hν₂2 : ν₂ ≤ 2) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2) (y y' : Torus d N₀) :
    |(coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν₁ a a')⁻¹ y y' -
        (coarseOperator d (N₀ * L ^ k) (L ^ k) N₀ L M ν₂ a a')⁻¹ y y'| ≤
      |ν₁ - ν₂| * coarseLipConst d L * Real.exp (-(lipRate d L / 4) * torusDist d N₀ y y') :=
  coarseGreen_lipschitz_of_nonneg hd hk hm hν₁0 hν₂0 ha1 ha2 ha'1 ha'2 y y'

end CoarseGreen

end Balaban.Green
