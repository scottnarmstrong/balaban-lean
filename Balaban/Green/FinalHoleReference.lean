/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.Green.FinalMassGreen
public import Balaban.Green.Perturbation
public import Balaban.Green.CauchyInverse

/-!
# Massive reference covariance on a retained region

The final reference operator is compressed to the complement of an arbitrary set of bad
blocks. Its inverse is the actual Dirichlet covariance of that compressed reference quadratic
form. The decay constants are independent of the selected set and the torus volume. This does
not identify the Hessian of P7's nonlinear variational background with the reference operator.
-/

@[expose] public section

noncomputable section

open Matrix Finset

namespace Balaban.Green

/-- The reference operator on the complement of `Z` is coercive with the full-volume gap.
No regularity of the shape of `Z` is required. -/
theorem finalHoleReference_coercive
    {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]
    (hd : 0 < d) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (Z : Finset (L1Torus d N₀)) :
    IsCoercive ((finalOp d L N₀ k v a).submatrix
      (Subtype.val : (Finset.univ \ Z : Finset (L1Torus d N₀)) → L1Torus d N₀)
      (Subtype.val : (Finset.univ \ Z : Finset (L1Torus d N₀)) → L1Torus d N₀))
      (finalGap d L) := by
  exact isCoercive_submatrix (finalMass_isCoercive (k := k) hd hv0 hv1 ha1 hmass)
    Subtype.val Subtype.val_injective

/-- The inverse of the massive reference operator on retained sites has a uniform
Combes–Thomas bound. It is the inverse of the principal submatrix, not a column deletion
of the full inverse. -/
theorem finalHoleReference_inverse_decay
    {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (Z : Finset (L1Torus d N₀)) :
    let I := (Finset.univ \ Z : Finset (L1Torus d N₀))
    IsUnit ((finalOp d L N₀ k v a).submatrix
      (Subtype.val : I → L1Torus d N₀) (Subtype.val : I → L1Torus d N₀)) ∧
    ∀ x y : I,
      ‖((finalOp d L N₀ k v a).submatrix
        (Subtype.val : I → L1Torus d N₀) (Subtype.val : I → L1Torus d N₀))⁻¹ x y‖ ≤
        2 / finalGap d L * Real.exp (-finalRate d L * dist x y) := by
  dsimp only
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hr : 0 < blockDecayRate d := blockDecayRate_pos hd
  have hball : ∀ x : L1Torus d N₀,
      ∑ y, Real.exp (-(blockDecayRate d / 4) * dist x y) ≤
        ballConst d (blockDecayRate d / 4) :=
    fun x => ballSum_L1Torus (d := d) (m := N₀) (by positivity) x
  have h := combesThomas (c₀ := finalDecayC d L) (δ₀ := blockDecayRate d)
    (γ₀ := finalGap d L) (κ := ballConst d (blockDecayRate d / 4))
    (finalDecayC_pos hd).le hr (finalGap_pos hL)
    (ballConst_decay_nonneg (by positivity))
    (fun x y => by
      simpa only [Matrix.submatrix_apply, Subtype.dist_eq] using
        finalMass_entry_decay (N₀ := N₀) (k := k) hd hk hv0 ha1 ha2
          (x : L1Torus d N₀) (y : L1Torus d N₀))
    (fun x => ballSum_subtype (Finset.univ \ Z) hball x)
    (finalHoleReference_coercive hd hv0 hv1 ha1 hmass Z) (le_refl (0 : ℝ))
  simpa only [Complex.ofReal_zero, zero_smul, add_zero, finalRate, div_eq_mul_inv] using h

/-- The absolute row sum of the inverse is uniform in the bad set and the volume. -/
theorem finalHoleReference_row_bound
    {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (Z : Finset (L1Torus d N₀))
    (x : (Finset.univ \ Z : Finset (L1Torus d N₀))) :
    ∑ y : (Finset.univ \ Z : Finset (L1Torus d N₀)),
      ‖((finalOp d L N₀ k v a).submatrix
        (Subtype.val : (Finset.univ \ Z : Finset (L1Torus d N₀)) → L1Torus d N₀)
        (Subtype.val : (Finset.univ \ Z : Finset (L1Torus d N₀)) → L1Torus d N₀))⁻¹ x y‖ ≤
      2 / finalGap d L * ballConst d (finalRate d L) := by
  have hentry := (finalHoleReference_inverse_decay hd hk hv0 hv1 ha1 ha2 hmass Z).2
  have hr : 0 < finalRate d L := finalRate_pos hd
  have hg : 0 < finalGap d L :=
    finalGap_pos (Nat.pos_of_ne_zero (NeZero.ne L))
  have hball : ∀ z : L1Torus d N₀,
      ∑ y, Real.exp (-finalRate d L * dist z y) ≤ ballConst d (finalRate d L) :=
    fun z => ballSum_L1Torus (d := d) (m := N₀) hr z
  calc
    _ ≤ ∑ y : (Finset.univ \ Z : Finset (L1Torus d N₀)),
        2 / finalGap d L * Real.exp (-finalRate d L * dist x y) :=
          Finset.sum_le_sum fun y _ => hentry x y
    _ = 2 / finalGap d L *
        ∑ y : (Finset.univ \ Z : Finset (L1Torus d N₀)),
          Real.exp (-finalRate d L * dist x y) := by rw [Finset.mul_sum]
    _ ≤ 2 / finalGap d L * ballConst d (finalRate d L) :=
          mul_le_mul_of_nonneg_left
            (ballSum_subtype (Finset.univ \ Z) hball x)
            (by positivity : 0 ≤ 2 / finalGap d L)

/-- The Gaussian determinant of the retained reference problem is nonzero. A quantitative
ratio to the full determinant requires a separate bound on the Schur complement. -/
theorem finalHoleReference_det_ne_zero
    {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (Z : Finset (L1Torus d N₀)) :
    ((finalOp d L N₀ k v a).submatrix
      (Subtype.val : (Finset.univ \ Z : Finset (L1Torus d N₀)) → L1Torus d N₀)
      (Subtype.val : (Finset.univ \ Z : Finset (L1Torus d N₀)) → L1Torus d N₀)).det ≠ 0 := by
  have hunit := (finalHoleReference_inverse_decay hd hk hv0 hv1 ha1 ha2 hmass Z).1
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

end Balaban.Green
