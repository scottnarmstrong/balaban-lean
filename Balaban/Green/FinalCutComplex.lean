/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalCutFamily
public import Balaban.Green.FinalComplexHessian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Complex cut family of the final operator (FINALCUT, leaves 1-3)

For a labelling `c : sites → κ` of the sites by cells (`κ` finite) and complex cell parameters
`s : κ → ℂ`, the cut weight is `1` for two sites of the same cell and `s (c x) * s (c y)` for two
sites of different cells.  The cut operator `U_s` has the entries `w_s x y * U x y`, where
`U = finalOp`.  Then `U_1 = U`, `U_0` is the block diagonal compression of `U`, and every entry
is a polynomial in `s`.

With `E_s = U_s - U` supported on pairs of different cells, `WSmall r η E_s` holds for
`‖s_P‖ ≤ ρ` with `η = (ρ² + 1) S_∂(r)`, `S_∂(r)` the largest weighted row or column sum of the
entries of `U` between different cells.  The entry decay of `U` gives `S_∂(r) ≤ c₀ ballConst d (δ₀ - r)`
(no smallness), and with a separation `M` between different cells the extra factor
`exp(-(δ₀ - r - σ) M)`.  Under the explicit inequality `η < finalGap d L` the gap, resolvent,
inverse and square-root decay and the analyticity of the inverse follow from the landed
perturbation lemmas.
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

section Generic

variable {ι κ : Type*}

/-- The complex cut weight: `1` inside a cell, `s (c x) * s (c y)` across cells. -/
noncomputable def cutWeightC [DecidableEq κ] (c : ι → κ) (s : κ → ℂ) (x y : ι) : ℂ :=
  if c x = c y then 1 else s (c x) * s (c y)

/-- The entries of `A` multiplied by the complex cut weight. -/
noncomputable def cutMatC [DecidableEq κ] (c : ι → κ) (s : κ → ℂ) (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Matrix.of fun x y => cutWeightC c s x y * A x y

variable [DecidableEq κ]

theorem cutMatC_one (c : ι → κ) (A : Matrix ι ι ℂ) : cutMatC c (fun _ => 1) A = A := by
  ext x y; simp [cutMatC, cutWeightC]

/-- At `s ≡ 0` the cut matrix is the block compression. -/
theorem cutMatC_zero (c : ι → κ) (A : Matrix ι ι ℂ) :
    cutMatC c (fun _ => 0) A = Matrix.of fun x y => if c x = c y then A x y else 0 := by
  ext x y; by_cases h : c x = c y <;> simp [cutMatC, cutWeightC, h]

/-- Block diagonality at `s ≡ 0`: entries between different cells vanish. -/
theorem cutMatC_zero_apply_of_ne (c : ι → κ) (A : Matrix ι ι ℂ) {x y : ι} (h : c x ≠ c y) :
    cutMatC c (fun _ => 0) A x y = 0 := by
  simp [cutMatC, cutWeightC, h]

/-- At `s ≡ 0` the cut matrix is `blockMat` for a labelling by `ℕ`. -/
theorem cutMatC_zero_eq_blockMat (c : ι → ℕ) (A : Matrix ι ι ℂ) :
    cutMatC c (fun _ => 0) A = blockMat c A := by
  rw [cutMatC_zero]; rfl

/-- Each entry is a polynomial of degree at most two in the coordinates of `s`; in particular it
is analytic. -/
theorem cutMatC_entry_analytic [Fintype κ] (c : ι → κ) (A : Matrix ι ι ℂ) (x y : ι) :
    AnalyticOnNhd ℂ (fun s : κ → ℂ => cutMatC c s A x y) Set.univ := by
  intro s _
  unfold cutMatC cutWeightC
  by_cases h : c x = c y
  · simp only [Matrix.of_apply, h, ite_true]
    exact analyticAt_const
  · simp only [Matrix.of_apply, h, ite_false]
    have h1 : AnalyticAt ℂ (fun s : κ → ℂ => s (c x)) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) (c x)).analyticAt s
    have h2 : AnalyticAt ℂ (fun s : κ → ℂ => s (c y)) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) (c y)).analyticAt s
    exact (h1.mul h2).mul analyticAt_const

theorem cutMatC_sub_entry_analytic [Fintype κ] (c : ι → κ) (A : Matrix ι ι ℂ) (x y : ι) (s : κ → ℂ) :
    AnalyticAt ℂ (fun w : κ → ℂ => (cutMatC c w A - A) x y) s := by
  show AnalyticAt ℂ (fun w : κ → ℂ => cutMatC c w A x y - A x y) s
  exact (cutMatC_entry_analytic c A x y s (Set.mem_univ _)).sub analyticAt_const

/-- Covariance under a permutation of the sites preserving the cells. -/
theorem cutMatC_submatrix (c : ι → κ) (s : κ → ℂ) (A : Matrix ι ι ℂ) (σ : ι ≃ ι)
    (hσ : ∀ x, c (σ x) = c x) :
    (cutMatC c s A).submatrix σ σ = cutMatC c s (A.submatrix σ σ) := by
  ext x y; simp [cutMatC, cutWeightC, hσ]

/-- The entries of `cutMatC c s A - A` are supported on pairs of different cells, with norm at
most `(ρ² + 1) ‖A x y‖` when `‖s_P‖ ≤ ρ`. -/
theorem norm_cutMatC_sub_le (c : ι → κ) {s : κ → ℂ} {ρ : ℝ} (hs : ∀ P, ‖s P‖ ≤ ρ)
    (A : Matrix ι ι ℂ) (x y : ι) :
    ‖(cutMatC c s A - A) x y‖ ≤ (ρ ^ 2 + 1) * (if c x = c y then 0 else ‖A x y‖) := by
  by_cases h : c x = c y
  · simp [cutMatC, cutWeightC, h]
  · have e : (cutMatC c s A - A) x y = (s (c x) * s (c y) - 1) * A x y := by
      simp [cutMatC, cutWeightC, h, sub_mul]
    rw [e]
    simp only [h, ite_false]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖s (c x) * s (c y) - 1‖ ≤ ‖s (c x) * s (c y)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ρ ^ 2 + 1 := by
        rw [norm_mul, norm_one, sq]
        have h0 : 0 ≤ ‖s (c x)‖ := norm_nonneg _
        have h1 := hs (c x)
        have h2 := hs (c y)
        nlinarith [norm_nonneg (s (c y))]

end Generic

section Weighted

variable {ι κ : Type*} [Fintype ι] [PseudoMetricSpace ι] [DecidableEq κ]

/-- Weighted row sum of the entries of `A` between different cells. -/
noncomputable def crossRow (c : ι → κ) (A : Matrix ι ι ℂ) (r : ℝ) (x : ι) : ℝ :=
  ∑ y, if c x = c y then 0 else ‖A x y‖ * Real.exp (r * dist x y)

/-- Weighted column sum of the entries of `A` between different cells. -/
noncomputable def crossCol (c : ι → κ) (A : Matrix ι ι ℂ) (r : ℝ) (y : ι) : ℝ :=
  ∑ x, if c x = c y then 0 else ‖A x y‖ * Real.exp (r * dist x y)

/-- `S_∂(r)`: the larger of the suprema of the cross-cell weighted row sums and column sums. -/
noncomputable def finalCutBoundary (c : ι → κ) (A : Matrix ι ι ℂ) (r : ℝ) : ℝ :=
  max (⨆ x, crossRow c A r x) (⨆ y, crossCol c A r y)

theorem crossRow_le_boundary (c : ι → κ) (A : Matrix ι ι ℂ) (r : ℝ) (x : ι) :
    crossRow c A r x ≤ finalCutBoundary c A r :=
  (le_ciSup (Finite.bddAbove_range _) x).trans (le_max_left _ _)

theorem crossCol_le_boundary (c : ι → κ) (A : Matrix ι ι ℂ) (r : ℝ) (y : ι) :
    crossCol c A r y ≤ finalCutBoundary c A r :=
  (le_ciSup (Finite.bddAbove_range _) y).trans (le_max_right _ _)

/-- **Weighted smallness of the cut** (`finalCutWeightedBound`, generic matrix): for
`‖s_P‖ ≤ ρ`, `WSmall r ((ρ² + 1) S_∂(r)) (U_s - U)`. -/
theorem wSmall_cutMatC_sub (c : ι → κ) {s : κ → ℂ} {ρ : ℝ} (hs : ∀ P, ‖s P‖ ≤ ρ)
    (A : Matrix ι ι ℂ) (r : ℝ) :
    WSmall r ((ρ ^ 2 + 1) * finalCutBoundary c A r) (cutMatC c s A - A) := by
  have hρ : 0 ≤ ρ ^ 2 + 1 := by positivity
  constructor
  · intro x
    calc ∑ y, ‖(cutMatC c s A - A) x y‖ * Real.exp (r * dist x y)
        ≤ ∑ y, (ρ ^ 2 + 1) * (if c x = c y then 0 else ‖A x y‖ * Real.exp (r * dist x y)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have := norm_cutMatC_sub_le c hs A x y
          by_cases h : c x = c y
          · simp [h, cutMatC, cutWeightC]
          · simp only [h, ite_false] at this ⊢
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = (ρ ^ 2 + 1) * crossRow c A r x := by rw [← Finset.mul_sum]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (crossRow_le_boundary c A r x) hρ
  · intro y
    calc ∑ x, ‖(cutMatC c s A - A) x y‖ * Real.exp (r * dist x y)
        ≤ ∑ x, (ρ ^ 2 + 1) * (if c x = c y then 0 else ‖A x y‖ * Real.exp (r * dist x y)) := by
          refine Finset.sum_le_sum fun x _ => ?_
          have := norm_cutMatC_sub_le c hs A x y
          by_cases h : c x = c y
          · simp [h, cutMatC, cutWeightC]
          · simp only [h, ite_false] at this ⊢
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = (ρ ^ 2 + 1) * crossCol c A r y := by rw [← Finset.mul_sum]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (crossCol_le_boundary c A r y) hρ

end Weighted

section Final

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {κ : Type*} [DecidableEq κ]

/-- The complex cut family `U_s` of the final operator. -/
noncomputable def finalOpCutC (c : L1Torus d N₀ → κ) (s : κ → ℂ) (v a : ℝ) :
    Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ :=
  cutMatC c s (finalOp d L N₀ k v a)

/-- **`finalCutComplexSpec`**: `U_1 = finalOp`. -/
theorem finalOpCutC_one (c : L1Torus d N₀ → κ) (v a : ℝ) :
    finalOpCutC (d := d) (L := L) (k := k) c (fun _ => 1) v a = finalOp d L N₀ k v a :=
  cutMatC_one _ _

/-- `U_0` is block diagonal for the cells of `c`. -/
theorem finalOpCutC_zero_apply_of_ne (c : L1Torus d N₀ → κ) (v a : ℝ) {x y : L1Torus d N₀}
    (h : c x ≠ c y) : finalOpCutC (d := d) (L := L) (k := k) c (fun _ => 0) v a x y = 0 :=
  cutMatC_zero_apply_of_ne _ _ h

theorem finalOpCutC_zero_apply_of_eq (c : L1Torus d N₀ → κ) (v a : ℝ) {x y : L1Torus d N₀}
    (h : c x = c y) : finalOpCutC (d := d) (L := L) (k := k) c (fun _ => 0) v a x y =
      finalOp d L N₀ k v a x y := by
  simp [finalOpCutC, cutMatC, cutWeightC, h]

/-- For a labelling by `ℕ`, `U_0 = blockMat c finalOp`. -/
theorem finalOpCutC_zero_eq_blockMat (c : L1Torus d N₀ → ℕ) (v a : ℝ) :
    finalOpCutC (d := d) (L := L) (k := k) c (fun _ => 0) v a =
      blockMat c (finalOp d L N₀ k v a) :=
  cutMatC_zero_eq_blockMat _ _

/-- Each entry of `U_s` is analytic (indeed polynomial) in `s`. -/
theorem finalOpCutC_entry_analytic [Fintype κ] (c : L1Torus d N₀ → κ) (v a : ℝ)
    (x y : L1Torus d N₀) :
    AnalyticOnNhd ℂ (fun s : κ → ℂ => finalOpCutC (d := d) (L := L) (k := k) c s v a x y)
      Set.univ :=
  cutMatC_entry_analytic _ _ x y

/-- Covariance under a permutation of the sites preserving the cells. -/
theorem finalOpCutC_submatrix (c : L1Torus d N₀ → κ) (s : κ → ℂ) (v a : ℝ)
    (σ : L1Torus d N₀ ≃ L1Torus d N₀) (hσ : ∀ x, c (σ x) = c x) :
    (finalOpCutC (d := d) (L := L) (k := k) c s v a).submatrix σ σ =
      cutMatC c s ((finalOp d L N₀ k v a).submatrix σ σ) :=
  cutMatC_submatrix _ _ _ σ hσ

/-- On real parameters, constant `σ` on every cell of a two-cell labelling gives the cut weight
`σ²` across and `1` inside: the real two-cell interpolation `twoCellLam (σ²)` of
`FinalCutFamily.lean` is an instance of the complex family. -/
theorem finalOpCutC_const_eq_twoCell (X : Set (L1Torus d N₀)) [DecidablePred (· ∈ X)]
    (σ : ℝ) (v a : ℝ) :
    finalOpCutC (d := d) (L := L) (k := k) (fun x => decide (x ∈ X)) (fun _ => (σ : ℂ)) v a =
      finalOpCut (d := d) (L := L) (k := k)
        (cutWeight (twoCellLam (σ ^ 2)) (twoCellLabel X)) v a := by
  ext x y
  simp only [finalOpCut, finalOpCutC, cutMatC, cutWeightC, Matrix.of_apply, cutWeight_twoCell,
    smul_eq_mul]
  by_cases h : (x ∈ X ↔ y ∈ X)
  · have : decide (x ∈ X) = decide (y ∈ X) := by simpa using h
    simp [h]
  · have : ¬ decide (x ∈ X) = decide (y ∈ X) := by simpa using h
    simp [this, h]; left; ring

/-! ### The explicit bound of `S_∂` -/

/-- The cross-cell weighted row sum of `U` is at most `c₀ ballConst d (δ₀ - r)` for `r < δ₀`:
the true bound, with no smallness. -/
theorem crossRow_final_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (c : L1Torus d N₀ → κ) {r : ℝ} (hr : r < blockDecayRate d)
    (x : L1Torus d N₀) :
    crossRow c (finalOp d L N₀ k v a) r x ≤
      finalDecayC d L * ballConst d (blockDecayRate d - r) := by
  have hc := finalDecayC_pos (L := L) hd
  have hpos : 0 < blockDecayRate d - r := by linarith
  calc crossRow c (finalOp d L N₀ k v a) r x
      ≤ ∑ y, finalDecayC d L * Real.exp (-(blockDecayRate d - r) * dist x y) := by
        refine Finset.sum_le_sum fun y _ => ?_
        have e : Real.exp (-(blockDecayRate d - r) * dist x y) =
            Real.exp (-blockDecayRate d * dist x y) * Real.exp (r * dist x y) := by
          rw [← Real.exp_add]; ring_nf
        by_cases h : c x = c y
        · simp only [h, ite_true]; positivity
        · simp only [h, ite_false]
          rw [e, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (finalMass_entry_decay hd hk hv0 ha1 ha2 x y)
            (Real.exp_pos _).le
    _ = finalDecayC d L * ∑ y, Real.exp (-(blockDecayRate d - r) * dist x y) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ballSum_L1Torus (d := d) (m := N₀) hpos x) hc.le

theorem crossCol_final_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (c : L1Torus d N₀ → κ) {r : ℝ} (hr : r < blockDecayRate d)
    (y : L1Torus d N₀) :
    crossCol c (finalOp d L N₀ k v a) r y ≤
      finalDecayC d L * ballConst d (blockDecayRate d - r) := by
  have hc := finalDecayC_pos (L := L) hd
  have hpos : 0 < blockDecayRate d - r := by linarith
  calc crossCol c (finalOp d L N₀ k v a) r y
      ≤ ∑ x, finalDecayC d L * Real.exp (-(blockDecayRate d - r) * dist y x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have e : Real.exp (-(blockDecayRate d - r) * dist y x) =
            Real.exp (-blockDecayRate d * dist x y) * Real.exp (r * dist x y) := by
          rw [dist_comm y x, ← Real.exp_add]; ring_nf
        by_cases h : c x = c y
        · simp only [h, ite_true]; positivity
        · simp only [h, ite_false]
          rw [e, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (finalMass_entry_decay hd hk hv0 ha1 ha2 x y)
            (Real.exp_pos _).le
    _ = finalDecayC d L * ∑ x, Real.exp (-(blockDecayRate d - r) * dist y x) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (ballSum_L1Torus (d := d) (m := N₀) hpos y) hc.le

/-- **True explicit bound of `S_∂`** (no separation between cells): for `r < δ₀`,
`S_∂(r) ≤ c₀ ballConst d (δ₀ - r)`. -/
theorem finalCutBoundary_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (c : L1Torus d N₀ → κ) {r : ℝ} (hr : r < blockDecayRate d) :
    finalCutBoundary c (finalOp d L N₀ k v a) r ≤
      finalDecayC d L * ballConst d (blockDecayRate d - r) := by
  have hc := finalDecayC_pos (L := L) hd
  have hpos : 0 < blockDecayRate d - r := by linarith
  have h0 : 0 ≤ finalDecayC d L * ballConst d (blockDecayRate d - r) :=
    mul_nonneg hc.le (ballConst_decay_nonneg hpos)
  exact max_le (Real.iSup_le (crossRow_final_le hd hk hv0 ha1 ha2 c hr) h0)
    (Real.iSup_le (crossCol_final_le hd hk hv0 ha1 ha2 c hr) h0)

/-- **Bound of `S_∂` with a separation `M`** between different cells (an extra hypothesis, not
implied by the geometry of adjacent cells): for `0 < σ < δ₀ - r`,
`S_∂(r) ≤ c₀ ballConst d σ exp(-(δ₀ - r - σ) M)`. -/
theorem finalCutBoundary_le_sep (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (c : L1Torus d N₀ → κ) {r σ M : ℝ} (hσ : 0 < σ)
    (hσr : σ < blockDecayRate d - r)
    (hsep : ∀ x y, c x ≠ c y → M ≤ dist x y) :
    finalCutBoundary c (finalOp d L N₀ k v a) r ≤
      finalDecayC d L * ballConst d σ * Real.exp (-(blockDecayRate d - r - σ) * M) := by
  have hc := finalDecayC_pos (L := L) hd
  have hq : 0 < blockDecayRate d - r - σ := by linarith
  have key : ∀ x y, c x ≠ c y → ‖finalOp d L N₀ k v a x y‖ * Real.exp (r * dist x y) ≤
      finalDecayC d L * Real.exp (-σ * dist x y) *
        Real.exp (-(blockDecayRate d - r - σ) * M) := by
    intro x y h
    have e : Real.exp (-blockDecayRate d * dist x y) * Real.exp (r * dist x y) =
        Real.exp (-σ * dist x y) * Real.exp (-(blockDecayRate d - r - σ) * dist x y) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h1 : Real.exp (-(blockDecayRate d - r - σ) * dist x y) ≤
        Real.exp (-(blockDecayRate d - r - σ) * M) :=
      Real.exp_le_exp.2 (by nlinarith [hsep x y h])
    calc ‖finalOp d L N₀ k v a x y‖ * Real.exp (r * dist x y)
        ≤ finalDecayC d L * Real.exp (-blockDecayRate d * dist x y) * Real.exp (r * dist x y) :=
          mul_le_mul_of_nonneg_right (finalMass_entry_decay hd hk hv0 ha1 ha2 x y)
            (Real.exp_pos _).le
      _ = finalDecayC d L * (Real.exp (-σ * dist x y) *
            Real.exp (-(blockDecayRate d - r - σ) * dist x y)) := by rw [mul_assoc, e]
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left h1 (by positivity) |>.trans_eq (by ring)
  have hB : 0 ≤ finalDecayC d L * ballConst d σ * Real.exp (-(blockDecayRate d - r - σ) * M) :=
    mul_nonneg (mul_nonneg hc.le (ballConst_decay_nonneg hσ)) (Real.exp_pos _).le
  refine max_le (Real.iSup_le (fun x => ?_) hB) (Real.iSup_le (fun y => ?_) hB)
  · calc crossRow c (finalOp d L N₀ k v a) r x
        ≤ ∑ y, finalDecayC d L * Real.exp (-σ * dist x y) *
            Real.exp (-(blockDecayRate d - r - σ) * M) := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases h : c x = c y
          · simp only [h, ite_true]; positivity
          · simp only [h, ite_false]; exact key x y h
      _ = finalDecayC d L * (∑ y, Real.exp (-σ * dist x y)) *
            Real.exp (-(blockDecayRate d - r - σ) * M) := by
          rw [← Finset.sum_mul, Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (ballSum_L1Torus (d := d) (m := N₀) hσ x) hc.le
  · calc crossCol c (finalOp d L N₀ k v a) r y
        ≤ ∑ x, finalDecayC d L * Real.exp (-σ * dist y x) *
            Real.exp (-(blockDecayRate d - r - σ) * M) := by
          refine Finset.sum_le_sum fun x _ => ?_
          by_cases h : c x = c y
          · simp only [h, ite_true]; positivity
          · simp only [h, ite_false]; rw [dist_comm y x]; exact key x y h
      _ = finalDecayC d L * (∑ x, Real.exp (-σ * dist y x)) *
            Real.exp (-(blockDecayRate d - r - σ) * M) := by
          rw [← Finset.sum_mul, Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left (ballSum_L1Torus (d := d) (m := N₀) hσ y) hc.le

/-- **`finalCutWeightedBound`**: for `‖s_P‖ ≤ ρ`, `WSmall r η (U_s - U)` with
`η = (ρ² + 1) S_∂(r)`. -/
theorem finalCutWeightedBound (c : L1Torus d N₀ → κ) {s : κ → ℂ} {ρ : ℝ}
    (hs : ∀ P, ‖s P‖ ≤ ρ) (v a r : ℝ) :
    WSmall r ((ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
      (finalOpCutC (d := d) (L := L) (k := k) c s v a - finalOp d L N₀ k v a) :=
  wSmall_cutMatC_sub c hs _ r

/-- The same with the true explicit bound: `η ≤ (ρ² + 1) c₀ ballConst d (δ₀ - r)`. -/
theorem finalCutWeightedBound_explicit (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (c : L1Torus d N₀ → κ) {s : κ → ℂ} {ρ r : ℝ}
    (hs : ∀ P, ‖s P‖ ≤ ρ) (hr : r < blockDecayRate d) :
    WSmall r ((ρ ^ 2 + 1) * (finalDecayC d L * ballConst d (blockDecayRate d - r)))
      (finalOpCutC (d := d) (L := L) (k := k) c s v a - finalOp d L N₀ k v a) := by
  have h := finalCutWeightedBound (d := d) (L := L) (k := k) c hs v a r
  have hb := finalCutBoundary_le (L := L) (k := k) hd hk hv0 ha1 ha2 c hr
  have hρ : 0 ≤ ρ ^ 2 + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hb hρ
  exact ⟨fun x => (h.1 x).trans hm, fun y => (h.2 y).trans hm⟩

/-! ### Resolvent, inverse and square root under `η < g_*` -/

variable {v a : ℝ}

theorem finalOp_add_cutMatC_sub (c : L1Torus d N₀ → κ) (s : κ → ℂ) :
    finalOp d L N₀ k v a + (finalOpCutC (d := d) (L := L) (k := k) c s v a -
      finalOp d L N₀ k v a) = finalOpCutC (d := d) (L := L) (k := k) c s v a :=
  add_sub_cancel _ _

/-- **Gap** of `U_s` under `η < g_*`. -/
theorem finalCutComplex_isCoercive (hd : 0 < d) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha : 1 / 2 ≤ a)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) (c : L1Torus d N₀ → κ) {s : κ → ℂ} {ρ r : ℝ}
    (hs : ∀ P, ‖s P‖ ≤ ρ) (hr : 0 ≤ r) :
    IsCoercive (finalOpCutC (d := d) (L := L) (k := k) c s v a)
      (finalGap d L - (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r) := by
  have := (finalMass_isCoercive (k := k) hd hv0 hv1 ha hmass).add_wSmall hr
    (finalCutWeightedBound (d := d) (L := L) (k := k) c hs v a r)
  rwa [finalOp_add_cutMatC_sub] at this

/-- **`finalCutComplexResolvent`**: under `η < g_*` with `η = (ρ² + 1) S_∂(r)`, `U_s + t` is
invertible for `t ≥ 0` and its inverse has entries at most
`2/((g_* - η) + t) exp(-r' dist)`, uniformly on the closed polydisc `‖s_P‖ ≤ ρ`. -/
theorem finalCutComplex_resolvent_decay (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (c : L1Torus d N₀ → κ) {s : κ → ℂ} {ρ r : ℝ} (hs : ∀ P, ‖s P‖ ≤ ρ) (hr : 0 < r)
    (hη : (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r < finalGap d L) {t : ℝ}
    (ht : 0 ≤ t) :
    IsUnit (finalOpCutC (d := d) (L := L) (k := k) c s v a + (t : ℂ) •
        (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)) ∧
      ∀ x y : L1Torus d N₀,
        ‖(finalOpCutC (d := d) (L := L) (k := k) c s v a + (t : ℂ) •
            (1 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ))⁻¹ x y‖ ≤
          2 / ((finalGap d L - (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r) + t) *
            Real.exp (-ctRate (finalDecayC d L +
                (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
              (min (blockDecayRate d) r)
              (finalGap d L - (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
              (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) := by
  have hη0 : 0 ≤ (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r := by
    obtain ⟨x⟩ : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩
    have h := (finalCutWeightedBound (d := d) (L := L) (k := k) c hs v a r).1 x
    exact (Finset.sum_nonneg fun y _ => by positivity).trans h
  have := finalPert_resolvent_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr
    hη0 hη (finalCutWeightedBound (d := d) (L := L) (k := k) c hs v a r) ht
  rwa [finalOp_add_cutMatC_sub] at this

/-- Inverse decay of `U_s` (the case `t = 0`). -/
theorem finalCutComplex_inverse_decay (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (c : L1Torus d N₀ → κ) {s : κ → ℂ} {ρ r : ℝ} (hs : ∀ P, ‖s P‖ ≤ ρ) (hr : 0 < r)
    (hη : (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r < finalGap d L)
    (x y : L1Torus d N₀) :
    ‖(finalOpCutC (d := d) (L := L) (k := k) c s v a)⁻¹ x y‖ ≤
      2 / (finalGap d L - (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r) *
        Real.exp (-ctRate (finalDecayC d L +
            (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
          (min (blockDecayRate d) r)
          (finalGap d L - (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
          (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) := by
  have h := (finalCutComplex_resolvent_decay (L := L) (k := k) hd hk hv0 hv1 ha1 ha2 hmass c hs
    hr hη (le_refl (0 : ℝ))).2 x y
  simpa using h

/-- Square-root decay of `U_s`. -/
theorem finalCutComplex_sqrt_decay (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (c : L1Torus d N₀ → κ) {s : κ → ℂ} {ρ r : ℝ} (hs : ∀ P, ‖s P‖ ≤ ρ) (hr : 0 < r)
    (hη : (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r < finalGap d L)
    (x y : L1Torus d N₀) :
    ‖Localization.sqrtMat (finalOpCutC (d := d) (L := L) (k := k) c s v a) x y‖ ≤
      2 / Real.sqrt (finalGap d L -
          (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r) *
        Real.exp (-ctRate (finalDecayC d L +
            (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
          (min (blockDecayRate d) r)
          (finalGap d L - (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r)
          (ballConst d (min (blockDecayRate d) r / 4)) * dist x y) := by
  have hη0 : 0 ≤ (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r := by
    obtain ⟨x⟩ : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩
    have h := (finalCutWeightedBound (d := d) (L := L) (k := k) c hs v a r).1 x
    exact (Finset.sum_nonneg fun y _ => by positivity).trans h
  have := finalPert_sqrt_decay (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr
    hη0 hη (finalCutWeightedBound (d := d) (L := L) (k := k) c hs v a r) x y
  rwa [finalOp_add_cutMatC_sub] at this

/-- Analyticity of the entries of `U_s⁻¹` on the open polydisc `‖s_P‖ < ρ`. -/
theorem finalCutComplex_inverse_analytic [Fintype κ] (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (c : L1Torus d N₀ → κ) {ρ r : ℝ} (hr : 0 < r)
    (hη : (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r < finalGap d L)
    (x y : L1Torus d N₀) :
    ∀ s ∈ {s : κ → ℂ | ∀ P, ‖s P‖ < ρ},
      AnalyticAt ℂ (fun w : κ → ℂ => (finalOpCutC (d := d) (L := L) (k := k) c w v a)⁻¹ x y) s := by
  intro s hs
  have hη0 : 0 ≤ (ρ ^ 2 + 1) * finalCutBoundary c (finalOp d L N₀ k v a) r := by
    obtain ⟨x⟩ : Nonempty (L1Torus d N₀) := ⟨(0 : Torus d N₀)⟩
    have h := (finalCutWeightedBound (d := d) (L := L) (k := k) c
      (s := s) (fun P => (hs P).le) v a r).1 x
    exact (Finset.sum_nonneg fun y _ => by positivity).trans h
  have := finalPert_analytic_inverse (L := L) (N₀ := N₀) (k := k) hd hk hv0 hv1 ha1 ha2 hmass hr
    hη0 hη (F := κ → ℂ) (Ω := {s : κ → ℂ | ∀ P, ‖s P‖ < ρ})
    (E := fun w => finalOpCutC (d := d) (L := L) (k := k) c w v a - finalOp d L N₀ k v a)
    (fun z _ i j => cutMatC_sub_entry_analytic c _ i j z)
    (fun z hz => finalCutWeightedBound (d := d) (L := L) (k := k) c (fun P => (hz P).le) v a r)
    x y s hs
  simpa [finalOp_add_cutMatC_sub] using this

end Final

end Balaban.Green
