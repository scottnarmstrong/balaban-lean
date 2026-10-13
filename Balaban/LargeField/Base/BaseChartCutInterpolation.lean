/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutSelection
public import Balaban.Green.FinalComplexHessian

/-!
# First bond interpolation in the physical cut chart

The chart quadratic is affine in the crossing-bond parameters. Its first
interpolation mark is the explicit sum of bond forms in BASE-KERNEL-3 (1.2).
This is the algebraic first step of P4 (2.51)–(2.54).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.LargeField.Base Balaban.Green Matrix Classical

variable {d L N₀ N : ℕ} [NeZero L] [NeZero N₀] {ϱ : ℝ}

/-- Along a complex line of bond parameters, the first-chart quadratic has
one explicit bond insertion. -/
theorem baseCutQuadratic_affine (G : GeneratingSet d L N₀ 1 ϱ)
    (aw : ℕ → ℝ) (μ : ℝ) (α : G.Ω 1 → ℂ)
    (W : G.Ω 1 × Fin N → ℂ)
    (s₀ v : FineBond d L N₀ → ℂ) (z : ℂ) :
    (1 / 2 : ℂ) * pair G W
      (liftOp N (baseHamiltonian G aw μ α (fun b => s₀ b + z * v b)) *ᵥ W) =
    (1 / 2 : ℂ) * pair G W (liftOp N (baseHamiltonian G aw μ α s₀) *ᵥ W) +
      z * ((1 / 2 : ℂ) * pair G W
        (liftOp N (∑ b ∈ baseCutBonds G, v b • baseBond G b) *ᵥ W)) := by
  rw [baseHamiltonian_affine, liftOp_add_eq, liftOp_smul_eq,
    Matrix.add_mulVec, Matrix.smul_mulVec, pair_add_right]
  change (1 / 2 : ℂ) *
      (pair G W (liftOp N (baseHamiltonian G aw μ α s₀) *ᵥ W) +
        pair G W (fun p => z *
          (liftOp N (∑ b ∈ baseCutBonds G, v b • baseBond G b) *ᵥ W) p)) = _
  rw [pair_smul_right]
  ring

/-- The exact first interpolation of an affine complex Gaussian exponent.
The inserted coefficient is the cut-bond quadratic from
`baseCutQuadratic_affine`. -/
theorem cutGaussian_first_interpolation (a mark : ℂ) :
    Complex.exp (a + mark) = Complex.exp a +
      ∫ t in (0 : ℝ)..1, mark * Complex.exp (a + (t : ℂ) * mark) := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => Complex.exp (a + (r : ℂ) * mark))
        (mark * Complex.exp (a + (t : ℂ) * mark)) t := by
    intro t _
    have hc : HasDerivAt (fun z : ℂ => Complex.exp (a + z * mark))
        (mark * Complex.exp (a + (t : ℂ) * mark)) (t : ℂ) := by
      have hinner : HasDerivAt (fun z : ℂ => a + z * mark) mark (t : ℂ) := by
        have hbase := ((hasDerivAt_id (t : ℂ)).mul_const mark).const_add a
        convert hbase using 1
        · funext z; simp only [id_eq, mul_comm]
        · ring
      have hcomp := (Complex.hasDerivAt_exp (a + (t : ℂ) * mark)).comp (t : ℂ) hinner
      convert hcomp using 1
      · funext z; rfl
      · ring
    exact hc.comp_ofReal
  have hcont : Continuous fun t : ℝ =>
      mark * Complex.exp (a + (t : ℂ) * mark) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcont.continuousOn.intervalIntegrable)
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul, add_zero] at hi
  rw [hi]
  ring

/-- The first interpolation step for the exact physical cut quadratic at a
fixed chart vector. The mark is a sum over the bonds whose parameters move
from the cut value to one. -/
theorem baseCutQuadratic_first_interpolation (G : GeneratingSet d L N₀ 1 ϱ)
    (aw : ℕ → ℝ) (μ : ℝ) (α : G.Ω 1 → ℂ)
    (W : G.Ω 1 × Fin N → ℂ) (s₀ : FineBond d L N₀ → ℂ) (a : ℂ) :
    let q : (FineBond d L N₀ → ℂ) → ℂ := fun s =>
      (1 / 2 : ℂ) * pair G W (liftOp N (baseHamiltonian G aw μ α s) *ᵥ W)
    let mark : ℂ := -((1 / 2 : ℂ) * pair G W
      (liftOp N (∑ b ∈ baseCutBonds G, (1 - s₀ b) • baseBond G b) *ᵥ W))
    Complex.exp (a - q (fun _ => 1)) =
      Complex.exp (a - q s₀) +
        ∫ t in (0 : ℝ)..1, mark * Complex.exp (a - q s₀ + (t : ℂ) * mark) := by
  dsimp only
  let v : FineBond d L N₀ → ℂ := fun b => 1 - s₀ b
  let q : (FineBond d L N₀ → ℂ) → ℂ := fun s =>
    (1 / 2 : ℂ) * pair G W (liftOp N (baseHamiltonian G aw μ α s) *ᵥ W)
  let mark : ℂ := -((1 / 2 : ℂ) * pair G W
    (liftOp N (∑ b ∈ baseCutBonds G, v b • baseBond G b) *ᵥ W))
  have hq := baseCutQuadratic_affine G aw μ α W s₀ v 1
  have hpoint : (fun b => s₀ b + (1 : ℂ) * v b) = (fun _ => 1) := by
    funext b
    dsimp [v]
    ring
  rw [hpoint, one_mul] at hq
  have hmark : q (fun _ => 1) = q s₀ - mark := by
    dsimp [q, mark]
    linear_combination hq
  change Complex.exp (a - q (fun _ => 1)) =
    Complex.exp (a - q s₀) +
      ∫ t in (0 : ℝ)..1, mark * Complex.exp (a - q s₀ + (t : ℂ) * mark)
  rw [hmark]
  have harg : a - (q s₀ - mark) = (a - q s₀) + mark := by ring
  rw [harg]
  exact cutGaussian_first_interpolation (a - q s₀) mark

end Balaban.LargeField
