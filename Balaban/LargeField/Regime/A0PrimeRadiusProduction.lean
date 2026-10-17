/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Regime.A0PrimeRadiusStep
public import Balaban.LargeField.Operators.KerBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Conditional P5 production at the thin source radius

The named physical input `hker` is P5 (1.26) for an actual `LFKernel`; `hbudget` is the
single-history Peierls inequality (1.30), after the decoration cost is included in its
exponent.  The first theorem yields the corresponding (1.31) integral bound for that
kernel.  The second theorem performs P5 (1.27)--(1.29)'s finite history sum using the
explicit decoration weights.  Neither theorem manufactures `hker` for a new physical
kernel; the complex source estimate needed for R-YM′ remains a separate input.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

/-- P5 (1.30) implies the (1.31) integral bound for the **actual supplied kernel**.
`hker` is the physical kernel estimate (1.26); `hbudget` is the named Peierls and
decoration budget.  The weighted size can be `|Z|_ξ` or `|Z|_η` as appropriate. -/
theorem p5_kernel_integral_of_physical_inputs
    {S : Setting} {n : ℕ → ℕ} [∀ j, NeZero (n j)] {R : ℕ → ℝ}
    {M K N : ℕ} [NeZero M] [NeZero S.L]
    (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : LFKernel (OutT N R a k) (SubCfg N a k A)
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    {κ P2 H W ell : ℝ}
    (hker : KerBound a k T κ)
    (hbudget : ell * P2 + H * W ≤ κ) :
    ∀ (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
      g ∈ l1Ball (GIdx S n M K N) → ∀ par : OutPar N R a k,
        ∫⁻ oz, ∫⁻ x, T.absW (mergeOut a k oz par) x hv g ∂(subMeasure N a k A)
          ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤
          ENNReal.ofReal (Real.exp (-(ell * P2) - H * W)) := by
  intro hv g hg par
  exact (hker hv g hg par).trans <|
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))

/-- The conditional P5 integral estimate simultaneously for a family of actual kernels
indexed by the complex source increment in the thin tube.  `hker` is precisely the
missing physical (1.26) estimate for that family.  The landed `KerBound` still has a
real `hv` argument, so this theorem supplies a uniform bound but no holomorphy claim. -/
theorem p5_kernel_integral_on_source_tube_of_physical_inputs
    {S : Setting} {n : ℕ → ℕ} [∀ j, NeZero (n j)] {R : ℕ → ℝ}
    {M K N : ℕ} [NeZero M] [NeZero S.L]
    (a : LocalHistory S n M K) (k : ℕ) {A : Set (InternalVars a k)}
    (T : (Fin N → ℂ) → LFKernel (OutT N R a k) (SubCfg N a k A)
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    {μ β c κ P2 H W ell : ℝ}
    (hker : ∀ q : Fin N → ℂ,
      (∑ i, ‖q i‖ ^ 2) ≤ c ^ 2 * μ / β → KerBound a k (T q) κ)
    (hbudget : ell * P2 + H * W ≤ κ) :
    ∀ q : Fin N → ℂ, (∑ i, ‖q i‖ ^ 2) ≤ c ^ 2 * μ / β →
      ∀ (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
        g ∈ l1Ball (GIdx S n M K N) → ∀ par : OutPar N R a k,
          ∫⁻ oz, ∫⁻ x, (T q).absW (mergeOut a k oz par) x hv g
            ∂(subMeasure N a k A) ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)) ≤
            ENNReal.ofReal (Real.exp (-(ell * P2) - H * W)) := by
  intro q hq
  exact p5_kernel_integral_of_physical_inputs a k (T q) (hker q hq) hbudget

/-- P5 (1.27)--(1.31): a finite sum of physical operator integrals keeps the same
`P2` and `H` when every decorated summand satisfies (1.30).  The function `F` is the
nonnegative value of the actual kernel integral after its measure has been fixed;
`hphysical` is the numerical content of its kernel estimate, not a bound on raw weights. -/
theorem p5_history_sum_of_physical_inputs {ι : Type*} [Fintype ι]
    (F C : ι → ℝ) {P2 H W ell : ℝ}
    (hC : ∀ i, 0 < C i)
    (hdec : (∑ i, (C i)⁻¹) ≤ 1)
    (hphysical : ∀ i, C i * F i ≤ Real.exp (-(ell * P2) - H * W)) :
    (∑ i, F i) ≤ Real.exp (-(ell * P2) - H * W) := by
  have hi : ∀ i, F i ≤ Real.exp (-(ell * P2) - H * W) * (C i)⁻¹ := by
    intro i
    apply (le_div_iff₀ (hC i)).mpr
    simpa [div_eq_mul_inv, mul_comm] using hphysical i
  calc
    (∑ i, F i) ≤ ∑ i, Real.exp (-(ell * P2) - H * W) * (C i)⁻¹ :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = Real.exp (-(ell * P2) - H * W) * ∑ i, (C i)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(ell * P2) - H * W) * 1 :=
      mul_le_mul_of_nonneg_left hdec (Real.exp_pos _).le
    _ = _ := by ring

/-- The P7 (3.8)--(3.10) exponent collection with a source-window cost.  The first two
inputs are the *physical* core and window bounds; the third is the available slack in
the printed `P2` constant.  The conclusion keeps the same `P2` and `H`. -/
theorem p7_removed_exponent_of_physical_inputs
    {Core Window P2 H W Q Lsrc : ℝ}
    (hWindow : 0 ≤ Window)
    (h38 : Core ≤ Real.exp (-(2 * P2) - H * W - Q))
    (h39 : Window ≤ Real.exp (Q + Lsrc))
    (hslack : Lsrc ≤ P2) :
    Core * Window ≤ Real.exp (-P2 - H * W) := by
  calc
    Core * Window ≤ Real.exp (-(2 * P2) - H * W - Q) * Real.exp (Q + Lsrc) :=
      mul_le_mul h38 h39 hWindow (Real.exp_nonneg _)
    _ = Real.exp (-(2 * P2) - H * W - Q + (Q + Lsrc)) :=
      (Real.exp_add _ _).symm
    _ ≤ Real.exp (-P2 - H * W) := Real.exp_le_exp.mpr (by linarith)

end Balaban.LargeField
