/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7
public import Balaban.LargeField.R.RGasRepR4Complex

/-!
# A labelled term of the Def-7 density

P7 (1.3)–(1.6), printed pp. 495–496, splits the density term of one history
according to the outcomes `σ` of its ripe components.  On the Def-7 carrier the
unsplit internal integrand is `Def7.gWeight * Def7.integrand`.  `rhoSigma` inserts
the product of the corresponding `ROutcome.weight` factors before the internal
integration.  The finite set `ripe` is the set of indices of ripe components;
components outside it retain their unsplit kernel.  The four cutoff-value maps
are the actual values of `χ̃_k`, `χ_S`, `χ⁰`, and `χ''` at the output and internal
configuration, in that order.  This definition makes no independence claim
about the internal variables.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N k : ℕ}
  {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}

/-- The term `ρ(𝔸,σ)` of P7 (1.3)–(1.6), on the Def-7 internal-variable
carrier.  Only the components in `ripe` receive an outcome factor. -/
noncomputable def rhoSigma {ι : Type} [Fintype ι]
    (a : ι → LocalHistory S n M K) (Pk : ∀ i, OpPkg N R (a i) k)
    (car : ι → Set (Torus S.d (M * n K * S.L ^ K)))
    {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Z : Set (Torus S.d (n k))) (ripe : Finset ι) (σ : ι → ROutcome)
    (t s z w : ∀ i, OutT N R (a i) k → SubCfg N (a i) k (Pk i).A → ℝ)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) : ℂ :=
  ∫ x, gWeight a k Pk ψk hv g x *
    ((∏ i ∈ ripe,
      ROutcome.weight (t i (outOf R (a i) k ψk) (x i))
        (s i (outOf R (a i) k ψk) (x i))
        (z i (outOf R (a i) k ψk) (x i))
        (w i (outOf R (a i) k ψk) (x i)) (σ i) : ℝ) : ℂ) *
    integrand a Pk car C rep A Z ψk hv g x ∂(gMeasure a k Pk)

/-- Unfolding P7 (1.3) on the Def-7 carrier as a global operator. -/
theorem rhoSigma_eq_gOp {ι : Type} [Fintype ι]
    (a : ι → LocalHistory S n M K) (Pk : ∀ i, OpPkg N R (a i) k)
    (car : ι → Set (Torus S.d (M * n K * S.L ^ K)))
    {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (Z : Set (Torus S.d (n k))) (ripe : Finset ι) (σ : ι → ROutcome)
    (t s z w : ∀ i, OutT N R (a i) k → SubCfg N (a i) k (Pk i).A → ℝ)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    rhoSigma a Pk car C rep A Z ripe σ t s z w ψk hv g =
      gOp a k Pk ψk hv g (fun x =>
        ((∏ i ∈ ripe,
          ROutcome.weight (t i (outOf R (a i) k ψk) (x i))
            (s i (outOf R (a i) k ψk) (x i))
            (z i (outOf R (a i) k ψk) (x i))
            (w i (outOf R (a i) k ψk) (x i)) (σ i) : ℝ) : ℂ) *
          integrand a Pk car C rep A Z ψk hv g x) := by
  unfold rhoSigma gOp
  congr 1
  funext x
  ring

end Balaban.LargeField.Def7
