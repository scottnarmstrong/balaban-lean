/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormMomentSum
public import Balaban.Flow.MomentAlgebra

/-!
# The limit of the moment sum of the second variation of `C₁`

Along tori `(ZMod (N₀ L^K))^d` with `N₀ → ∞` carrying whole-lattice levels `n`, the moment sum
`∑_b |b|² B(1_b, 1_0)` of the second variation of `C₁` (`BsV`) tends to
`secondVarScalar w ν ξ₂ ξ₃ ζ 0 (d M^d cellAvg Φ₀) (d M^d cellAvg Ψ₀)`, `M = L^n`
(`momBs_tendsto`), and this limit equals the third row of `matrixInfty` times `-4 d M^{d-2}`
plus the explicit product term `ξ₃ ζ w² (w z - 2 y)` (`momBs_limit_eq`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Flow Finset Matrix Filter Topology

variable {d L K n : ℕ} [NeZero L] {ϱ : ℝ}

theorem momBs_tendsto {Ns : ℕ → ℕ} [hne : ∀ j, NeZero (Ns j)]
    [hne' : ∀ j, NeZero (Ns j * L ^ (K - n))] (hNs : Tendsto Ns atTop atTop)
    (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 < ν) (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2)
    (ha : IsAdmissibleWeights K a) (Gs : ∀ j, GeneratingSet d L (Ns j) K ϱ)
    (hGs : ∀ j, IsLevel (Gs j) n)
    (hUs : ∀ j, IsUnit (dirichletOperator (Gs j) a ν (0 : (Gs j).Ω 1 → ℂ))) (ξ₂ ξ₃ ζ : ℝ) :
    Tendsto (fun j => ∑ b : Torus d (Ns j * L ^ (K - n)), liftSqB b *
        BsV (wLevel L a n) ν ξ₂ ξ₃ ζ (greenD (Gs j) a ν 0)
          (indB (Gs j) (L ^ n) (Ns j * L ^ (K - n)) b) (indB (Gs j) (L ^ n) (Ns j * L ^ (K - n)) 0))
      atTop (𝓝 (secondVarScalar (wLevel L a n) ν ξ₂ ξ₃ ζ 0
        ((d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d *
          cellAvg (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))
        ((d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d *
          cellAvg (psiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)))) := by
  have h1 := moment_R1_tendsto hNs hd hν hw ha Gs hGs hUs
  have h2 := moment_R2_tendsto hNs hd hν hw ha Gs hGs hUs
  set w := wLevel L a n
  have hfun : (fun j => ∑ b : Torus d (Ns j * L ^ (K - n)), liftSqB b *
        BsV (wLevel L a n) ν ξ₂ ξ₃ ζ (greenD (Gs j) a ν 0)
          (indB (Gs j) (L ^ n) (Ns j * L ^ (K - n)) b) (indB (Gs j) (L ^ n) (Ns j * L ^ (K - n)) 0)) =
      fun j => secondVarScalar w ν ξ₂ ξ₃ ζ 0
        (blockInd (Gs j) (L ^ n) (Ns j * L ^ (K - n)) ⬝ᵥ
          (greenD (Gs j) a ν 0 *ᵥ (fun y : (Gs j).Ω 1 => liftSum (d := d)
            (fun s : ZMod (Ns j * L ^ K) => ((sb (L ^ n) (Ns j * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (Ns j * L ^ K)))))
        (blockInd (Gs j) (L ^ n) (Ns j * L ^ (K - n)) ⬝ᵥ
          (greenD (Gs j) a ν 0 *ᵥ (greenD (Gs j) a ν 0 *ᵥ (fun y : (Gs j).Ω 1 => liftSum (d := d)
            (fun s : ZMod (Ns j * L ^ K) => ((sb (L ^ n) (Ns j * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (Ns j * L ^ K)))))) :=
    funext fun j => momentBs_eq (G := Gs j) (n := n) a ν ξ₂ ξ₃ ζ
  rw [hfun]
  simp only [secondVarScalar_linear]
  have := ((tendsto_const_nhds (x := (((ξ₃ : ℂ) * w + (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * (2 * w) +
      (ζ : ℂ) ^ 2 * w)) * 0))).add
    (h1.const_mul (-(ξ₃ : ℂ) * w ^ 2 - (1 + (ξ₃ : ℂ)) * (ζ : ℂ) * (2 * w ^ 2)))).add
    (h2.const_mul (-(ξ₃ : ℂ) * ν * w ^ 2 + (1 + (ξ₃ : ℂ)) * (ζ : ℂ) * w ^ 3 +
      ((ν * ξ₂ : ℝ) : ℂ) * w ^ 2))
  exact this

end Balaban.Fluctuation
