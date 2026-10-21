/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfUniv

/-!
# The Gaussian integrand of the small-field factor: the exponent after the cancellation

A6-3 (a), step (P3). The integrand `sfGaussIntegrand` of the Gaussian reduction
(`Spine/FinalSfGauss.lean`) is, for every cut `Y`, the characteristic function times the exponential
of `𝒜_k + ℱ_k + ℛ^{(k)}` plus the half quadratic form `½ Q_K` of the displacement
(`sfGaussIntegrand_eq`). For the whole torus and a form `K = β_k H`, the quadratic part of
`-β_k A*_k` cancels `½ Q_K`: the exponent is `-β_k` times the cubic remainder
`V³ = A*_k - ½ ⟨v, H v⟩` of the action, plus the sources and the restricted energy
(`sfGaussIntegrand_univ_eq`).
-/

@[expose] public section

open MeasureTheory Matrix Balaban Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- **The Gaussian integrand over a cut `Y`**: `χ_k(Y) exp(𝒜_k + ℱ_k + ℛ^{(k)} + ½ Q_K(v))`
at the displacement `v = K^{-1/2} w` from the centre. -/
theorem sfGaussIntegrand_eq (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (Kq : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (w : BlockAt S n M K k × Fin N → ℝ) :
    sfGaussIntegrand C vc Y hv g Kq ψ0 w =
      ((C.chiY Y ((spinField (BlockAt S n M K k) N).symm
          (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv : ℝ) : ℂ) *
        Complex.exp (Ares2 C vc Y ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv +
          C.Fres Y ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv g +
          C.Rres Y ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv g +
          (((1 / 2) * pdQuad Kq (matAct (pdSqrtInv Kq) w) : ℝ) : ℂ)) := by
  unfold sfGaussIntegrand sfGaussIntegrandL sfFactor2
  rw [mul_assoc, Complex.ofReal_exp (1 / 2 * pdQuad Kq (matAct (pdSqrtInv Kq) w)), ← Complex.exp_add]

/-- **The cancellation of the quadratic part** (`Y` arbitrary, `K = β_k H`): the Gaussian
integrand is the characteristic function times the exponential of `-β_k V³ + ℰ_k - E_k |Y|_k + ℱ_k
+ ℛ^{(k)}`, with the cubic remainder `V³(ψ) = A*_k(Y; ψ) - ½ ⟨v, H v⟩`, `v = K^{-1/2} w`. -/
theorem sfGaussIntegrand_cubic (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (Y : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (Kq Hm : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    (hK : ∀ v, pdQuad Kq v = betaCanon S.d S.L (C.sf.β k) k 0 * (v ⬝ᵥ (Hm *ᵥ v)))
    (ψ0 : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (w : BlockAt S n M K k × Fin N → ℝ) :
    sfGaussIntegrand C vc Y hv g Kq ψ0 w =
      ((C.chiY Y ((spinField (BlockAt S n M K k) N).symm
          (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv : ℝ) : ℂ) *
        Complex.exp (-((betaCanon S.d S.L (C.sf.β k) k 0 : ℝ) : ℂ) *
            ((actStar2 C Y ((spinField (BlockAt S n M K k) N).symm
              (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv -
              (1 / 2) * ((matAct (pdSqrtInv Kq) w) ⬝ᵥ (Hm *ᵥ matAct (pdSqrtInv Kq) w)) : ℝ) : ℂ) +
          EresK2 C vc Y ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv -
          ((C.sf.E C.N₁ * volK M Y : ℝ) : ℂ) +
          C.Fres Y ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv g +
          C.Rres Y ((spinField (BlockAt S n M K k) N).symm
            (spinField (BlockAt S n M K k) N ψ0 + matAct (pdSqrtInv Kq) w)) hv g) := by
  rw [sfGaussIntegrand_eq, hK]
  unfold Ares2
  congr 2
  push_cast
  ring

end Balaban.RootFSpine
