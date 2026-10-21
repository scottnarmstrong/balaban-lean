/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalHessianBridge

/-!
# Equal action and background masses at the final scale

Under the field clauses of Def-7 (ruling R2) the background mass and the action mass of scale `k`
are both `ν_k L^{-2k}` (`FieldClauses.muBg_eq`, `FieldClauses.muAct_eq`), so the hypothesis
`sfActMass2 cs k = cs.muBg k` of `actStar2_univ_hessian` holds: `actStar2_univ_hessian_of_field`.
-/

@[expose] public section

open Matrix Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- The action mass of scale `k` is the background mass, under the field clauses. -/
theorem sfActMass2_eq_muBg {k0 : ℕ} {cs : OpConsts} {sf : SFData S.d S.L m₁ k N ϱ}
    {hv : EuclideanSpace ℝ (Fin N)} (h : FieldClauses S k0 k cs sf hv) :
    sfActMass2 cs k = cs.muBg k := by
  unfold sfActMass2
  rw [h.muAct_eq k le_rfl, h.muBg_eq k le_rfl]

/-- **The Hessian of `A*_k(univ; ·)` is the final Hessian under the field clauses**: the
hypothesis of equal masses of `actStar2_univ_hessian` is discharged. -/
theorem actStar2_univ_hessian_of_field {k0 : ℕ} (C : SFCtx S n R M K N k m₁ ϱ)
    (hv : EuclideanSpace ℝ (Fin N)) (h : FieldClauses S k0 k C.cs C.sf hv)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) (hd2 : 2 ≤ S.d)
    (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    Filter.Tendsto (fun t : ℝ => actStar2 C Set.univ (fun z => hv + t • u z) hv / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds ((1 / 2) * (((S.L : ℝ) ^ k) ^ (S.d - 2) *
        ((fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
            blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2) ⬝ᵥ
          (finalHessian S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (S.L ^ k)
            (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k))
            (C.cs.muBg k * ((S.L : ℝ) ^ k) ^ 2) (C.weights k) (fun i => hv i) *ᵥ
          (fun p : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ (k - k)) × Fin N =>
            blockCfgOf C.geo C.hnn le_rfl C.hkK u p.1 p.2)))))) :=
  actStar2_univ_hessian C hv H (sfActMass2_eq_muBg h) he hk hd2 u

end Balaban.RootFSpine
