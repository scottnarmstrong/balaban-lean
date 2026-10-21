/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalHessianBridge
public import Balaban.Green.GaussianMgf

/-!
# The linear part of the source term and its Gaussian average

A6-3 (b), linear part. At the constant configuration the linear response of the background field
to a block displacement `u` is `φ̇ = R u` with the real matrix
`R = (a_k/L^{2k}) · Hr⁻¹ (1 − P_e) Q*` (`response_top`). The linear part of `⟨g, φ̄_k − h⟩` in the
Gaussian variable `v = K^{-1/2} w` is therefore `⟨Rᵀ g, v⟩`, and its Gaussian average is
`exp(½ ⟨Rᵀ g, K⁻¹ Rᵀ g⟩)` (`gauss_source_linear`): a quadratic form in `g`, the scale-`(k+1)`
term `ℳ^{(k+1)}_0` of the source.
-/

@[expose] public section

open MeasureTheory Matrix Balaban Balaban.Green Balaban.LargeField Balaban.Multiscale Balaban.Background Complex

namespace Balaban.RootFSpine

section Gauss

variable {X ι : Type*} [Fintype X] [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The Gaussian average of a linear source**: for a real response matrix `Rm`, a complex source
`g` and `K` positive definite,
`∫ exp(∑_p g_p (Rm · K^{-1/2} w)_p) dγ(w) = exp(½ ∑_{q,q'} J_q K⁻¹(q,q') J_{q'})`,
`J_q = ∑_p g_p Rm(p, q)`. -/
theorem gauss_source_linear {K : Matrix ι ι ℝ} (hK : K.PosDef) (Rm : Matrix X ι ℝ)
    (g : X → ℂ) :
    ∫ w : ι → ℝ, cexp (∑ p, g p * ((Rm *ᵥ matAct (pdSqrtInv K) w) p : ℝ)) ∂(pdGaussian ι ℝ) =
      cexp ((1 / 2 : ℂ) * ∑ q, ∑ q', (∑ p, g p * (Rm p q : ℝ)) * ((K⁻¹ q q' : ℝ) : ℂ) *
        (∑ p, g p * (Rm p q' : ℝ))) := by
  have h := pdGaussian_integral_exp_lin_sqrtInv hK (fun q => ∑ p, g p * ((Rm p q : ℝ) : ℂ))
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => by ring

end Gauss

section Response

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν : ℝ}

/-- The pull-back of a block field, lifted to spins, is the block lift. -/
theorem pullback_mulVec (Uv : Torus d (N₀ * L ^ (k - k)) × Fin N → ℝ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) :
    (spinLift N (blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k))) *ᵥ Uv) (x, i) =
      Uv (blockMap (L ^ k) (N₀ * L ^ (k - k)) x, i) := by
  simp only [spinLift, blockPullbackMatrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp [ite_mul, Finset.sum_ite_eq]

/-- The real response matrix of the background field at the constant configuration (top layer):
`R = (a_k/L^{2k}) Hr⁻¹ (1 − P_e) Q*`, from the block field `U` to the fine field. -/
noncomputable def responseMat (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (e : Fin N → ℝ) :
    Matrix (Torus d (N₀ * L ^ k) × Fin N) (Torus d (N₀ * L ^ (k - k)) × Fin N) ℝ :=
  (a k / ((L : ℝ) ^ k) ^ 2) • (spinLift N (fullMatrix G a ν)⁻¹ *
    (1 - projH (ι := Torus d (N₀ * L ^ k)) e) *
    spinLift N (blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k))))

/-- **The linear response is the response matrix** (top layer, constant configuration). -/
theorem response_top_mat (H : BgHyp d L k ϱ a ν)
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (hd2 : 2 ≤ d)
    {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) (E : BgData G N) (hmem : ∀ x, x ∈ G.Ω 1)
    (Uv : Torus d (N₀ * L ^ (k - k)) × Fin N → ℝ)
    (hEΨ : ∀ x i, E.Ψ x i = ((Uv (blockMap (L ^ k) (N₀ * L ^ (k - k)) x, i) : ℝ) : ℂ))
    (hEh : ∀ x, E.h x = 0) :
    (liftOp N (dirichletOperator G a ν 0)⁻¹ -
        constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E =
      cplxLift hmem (responseMat G a ν e *ᵥ Uv) := by
  have h := response_top H hΩ hk hd2 he E hmem
    (spinLift N (blockPullbackMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k))) *ᵥ Uv)
    (fun x i => by rw [hEΨ, pullback_mulVec]) hEh
  rw [h]
  congr 1
  unfold responseMat
  simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Response

end Balaban.RootFSpine
