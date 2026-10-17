module

public import Balaban.LargeField.R.SmallFactorOne
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pointwise gains for the second and third kept outcomes

The second result applies Lemma III.5.3 (b) in its landed level-torus form. The
conversion of the multiscale action into the window action is the named input
from (2.15′). For the third outcome, Lemma III.5.3 (c) is still a source input:
the history-level small-factor theorem has not landed.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {Nspin : ℕ}

/-- The exponent arithmetic after Lemma III.5.3 (b): the composed Gaussian is
retained in the small-factor estimate. -/
theorem kept_two_exp_gain_of_action (Gwin Awin C γ : ℝ)
    (hsmall : γ ≤ Gwin + Awin + C) :
    Real.exp (-Gwin - Awin) ≤ Real.exp (C - γ) := by
  apply Real.exp_le_exp.mpr
  linarith

/-- The exponent arithmetic after Lemma III.5.3 (c), using nonnegativity of
the composed Gaussian. -/
theorem kept_three_exp_gain_of_action (Gwin Awin C γ : ℝ)
    (hG : 0 ≤ Gwin) (hsmall : γ ≤ Awin + C) :
    Real.exp (-Gwin - Awin) ≤ Real.exp (C - γ) := by
  exact kept_two_exp_gain_of_action Gwin Awin C γ (by linarith)

/-- Lemma III.5.3 (b) on the support of the second outcome, followed by
(2.15′). Here `q` is its weight, and `hconv` is the action conversion. -/
theorem kept_two_exp_gain_of_smallFactor (P : SmallFactorPar)
    (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k) (hL : 2 ≤ L)
    (hd : 2 ≤ d) (hϱ : 2 * (d : ℝ) * L ≤ ϱ) {a₁ : ℝ} (ha₁ : 0 < a₁)
    (hadm : IsAdmissibleWeights k (compWeight L a₁)) {μ : ℝ} (hμ : 0 ≤ μ)
    (h : EuclideanSpace ℝ (Fin Nspin)) {Xc Xwin : Finset (Site d L N₀ k)}
    (hXc : Xc ⊆ Xwin) (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k)
    (hXk : IsBlockUnion L N₀ k k Xc)
    (hX : ∀ n, 1 ≤ n → n ≤ k → IsBlockUnion L N₀ k n (Xc ∩ G.layer n))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin))
    (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1) {βk : ℝ} (hβ : 0 ≤ βk)
    (ϖ : ℕ → ℝ) (aN : Blk d L N₀ k k → ℝ)
    (hη0 : 0 ≤ P.eta) (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks d L N₀ k k Xc, Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks d L N₀ k k Xc).card : ℝ) ≤ Nbl)
    (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hK1 : 0 < P.K1) (hγ0 : P.gamma0 = gamma0 d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (q : ℝ) (hq : q ≠ 0 →
      ¬ PsiTildeSet {y : Blk d L N₀ k k | fib d L N₀ k k y ⊆ Xc} (ψ k)
        (δ / (6 * P.K1)))
    (Awin C : ℝ)
    (hconv : Awin + C = multiAction G (compWeight L a₁) βk μ h Xwin ψ φ)
    (hq0 : q ≠ 0) :
    Real.exp (-(composedGauss G βk aN ϖ ψ Xc) - Awin) ≤
      Real.exp (C - P.gamma2) := by
  have hsmall := smallFactor_two_gamma2 P G hk hL hd hϱ ha₁ hadm hμ h hXc hXΩ
    hXk hX ψ φ hφ hβ ϖ aN hη0 hη haN hM hSig hN hΛ19 hδ hK1 hγ0 hβδ
    (hq hq0)
  apply kept_two_exp_gain_of_action
  rw [← hconv] at hsmall
  linarith

/-- Positivity of the composed Gaussian when its quadratic coefficients are
nonnegative. -/
theorem composedGauss_nonneg_of_coeff (G : GeneratingSet d L N₀ k ϱ)
    {βk : ℝ} (hβ : 0 ≤ βk) (aN : Blk d L N₀ k k → ℝ)
    (Xc : Finset (Site d L N₀ k))
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc, 0 ≤ aN z)
    (ϖ : ℕ → ℝ)
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin)) :
    0 ≤ composedGauss G βk aN ϖ ψ Xc := by
  unfold composedGauss
  apply Finset.sum_nonneg
  intro z hz
  have haz := haN z hz
  positivity

/-- The third-outcome gain, conditional precisely on the still-unlanded
Lemma III.5.3 (c) support estimate and on (2.15′). -/
theorem kept_three_exp_gain_of_III53c (P : SmallFactorPar)
    (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {βk : ℝ} (hβ : 0 ≤ βk)
    {μ : ℝ} (h : EuclideanSpace ℝ (Fin Nspin))
    (Xc Xwin : Finset (Site d L N₀ k))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin Nspin))
    (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin Nspin))
    (aN : Blk d L N₀ k k → ℝ)
    (haN : ∀ z ∈ tBlocks d L N₀ k k Xc, 0 ≤ aN z) (ϖ : ℕ → ℝ)
    (q : ℝ) (hIII53c : q ≠ 0 → P.gamma3 ≤ multiAction G a βk μ h Xwin ψ φ)
    (Awin C : ℝ)
    (hconv : Awin + C = multiAction G a βk μ h Xwin ψ φ)
    (hq0 : q ≠ 0) :
    Real.exp (-(composedGauss G βk aN ϖ ψ Xc) - Awin) ≤
      Real.exp (C - P.gamma3) := by
  have hsmall := hIII53c hq0
  rw [← hconv] at hsmall
  exact kept_three_exp_gain_of_action _ Awin C P.gamma3
    (composedGauss_nonneg_of_coeff G hβ aN Xc haN ϖ ψ) hsmall

end Balaban.LargeField
