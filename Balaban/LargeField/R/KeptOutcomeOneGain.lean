module

public import Balaban.LargeField.R.HgeoDischarge
public import Balaban.LargeField.R.KeptOutcomeOneHalfGauss
import Mathlib.Tactic.Linarith

/-!
# The first kept gain on a ripe component

Lemma III.5.3 (a) uses half of the composed Gaussian to pay for the
violation of the tilde window. The other half remains for Gaussian
integration.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  [NeZero S.L] [NeZero S.M] {Nspin : ℕ} {ϱ : ℝ} {k : ℕ}

/-- Exponent arithmetic retaining half the Gaussian for the node integral. -/
theorem kept_one_half_exp_gain_of_action (Gwin Awin C γ : ℝ)
    (hsmall : γ ≤ Gwin / 2 + Awin + C) :
    Real.exp (-Gwin - Awin) ≤
      Real.exp (C - γ) * Real.exp (-Gwin / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The nonzero `ϰ₁` outcome weight lies off the tilde window. Applying
`smallFactor_one_ripe` and (2.15′) leaves half the Gaussian in the estimate. -/
theorem kept_one_ripe_half_exp_gain_of_conversion (P : SmallFactorPar)
    (H : RegionHistory S n R k0 K) (g : Geo S n R S.M)
    (hkK : k ≤ K) (Z : H.Comp k)
    (G : GeneratingSet S.d S.L (g.M1 * (g.c * n k)) k ϱ) (hk : 1 ≤ k)
    (hL : 2 ≤ S.L) (hd : 2 ≤ S.d) (hϱ : 2 * (S.d : ℝ) * S.L ≤ ϱ)
    {a₁ : ℝ} (ha₁ : 0 < a₁) (hadm : IsAdmissibleWeights k (compWeight S.L a₁))
    {μ : ℝ} (hμ : 0 ≤ μ) (h : EuclideanSpace ℝ (Fin Nspin))
    {Xc Xwin : Finset (Site S.d S.L (g.M1 * (g.c * n k)) k)}
    (hXcdef : ∀ x, x ∈ Xc ↔
      torusCast (histFine_eq g H.F.hnn hkK) x ∈
        fineSet (S := S) (n := n) S.M K k (Z.1 : Set _) ∧
      torusCast (histFine_eq g H.F.hnn hkK) x ∉ H.fineZzero k Z)
    (hXc : Xc ⊆ Xwin)
    (hXΩ : ∀ s ∈ Xc, s ∈ G.Ω 1 ∧ s ∉ G.Ω k)
    (hXk : IsBlockUnion S.L (g.M1 * (g.c * n k)) k k Xc)
    (hX : ∀ m, 1 ≤ m → m ≤ k →
      IsBlockUnion S.L (g.M1 * (g.c * n k)) k m (Xc ∩ G.layer m))
    (ψ : (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n k)) k m →
      EuclideanSpace ℝ (Fin Nspin))
    (φ : Site S.d S.L (g.M1 * (g.c * n k)) k → EuclideanSpace ℝ (Fin Nspin))
    (hφ : ∀ x ∈ Xc, ‖φ x‖ = 1) {βk : ℝ} (hβ : 0 ≤ βk)
    (ϖ : ℕ → ℝ) (aN : Blk S.d S.L (g.M1 * (g.c * n k)) k k → ℝ)
    (hη0 : 0 ≤ P.eta) (hη : P.eta ≤ 1 / 2)
    (haN : ∀ z ∈ tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc,
      |aN z - compWeightZ G a₁ z| ≤ P.eta * compWeightZ G a₁ z)
    {Mψ Sig Nbl : ℝ} (hM : ∀ s ∈ Xc, ‖leafField G ψ s‖ ≤ Mψ)
    (hSig : ∀ z ∈ tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc,
      Real.sqrt βk * varsigmaBar G ϖ z ≤ Sig)
    (hN : ((tBlocks S.d S.L (g.M1 * (g.c * n k)) k k Xc).card : ℝ) ≤ Nbl)
    (hΛ19 : 8 * Sig ^ 2 * Nbl * Mψ ^ 2 ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hγ0 : P.gamma0 = gamma0 S.d)
    (hβδ : βk * δ ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (ψh : BlockAt S n S.M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh
      (torusCast (histScale_eq g.hM H.F.hnn (le_refl k) hkK) z))
    (Awin C : ℝ)
    (hconv : Awin + C = multiAction G (compWeight S.L a₁) βk μ h Xwin ψ φ)
    (hq0 : Outcome.weight
      (chiTilde (H.localHistory S.M K k Z) k (H.fineZzero k Z) δ ψh)
      0 0 0 0 Outcome.kappa1 ≠ 0) :
    Real.exp (-(composedGauss G βk aN ϖ ψ Xc) - Awin) ≤
      Real.exp (C - P.gamma1) *
        Real.exp (-(composedGauss G βk aN ϖ ψ Xc) / 2) := by
  have hnot := kept_one_weight_support (H.localHistory S.M K k Z) k
    (H.fineZzero k Z) δ ψh hq0
  have hchi : chiTilde (H.localHistory S.M K k Z) k
      (H.fineZzero k Z) δ ψh = 0 := charFn_eq_zero hnot
  have hs := smallFactor_one_ripe P H g hkK Z G hk hL hd hϱ ha₁ hadm hμ h
    hXcdef hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0 hη haN hM hSig hN
    hΛ19 hδ hγ0 hβδ ψh hψk hchi
  rw [← hconv] at hs
  exact kept_one_half_exp_gain_of_action _ Awin C P.gamma1 (by linarith)

end Balaban.LargeField
