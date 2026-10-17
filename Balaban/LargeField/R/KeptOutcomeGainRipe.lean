module

public import Balaban.LargeField.R.HgeoDischarge
public import Balaban.LargeField.R.KeptOutcomeGain23
import Mathlib.Tactic.Linarith

/-!
# The second kept gain for a ripe history component

This applies the landed history form of Lemma III.5.3 (b), including its
proved geometric premise, to the support of the second outcome weight.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  [NeZero S.L] [NeZero S.M] {Nspin : ℕ} {ϱ : ℝ} {k : ℕ}

/-- Lemma III.5.3 (b) and (2.15′) give the exponential gain on the support
of the weight of `ϰ₂`. The composed Gaussian remains in the exponent. -/
theorem kept_two_ripe_exp_gain_of_conversion (P : SmallFactorPar)
    (H : RegionHistory S n R k0 K) (g : Geo S n R S.M)
    (hkK : k ≤ K) (Z : H.Comp k) (cs : OpConsts)
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
    (hδ : 0 < cs.delta k) (hK1 : 0 < P.K1)
    (hγ0 : P.gamma0 = gamma0 S.d)
    (hβδ : βk * (cs.delta k) ^ 2 = P.A0 ^ 2 * P.lamK ^ (2 * P.p0) / P.a)
    (hK1b : bgK1 S.d S.L Nspin ≤ P.K1) (hδ1 : cs.delta k ≤ 6 * P.K1)
    (hδc : cs.delta k ≤ 2 * P.K1 * bgC1 S.d S.L Nspin)
    (hmu : cs.mu k = 0) (Hbg : BgHyp S.d S.L k (minSep S.L g.M1) cs.aw 0)
    (ψh : BlockAt S n S.M K k → EuclideanSpace ℝ (Fin Nspin))
    (hψk : ∀ z, ψ k z = ψh
      (torusCast (histScale_eq g.hM H.F.hnn (le_refl k) hkK) z))
    (q : ℝ) (hq : q ≠ 0 →
      chiS (H.localHistory S.M K k Z) k g H.F.hnn cs h hkK
        (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψh = 0)
    (Awin C : ℝ)
    (hconv : Awin + C = multiAction G (compWeight S.L a₁) βk μ h Xwin ψ φ)
    (hq0 : q ≠ 0) :
    Real.exp (-(composedGauss G βk aN ϖ ψ Xc) - Awin) ≤
      Real.exp (C - P.gamma2) := by
  have hs := smallFactor_two_ripe P H g hkK Z cs G hk hL hd hϱ ha₁ hadm hμ h
    hXcdef hXc hXΩ hXk hX ψ φ hφ hβ ϖ aN hη0 hη haN hM hSig hN
    hΛ19 hδ hK1 hγ0 hβδ hK1b hδ1 hδc hmu Hbg ψh hψk (hq hq0)
  rw [← hconv] at hs
  exact kept_two_exp_gain_of_action _ Awin C P.gamma2 (by linarith)

end Balaban.LargeField
