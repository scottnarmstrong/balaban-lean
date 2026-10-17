/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedTau
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# `lf4R_removed`: the halo gas bound for removed components from the window bound (W946)

`notes/phase1/LF4R-PLAN.md`, item 7.  P7 (3.10′) for all ripe components, feeding `RGasCoreFinal`: the removed factor
`τ z` is the sum over localized histories `𝔞 ∈ Hs z` of integrals of the removed kernels `Tr a`; the window bound
`hwin` (`KerBound a k (Tr a) (κ^pre − C_R λ_k^{2d+1})`, what `removedKernel_kerBound_of_hid` produces) with the ripeness
`G^pre ≥ 2 A₂ λ_k^{p₂} + 1` (`hrip`) and `C_R λ^{2d+1} ≤ A₂ λ^{p₂}` (`CR_pow_le_A2_pow`) gives the kernel bound with
exponent `A₂ λ^{p₂} + H_k M^d c + 1 + log C(𝔞)` (`removed_kerBound_logC_of_window`), hence `hrem` by
`norm_tau_le_of_removed_kernels` (summability `∑ C(𝔞)⁻¹ ≤ 1`) and `p₂(β_k) ≤ A₂ λ̂_k^{p₂}`
(`p2Run_le_A2_lamHat_pow`, `λ̂_k = log(β a) + 1 + kθ ≥ log b_k`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

section Final

open Balaban.Polymer RegionHistory Balaban.Background D7Reserve Balaban.Fluctuation
  Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **`lf4R_removed`.** -/
theorem lf4R_removed
    {m₀ m₁ : ℕ}
    {Fr : FineSizeFrame S n M K m₀ m₁}
    {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : k ≤ K}
    {rep : Rep S n R k0 K M N geo cs P k} {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    (hD : D7BdryPost Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {hext : Fin N → ℂ} (hhB : hext ∈ hSetB hv)
    (p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ))
    (labY : Yt → Finset (Torus S.d (n k))) (hlabY : Function.Injective labY)
    (hlabYv : ∀ y, labY y ∈ bdryDomsPost Fr A k (Zof A))
    (hp : ∀ y, H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) k hkK
        (fineSet (S := S) (n := n) M K k (labY y : Set (Torus S.d (n k)))) aw μs ε ε1 νs hext
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    (labZ : Zt → Finset (Torus S.d (n k))) (hlabZ : Function.Injective labZ)
    {cy zs cr : _ → Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))}
    (hXY : ∀ y, d7Pull Fr k (labY y : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (cy y)))
    (hXZ : ∀ z, d7Pull Fr k (labZ z : Set (Torus S.d (n k))) =
      Yhat (d7Pull Fr k (A.H.omegaPost k)) (sitesOf (zs z)))
    (hk : 1 ≤ k) (hR : ⌊R (k - 1)⌋₊ = ⌊S.Rb * S.lam (k - 1) ^ 2⌋₊)
    (cz : Zt → A.H.Comp k) (hcz : ∀ z, (cz z).1 ∈ A.H.rem k)
    (hlabZ' : ∀ z, (labZ z : Set (Torus S.d (n k))) =
      nbhd (2 * ⌊R (k - 1)⌋₊ + 4) ((cz z).1 : Set (Torus S.d (n k))))
    {κ' p' h' : ℝ} (hfac : 0 ≤ fac) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ rate) (hp' : 0 ≤ p')
    (hκ : aEnt S.d S.L + 1 ≤ rate - κ')
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (β : Yt → ℂ) (hβ : ∀ y, β y = rep.B A (labY y) (extK p.1) (extK p.2.1) hext p.2.2)
    (G : S.Good) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j)
    {H : ℝ} (hH : 0 ≤ H) (hh' : 0 ≤ h')
    {β₀ ν₀ a₀ ε₀ : ℝ} {b nn : ℕ → ℝ} (ok : S.Ok)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β₀ a₀ j)
    (hrun : RunningHyp S.d S.L β₀ ν₀ a₀ ε₀ b nn)
    (hp'2 : p' ≤ 1 / 2 * p2Run S.A2 S.p2 b k)
    (hx0 : x0 S.d h' (2 ^ S.d * ((2 * (S.c0 : ℝ) + 18) ^ S.d +
      (2 * (S.c0 : ℝ) * S.Rb + 4 * S.Rb) ^ S.d)) S.A2 ≤ Real.log (b k))
    (hLd : 8 ≤ S.L ^ S.d) (hA2 : 0 ≤ S.A2) (hb0 : 0 ≤ Real.log (b k)) (hPb : P.beta = b)
    (hHdef : H = HRun P.H0 b k * (S.M : ℝ) ^ S.d)
    (Hs : Zt → Finset (LocalHistory S n M K))
    (hHs : ∀ z, ∀ a ∈ Hs z, a ∈ histSet S n R k0 M K k (cz z).1)
    {Aint : ∀ a : LocalHistory S n M K, Set (InternalVars a k)}
    (Tr : ∀ a : LocalHistory S n M K, LFKernel (OutT N R a k) (SubCfg N a k (Aint a))
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (Fa : Zt → ∀ a : LocalHistory S n M K, OutT N R a k → SubCfg N a k (Aint a) → ℂ)
    (hFa : ∀ z a o x, ‖Fa z a o x‖ ≤ 1)
    (gk : GIdx S n M K N → ℂ) (hgk : gk ∈ l1Ball (GIdx S n M K N))
    (parK : Zt → ∀ a : LocalHistory S n M K, OutPar N R a k)
    (hτ : ∀ z, τ z = ∑ a ∈ Hs z, ∫ oz, ∫ x, (Tr a).w (mergeOut a k oz (parK z a)) x hv gk *
        Fa z a (mergeOut a k oz (parK z a)) x ∂(subMeasure N a k (Aint a))
        ∂(outPartMeasure N (Vblk R a k) (ZBlk a k)))
    (κpre : Zt → LocalHistory S n M K → ℝ) (hp2 : 2 * S.d + 1 ≤ S.p2) (hlk : 0 ≤ S.lam k)
    (hCR0 : S.CR ≤ S.A2 * S.lam k ^ (S.p2 - (2 * S.d + 1)))
    (hrip : ∀ z, ∀ a ∈ Hs z, 2 * S.A2 * S.lam k ^ S.p2 + 1 ≤
      P.budgetG S k (κpre z a) (a.logC k) (cz z).1.card)
    (hwin : ∀ z, ∀ a ∈ Hs z, KerBound a k (Tr a) (κpre z a - S.CR * S.lam k ^ (2 * S.d + 1)))
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ k
      (d7Pull Fr k (A.H.omegaPost k)))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) := by
  refine gas_activity_bound_physical_of_D7BdryPost_halo_of_removed_factor_run_of_kernel hD hA hhB p labY
    hlabY hlabYv hp labZ hlabZ hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ'' hp' hκ hz hcr β hβ G hT hH hh'
    ok hlam hrun hp'2 hx0 hLd hA2 hb0 hPb hHdef Hs hHs Tr Fa hFa gk hgk parK hτ ?_ hh X
  intro z a ha
  exact removed_kerBound_logC_of_window (P := P) (c := (cz z).1.card) rfl (hrip z a ha)
    (CR_pow_le_A2_pow hlk hp2 hCR0) (hwin z a ha)

end Final

end Balaban.LargeField
