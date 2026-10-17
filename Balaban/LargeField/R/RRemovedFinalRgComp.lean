/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedFinal
public import Balaban.LargeField.R.RRemovedFinalRg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# `lf4R_removed` with `hrip` discharged from the flow's counter (W948)

`notes/phase1/LF4R-PLAN.md`, item 7.  `lf4R_removed_of_flow`: `hrip` of `lf4R_removed` is replaced by the witnesses
`hwit` (for each localized history `a` of the removed component, a region history `H` with `a = H.localHistory …`, the
component ripe, `κpre` its `kappaPre`, and the kept-data inequality `hκ` = the kept outcome bound III.8.9 (a)) and the
flow hypotheses (`F.Matches S`, `hΛ12`, `hgen`): `hrip_of_flow'` (counter conclusion from `flow_counter`, Lemma B).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

section Final

open Balaban.Polymer RegionHistory Balaban.Background D7Reserve Balaban.Fluctuation
  Balaban.Localization Balaban.Multiscale Balaban.LargeField.Def7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] [NeZero S.M] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {j : ℕ}
  {Yt Zt : Type*} [Fintype Yt] [Fintype Zt] {τ : Zt → ℂ}

open Classical in
/-- **`lf4R_removed` with `hrip` discharged from the counter of the flow's region histories.** -/
theorem lf4R_removed_of_flow
    {m₀ m₁ : ℕ}
    {Fr : FineSizeFrame S n M K m₀ m₁}
    {hnn : ∀ i, i < K → n i = S.L * n (i + 1)} {hkK : (j + 1) ≤ K}
    {rep : Rep S n R k0 K M N geo cs P (j + 1)} {Zof : LabHist S n R k0 K → Set (Torus S.d (n (j + 1)))}
    {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ} {hv : EuclideanSpace ℝ (Fin N)}
    (hD : D7BdryPost Fr hnn hkK rep Zof aw μs ε ε1 νs fac rate hv) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {hext : Fin N → ℂ} (hhB : hext ∈ hSetB hv)
    (p : FinFieldC S n M K N × FinFieldC S n M K N × (GIdx S n M K N → ℂ))
    (labY : Yt → Finset (Torus S.d (n (j + 1)))) (hlabY : Function.Injective labY)
    (hlabYv : ∀ y, labY y ∈ bdryDomsPost Fr A (j + 1) (Zof A))
    (hp : ∀ y, H7Domain geo.M1 geo.c geo.hM hnn (globalLH A.H M) (j + 1) hkK
        (fineSet (S := S) (n := n) M K (j + 1) (labY y : Set (Torus S.d (n (j + 1))))) aw μs ε ε1 νs hext
        (extK p.1) (extK p.2.1) (fun x i => p.2.2 (x, i)))
    (labZ : Zt → Finset (Torus S.d (n (j + 1)))) (hlabZ : Function.Injective labZ)
    {cy zs cr : _ → Finset (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (j + 1)
      (d7Pull Fr (j + 1) (A.H.omegaPost (j + 1))))}
    (hXY : ∀ y, d7Pull Fr (j + 1) (labY y : Set (Torus S.d (n (j + 1)))) =
      Yhat (d7Pull Fr (j + 1) (A.H.omegaPost (j + 1))) (sitesOf (cy y)))
    (hXZ : ∀ z, d7Pull Fr (j + 1) (labZ z : Set (Torus S.d (n (j + 1)))) =
      Yhat (d7Pull Fr (j + 1) (A.H.omegaPost (j + 1))) (sitesOf (zs z)))
    (hk : 1 ≤ (j + 1)) (hR : ⌊R ((j + 1) - 1)⌋₊ = ⌊S.Rb * S.lam ((j + 1) - 1) ^ 2⌋₊)
    (cz : Zt → A.H.Comp (j + 1)) (hcz : ∀ z, (cz z).1 ∈ A.H.rem (j + 1))
    (hlabZ' : ∀ z, (labZ z : Set (Torus S.d (n (j + 1)))) =
      nbhd (2 * ⌊R ((j + 1) - 1)⌋₊ + 4) ((cz z).1 : Set (Torus S.d (n (j + 1)))))
    {κ' p' h' : ℝ} (hfac : 0 ≤ fac) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ rate) (hp' : 0 ≤ p')
    (hκ : aEnt S.d S.L + 1 ≤ rate - κ')
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (β : Yt → ℂ) (hβ : ∀ y, β y = rep.B A (labY y) (extK p.1) (extK p.2.1) hext p.2.2)
    (G : S.Good) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j)
    {H : ℝ} (hH : 0 ≤ H) (hh' : 0 ≤ h')
    {β₀ ν₀ a₀ ε₀ : ℝ} {b nn : ℕ → ℝ} (ok : S.Ok)
    (hlam : ∀ j, S.lam j = lamHat S.d S.L β₀ a₀ j)
    (hrun : RunningHyp S.d S.L β₀ ν₀ a₀ ε₀ b nn)
    (hp'2 : p' ≤ 1 / 2 * p2Run S.A2 S.p2 b (j + 1))
    (hx0 : x0 S.d h' (2 ^ S.d * ((2 * (S.c0 : ℝ) + 18) ^ S.d +
      (2 * (S.c0 : ℝ) * S.Rb + 4 * S.Rb) ^ S.d)) S.A2 ≤ Real.log (b (j + 1)))
    (hLd : 8 ≤ S.L ^ S.d) (hA2 : 0 ≤ S.A2) (hb0 : 0 ≤ Real.log (b (j + 1))) (hPb : P.beta = b)
    (hHdef : H = HRun P.H0 b (j + 1) * (S.M : ℝ) ^ S.d)
    (Hs : Zt → Finset (LocalHistory S n M K))
    (hHs : ∀ z, ∀ a ∈ Hs z, a ∈ histSet S n R k0 M K (j + 1) (cz z).1)
    {Aint : ∀ a : LocalHistory S n M K, Set (InternalVars a (j + 1))}
    (Tr : ∀ a : LocalHistory S n M K, LFKernel (OutT N R a (j + 1)) (SubCfg N a (j + 1) (Aint a))
      (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N))
    (Fa : Zt → ∀ a : LocalHistory S n M K, OutT N R a (j + 1) → SubCfg N a (j + 1) (Aint a) → ℂ)
    (hFa : ∀ z a o x, ‖Fa z a o x‖ ≤ 1)
    (gk : GIdx S n M K N → ℂ) (hgk : gk ∈ l1Ball (GIdx S n M K N))
    (parK : Zt → ∀ a : LocalHistory S n M K, OutPar N R a (j + 1))
    (hτ : ∀ z, τ z = ∑ a ∈ Hs z, ∫ oz, ∫ x, (Tr a).w (mergeOut a (j + 1) oz (parK z a)) x hv gk *
        Fa z a (mergeOut a (j + 1) oz (parK z a)) x ∂(subMeasure N a (j + 1) (Aint a))
        ∂(outPartMeasure N (Vblk R a (j + 1)) (ZBlk a (j + 1))))
    (κpre : Zt → LocalHistory S n M K → ℝ) (hp2 : 2 * S.d + 1 ≤ S.p2) (hlk : 0 ≤ S.lam (j + 1))
    (hCR0 : S.CR ≤ S.A2 * S.lam (j + 1) ^ (S.p2 - (2 * S.d + 1)))
    (F : FlowSeq) (hS : F.Matches S) (hk0F : k0 = F.k0) (hKF : K = F.kf) (hkf : 1 ≤ F.kf)
    (hΛ12 : ((F.d : ℝ) + 3) / 2 ≤ S.lam F.k0 * (1 - 1 / (2 * Real.log F.L)))
    (hgen : F.beta F.k0 * F.nu F.k0 ≤ 1 → 2 * (F.L : ℝ) ^ 2 ≤ F.beta F.k0)
    (Bs : BudgetSetup S P) (hjk0 : j + 1 ≤ k0)
    (hwit : ∀ z, ∀ a ∈ Hs z, ∃ (H : RegionHistory S n R k0 K)
      (hY : (cz z).1 ∈ comps (S.omega (j + 1)) (H.Zp (j + 1))) (hadm : H.Admissible)
      (κK : ∀ m, H.Comp m → ℝ),
      (∀ i, i + 1 ≤ k0 → ∀ c : H.Comp (i + 1), c.1 ∉ H.rem (i + 1) →
        S.Ripe (i + 1) (H.bk (i + 1) c) →
          H.kappaPre P i (H.kappa P κK i) c - S.CR * S.lam (i + 1) ^ (2 * S.d + 1) +
            S.A3' * S.lam (i + 1) ^ S.pR ≤ κK (i + 1) c) ∧
      a = RegionHistory.localHistory H M K (j + 1) ⟨(cz z).1, hY⟩ ∧
      S.Ripe (j + 1) (H.bk (j + 1) ⟨(cz z).1, hY⟩) ∧
      κpre z a = H.kappaPre P j (H.kappa P κK j) ⟨(cz z).1, hY⟩)
    (hwin : ∀ z, ∀ a ∈ Hs z, KerBound a (j + 1) (Tr a) (κpre z a - S.CR * S.lam (j + 1) ^ (2 * S.d + 1)))
    (hh : fac * Real.exp fac * Real.exp (κ' * cG S.d S.L) *
        (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1)) +
      κ' * (1 + cG S.d S.L) + c1 S.d S.L + 3 +
      Real.log (1 * (K0 S.d S.L (aEnt S.d S.L + 1) + 1) *
        Real.exp ((aEnt S.d S.L + 1) * 1)) ≤ h')
    (X : NePoly (CubeB (L := S.L) (N₁ := Fr.N₁) (m₁ := m₁) (K := K) m₀ (j + 1)
      (d7Pull Fr (j + 1) (A.H.omegaPost (j + 1))))) :
    ‖gasK cy zs cr β τ X‖ ≤
      3 * c1 S.d S.L * Real.exp (-p') * Real.exp (-(κ' - 2) * dExt (d := S.d) X.1) := by
  refine lf4R_removed hD hA hhB p labY hlabY hlabYv hp labZ hlabZ hXY hXZ hk hR cz hcz hlabZ' hfac hκ' hκ''
    hp' hκ hz hcr β hβ G hT hH hh' ok hlam hrun hp'2 hx0 hLd hA2 hb0 hPb hHdef Hs hHs Tr Fa hFa gk hgk parK
    hτ κpre hp2 hlk hCR0 ?_ hwin hh X
  intro z a ha
  obtain ⟨H, hY, hadm, κK, hκK, rfl, hripe, hκpre⟩ := hwit z a ha
  rw [hκpre]
  exact hrip_of_flow' G F hS hk0F hKF H hadm hkf hΛ12 hgen Bs κK hκK hjk0 hkK ⟨(cz z).1, hY⟩ hripe

end Final

end Balaban.LargeField
