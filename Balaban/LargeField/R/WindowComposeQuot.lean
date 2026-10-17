/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedFracInst
public import Balaban.LargeField.R.CancelStationary
public import Balaban.LargeField.R.WindowRegionDecomp

/-!
# The quotient (2.58′) of the removed outcome with `hid` from the cancellation identity (blocker 4, item S6)

`notes/phase1/LF4R-PLAN.md` §9.3, item S6.  `window_quotient_of_history` is `removed_quotient_le_of_history`
with its hypothesis `hid` (the fundamental formula, Lemma III.6.3) supplied by `cancellation_identity` at the
window datum `Du`.  The Euler-Lagrange background of `Du` is `bgField`, with its reality and the
Euler-Lagrange system from `theorem71` (`hDuDom`, `Hbg0`); `hKδ` follows from `hrad`.  The region data of
`cancellation_identity` are the conclusions of `window_region_decomp` (W959) for the window generating set; they
enter as the named typing data `hD`, `hD0ω`, `hDr`, `hZr`, `hZd`, `hD0Z`, `hZk1Z` and the layer part of `hDω`;
the data of the history not given by `window_region_decomp` are `hlay'` (top layer of `Z_r`) and the part
`dataInc … = 0` of `hDω` (the datum `Du` is the field of the configuration, `ψ⁰ = ψ_k` off `Z₀`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization ActionConv
  RegionHistory

section Quotient

variable {S : Setting} (ok : S.Ok) {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  [NeZero S.L] [NeZero S.M] {k' : ℕ} {N₁ m₁ N : ℕ} [NeZero N₁] [NeZero N] {ϱ ϱ₀ : ℝ}
  {G₀ : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k' + 1) ϱ₀}
  {G : GeneratingSet S.d S.L (N₁ * S.L ^ m₁) (k' + 1) ϱ}

include ok in
/-- **The quotient (2.58′) of the removed outcome, with `hid` from `cancellation_identity`.** -/
theorem window_quotient_of_history {a₁ : ℝ}
    (hprec : Precedes G₀ G)
    (ψ0 : BlockV S.d S.L (N₁ * S.L ^ m₁) (k' + 1) → EuclideanSpace ℝ (Fin N))
    (h : Fin N → ℝ)
    (Du : BgData G₀ N)
    {φu : G₀.Ω 1 × Fin N → ℂ}
    (D : Region G₀)
    (Zr Zk1 : Region G)
    (Zb : Finset (Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1)))))
    {β0 ν : ℝ}
    (ϖ : ℕ → ℝ)
    (aN : Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))) → ℝ)
    (ψk : Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))) → Fin N → ℂ)
    (hβ0 : 0 < β0)
    (hν : 0 ≤ ν)
    (ha₁ : 0 < a₁)
    (hL : 2 ≤ S.L)
    (ha : ∀ j, 0 ≤ compWeight S.L a₁ j)
    (haN : ∀ z ∈ Zb, 0 < aN z)
    (hZb : ∀ z ∈ Zb, ∀ x ∈ fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) z, 1 ≤ G₀.layerIndex x ∧ G₀.layerIndex x < (k' + 1))
    (hDat : (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h).IsReal)
    (hφu : φu = bgField G₀ (compWeight S.L a₁) 0 Du)
    (hφ : ∀ p, (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h) p).im = 0)
    (hA0 : ‖(β0 : ℂ) * actionRegion0 Zk1 ν (psiZeroData G ψ0 h)
      (phiZero G (compWeight S.L a₁) ψ0 h)‖ < 1 / 4)
    (hb : ‖(1 / 2 : ℂ) * (β0 : ℂ) * D.sitePair (hprec.restrictα (alphaZero G (compWeight S.L a₁) ψ0 h))
        (svec G₀ (φu - hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)))
        (svec G₀ (φu - hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)))‖ < 1 / 4)
    (hst : ‖(β0 : ℂ) * stTerm D (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du
        (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu‖ < 1 / 4)
    (hnu : ‖(β0 : ℂ) * nuTerm D ν (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h)
        (hprec.restrictφ (phiZero G (compWeight S.L a₁) ψ0 h)) φu‖ < 1 / 4)
    {D0 : ℕ}
    (hd : 2 ≤ S.d)
    (hk : 1 ≤ (k' + 1))
    (b0 : Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))))
    (w : Fin S.d → ℕ)
    (hw1 : ∀ i, 1 ≤ w i)
    (hwD : ∀ i, w i ≤ D0)
    (hm : D0 + 2 ≤ (N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1)))
    {X : Set (Torus S.d ((N₁ * S.L ^ m₁) * S.L ^ ((k' + 1) - (k' + 1))))}
    (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ X)
    (Hbg : BgHyp S.d S.L (k' + 1) ϱ (compWeight S.L a₁) 0)
    {δ : ℝ}
    (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg)
    {ψout : BlockField S.d S.L (N₁ * S.L ^ m₁) (k' + 1) N}
    (hψout : TubeOn G (X \ box b0 w) δ ψout)
    {p0 : ℝ}
    (hp0 : 1 ≤ cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg) * p0)
    (hrad : psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg * δ +
      5 * zeroRadius (cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg))
        (betaK S.d S.L (k' + 1) β0) p0 ≤ etaDen S.d S.L N D0)
    (hψ0 : ∀ z i, ψ0 ⟨(k' + 1), z⟩ i =
      psiZero N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout z i)
    (Hbg0 : BgHyp S.d S.L (k' + 1) ϱ₀ (compWeight S.L a₁) 0)
    (hDuDom : InUnionDomainR G₀ (bgC1 S.d S.L N) 0 Du)
    (hDuh : ∀ x i, Du.h x i = (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h).h x i)
    (E0 Eω : Finset (Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1))))
    (hD : D.sites = E0 ∪ Eω ∪ Zb.biUnion (fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1)))
    (hD0ω : Disjoint E0 Eω)
    (hDr : Disjoint (E0 ∪ Eω) (Zb.biUnion (fib S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1))))
    (hZr : Zr.sites = D.sites ∪ Zk1.sites) (hZd : Disjoint D.sites Zk1.sites)
    (hlay' : ∀ x ∈ Zr.sites, G.layerIndex x = k' + 1)
    (hD0Z : ∀ x ∈ E0, jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w)
    (hZk1Z : ∀ x ∈ Zk1.sites, jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w)
    (hDω : ∀ x ∈ Eω, G₀.layerIndex x = k' + 1 ∧
      ∀ i, dataInc (windowData G₀ G hprec (compWeight S.L a₁) ψ0 h) Du x i = 0)
    (hψk : ∀ z ∈ Zb, ∀ i, ψk z i = ((ψ0 ⟨k' + 1, z⟩ i : ℝ) : ℂ))
    (Ckk : ℝ)
    (Hh : RegionHistory S n R k0 K)
    (hkK : k' + 1 ≤ K)
    (Zc : Hh.Comp (k' + 1))
    (hq : N₁ * S.L ^ m₁ = S.M * n (k' + 1))
    (hbx : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
      jBlock S.d S.L (N₁ * S.L ^ m₁) (k' + 1) (k' + 1) x ∈ box b0 w ↔
        blockMap (S.L ^ (k' + 1)) (S.M * n (k' + 1))
          (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ Hh.Zzero (k' + 1) Zc)
    (hZrsites : ∀ x : Torus S.d (N₁ * S.L ^ m₁ * S.L ^ (k' + 1)),
      x ∈ Zr.sites ↔ cubeMap n S.L S.M (k' + 1) (k' + 1)
        (torusCast (congrArg (· * S.L ^ (k' + 1)) hq) x) ∈ (Zc.1 : Set (Torus S.d (n (k' + 1)))))
    {Kw δw : ℝ}
    (hWP : WeightedProp51S S.d S.L N Kw δw)
    (hKw : 0 ≤ Kw)
    (hOp : Dec2.OpSetting G (compWeight S.L a₁) 0)
    (hsep2 : 2 * S.d * Real.log S.L ≤ gammaW S.d / 4 * (ϱ - 1))
    (hν0 : ν = 0)
    (hh1 : ∀ i, |h i| ≤ 1)
    (hsmall : bgK1 S.d S.L N * (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg * δ) ≤
      min (deltaStar S.d S.L N) δw)
    (hρs : zeroRadius (cSix S.d D0 (psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg))
      (betaK S.d S.L (k' + 1) β0) p0 ≤ min (deltaStar S.d S.L N) δw)
    (hRfl : ⌊R k'⌋₊ = ⌊S.Rb * S.lam k' ^ 2⌋₊)
    (hlogβ : Real.log (betaK S.d S.L (k' + 1) β0) ≤ S.lam (k' + 1))
    (hxl : ((S.L : ℝ) * (2 / gammaW S.d) * (1 + S.θp) + S.M) / (S.M * S.Rb) ≤ S.lam k')
    {CEt Cnat : ℝ}
    (hCEt : cTildeE N S.d D0 + (S.d + 1) * N * (2 * (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) +
        (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) ^ 2) *
        (Real.exp (gammaW S.d / 2 * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d / 2)) ≤ CEt)
    (hnat : ‖Cnat0 a₁ hprec ψ0 h Du Zb β0 ϖ aN ψk‖ ≤ Cnat * S.lam (k' + 1) ^ (2 * S.d + 1))
    :
    Real.exp (-(gaussNat G₀ ϖ Du.Ψ (betaK S.d S.L (k' + 1) β0) aN ψk Zb).re -
          (((β0 : ℂ) * actionRegionC D (compWeight S.L a₁) ν Du φu).re - Ckk)) *
        constNat N (betaK S.d S.L (k' + 1) β0) aN Zb / constNat N (betaK S.d S.L (k' + 1) β0) (compWeightZ G₀ a₁) Zb /
        (∫ u, rhoZeroRestricted G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout
          Zr ν h β0 p0 u) ≤
      Real.exp ((N : ℝ) / 2 * Real.log (betaK S.d S.L (k' + 1) β0) *
        ((boxFinset (L := S.L) (N₀ := N₁ * S.L ^ m₁) (k := k' + 1) b0 w).card : ℝ) + CEt * (D0 : ℝ) ^ S.d +
        Cnat * S.lam (k' + 1) ^ (2 * S.d + 1) + 4 + Ckk)
  := by
  subst hν0
  subst hφu
  have hd0 : 0 < S.d := by omega
  have hDu : Du.IsReal := by
    obtain ⟨δ', -, -, hD'⟩ := hDuDom
    exact isReal_of_inDomainR hD'
  have hEL := (theorem71 Hbg0 hDuDom).2.2.1.1
  have hreal : ∀ p, (bgField G₀ (compWeight S.L a₁) 0 Du p).im = 0 := fun p =>
    ((theorem71 Hbg0 hDuDom).2.1 p.1).1 p.2
  have hβk : 0 < betaK S.d S.L (k' + 1) β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hD1 : 1 ≤ D0 := (hw1 ⟨0, hd0⟩).trans (hwD _)
  have hK : 0 < psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg :=
    psiZeroK_pos N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg
  have hC6 := cSix_pos hd0 hD1 hK.le
  have hρ0 := zeroRadius_pos hC6 hβk hp0
  have hKδ : psiZeroK N G (compWeight S.L a₁) hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg * δ <
      etaDen S.d S.L N D0 := by linarith
  have hid := cancellation_identity (G := G₀) (G' := G) (ν := 0) hd hk ha₁ hβ0 b0 w hw1 hwD hm hXreg hΩ hdata Hbg
    hδ hδc hψout hKδ hprec ψ0 h hψ0 Du hDuh hEL D Zr Zk1 E0 Eω Zb hD hD0ω hDr hZr hZd hlay' hD0Z hZk1Z
    hDω hZb ψk hψk ϖ aN haN
  exact removed_quotient_le_of_history ok hprec ψ0 h Du D Zr Zk1 Zb ϖ aN ψk hβ0 hν ha₁ hL ha haN hZb hDat
    hDu hreal hφ hid hA0 hb hst hnu hd hk b0 w hw1 hwD hm hXreg hΩ hdata Hbg hδ hδc hψout hp0 hrad hψ0 Ckk
    Hh hkK Zc hq hbx hZrsites hWP hKw hOp hsep2 rfl hh1 hsmall hρs hRfl hlogβ hxl hCEt hnat

end Quotient

end Balaban.LargeField
