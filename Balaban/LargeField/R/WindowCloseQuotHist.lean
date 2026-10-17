/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowComposeCore
public import Balaban.LargeField.R.WindowCloseGeom
public import Balaban.LargeField.R.WindowCloseAlg
public import Balaban.LargeField.R.WindowCloseNodeExact
public import Balaban.LargeField.R.WindowCloseSum
public import Balaban.LargeField.R.WindowCloseQuot
public import Balaban.LargeField.R.RTransportDensity

/-!
# The quotient of the window at the data of a point of the history (blocker 4, W964)

`notes/phase1/LF4R-PLAN.md` §9.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  ActionConv RegionHistory ENNReal Balaban.SmallField

section Core

open Classical

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The quotient (2.58′) at the data of a point of the history** (`window_quotient_at` for the window of `Z` and the regions
`Z_{k₁}^+`, `X_win ∖ Z_{k₁}^+`). -/
theorem window_quot_hist [NeZero S.M] [NeZero N] {k1 m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hMS : M = S.M) (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (h3 : 8 ≤ S.L * S.lateR (m' + 1)) (hW : H.RipeWindow (m' + 1) Z) (hk1def : S.k1 (m' + 1) = k1)
    (Z0 V2 : Set (BlockAt S n M K (m' + 1))) (P2 : BlockAt S n M K (m' + 1) → Prop)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∉ Z0)
    (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
    (hV2full : ∀ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m', y ∉ Z0 → y ∈ V2 ∧ P2 y)
    {a₁ β0 : ℝ} (hβ0 : 0 < β0) (ha₁ : 0 < a₁)
    {D0 : ℕ}
    (hd : 2 ≤ S.d)
    (hk : 1 ≤ (m' + 1))
    (b0 : Torus S.d ((M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1))))
    (wb : Fin S.d → ℕ)
    (hw1 : ∀ i, 1 ≤ wb i)
    (hwD : ∀ i, wb i ≤ D0)
    (hmD : D0 + 2 ≤ (M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1)))
    {X : Set (Torus S.d ((M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1))))}
    (hXreg : box b0 wb ∪ shellOut (box b0 wb) ⊆ X)
    (hΩ : OverTop (windowOfHistory H Z geo hm hW).bdry (box b0 wb ∪ shellOut (box b0 wb)))
    (hdata : ∀ x ∈ dataSites (windowOfHistory H Z geo hm hW).bdry, jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ X)
    (Hbg : BgHyp S.d S.L (m' + 1) (winSep geo) (compWeight S.L a₁) 0)
    {δ : ℝ}
    (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg)
    {p0 : ℝ}
    (hp0 : 1 ≤ cSix S.d D0 (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg) * p0)
    (hradδ : psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg * δ +
      5 * zeroRadius (cSix S.d D0 (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg))
        (betaK S.d S.L (m' + 1) β0) p0 ≤ etaDen S.d S.L N D0)
    (Hbg0 : BgHyp S.d S.L (m' + 1) (winSep geo) (compWeight S.L a₁) 0)
    {Kw δw : ℝ}
    (hWP : WeightedProp51S S.d S.L N Kw δw)
    (hKw : 0 ≤ Kw)
    (hOp : Dec2.OpSetting (Multiscale.GeneratingSet.castN (window_hNq (S := S) (n := n) (M := M) (K := K) H.F.hnn hm) (windowOfHistory H Z geo hm hW).bdry) (compWeight S.L a₁) 0)
    (hsep2 : 2 * S.d * Real.log S.L ≤ gammaW S.d / 4 * ((winSep geo) - 1))
    (hsmall : bgK1 S.d S.L N * (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg * δ) ≤
      min (deltaStar S.d S.L N) δw)
    (hρs : zeroRadius (cSix S.d D0 (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg))
      (betaK S.d S.L (m' + 1) β0) p0 ≤ min (deltaStar S.d S.L N) δw)
    (hRfl : ⌊R m'⌋₊ = ⌊S.Rb * S.lam m' ^ 2⌋₊)
    (hlogβ : Real.log (betaK S.d S.L (m' + 1) β0) ≤ S.lam (m' + 1))
    (hxl : ((S.L : ℝ) * (2 / gammaW S.d) * (1 + S.θp) + S.M) / (S.M * S.Rb) ≤ S.lam m')
    {CEt Cnat : ℝ}
    (hCEt : cTildeE N S.d D0 + (S.d + 1) * N * (2 * (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) +
        (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) ^ 2) *
        (Real.exp (gammaW S.d / 2 * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d / 2)) ≤ CEt)
    (hbx : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ box b0 wb ↔
        torusCast (congrArg (· * n (m' + 1)) hMS) (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) x) ∈
          H.Zzero (m' + 1) Z)
    (hZ0b : ∀ y : BlockAt S n M K (m' + 1), (y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0) ↔
      torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y ∈ boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb)
    (Zr : Region (windowOfHistory H Z geo hm hW).bdry) (hZrs : Zr.sites = (windowOfHistory H Z geo hm hW).Z)
    (ftop : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (ψout : BlockField S.d S.L (M * n (m' + 1)) (m' + 1) N)
    (hψout : TubeOn (windowOfHistory H Z geo hm hW).bdry (X \ box b0 wb) δ ψout)
    (hψoutz : ∀ y : BlockAt S n M K (m' + 1), y ∉ Z0 → ∀ i,
      ψout (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ftop y i)
    (ψ0 : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ0 : ∀ z i, ψ0 ⟨m' + 1, z⟩ i =
      psiZero N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg hδ hδc hψout z i)
    (Du : BgData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) N)
    (hDuh : ∀ x i, Du.h x i = 0)
    (hDu2 : ∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x = m' + 1 → ∀ i, Du.Ψ x i =
      ((ftop (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ))
    (Dpp : Region (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW))) (Zp : Region (windowOfHistory H Z geo hm hW).bdry)
    (hZp : ∀ x, x ∈ Zp.sites ↔ ∃ y ∈ (windowOfHistory H Z geo hm hW).Zk1,
      jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x = jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) y)
    (hDpp : Dpp.sites = ((windowOfHistory H Z geo hm hW).Z \ (windowOfHistory H Z geo hm hW).Zk1) \ Zp.sites)
    (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
    (hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y)
    (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
    (hψk : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y → y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
      ψk (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ((ftop y i : ℝ) : ℂ))
    (aN : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → ℝ) (haN : ∀ z ∈ Zb, 0 < aN z)
    (hDat : (windowData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (windowOfHistory H Z geo hm hW).bdry (windowOfHistory_precedes geo hm hW) (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)).IsReal)
    (hφ : ∀ p, ((windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)) p).im = 0)
    (hDuDom : InUnionDomainR (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (bgC1 S.d S.L N) 0 Du)
    (hA0 : ‖(β0 : ℂ) * actionRegion0 Zp 0 (psiZeroData (windowOfHistory H Z geo hm hW).bdry ψ0 (0 : Fin N → ℝ))
      (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))‖ < 1 / 4)
    (hb : ‖(1 / 2 : ℂ) * (β0 : ℂ) * Dpp.sitePair ((windowOfHistory_precedes geo hm hW).restrictα (alphaZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)))
        (svec (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) ((bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du) - (windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))))
        (svec (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) ((bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du) - (windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))))‖ < 1 / 4)
    (hst : ‖(β0 : ℂ) * stTerm Dpp (windowData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (windowOfHistory H Z geo hm hW).bdry (windowOfHistory_precedes geo hm hW) (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)) Du
        ((windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))) (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)‖ < 1 / 4)
    (hnu : ‖(β0 : ℂ) * nuTerm Dpp 0 (windowData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (windowOfHistory H Z geo hm hW).bdry (windowOfHistory_precedes geo hm hW) (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))
        ((windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))) (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)‖ < 1 / 4)
    (hnat : ‖Cnat0 a₁ (windowOfHistory_precedes geo hm hW) ψ0 (0 : Fin N → ℝ) Du Zb β0 (varpi (m' + 1) cs.z) aN ψk‖ ≤ Cnat * S.lam (m' + 1) ^ (2 * S.d + 1))
    (Ckk : ℝ) :
    Real.exp (-(gaussNat (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (varpi (m' + 1) cs.z) Du.Ψ (betaK S.d S.L (m' + 1) β0) aN ψk Zb).re -
          (((β0 : ℂ) * actionRegionC Dpp (compWeight S.L a₁) 0 Du (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)).re - Ckk)) *
        constNat N (betaK S.d S.L (m' + 1) β0) aN Zb / constNat N (betaK S.d S.L (m' + 1) β0) (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb /
        (∫ u, rhoZeroRestricted (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg hδ hδc hψout
          Zr 0 (0 : Fin N → ℝ) β0 p0 u) ≤
      Real.exp ((N : ℝ) / 2 * Real.log (betaK S.d S.L (m' + 1) β0) *
        ((boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb).card : ℝ) + CEt * (D0 : ℝ) ^ S.d +
        Cnat * S.lam (m' + 1) ^ (2 * S.d + 1) + 4 + Ckk) := by
  classical
  subst hMS
  have hnn := H.F.hnn
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  have hdS : 0 < S.d := by omega
  have hBx : ∀ y : BlockAt S n S.M K (m' + 1), y ∈ Z0 ↔
      torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y ∈ box b0 wb := by
    intro y
    constructor
    · intro hy
      have hv : y ∈ Vblk R (H.localHistory S.M K (m' + 1) Z) (m' + 1) :=
        ZBlk_mem_Vblk hm Z y (gaussBlocks_zblk hm Z (hZ0g hy))
      exact mem_boxFinset.mp ((hZ0b y).mp ⟨hv, hy⟩)
    · intro h
      exact ((hZ0b y).mpr (mem_boxFinset.mpr h)).2
  have hZ0box : ∀ s : Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (congrArg (· * n (m' + 1)) rfl) (blockMap (S.L ^ (m' + 1)) (S.M * n (m' + 1)) s) ∈
        H.Zzero (m' + 1) Z →
      jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm s) ∈ Z0 := by
    intro s hs
    have h1 := (hbx s).mpr hs
    have h2 := (mem_fib_cast hnn hm (le_refl (m' + 1))
      (jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm s)) s).mpr rfl
    rw [mem_fib] at h2
    exact (hBx _).mpr (by rw [← h2]; exact h1)
  have hZb' : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n S.M K (m' + 1),
      y ∈ gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
        zb = torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y := by
    intro zb
    rw [hZb]
    constructor
    · rintro ⟨y, hy1, hy2, hy3, rfl⟩; exact ⟨y, hy3, hV2 y hy1 hy2, rfl⟩
    · rintro ⟨y, hy1, hy2, rfl⟩
      obtain ⟨h1, h2⟩ := hV2full y hy1 hy2
      exact ⟨y, h1, h2, hy1, rfl⟩
  have hWh := windowOfHistory_hyp (g := geo) hm hW
  obtain ⟨D, D0, Dω, hD1, hD2, hD3, hD4, hD5, hD6, hD7, hD8, hD9, hD10⟩ := window_region_decomp rfl G h18 h3 hm hW
    hk1def geo (windowOfHistory H Z geo hm hW) hWh (fun q => windowOfHistory_full_Ω H Z geo hm hW q)
    (windowOfHistory_Z H Z geo hm hW) (by rw [windowOfHistory_Zk1, hk1def]) Z0 (box b0 wb) hZ0box hBx Zb hZb'
  have hZsub : (windowOfHistory H Z geo hm hW).Zk1 ⊆ (windowOfHistory H Z geo hm hW).Z :=
    windowOfHistory_hZ (g := geo) hm hW
  have hZpbox : ∀ x ∈ Zp.sites, jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ box b0 wb := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (hZp x).mp hx
    rw [hxy]; exact hD10 y hy
  have hZpZ : ∀ x ∈ Zp.sites, x ∈ (windowOfHistory H Z geo hm hW).Z := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (hZp x).mp hx
    exact (windowOfHistory_hbZ geo hm hW (m' + 1) (by omega) le_rfl x y hxy).mpr (hZsub hy)
  have hZk1Zp : ∀ y ∈ (windowOfHistory H Z geo hm hW).Zk1, y ∈ Zp.sites := fun y hy =>
    (hZp y).mpr ⟨y, hy, rfl⟩
  have hDsub : Dpp.sites ⊆ D.sites := by
    intro x hx
    rw [hDpp] at hx; rw [hD1]
    exact (Finset.mem_sdiff.mp hx).1
  have hzbox : ∀ z ∈ Zb, z ∉ box b0 wb := by
    intro z hz hzb
    obtain ⟨y, -, hy0, rfl⟩ := (hZb' z).mp hz
    exact hy0 ((hBx y).mpr hzb)
  have hfibD : ∀ z ∈ Zb, ∀ x ∈ fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) z, x ∈ Dpp.sites := by
    intro z hz x hx
    have hxD : x ∈ D.sites := by
      rw [hD2]; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z, hz, hx⟩)
    rw [hDpp]
    refine Finset.mem_sdiff.mpr ⟨by rw [← hD1]; exact hxD, fun hxp => hzbox z hz ?_⟩
    rw [mem_fib] at hx
    rw [← hx]; exact hZpbox x hxp
  let E0 : Finset (Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1))) :=
    Dpp.sites.filter fun x => jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ box b0 wb
  let Eω : Finset (Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1))) :=
    (Dpp.sites.filter fun x => jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x ∉ box b0 wb) \
      Zb.biUnion (fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1))
  have hfibblk : ∀ x ∈ Zb.biUnion (fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1)),
      jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x ∉ box b0 wb := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.mp hx
    have hxz' : jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x = z := mem_fib.mp hxz
    rw [hxz']; exact hzbox z hz
  have hDfull : Dpp.sites = E0 ∪ Eω ∪ Zb.biUnion (fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1)) := by
    ext x
    simp only [E0, Eω, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · intro hx
      by_cases hb : jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ box b0 wb
      · exact Or.inl (Or.inl ⟨hx, hb⟩)
      · by_cases hf : ∃ z ∈ Zb, x ∈ fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) z
        · exact Or.inr hf
        · exact Or.inl (Or.inr ⟨⟨hx, hb⟩, hf⟩)
    · rintro ((⟨hx, -⟩ | ⟨⟨hx, -⟩, -⟩) | ⟨z, hz, hxz⟩)
      · exact hx
      · exact hx
      · exact hfibD z hz x hxz
  have hD0ω : Disjoint E0 Eω := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [E0, Eω, Finset.mem_filter, Finset.mem_sdiff] at h1 h2
    exact h2.1.2 h1.2
  have hDr : Disjoint (E0 ∪ Eω) (Zb.biUnion (fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1))) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [E0, Eω, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff] at h1
    rcases h1 with h1 | h1
    · exact hfibblk x h2 h1.2
    · exact h1.2 h2
  have hDωl : ∀ x ∈ Eω, (windowOfHistory H Z geo hm hW |>.windowGenSet hWh).layerIndex x = m' + 1 := by
    intro x hx
    simp only [Eω, Finset.mem_sdiff, Finset.mem_filter] at hx
    obtain ⟨⟨hxD, hxb⟩, hxf⟩ := hx
    have hxD' := hDsub hxD
    rw [hD2] at hxD'
    rcases Finset.mem_union.mp hxD' with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact absurd (hD5 x h) hxb
      · exact hD6 x h
    · exact absurd h hxf
  have hZr : Zr.sites = Dpp.sites ∪ Zp.sites := by
    rw [hZrs, hDpp]
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hp : x ∈ Zp.sites
      · exact Or.inr hp
      · exact Or.inl ⟨⟨hx, fun h => hp (hZk1Zp x h)⟩, hp⟩
    · rintro (⟨⟨hx, -⟩, -⟩ | hp)
      · exact hx
      · exact hZpZ x hp
  have hZd : Disjoint Dpp.sites Zp.sites := by
    rw [hDpp]; exact Finset.sdiff_disjoint
  have hlay' : ∀ x ∈ Zr.sites, (windowOfHistory H Z geo hm hW).bdry.layerIndex x = m' + 1 := by
    intro x hx
    rw [hZrs] at hx
    exact windowOfHistory_bdry_layerIndex geo hm hW (by omega) hx
  have hEωy : ∀ x ∈ Eω, ∃ y : BlockAt S n S.M K (m' + 1), y ∉ Z0 ∧
      jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x = torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y ∧
      y = jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm x) := by
    intro x hx
    simp only [Eω, Finset.mem_sdiff, Finset.mem_filter] at hx
    have h2 := (mem_fib_cast hnn hm (le_refl (m' + 1))
      (jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm x)) x).mpr rfl
    have h2' : jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x =
        torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm
          (jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm x)) := mem_fib.mp h2
    refine ⟨_, fun hy => hx.1.2 (by rw [h2']; exact (hBx _).mp hy), h2', rfl⟩
  have hDtop : ∀ x ∈ Eω, ∀ i, Du.Ψ x i = ((ψout (jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x) i : ℝ) : ℂ) := by
    intro x hx i
    obtain ⟨y, hy0, hy1, hy2⟩ := hEωy x hx
    have hxΩ : x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet hWh).Ω 1 := by
      have := Finset.mem_sdiff.mp hx
      exact Dpp.sub_Ω (Finset.mem_filter.mp this.1).1
    rw [hDu2 x hxΩ (hDωl x hx) i, hy1, hψoutz y hy0 i, ← hy2]
  have hψkψ : ∀ z ∈ Zb, ∀ i, ψk z i = ((ψout z i : ℝ) : ℂ) := by
    intro z hz i
    obtain ⟨y, hy1, hy0, rfl⟩ := (hZb' z).mp hz
    obtain ⟨hyV, hyP⟩ := hV2full y hy1 hy0
    rw [hψk y hyV hyP hy1 i, hψoutz y hy0 i]
  have hha : ∀ j, 0 ≤ compWeight S.L a₁ j := compWeight_nonneg hL ha₁
  refine window_quotient_at H.F.ok (windowOfHistory_precedes geo hm hW) ψ0 (0 : Fin N → ℝ) Du Dpp Zr Zp Zb
    (varpi (m' + 1) cs.z) aN ψk hβ0 le_rfl ha₁ hL hha haN hD7 hDat rfl hφ hA0 hb hst hnu hd hk b0 wb hw1 hwD hmD hXreg
    hΩ hdata Hbg hδ hδc hψout hp0 hradδ hψ0 Hbg0 hDuDom ?_ E0 Eω hDfull hD0ω hDr hZr hZd hlay'
    (fun x hx => (Finset.mem_filter.mp hx).2) (fun x hx => hZpbox x hx) hDωl hDtop
    (fun x hx => (Finset.mem_sdiff.mp hx).1 |> Finset.mem_filter.mp |>.2) hψkψ hzbox Ckk H hm Z rfl
    (window_hNq hnn hm) (fun x => hbx x) (fun x => ?_) hWP hKw hOp hsep2 rfl (fun i => by simp) hsmall hρs hRfl hlogβ hxl
    hCEt hnat
  · intro x i
    rw [hDuh x i]
    simp only [windowData, BgData.clip]
    split_ifs <;> simp
  · rw [hZrs]
    simp only [windowOfHistory_Z, mem_locFineFin, mem_locFine_k hm]
    exact Iff.rfl

end Core

end Balaban.LargeField
