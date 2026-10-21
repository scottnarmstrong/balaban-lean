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
public import Balaban.LargeField.R.WindowCloseQuotHist
public import Balaban.LargeField.R.RTransportDensity

/-!
# The composed window bound `hbG` with collar values of the reference datum (blocker 4, W1086)

The cores of `WindowCloseHbG` (`window_hbG_fields_cl`, `window_hbG_node_cl`, `window_hbG_cI_cl`,
`window_hbG_sum_cl`, `window_hbG_psiz_cl`, `window_hbG_regions_cl`) with the reference datum `Du` of the hid
chain carrying the collar values `cl` (vanishing off the data sites) instead of `0`, and the named source
inputs `hnamedC` stating the sum-level conversion at `Du` (instead of the per-piece inputs of `hnamed`).
The landed `window_hbG_*` are the instances `cl = 0`.
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

variable {k1 m' : ℕ}
variable (hk1p : 1 ≤ k1)
variable (hk1 : k1 ≤ m')
variable (hm : m' + 1 ≤ K)
variable (hk1K : k1 ≤ K)
variable (hk1K1 : k1 + 1 ≤ K)
variable (hmk : k1 < m' + 1)
variable {Z : H.Comp (m' + 1)}
variable (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
variable (r : ℕ → ℝ)
variable (TB : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → Prop)
variable (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
variable (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
variable (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1)))
variable (P2 : BlockAt S n M K (m' + 1) → Prop)
variable (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
variable (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0)
variable (hG3 : ∀ y, y ∈ G3 ↔ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
      ¬ (y ∈ V2 ∧ P2 y))
variable (T : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
variable [Fintype ↑T]
variable (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
variable [Fintype ↑Nd]
variable (nd : (Σ s, BlockAt S n M K s) → Prop)
variable (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
variable (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
variable (jS : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A → ℕ)
variable {c0 : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ℝ}
variable {rr : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 →
      OutRest N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 → ℝ}
variable (hc0 : ∀ o, 0 ≤ c0 o)
variable (hrr : ∀ w y, 0 ≤ rr w y)
variable (Zt : Set (Torus S.d (M * n K * S.L ^ K)))
variable (δk : ℝ)
variable (cen : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0} →
      EuclideanSpace ℝ (Fin N))
variable (radZ : ℝ)
variable {ρt : Type}
variable (e : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ρt → EuclideanSpace ℝ (Fin N))
variable (cb : ρt → BlockAt S n M K (m' + 1))
variable (hN2 : 2 ≤ N)
variable (Φ : ((OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
        ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) ×
            ((OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)) ×
                OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)))) →
      OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) × (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A × OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0))
variable (φ1 : ∀ θ (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}),
      (Φ θ).1 ⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩ = θ.1.1 y)
variable (φ2 : ∀ θ (y : {y // y ∈ V2 ∧ P2 y}),
      (Φ θ).1 ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩ = θ.1.2.1 y)
variable (φ3 : ∀ θ (t : ↥T), (Φ θ).2.1 t.1 = θ.1.2.2 t)
variable (φ4 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (θ.2.1 C).1 y = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inl y⟩)))
variable (φ5 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A),
        VarVal.toEuc ((θ.2.1 C).2 q) = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inr q⟩)))
variable (φ7 : ∀ θ (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
          (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)}),
      (Φ θ).1 ⟨y.1, y.2.1, y.2.2.1⟩ = θ.2.2.1.2 y)
variable (φ9 : ∀ θ (t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
        p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}), (Φ θ).2.1 t.1 = θ.2.2.2.1.2 t)
variable (Qtot : ℝ≥0∞)
variable (φ8 : ∀ θ (t : ↥Nd), (Φ θ).2.1 t.1 = θ.2.2.2.1.1 t)
variable (φ10 : ∀ θ, (Φ θ).2.2 = θ.2.2.2.2)
variable [NeZero S.M]
variable [NeZero N]
variable (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
variable (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
variable (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
variable (hV2full : ∀ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m', y ∉ Z0 → y ∈ V2 ∧ P2 y)
variable (hMS : M = S.M)
variable (G : S.Good)
variable (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
variable (h3 : 8 ≤ S.L * S.lateR (m' + 1))
variable (hW : H.RipeWindow (m' + 1) Z)
variable (hk1def : S.k1 (m' + 1) = k1)
variable (hzpos : ∀ s, 0 < cs.z s)
variable (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
variable (hc01 : ∀ o, c0 o ≤ 1)
variable [hfin : Fintype {b : Σ s, BlockAt S n M K s // nd b}]
variable [hfinl : Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
variable (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
variable (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
variable (Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop)
variable [DecidablePred Fx]
variable (hFxdef : ∀ i : {b : Σ s, BlockAt S n M K s // nd b},
      Fx i ↔ ∃ y : BlockAt S n M K (m' + 1), i.1 = ⟨m' + 1, y⟩ ∧ y ∈ V2 ∧ P2 y)
variable {a₁ β0 : ℝ}
variable (hβ0 : 0 < β0)
variable (ha₁ : 0 < a₁)
variable {D0 : ℕ}
variable (hd : 2 ≤ S.d)
variable (hk : 1 ≤ (m' + 1))
variable (b0 : Torus S.d ((M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1))))
variable (wb : Fin S.d → ℕ)
variable (hw1 : ∀ i, 1 ≤ wb i)
variable (hwD : ∀ i, wb i ≤ D0)
variable (hmD : D0 + 2 ≤ (M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1)))
variable {X : Set (Torus S.d ((M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1))))}
variable (hXreg : box b0 wb ∪ shellOut (box b0 wb) ⊆ X)
variable (hΩ : OverTop (windowOfHistory H Z geo hm hW).bdry (box b0 wb ∪ shellOut (box b0 wb)))
variable (hdata : ∀ x ∈ dataSites (windowOfHistory H Z geo hm hW).bdry, jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ X)
variable (Hbg : BgHyp S.d S.L (m' + 1) (winSep geo) (compWeight S.L a₁) 0)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hδc : δ ≤ psiZeroC11 N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg)
variable {p0 : ℝ}
variable (hp0 : 1 ≤ cSix S.d D0 (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg) * p0)
variable (hradδ : psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg * δ +
      5 * zeroRadius (cSix S.d D0 (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg))
        (betaK S.d S.L (m' + 1) β0) p0 ≤ etaDen S.d S.L N D0)
variable (Hbg0 : BgHyp S.d S.L (m' + 1) (winSep geo) (compWeight S.L a₁) 0)
variable {Kw δw : ℝ}
variable (hWP : WeightedProp51S S.d S.L N Kw δw)
variable (hKw : 0 ≤ Kw)
variable (hOp : Dec2.OpSetting (Multiscale.GeneratingSet.castN (window_hNq (S := S) (n := n) (M := M) (K := K) H.F.hnn hm) (windowOfHistory H Z geo hm hW).bdry) (compWeight S.L a₁) 0)
variable (hsep2 : 2 * S.d * Real.log S.L ≤ gammaW S.d / 4 * ((winSep geo) - 1))
variable (hsmall : bgK1 S.d S.L N * (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg * δ) ≤
      min (deltaStar S.d S.L N) δw)
variable (hρs : zeroRadius (cSix S.d D0 (psiZeroK N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg))
      (betaK S.d S.L (m' + 1) β0) p0 ≤ min (deltaStar S.d S.L N) δw)
variable (hRfl : ⌊R m'⌋₊ = ⌊S.Rb * S.lam m' ^ 2⌋₊)
variable (hlogβ : Real.log (betaK S.d S.L (m' + 1) β0) ≤ S.lam (m' + 1))
variable (hxl : ((S.L : ℝ) * (2 / gammaW S.d) * (1 + S.θp) + S.M) / (S.M * S.Rb) ≤ S.lam m')
variable {CEt Cnat : ℝ}
variable (hCEt : cTildeE N S.d D0 + (S.d + 1) * N * (2 * (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) +
        (Kw * cF S.d S.L * Real.exp (2 * S.d * gammaW S.d)) ^ 2) *
        (Real.exp (gammaW S.d / 2 * (2 * S.d + 1)) * countConst S.d S.L (gammaW S.d / 2)) ≤ CEt)
variable (hbx : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ box b0 wb ↔
        torusCast (congrArg (· * n (m' + 1)) hMS) (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) x) ∈
          H.Zzero (m' + 1) Z)
variable (hZ0b : ∀ y : BlockAt S n M K (m' + 1), (y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0) ↔
      torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y ∈ boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb)
variable (Zr : Region (windowOfHistory H Z geo hm hW).bdry)
variable (hZrs : Zr.sites = (windowOfHistory H Z geo hm hW).Z)
variable (hrdef : ∀ (wv : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0) (y : OutRest N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0), rr wv y =
      if hψ : TubeOn (windowOfHistory H Z geo hm hW).bdry (X \ box b0 wb) δ (fun (z : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))))
          (i : Fin N) => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (0, y)) (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))) z) i) then
        rhoZeroRestricted (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg hδ hδc hψ Zr 0
          (0 : Fin N → ℝ) β0 p0
          (WithLp.toLp 2 (fun p : ↥(boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb) × Fin N =>
            wv ⟨torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))) p.1.1, (hZ0b _).2 (by rw [torusCast_symm_cast]; exact p.1.2)⟩ p.2) :
            SuppSpace (boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb) N)
      else 0)
variable (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
variable (hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y)
variable (br : MassBranch)
variable (Xw : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → Region (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)))
variable (hXw : ∀ i x, x ∈ (Xw i).sites ↔
      torusCast (piece_torus_eq geo H.F.hnn hm (chain_piece_spec (Z := Z) hk1 i).2.1) x ∈
        Xfine geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1)
variable (Xwin : Region (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)))
variable (hXwin : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq geo H.F.hnn hm hj.2) x ∈ Xfine geo (H.locRH (j + 1) c) j c.1)
variable (Xc : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), Region (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
      (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)))
variable (hXc : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (Xc i).sites = Xfine geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1)
variable (decomp : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), StepDecomp (Xc i))
variable {Kconv Kbg γw M₀ M₁ : ℝ}
variable {ε Rhat : ℕ → ℝ}
variable {γ η α α₀ : ℝ}
variable (hγ : 0 < γ)
variable (hα₀ : 0 < α₀)
variable (hε : ε = epsSeq S.L α α₀)
variable (hγα : (S.d : ℝ) - 2 - 2 * α = 2 * γ)
variable (hflow : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∃ B : ℝ, 0 < B ∧ ∃ gg : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ gg m ∧ gg m ≤ Real.exp η) ∧
      ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1 ≤ m → m ≤ m' + 1 →
        cs.beta m = B * (S.L : ℝ) ^ ((S.d - 2) * m) * gg m)
variable (hKc : 0 ≤ Kconv)
variable (hKb : 0 ≤ Kbg)
variable (hγw : 0 ≤ γw)
variable (hsep : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), 0 ≤ M₀ * (Rhat ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 - 1) - 1) - 2 * M₁)
variable (hβp : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0)
variable (hμp : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0)
variable (hB0p : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), BgHyp S.d S.L ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (minSep S.L geo.M1) cs.aw (cs.muBg ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)))
variable (hBnp : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (minSep S.L geo.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)))
variable (cl : ∀ (_hv : EuclideanSpace ℝ (Fin N)) (_par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (_wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (_cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (_ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (_sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (_a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (_nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (_w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0), Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) → Fin N → ℝ)
variable (hcl : ∀ (hv : EuclideanSpace ℝ (Fin N)) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0), ∀ x, x ∉ dataSites (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) → ∀ i, cl hv par wd cc ro sh a nd' w' x i = 0)
variable (wt : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) → SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A → ℝ)
variable (hvOK : EuclideanSpace ℝ (Fin N) → Prop)
variable (hnamedC : ∀ (hv : EuclideanSpace ℝ (Fin N)) (_hok : hvOK hv) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)
      (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
      (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)), (∀ v s y, fld v s y = subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y) → (∀ v y, ft v y = outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
            ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
              (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y) → wd ∈ ({o : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 |
            ∀ i, ‖o i - cen par i‖ < radZ} ×ˢ
          ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
            (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
              ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ
            {w3 : ∀ t : ↥T, VarVal N t.1.1.isSpin |
              ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| < r (jS t.1)})) → (TB m' Z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)),
            TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1)) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (Nat.lt_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))) →
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1 hv * wt (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1 ≠ 0 →
        ∀ (Du : BgData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) N) (_hDuh : ∀ x i, Du.h x i = 0)
          (_hDu0 : ∀ x, x ∉ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1 → ∀ i, Du.Ψ x i = ((cl hv par wd cc ro sh a nd' w' x i : ℝ) : ℂ))
          (_hDu1 : ∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x ≠ m' + 1 → ∀ i, Du.Ψ x i =
            ((fld (a, nd', w') ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x) (jBlock S.d S.L (M * n K) K ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
              (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ))
          (_hDu2 : ∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x = m' + 1 → ∀ i, Du.Ψ x i =
            ((ft (a, nd', w') (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)),
          (∃ C : ℂ, (mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
          (locRH_rem (m' + 1) Z) (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) hv +
        ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∑ c : ↥(H.parts (j.1 + 1) P.1),
            mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
              (locComp_mem H (Nat.le_trans (Finset.mem_Ico.mp j.2).2 (Nat.le_of_succ_le hm)) c.1)
              (Nat.le_trans (Finset.mem_Ico.mp j.2).2 (Nat.le_of_succ_le hm)) cs (locRH_rem (j.1 + 1) c.1)
              (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1)) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (Nat.lt_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1)) hv) =
      ((β0 : ℂ) * actionRegionC Xwin (compWeight S.L a₁) 0 Du (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)).re - C.re ∧
      ‖C‖ ≤ ((9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) * ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (decomp i).total)) ∧
          (∀ (ψout : BlockField S.d S.L (M * n (m' + 1)) (m' + 1) N)
            (hψout : TubeOn (windowOfHistory H Z geo hm hW).bdry (X \ box b0 wb) δ ψout)
            (_hψoutz : ∀ y : BlockAt S n M K (m' + 1), y ∉ Z0 → ∀ i,
              ψout (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ft (a, nd', w') y i)
            (ψ0 : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
            (_hψ0 : ∀ z i, ψ0 ⟨m' + 1, z⟩ i =
              psiZero N (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg hδ hδc hψout z i)
            (Dpp : Region (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW))) (Zp : Region (windowOfHistory H Z geo hm hW).bdry)
            (_hZp : ∀ x, x ∈ Zp.sites ↔ ∃ y ∈ (windowOfHistory H Z geo hm hW).Zk1,
              jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x = jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) y)
            (_hDpp : Dpp.sites = ((windowOfHistory H Z geo hm hW).Z \ (windowOfHistory H Z geo hm hW).Zk1) \ Zp.sites)
            (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
            (_hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y)
            (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
            (_hψk : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y → y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
              ψk (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ((ft (a, nd', w') y i : ℝ) : ℂ))
            (aN : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → ℝ)
            (_haN : ∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y → y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
              ∀ b0 : {b : Σ s, BlockAt S n M K s // nd b}, b0.1 = ⟨m' + 1, y⟩ →
                betaK S.d S.L (m' + 1) β0 * aN (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) =
                  (∑ b ∈ Finset.univ.filter (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
                      pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b = b0),
                    varpi (m' + 1) cs.z (b.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) (m' + 1) b.1.1 ^ 2 /
                      (cs.beta (b.1.1 - 1) * cs.aKer * (S.L : ℝ) ^ (S.d - 2)))⁻¹),
            ((windowData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (windowOfHistory H Z geo hm hW).bdry (windowOfHistory_precedes geo hm hW) (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)).IsReal) ∧
          (∀ p, ((windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)) p).im = 0) ∧
          (InUnionDomainR (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (bgC1 S.d S.L N) 0 Du) ∧
          (‖(β0 : ℂ) * actionRegion0 Zp 0 (psiZeroData (windowOfHistory H Z geo hm hW).bdry ψ0 (0 : Fin N → ℝ))
      (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))‖ < 1 / 4) ∧
          (‖(1 / 2 : ℂ) * (β0 : ℂ) * Dpp.sitePair ((windowOfHistory_precedes geo hm hW).restrictα (alphaZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)))
        (svec (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) ((bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du) - (windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))))
        (svec (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) ((bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du) - (windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))))‖ < 1 / 4) ∧
          (‖(β0 : ℂ) * stTerm Dpp (windowData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (windowOfHistory H Z geo hm hW).bdry (windowOfHistory_precedes geo hm hW) (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ)) Du
        ((windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))) (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)‖ < 1 / 4) ∧
          (‖(β0 : ℂ) * nuTerm Dpp 0 (windowData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (windowOfHistory H Z geo hm hW).bdry (windowOfHistory_precedes geo hm hW) (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))
        ((windowOfHistory_precedes geo hm hW).restrictφ (phiZero (windowOfHistory H Z geo hm hW).bdry (compWeight S.L a₁) ψ0 (0 : Fin N → ℝ))) (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)‖ < 1 / 4) ∧
          (‖Cnat0 a₁ (windowOfHistory_precedes geo hm hW) ψ0 (0 : Fin N → ℝ) Du Zb β0 (varpi (m' + 1) cs.z) aN ψk‖ ≤ Cnat * S.lam (m' + 1) ^ (2 * S.d + 1))))
variable (hQtotv : Qtot = ENNReal.ofReal (ActionConv.constNat N (betaK S.d S.L (m' + 1) β0)
      (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb * Real.exp ((N : ℝ) / 2 * Real.log (betaK S.d S.L (m' + 1) β0) * ((boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb).card : ℝ) + CEt * (D0 : ℝ) ^ S.d + Cnat * S.lam (m' + 1) ^ (2 * S.d + 1) + 4 + ((9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) * ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (decomp i).total))))

include k1 m' hk1p hk1 hm hk1K hk1K1 hmk Z hq r TB ρ hρ Z0 V2 G3 P2 hZ0 hV2 hG3 T Nd nd hNd κc jS c0 rr hc0 hrr Zt δk cen radZ ρt e cb hN2 Φ φ1 φ2 φ3 φ4 φ5 φ7 φ9 Qtot φ8 φ10 hnd hnd0 hZ0g hV2full hMS G h18 h3 hW hk1def hzpos hcpos hc01 pa hpa Fx hFxdef a₁ β0 hβ0 ha₁ D0 hd hk b0 wb hw1 hwD hmD X hXreg hΩ hdata Hbg δ hδ hδc p0 hp0 hradδ Hbg0 Kw δw hWP hKw hOp hsep2 hsmall hρs hRfl hlogβ hxl CEt Cnat hCEt hbx hZ0b Zr hZrs hrdef Zb hZb br Xw hXw Xwin hXwin Xc hXc decomp Kconv Kbg γw M₀ M₁ ε Rhat γ η α α₀ hγ hα₀ hε hγα hflow hKc hKb hγw hsep hβp hμp hB0p hBnp cl hcl wt hvOK hnamedC hQtotv

open Classical in
/-- **The identities of the node variables and of the top field** used for the exact node integral at the Φ-coordinates. -/
theorem window_hbG_fields_cl :
    ∀ (_hv : EuclideanSpace ℝ (Fin N)) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (_a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (_nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (_w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)
      (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
      (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)), (∀ v s y, fld v s y = subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y) → (∀ v y, ft v y = outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
            ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
              (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y) →
    ((∀ (v : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) (p : ↥Nd), (fun v s y => subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y)
      v (p.1.1.1.1 : ℕ) p.1.1.1.2.2 = VarVal.toEuc (v.2.1 p)) ∧
    (∀ (v v' : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) s (y : BlockAt S n M K s), ¬ nd ⟨s, y⟩ →
      subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y =
        subVarField N (Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.1 s y) ∧
    (∀ (v : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3}),
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y.1 = v.1 y) ∧
    (∀ (v : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}),
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y.1 = v.2.2 y) ∧
    (∀ (v v' : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) y, y ∈ V2 → P2 y →
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y =
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).1 par)).2)) y)) := by
  classical
  intro _ par wd cc ro sh _ _ _ fld ft hfld hft
  have hnn := H.F.hnn
  have hG3e : ∀ y, y ∉ G3 := fun y hy => by
    obtain ⟨h1, h2, h3⟩ := (hG3 y).mp hy
    exact h3 (hV2full y h1 h2)
  have hfld' : fld = fun v s y => subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y :=
    funext fun v => funext fun s => funext fun y => hfld v s y
  have hft' : ft = fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
      ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
        (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
          (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y :=
    funext fun v => funext fun y => hft v y
  subst hfld' hft'
  have hV2' : ∀ y, y ∈ V2 → P2 y → y ∉ Z0 := fun y h1 h2 => (hV2 y h1 h2).2.2
  have hxag : ∀ (v v' : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
        ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
          OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))
      (p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A), p ∉ Nd →
      VarVal.toEuc ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 p) =
        VarVal.toEuc ((Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.1 p) := by
    intro v v' p hp
    by_cases hr : p ∈ Set.range κc
    · obtain ⟨⟨C, y | q⟩, rfl⟩ := hr
      · exact (φ4 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2))) C y).symm.trans
          (φ4 (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) C y)
      · exact (φ5 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2))) C q).symm.trans
          (φ5 (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) C q)
    · by_cases hT : p ∈ T
      · exact congrArg VarVal.toEuc ((φ3 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2))) ⟨p, hT⟩).trans
          (φ3 (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) ⟨p, hT⟩).symm)
      · exact congrArg VarVal.toEuc
          ((φ9 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2))) ⟨p, hr, hT, hp⟩).trans
          (φ9 (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) ⟨p, hr, hT, hp⟩).symm)
  have hfldn : ∀ (v : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) (p : ↥Nd), (fun v s y => subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y)
      v (p.1.1.1.1 : ℕ) p.1.1.1.2.2 = VarVal.toEuc (v.2.1 p) := fun v p => by
    show subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 (p.1.1.1.1 : ℕ) p.1.1.1.2.2 = _
    rw [subVarField_var _ p.1 ((hNd p.1).mp p.2).1, φ8 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2))) p]
  have hfldb : ∀ (v v' : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) s (y : BlockAt S n M K s), ¬ nd ⟨s, y⟩ →
      subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y =
        subVarField N (Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.1 s y :=
    fun v v' s y hn => subVarField_congr _ _ s y (fun p hl hs hy => hxag v v' p
      (fun hpN => by
        subst hs
        have hy' := eq_of_heq hy
        subst hy'
        exact hn ((hNd p).mp hpN).2))
  have hftg : ∀ (v : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3}),
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y.1 = v.1 y :=
    fun v y => absurd y.2.2 (hG3e y.1)
  have hftz : ∀ (v : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}),
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y.1 = v.2.2 y := fun v y => by
    rw [outField, dite_eq_left_of_eq_true (eq_true y.2.1),
      merge_apply_zero (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par
        (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2 y.1 y.2.1 y.2.2]
    exact congrFun (φ10 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))) ⟨y.1, y.2.1, y.2.2⟩
  have hftt : ∀ (v v' : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) y, y ∈ V2 → P2 y →
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y =
      outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).1 par)).2)) y := fun v v' y h1 h2 => by
    rw [outField, outField, dite_eq_left_of_eq_true (eq_true (hV2 y h1 h2).1),
      dite_eq_left_of_eq_true (eq_true (hV2 y h1 h2).1),
      merge_apply_out (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par
        (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2 y (hV2 y h1 h2).1 (hV2' y h1 h2) (hV2 y h1 h2).2.1,
      merge_apply_out (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).1 par
        (Φ (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.2 y (hV2 y h1 h2).1 (hV2' y h1 h2) (hV2 y h1 h2).2.1]
    exact (φ2 (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2))) ⟨y, h1, h2⟩).trans
      (φ2 (wd, cc, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) ⟨y, h1, h2⟩).symm
  exact ⟨hfldn, hfldb, hftg, hftz, hftt⟩

open Classical in
/-- **The exact node integral at the Φ-coordinates** (window datum `D` with the data of the point, composed precision `aN`). -/
theorem window_hbG_node_cl :
    ∀ (_hv : EuclideanSpace ℝ (Fin N)) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)
      (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
      (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)), (∀ v s y, fld v s y = subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y) → (∀ v y, ft v y = outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
            ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
              (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y) →
    ∃ (D : Background.BgData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) N)
      (ψk : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → Fin N → ℂ)
      (aN : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1))) → ℝ),
      D.IsReal ∧
      (∀ zb ∈ Zb, 0 < (betaK S.d S.L (m' + 1) β0) * aN zb) ∧
      (∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y →
        y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' → ∀ i,
          ψk (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = ((ft (a, nd', w') y i : ℝ) : ℂ)) ∧
      (∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x ≠ m' + 1 → ∀ i, D.Ψ x i =
        ((fld (a, nd', w') ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
          (jBlock S.d S.L (M * n K) K ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
            (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)) ∧
      (∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x = m' + 1 → ∀ i, D.Ψ x i =
        ((ft (a, nd', w') (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)) ∧
      (∀ x i, D.h x i = 0) ∧ (∀ x, x ∉ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1 → ∀ i, D.Ψ x i = ((cl _hv par wd cc ro sh a nd' w' x i : ℝ) : ℂ)) ∧
      (∀ y : BlockAt S n M K (m' + 1), y ∈ V2 → P2 y → y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
        ∀ b0 : {b : Σ s, BlockAt S n M K s // nd b}, b0.1 = ⟨m' + 1, y⟩ →
          (betaK S.d S.L (m' + 1) β0) * aN (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) =
            (∑ b ∈ Finset.univ.filter (fun b : {b : Σ s, BlockAt S n M K s // nd b} =>
                pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] b = b0),
              varpi (m' + 1) cs.z (b.1.1 - 1) ^ 2 * blockFrac (S.L ^ S.d) (m' + 1) b.1.1 ^ 2 / (cs.beta (b.1.1 - 1) * cs.aKer * (S.L : ℝ) ^ (S.d - 2)))⁻¹) ∧
      ∫⁻ v, ENNReal.ofReal
        ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
            ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
          cs.z (m' + 1) ^ N * gaussDens (cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
            (cs.z (m' + 1) • ft v y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld v m' y')) *
        ∏ j ∈ Finset.Ico k1 m',
          ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
              ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
            cs.z (j + 1) ^ N * gaussDens (cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
              (cs.z (j + 1) • fld v (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                  blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld v j y')) ∂
        ((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
          ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) =
        ENNReal.ofReal (ActionConv.constNat N (betaK S.d S.L (m' + 1) β0) aN Zb *
          Real.exp (-(ActionConv.gaussNat (windowOfHistory H Z geo hm hW |>.windowGenSet
            (windowOfHistory_hyp (g := geo) hm hW)) (varpi (m' + 1) cs.z) D.Ψ (betaK S.d S.L (m' + 1) β0) aN ψk Zb).re)) := by
  classical
  intro hv par wd cc ro sh a nd' w' fld ft hfld hft
  have hnn := H.F.hnn
  have hfld' : fld = fun v s y => subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y :=
    funext fun v => funext fun s => funext fun y => hfld v s y
  have hft' : ft = fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
      ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
        (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
          (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y :=
    funext fun v => funext fun y => hft v y
  subst hfld' hft'
  have hV2' : ∀ y, y ∈ V2 → P2 y → y ∉ Z0 := fun y h1 h2 => (hV2 y h1 h2).2.2
  obtain ⟨hfldn, hfldb, hftg, hftz, hftt⟩ := window_hbG_fields_cl geo cs SD KD hk1p hk1 hm hk1K hk1K1 hmk hq r TB ρ hρ Z0 V2 G3 P2 hZ0 hV2 hG3 T Nd nd hNd κc jS hc0 hrr Zt δk cen radZ e cb hN2 Φ φ1 φ2 φ3 φ4 φ5 φ7 φ9 Qtot φ8 φ10 hnd hnd0 hZ0g hV2full hMS G h18 h3 hW hk1def hzpos hcpos hc01 pa hpa Fx hFxdef hβ0 ha₁ hd hk b0 wb hw1 hwD hmD hXreg hΩ hdata Hbg hδ hδc hp0 hradδ Hbg0 hWP hKw hOp hsep2 hsmall hρs hRfl hlogβ hxl hCEt hbx hZ0b Zr hZrs hrdef Zb hZb br Xw hXw Xwin hXwin Xc hXc decomp hγ hα₀ hε hγα hflow hKc hKb hγw hsep hβp hμp hB0p hBnp cl hcl wt hvOK hnamedC hQtotv hv par wd cc ro sh a nd' w' _ _
    (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hβG : 0 < betaK S.d S.L (m' + 1) β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hZ0box : ∀ s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (congrArg (· * n (m' + 1)) hMS) (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) s) ∈
        H.Zzero (m' + 1) Z →
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm s) ∈ Z0 := by
    intro s hs
    have h1 := (hbx s).mpr hs
    have h2 := (mem_fib_cast hnn hm (le_refl (m' + 1))
      (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm s)) s).mpr rfl
    rw [mem_fib] at h2
    exact ((hZ0b _).mpr (by rw [mem_boxFinset]; rw [← h2]; exact h1)).2
  obtain ⟨D, ψk, Zb', aN, hDreal, hZb', hpos, hψkD, hR1, hR2, hDh, hD0, haNf, hint⟩ :=
    window_node_integral_exact_collar geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2 hV2' hZ0g hG3 Nd hNd
      (fun j => cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) cs.z (fun j _ _ => hcpos j)
      (fun s _ _ => hzpos s) _ _ hfldn hfldb hftg hftz hftt pa hpa Fx hFxdef (a, nd', w') hMS G h18 h3 hW hk1def
      hZ0box (betaK S.d S.L (m' + 1) β0) hβG (cl hv par wd cc ro sh a nd' w')
      (hcl hv par wd cc ro sh a nd' w')
  have hZbe : Zb = Zb' := Finset.ext fun zb => by rw [hZb', hZb]
  subst hZbe
  exact ⟨D, ψk, aN, hDreal, hpos, hψkD, hR1, hR2, hDh, hD0, haNf, hint⟩

open Classical in
/-- **The composed precision of the top Gaussian blocks is positive**: `const♮_{β_k}(ϰ̄_z; Z_b) > 0`. -/
theorem window_hbG_cI_cl :
    0 < ActionConv.constNat N (betaK S.d S.L (m' + 1) β0)
      (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb := by
  classical
  have hnn := H.F.hnn
  have hL2 : 2 ≤ S.L := H.F.ok.two_le_L
  have hβG : 0 < betaK S.d S.L (m' + 1) β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have hBx : ∀ y : BlockAt S n M K (m' + 1), y ∈ Z0 ↔
      torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y ∈ box b0 wb := by
    intro y
    constructor
    · intro hy
      have hv : y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) :=
        ZBlk_mem_Vblk hm Z y (gaussBlocks_zblk hm Z (hZ0g hy))
      exact mem_boxFinset.mp ((hZ0b y).mp ⟨hv, hy⟩)
    · intro h
      exact ((hZ0b y).mpr (mem_boxFinset.mpr h)).2
  have hZ0box : ∀ s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (congrArg (· * n (m' + 1)) hMS) (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) s) ∈
        H.Zzero (m' + 1) Z →
      jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm s) ∈ Z0 := by
    intro s hs
    have h1 := (hbx s).mpr hs
    have h2 := (mem_fib_cast hnn hm (le_refl (m' + 1))
      (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hm).symm s)) s).mpr rfl
    rw [mem_fib] at h2
    exact (hBx _).mpr (by rw [← h2]; exact h1)
  have hZb' : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1),
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
        zb = torusCast (blk_eq_top hnn hm (le_refl (m' + 1))).symm y := by
    intro zb
    rw [hZb]
    constructor
    · rintro ⟨y, hy1, hy2, hy3, rfl⟩; exact ⟨y, hy3, (hV2 y hy1 hy2).2.2, rfl⟩
    · rintro ⟨y, hy1, hy2, rfl⟩
      obtain ⟨h1, h2⟩ := hV2full y hy1 hy2
      exact ⟨y, h1, h2, hy1, rfl⟩
  have hWh := windowOfHistory_hyp (g := geo) hm hW
  obtain ⟨-, -, -, -, -, -, -, -, -, hD7, -⟩ := window_region_decomp hMS G h18 h3 hm hW hk1def geo
    (windowOfHistory H Z geo hm hW) hWh (fun q => windowOfHistory_full_Ω H Z geo hm hW q)
    (windowOfHistory_Z H Z geo hm hW) (by rw [windowOfHistory_Zk1, hk1def]) Z0 (box b0 wb) hZ0box hBx Zb hZb'
  exact constNat_pos hβG (fun z hz => compWeightZ_pos ha₁ hL2 _ (hD7 z hz))

open Classical in
/-- **The sum of the main actions of the pieces at the point** (LFR (2.15′)): `∑ 𝒜 = Re(β_k A_{X_win}) - Re C`, `‖C‖ ≤ Ckk`. -/
theorem window_hbG_sum_cl :
    ∀ (hv : EuclideanSpace ℝ (Fin N)) (_hok : hvOK hv) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)
      (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
      (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)), (∀ v s y, fld v s y = subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y) → (∀ v y, ft v y = outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
            ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
              (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y) → wd ∈ ({o : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 |
            ∀ i, ‖o i - cen par i‖ < radZ} ×ˢ
          ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
            (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
              ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ
            {w3 : ∀ t : ↥T, VarVal N t.1.1.isSpin |
              ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| < r (jS t.1)})) → (TB m' Z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)),
            TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1)) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (Nat.lt_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))) →
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1 hv * wt (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1 ≠ 0 →
    ∀ (Du : BgData (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) N) (_hDuh : ∀ x i, Du.h x i = 0)
          (_hDu0 : ∀ x, x ∉ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1 → ∀ i, Du.Ψ x i = ((cl hv par wd cc ro sh a nd' w' x i : ℝ) : ℂ))
          (_hDu1 : ∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x ≠ m' + 1 → ∀ i, Du.Ψ x i =
            ((fld (a, nd', w') ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x) (jBlock S.d S.L (M * n K) K ((windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x)
              (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ))
          (_hDu2 : ∀ x ∈ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).Ω 1, (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)).layerIndex x = m' + 1 → ∀ i, Du.Ψ x i =
            ((ft (a, nd', w') (jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hm).symm x)) i : ℝ) : ℂ)), ∃ C : ℂ, (mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
          (locRH_rem (m' + 1) Z) (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) hv +
        ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∑ c : ↥(H.parts (j.1 + 1) P.1),
            mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
              (locComp_mem H (Nat.le_trans (Finset.mem_Ico.mp j.2).2 (Nat.le_of_succ_le hm)) c.1)
              (Nat.le_trans (Finset.mem_Ico.mp j.2).2 (Nat.le_of_succ_le hm)) cs (locRH_rem (j.1 + 1) c.1)
              (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1)) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (Nat.lt_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1)) hv) =
      ((β0 : ℂ) * actionRegionC Xwin (compWeight S.L a₁) 0 Du (bgField (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) (compWeight S.L a₁) 0 Du)).re - C.re ∧
      ‖C‖ ≤ ((9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) * ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (decomp i).total) := by
  intro hv hok par wd cc ro sh a nd' w' fld ft hfld hft hw hTBp hK Du hDuh hDu0 hDu1 hDu2
  exact (hnamedC hv hok par wd cc ro sh a nd' w' fld ft hfld hft hw hTBp hK Du hDuh hDu0 hDu1 hDu2).1

open Classical in
/-- **The top field of the point is the field of the removed-zero merge off `Z₀`.** -/
theorem window_hbG_psiz_cl :
    ∀ (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0), ∀ y : BlockAt S n M K (m' + 1), y ∉ Z0 → ∀ i,
      (fun (z : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))) (i : Fin N) =>
        outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (0, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2))
          (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))) z) i) (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y) i = (fun y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) y) y i := by
  classical
  intro par wd cc ro sh a nd' w' y hy i
  simp only [torusCast_cast_symm]
  by_cases hV : y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)
  · simp [outField, remZeroMerge, hV, hy]
  · simp [outField, hV]

open Classical in
/-- **The regions of the removed-kernel quotient**: `Z_{k₁}^+` (block closure of `Z_{k₁}` on `𝔹_k(U_k)`) and `D = (Z ∖ Z_{k₁}) ∖ Z_{k₁}^+`, a region of `X_win`. -/
theorem window_hbG_regions_cl :
    ∃ (Zp : Region (windowOfHistory H Z geo hm hW).bdry) (Dpp : Region (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW))),
      (∀ x, x ∈ Zp.sites ↔ ∃ y ∈ (windowOfHistory H Z geo hm hW).Zk1,
        jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x = jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) y) ∧
      Dpp.sites = ((windowOfHistory H Z geo hm hW).Z \ (windowOfHistory H Z geo hm hW).Zk1) \ Zp.sites ∧
      Dpp.sites ⊆ Xwin.sites := by
  classical
  have hWh := windowOfHistory_hyp (g := geo) hm hW
  obtain ⟨Zp, hZp, -⟩ := exists_region_blockClosure (windowOfHistory H Z geo hm hW).bdry hk
    (windowOfHistory H Z geo hm hW).Zk1 (fun y hy => windowOfHistory_bdryCover geo hm hW y
      (windowOfHistory_hZ (g := geo) hm hW hy))
  obtain ⟨Dw, hDws, hDwiff⟩ := exists_region_window geo hm H.F.ok.two_le_L (fun j _ _ => geo.hRlow j) hk1p hk1
    (windowOfHistory H Z geo hm hW) hWh (fun q => windowOfHistory_full_Ω H Z geo hm hW q)
    (windowOfHistory_Z H Z geo hm hW) (by rw [windowOfHistory_Zk1, hk1def])
  obtain ⟨Dpp, hDpp0⟩ := exists_region_sdiff (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) Dw Zp.sites
    (blockClosure_isBlockUnion (windowOfHistory H Z geo hm hW).Zk1 Zp.sites hZp)
  have hDpp : Dpp.sites = ((windowOfHistory H Z geo hm hW).Z \ (windowOfHistory H Z geo hm hW).Zk1) \ Zp.sites := by
    rw [hDpp0, hDws]
  have hXwins : Xwin.sites = (windowOfHistory H Z geo hm hW).Z \ (windowOfHistory H Z geo hm hW).Zk1 := by
    rw [← hDws]; ext x; rw [hXwin, hDwiff]
  exact ⟨Zp, Dpp, hZp, hDpp, by rw [hDpp, hXwins]; exact Finset.sdiff_subset⟩

end Core

end Balaban.LargeField
