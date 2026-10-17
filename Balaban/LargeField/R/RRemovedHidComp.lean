/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidMain
public import Balaban.LargeField.R.RRemovedWindowInst
public import Balaban.LargeField.R.RRemovedWindowAncCore

/-!
# The kernel bound of the removed outcome with `hid` and `hsupp` discharged (W934)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4.  `removedKernel_kerBound_of_hid`: `removedKernel_kerBound_of_window`
with the composition inputs supplied by `exists_window_hid` (`hid`, `hsupp`, the set `E₃`), `hcore` by
`hcore_of_anc`, `bw` the constant `bw₀`, `frac` the constant `Q_b`, and `hvol`, `hnZ`, `hnT` as in
`removedKernel_kerBound_of_window_inst`.  The support set is replaced by a measurable superset
(`toMeasurable`) of the same measure, so no measurability of `E₃` is needed.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal ActionConv

section Comp

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
theorem removedKernel_kerBound_of_hid {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (hk1K : k1 ≤ K) (hk1K1 : k1 + 1 ≤ K) (hmk : k1 < m' + 1) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hQuiet : ∀ j, k1 ≤ j → j ≤ m' → ∀ c' : H.Comp (j + 1), H.Desc (j + 1) (m' + 1) c' Z →
      IsQuiet (H.locRH (j + 1) c') j c'.1)
    (hzpos : ∀ s, 0 < cs.z s) (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 ≤ cs.delta k) (hdL : 1 ≤ S.d * S.L) (hβ : ∀ k, 0 ≤ cs.beta k)
    (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct k) (hN2 : 2 ≤ N)
    (hrad : ∀ j, k1 ≤ j → j ≤ m' → 0 < 3 * (S.d : ℝ) * S.L * cs.delta j ∧
      3 * (S.d : ℝ) * S.L * cs.delta j ≤ 1 / 2 ∧ cShell N * (3 * (S.d : ℝ) * S.L * cs.delta j) ≤ 1)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1))) (P2 : BlockAt S n M K (m' + 1) → Prop)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0)
    (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
    (hG3 : ∀ y, y ∈ G3 ↔ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
      ¬ (y ∈ V2 ∧ P2 y))
    (T : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) [Fintype ↑T]
    (hT : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A, p ∈ T ↔
      ((p.1.1.1.1 : ℕ) = k1 ∧ p.1.1.2.1 = VarKind.large ∧
        ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
          (y : OutIdx (K := K) (M := M) R C.2.1), p.1 ≠
            (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar hk1K1 C.1.1 C.2.2 y).1.1,
              (oldVar hk1K1 C.1.1 C.2.2 y).1.2.1, (oldVar hk1K1 C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hm (mem_ancFin.mp C.1.2) (oldVar hk1K1 C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1))))
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) [Fintype ↑Nd]
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (t s z w : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A → ℝ)
    {c0 : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ℝ}
    {r : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 →
      OutRest N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 → ℝ}
    (ht : ∀ o x, 0 ≤ t o x ∧ t o x ≤ 1) (hs : ∀ o x, 0 ≤ s o x ∧ s o x ≤ 1)
    (hz : ∀ o x, 0 ≤ z o x ∧ z o x ≤ 1) (hw : ∀ o x, 0 ≤ w o x ∧ w o x ≤ 1)
    (hc0 : ∀ o, 0 ≤ c0 o) (hr : ∀ w y, 0 ≤ r w y)
    (Zt : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ)
    (ht_def : ∀ o x, t o x = chiTilde (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk
      (outField N o))
    (cen : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0} →
      EuclideanSpace ℝ (Fin N)) (radZ : ℝ) {ρ : Type}
    (e : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ρ → EuclideanSpace ℝ (Fin N))
    (cb : ρ → BlockAt S n M K (m' + 1))
    (hc0s : ∀ (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (oz : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1)),
      c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) ≠ 0 →
      ∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
        y ∈ Z0}, ‖oz ⟨i.1, i.2.1, hZ0 _ i.2.1 i.2.2⟩ - cen par i‖ < radZ)
    (hcb : ∀ (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (oz : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1)) c,
      outField N (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) (cb c) = e par c)
    (hcbZ0 : ∀ c, cb c ∉ Z0) (Qb : ℝ) (hQb : 0 < Qb)
    (hquot : ∀ (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (oz : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1)),
      (∀ i : {y : BlockAt S n M K (m' + 1) //
        y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0},
        ‖oz ⟨i.1, i.2.1, hZ0 _ i.2.1 i.2.2⟩ - cen par i‖ < radZ) →
      (∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
        (∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y},
          ψ i.1 = oz ⟨i.1, (hV2 i.1 i.2.1 i.2.2).1, (hV2 i.1 i.2.1 i.2.2).2.1⟩) ∧
        (∀ c, ψ (cb c) = e par c) ∧
        ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ) →
      (∀ y : {y : BlockAt S n M K (m' + 1) //
          y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
            newOutP (H.localHistory M K (m' + 1) Z) m' y},
        y.1 ∉ Z0 → |‖mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par ⟨y.1, y.2.1⟩‖ ^ 2 - 1| <
          3 * (S.d : ℝ) * S.L * cs.delta m') →
      c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 r
          (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) ≤ Qb)
    (wz : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} → ℝ) {Lc : ℝ}
    (hLc : Real.exp Lc = ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2))
    (hwz1 : ∀ i, Real.pi ≤ wz i)
    (hwz2 : ∀ i, cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2) * cs.z (m' + 1) ^ 2 ≤ 2 * wz i)
    (bw0 : ℝ)
    (hbw0 : (cs.Cb * Real.log (cs.beta m') + cs.Cb * cs.B0) *
        volScale S (m' + 1) {z | z ∈ (H.localHistory M K (m' + 1) Z).Z (m' + 1) ∧
          z ∉ (H.localHistory M K (m' + 1) Z).Z m'} +
      ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∑ c : ↥(H.parts (j.1 + 1) P.1),
          (cs.Cb * Real.log (cs.beta j.1) + cs.Cb * cs.B0) *
            volScale S (j.1 + 1) {z | z ∈ (H.localHistory M K (j.1 + 1) c.1).Z (j.1 + 1) ∧
              z ∉ (H.localHistory M K (j.1 + 1) c.1).Z j.1} ≤ bw0)
    (F : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) →
      OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) ×
        (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).A ×
          OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0) → ℝ≥0∞)
    (hF : ∀ hv g par oz x w', F hv g par (oz, x, w') = ENNReal.ofReal
      (c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) *
        (toRKernel (H.localHistory M K (m' + 1) Z) (m' + 1)
            (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K t s z w
            (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
              (w', (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
                (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)).2)) x hv *
          Real.exp ((locOp geo cs SD KD hH lab (m' + 1) hm Z).T.b
            (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
              (w', (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
                (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)).2)) x hv g).re) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 r
          (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)))
    (ok : S.Ok) (hx : 1 ≤ S.lam (m' + 1)) {Cvol CEt CE' Cnat : ℝ} {D : ℕ}
    (hCE' : 0 ≤ CE') (hCvol : 0 ≤ Cvol)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        (D : ℝ) ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR)
    (u : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ℝ) (hu : ∀ o, 0 ≤ u o) (hu1 : ∀ o, u o ≤ 1)
    (hb : ∀ (o o' : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1)) (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).A)
      (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
      (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 o).2 = (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 o').2 →
        ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).T.b o x hv g = ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).T.b o' x hv g)
    (htm : Measurable fun p : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) × SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).A => t p.1 p.2)
    (hsm : Measurable fun p : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) × SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).A => s p.1 p.2)
    (hzm : Measurable fun p : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) × SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).A => z p.1 p.2)
    (hwm : Measurable fun p : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) × SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) ((locOp geo cs SD KD hH lab (m' + 1) hm Z)).A => w p.1 p.2)
    (hum : Measurable u) (hc0m : Measurable c0)
    (hrm : Measurable fun q : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × OutRest N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 => r q.1 q.2)
    {β0 A0 C6 : ℝ} (hβ0 : 0 < β0) (hC6 : 0 ≤ C6) (hA0 : 0 < A0)
    (hδk : δk = betaK S.d S.L (m' + 1) β0 ^ (-(1 / 2 : ℝ)) * (A0 * S.lam (m' + 1) ^ S.p0))
    (hradZ : radZ = C6 * betaK S.d S.L (m' + 1) β0 ^ (-(1 / 2 : ℝ)) * (A0 * S.lam (m' + 1) ^ S.p0))
    (parT : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} →
      {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} ⊕ ρ)
    (rk : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} → ℕ)
    (hrk : ∀ i j, parT i = Sum.inl j → rk j < rk i)
    (hreg : ∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y},
      BlockSub (S := S) (n := n) (M := M) (K := K) (m' + 1) i.1 (tildeRegion (H.localHistory M K (m' + 1) Z) (m' + 1) Zt))
    (hregc : ∀ c, BlockSub (S := S) (n := n) (M := M) (K := K) (m' + 1) (cb c)
      (tildeRegion (H.localHistory M K (m' + 1) Z) (m' + 1) Zt))
    (hadj : ∀ i j, parT i = Sum.inl j → AdjT i.1 j.1)
    (hadjc : ∀ i c, parT i = Sum.inr c → AdjT i.1 (cb c))
    (hw0 : ∀ i, 0 ≤ wz i) (hw2 : ∀ i, wz i ≤ 2 * betaK S.d S.L (m' + 1) β0)
    (hcc : Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
      (max 3 C6) ^ N * A0 ^ N) ≤ Cvol)
    {Fz Ck : ℝ}
    (hFz : Fz = (N : ℝ) / 2 * Real.log (betaK S.d S.L (m' + 1) β0) *
      Nat.card {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})
    (hFr : Real.log Qb ≤ Fz + CEt * (D : ℝ) ^ S.d + Cnat * S.lam (m' + 1) ^ (2 * S.d + 1) + 4 + Ck)
    {N₀ k' : ℕ} [NeZero N₀] (b0 : Torus S.d (N₀ * S.L ^ (k' - k'))) (wb : Fin S.d → ℕ)
    (hwD : ∀ i, wb i ≤ D)
    (hZcard : Nat.card {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0} ≤
      (boxFinset (L := S.L) (N₀ := N₀) (k := k') b0 wb).card)
    (G : S.Good) (hTn : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j)
    (hrem : Z.1 ∈ H.rem (m' + 1))
    (hTcard : (Nat.card {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} : ℝ) ≤
      BudgetConsts.cubeVol S Z.1.card)
    (EZ : ℝ) (hEZ : EZ ≤ (CE' * S.lam (m' + 1) + CE') * ((S.M : ℝ) * S.crit (m' + 1)) ^ S.d)
    (B : BudgetConsts) (κK : ∀ k, H.Comp k → ℝ)
    (hκs : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), κs k (H.localHistory M K (k + 1) Z') =
      B.kappaStep S k (Z'.1 ∩ H.newCubes (k + 1)).card (H.outCubes k Z').card)
    (hkept : ∀ (k : ℕ) (hk : k ≤ K) (Z : H.Comp k), IsKept H k Z →
      PkgBound (H.localHistory M K k Z) k (locOp geo cs SD KD hH lab k hk Z) (κK k Z))
    {κpre : ℝ}
    (hκ : κpre ≤ ∑ C ∈ H.ancFin k1 (m' + 1) Z, H.kappa B κK k1 C - (bw0 + Ck)) :
    KerBound (H.localHistory M K (m' + 1) Z) (m' + 1) (removedKernel (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (locOp geo cs SD KD hH lab (m' + 1) hm Z) t s z w u c0 r EZ
      (fun o x => (ht o x).1) (fun o x => (hs o x).1) (fun o x => (hz o x).1)
      (fun o x => (hw o x).1) hu hc0 hr htm hsm hzm hwm hum hc0m hrm)
      (κpre - S.CR * S.lam (m' + 1) ^ (2 * S.d + 1)) := by
  classical
  subst hradZ
  obtain ⟨κc, Θ, parC, E3, hMP, hE3, hid, hsupp⟩ := exists_window_hid geo cs SD KD hk1p hk1 hm hk1K hk1K1
    hmk hq hQuiet hzpos hcpos hδ hdL hβ haw hμ hN2 hrad nd hnd hnd0 Z0 V2 G3 P2 hV2 hZ0g hG3 T hT Nd hNd
    hZ0 t s z w ht hs hz hw hc0 hr Zt δk ht_def cen _ e cb hc0s hcb hcbZ0 Qb hQb hquot wz hLc hwz1 hwz2
    bw0 hbw0 F hF
  have hlam : 0 < S.lam (m' + 1) := by linarith
  have hβk : 0 < betaK S.d S.L (m' + 1) β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  refine removedKernel_kerBound_of_window (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
    (locOp geo cs SD KD hH lab (m' + 1) hm Z) EZ (fun o x => (ht o x).1) (fun o x => (hs o x).1)
    (fun o x => (hz o x).1) (fun o x => (hw o x).1) hu hc0 hr htm hsm hzm hwm hum hc0m hrm ok hx
    (D0 := (D : ℝ)) (nZ0 := (Nat.card {y : BlockAt S n M K (m' + 1) //
      y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0} : ℝ))
    (nTree := (Nat.card {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} : ℝ)) hCE' (by positivity)
    hCvol hCR hu1 hb
    (μW := (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)).prod
      ((outPartMeasure N V2 P2).prod (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin)))
    Θ hMP
    (fun par => toMeasurable ((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (· ∈ Z0)).prod ((outPartMeasure N V2 P2).prod (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin)))
      ({o | ∀ i, ‖o i - cen par i‖ < C6 * betaK S.d S.L (m' + 1) β0 ^ (-(1 / 2 : ℝ)) *
          (A0 * S.lam (m' + 1) ^ S.p0)} ×ˢ
        ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
          (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
            ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ E3 par)))
    (fun par => measurableSet_toMeasurable _ _) F hF
    (fun hv g par w c => if g ∈ l1Ball (GIdx S n M K N) then
          ∏ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            (locOp geo cs SD KD hH lab k1 hk1K C.2.1).T.absW
              (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC w.2.2 C)) (c C).2 hv g
         else ⊤)
    (fun _ _ _ _ _ => bw0) (fun _ _ _ _ _ => Qb) (Bw := bw0) (Ck := Ck) (Fr := Real.log Qb) (Fz := Fz)
    (Lc := Lc)
    (κcore := ∑ C ∈ H.ancFin k1 (m' + 1) Z, H.kappa B κK k1 C) (κpre := κpre)
    (fun hv g par w c => hid hv g par w c)
    (fun hv g par w c hw' => hsupp hv g par w c (fun h => hw' (subset_toMeasurable _ _ h)))
    (fun _ _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => hQb.le)
    (fun _ _ _ _ _ _ => (Real.exp_log hQb).ge) ?_ ?_ hFr hEZ ?_ ?_ hκ
  · intro hv g hg par w'
    have h := hcore_of_anc geo cs SD KD hH lab (fun k => hzpos _) (fun k => (hcpos k).le) B κK hκs hkept
      hmk hm Z (fun _ w => parC w.2.2) hv g hg par w'
    refine Eq.trans_le (lintegral_congr fun c => ?_) h
    simp only [hg, ↓reduceIte]
  · intro par
    rw [measure_toMeasurable]
    have h := window_hvol_of_groups (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (by omega) (hE3 par)
      (cen par) Zt δk V2 P2 (e par) cb parT rk hrk hreg hregc hadj hadjc S.p0 hβk hC6 hA0 hlam hδk wz hw0
      hw2 hcc hLc hFz
    exact h
  · exact hTcard.trans (removed_cubeVol_le G hTn hH hm hrem)
  · exact (Nat.cast_le.2 hZcard).trans (card_boxFinset_le b0 wb hwD)

end Comp

end Balaban.LargeField
