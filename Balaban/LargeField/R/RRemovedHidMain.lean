/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidCoreThm
public import Balaban.LargeField.R.RRemovedHidAux
public import Balaban.LargeField.R.RRemovedHidRegroup
public import Balaban.LargeField.R.RRemovedRegroupCanon

/-!
# The composition inputs `hid` and `hsupp` of the removed-kernel window integral (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4.  `exists_window_hid`: the measure preserving regrouping
`Θ` (`exists_regroup_shell`) together with the two composition inputs of
`removedKernel_kerBound_of_window`: `hid` (the integral over the variables `Jv` integrated first is at most
`Core · e^{B_w} e^{L_c} Q_b`) and `hsupp` (it vanishes outside the product of the three window sets).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Main

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
theorem exists_window_hid {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
          (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par))) :
    ∃ (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
      (Θ : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) ×
          (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
            (locOp geo cs SD KD hH lab (m' + 1) hm Z).A ×
            OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0) ≃ᵐ
        (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 ×
            (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
          ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) ×
            ((OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
              OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
                (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧
                  ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
                (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)) ×
                OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0))))
      (parC : (∀ t : ↥T, VarVal N t.1.1.isSpin) →
        ∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
          OutPar N R (H.localHistory M K k1 C.2.1) k1)
      (E3 : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
        Set (∀ t : ↥T, VarVal N t.1.1.isSpin)),
      MeasurePreserving Θ
        ((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
          (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1))).prod
          ((subMeasure N (H.localHistory M K (m' + 1) Z) (m' + 1)
            (locOp geo cs SD KD hH lab (m' + 1) hm Z).A).prod
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))
        (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)).prod
          ((outPartMeasure N V2 P2).prod
            (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin))).prod
          ((Measure.pi fun C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)) =>
            (outPartMeasure N (Vblk R (H.localHistory M K k1 C.2.1) k1)
              (ZBlk (H.localHistory M K k1 C.2.1) k1)).prod
            (subMeasure N (H.localHistory M K k1 C.2.1) k1
              (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)).prod
            (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
              (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
                (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧
                  ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))))) ∧
      (∀ par, (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin) (E3 par) ≤ 1) ∧
      (∀ hv g par w c, ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
              (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
                (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧
                  ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) ≤
        (if g ∈ l1Ball (GIdx S n M K N) then
          ∏ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            (locOp geo cs SD KD hH lab k1 hk1K C.2.1).T.absW
              (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC w.2.2 C)) (c C).2 hv g
         else ⊤) *
        ENNReal.ofReal (Real.exp bw0 * Real.exp Lc * Qb)) ∧
      (∀ hv g par w c,
        w ∉ ({o : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 |
            ∀ i, ‖o i - cen par i‖ < radZ} ×ˢ
          ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
            (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
              ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ E3 par)) →
        ∫⁻ j, F hv g par (Θ.symm (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
              (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
                (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧
                  ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) = 0) := by
  classical
  have hz0 : ∀ k, 0 ≤ cs.z (k + 1) := fun k => (hzpos _).le
  have hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2) := fun k => (hcpos k).le
  have hscale_nd : ∀ s (y : BlockAt S n M K s), nd ⟨s, y⟩ → k1 < s := by
    intro s y h
    cases s with
    | zero => exact absurd h (hnd0 y)
    | succ j => obtain ⟨h1, -, -⟩ := (hnd j y).mp h; omega
  obtain ⟨hTo, hTi, hTm⟩ := canonT_spec geo cs SD KD hmk hm hq T hT
  have hNj : ∀ p ∈ Nd, k1 < ((p.1.1.1 : Fin (m' + 1)) : ℕ) := fun p hp =>
    hscale_nd _ _ ((hNd p).mp hp).2
  have hTk : ∀ p ∈ T, ((p.1.1.1 : Fin (m' + 1)) : ℕ) = k1 := fun p hp => ((hT p).mp hp).1
  have hNT : ∀ p ∈ Nd, p ∉ T := fun p hp hpT => by
    have := hNj p hp; have := hTk p hpT; omega
  have hG3z : ∀ y ∈ G3, ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y := fun y hy =>
    gaussBlocks_zblk hm Z ((hG3 y).mp hy).1
  have hG3' : ∀ y ∈ G3, y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) := fun y hy =>
    ⟨ZBlk_mem_Vblk hm Z y (hG3z y hy), hG3z y hy, ((hG3 y).mp hy).2.1, ((hG3 y).mp hy).2.2⟩
  obtain ⟨κc, Θ, hinj, hκ1, hκ2, hMP, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ :=
    exists_regroup_shell geo cs SD KD hmk hm hq Z0 V2 P2 hZ0 hV2 T hTo hTi Nd hNj hNT G3 hG3'
  have hparCx := exists_parC geo cs SD KD hmk hm hq T hTm κc hκ1
  have hparC := hparCx.choose_spec
  have hTBx := exists_window_TB (H := H) (M := M) (N := N) (fun j => 3 * (S.d : ℝ) * S.L * cs.delta j)
  have hcstx := exists_window_cst (H := H) (M := M) cs
  have hρrx := exists_window_rho geo cs SD KD (hH := hH) (lab := lab) hm hq
  have hjSx := shell_of_tubes geo cs SD KD hk1 hm hq nd hnd
    (fun j => 3 * (S.d : ℝ) * S.L * cs.delta j) hTBx.choose hTBx.choose_spec hρrx.choose hρrx.choose_spec κc hκ1 hκ2
  have hTnr : ∀ t ∈ T, t ∉ Set.range κc := by
    rintro t ht ⟨⟨C, y | q⟩, hκ⟩
    · refine hTo C y ((hκ1 C y) ▸ (κc ⟨C, Sum.inl y⟩).2) ?_
      convert ht using 1
      exact (Subtype.ext (hκ1 C y)).symm.trans hκ
    · refine hTi C q ((hκ2 C q) ▸ (κc ⟨C, Sum.inr q⟩).2) ?_
      convert ht using 1
      exact (Subtype.ext (hκ2 C q)).symm.trans hκ
  have hjT := fun (t : ↥T) => ((hjSx.choose_spec t.1).resolve_left (hTnr t.1 t.2)).resolve_left
    (fun h => hNT t.1 ((hNd t.1).mpr h) t.2)
  have hbw0' : hcstx.choose m' Z + ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ∑ c : ↥(H.parts (j.1 + 1) P.1), hcstx.choose j.1 c.1 ≤ bw0 := by
    simp only [hcstx.choose_spec]; exact hbw0
  have hE3vol : ∀ par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1),
      (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin)
        {w3 : ∀ t : ↥T, VarVal N t.1.1.isSpin |
          ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| < 3 * (S.d : ℝ) * S.L * cs.delta (hjSx.choose t.1)} ≤ 1 := by
    intro par
    refine pi_shell_le_one hN2 (fun t : ↥T => t.1.1.isSpin) (fun t => ?_)
      (fun t => 3 * (S.d : ℝ) * S.L * cs.delta (hjSx.choose t.1))
      (fun t => (hrad _ (hjT t).1 (hjT t).2.1).1) (fun t => (hrad _ (hjT t).1 (hjT t).2.1).2.1)
      (fun t => (hrad _ (hjT t).1 (hjT t).2.1).2.2)
    unfold InternalVars.isSpin
    exact decide_eq_false (fun h => by have := hTk t.1 t.2; omega)
  have hcore := window_hid_core geo cs SD KD hk1p hk1 hm hk1K hk1K1 hmk hq hQuiet hz0 hc hδ hdL hβ haw hμ
    (fun j => 3 * (S.d : ℝ) * S.L * cs.delta j) (fun _ => rfl) hTBx.choose hTBx.choose_spec hcstx.choose hcstx.choose_spec bw0 hbw0' hρrx.choose hρrx.choose_spec
    Z0 V2 G3 P2 hZ0 hV2 hG3 T Nd nd hNd κc hjSx.choose hjSx.choose_spec hTnr hNT t s z w ht hs hz hw hc0 hr Zt δk ht_def
    cen radZ e cb hc0s hcb hcbZ0 Qb hquot hzpos hcpos hN2 hrad hnd hnd0 hZ0g hκ2 hparCx.choose hparC wz hLc
    hwz1 hwz2 hQb F hF Θ.symm
    (fun θ y => by have := e1 (Θ.symm θ) y; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ y => by have := e2 (Θ.symm θ) y; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ t => by have := e3 (Θ.symm θ) t; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ C y => by have := e4 (Θ.symm θ) C y; rw [Θ.apply_symm_apply] at this; exact this)
    (fun θ C q => by have := e5 (Θ.symm θ) C q; rw [Θ.apply_symm_apply] at this; exact this)
    hG3z
    (fun θ y => by have := e6 (Θ.symm θ) y; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ y => by have := e7 (Θ.symm θ) y; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ t => by have := e8 (Θ.symm θ) t; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ t => by have := e9 (Θ.symm θ) t; rw [Θ.apply_symm_apply] at this; exact this.symm)
    (fun θ => by have := e10 (Θ.symm θ); rw [Θ.apply_symm_apply] at this; exact this.symm)
  exact ⟨κc, Θ, hparCx.choose, fun _ => {w3 | ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| <
    3 * (S.d : ℝ) * S.L * cs.delta (hjSx.choose t.1)}, hMP, hE3vol, hcore.1, hcore.2⟩

end Main

end Balaban.LargeField
