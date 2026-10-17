/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidPt
public import Balaban.LargeField.R.RRemovedHidCover
public import Balaban.LargeField.R.SmallFactorChi

/-!
# The pointwise bound of the window integrand in the coordinates of the regrouping (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (1), (3), (5), (6).  `window_pt`: at a point of the
integration variables given by its coordinates (the output values `oz`, the variables `x`, the inner outputs
`w'`, the shell outputs `ro` and the shell variables `sh` of the regrouping), the integrand is at most
`Q_b e^{B_w}` times the Gaussian products, the shell indicators `I_O(ro) I_S(sh)` and the core weights, once
`ψ_k↾Z₀` and the tree group are in their balls; and it vanishes unless they are, and the window variables `x↾T`
are in their shells.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section At

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- If the integrand is non-zero at one value of the exponent it is non-zero at any other. -/
theorem ofReal_ne_zero_swap {c0 T D e1 e2 : ℝ} (hc : 0 ≤ c0) (hT : 0 ≤ T) (hD : 0 ≤ D) (h2 : 0 < e2)
    (h : ENNReal.ofReal (c0 * (T * e1) / D) ≠ 0) :
    ENNReal.ofReal (c0 * (T * e2) / D) ≠ 0 := by
  intro h0
  apply h
  rw [ENNReal.ofReal_eq_zero] at h0 ⊢
  rcases hc.eq_or_lt with hc0 | hc0
  · rw [← hc0]; simp
  rcases hT.eq_or_lt with hT0 | hT0
  · rw [← hT0]; simp
  rcases hD.eq_or_lt with hD0 | hD0
  · rw [← hD0]; simp
  exfalso
  have : 0 < c0 * (T * e2) / D := by positivity
  linarith

open Classical in
theorem window_pt {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hQuiet : ∀ j, k1 ≤ j → j ≤ m' → ∀ c' : H.Comp (j + 1), H.Desc (j + 1) (m' + 1) c' Z →
      IsQuiet (H.locRH (j + 1) c') j c'.1)
    (hz0 : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 ≤ cs.delta k) (hdL : 1 ≤ S.d * S.L) (hβ : ∀ k, 0 ≤ cs.beta k)
    (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct k)
    (r : ℕ → ℝ) (hr : ∀ k, r k = 3 * (S.d : ℝ) * S.L * cs.delta k)
    (TB : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → Prop)
    (hTB : ∀ k Z' o x, TB k Z' o x ↔
      ((∀ y : {y : BlockAt S n M K (k + 1) //
          y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
            newOutP (H.localHistory M K (k + 1) Z') k y},
        |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| < r k) ∧
      (∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
        |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
          r k)))
    (cst : ∀ (k : ℕ), H.Comp (k + 1) → ℝ)
    (hcst : ∀ k Z', cst k Z' = (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
      volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
        z ∉ (H.localHistory M K (k + 1) Z').Z k})
    (bw0 : ℝ)
    (hbw0 : cst m' Z + ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ∑ c : ↥(H.parts (j.1 + 1) P.1), cst j.1 c.1 ≤ bw0)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1))) (P2 : BlockAt S n M K (m' + 1) → Prop)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0)
    (hG3 : ∀ y, y ∈ G3 ↔ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
      ¬ (y ∈ V2 ∧ P2 y))
    (T : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) [Fintype ↑T]
    (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) [Fintype ↑Nd]
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hNd : ∀ p, p ∈ Nd ↔ p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩)
    (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (by omega) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (jS : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A → ℕ)
    (hjS : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A, p ∈ Set.range κc ∨
        (p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩) ∨
        (k1 ≤ jS p ∧ jS p ≤ m' ∧ k1 ≤ (p.1.1.1 : ℕ) ∧
          ∀ (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
            (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
              (locOp geo cs SD KD hH lab (m' + 1) hm Z).A),
            TB m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
              (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) →
            (∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
              (c : ↥(H.parts (j.1 + 1) P.1)),
              TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                  (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
                (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                  (newVars_sub_locOp_A geo cs SD KD
                    ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                    (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                      (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                  (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) →
            |‖VarVal.toEuc (x p)‖ ^ 2 - 1| < r (jS p)))
    (hTnr : ∀ t ∈ T, t ∉ Set.range κc) (hNT : ∀ p ∈ Nd, p ∉ T)
    (t s z w : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A → ℝ)
    {c0 : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ℝ}
    {rr : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 →
      OutRest N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 → ℝ}
    (ht : ∀ o x, 0 ≤ t o x ∧ t o x ≤ 1) (hs : ∀ o x, 0 ≤ s o x ∧ s o x ≤ 1)
    (hz : ∀ o x, 0 ≤ z o x ∧ z o x ≤ 1) (hw : ∀ o x, 0 ≤ w o x ∧ w o x ≤ 1)
    (hc0 : ∀ o, 0 ≤ c0 o) (hrr : ∀ w y, 0 ≤ rr w y)
    (Zt : Set (Torus S.d (M * n K * S.L ^ K))) (δk : ℝ)
    (ht_def : ∀ o x, t o x = chiTilde (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk
      (outField N o))
    (cen : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0} →
      EuclideanSpace ℝ (Fin N)) (radZ : ℝ) {ρt : Type}
    (e : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) → ρt → EuclideanSpace ℝ (Fin N))
    (cb : ρt → BlockAt S n M K (m' + 1))
    (hc0s : ∀ (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (oz : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1)),
      c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) ≠ 0 →
      ∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
        y ∈ Z0}, ‖oz ⟨i.1, i.2.1, hZ0 _ i.2.1 i.2.2⟩ - cen par i‖ < radZ)
    (hcb : ∀ (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (oz : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1)) c,
      outField N (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) (cb c) = e par c)
    (hcbZ0 : ∀ c, cb c ∉ Z0) (Qb : ℝ)
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
          r m') →
      c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr
          (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) ≤ Qb)
    (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (oz : OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)
    (ro : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))
    (sh : ∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
      p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)
    (o o' : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (ho : o = mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)
    (ho' : o' = remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
      (w', (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 o).2))
    (hro : ∀ y : {y : BlockAt S n M K (m' + 1) //
        y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
          (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)},
      ro y = o' ⟨y.1, y.2.1⟩)
    (hsh : ∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
        p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal.toEuc (sh p) = VarVal.toEuc (x p.1))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (g ∈ l1Ball (GIdx S n M K N) → (∀ i : {y : BlockAt S n M K (m' + 1) //
        y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0},
        ‖oz ⟨i.1, i.2.1, hZ0 _ i.2.1 i.2.2⟩ - cen par i‖ < radZ) →
      (∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
        (∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y},
          ψ i.1 = oz ⟨i.1, (hV2 i.1 i.2.1 i.2.2).1, (hV2 i.1 i.2.1 i.2.2).2.1⟩) ∧
        (∀ c, ψ (cb c) = e par c) ∧
        ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ) →
      ENNReal.ofReal (c0 o * (toRKernel (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K t s z w o' x hv *
        Real.exp ((locOp geo cs SD KD hH lab (m' + 1) hm Z).T.b o' x hv g).re) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr o) ≤
      ENNReal.ofReal Qb * ENNReal.ofReal (Real.exp bw0) *
        (ENNReal.ofReal (gaussProd N (H.localHistory M K (m' + 1) Z) m' cs o'
          (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x)) *
        (∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∏ c : ↥(H.parts (j.1 + 1) P.1),
            ENNReal.ofReal (gaussProd N (H.localHistory M K (j.1 + 1) c.1) j.1 cs
              (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))))) * (if (∀ y : {y : BlockAt S n M K (m' + 1) //
            y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
              (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)},
          |‖ro y‖ ^ 2 - 1| < r m') then (1 : ℝ≥0∞) else 0) * (if (∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
            p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, |‖VarVal.toEuc (sh p)‖ ^ 2 - 1| < r (jS p.1))
          then (1 : ℝ≥0∞) else 0) *
        ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
          (locOp geo cs SD KD hH lab k1
            ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
            (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
            (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g) ∧
    (ENNReal.ofReal (c0 o * (toRKernel (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K t s z w o' x hv *
        Real.exp ((locOp geo cs SD KD hH lab (m' + 1) hm Z).T.b o' x hv g).re) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr o) ≠ 0 →
      (∀ i : {y : BlockAt S n M K (m' + 1) //
        y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0},
        ‖oz ⟨i.1, i.2.1, hZ0 _ i.2.1 i.2.2⟩ - cen par i‖ < radZ) ∧
      (∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
        (∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y},
          ψ i.1 = oz ⟨i.1, (hV2 i.1 i.2.1 i.2.2).1, (hV2 i.1 i.2.1 i.2.2).2.1⟩) ∧
        (∀ c, ψ (cb c) = e par c) ∧
        ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ) ∧
      (∀ t : ↥T, |‖VarVal.toEuc (x t.1)‖ ^ 2 - 1| < r (jS t.1))) := by
  classical
  have hoo : ∀ y (hV : y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)),
      o ⟨y, hV⟩ = mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par ⟨y, hV⟩ := by
    intro y hV; rw [ho]
  have ho'out : ∀ y (hV : y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (hy : y ∉ Z0),
      o' ⟨y, hV⟩ = o ⟨y, hV⟩ := by
    intro y hV hy
    rw [ho']
    simp [remZeroMerge, remZeroSplit_apply, restrictOutPart, hy]
  have hom : ∀ y (hV : y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (hZ : ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y),
      o ⟨y, hV⟩ = oz ⟨y, hV, hZ⟩ := by
    intro y hV hZ
    rw [ho]
    simp [mergeOut, hZ]
  refine ⟨fun hg hBall hTree => ?_, fun hne => ?_⟩
  · refine (window_pw_point geo cs SD KD hk1p hk1 hm hq hQuiet hz0 hc hδ hdL hβ haw hμ r hr TB hTB cst hcst
      bw0 hbw0 ρ hρ Z0 t s z w ht hs hz hw hc0 hrr o o' x hv g hg Qb _ _ ?_).1
    intro hT
    have hT1 := (hTB _ _ _ _).mp hT.1
    refine ⟨?_, ?_, ?_⟩
    · rw [ho]
      refine hquot par oz hBall hTree (fun y hy => ?_)
      have h1 := hT1.1 y
      have h2 : restrictOutPart o' (newOutP (H.localHistory M K (m' + 1) Z) m') y =
          mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par ⟨y.1, y.2.1⟩ :=
        (ho'out y.1 y.2.1 hy).trans (hoo _ _)
      rw [h2] at h1
      exact h1
    · have hall : ∀ y : {y : BlockAt S n M K (m' + 1) //
          y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
            (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)},
          |‖ro y‖ ^ 2 - 1| < r m' := by
        intro y
        have hy1 := y.2.2
        have hnew : newOutP (H.localHistory M K (m' + 1) Z) m' y.1 := by
          rcases zblk_gauss_or_new hm Z hy1.1 with hg' | hn
          · exact absurd ((hG3 y.1).mpr ⟨hg', hy1.2.1, hy1.2.2.1⟩) hy1.2.2.2
          · exact hn
        have h1 := hT1.1 ⟨y.1, y.2.1, hnew⟩
        rw [hro y]
        exact h1
      simp [hall]
    · have hall : ∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
            p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, |‖VarVal.toEuc (sh p)‖ ^ 2 - 1| < r (jS p.1) := by
        intro p
        have hcov := ((hjS p.1).resolve_left p.2.1).resolve_left
          (fun h => p.2.2.2 ((hNd p.1).mpr h))
        rw [hsh p]
        exact hcov.2.2.2 o' x hT.1 hT.2
      simp [hall]
  · have hg0 : (0 : GIdx S n M K N → ℂ) ∈ l1Ball (GIdx S n M K N) := by simp [l1Ball]
    have hne0 : ENNReal.ofReal (c0 o * (toRKernel (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K t s z w o' x hv *
        Real.exp ((locOp geo cs SD KD hH lab (m' + 1) hm Z).T.b o' x hv 0).re) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr o) ≠ 0 :=
      ofReal_ne_zero_swap (hc0 o) (toRKernel_nonneg _ _
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K_nonneg (fun o x => (ht o x).1)
        (fun o x => (hs o x).1) (fun o x => (hz o x).1) (fun o x => (hw o x).1) o' x hv)
        (remDen_nonneg _ _ Z0 hrr o) (Real.exp_pos _) hne
    obtain ⟨hTall', hc0', ht'⟩ := (window_pw_point geo cs SD KD hk1p hk1 hm hq hQuiet hz0 hc hδ hdL hβ haw
      hμ r hr TB hTB cst hcst bw0 hbw0 ρ hρ Z0 t s z w ht hs hz hw hc0 hrr o o' x hv 0 hg0
      (c0 o / remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr o) 1 1
      (fun _ => ⟨le_rfl, rfl, rfl⟩)).2 hne0
    refine ⟨hc0s par oz (by rw [← ho]; exact hc0'), ?_, ?_⟩
    · have hχ : ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk (outField N o') := by
        by_contra hn
        apply ht'
        rw [ht_def]
        unfold chiTilde
        rw [charFn_apply]; simp [hn]
      refine ⟨outField N o', fun i => ?_, fun c => ?_, hχ⟩
      · have hV := (hV2 i.1 i.2.1 i.2.2).1
        have hZ := (hV2 i.1 i.2.1 i.2.2).2.1
        have hn := (hV2 i.1 i.2.1 i.2.2).2.2
        show outField N o' i.1 = _
        rw [outField, dite_eq_left_of_eq_true (eq_true hV), ho'out _ hV hn, hom _ hV hZ]
      · have h1 : outField N o' (cb c) = outField N o (cb c) := by
          unfold outField
          by_cases hV : cb c ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)
          · rw [dite_eq_left_of_eq_true (eq_true hV), dite_eq_left_of_eq_true (eq_true hV), ho'out _ hV (hcbZ0 c)]
          · rw [dite_eq_right_of_eq_false (eq_false hV), dite_eq_right_of_eq_false (eq_false hV)]
        rw [h1, ho]
        exact hcb par oz c
    · intro t
      have hcov := ((hjS t.1).resolve_left (hTnr t.1 t.2)).resolve_left
        (fun h => hNT t.1 ((hNd t.1).mpr h) t.2)
      exact hcov.2.2.2 o' x hTall'.1 hTall'.2

end At

end Balaban.LargeField
