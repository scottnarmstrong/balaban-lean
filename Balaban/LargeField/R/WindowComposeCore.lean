/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidCoreThm
public import Balaban.LargeField.R.WindowComposeCongr
public import Balaban.LargeField.R.WindowComposePt

/-!
# The window integral with the action factor and the exact Gaussian integral (blocker 4, item S7)

`notes/phase1/LF4R-PLAN.md` §9.3, item S7.  `window_hid_core_action` is `window_hid_core` with the uniform quotient
bound `c₀/∫r ≤ Q_b` (`hquot`) and the sup bound of the Gaussian integral (`lintegral_gauss_coords`) replaced by
the exact form of P7 (2.58′): the integrand of the removed outcome is at most `c₀/∫r · e^{-∑ 𝒜}` times the
weights of the chain (`window_chain_le_action`), and the hypothesis `hbG` says that `c₀/∫r · e^{-∑ 𝒜}` times the
integral of the Gaussian product over the node coordinates is at most `Q_tot` (at every point of the support).
The conclusion is the `hid` of `removedKernel_kerBound_of_window` with `e^{B_w} Q_tot` in place of
`e^{B_w} e^{L_c} Q_b`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Core

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
theorem window_hid_core_action {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (hk1K : k1 ≤ K) (hk1K1 : k1 + 1 ≤ K) (hmk : k1 < m' + 1) {Z : H.Comp (m' + 1)}
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
          ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (jS : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A → ℕ)
    (hjS : ∀ p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A, p ∈ Set.range κc ∨
        (p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩) ∨
        (k1 ≤ jS p ∧ jS p ≤ m' ∧ k1 ≤ (p.1.1.1 : ℕ) ∧
          ∀ (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
            (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
              (locOp geo cs SD KD hH lab (m' + 1) hm Z).A),
            TB m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
              (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) x) →
            (∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
              (c : ↥(H.parts (j.1 + 1) P.1)),
              TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                  (le_trans (le_trans (Finset.mem_Ico.mp j.2).1 (Nat.le_succ _)) (Nat.le_succ _)) P.1 (mem_ancFin.mp P.2) x))
                (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                  (newVars_sub_locOp_A geo cs SD KD
                    ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                    (hq (j.1 + 1) (Nat.lt_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1
                      (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                  (ρ (j.1 + 1) (le_trans (Finset.mem_Ico.mp j.2).1 (Nat.le_succ _)) c.1
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
    (hcbZ0 : ∀ c, cb c ∉ Z0)
    (hN2 : 2 ≤ N)
    (hrad : ∀ j, k1 ≤ j → j ≤ m' → 0 < r j ∧ r j ≤ 1 / 2 ∧ cShell N * r j ≤ 1)
    (hκ2 : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A),
        (κc ⟨C, Sum.inr q⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc hk1K1 C.2.2 q.1).1.1,
              (ancInc hk1K1 C.2.2 q.1).1.2.1, (ancInc hk1K1 C.2.2 q.1).1.2.2⟩,
            inclVar_mem hm (mem_ancFin.mp C.1.2) (ancInc hk1K1 C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1)))
    (parC : (∀ t : ↥T, VarVal N t.1.1.isSpin) →
        ∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
          OutPar N R (H.localHistory M K k1 C.2.1) k1)
    (hparC : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (ρP : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
          SubCfg N (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1)
            (locOp geo cs SD KD hH lab (k1 + 1) hk1K1 C.1.1).A)
        (_ : ∀ x p, ρP x p = x ⟨_, locOp_A_incl geo cs SD KD hm (mem_ancFin.mp C.1.2)
          (fun t ht Y' h' => hq t (lt_trans (Nat.lt_succ_self k1) ht) Y' h') p.1 p.2⟩)
        (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A),
        ancOut (N := N) (R := R) C.2.1 C.1.1 (ρP x) =
          mergeOut (H.localHistory M K k1 C.2.1) k1
            (fun y => VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩))) (parC (fun t => x t.1) C))
    (F : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) × (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A × OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0) → ℝ≥0∞)
    (hF : ∀ hv g par oz x w', F hv g par (oz, x, w') = ENNReal.ofReal
      (c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par) *
        (toRKernel (H.localHistory M K (m' + 1) Z) (m' + 1)
            (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K t s z w
            (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
              (w', (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)).2)) x hv *
          Real.exp ((locOp geo cs SD KD hH lab (m' + 1) hm Z).T.b
            (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
              (w', (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)).2)) x hv g).re) /
        remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) oz par)))
    (Φ : ((OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
        ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) ×
            ((OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)) ×
                OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)))) →
      OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) × (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A × OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0))
    (φ1 : ∀ θ (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0}),
      (Φ θ).1 ⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩ = θ.1.1 y)
    (φ2 : ∀ θ (y : {y // y ∈ V2 ∧ P2 y}),
      (Φ θ).1 ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩ = θ.1.2.1 y)
    (φ3 : ∀ θ (t : ↥T), (Φ θ).2.1 t.1 = θ.1.2.2 t)
    (φ4 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (θ.2.1 C).1 y = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inl y⟩)))
    (φ5 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A),
        VarVal.toEuc ((θ.2.1 C).2 q) = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inr q⟩)))
    (φ7 : ∀ θ (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
          (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)}),
      (Φ θ).1 ⟨y.1, y.2.1, y.2.2.1⟩ = θ.2.2.1.2 y)
    (φ9 : ∀ θ (t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
        p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}), (Φ θ).2.1 t.1 = θ.2.2.2.1.2 t)
    (Qtot : ℝ≥0∞) (hQtot : 0 < Qtot) (hQtotT : Qtot ≠ ⊤)
    (hbG : ∀ (hv : EuclideanSpace ℝ (Fin N)) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin))
      (a : OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (nd' : ∀ t : ↥Nd, VarVal N t.1.1.isSpin)
      (w' : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)
      (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
      (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)),
      (∀ v s y, fld v s y = subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y) → (∀ v y, ft v y = outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
            ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
              (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y) →
      wd ∈ ({o : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 |
            ∀ i, ‖o i - cen par i‖ < radZ} ×ˢ
          ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
            (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
              ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ
            {w3 : ∀ t : ↥T, VarVal N t.1.1.isSpin |
              ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| < r (jS t.1)})) →
      (TB m' Z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)),
            TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))) →
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1 hv * ROutcome.weight (t (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) (s (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) (z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) (w (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) ROutcome.toR ≠ 0 →
      (0 < (∫⁻ v, ENNReal.ofReal
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
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))) ∧
      ENNReal.ofReal (c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par) / remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)) *
        ENNReal.ofReal (Real.exp (-(mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
          (locRH_rem (m' + 1) Z) (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1) hv +
        ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∑ c : ↥(H.parts (j.1 + 1) P.1),
            mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
              (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
              (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
              (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd', sh), w')))).2.1)) hv))) *
        (∫⁻ v, ENNReal.ofReal
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
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))) ≤ Qtot)) :
    (∀ hv g par w c, ∫⁻ j, F hv g par (Φ (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) ≤
        (if g ∈ l1Ball (GIdx S n M K N) then
          ∏ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            (locOp geo cs SD KD hH lab k1 hk1K C.2.1).T.absW
              (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC w.2.2 C)) (c C).2 hv g
         else ⊤) *
        (ENNReal.ofReal (Real.exp bw0) * Qtot)) ∧
      (∀ hv g par w c,
        w ∉ ({o : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 |
            ∀ i, ‖o i - cen par i‖ < radZ} ×ˢ
          ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
            (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
              ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ
            {w3 : ∀ t : ↥T, VarVal N t.1.1.isSpin |
              ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| < r (jS t.1)})) →
        ∫⁻ j, F hv g par (Φ (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) = 0) := by
  classical
  have hpt := fun hv g par wd cc (j : _) =>
    window_pt_action geo cs SD KD hk1p hk1 hm hq hQuiet hz0 hc hδ hdL hβ haw hμ r hr TB hTB cst hcst bw0 hbw0
      ρ hρ Z0 V2 G3 P2 hZ0 hV2 hG3 T Nd nd hNd κc jS hjS hTnr hNT t s z w ht hs hz hw hc0 hrr Zt δk
      ht_def cen radZ e cb hc0s hcb hcbZ0 par (Φ (wd, cc, j)).1 (Φ (wd, cc, j)).2.1 (Φ (wd, cc, j)).2.2 j.1.2 j.2.1.2
      (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)
      (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)).2))
      rfl rfl
      (fun y => by
        rw [merge_apply_out (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, cc, j)).1 par
          (Φ (wd, cc, j)).2.2 y.1 y.2.1 y.2.2.2.1 y.2.2.1]
        exact (φ7 (wd, cc, j) y).symm)
      (fun p => congrArg VarVal.toEuc (φ9 (wd, cc, j) p).symm) hv g
  let Ewin : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      Set (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 ×
        (∀ t : ↥T, VarVal N t.1.1.isSpin))) := fun par =>
    {o : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 | ∀ i, ‖o i - cen par i‖ < radZ} ×ˢ
      ({o : OutPart N V2 P2 | ∃ ψ : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N),
        (∀ i, ψ i.1 = o i) ∧ (∀ c, ψ (cb c) = e par c) ∧
          ChiTildeProp (H.localHistory M K (m' + 1) Z) (m' + 1) Zt δk ψ} ×ˢ
        {w3 : ∀ t : ↥T, VarVal N t.1.1.isSpin | ∀ t : ↥T, |‖VarVal.toEuc (w3 t)‖ ^ 2 - 1| < r (jS t.1)})
  have hFpt2 : ∀ hv g par wd cc j, F hv g par (Φ (wd, cc, j)) ≠ 0 → wd ∈ Ewin par := by
    intro hv g par wd cc j hne
    obtain ⟨hBall, hTree, hTsh⟩ := (hpt hv g par wd cc j).2
      (by rw [← hF hv g par (Φ (wd, cc, j)).1 (Φ (wd, cc, j)).2.1 (Φ (wd, cc, j)).2.2]; exact hne)
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have := hBall i
      rwa [φ1 (wd, cc, j) i] at this
    · obtain ⟨ψ, h1, h2, h3⟩ := hTree
      exact ⟨ψ, fun i => (h1 i).trans (φ2 (wd, cc, j) i), h2, h3⟩
    · intro t
      have := hTsh t
      rwa [φ3 (wd, cc, j) t] at this
  let brk : EuclideanSpace ℝ (Fin N) → OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) → (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin))) → (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) → (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) → (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin) →
      OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) → (∀ t : ↥Nd, VarVal N t.1.1.isSpin) → OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 → ℝ≥0∞ := fun hv par wd cc ro sh a nd w' =>
    if ((TB m' Z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)),
            TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1))) ∧ (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1 hv * ROutcome.weight (t (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1) (s (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1) (z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1) (w (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1) ROutcome.toR ≠ 0) then
      ENNReal.ofReal (c0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par) / remDen (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 rr (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)) *
        ENNReal.ofReal (Real.exp (-(mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
          (locRH_rem (m' + 1) Z) (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).1 par)).2)) (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1) hv +
        ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∑ c : ↥(H.parts (j.1 + 1) P.1),
            mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
              (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
              (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
              (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) (Φ (wd, cc, ((a, ro), ((nd, sh), w')))).2.1)) hv))) else 0
  let Qf : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) → (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin))) → (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) →
      (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) → (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin) → ℝ≥0∞ := fun hv _ par wd cc ro sh => ⨆ a, ⨆ nd, ⨆ w', brk hv par wd cc ro sh a nd w'
  exact window_hid_core_glue geo cs SD KD (hk1p := hk1p) (hk1 := hk1) (hm := hm) (hk1K := hk1K) (hk1K1 := hk1K1) (hmk := hmk) (hq := hq) (hz0 := hz0) (hc := hc) (r := r) (TB := TB) (bw0 := bw0) (ρ := ρ) (hρ := hρ) (Z0 := Z0) (V2 := V2) (G3 := G3) (P2 := P2) (T := T) (Nd := Nd) (nd := nd) (hNd := hNd) (κc := κc) (jS := jS) (hjS := hjS) (hTnr := hTnr) (hNT := hNT) (hN2 := hN2) (hrad := hrad) (hκ2 := hκ2) (parC := parC) (hparC := hparC) (F := F) (Ewin := Ewin) (Φ := Φ) (φ3 := φ3) (φ4 := φ4) (φ5 := φ5) (hFpt2 := hFpt2)
    (Qf := Qf) (P := Qtot) (hP0 := hQtot.ne')
    (hFpt1 := fun hv g par wd cc j o' x hx ho' hg hw => by
      subst hx ho'
      by_cases hF0 : F hv g par (Φ (wd, cc, j)) = 0
      · rw [hF0]; exact bot_le
      have hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)).2)) (Φ (wd, cc, j)).2.1 hv * ROutcome.weight (t (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)).2)) (Φ (wd, cc, j)).2.1) (s (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)).2)) (Φ (wd, cc, j)).2.1) (z (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)).2)) (Φ (wd, cc, j)).2.1) (w (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, j)).1 par)).2)) (Φ (wd, cc, j)).2.1) ROutcome.toR ≠ 0 := by
        intro hK0
        apply hF0
        rw [hF hv g par (Φ (wd, cc, j)).1 (Φ (wd, cc, j)).2.1 (Φ (wd, cc, j)).2.2]
        simp [toRKernel, hK0]
      refine (hF hv g par (Φ (wd, cc, j)).1 (Φ (wd, cc, j)).2.1 (Φ (wd, cc, j)).2.2).le.trans
        ((hpt hv g par wd cc j).1 (Qf hv g par wd cc j.1.2 j.2.1.2) hg ?_)
      intro hT
      have e : brk hv par wd cc j.1.2 j.2.1.2 j.1.1 j.2.1.1 j.2.2 = _ :=
        ite_eq_left_iff.mpr (fun hn => absurd ⟨hT, hK⟩ hn)
      exact e.symm.le.trans (le_iSup_of_le j.1.1 (le_iSup_of_le j.2.1.1 (le_iSup_of_le j.2.2 le_rfl))))
    (hG := fun hv g par wd cc ro sh hg hw fld ft hfld hft => by
      have hfld' : fld = fun v s y => subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y :=
        funext fun v => funext fun s => funext fun y => hfld v s y
      have hft' : ft = fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
          ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
            (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
              (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y :=
        funext fun v => funext fun y => hft v y
      subst hfld' hft'
      let Gint : (∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N)) →
          (BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)) → ℝ := fun fld ft =>
        (∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
                ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
                  y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
              cs.z (m' + 1) ^ N * gaussDens (cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
                (cs.z (m' + 1) • ft y - ((S.L : ℝ) ^ S.d)⁻¹ •
                  ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                    blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld m' y')) *
            ∏ j ∈ Finset.Ico k1 m',
              ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
                  ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                    y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
                cs.z (j + 1) ^ N * gaussDens (cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
                  (cs.z (j + 1) • fld (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                    ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                      blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld j y')
      have hI : ∀ a' nd' w', brk hv par wd cc ro sh a' nd' w' * (∫⁻ x, ENNReal.ofReal (Gint (fun s y => subVarField N (Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).2.1 s y) (fun y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).1 par)).2)) y)) ∂((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))) ≤ Qtot := by
        intro a' nd' w'
        simp only [brk]
        split_ifs with hT'
        · exact (hbG hv par wd cc ro sh a' nd' w' (fun v s y => subVarField N
            (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y)
            (fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
              ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
                (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                  (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y)
            (fun _ _ _ => rfl) (fun _ _ => rfl) hw hT'.1 hT'.2).2
        · simp
      have hBI : Qf hv g par wd cc ro sh * (∫⁻ x, ENNReal.ofReal (Gint (fun s y => subVarField N (Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).2.1 s y) (fun y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).1 par)).2)) y)) ∂((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))) ≤ Qtot := by
        simp only [Qf, ENNReal.iSup_mul]
        exact iSup_le fun a' => iSup_le fun nd' => iSup_le fun w' => hI a' nd' w'
      by_cases hB0 : Qf hv g par wd cc ro sh = 0
      · simp [hB0]
      · have hex : ∃ a nd w', brk hv par wd cc ro sh a nd w' ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hB0 (by simp [Qf, hcon])
        obtain ⟨a, nd, w', hne⟩ := hex
        have hIpos : 0 < (∫⁻ x, ENNReal.ofReal (Gint (fun s y => subVarField N (Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).2.1 s y) (fun y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, cc, ((x.1, ro), ((x.2.1, sh), x.2.2)))).1 par)).2)) y)) ∂((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))) := by
          simp only [brk] at hne
          split_ifs at hne with hT'
          · exact (hbG hv par wd cc ro sh a nd w' (fun v s y => subVarField N
              (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y)
              (fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
                ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
                  (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                    (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y)
              (fun _ _ _ => rfl) (fun _ _ => rfl) hw hT'.1 hT'.2).1
          · exact absurd rfl hne
        have hBfin : Qf hv g par wd cc ro sh ≠ ⊤ := by
          intro hB
          rw [hB, ENNReal.top_mul hIpos.ne'] at hBI
          exact hQtotT (top_le_iff.mp hBI)
        rw [lintegral_const_mul' _ _ hBfin]
        exact hBI
)

end Core

end Balaban.LargeField
