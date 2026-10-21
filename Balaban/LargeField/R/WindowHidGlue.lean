/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidAt
public import Balaban.LargeField.R.RRemovedHidCore
public import Balaban.LargeField.R.RRemovedHidGu
public import Balaban.LargeField.R.RRemovedHidRead
public import Balaban.LargeField.R.RRemovedHidGauss
public import Balaban.LargeField.R.RRemovedHidGen
public import Balaban.LargeField.R.RRemovedHidVol
public import Balaban.LargeField.R.RRemovedHidO
public import Balaban.LargeField.R.RRemovedHidCover
public import Balaban.LargeField.R.SmallFactorChi

/-!
# The shared glue of the window integral (W961)

`window_hid_core_glue`: the common core of `window_hid_core_gen` (sup bound for the Gaussian node integral) and
`window_hid_core_action` (exact node integral).  The pointwise bound `hFpt1` carries a factor `Qf` that does not
depend on the node variables, and the Gaussian-node step is the hypothesis `hG`: for every value of the shell
variables, the integral of `Qf` times the Gaussian chain over the node coordinates is at most `P`.
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
theorem window_hid_core_glue {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (hk1K : k1 ≤ K) (hk1K1 : k1 + 1 ≤ K) (hmk : k1 < m' + 1) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hz0 : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (r : ℕ → ℝ)
    (TB : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → Prop)
    (bw0 : ℝ)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1))) (P2 : BlockAt S n M K (m' + 1) → Prop)
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
    (Qf : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) → (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin))) → (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) → (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) → (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin) → ℝ≥0∞)
    (P : ℝ≥0∞) (hP0 : P ≠ 0)
    (F : EuclideanSpace ℝ (Fin N) → (GIdx S n M K N → ℂ) → OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) × (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A × OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0) → ℝ≥0∞)
    (Ewin : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1) →
      Set (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 ×
        (∀ t : ↥T, VarVal N t.1.1.isSpin))))
    (Φ : ((OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
        ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A) ×
            ((OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)) ×
                OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)))) →
      OutZ N R (H.localHistory M K (m' + 1) Z) (m' + 1) × (SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) (locOp geo cs SD KD hH lab (m' + 1) hm Z).A × OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0))
    (φ3 : ∀ θ (t : ↥T), (Φ θ).2.1 t.1 = θ.1.2.2 t)
    (φ4 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (θ.2.1 C).1 y = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inl y⟩)))
    (φ5 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A),
        VarVal.toEuc ((θ.2.1 C).2 q) = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inr q⟩)))
    (hvOK : EuclideanSpace ℝ (Fin N) → Prop)
    (hFpt1 : ∀ (hv : EuclideanSpace ℝ (Fin N)) (_hok : hvOK hv) (g : GIdx S n M K N → ℂ)
      (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 ×
        (∀ t : ↥T, VarVal N t.1.1.isSpin)))
      (c : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A))
      (j : ((OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) ×
              OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
                (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧
                  ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
                (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)) ×
                OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0)))
      (o' : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A),
      x = (Φ (wd, c, j)).2.1 →
      o' = remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, c, j)).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
          (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, c, j)).1 par)).2) →
      g ∈ l1Ball (GIdx S n M K N) → wd ∈ Ewin par →
      F hv g par (Φ (wd, c, j)) ≤
      Qf hv g par wd c j.1.2 j.2.1.2 * ENNReal.ofReal (Real.exp bw0) *
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
          |‖j.1.2 y‖ ^ 2 - 1| < r m') then (1 : ℝ≥0∞) else 0) * (if (∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
            p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, |‖VarVal.toEuc (j.2.1.2 p)‖ ^ 2 - 1| < r (jS p.1))
          then (1 : ℝ≥0∞) else 0) *
        ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
          (locOp geo cs SD KD hH lab k1
            ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
            (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
            (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g)
    (hFpt2 : ∀ hv g par wd c j, F hv g par (Φ (wd, c, j)) ≠ 0 → wd ∈ Ewin par)
    (hG : ∀ (hv : EuclideanSpace ℝ (Fin N)) (_hok : hvOK hv) (g : GIdx S n M K N → ℂ) (par : OutPar N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (wd : (OutZero N R (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 × (OutPart N V2 P2 × (∀ t : ↥T, VarVal N t.1.1.isSpin)))) (cc : (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)), OutZ N R (H.localHistory M K k1 C.2.1) k1 × SubCfg N (H.localHistory M K k1 C.2.1) k1 (locOp geo cs SD KD hH lab k1 hk1K C.2.1).A)) (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)),
      g ∈ l1Ball (GIdx S n M K N) → wd ∈ Ewin par →
      ∀ (fld : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
        (ft : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))) → BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)),
      (∀ v s y, fld v s y = subVarField N (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y) → (∀ v y, ft v y = outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
            ((Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
              (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
                (Φ (wd, cc, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y) →
      (∫⁻ v, Qf hv g par wd cc ro sh * ENNReal.ofReal
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
            (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))) ≤ P) :
    (∀ hv, hvOK hv → ∀ g par w c, ∫⁻ j, F hv g par (Φ (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) ≤
        (if g ∈ l1Ball (GIdx S n M K N) then
          ∏ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            (locOp geo cs SD KD hH lab k1 hk1K C.2.1).T.absW
              (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC w.2.2 C)) (c C).2 hv g
         else ⊤) *
        (ENNReal.ofReal (Real.exp bw0) * P)) ∧
      (∀ hv g par w c,
        w ∉ (Ewin par) →
        ∫⁻ j, F hv g par (Φ (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) = 0) := by
  classical
  have hjSh := fun (p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
      p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}) =>
    ((hjS p.1).resolve_left p.2.1).resolve_left (fun h => p.2.2.2 ((hNd p.1).mpr h))
  have hjT := fun (t : ↥T) => ((hjS t.1).resolve_left (hTnr t.1 t.2)).resolve_left
    (fun h => hNT t.1 ((hNd t.1).mpr h) t.2)
  have hsupp : ∀ hv g par wd c,
      wd ∉ (Ewin par) →
      ∫⁻ j, F hv g par (Φ (wd, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod
              (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1))
                (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧
                  ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) = 0 := by
    intro hv g par wd c hw
    have h0 : ∀ j, F hv g par (Φ (wd, c, j)) = 0 := fun j => by
      by_contra hne
      exact hw (hFpt2 hv g par wd c j hne)
    simp only [h0, lintegral_zero]
  refine ⟨fun hv hok g par wd c => ?_, hsupp⟩
  by_cases hw : wd ∈ (Ewin par)
  swap
  · rw [hsupp hv g par wd c hw]; exact zero_le
  have hIO : ∫⁻ ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)), (if (∀ y : {y : BlockAt S n M K (m' + 1) //
            y ∈ (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) ∧
              (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)},
          |‖ro y‖ ^ 2 - 1| < r m') then (1 : ℝ≥0∞) else 0)
        ∂(outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) ≤ 1 := by
    refine lintegral_ite_le_one _ _ ?_
    exact outPartMeasure_shell_le_one hN2 _ _ (fun _ => r m') (fun _ => (hrad m' hk1 le_rfl).1)
      (fun _ => (hrad m' hk1 le_rfl).2.1) (fun _ => (hrad m' hk1 le_rfl).2.2)
  have hIS : ∀ ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)), True := fun _ => trivial
  have hIS' : ∫⁻ sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin),
      (if (∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, |‖VarVal.toEuc (sh p)‖ ^ 2 - 1| < r (jS p.1)) then (1 : ℝ≥0∞) else 0)
        ∂(Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin) ≤ 1 := by
    refine lintegral_ite_le_one _ _ ?_
    refine pi_shell_le_one hN2 (fun p => p.1.1.isSpin) (fun p => ?_) (fun p => r (jS p.1))
      (fun p => (hrad _ (hjSh p).1 (hjSh p).2.1).1) (fun p => (hrad _ (hjSh p).1 (hjSh p).2.1).2.1)
      (fun p => (hrad _ (hjSh p).1 (hjSh p).2.1).2.2)
    have := (hjSh p).2.2.1
    unfold InternalVars.isSpin
    exact decide_eq_false (fun h => by omega)
  -- the Gaussian integrand and the fields
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
  by_cases hg : g ∈ l1Ball (GIdx S n M K N)
  swap
  · have hpos : ENNReal.ofReal (Real.exp bw0) * P ≠ 0 :=
      mul_ne_zero (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _) hP0
    simp only [hg, ↓reduceIte]
    rw [ENNReal.top_mul hpos]
    exact le_top
  simp only [hg, ↓reduceIte]
  have hK : ENNReal.ofReal (Real.exp bw0) * (∏ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            (locOp geo cs SD KD hH lab k1 hk1K C.2.1).T.absW
              (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC wd.2.2 C)) (c C).2 hv g) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.prod_ne_top fun C _ => ENNReal.ofReal_ne_top)
  refine le_trans (lintegral_nodes_shells_le
      (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)) (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))
      (Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin)
      (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)
      (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))
      (fun j => F hv g par (Φ (wd, c, j)))
      (ENNReal.ofReal (Real.exp bw0) * (∏ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
            (locOp geo cs SD KD hH lab k1 hk1K C.2.1).T.absW
              (mergeOut (H.localHistory M K k1 C.2.1) k1 (c C).1 (parC wd.2.2 C)) (c C).2 hv g)) P hK
      (fun a ro nd w' sh => Qf hv g par wd c ro sh * ENNReal.ofReal (Gint (fun s y => subVarField N (Φ (wd, c, ((a, ro), ((nd, sh), w')))).2.1 s y) (fun y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, c, ((a, ro), ((nd, sh), w')))).2.2, (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, c, ((a, ro), ((nd, sh), w')))).1 par)).2)) y)))
      (fun ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)) => if (∀ y : {y : BlockAt S n M K (m' + 1) //
            y ∈ (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) ∧
              (ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)},
          |‖ro y‖ ^ 2 - 1| < r m') then (1 : ℝ≥0∞) else 0) (fun sh : (∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin) => if (∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, |‖VarVal.toEuc (sh p)‖ ^ 2 - 1| < r (jS p.1)) then (1 : ℝ≥0∞) else 0)
      (fun ro => by split_ifs <;> simp) (fun sh => by split_ifs <;> simp)
      (fun a ro nd sh w' => ?_) (fun ro sh => ?_) hIO hIS') ?_
  · have h1 := hFpt1 hv hok g par wd c ((a, ro), ((nd, sh), w')) _ _ rfl rfl hg hw
    rw [gchain_eq geo cs SD KD hk1 hm hq hz0 hc ρ hρ _ (Φ (wd, c, ((a, ro), ((nd, sh), w')))).2.1
      (fun s y => subVarField N (Φ (wd, c, ((a, ro), ((nd, sh), w')))).2.1 s y)
      (fun y => outField N _ y) (fun _ _ => rfl) (fun _ => rfl)] at h1
    rw [core_prod_eq geo cs SD KD hmk hm hq T κc hκ2 parC hparC ρ hρ
      (Φ (wd, c, ((a, ro), ((nd, sh), w')))).2.1 c wd.2.2
      (fun t => (φ3 (wd, c, ((a, ro), ((nd, sh), w'))) t).symm)
      (fun C y => φ4 (wd, c, ((a, ro), ((nd, sh), w'))) C y)
      (fun C q => φ5 (wd, c, ((a, ro), ((nd, sh), w'))) C q) hv g] at h1
    exact h1.trans (le_of_eq (by ring))
  · exact hG hv hok g par wd c ro sh hg hw
      (fun v s y => subVarField N (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y)
      (fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y)
      (fun _ _ _ => rfl) (fun _ _ => rfl)
  · exact le_of_eq (by ring)

end Core

end Balaban.LargeField
