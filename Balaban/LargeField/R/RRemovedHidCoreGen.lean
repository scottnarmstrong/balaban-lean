/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidAt
public import Balaban.LargeField.R.RRemovedHidCore
public import Balaban.LargeField.R.RRemovedHidGu
public import Balaban.LargeField.R.WindowHidGlue
public import Balaban.LargeField.R.RRemovedHidRead
public import Balaban.LargeField.R.RRemovedHidGauss
public import Balaban.LargeField.R.RRemovedHidGen
public import Balaban.LargeField.R.RRemovedHidVol
public import Balaban.LargeField.R.RRemovedHidO
public import Balaban.LargeField.R.RRemovedHidCover
public import Balaban.LargeField.R.SmallFactorChi

/-!
# The general core of `hid` and `hsupp` (W952)

`window_hid_core_gen`: for the inverse `Φ` of the regrouping, given by its coordinate formulas, the composition
inputs `hid` and `hsupp` of the window integral for an arbitrary integrand `F` with the pointwise bound `hFpt1`
(the chain bound times a factor `Q_b`) and the support condition `hFpt2` (support in the window set `Ewin`).
`window_hid_core` (`RRemovedHidCoreThm.lean`) is the case of the removed outcome, `F = c₀ K^{→R} e^{Re b}/remDen`.
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
theorem window_hid_core_gen {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
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
    (Qb : ℝ)
    (hzpos : ∀ s, 0 < cs.z s) (hcpos : ∀ k, 0 < cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hN2 : 2 ≤ N)
    (hrad : ∀ j, k1 ≤ j → j ≤ m' → 0 < r j ∧ r j ≤ 1 / 2 ∧ cShell N * r j ≤ 1)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
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
    (wz : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} → ℝ) {Lc : ℝ}
    (hLc : Real.exp Lc = ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2))
    (hwz1 : ∀ i, Real.pi ≤ wz i)
    (hwz2 : ∀ i, cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2) * cs.z (m' + 1) ^ 2 ≤ 2 * wz i)
    (hQb : 0 < Qb)
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
    (φ2 : ∀ θ (y : {y // y ∈ V2 ∧ P2 y}),
      (Φ θ).1 ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩ = θ.1.2.1 y)
    (φ3 : ∀ θ (t : ↥T), (Φ θ).2.1 t.1 = θ.1.2.2 t)
    (φ4 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (θ.2.1 C).1 y = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inl y⟩)))
    (φ5 : ∀ θ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 hk1K C.2.1).A),
        VarVal.toEuc ((θ.2.1 C).2 q) = VarVal.toEuc ((Φ θ).2.1 (κc ⟨C, Sum.inr q⟩)))
    (hG3z : ∀ y ∈ G3, ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (φ6 : ∀ θ (y : {y // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ G3}),
      (Φ θ).1 ⟨y.1, y.2.1, hG3z _ y.2.2⟩ = θ.2.2.1.1 y)
    (φ8 : ∀ θ (t : ↥Nd), (Φ θ).2.1 t.1 = θ.2.2.2.1.1 t)
    (φ9 : ∀ θ (t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
        p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}), (Φ θ).2.1 t.1 = θ.2.2.2.1.2 t)
    (φ10 : ∀ θ, (Φ θ).2.2 = θ.2.2.2.2)
    (hFpt1 : ∀ (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
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
          |‖j.1.2 y‖ ^ 2 - 1| < r m') then (1 : ℝ≥0∞) else 0) * (if (∀ p : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A //
            p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, |‖VarVal.toEuc (j.2.1.2 p)‖ ^ 2 - 1| < r (jS p.1))
          then (1 : ℝ≥0∞) else 0) *
        ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
          (locOp geo cs SD KD hH lab k1
            ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
            (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
            (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g)
    (hFpt2 : ∀ hv g par wd c j, F hv g par (Φ (wd, c, j)) ≠ 0 → wd ∈ Ewin par) :
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
        ENNReal.ofReal (Real.exp bw0 * Real.exp Lc * Qb)) ∧
      (∀ hv g par w c,
        w ∉ (Ewin par) →
        ∫⁻ j, F hv g par (Φ (w, c, j)) ∂
          (((outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3)).prod (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0)))) = 0) := by
  classical
  have hglue := window_hid_core_glue geo cs SD KD (hk1p := hk1p) (hk1 := hk1) (hm := hm) (hk1K := hk1K) (hk1K1 := hk1K1) (hmk := hmk) (hq := hq) (hz0 := hz0) (hc := hc) (r := r) (TB := TB) (bw0 := bw0) (ρ := ρ) (hρ := hρ) (Z0 := Z0) (V2 := V2) (G3 := G3) (P2 := P2) (T := T) (Nd := Nd) (nd := nd) (hNd := hNd) (κc := κc) (jS := jS) (hjS := hjS) (hTnr := hTnr) (hNT := hNT) (hN2 := hN2) (hrad := hrad) (hκ2 := hκ2) (parC := parC) (hparC := hparC) (F := F) (Ewin := Ewin) (Φ := Φ) (φ3 := φ3) (φ4 := φ4) (φ5 := φ5) (hFpt1 := hFpt1) (hFpt2 := hFpt2)
    (Qf := fun _ _ _ _ _ _ _ => ENNReal.ofReal Qb) (P := ENNReal.ofReal (Real.exp Lc * Qb))
    (hP0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; have := Real.exp_pos Lc; positivity)
    (hG := by
      intro hv g par wd c ro sh hg hw fld ft hfld hft
      have hfld' : fld = fun v s y => subVarField N (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y :=
      funext fun v => funext fun s => funext fun y => hfld v s y
      have hft' : ft = fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0
        ((Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
          (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1)
            (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y :=
      funext fun v => funext fun y => hft v y
      subst hfld' hft'
      have hV2' : ∀ y, y ∈ V2 → P2 y → y ∉ Z0 := fun y h1 h2 => (hV2 y h1 h2).2.2
      -- the node coordinates of the fields
      have hxag : ∀ (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : ∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin) (v v' : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ G3) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (· ∈ Z0))))
          (p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A), p ∉ Nd →
          VarVal.toEuc ((Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 p) =
            VarVal.toEuc ((Φ (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.1 p) := by
        intro ro sh v v' p hp
        by_cases hr : p ∈ Set.range κc
        · obtain ⟨⟨C, y | q⟩, rfl⟩ := hr
          · exact (φ4 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) C y).symm.trans
              (φ4 (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) C y)
          · exact (φ5 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) C q).symm.trans
              (φ5 (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) C q)
        · by_cases hT : p ∈ T
          · exact congrArg VarVal.toEuc ((φ3 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) ⟨p, hT⟩).trans
              (φ3 (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) ⟨p, hT⟩).symm)
          · exact congrArg VarVal.toEuc
              ((φ9 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) ⟨p, hr, hT, hp⟩).trans
              (φ9 (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) ⟨p, hr, hT, hp⟩).symm)
      have hG := fun (ro : (OutPart N (Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1)) (fun y => ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3))) (sh : ∀ t : {p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A // p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin) =>
        lintegral_gauss_coords geo cs SD KD hk1 hm hq nd hnd hnd0 Z0 V2 G3 P2 hV2' hZ0g hG3 Nd hNd
          (fun j => cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) cs.z (fun j _ _ => hcpos j)
          (fun s _ _ => hzpos s)
          (fun v s y => subVarField N (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 s y)
          (fun v y => outField N (remZeroMerge (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 ((Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2,
            (remZeroSplit (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (mergeOut (H.localHistory M K (m' + 1) Z) (m' + 1) (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par)).2)) y)
          (fun v p => by
            show subVarField N (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.1 (p.1.1.1.1 : ℕ) p.1.1.1.2.2 = _
            rw [subVarField_var _ p.1 ((hNd p.1).mp p.2).1, φ8 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) p])
          (fun v v' s y hn => subVarField_congr _ _ s y (fun p hl hs hy => hxag ro sh v v' p
            (fun hpN => by
              subst hs
              have hy' := eq_of_heq hy
              subst hy'
              exact hn ((hNd p).mp hpN).2)))
          (fun v y => by
            show outField N _ y.1 = _
            rw [outField, dite_eq_left_of_eq_true (eq_true y.2.1),
              merge_apply_out (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2 y.1 y.2.1
                ((hG3 y.1).mp y.2.2).2.1 (hG3z _ y.2.2)]
            exact φ6 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) y)
          (fun v y => by
            show outField N _ y.1 = _
            rw [outField, dite_eq_left_of_eq_true (eq_true y.2.1),
              merge_apply_zero (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2 y.1 y.2.1 y.2.2]
            exact congrFun (φ10 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))) ⟨y.1, y.2.1, y.2.2⟩)
          (fun v v' y h1 h2 => by
            show outField N _ y = outField N _ y
            rw [outField, outField, dite_eq_left_of_eq_true (eq_true (hV2 y h1 h2).1),
              dite_eq_left_of_eq_true (eq_true (hV2 y h1 h2).1),
              merge_apply_out (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).1 par (Φ (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2)))).2.2 y (hV2 y h1 h2).1
                (hV2' y h1 h2) (hV2 y h1 h2).2.1,
              merge_apply_out (H.localHistory M K (m' + 1) Z) (m' + 1) Z0 (Φ (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).1 par (Φ (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2)))).2.2 y (hV2 y h1 h2).1
                (hV2' y h1 h2) (hV2 y h1 h2).2.1]
            exact (φ2 (wd, c, ((v.1, ro), ((v.2.1, sh), v.2.2))) ⟨y, h1, h2⟩).trans (φ2 (wd, c, ((v'.1, ro), ((v'.2.1, sh), v'.2.2))) ⟨y, h1, h2⟩).symm)
      have hP : ENNReal.ofReal (((cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) * cs.z (m' + 1) ^ 2 /
            (2 * Real.pi)) ^ ((N : ℝ) / 2)) ^
          (Finset.univ.filter fun y : BlockAt S n M K (m' + 1) =>
            y ∈ V2 ∧ P2 y ∧ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m').card ≤
          ENNReal.ofReal (Real.exp Lc) := by
        rw [hLc]
        refine root_prod_le (fun a => a ∈ V2 ∧ P2 a)
          (fun a => a ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
          (fun y => y ∈ V2 ∧ P2 y ∧ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
          (fun a => and_assoc.symm) (fun i => (wz i / Real.pi) ^ ((N : ℝ) / 2)) _ (fun i => ?_) (fun i hi => ?_)
        · exact Real.one_le_rpow ((one_le_div Real.pi_pos).mpr (hwz1 i)) (by positivity)
        · refine Real.rpow_le_rpow (by have := hcpos m'; have := hzpos (m' + 1); positivity) ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
          have := hwz2 i
          have hp := Real.pi_pos
          nlinarith
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal Qb * _ ≤ ENNReal.ofReal Qb * (ENNReal.ofReal (((cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) * cs.z (m' + 1) ^ 2 /
        (2 * Real.pi)) ^ ((N : ℝ) / 2)) ^
      (Finset.univ.filter fun y : BlockAt S n M K (m' + 1) =>
        y ∈ V2 ∧ P2 y ∧ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m').card) := mul_le_mul' le_rfl (hG ro sh)
      _ ≤ ENNReal.ofReal Qb * ENNReal.ofReal (Real.exp Lc) := mul_le_mul' le_rfl hP
      _ = ENNReal.ofReal (Real.exp Lc * Qb) := by
        rw [← ENNReal.ofReal_mul hQb.le, mul_comm]

    )
  refine ⟨fun hv g par w c => (hglue.1 hv g par w c).trans (le_of_eq ?_), hglue.2⟩
  congr 1
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]

end Core

end Balaban.LargeField
