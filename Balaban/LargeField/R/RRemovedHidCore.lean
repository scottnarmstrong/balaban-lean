/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidChain
public import Balaban.LargeField.R.RRemovedRegroupCanon
public import Balaban.LargeField.R.RRemovedRegroupOut

/-!
# The weights of the core operators in the coordinates of the regrouping (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4.  `core_prod_eq`: the product, over the ancestors `P` of scale
`k₁ + 1` and their old parts `C`, of the weights of the core operators at the restrictions of `x` is the product
over the core indices of the weights at the core coordinates `c C` merged with the parameters
`parC (x↾T)` (`core_weight_eq` for every index, `Fintype.prod_sigma`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section CoreProd

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
theorem core_prod_eq {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    (T : Set ↥(locOp geo cs SD KD hH lab m hmK Z).A)
    (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A)
    (hκ2 : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
        (κc ⟨C, Sum.inr q⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc (by omega) C.2.2 q.1).1.1,
              (ancInc (by omega) C.2.2 q.1).1.2.1, (ancInc (by omega) C.2.2 q.1).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (ancInc (by omega) C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K m Z) m))
    (parC : (∀ t : ↥T, VarVal N t.1.1.isSpin) →
        ∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
          OutPar N R (H.localHistory M K k1 C.2.1) k1)
    (hparC : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (ρP : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
          SubCfg N (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1)
            (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A)
        (_ : ∀ x p, ρP x p = x ⟨_, locOp_A_incl geo cs SD KD hmK (mem_ancFin.mp C.1.2)
          (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
        (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A),
        ancOut (N := N) (R := R) C.2.1 C.1.1 (ρP x) =
          mergeOut (H.localHistory M K k1 C.2.1) k1
            (fun y => VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩))) (parC (fun t => x t.1) C))
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s m P Z),
      SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hmK) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s m P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hmK hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A)
    (cC : ∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
      OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
        SubCfg N (H.localHistory M K k1 C.2.1) k1
          (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
    (wT : ∀ t : ↥T, VarVal N t.1.1.isSpin) (hwT : ∀ t, wT t = x t.1)
    (hc1 : ∀ C y, (cC C).1 y = VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩)))
    (hc2 : ∀ C q, VarVal.toEuc ((cC C).2 q) = VarVal.toEuc (x (κc ⟨C, Sum.inr q⟩)))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (∏ P : ↥(H.ancFin (k1 + 1) m Z), ∏ C : ↥(H.parts k1 P.1),
        (locOp geo cs SD KD hH lab k1
          ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hmK) C.1).T.absW
          (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
          (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g) =
      ∏ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).T.absW
          (mergeOut (H.localHistory M K k1 C.2.1) k1 (cC C).1 (parC wT C)) (cC C).2 hv g := by
  rw [← Fintype.prod_sigma' (fun (P : ↥(H.ancFin (k1 + 1) m Z)) (C : ↥(H.parts k1 P.1)) =>
    (locOp geo cs SD KD hH lab k1
          ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hmK) C.1).T.absW
          (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
          (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g)]
  refine Finset.prod_congr rfl fun C _ => ?_
  exact core_weight_eq geo cs SD KD h hmK hq T κc hκ2 parC C
    (ρ (k1 + 1) (by omega) C.1.1 (mem_ancFin.mp C.1.2))
    (fun x p => hρ _ _ _ _ _ p) (ρ k1 le_rfl C.2.1 (desc_of_parts C.2.2 (mem_ancFin.mp C.1.2)))
    (fun x p => hρ _ _ _ _ _ p) (fun ρP' hρP' x' => hparC C ρP' hρP' x') x (cC C) wT hwT
    (hc1 C) (hc2 C) hv g

end CoreProd

end Balaban.LargeField
