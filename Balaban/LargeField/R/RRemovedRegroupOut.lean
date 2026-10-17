/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupTheta

/-!
# The regrouping of the removed-outcome window integral: the outputs of the ancestors (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, step (3).  In the unrolled weight of the operator of
`Z` (`locOp_absW_unroll`) the operator of an ancestor `C` of scale `k₁` is evaluated at the outputs
`ancOut C P (ρ_P x)`, `ρ_P x` the variables of the successor `P` read from `x`.  `exists_parC`: these
outputs are `mergeOut (core outputs) (parC (window coordinates))`, the core outputs being the
coordinates `κc ⟨C, inl y⟩` of `x` (`exists_coreCoord`), and the parameters on the margin
`V_C ∖ Z_C` a function `parC` of the coordinates of `x` in a set `T` that contains the
scale-`k₁` large-field variables of the margins.  `VarVal.toEuc_injective` converts the statements
in terms of `toEuc` into equalities of configurations.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

theorem VarVal.toEuc_injective {N : ℕ} (b : Bool) :
    Function.Injective (VarVal.toEuc : VarVal N b → EuclideanSpace ℝ (Fin N)) := by
  cases b
  · exact fun _ _ h => h
  · exact fun u v h => Subtype.ext h

section Out

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The outputs of the ancestors** (Lemma III.8.7 (4), step (3)): along a quiet window, for the
ancestor `C` of scale `k₁` (an old part of the ancestor `P` of scale `k₁ + 1`), the outputs
`ancOut C P (ρ_P x)` at which its operator is evaluated are the core outputs (the coordinates
`κc ⟨C, inl y⟩` of `x`, `hκ1`) merged with parameters `parC` that depend on `x` only through its
coordinates in `T`.  The set `T` is assumed to contain the scale-`k₁` large-field variables
of `P` at the margin blocks `V_C ∖ Z_C` that are integrated by the operator of `P` (`hTm`). -/
theorem exists_parC {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    (T : Set ↥(locOp geo cs SD KD hH lab m hmK Z).A)
    (hTm : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (b : BlockAt S n M K k1) (_ : b ∈ Vblk R (H.localHistory M K k1 C.2.1) k1)
      (_ : ¬ ZBlk (H.localHistory M K k1 C.2.1) k1 b)
      (hb : BlockSub (S := S) (n := n) (M := M) (K := K) k1 b
        (varSet (H.localHistory M K (k1 + 1) C.1.1) k1 .large))
      (hA : mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large b (Nat.lt_succ_self k1) hb ∈
        (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A),
      (⟨⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le
          (mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large b (Nat.lt_succ_self k1) hb).1.1,
          (mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large b (Nat.lt_succ_self k1) hb).1.2.1,
          (mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large b (Nat.lt_succ_self k1) hb).1.2.2⟩,
          inclVar_mem hmK (mem_ancFin.mp C.1.2)
            (mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large b (Nat.lt_succ_self k1) hb)⟩,
        locOp_A_incl geo cs SD KD hmK (mem_ancFin.mp C.1.2)
          (fun t ht Y' h' => hq t (by omega) Y' h') _ hA⟩ :
        ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∈ T)
    (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A)
    (hκ1 : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (κc ⟨C, Sum.inl y⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K m Z) m)) :
    ∃ parC : (∀ t : ↥T, VarVal N t.1.1.isSpin) →
        ∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
          OutPar N R (H.localHistory M K k1 C.2.1) k1,
      ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (ρP : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
          SubCfg N (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1)
            (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A)
        (_ : ∀ x p, ρP x p = x ⟨_, locOp_A_incl geo cs SD KD hmK (mem_ancFin.mp C.1.2)
          (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
        (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A),
        ancOut (N := N) (R := R) C.2.1 C.1.1 (ρP x) =
          mergeOut (H.localHistory M K k1 C.2.1) k1
            (fun y => VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩))) (parC (fun t => x t.1) C) := by
  classical
  have hK : ∀ k : ℕ, k < m → k + 1 ≤ K := fun k hk => by omega
  refine ⟨fun wT C y => if hh : ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k1 y.1
      (varSet (H.localHistory M K (k1 + 1) C.1.1) k1 .large),
      mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 (Nat.lt_succ_self k1) hb ∈
        (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A then
    VarVal.toEuc (wT ⟨⟨⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le
        (mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 (Nat.lt_succ_self k1)
          hh.1).1.1, _, _⟩,
        inclVar_mem hmK (mem_ancFin.mp C.1.2)
          (mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 (Nat.lt_succ_self k1) hh.1)⟩,
        locOp_A_incl geo cs SD KD hmK (mem_ancFin.mp C.1.2)
          (fun t ht Y' h' => hq t (by omega) Y' h') _ hh.2⟩,
        hTm C y.1 y.2.1 y.2.2 hh.1 hh.2⟩) else 0, ?_⟩
  intro C ρP hρ x
  funext y
  show subVarField N (ρP x) k1 y.1 = _
  unfold mergeOut
  by_cases hz : ZBlk (H.localHistory M K k1 C.2.1) k1 y.1
  · simp only [hz, ↓reduceDIte]
    have hK' : k1 + 1 ≤ K := hK k1 h
    have hnk := hq (k1 + 1) (by omega) C.1.1 (mem_ancFin.mp C.1.2)
    have h1 : ∃ hj : k1 < k1 + 1, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k1 y.1
        (varSet (H.localHistory M K (k1 + 1) C.1.1) k1 .large),
        mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 hj hb ∈
          (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A :=
      ⟨Nat.lt_succ_self k1, outBlock_large hK' C.1.1 C.2.2 y.1 hz,
        newVars_sub_locOp_A geo cs SD KD hK' hnk
          (oldVar_val hK' C.1.1 C.2.2 ⟨y.1, y.2, hz⟩)⟩
    unfold subVarField
    simp only [h1, ↓reduceDIte]
    rw [hρ]
    exact congrArg (fun p => VarVal.toEuc (x p))
      (Subtype.ext (hκ1 C ⟨y.1, y.2, hz⟩).symm)
  · simp only [hz, ↓reduceDIte]
    unfold subVarField
    by_cases h1 : ∃ hj : k1 < k1 + 1, ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k1 y.1
        (varSet (H.localHistory M K (k1 + 1) C.1.1) k1 .large),
        mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 hj hb ∈
          (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A
    · have h2 : ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k1 y.1
          (varSet (H.localHistory M K (k1 + 1) C.1.1) k1 .large),
          mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 (Nat.lt_succ_self k1) hb ∈
            (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A := ⟨h1.2.1, h1.2.2⟩
      rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2), hρ]
      rfl
    · have h2 : ¬ ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) k1 y.1
          (varSet (H.localHistory M K (k1 + 1) C.1.1) k1 .large),
          mkVar (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1) k1 .large y.1 (Nat.lt_succ_self k1) hb ∈
            (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A :=
        fun ⟨hb, hA⟩ => h1 ⟨Nat.lt_succ_self k1, hb, hA⟩
      rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_right_of_eq_false (eq_false h2)]

end Out

end Balaban.LargeField
