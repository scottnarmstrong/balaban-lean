/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupOut

/-!
# The regrouping of the removed-outcome window integral: the canonical window set (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, step (3).

* `margin_not_ZBlk_of`: a margin block of `V_C ∖ Z_C` is not an output block `Z_{C'}` of any
  component `C'` of the same scale;
* `canonT_spec`: the set `T` of the scale-`k₁` large-field variables of `Z` that are not core
  outputs satisfies the typing hypotheses of `exists_regroup` (`hTo`, `hTi`) and the cover
  hypothesis `hTm` of `exists_parC`;
* `core_snd_eq`: a configuration of the internal variables of `C` whose vector of coordinates is
  that of the core coordinates of `x` is the restriction `ρ_C x`;
* `core_weight_eq`: the weight of the operator of `C` in the unrolled weight is its weight at the
  core variables and window parameters read from `Θ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Canon

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- A margin block `b ∈ V_C ∖ Z_C` is not an output block of any component `C'` of the same
scale (the sets `V_C`, `V_{C'}` of distinct components are disjoint). -/
theorem margin_not_ZBlk_of {k : ℕ} (hkK : k ≤ K) (C C' : H.Comp k) (b : BlockAt S n M K k)
    (hV : b ∈ Vblk R (H.localHistory M K k C) k) (hnz : ¬ ZBlk (H.localHistory M K k C) k b) :
    ¬ ZBlk (H.localHistory M K k C') k b := by
  intro hz'
  by_cases hCC : C' = C
  · subst hCC; exact hnz hz'
  · exact (Set.disjoint_left.mp (locOp_factor (H := H) (one_le_of_comp C) hkK hCC).1)
      (ZBlk_mem_Vblk hkK C' b hz') hV

/-- **The restriction of the core internal variables**: a configuration `c` of the internal
variables of `C` whose vector of values at each `q` is that of the core coordinate
`κc ⟨C, inr q⟩` of `x` is the restriction `ρ_C x` of `x`. -/
theorem core_snd_eq {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
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
    (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
    (ρC : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
      SubCfg N (H.localHistory M K k1 C.2.1) k1
        (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
    (hρC : ∀ x p, ρC x p = x ⟨_, locOp_A_incl geo cs SD KD hmK
      (desc_of_parts C.2.2 (mem_ancFin.mp C.1.2))
      (fun t ht Y' h' => hq t (lt_of_le_of_lt le_rfl ht) Y' h') p.1 p.2⟩)
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A)
    (c : SubCfg N (H.localHistory M K k1 C.2.1) k1
      (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
    (hc : ∀ q, VarVal.toEuc (c q) = VarVal.toEuc (x (κc ⟨C, Sum.inr q⟩))) :
    c = ρC x := by
  funext q
  refine VarVal.toEuc_injective _ ?_
  rw [hc q, hρC x q]
  exact congrArg (fun p => VarVal.toEuc (x p)) (Subtype.ext (hκ2 C q))

/-- **The canonical window set**: let `T` be the set of the scale-`k₁` large-field variables of `Z`
(integrated by its operator) that are not outputs of a core operator.  It satisfies the typing
hypotheses `hTo`, `hTi` of `exists_regroup` and the cover hypothesis `hTm` of `exists_parC`. -/
theorem canonT_spec {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    (T : Set ↥(locOp geo cs SD KD hH lab m hmK Z).A)
    (hT : ∀ p : ↥(locOp geo cs SD KD hH lab m hmK Z).A, p ∈ T ↔
      ((p.1.1.1 : Fin m).val = k1 ∧ p.1.1.2.1 = VarKind.large ∧
        ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
          (y : OutIdx (K := K) (M := M) R C.2.1), p.1 ≠
            (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K m Z) m))) :
    (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (y : OutIdx (K := K) (M := M) R C.2.1)
      (hy : (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K m Z) m) ∈ (locOp geo cs SD KD hH lab m hmK Z).A),
      (⟨_, hy⟩ : ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∉ T) ∧
    (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
      (hy : (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc (by omega) C.2.2 q.1).1.1,
              (ancInc (by omega) C.2.2 q.1).1.2.1, (ancInc (by omega) C.2.2 q.1).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (ancInc (by omega) C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K m Z) m) ∈ (locOp geo cs SD KD hH lab m hmK Z).A),
      (⟨_, hy⟩ : ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∉ T) ∧
    (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
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
        ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∈ T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C y hy hmem
    exact ((hT _).mp hmem).2.2 C y rfl
  · intro C q hy hmem
    have h1 := ((hT _).mp hmem).1
    have h2 := q.1.1.1.2
    simp only [ancInc, Fin.val_castLE, Fin.val_castSucc] at h1
    omega
  · intro C b hV hnz hb hA
    refine (hT _).mpr ⟨rfl, rfl, ?_⟩
    intro C' y' heq
    have e1 := congrArg (fun p : InternalVars (H.localHistory M K m Z) m => p.1) heq
    simp only [mkVar, oldVar, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at e1
    obtain ⟨-, -, e3⟩ := e1
    have hb' : b = y'.1 := e3
    exact margin_not_ZBlk_of (by omega) C.2.1 C'.2.1 b hV hnz (hb' ▸ y'.2.2)

/-- **The weight of a core operator in the coordinates of `Θ`** (step (3)): the weight of the
operator of the ancestor `C` at the outputs `ancOut C P (ρ_P x)` and the variables `ρ_C x` read from
`x` is the weight at the core outputs and variables `cC` (the values of `Θ` on the core coordinates,
`hc1`, `hc2`) merged with the parameters `parC wT`, `wT` the values of `Θ` on the window
coordinates in `T` (`hwT`).  This is the integrand of `hcore_of_anc`, with `parC par w C` the value
of `parC` at the `T`-component of `w`. -/
theorem core_weight_eq {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
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
    (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
    (ρP : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
      SubCfg N (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1)
        (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A)
    (hρP : ∀ x p, ρP x p = x ⟨_, locOp_A_incl geo cs SD KD hmK (mem_ancFin.mp C.1.2)
      (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
    (ρC : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
      SubCfg N (H.localHistory M K k1 C.2.1) k1
        (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
    (hρC : ∀ x p, ρC x p = x ⟨_, locOp_A_incl geo cs SD KD hmK
      (desc_of_parts C.2.2 (mem_ancFin.mp C.1.2))
      (fun t ht Y' h' => hq t (lt_of_le_of_lt le_rfl ht) Y' h') p.1 p.2⟩)
    (hpar : ∀ (ρP' : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A →
          SubCfg N (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1)
            (locOp geo cs SD KD hH lab (k1 + 1) (by omega) C.1.1).A)
        (_ : ∀ x p, ρP' x p = x ⟨_, locOp_A_incl geo cs SD KD hmK (mem_ancFin.mp C.1.2)
          (fun t ht Y' h' => hq t (by omega) Y' h') p.1 p.2⟩)
        (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A),
        ancOut (N := N) (R := R) C.2.1 C.1.1 (ρP' x) =
          mergeOut (H.localHistory M K k1 C.2.1) k1
            (fun y => VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩))) (parC (fun t => x t.1) C))
    (x : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A)
    (cC : OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
      SubCfg N (H.localHistory M K k1 C.2.1) k1
        (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
    (wT : ∀ t : ↥T, VarVal N t.1.1.isSpin) (hwT : ∀ t, wT t = x t.1)
    (hc1 : ∀ y, cC.1 y = VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩)))
    (hc2 : ∀ q, VarVal.toEuc (cC.2 q) = VarVal.toEuc (x (κc ⟨C, Sum.inr q⟩)))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).T.absW
        (ancOut (N := N) (R := R) C.2.1 C.1.1 (ρP x)) (ρC x) hv g =
      (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).T.absW
        (mergeOut (H.localHistory M K k1 C.2.1) k1 cC.1 (parC wT C)) cC.2 hv g := by
  have e1 : wT = fun t : ↥T => x t.1 := funext hwT
  have e2 : (fun y => VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩))) = cC.1 := funext fun y => (hc1 y).symm
  have e3 : cC.2 = ρC x := core_snd_eq geo cs SD KD h hmK hq κc hκ2 C ρC hρC x cC.2 hc2
  rw [hpar ρP hρP x, e2, ← e1, ← e3]

end Canon

end Balaban.LargeField
