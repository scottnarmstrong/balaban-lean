/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidOrigin
public import Balaban.LargeField.R.RRemovedChainBound

/-!
# The shell conditions of the quiet steps in the variables of the top component (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  The indicators of the shells of the new
outputs and of the new′ variables of the quiet steps of the window (`absW_quiet_le`), evaluated at the
restrictions to the ancestors of a configuration `x` of the variables of `Z`, give the shell conditions on
the coordinates of `x` used by the coverage lemma `shell_cover` (`tubes_imp_shell`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Tube

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The shell conditions of the steps of the window in the variables of the top component.**  Let `TB k Z' o x`
be the conjunction of the shell conditions of the new outputs of `o` and of the new′ variables of `x` for
the step `k → k + 1` of `Z'`, with radius `r k`.  If it holds for the top step at `(o, x)` and for the
steps `j ∈ [k₁, m')` of the ancestors `c` of `Z` at the restrictions `(ancOut c P (ρ_P x), ρ_c x)`,
then the new′ variables and the new outputs of every ancestor are in their shells, read from `x`. -/
theorem tubes_imp_shell {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (r : ℕ → ℝ)
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
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (htop : TB m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x))
    (hanc : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)),
      TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
          (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD
            ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) :
    (∀ (j : ℕ) (_ : k1 ≤ j) (_ : j ≤ m') (c : H.Comp (j + 1)) (hd : H.Desc (j + 1) (m' + 1) c Z)
      (κ : VarKind) (y : BlockAt S n M K j)
      (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (varSet (H.localHistory M K (j + 1) c) j κ)),
      mkVar (H.localHistory M K (j + 1) c) (j + 1) j κ y (Nat.lt_succ_self j) hb ∈
        newPrimeVars (H.localHistory M K (j + 1) c) j →
      ∀ hA : (⟨⟨Fin.castLE hd.le ⟨j, Nat.lt_succ_self j⟩, κ, y⟩,
          inclVar_mem hm hd (mkVar (H.localHistory M K (j + 1) c) (j + 1) j κ y
            (Nat.lt_succ_self j) hb)⟩ : InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1)) ∈
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).A,
        |‖VarVal.toEuc (x ⟨_, hA⟩)‖ ^ 2 - 1| < r j) ∧
    (∀ (j : ℕ) (_ : k1 ≤ j) (hj2 : j + 1 ≤ m') (c : H.Comp (j + 1))
      (hd : H.Desc (j + 1) (m' + 1) c Z)
      (y : BlockAt S n M K (j + 1)) (_ : newOutP (H.localHistory M K (j + 1) c) j y)
      (hb : BlockSub (S := S) (n := n) (M := M) (K := K) (j + 1) y
        (varSet (H.localHistory M K (m' + 1) Z) (j + 1) .large))
      (hA : mkVar (H.localHistory M K (m' + 1) Z) (m' + 1) (j + 1) .large y (by omega) hb ∈
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A),
      |‖VarVal.toEuc (x ⟨_, hA⟩)‖ ^ 2 - 1| < r j) := by
  classical
  refine ⟨?_, ?_⟩
  · intro j hj1 hj2 c hd κ y hb hmem hA
    by_cases hjm : j = m'
    · subst hjm
      have hcZ : Z = c := hd.unique (Desc.refl c)
      subst hcZ
      exact ((hTB _ _ _ _).mp htop).2 ⟨_, hmem⟩
    · have hjm' : j < m' := by omega
      have hc' : c ∈ H.ancFin (j + 1) (m' + 1) Z := mem_ancFin.mpr hd
      rw [ancFin_eq_biUnion_parts (by omega : j + 1 < m' + 1) Z] at hc'
      obtain ⟨P, hP, hcP⟩ := Finset.mem_biUnion.mp hc'
      have h5 := ((hTB _ _ _ _).mp (hanc ⟨j, Finset.mem_Ico.mpr ⟨hj1, hjm'⟩⟩ ⟨P, hP⟩ ⟨c, hcP⟩)).2
        ⟨_, hmem⟩
      simp only [restrictSub, newRestrict, hρ] at h5
      exact h5
  · intro j hj1 hj2 c hd y hy hb hA
    have hc' : c ∈ H.ancFin (j + 1) (m' + 1) Z := mem_ancFin.mpr hd
    rw [ancFin_eq_biUnion_parts (by omega : j + 1 < m' + 1) Z] at hc'
    obtain ⟨P, hP, hcP⟩ := Finset.mem_biUnion.mp hc'
    have hdP := mem_ancFin.mp hP
    have hK : j + 1 + 1 ≤ K := hdP.le.trans hm
    have hzb := newOutP_zblk (by omega : j + 1 ≤ K) c hy
    have hV := ZBlk_mem_Vblk (R := R) (by omega : j + 1 ≤ K) c y hzb
    have h1 := ((hTB _ _ _ _).mp (hanc ⟨j, Finset.mem_Ico.mpr ⟨hj1, by omega⟩⟩ ⟨P, hP⟩ ⟨c, hcP⟩)).1
      ⟨y, hV, hy⟩
    have hbP := outBlock_large hK P hcP y hzb
    have hAP : mkVar (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1) (j + 1) .large y (by omega) hbP ∈
        (locOp geo cs SD KD hH lab (j + 1 + 1) hK P).A :=
      newVars_sub_locOp_A geo cs SD KD hK (fun hk => hq _ (by omega) P hdP hk) rfl
    have h2 := subVarField_rho geo cs SD KD hm hdP
      (fun t ht Y' h' => hq t (by omega) Y' h') x
      (ρ (j + 1 + 1) (by omega) P hdP x) (fun p => hρ _ _ _ _ _ p) y (by omega) hbP hAP
    have h3 : subVarField N x (j + 1) y = VarVal.toEuc (x ⟨_, hA⟩) := by
      have hex : ∃ hj : j + 1 < m' + 1, ∃ hb' : BlockSub (S := S) (n := n) (M := M) (K := K) (j + 1) y
          (varSet (H.localHistory M K (m' + 1) Z) (j + 1) .large),
          mkVar (H.localHistory M K (m' + 1) Z) (m' + 1) (j + 1) .large y hj hb' ∈
            (locOp geo cs SD KD hH lab (m' + 1) hm Z).A := ⟨by omega, hb, hA⟩
      simp only [subVarField, hex, dite_true]
    have h4 : restrictOutPart (ancOut (N := N) (R := R) c P (ρ (j + 1 + 1) (by omega) P hdP x))
        (newOutP (H.localHistory M K (j + 1) c) j) ⟨y, hV, hy⟩ =
        subVarField N x (j + 1) y := by
      rw [← h2]
      rfl
    rw [h4, h3] at h1
    exact h1

end Tube

end Balaban.LargeField
