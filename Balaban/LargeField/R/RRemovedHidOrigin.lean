/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidNode
public import Balaban.LargeField.R.RRemovedWindowAnc

/-!
# The origin of the internal variables of a quiet window (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1), the coverage lemma.  Along a quiet window
`[k₁, t)` of `Y`, every internal variable of the operator of `Y` is either a variable of the operator of
an ancestor `C` at scale `k₁` (included through the ancestor `P` of scale `k₁ + 1`; the core), or a new
variable of the step `s → s + 1` of an ancestor `Y'` of scale `s + 1`, `k₁ ≤ s < t` (`var_origin`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Origin

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The origin of an internal variable** (coverage).  Let `Y` be a component of scale `t ≥ k₁ + 1` with
no kept ancestor of scale above `k₁`.  An internal variable `p` of the operator of `Y` is either (core) the
inclusion into `Y` of a variable `q` of the operator of an old part `C` of an ancestor `P` of scale `k₁ + 1`
(through `ancInc`), or (new) the inclusion into `Y` of the variable `mkVar … s κ y` of scale `s ≥ k₁` of an
ancestor `Y'` of scale `s + 1`. -/
theorem var_origin {k1 : ℕ} :
    ∀ (t : ℕ) (ht : k1 + 1 ≤ t) (htK : t ≤ K) (Y : H.Comp t)
      (_ : ∀ s, k1 < s → ∀ Y' : H.Comp s, H.Desc s t Y' Y → ¬ IsKept H s Y')
      (p : InternalVars (H.localHistory M K t Y) t),
      p ∈ (locOp geo cs SD KD hH lab t htK Y).A →
      (∃ (P' : H.Comp (k1 + 1)) (hd : H.Desc (k1 + 1) t P' Y) (C : H.Comp k1) (hC : C ∈ H.parts k1 P')
        (q : InternalVars (H.localHistory M K k1 C) k1),
        q ∈ (locOp geo cs SD KD hH lab k1 (by omega) C).A ∧
        p = ⟨⟨Fin.castLE hd.le (ancInc (by omega) hC q).1.1, (ancInc (by omega) hC q).1.2.1,
          (ancInc (by omega) hC q).1.2.2⟩, inclVar_mem htK hd (ancInc (by omega) hC q)⟩) ∨
      (∃ (s : ℕ) (_ : k1 ≤ s) (_ : s < t) (Y' : H.Comp (s + 1)) (hd : H.Desc (s + 1) t Y' Y)
        (κ : VarKind) (y : BlockAt S n M K s)
        (hb : BlockSub (S := S) (n := n) (M := M) (K := K) s y
          (varSet (H.localHistory M K (s + 1) Y') s κ)),
        p = ⟨⟨Fin.castLE hd.le ⟨s, Nat.lt_succ_self s⟩, κ, y⟩,
          inclVar_mem htK hd (mkVar (H.localHistory M K (s + 1) Y') (s + 1) s κ y (Nat.lt_succ_self s) hb)⟩) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    intro htK Y hnk p hp
    have hnkY : ¬ IsKept H (k1 + 1) Y := hnk (k1 + 1) (by omega) Y (Desc.refl Y)
    rw [locOp_level geo cs SD KD htK hnkY] at hp
    have hp' : p ∈ preVars htK Y (fun Y1 _ => locOp geo cs SD KD hH lab k1 (by omega) Y1) := hp
    rcases hp' with hnew | ⟨Y1, hY1, q, hq, hqp⟩
    · right
      obtain ⟨⟨⟨j, hj⟩, κ, y⟩, hmem⟩ := p
      have hjk : j = k1 := hnew
      subst hjk
      exact ⟨j, le_rfl, Nat.lt_succ_self j, Y, Desc.refl Y, κ, y, hmem, rfl⟩
    · left
      exact ⟨Y, Desc.refl Y, Y1, hY1, q, hq, by rw [← hqp]; rfl⟩
  | succ b hb ih =>
    intro htK Y hnk p hp
    have hnkY : ¬ IsKept H (b + 1) Y := hnk (b + 1) (by omega) Y (Desc.refl Y)
    rw [locOp_level geo cs SD KD htK hnkY] at hp
    have hp' : p ∈ preVars htK Y (fun Y1 _ => locOp geo cs SD KD hH lab b (by omega) Y1) := hp
    rcases hp' with hnew | ⟨Y1, hY1, q, hq, hqp⟩
    · right
      obtain ⟨⟨⟨j, hj⟩, κ, y⟩, hmem⟩ := p
      have hjk : j = b := hnew
      subst hjk
      exact ⟨j, by omega, Nat.lt_succ_self j, Y, Desc.refl Y, κ, y, hmem, rfl⟩
    · obtain ⟨hrem, hs⟩ := (H.mem_parts b Y1 Y).mp hY1
      have hnk1 : ∀ s, k1 < s → ∀ Y' : H.Comp s, H.Desc s b Y' Y1 → ¬ IsKept H s Y' :=
        fun s hs1 Y' hd => hnk s hs1 Y' (Desc.step b Y' Y1 Y hd hrem hs)
      rcases ih (by omega) Y1 hnk1 q hq with
        ⟨P', hd, C, hC, q', hq', hqe⟩ | ⟨s, hs1, hst, Y', hd, κ, y, hbb, hqe⟩
      · left
        refine ⟨P', Desc.step b P' Y1 Y hd hrem hs, C, hC, q', hq', ?_⟩
        rw [← hqp, hqe]
        rfl
      · right
        refine ⟨s, hs1, by omega, Y', Desc.step b Y' Y1 Y hd hrem hs, κ, y, hbb, ?_⟩
        rw [← hqp, hqe]
        rfl

open Classical in
/-- **Coverage**: every internal variable of the operator of `Z` (top component of a quiet window `[k₁, m' + 1)`)
is a core coordinate (`κc`), a Gaussian node, or a shell variable: its value `x p` satisfies
`|‖x p‖² - 1| < rad j` for some step `j ∈ [k₁, m']`, given the shell conditions of the new′ variables
(`hN`) and of the new outputs of the ancestors (`hO`) of the steps `[k₁, m']`. -/
theorem shell_cover {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (rad : ℕ → ℝ)
    (Good : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A → Prop)
    (hN : ∀ x, Good x → ∀ (j : ℕ) (_ : k1 ≤ j) (_ : j ≤ m') (c : H.Comp (j + 1)) (hd : H.Desc (j + 1) (m' + 1) c Z)
      (κ : VarKind) (y : BlockAt S n M K j)
      (hb : BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (varSet (H.localHistory M K (j + 1) c) j κ)),
      mkVar (H.localHistory M K (j + 1) c) (j + 1) j κ y (Nat.lt_succ_self j) hb ∈
        newPrimeVars (H.localHistory M K (j + 1) c) j →
      ∀ hA : (⟨⟨Fin.castLE hd.le ⟨j, Nat.lt_succ_self j⟩, κ, y⟩,
          inclVar_mem hm hd (mkVar (H.localHistory M K (j + 1) c) (j + 1) j κ y
            (Nat.lt_succ_self j) hb)⟩ : InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1)) ∈
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).A,
        |‖VarVal.toEuc (x ⟨_, hA⟩)‖ ^ 2 - 1| < rad j)
    (hO : ∀ x, Good x → ∀ (j : ℕ) (_ : k1 ≤ j) (hj2 : j + 1 ≤ m') (c : H.Comp (j + 1)) (hd : H.Desc (j + 1) (m' + 1) c Z)
      (y : BlockAt S n M K (j + 1)) (_ : newOutP (H.localHistory M K (j + 1) c) j y)
      (hb : BlockSub (S := S) (n := n) (M := M) (K := K) (j + 1) y
        (varSet (H.localHistory M K (m' + 1) Z) (j + 1) .large))
      (hA : mkVar (H.localHistory M K (m' + 1) Z) (m' + 1) (j + 1) .large y (by omega) hb ∈
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A),
      |‖VarVal.toEuc (x ⟨_, hA⟩)‖ ^ 2 - 1| < rad j)
    (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (by omega) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hκ1 : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (κc ⟨C, Sum.inl y⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hm (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1)))
    (hκ2 : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 (by omega) C.2.1).A),
        (κc ⟨C, Sum.inr q⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc (by omega) C.2.2 q.1).1.1,
              (ancInc (by omega) C.2.2 q.1).1.2.1, (ancInc (by omega) C.2.2 q.1).1.2.2⟩,
            inclVar_mem hm (mem_ancFin.mp C.1.2) (ancInc (by omega) C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1)))
    (p : ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A) :
    p ∈ Set.range κc ∨ (p.1.1.2.1 = VarKind.large ∧ nd ⟨(p.1.1.1 : ℕ), p.1.1.2.2⟩) ∨
      ∃ j, k1 ≤ j ∧ j ≤ m' ∧ k1 ≤ (p.1.1.1 : ℕ) ∧
        ∀ x, Good x → |‖VarVal.toEuc (x p)‖ ^ 2 - 1| < rad j := by
  obtain ⟨pi, hpA⟩ := p
  rcases var_origin geo cs SD KD (m' + 1) (by omega) hm Z hq pi hpA with
    ⟨P', hd, C, hC, q, hq', hqe⟩ | ⟨s, hs1, hst, Y', hd, κ, y, hb, hqe⟩
  · left
    refine ⟨Sigma.mk (Sigma.mk (⟨P', mem_ancFin.mpr hd⟩ : ↥(H.ancFin (k1 + 1) (m' + 1) Z))
      (⟨C, hC⟩ : ↥(H.parts k1 P'))) (Sum.inr ⟨q, hq'⟩), ?_⟩
    exact Subtype.ext ((hκ2 _ _).trans hqe.symm)
  · subst hqe
    have hs' : s ≤ m' := by omega
    have hK1 : s + 1 ≤ K := by omega
    rcases κ with _ | _
    · by_cases hnc : BlockSub (S := S) (n := n) (M := M) (K := K) s y
          ((H.localHistory M K (s + 1) Y').Z s)ᶜ
      · right; right
        exact ⟨s, hs1, hs', hs1, fun x hx => hN x hx s hs1 hs' Y' hd VarKind.large y hb ⟨rfl, Or.inr hnc⟩ hpA⟩
      · have hz := ZBlk_of_not_blockSub_compl hK1 Y' hnc
        obtain ⟨Y'', hY'', hcube⟩ := (ZBlk_pre_iff hK1 Y' y).mp hz
        have hz'' : ZBlk (H.localHistory M K s Y'') s y :=
          (ZBlk_self_iff (by omega) Y'' y).mpr hcube
        rcases Nat.eq_or_lt_of_le hs1 with h | h
        · subst h
          left
          refine ⟨Sigma.mk (Sigma.mk (⟨Y', mem_ancFin.mpr hd⟩ : ↥(H.ancFin (k1 + 1) (m' + 1) Z))
            (⟨Y'', hY''⟩ : ↥(H.parts k1 Y'))) (Sum.inl ⟨y, ZBlk_mem_Vblk (by omega) Y'' y hz'', hz''⟩),
            ?_⟩
          exact Subtype.ext (hκ1 _ _)
        · obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by omega⟩
          have hj : k1 ≤ j := by omega
          have hdY'' := desc_of_parts hY'' hd
          rcases zblk_gauss_or_new (by omega : j + 1 ≤ K) Y'' hz'' with hg | ho
          · right; left
            exact ⟨rfl, (hnd j y).mpr ⟨hj, by omega, Y'', mem_ancFin.mpr hdY'', hg⟩⟩
          · right; right
            exact ⟨j, hj, by omega, (by show k1 ≤ j + 1; omega), fun x hx => hO x hx j hj (by omega) Y'' hdY'' y ho _ hpA⟩
    · right; right
      exact ⟨s, hs1, hs', hs1, fun x hx => hN x hx s hs1 hs' Y' hd VarKind.fluct y hb ⟨rfl, Or.inl rfl⟩ hpA⟩

end Origin

end Balaban.LargeField
