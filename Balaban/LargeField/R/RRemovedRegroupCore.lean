/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupDisj
public import Balaban.LargeField.R.RRemovedRegroupPi

/-!
# The regrouping of the removed-outcome window integral: the core coordinates (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, step (2).  The core variables of the window integral
are the outputs `ψ_{k₁}↾Z` and the internal variables of the operators `𝕋_{k₁}(C)` of the
ancestors `C` of `Z` at scale `k₁`, indexed as the old parts `C` of the ancestors `P` of `Z` at
scale `k₁ + 1`.  `exists_coreCoord`: they are distinct coordinates of the internal variables of
`Z`: output `y` of `C` is the variable `(k₁, large, y)` of `P` (`oldVar`), an internal variable `q`
of `C` is the variable `ancInc q` of `P`, and a variable of `P` is a variable of `Z` along the quiet
descent (`inclVar_mem`, `locOp_A_incl`).  The coordinates are pairwise different: for one `P` by
`ancMap_injective`, for different `P` by `incl_ne_of_ne`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section CoreCoord

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The core coordinates** (Lemma III.8.7 (4), step (2)): along a quiet window, the outputs and
internal variables of the operators of the ancestors `C` of `Z` at scale `k₁` (indexed as the old
parts `C` of the ancestors `P` of `Z` at scale `k₁ + 1`) are pairwise different coordinates of the
variables integrated by the operator of `Z`.  An output `y` of `C` is the variable `oldVar y` of
`P`, an internal variable `q` of `C` is `ancInc q`, both included into the variables of `Z`. -/
theorem exists_coreCoord {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y) :
    ∃ κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A,
      Function.Injective κc ∧
      (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (κc ⟨C, Sum.inl y⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K m Z) m)) ∧
      (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
        (κc ⟨C, Sum.inr q⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc (by omega) C.2.2 q.1).1.1,
              (ancInc (by omega) C.2.2 q.1).1.2.1, (ancInc (by omega) C.2.2 q.1).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (ancInc (by omega) C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K m Z) m)) := by
  have hK : k1 + 1 ≤ K := by omega
  -- the coordinate of an index, with membership in `A`
  have key : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (s : OutIdx (K := K) (M := M) R C.2.1 ⊕
        ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
      ∃ p : InternalVars (H.localHistory M K (k1 + 1) C.1.1) (k1 + 1),
        (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le p.1.1, p.1.2.1, p.1.2.2⟩,
          inclVar_mem hmK (mem_ancFin.mp C.1.2) p⟩ :
            InternalVars (H.localHistory M K m Z) m) ∈
          (locOp geo cs SD KD hH lab m hmK Z).A ∧
        p = (ancMap (K := K) (M := M) hK C.1.1
          (fun Y _ => locOp geo cs SD KD hH lab k1 (by omega) Y) ⟨C.2, s⟩).1.1 := by
    intro C s
    refine ⟨_, ?_, rfl⟩
    have hd := mem_ancFin.mp C.1.2
    have hnk := hq (k1 + 1) (by omega) C.1.1 hd
    have hA : (ancMap (K := K) (M := M) hK C.1.1
        (fun Y _ => locOp geo cs SD KD hH lab k1 (by omega) Y) ⟨C.2, s⟩).1.1 ∈
        (locOp geo cs SD KD hH lab (k1 + 1) hK C.1.1).A := by
      rw [locOp_level geo cs SD KD hK hnk]
      exact (ancMap (K := K) (M := M) hK C.1.1
        (fun Y _ => locOp geo cs SD KD hH lab k1 (by omega) Y) ⟨C.2, s⟩).1.2
    exact locOp_A_incl geo cs SD KD hmK hd (fun t ht Y' h' => hq t (by omega) Y' h') _ hA
  choose p hp1 hp2 using key
  refine ⟨fun s => ⟨⟨⟨Fin.castLE (mem_ancFin.mp s.1.1.2).le (p s.1 s.2).1.1,
      (p s.1 s.2).1.2.1, (p s.1 s.2).1.2.2⟩, inclVar_mem hmK (mem_ancFin.mp s.1.1.2) (p s.1 s.2)⟩,
      hp1 s.1 s.2⟩, ?_, ?_, ?_⟩
  · rintro ⟨C, s⟩ ⟨C', s'⟩ hκ
    have h1 := congrArg Subtype.val hκ
    simp only at h1
    by_cases hP : (C.1.1 : H.Comp (k1 + 1)) = C'.1.1
    · rcases C with ⟨⟨P, hP1⟩, Cc⟩
      rcases C' with ⟨⟨P', hP1'⟩, Cc'⟩
      simp only at hP
      subst hP
      have h2 := incl_injective hmK (mem_ancFin.mp hP1) h1
      rw [hp2, hp2] at h2
      have h3 := ancMap_injective (K := K) (M := M) hK P
        (fun Y _ => locOp geo cs SD KD hH lab k1 (by omega) Y)
        (Subtype.ext (Subtype.ext h2))
      simp only [Sigma.mk.injEq] at h3
      obtain ⟨rfl, hs⟩ := h3
      have hs' := eq_of_heq hs
      subst hs'
      rfl
    · exact absurd h1 (incl_ne_of_ne hmK (mem_ancFin.mp C.1.2) (mem_ancFin.mp C'.1.2) hP _ _)
  · intro C y
    have e : p C (Sum.inl y) = oldVar (by omega) C.1.1 C.2.2 y := (hp2 C (Sum.inl y)).trans rfl
    show (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (p C (Sum.inl y)).1.1, _, _⟩, _⟩ :
      InternalVars (H.localHistory M K m Z) m) = _
    rw [e]
  · intro C q
    have e : p C (Sum.inr q) = ancInc (by omega) C.2.2 q.1 := (hp2 C (Sum.inr q)).trans rfl
    show (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (p C (Sum.inr q)).1.1, _, _⟩, _⟩ :
      InternalVars (H.localHistory M K m Z) m) = _
    rw [e]

end CoreCoord

end Balaban.LargeField
