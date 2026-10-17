/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.LocOpBound
public import Balaban.LargeField.R.RRemovedWindowCore

/-!
# The window integral: the ancestors at scale `k₁` (Lemma III.8.7 (4)) (W909)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4.  Variables of the ancestors along a descent
`Desc s m Y Z` of a quiet window: the variables of `𝕋_s(Y)` are variables of `𝕋_m(Z)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Incl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- The variable sets of an ancestor are contained in those of its descendant (below the scale of
the ancestor). -/
theorem varSet_desc_mono {s m : ℕ} (hm : m ≤ K) {Y : H.Comp s} {Z : H.Comp m}
    (h : H.Desc s m Y Z) {j : ℕ} (hj : j < s) (κ : VarKind) :
    varSet (H.localHistory M K s Y) j κ ⊆ varSet (H.localHistory M K m Z) j κ := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step b Y Y' Y'' hd hrem hs ih =>
    have hsb := hd.le
    exact (ih (by omega)).trans (varSet_mono (M := M) hm
      ((H.mem_parts b Y' Y'').mpr ⟨hrem, hs⟩) (by omega) κ)

theorem inclVar_mem {s m : ℕ} (hm : m ≤ K) {Y : H.Comp s} {Z : H.Comp m}
    (h : H.Desc s m Y Z) (p : InternalVars (H.localHistory M K s Y) s) :
    BlockSub (S := S) (n := n) (M := M) (K := K) (↑(Fin.castLE h.le p.1.1)) p.1.2.2
      (varSet (H.localHistory M K m Z) (↑(Fin.castLE h.le p.1.1)) p.1.2.1) :=
  fun x hx => varSet_desc_mono hm h p.1.1.2 p.1.2.1 (p.2 x hx)


section A

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- The variables integrated by the operator of an ancestor are integrated by the operator of the
descendant, along a quiet descent. -/
theorem locOp_A_incl {m : ℕ} (hm : m ≤ K) {Z : H.Comp m} :
    ∀ {s : ℕ} {Y : H.Comp s} (h : H.Desc s m Y Z),
      (∀ t, s < t → ∀ Y' : H.Comp t, H.Desc t m Y' Z → ¬ IsKept H t Y') →
      ∀ q : InternalVars (H.localHistory M K s Y) s,
        q ∈ (locOp geo cs SD KD hH lab s (h.le.trans hm) Y).A →
        (⟨⟨Fin.castLE h.le q.1.1, q.1.2.1, q.1.2.2⟩, inclVar_mem hm h q⟩ :
          InternalVars (H.localHistory M K m Z) m) ∈ (locOp geo cs SD KD hH lab m hm Z).A := by
  intro s Y h
  induction h with
  | refl => intro _ q hq; exact hq
  | step b Y Y' Y'' hd hrem hs ih =>
    intro hq q hqA
    have hsb := hd.le
    have hK : b + 1 ≤ K := hm
    have hYp : Y' ∈ H.parts b Y'' := (H.mem_parts b Y' Y'').mpr ⟨hrem, hs⟩
    have hqb : ∀ t, s < t → ∀ Y3 : H.Comp t, H.Desc t b Y3 Y' → ¬ IsKept H t Y3 :=
      fun t ht Y3 h3 => hq t ht Y3 (Desc.step b Y3 Y' Y'' h3 hrem hs)
    have h1 := ih (by omega) hqb q hqA
    have hnk : ¬ IsKept H (b + 1) Y'' := hq (b + 1) (by omega) Y'' (Desc.refl Y'')
    rw [locOp_level geo cs SD KD (lab := lab) (hH := hH) hm hnk]
    exact preVars_anc hK Y''
      (fun Y3 _ => locOp geo cs SD KD hH lab b (by omega) Y3) Y' hYp _ h1

/-- At a component that is not kept the operator integrates the new variables. -/
theorem newVars_sub_locOp_A {k : ℕ} (hk : k + 1 ≤ K) {Z' : H.Comp (k + 1)}
    (h : ¬ IsKept H (k + 1) Z') :
    newVars (H.localHistory M K (k + 1) Z') k ⊆
      (locOp geo cs SD KD hH lab (k + 1) hk Z').A := by
  rw [locOp_level geo cs SD KD (lab := lab) (hH := hH) hk h]
  exact preVars_new hk Z' _

/-- At a component that is not kept the operator integrates the variables of the operators of
the old parts. -/
theorem locOp_A_anc {k : ℕ} (hk : k + 1 ≤ K) {Z' : H.Comp (k + 1)}
    (h : ¬ IsKept H (k + 1) Z') {Y : H.Comp k} (hY : Y ∈ H.parts k Z') :
    ∀ p ∈ (locOp geo cs SD KD hH lab k (by omega) Y).A,
      ancInc hk hY p ∈ (locOp geo cs SD KD hH lab (k + 1) hk Z').A := by
  rw [locOp_level geo cs SD KD (lab := lab) (hH := hH) hk h]
  exact preVars_anc hk Z' (fun Y3 _ => locOp geo cs SD KD hH lab k (by omega) Y3) Y hY

/-- **One level of the unrolling**: at a component that is not kept, the weight `K e^{Re b}` of the
operator is the weight of the step kernel at the new variables times the weights of the operators
of the old parts at `(ψ_k↾V_Y, x↾Y)`. -/
theorem locOp_absW_level {k : ℕ} (hk : k + 1 ≤ K) {Z' : H.Comp (k + 1)}
    (h : ¬ IsKept H (k + 1) Z')
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1)
      (locOp geo cs SD KD hH lab (k + 1) hk Z').A)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) :
    (locOp geo cs SD KD hH lab (k + 1) hk Z').T.absW o x hv g =
      (SD.ker k (H.localHistory M K (k + 1) Z')).absW o
        (newRestrict (H.localHistory M K (k + 1) Z')
          (newVars_sub_locOp_A geo cs SD KD hk h) x) hv g *
      ∏ Y : ↥(H.parts k Z'),
        (locOp geo cs SD KD hH lab k (by omega) Y.1).T.absW (ancOut Y.1 Z' x)
          (ancRestrict hk Y.2 (locOp_A_anc geo cs SD KD hk h Y.2) x) hv g := by
  have key : ∀ (P : OpPkg N R (H.localHistory M K (k + 1) Z') (k + 1))
      (hP : P = preOp geo cs SD hH hk Z' (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y))
      (x : SubCfg N (H.localHistory M K (k + 1) Z') (k + 1) P.A)
      (h1 : newVars (H.localHistory M K (k + 1) Z') k ⊆ P.A)
      (h2 : ∀ Y : H.Comp k, ∀ hY : Y ∈ H.parts k Z',
        ∀ p ∈ (locOp geo cs SD KD hH lab k (by omega) Y).A, ancInc hk hY p ∈ P.A),
      P.T.absW o x hv g =
        (SD.ker k (H.localHistory M K (k + 1) Z')).absW o
          (newRestrict (H.localHistory M K (k + 1) Z') h1 x) hv g *
        ∏ Y : ↥(H.parts k Z'),
          (locOp geo cs SD KD hH lab k (by omega) Y.1).T.absW (ancOut Y.1 Z' x)
            (ancRestrict hk Y.2 (h2 Y.1 Y.2) x) hv g := by
    intro P hP x h1 h2
    subst hP
    exact absW_preKernel hk Z' (fun Y _ => locOp geo cs SD KD hH lab k (by omega) Y)
      (SD.ker k (H.localHistory M K (k + 1) Z')) o x hv g
  exact key _ (locOp_level geo cs SD KD (lab := lab) (hH := hH) hk h) x _ _

theorem desc_of_parts {b m : ℕ} {c : H.Comp b} {P : H.Comp (b + 1)} {Z : H.Comp m}
    (hc : c ∈ H.parts b P) (h : H.Desc (b + 1) m P Z) : H.Desc b m c Z :=
  Desc.trans (Desc.single ((H.mem_parts b c P).mp hc).1 ((H.mem_parts b c P).mp hc).2) h

/-- The dependent product over the subtype of a finset is the product over the finset of the
function extended by `1`. -/
theorem prod_coe_dep {α β : Type*} [DecidableEq α] [CommMonoid β] (s : Finset α)
    (f : ∀ x, x ∈ s → β) :
    ∏ x : ↥s, f x.1 x.2 = ∏ x ∈ s, if h : x ∈ s then f x h else 1 := by
  rw [← Finset.prod_attach s (fun x => if h : x ∈ s then f x h else 1)]
  exact Finset.prod_congr rfl fun x _ => by simp

/-- The multi-scale ancestor bijection, as a reindexing of products: the ancestors at scale `a`
of `Z'` (scale `b + 1`) are the disjoint union over the old parts `Y` of `Z'` of the ancestors at
scale `a` of `Y` (`ancFin_succ`, `ancFin_disjoint`). -/
theorem prod_ancFin_succ_dep {β : Type*} [CommMonoid β] {a b : ℕ} (hab : a ≤ b)
    (Z' : H.Comp (b + 1)) (F : ∀ P : H.Comp a, H.Desc a (b + 1) P Z' → β) :
    ∏ P : ↥(H.ancFin a (b + 1) Z'), F P.1 (mem_ancFin.mp P.2) =
      ∏ Y : ↥(H.parts b Z'), ∏ P : ↥(H.ancFin a b Y.1),
        F P.1 ((desc_succ_iff hab).mpr ⟨Y.1, Y.2, mem_ancFin.mp P.2⟩) := by
  classical
  have hL : ∏ P : ↥(H.ancFin a (b + 1) Z'), F P.1 (mem_ancFin.mp P.2) =
      ∏ P ∈ H.ancFin a (b + 1) Z', if h : H.Desc a (b + 1) P Z' then F P h else 1 := by
    rw [prod_coe_dep (H.ancFin a (b + 1) Z') (fun P h => F P (mem_ancFin.mp h))]
    exact Finset.prod_congr rfl fun P hP => by
      simp [hP, mem_ancFin.mp hP]
  have hR : ∏ Y : ↥(H.parts b Z'), ∏ P : ↥(H.ancFin a b Y.1),
        F P.1 ((desc_succ_iff hab).mpr ⟨Y.1, Y.2, mem_ancFin.mp P.2⟩) =
      ∏ Y ∈ H.parts b Z', ∏ P ∈ H.ancFin a b Y,
        if h : H.Desc a (b + 1) P Z' then F P h else 1 := by
    rw [prod_coe_dep (H.parts b Z') (fun Y hY => ∏ P : ↥(H.ancFin a b Y), F P.1
      ((desc_succ_iff hab).mpr ⟨Y, hY, mem_ancFin.mp P.2⟩))]
    refine Finset.prod_congr rfl fun Y hY => ?_
    rw [dite_eq_left_of_eq_true (eq_true hY), prod_coe_dep (H.ancFin a b Y) (fun P h => F P ((desc_succ_iff hab).mpr
      ⟨Y, hY, mem_ancFin.mp h⟩))]
    refine Finset.prod_congr rfl fun P hP => ?_
    simp [hP, (desc_succ_iff hab).mpr ⟨Y, hY, mem_ancFin.mp hP⟩]
  rw [hL, hR, ancFin_succ hab, Finset.prod_biUnion (fun c _ c' _ hne => ancFin_disjoint hne)]

/-- Splitting off the top layer of a product over a range of scales. -/
theorem prod_Ico_succ_dep {β : Type*} [CommMonoid β] {a b : ℕ} (hab : a ≤ b)
    (F : ∀ j, j ∈ Finset.Ico a (b + 1) → β) :
    ∏ j : ↥(Finset.Ico a (b + 1)), F j.1 j.2 =
      (∏ j : ↥(Finset.Ico a b), F j.1 (by
        have := Finset.mem_Ico.mp j.2
        exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩)) *
      F b (Finset.mem_Ico.mpr ⟨hab, by omega⟩) := by
  classical
  rw [prod_coe_dep (Finset.Ico a (b + 1)) F, Finset.prod_Ico_succ_top hab,
    prod_coe_dep (Finset.Ico a b) (fun j hj => F j (by
        have := Finset.mem_Ico.mp hj
        exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩))]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have h1 : j ∈ Finset.Ico a (b + 1) := by
      have := Finset.mem_Ico.mp hj
      exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩
    simp [hj, h1]
  · simp [hab]

/-- **The restriction of the variables of a descendant to those of its quiet ancestors**
(coordinates): the configuration of the variables of `𝕋_m(Z)` restricted to the variables of
`𝕋_s(P)`, `P` an ancestor of `Z` at a scale `s ≥ k₁`, along a quiet descent. -/
theorem exists_rho (k1 m' : ℕ) (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y) :
    ∃ ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
        SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
        SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A,
      ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
        x ⟨_, locOp_A_incl geo cs SD KD hm hd
          (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩ :=
  ⟨fun _ hs _ hd x p => x ⟨_, locOp_A_incl geo cs SD KD hm hd
    (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩, fun _ _ _ _ _ _ => rfl⟩

/-- `prod_ancFin_succ_dep` for a function on the subtype. -/
theorem prod_ancFin_succ_sub {β : Type*} [CommMonoid β] {a b : ℕ} (hab : a ≤ b)
    (Z' : H.Comp (b + 1)) (f : ↥(H.ancFin a (b + 1) Z') → β) :
    ∏ P : ↥(H.ancFin a (b + 1) Z'), f P =
      ∏ Y : ↥(H.parts b Z'), ∏ P : ↥(H.ancFin a b Y.1),
        f ⟨P.1, mem_ancFin.mpr ((desc_succ_iff hab).mpr ⟨Y.1, Y.2, mem_ancFin.mp P.2⟩)⟩ :=
  prod_ancFin_succ_dep hab Z' (fun P hd => f ⟨P, mem_ancFin.mpr hd⟩)

/-- `prod_Ico_succ_dep` for a function on the subtype. -/
theorem prod_Ico_succ_sub {β : Type*} [CommMonoid β] {a b : ℕ} (hab : a ≤ b)
    (f : ↥(Finset.Ico a (b + 1)) → β) :
    ∏ j : ↥(Finset.Ico a (b + 1)), f j =
      (∏ j : ↥(Finset.Ico a b), f ⟨j.1, by
        have := Finset.mem_Ico.mp j.2
        exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩⟩) *
      f ⟨b, Finset.mem_Ico.mpr ⟨hab, by omega⟩⟩ :=
  prod_Ico_succ_dep hab (fun j hj => f ⟨j, hj⟩)

/-- **The unrolling of the pre-operator along a quiet window** (Lemma III.8.7 (4)): along a quiet
window `[k₁, m'+1)` the weight of the operator of `Z` is the weight of the step kernel of `Z`, times
the weights of the step kernels of all the components `c` of scales `k₁ < j+1 ≤ m'` that are
ancestors of `Z` (with outputs `ψ_{j+1}` read from the variables of their successors `P`), times the
weights of the operators of the components `C` of scale `k₁` (ancestors of `Z`) at outputs `ψ_{k₁}`
read from the variables of their successors, all at the restrictions `ρ` of the variables of `Z`. -/
theorem locOp_absW_unroll (k1 : ℕ) :
    ∀ (m' : ℕ) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
      (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
      (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
        SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
          (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
        SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
      (_ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
        x ⟨_, locOp_A_incl geo cs SD KD hm hd
          (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
      (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
      (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
      (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ),
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.absW o x hv g =
        (SD.ker m' (H.localHistory M K (m' + 1) Z)).absW o
          (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x)
          hv g *
        (∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∏ c : ↥(H.parts (j.1 + 1) P.1),
          (SD.ker j.1 (H.localHistory M K (j.1 + 1) c.1)).absW
            (ancOut c.1 P.1 (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
              (mem_ancFin.mp P.2) x))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv g) *
        ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
          (locOp geo cs SD KD hH lab k1
            ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
            (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
            (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g := by
  intro m' hk1
  induction m', hk1 using Nat.le_induction with
  | base =>
    intro hm Z hq ρ hρ o x hv g
    have hnk := hq (k1 + 1) (by omega) Z (Desc.refl Z)
    rw [locOp_absW_level geo cs SD KD hm hnk o x hv g]
    have : IsEmpty ↥(Finset.Ico k1 k1) := ⟨fun j => by simpa using j.2⟩
    rw [Finset.univ_eq_empty (α := ↥(Finset.Ico k1 k1)), Finset.prod_empty, mul_one,
      Fintype.prod_eq_single (⟨Z, mem_ancFin.mpr (Desc.refl Z)⟩ :
        ↥(H.ancFin (k1 + 1) (k1 + 1) Z))]
    · congr 1
      refine Finset.prod_congr rfl fun C _ => ?_
      have e1 : ρ (k1 + 1) (by omega) Z (Desc.refl Z) x = x :=
        funext fun p => by rw [hρ]; rfl
      have e2 : ρ k1 le_rfl C.1 (desc_of_parts C.2 (Desc.refl Z)) x =
          ancRestrict hm C.2 (locOp_A_anc geo cs SD KD hm hnk C.2) x :=
        funext fun p => by rw [hρ]; rfl
      rw [e1, e2]
    · intro P hP
      exfalso
      apply hP
      exact Subtype.ext (Finset.mem_singleton.mp
        ((Finset.ext_iff.mp (ancFin_self (k1 + 1) Z) P.1).mp P.2))
  | succ m' hk1 ih =>
    intro hm Z hq ρ hρ o x hv g
    have hnk := hq (m' + 1 + 1) (by omega) Z (Desc.refl Z)
    rw [locOp_absW_level geo cs SD KD hm hnk o x hv g]
    have hqY : ∀ Y : ↥(H.parts (m' + 1) Z), ∀ s, k1 < s → ∀ Y' : H.Comp s,
        H.Desc s (m' + 1) Y' Y.1 → ¬ IsKept H s Y' := fun Y s hs Y' h' =>
      hq s hs Y' (Desc.trans h' (Desc.single ((H.mem_parts _ _ _).mp Y.2).1
        ((H.mem_parts _ _ _).mp Y.2).2))
    choose ρY hρY using fun Y : ↥(H.parts (m' + 1) Z) =>
      exists_rho geo cs SD KD k1 m' (by omega) Y.1 (hqY Y)
    have hY := fun Y : ↥(H.parts (m' + 1) Z) =>
      ih (by omega) Y.1 (hqY Y) (ρY Y) (hρY Y) (ancOut Y.1 Z x)
        (ancRestrict hm Y.2 (locOp_A_anc geo cs SD KD hm hnk Y.2) x) hv g
    rw [Finset.prod_congr rfl fun Y _ => hY Y, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    rw [prod_Ico_succ_sub (a := k1) (b := m') hk1]
    have hcompat : ∀ (Y : ↥(H.parts (m' + 1) Z)) (s : ℕ) (hs : k1 ≤ s) (P : H.Comp s)
        (hdY : H.Desc s (m' + 1) P Y.1) (hd : H.Desc s (m' + 1 + 1) P Z),
        ρ s hs P hd x = ρY Y s hs P hdY
          (ancRestrict hm Y.2 (locOp_A_anc geo cs SD KD hm hnk Y.2) x) :=
      fun Y s hs P hdY hd => funext fun p => by rw [hρ, hρY]; rfl
    have key : ∀ a1 a2 a3 b1 b2 b3 : ENNReal, a1 = b2 → a2 = b1 → a3 = b3 →
        a1 * a2 * a3 = b1 * b2 * b3 := by
      intro a1 a2 a3 b1 b2 b3 h1 h2 h3
      subst h1 h2 h3
      ring
    refine Eq.trans (congrArg _ (key _ _ _ _ _ _ ?_ ?_ ?_)) (mul_assoc _ _ _).symm
    · rw [Fintype.prod_eq_single (⟨Z, mem_ancFin.mpr (Desc.refl Z)⟩ :
        ↥(H.ancFin (m' + 1 + 1) (m' + 1 + 1) Z))]
      · refine Finset.prod_congr rfl fun Y _ => ?_
        have e1 : ρ (m' + 1 + 1) (by omega) Z (Desc.refl Z) x = x :=
          funext fun p => by rw [hρ]; rfl
        have e2 : ρ (m' + 1) (by omega) Y.1 (desc_of_parts Y.2 (Desc.refl Z)) x =
            ancRestrict hm Y.2 (locOp_A_anc geo cs SD KD hm hnk Y.2) x :=
          funext fun p => by rw [hρ]; rfl
        dsimp only
        rw [e1, e2]
      · intro P hP
        exfalso
        apply hP
        exact Subtype.ext (Finset.mem_singleton.mp
          ((Finset.ext_iff.mp (ancFin_self (m' + 1 + 1) Z) P.1).mp P.2))
    · rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [prod_ancFin_succ_sub (a := j.1 + 1 + 1) (b := m' + 1)
        (by have := Finset.mem_Ico.mp j.2; omega) Z]
      refine Finset.prod_congr rfl fun Y _ => Finset.prod_congr rfl fun P _ =>
        Finset.prod_congr rfl fun c _ => ?_
      rw [hcompat Y _ _ P.1 (mem_ancFin.mp P.2) _,
        hcompat Y _ _ c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) _]
    · rw [prod_ancFin_succ_sub (a := k1 + 1) (b := m' + 1) (by omega) Z]
      refine Finset.prod_congr rfl fun Y _ => Finset.prod_congr rfl fun P _ =>
        Finset.prod_congr rfl fun c _ => ?_
      rw [hcompat Y _ _ P.1 (mem_ancFin.mp P.2) _,
        hcompat Y _ _ c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) _]

/-- The restrictions `ρ` are measurable. -/
theorem measurable_rho {k1 m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (s : ℕ) (hs : k1 ≤ s) (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z) :
    Measurable (ρ s hs P hd) :=
  Measurable.of_eval fun p => by
    have : (fun x => ρ s hs P hd x p) = fun x => x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩ :=
      funext fun x => hρ s hs P hd x p
    rw [this]
    exact measurable_pi_apply _

end A

end Incl

end Balaban.LargeField
