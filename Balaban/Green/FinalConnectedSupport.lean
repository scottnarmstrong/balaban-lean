/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLocalityAE
public import Balaban.Green.FinalTagSupport
public import Balaban.Localization.DecEquivCoef
public import Balaban.Green.FinalTaggedSqrt
import Mathlib.Tactic.Linarith

/-!
# Connected supports of the tagged last-integral family (W753, FINALPHYS leaf L6)

This construction is proposed in FINALFAM; the papers print no formula (Roland question 18
pending).  `isConnectedFamily_macBox` in `FinalLocalityAE.lean` declares every family connected
for the patches `macBox i ×ˢ macBox i`, so the abstract vanishing there is empty.  Here the
vanishing is proved for the geometry of the cover: two cells are adjacent when their boxes meet.

* `macTags_closed`, `macTags_subset_or`: if `y ∈ B_z`, the tags `macTags z x y` are connected in
  the adjacency "boxes meet" (path points are chained by steps of length one, `path_chain`); so
  tags lying in `A ∪ B` with the boxes of `A` disjoint from those of `B` lie in `A` or in `B`.
* `taggedGfin_split_of_separated`: at a parameter supported on `C = A ⊔ B`, with the boxes of `A`
  disjoint from those of `B`, and `1 - K` invertible, `G_fin(s) = G_fin(s|_A) + G_fin(s|_B)`.
  The entries `χ_z G_z` and `R_z` have their column in `B_z`, and the tags contain the cells of the
  two end points, so the cross products `K_A K_B`, `G_A K_B`, ... vanish.
* `coef_eq_zero_of_split`: a function analytic on the polydisc of radius `R > 1` that is, on the
  parameters supported on `C = A ⊔ B`, the sum of its values at the two restrictions has zero
  coefficient at `C`.
* `coef_taggedGfin_final_eq_zero_of_separated`, `coef_taggedGfin_final_eq_zero_of_not_connected`,
  `coef_taggedCfin_final_eq_zero_of_separated`: the coefficient of the tagged final family
  `G_fin(·, t)` and of its Stieltjes integral `taggedCfin` at a set `C` of cells vanishes when `C`
  is not connected (`C = A ⊔ B`, both nonempty, `macRegion A` disjoint from `macRegion B`).
-/

@[expose] public section

open Finset Matrix Relation

namespace Balaban.Green

section Geometry

variable {d m M : ℕ} [NeZero m]

lemma dist_le_one_of_single (p q : L1Torus d m) (k : Fin d) (e : ℤ) (he : e.natAbs ≤ 1)
    (hk : p k = q k + (e : ZMod m)) (hi : ∀ i, i ≠ k → p i = q i) : dist p q ≤ 1 := by
  rw [dist_L1Torus]
  unfold torusDist
  rw [Finset.sum_eq_single k]
  · have := natAbs_cycRep_le_of_cast (p k - q k) e (by rw [hk]; ring)
    exact_mod_cast this.trans he
  · intro i _ hik
    rw [hi i hik, sub_self, natAbs_cycRep_zero]
    simp
  · simp

/-- Stepping along a chain of points of the path. -/
lemma path_chain_of_steps {x y : L1Torus d m} (Pf : ℤ → L1Torus d m) (lo hi : ℤ)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hmem : ∀ e, lo ≤ e → e ≤ hi → Pf e ∈ macPath d m x y)
    (hstep : ∀ e, dist (Pf e) (Pf (e + 1)) ≤ 1) :
    ∀ e, lo ≤ e → e ≤ hi → ReflTransGen
      (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1)
      (Pf 0) (Pf e) := by
  intro e he1 he2
  rcases le_total 0 e with h0 | h0
  · induction e, h0 using Int.leInduction with
    | base => exact ReflTransGen.refl
    | succ n hn ih =>
      refine (ih (by omega) (by omega)).tail ⟨hmem n (by omega) (by omega),
        hmem (n + 1) (by omega) he2, hstep n⟩
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, e = -(n : ℤ) := ⟨e.natAbs, by omega⟩
    have key : ∀ n : ℕ, lo ≤ -(n : ℤ) → ReflTransGen
        (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1)
        (Pf 0) (Pf (-(n : ℤ))) := by
      intro n
      induction n with
      | zero => intro _; simpa using ReflTransGen.refl
      | succ n ih =>
        intro hn
        have h1 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
        refine (ih (by push_cast at hn; omega)).tail ⟨hmem _ (by omega) (by omega),
          hmem _ hn (by push_cast; omega), ?_⟩
        have := hstep (-((n + 1 : ℕ) : ℤ))
        rw [h1, dist_comm] at this
        exact this
    exact key n he1

/-- Every point of the path from `x` to `y` is reached from `x` by steps of length at most one
inside the path. -/
lemma path_chain (x y : L1Torus d m) {p : L1Torus d m} (hp : p ∈ macPath d m x y) :
    ReflTransGen
      (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1)
      x p := by
  -- the point of segment `j` at arc parameter `e`
  have hseg : ∀ (j : ℕ) (hj : j < d), ∀ e : ℤ, min 0 (cycRep (y ⟨j, hj⟩ - x ⟨j, hj⟩)) ≤ e →
      e ≤ max 0 (cycRep (y ⟨j, hj⟩ - x ⟨j, hj⟩)) →
      ReflTransGen
        (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1)
        (fun i : Fin d => if i.val < j then y i else if i.val = j then x i + ((0 : ℤ) : ZMod m)
          else x i)
        (fun i : Fin d => if i.val < j then y i else if i.val = j then x i + (e : ZMod m)
          else x i) := by
    intro j hj
    refine path_chain_of_steps (x := x) (y := y)
      (fun e : ℤ => fun i : Fin d => if i.val < j then y i else if i.val = j then
        x i + (e : ZMod m) else x i) _ _ (min_le_left _ _) (le_max_left _ _) ?_ ?_
    · intro e h1 h2
      refine ⟨⟨j, hj⟩, fun i hi => ?_, fun i hi => ?_, ?_⟩
      · have : i.val < j := hi
        simp [this]
      · have h3 : j < i.val := hi
        simp [not_lt.2 h3.le, h3.ne']
      · simp only [lt_self_iff_false, ite_false, ite_true]
        exact Finset.mem_image.2 ⟨e, Finset.mem_Icc.2 ⟨h1, h2⟩, rfl⟩
    · intro e
      refine dist_le_one_of_single _ _ ⟨j, hj⟩ (-1) (by simp) ?_ ?_
      · simp only [lt_self_iff_false, ite_false, ite_true]
        push_cast; ring
      · intro i hi
        have : i.val ≠ j := fun h => hi (Fin.ext h)
        simp [this]
  have hreach : ∀ (j : ℕ) (hj : j < d), ReflTransGen
      (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1) x
      (fun i : Fin d => if i.val < j then y i else if i.val = j then x i + ((0 : ℤ) : ZMod m)
        else x i) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have : (fun i : Fin d => if i.val < 0 then y i else if i.val = 0 then
          x i + ((0 : ℤ) : ZMod m) else x i) = x := by
        funext i; split_ifs <;> simp_all
      rw [this]
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hseg j (by omega) (cycRep (y ⟨j, by omega⟩ - x ⟨j, by omega⟩))
        (min_le_right _ _) (le_max_right _ _)
      have h3 : (fun i : Fin d => if i.val < j then y i else if i.val = j then
          x i + ((cycRep (y ⟨j, by omega⟩ - x ⟨j, by omega⟩) : ℤ) : ZMod m) else x i) =
          (fun i : Fin d => if i.val < j + 1 then y i else if i.val = j + 1 then
          x i + ((0 : ℤ) : ZMod m) else x i) := by
        funext i
        by_cases a1 : i.val < j
        · simp [a1, show i.val < j + 1 by omega]
        · by_cases a2 : i.val = j
          · have hij : i = ⟨j, by omega⟩ := Fin.ext a2
            have hc : x i + ((cycRep (y ⟨j, by omega⟩ - x ⟨j, by omega⟩) : ℤ) : ZMod m) = y i := by
              rw [cast_cycRep, ← hij]; ring
            simp [a2, hc]
          · have a3 : ¬ i.val < j + 1 := by omega
            simp [a1, a2, a3]
      rw [h3] at h2
      exact h1.trans h2
  obtain ⟨k, hk1, hk2, hk3⟩ := hp
  obtain ⟨e, he, hpk⟩ := Finset.mem_image.1 hk3
  have he' := Finset.mem_Icc.1 he
  have hp_eq : p = (fun i : Fin d => if i.val < k.val then y i else if i.val = k.val then
      x i + (e : ZMod m) else x i) := by
    funext i
    by_cases a1 : i < k
    · simp [Fin.lt_def.1 a1, hk1 i a1]
    · by_cases a2 : i = k
      · subst a2; simp [← hpk]
      · have a3 : k < i := lt_of_le_of_ne (not_lt.1 a1) (Ne.symm a2)
        have a4 : ¬ i.val < k.val := fun h => a1 (Fin.lt_def.2 h)
        have a5 : i.val ≠ k.val := fun h => a2 (Fin.ext h)
        simp [a4, a5, hk2 i a3]
  rw [hp_eq]
  exact (hreach k.val k.2).trans (hseg k.val k.2 e he'.1 he'.2)

lemma macBox_self (hM : 0 < M) (p : L1Torus d m) : p ∈ macBox d m M (macZ M p) :=
  mem_macBox_of_mem_macCore hM (mem_macCore_macZ p)

lemma macBox_macZ_of_dist_le (hM : 0 < M) {p q : L1Torus d m} (h : dist p q ≤ 1) :
    p ∈ macBox d m M (macZ M q) := by
  show Metric.infDist p (macCore d m M (macZ M q)) < 2 * M
  have h1 := Metric.infDist_le_dist_of_mem (x := p) (mem_macCore_macZ (M := M) q)
  have h2 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith

lemma macZ_end_mem_macTags (hM : 0 < M) (hd : 0 < d) (z : MacIdx d m M) (x y : L1Torus d m) :
    macZ M y ∈ macTags d m M z x y := by
  simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨y, macPath_end hd x y, macBox_self hM y⟩

lemma macZ_start_mem_macTags (hM : 0 < M) (hd : 0 < d) (z : MacIdx d m M) (x y : L1Torus d m) :
    macZ M x ∈ macTags d m M z x y := by
  simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨x, macPath_start hd x y, macBox_self hM x⟩

/-- The tags `macTags z x y` form a connected set of cells when `y ∈ B_z`: a set `Q` of cells
that contains the cell of `y` and is closed under adjacency (boxes meeting) inside the tags,
contains all the tags. -/
theorem macTags_closed (hM : 0 < M) (hd : 0 < d) {z : MacIdx d m M} {x y : L1Torus d m}
    (hy : y ∈ macBox d m M z) (Q : Set (MacIdx d m M))
    (hQ : ∀ w ∈ macTags d m M z x y, ∀ w' ∈ macTags d m M z x y, ∀ p, p ∈ macBox d m M w →
      p ∈ macBox d m M w' → w ∈ Q → w' ∈ Q)
    (hc : macZ M y ∈ Q) : ∀ w ∈ macTags d m M z x y, w ∈ Q := by
  have hsym : Std.Symm
      (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1) :=
    ⟨fun p q h => ⟨h.2.1, h.1, by rw [dist_comm]; exact h.2.2⟩⟩
  have hpathT : ∀ p ∈ macPath d m x y, macZ M p ∈ macTags d m M z x y := fun p hp => by
    simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨p, hp, macBox_self hM p⟩
  have hpath_Q : ∀ p ∈ macPath d m x y, macZ M p ∈ Q := by
    intro p hp
    have R : ReflTransGen
        (fun p q : L1Torus d m => p ∈ macPath d m x y ∧ q ∈ macPath d m x y ∧ dist p q ≤ 1)
        y p :=
      (Std.Symm.symm _ _ (path_chain x y (macPath_end hd x y))).trans
        (path_chain x y hp)
    clear hp
    induction R with
    | refl => exact hc
    | tail _ hbc ih =>
      exact hQ _ (hpathT _ hbc.1) _ (hpathT _ hbc.2.1) _ (macBox_self hM _)
        (macBox_macZ_of_dist_le hM hbc.2.2) ih
  intro w hw
  simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rcases hw with ⟨p, hpw, hpz⟩ | ⟨p, hp, hpw⟩
  · have hzT : z ∈ macTags d m M z x y := by
      simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨y, hy, hy⟩
    have hzQ : z ∈ Q :=
      hQ _ (macZ_end_mem_macTags hM hd z x y) _ hzT y (macBox_self hM y) hy hc
    refine hQ _ hzT w ?_ p hpz hpw hzQ
    simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl ⟨p, hpw, hpz⟩
  · refine hQ _ (hpathT p hp) w ?_ p (macBox_self hM p) hpw (hpath_Q p hp)
    simp only [macTags, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨p, hp, hpw⟩

/-- If the tags lie in `A ∪ B` with the boxes of `A` disjoint from the boxes of `B`, and
`y ∈ B_z`, they lie in `A` or in `B`. -/
theorem macTags_subset_or (hM : 0 < M) (hd : 0 < d) {z : MacIdx d m M} {x y : L1Torus d m}
    (hy : y ∈ macBox d m M z) {A B : Finset (MacIdx d m M)}
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ∀ p, p ∈ macBox d m M a → p ∈ macBox d m M b → False)
    (hT : macTags d m M z x y ⊆ A ∪ B) :
    macTags d m M z x y ⊆ A ∨ macTags d m M z x y ⊆ B := by
  have hc := hT (macZ_end_mem_macTags hM hd z x y)
  rcases Finset.mem_union.1 hc with hA | hB
  · left
    intro w hw
    have := macTags_closed hM hd hy (↑A : Set (MacIdx d m M))
      (fun w hw w' hw' p h1 h2 hwA => by
        rcases Finset.mem_union.1 (hT hw') with h | h
        · exact h
        · exact (hsep w hwA w' h p h1 h2).elim)
      hA w hw
    exact this
  · right
    intro w hw
    have := macTags_closed hM hd hy (↑B : Set (MacIdx d m M))
      (fun w hw w' hw' p h1 h2 hwB => by
        rcases Finset.mem_union.1 (hT hw') with h | h
        · exact (hsep w' h w hwB p h2 h1).elim
        · exact h)
      hB w hw
    exact this

end Geometry

section Algebra

open Balaban.Localization

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Z Pc : Type*} [Fintype Pc] [DecidableEq Pc]

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
/-- A tag monomial splits over a decomposition `C = A ⊔ B` of the support. -/
theorem tagMon_split {A B C V : Finset Pc} {s sA sB : Pc → ℂ} (hAB : Disjoint A B)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hs : s ∈ supportedOn C)
    (hsA : ∀ p, sA p = if p ∈ A then s p else 0) (hsB : ∀ p, sB p = if p ∈ B then s p else 0)
    (hne : V.Nonempty) (hV : V ⊆ A ∨ V ⊆ B ∨ ¬ V ⊆ C) :
    tagMon V s = tagMon V sA + tagMon V sB := by
  obtain ⟨q, hq⟩ := hne
  rcases hV with h | h | h
  · have h1 : tagMon V s = tagMon V sA := Finset.prod_congr rfl fun p hp => by
      simp [hsA p, h hp]
    have h2 : tagMon V sB = 0 := Finset.prod_eq_zero hq (by
      simp [hsB q, show q ∉ B from fun hqB => Finset.disjoint_left.1 hAB (h hq) hqB])
    rw [h1, h2, add_zero]
  · have h1 : tagMon V s = tagMon V sB := Finset.prod_congr rfl fun p hp => by
      simp [hsB p, h hp]
    have h2 : tagMon V sA = 0 := Finset.prod_eq_zero hq (by
      simp [hsA q, show q ∉ A from fun hqA => Finset.disjoint_left.1 hAB hqA (h hq)])
    rw [h1, h2, zero_add]
  · obtain ⟨p, hpV, hpC⟩ := Finset.not_subset.1 h
    have e0 : tagMon V s = 0 := tagMon_zero_of_not_subset hs h
    have e1 : tagMon V sA = 0 := Finset.prod_eq_zero hpV (by
      simp [hsA p, show p ∉ A from fun hpA => hpC (hAC hpA)])
    have e2 : tagMon V sB = 0 := Finset.prod_eq_zero hpV (by
      simp [hsB p, show p ∉ B from fun hpB => hpC (hBC hpB)])
    rw [e0, e1, e2, add_zero]

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
/-- The tagged matrix splits over a decomposition of the support, provided each nonzero entry
carries a nonempty tag set that lies in `A`, in `B`, or not in `C`. -/
theorem taggedMat_split (S : Finset Z) (V : Z → ι → ι → Finset Pc) (a : Z → Matrix ι ι ℂ)
    {A B C : Finset Pc} {s sA sB : Pc → ℂ} (hAB : Disjoint A B)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (hs : s ∈ supportedOn C)
    (hsA : ∀ p, sA p = if p ∈ A then s p else 0) (hsB : ∀ p, sB p = if p ∈ B then s p else 0)
    (h : ∀ z ∈ S, ∀ x y, a z x y ≠ 0 →
      (V z x y).Nonempty ∧ (V z x y ⊆ A ∨ V z x y ⊆ B ∨ ¬ V z x y ⊆ C)) :
    taggedMat S V a s = taggedMat S V a sA + taggedMat S V a sB := by
  classical
  ext x y
  simp only [taggedMat, Matrix.of_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  by_cases ha : a z x y = 0
  · simp [ha]
  · obtain ⟨h1, h2⟩ := h z hz x y ha
    rw [tagMon_split hAB hAC hBC hs hsA hsB h1 h2, add_mul]

omit [Fintype ι] [DecidableEq ι] [Fintype Pc] in
/-- A nonzero entry of the tagged matrix at a parameter supported on `A` has its tag set in `A`. -/
theorem taggedMat_ne_zero_supp (S : Finset Z) (V : Z → ι → ι → Finset Pc) (a : Z → Matrix ι ι ℂ)
    {A : Finset Pc} {s sA : Pc → ℂ} (hsA : ∀ p, sA p = if p ∈ A then s p else 0) {x y : ι}
    (h : taggedMat S V a sA x y ≠ 0) :
    ∃ z ∈ S, a z x y ≠ 0 ∧ ∀ p ∈ V z x y, p ∈ A := by
  classical
  simp only [taggedMat, Matrix.of_apply] at h
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨z, hz, right_ne_zero_of_mul hne, fun p hp => ?_⟩
  by_contra hpA
  apply left_ne_zero_of_mul hne
  exact Finset.prod_eq_zero hp (by simp [hsA p, hpA])

omit [Fintype Pc] [DecidableEq ι] in
/-- Two tagged matrices at parameters supported on disjoint sets multiply to zero, when each
nonzero entry carries the end (start) cell `e y` (`e x`) among its tags. -/
theorem taggedMat_mul_eq_zero (S : Finset Z) (V : Z → ι → ι → Finset Pc)
    (a b : Z → Matrix ι ι ℂ) {A B : Finset Pc} {s sA sB : Pc → ℂ} (hAB : Disjoint A B)
    (hsA : ∀ p, sA p = if p ∈ A then s p else 0) (hsB : ∀ p, sB p = if p ∈ B then s p else 0)
    (e : ι → Pc) (ha : ∀ z ∈ S, ∀ x y, a z x y ≠ 0 → e y ∈ V z x y)
    (hb : ∀ z ∈ S, ∀ x y, b z x y ≠ 0 → e x ∈ V z x y) :
    taggedMat S V a sA * taggedMat S V b sB = 0 := by
  ext x w
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_contra hne
  obtain ⟨z, hz, hz1, hz2⟩ := taggedMat_ne_zero_supp S V a hsA (left_ne_zero_of_mul hne)
  obtain ⟨z', hz', hz1', hz2'⟩ := taggedMat_ne_zero_supp S V b hsB (right_ne_zero_of_mul hne)
  exact Finset.disjoint_left.1 hAB (hz2 _ (ha z hz x y hz1)) (hz2' _ (hb z' hz' y w hz1'))

/-- Algebra of the inverse for two commuting-null pieces. -/
theorem inv_split {GA GB KA KB : Matrix ι ι ℂ} (h1 : KA * KB = 0) (h2 : KB * KA = 0)
    (h3 : GA * KB = 0) (h4 : GB * KA = 0) (hu : IsUnit (1 - (KA + KB))) :
    (GA + GB) * (1 - (KA + KB))⁻¹ = GA * (1 - KA)⁻¹ + GB * (1 - KB)⁻¹ := by
  have e1 : 1 - (KA + KB) = (1 - KA) * (1 - KB) := by
    calc 1 - (KA + KB) = (1 - KA) * (1 - KB) - KA * KB := by noncomm_ring
      _ = _ := by rw [h1, sub_zero]
  have e2 : 1 - (KA + KB) = (1 - KB) * (1 - KA) := by
    calc 1 - (KA + KB) = (1 - KB) * (1 - KA) - KB * KA := by noncomm_ring
      _ = _ := by rw [h2, sub_zero]
  have hdet : IsUnit ((1 - KA).det * (1 - KB).det) := by
    rw [← Matrix.det_mul, ← e1]; exact (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hA : IsUnit (1 - KA) := (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mul_iff.1 hdet).1
  have hB : IsUnit (1 - KB) := (Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mul_iff.1 hdet).2
  have iA : (1 - KA) * (1 - KA)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hA)
  have iB : (1 - KB) * (1 - KB)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hB)
  have gA : GA * (1 - KB)⁻¹ = GA := by
    have : GA * (1 - KB) = GA := by rw [mul_sub, mul_one, h3, sub_zero]
    calc GA * (1 - KB)⁻¹ = (GA * (1 - KB)) * (1 - KB)⁻¹ := by rw [this]
      _ = GA := by rw [mul_assoc, iB, mul_one]
  have gB : GB * (1 - KA)⁻¹ = GB := by
    have : GB * (1 - KA) = GB := by rw [mul_sub, mul_one, h4, sub_zero]
    calc GB * (1 - KA)⁻¹ = (GB * (1 - KA)) * (1 - KA)⁻¹ := by rw [this]
      _ = GB := by rw [mul_assoc, iA, mul_one]
  rw [add_mul]
  congr 1
  · rw [e1, Matrix.mul_inv_rev, ← mul_assoc, gA]
  · rw [e2, Matrix.mul_inv_rev, ← mul_assoc, gB]

end Algebra

section Splitting

open Balaban.Localization Balaban.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pder_add_open {R : ℝ} {g h : (ι → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hh : AnalyticOnNhd ℂ h (polydisc (0 : ι → ℂ) (fun _ => R))) (a : ι) :
    ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => R),
      pder a (fun s => g s + h s) w = pder a g w + pder a h w := by
  intro w hw
  have hg' := (hg w hw).differentiableAt
  have hh' := (hh w hw).differentiableAt
  have hgh : DifferentiableAt ℂ (fun s => g s + h s) w := hg'.add hh'
  rw [pder_eq_fderiv a hgh, pder_eq_fderiv a hg', pder_eq_fderiv a hh']
  have : fderiv ℂ (fun s => g s + h s) w = fderiv ℂ g w + fderiv ℂ h w := fderiv_add hg' hh'
  rw [this]; rfl

theorem pderList_add_open {R : ℝ} (l : List ι) : ∀ {g h : (ι → ℂ) → ℂ},
    AnalyticOnNhd ℂ g (polydisc (0 : ι → ℂ) (fun _ => R)) →
    AnalyticOnNhd ℂ h (polydisc (0 : ι → ℂ) (fun _ => R)) →
    ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => R),
      pderList l (fun s => g s + h s) w = pderList l g w + pderList l h w := by
  induction l with
  | nil => intro g h _ _ w _; rfl
  | cons a l ih =>
    intro g h hg hh w hw
    simp only [pderList_cons]
    have e := pderList_congr_open (isOpen_polydisc (0 : ι → ℂ) (fun _ : ι => R)) l
      (f := pder a (fun s => g s + h s)) (g := fun s => pder a g s + pder a h s)
      (pder_add_open hg hh a) w hw
    rw [e]
    exact ih (analyticOnNhd_pder hg a) (analyticOnNhd_pder hh a) w hw

/-- The coordinate projection onto the coordinates in `X`, as a continuous linear map. -/
theorem analyticOnNhd_comp_proj {R : ℝ} {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) (X : Finset ι) (hR : 0 < R) :
    AnalyticOnNhd ℂ (fun s : ι → ℂ => f (fun i => if i ∈ X then s i else 0))
      (polydisc (0 : ι → ℂ) (fun _ => R)) := by
  classical
  let T : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi fun i => if i ∈ X then ContinuousLinearMap.proj i else 0
  have hT : ∀ s, T s = fun i => if i ∈ X then s i else 0 := fun s => by
    funext i; by_cases hi : i ∈ X <;> simp [T, hi]
  have := hf.comp (g := f) (f := T) (s := polydisc (0 : ι → ℂ) (fun _ => R))
    (fun s _ => T.analyticAt s) (fun s hs i => by
      rw [hT]; by_cases hi : i ∈ X
      · simpa [hi] using hs i
      · simpa [hi] using hR)
  simpa [Function.comp_def, hT] using this

/-- **Separability kills the mixed coefficient.**  If `f` is analytic on the polydisc of radius
`R > 1` and on parameters supported on `C = A ⊔ B` it is the sum of its values at the restrictions
to `A` and to `B`, then the coefficient of `f` at `C` vanishes (`A` and `B` nonempty). -/
theorem coef_eq_zero_of_split {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) {A B C : Finset ι}
    (hAB : Disjoint A B) (hAC : A ⊆ C) (hBC : B ⊆ C) (hA : A.Nonempty) (hB : B.Nonempty)
    (hsplit : ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), s ∈ supportedOn C →
      f s = f (fun i => if i ∈ A then s i else 0) + f (fun i => if i ∈ B then s i else 0)) :
    coef f C = 0 := by
  classical
  have hR0 : 0 < R := by linarith
  set P := polydisc (0 : ι → ℂ) (fun _ => R) with hP
  have hproj : ∀ (X : Finset ι) (s : ι → ℂ), s ∈ P → (fun i => if i ∈ X then s i else 0) ∈ P := by
    intro X s hs i
    by_cases hi : i ∈ X
    · simpa [hi] using hs i
    · simpa [hi] using hR0
  have hgA := analyticOnNhd_comp_proj hf A hR0
  have hgB := analyticOnNhd_comp_proj hf B hR0
  have hgC := analyticOnNhd_comp_proj hf C hR0
  -- replace `f` by its restriction to the support
  have h1 : coef f C = coef (fun s => f (fun i => if i ∈ C then s i else 0)) C :=
    coef_congr fun w hw => by
      congr 1; funext i; by_cases hi : i ∈ C
      · simp [hi]
      · simp [hi, hw i hi]
  have h2 : coef (fun s => f (fun i => if i ∈ C then s i else 0)) C =
      coef (fun s => f (fun i => if i ∈ A then s i else 0) +
        f (fun i => if i ∈ B then s i else 0)) C := by
    refine coef_congr_polydisc (ι := ι) hR (C := C) fun s hs => ?_
    have hsC : (fun i => if i ∈ C then s i else 0) ∈ supportedOn C := fun i hi => by simp [hi]
    rw [hsplit _ (hproj C s hs) hsC]
    congr 2
    · funext i; by_cases hi : i ∈ A
      · simp [hi, hAC hi]
      · simp [hi]
    · funext i; by_cases hi : i ∈ B
      · simp [hi, hBC hi]
      · simp [hi]
  rw [h1, h2]
  unfold coef
  set l := Finset.univ.toList.filter (· ∈ C) with hl
  have hlC : ∀ a ∈ l, a ∈ C := fun a ha => mem_filter_toList.mp ha
  obtain ⟨i₀, hi₀⟩ := hA
  obtain ⟨j₀, hj₀⟩ := hB
  have hj₀l : j₀ ∈ l := mem_filter_toList.mpr (hBC hj₀)
  have hi₀l : i₀ ∈ l := mem_filter_toList.mpr (hAC hi₀)
  have h0 : (0 : ι → ℂ) ∈ supportedOn C := fun i _ => rfl
  have hz : iterInt l (pderList l fun s => f (fun i => if i ∈ A then s i else 0) +
        f (fun i => if i ∈ B then s i else 0)) 0 =
      iterInt l (fun w => pderList l (fun s => f (fun i => if i ∈ A then s i else 0)) w +
        pderList l (fun s => f (fun i => if i ∈ B then s i else 0)) w) 0 :=
    iterInt_congr (fun w hw => pderList_add_open l hgA hgB w (unitCube_subset_polydisc hR hw))
      l (fun j _ => by simp)
  rw [hz]
  have hzero : iterInt l (fun w => pderList l (fun s => f (fun i => if i ∈ A then s i else 0)) w +
        pderList l (fun s => f (fun i => if i ∈ B then s i else 0)) w) 0 =
      iterInt l (fun _ => (0 : ℂ)) 0 := by
    refine iterInt_congr_supportedOn (C := C) (fun w hw => ?_) l hlC h0
    have a1 : pderList l (fun s => f (fun i => if i ∈ A then s i else 0)) w = 0 :=
      pderList_eq_zero_of_inv (C := C) (i₀ := j₀) l hlC hj₀l (fun w' _ τ => by
        congr 1; funext i
        by_cases hi : i ∈ A
        · have : i ≠ j₀ := fun h => Finset.disjoint_left.1 hAB hi (h ▸ hj₀)
          simp [hi, Pi.single_eq_of_ne this]
        · simp [hi]) w hw
    have a2 : pderList l (fun s => f (fun i => if i ∈ B then s i else 0)) w = 0 :=
      pderList_eq_zero_of_inv (C := C) (i₀ := i₀) l hlC hi₀l (fun w' _ τ => by
        congr 1; funext i
        by_cases hi : i ∈ B
        · have : i ≠ i₀ := fun h => Finset.disjoint_left.1 hAB (h ▸ hi₀) hi
          simp [hi, Pi.single_eq_of_ne this]
        · simp [hi]) w hw
    rw [a1, a2, add_zero]
  rw [hzero]
  exact iterInt_zero _ _

end Splitting

section Entries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The box resolvent has zero columns outside the box. -/
theorem boxG_apply_of_not_mem {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} {w y : ι}
    (hy : y ∉ B) : boxG U B t w y = 0 := by
  simp [boxG, boxP, Matrix.mul_diagonal, hy]

/-- A nonzero entry of `χ_z G_z` has its column in the box. -/
theorem mem_of_diag_mul_boxG_ne_zero {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} {c : ι → ℂ}
    {x y : ι} (h : (Matrix.diagonal c * boxG U B t) x y ≠ 0) : y ∈ B := by
  by_contra hy
  apply h
  rw [Matrix.diagonal_mul, boxG_apply_of_not_mem hy, mul_zero]

/-- A nonzero entry of the defect `R_z` has its column in the box. -/
theorem mem_of_boxR_ne_zero {U : Matrix ι ι ℂ} {B : Finset ι} {t : ℝ} {c : ι → ℂ}
    (hc : ∀ w, c w ≠ 0 → w ∈ B) {x y : ι} (h : boxR U B c t x y ≠ 0) : y ∈ B := by
  by_contra hy
  apply h
  have h1 : Matrix.diagonal c x y = 0 := by
    rw [Matrix.diagonal_apply]
    split_ifs with hxy
    · by_contra hcx
      exact hy (hxy ▸ hc x hcx)
    · rfl
  have h2 : (shiftMat U t * Matrix.diagonal c * boxG U B t) x y = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun w _ => by rw [boxG_apply_of_not_mem hy, mul_zero]
  simp only [boxR, Matrix.sub_apply, h1, h2, sub_zero]

end Entries

section Main

open Balaban.Localization Balaban.Analysis

variable {d N₀ M : ℕ} [NeZero N₀]

/-- **The tagged family splits over a separated decomposition of the support.**  Let
`C = A ⊔ (C \ A)` with the boxes of `A` disjoint from the boxes of `C \ A`, and `s` supported on
`C` with `1 - K(s, t)` invertible.  Then `G_fin(s, t) = G_fin(s|_A, t) + G_fin(s|_{C \ A}, t)`. -/
theorem taggedGfin_split_of_separated (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {C A : Finset (MacIdx d N₀ M)}
    (hAC : A ⊆ C) (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)))
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ supportedOn C)
    (hu : IsUnit (1 - taggedK Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s)) :
    taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) U t s =
      taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) U t (fun i => if i ∈ A then s i else 0) +
      taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) U t (fun i => if i ∈ C \ A then s i else 0) := by
  classical
  set c : MacIdx d N₀ M → L1Torus d N₀ → ℂ := fun z u => ((macChi d N₀ M z u : ℝ) : ℂ) with hc
  set B : Finset (MacIdx d N₀ M) := C \ A with hBdef
  have hAB : Disjoint A B := Finset.disjoint_sdiff
  have hBC : B ⊆ C := Finset.sdiff_subset
  have hBA : Disjoint B A := hAB.symm
  have hsep' : ∀ a ∈ A, ∀ b ∈ B, ∀ p, p ∈ macBox d N₀ M a → p ∈ macBox d N₀ M b → False :=
    fun a ha b hb p h1 h2 => Set.disjoint_left.1 hsep (mem_macRegion.2 ⟨a, ha, h1⟩)
      (mem_macRegion.2 ⟨b, hb, h2⟩)
  have hCAB : C ⊆ A ∪ B := by
    intro i hi
    by_cases hiA : i ∈ A
    · exact Finset.mem_union_left _ hiA
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hi, hiA⟩)
  have hcB : ∀ z w, c z w ≠ 0 → w ∈ macBoxF d N₀ M z := fun z w h =>
    macChi_ne_zero_mem_macBoxF hM h
  have hGy : ∀ z x y, (Matrix.diagonal (c z) * boxG U (macBoxF d N₀ M z) t) x y ≠ 0 →
      y ∈ macBox d N₀ M z := fun z x y h => mem_macBoxF.1 (mem_of_diag_mul_boxG_ne_zero h)
  have hKy : ∀ z x y, boxR U (macBoxF d N₀ M z) (c z) t x y ≠ 0 → y ∈ macBox d N₀ M z :=
    fun z x y h => mem_macBoxF.1 (mem_of_boxR_ne_zero (hcB z) h)
  have hsplitTags : ∀ z x y, y ∈ macBox d N₀ M z → (macTags d N₀ M z x y).Nonempty ∧
      (macTags d N₀ M z x y ⊆ A ∨ macTags d N₀ M z x y ⊆ B ∨ ¬ macTags d N₀ M z x y ⊆ C) :=
    fun z x y hy => ⟨⟨_, macZ_end_mem_macTags hM hd z x y⟩, by
      by_cases hVC : macTags d N₀ M z x y ⊆ C
      · rcases macTags_subset_or hM hd hy hsep' (hVC.trans hCAB) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hVC)⟩
  have hG : taggedG Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t s =
      taggedG Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ A then s i else 0) +
      taggedG Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ B then s i else 0) :=
    taggedMat_split _ _ _ hAB hAC hBC hs (fun _ => rfl) (fun _ => rfl)
      fun z _ x y h => hsplitTags z x y (hGy z x y h)
  have hK : taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t s =
      taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ A then s i else 0) +
      taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ B then s i else 0) :=
    taggedMat_split _ _ _ hAB hAC hBC hs (fun _ => rfl) (fun _ => rfl)
      fun z _ x y h => hsplitTags z x y (hKy z x y h)
  have hend : ∀ z x y, macZ M y ∈ macTags d N₀ M z x y := fun z x y =>
    macZ_end_mem_macTags hM hd z x y
  have hstart : ∀ z x y, macZ M x ∈ macTags d N₀ M z x y := fun z x y =>
    macZ_start_mem_macTags hM hd z x y
  have m1 : taggedG Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ A then s i else 0) *
      taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ B then s i else 0) = 0 :=
    taggedMat_mul_eq_zero _ _ _ _ hAB (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)
  have m2 : taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ A then s i else 0) *
      taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ B then s i else 0) = 0 :=
    taggedMat_mul_eq_zero _ _ _ _ hAB (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)
  have m3 : taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ B then s i else 0) *
      taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ A then s i else 0) = 0 :=
    taggedMat_mul_eq_zero _ _ _ _ hBA (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)
  have m4 : taggedG Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ B then s i else 0) *
      taggedK Finset.univ (macBoxF d N₀ M) c (macTags d N₀ M) U t
        (fun i => if i ∈ A then s i else 0) = 0 :=
    taggedMat_mul_eq_zero _ _ _ _ hBA (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)
  rw [hK] at hu
  unfold taggedGfin
  rw [hG, hK]
  exact inv_split m2 m3 m1 m4 hu

/-- **Vanishing of the coefficient at a split support (matrix level).**  Let `C = A ⊔ B` be a
decomposition of a set of cells such that the boxes of `A` are disjoint from the boxes of `B`.
If `1 - K(s, t)` is invertible and the entries of `G_fin(s, t)` are analytic on the polydisc of
radius `e^κ`, `κ > 0`, then the mixed coefficient of every entry of `s ↦ G_fin(s, t)` at `C`
vanishes. -/
theorem coef_taggedGfin_eq_zero_of_separated_of_unit (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hunit : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) →
      IsUnit (1 - taggedK Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s))
    (hana : ∀ x y : L1Torus d N₀, AnalyticOnNhd ℂ (fun s => taggedGfin Finset.univ
        (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y)
      {s : MacIdx d N₀ M → ℂ | ∀ p, ‖s p‖ ≤ Real.exp κ})
    (x y : L1Torus d N₀) {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty)
    (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t s x y) C = 0 := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  refine coef_eq_zero_of_split hR ((hana x y).mono fun s hs p => ?_) Finset.disjoint_sdiff hAC
    Finset.sdiff_subset hA hB (fun s hs hsC => ?_)
  · simpa using (hs p).le
  · have := congrFun (congrFun (taggedGfin_split_of_separated hM hd U t hAC hsep hsC
      (hunit s fun p => by simpa using (hs p).le)) x) y
    simpa [Matrix.add_apply] using this

end Main

section Final

open Balaban.Localization MeasureTheory Set

variable {d N₀ M L k : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **Connected supports (the genuine statement), `G_fin`.**  For the tagged final family
`s ↦ G_fin(s, t)` of the final operator, the mixed coefficient at a set `C` of cells vanishes when
`C` is not connected in the macro-cell adjacency: `C = A ⊔ (C \ A)` with `A` and `C \ A` nonempty
and the boxes of `A` disjoint from the boxes of `C \ A`.  Same hypotheses as
`abstract_expansion_taggedGfin_final`. -/
theorem coef_taggedGfin_final_eq_zero_of_separated (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (x y : L1Torus d N₀) {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty)
    (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y)
      C = 0 := by
  have hfin := taggedGfin_final (N₀ := N₀) (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass ht hM
    (by linarith) hMB hMκ
  exact coef_taggedGfin_eq_zero_of_separated_of_unit hM hd _ t (by linarith) hfin.2.1
    hfin.2.2.1 x y hAC hA hB hsep

/-- The same, with the hypothesis "`C` is not connected" stated as the existence of a separated
decomposition. -/
theorem coef_taggedGfin_final_eq_zero_of_not_connected (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (x y : L1Torus d N₀) {C : Finset (MacIdx d N₀ M)}
    (hC : ∃ A ⊆ C, A.Nonempty ∧ (C \ A).Nonempty ∧
      Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef (fun s => taggedGfin Finset.univ (macBoxF d N₀ M)
      (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y)
      C = 0 := by
  obtain ⟨A, hAC, hA, hB, hsep⟩ := hC
  exact coef_taggedGfin_final_eq_zero_of_separated hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ
    x y hAC hA hB hsep

/-- **Connected supports, `C_fin`.**  The Stieltjes square-root family `s ↦ taggedCfin s` of the
final operator has vanishing coefficient at every set `C` of cells that is not connected in the
macro-cell adjacency. -/
theorem coef_taggedCfin_final_eq_zero_of_separated (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (x y : L1Torus d N₀) {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty)
    (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef (fun s => taggedCfin d L N₀ k M v a s x y) C = 0 := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  have hentry : ∀ s' : MacIdx d N₀ M → ℂ, taggedCfin d L N₀ k M v a s' x y =
      ((1 / Real.pi : ℝ) : ℂ) * ∫ t in Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s' x y := fun s' => by
    simp [taggedCfin, Localization.intMat, Matrix.smul_apply]
  refine coef_eq_zero_of_split hR ((taggedCfin_analyticOnNhd (N₀ := N₀) (k := k) (L := L)
    (v := v) (a := a) (M := M) hd hk hv0 hv1 ha1 ha2 hmass hM (by linarith) hMB hMκ x y).mono
    fun s hs p => by simpa using hs p) Finset.disjoint_sdiff hAC Finset.sdiff_subset hA hB
    (fun s hs hsC => ?_)
  have hsb : ∀ p, ‖s p‖ ≤ Real.exp κ := fun p => by simpa using (hs p).le
  have hproj : ∀ X : Finset (MacIdx d N₀ M), ∀ p, ‖(fun i => if i ∈ X then s i else 0) p‖ ≤
      Real.exp κ := fun X p => by
    by_cases hp : p ∈ X
    · simpa [hp] using hsb p
    · simpa [hp] using (Real.exp_pos κ).le
  have hint : ∀ X : Finset (MacIdx d N₀ M), Integrable (fun t : ℝ =>
      ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t
        (fun i => if i ∈ X then s i else 0) x y) (volume.restrict (Ioi (0 : ℝ))) := fun X =>
    taggedCfin_integrable hd hk hv0 hv1 ha1 ha2 hmass hM (by linarith) hMB hMκ (hproj X) x y
  have pt : ∀ t ∈ Ioi (0 : ℝ), ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        taggedGfin Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y =
      ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t
        (fun i => if i ∈ A then s i else 0) x y +
      ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * taggedGfin Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t
        (fun i => if i ∈ C \ A then s i else 0) x y := fun t ht => by
    have hfin := taggedGfin_final (N₀ := N₀) (k := k) (L := L) hd hk hv0 hv1 ha1 ha2 hmass
      (le_of_lt (mem_Ioi.1 ht)) hM (by linarith) hMB hMκ
    rw [taggedGfin_split_of_separated hM hd _ t hAC hsep hsC (hfin.2.1 s hsb), Matrix.add_apply,
      mul_add]
  rw [hentry s, hentry, hentry, ← mul_add]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi pt]
  exact integral_add (hint A) (hint (C \ A))

end Final

end Balaban.Green
