/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A product of order-connected sets meets a union of integer boxes in a connected set

The `ℤ^d` geometry behind the connectedness of the thickened interaction cubes inside `Ω₁`
(`HatConn`, P3 §4) for the generating sets `𝔹_k(W)` of `R`: there `□̂_z` is a box, `Ω₁` lifts to
a union of integer boxes, and two boxes meeting `□̂_z` overlap (or touch) in every coordinate.

* `NStep S`, `KStep S`: the nearest-neighbour and the king (`|X_μ - Y_μ| ≤ 1` for every `μ`) steps
  inside `S`; `box lo hi = ∏_μ [lo_μ, hi_μ]`;
* `pi_nconn`: a product of order-connected sets is nearest-neighbour connected;
* `nconn_inter_iUnion`: if `H = ∏_μ H_μ` with every `H_μ` order connected, and any two boxes
  meeting `H` overlap in every coordinate, `H ∩ ⋃_i B_i` is nearest-neighbour connected;
* `kconn_inter_iUnion`: if any two boxes meeting `H` overlap or touch in every coordinate,
  `H ∩ ⋃_i B_i` is king connected.
-/

@[expose] public section

namespace Balaban.LargeField.ZBox

open Set

variable {d : ℕ}

/-- A nearest-neighbour step of `ℤ^d` inside `S`. -/
def NStep (S : Set (Fin d → ℤ)) (X Y : Fin d → ℤ) : Prop :=
  X ∈ S ∧ Y ∈ S ∧ ∃ μ, Y = X + Pi.single μ 1 ∨ X = Y + Pi.single μ 1

/-- A king step of `ℤ^d` inside `S`: `|X_μ - Y_μ| ≤ 1` for every `μ`. -/
def KStep (S : Set (Fin d → ℤ)) (X Y : Fin d → ℤ) : Prop :=
  X ∈ S ∧ Y ∈ S ∧ ∀ μ, |X μ - Y μ| ≤ 1

/-- The integer box `∏_μ [lo_μ, hi_μ]`. -/
def box (lo hi : Fin d → ℤ) : Set (Fin d → ℤ) := Set.pi univ fun μ => Icc (lo μ) (hi μ)

theorem mem_box {lo hi X : Fin d → ℤ} : X ∈ box lo hi ↔ ∀ μ, lo μ ≤ X μ ∧ X μ ≤ hi μ := by
  simp [box, Set.mem_pi]

theorem NStep.mono {S T : Set (Fin d → ℤ)} (hST : S ⊆ T) {X Y : Fin d → ℤ} (h : NStep S X Y) :
    NStep T X Y :=
  ⟨hST h.1, hST h.2.1, h.2.2⟩

/-- A nearest-neighbour step is a king step. -/
theorem NStep.kStep {S : Set (Fin d → ℤ)} {X Y : Fin d → ℤ} (h : NStep S X Y) : KStep S X Y := by
  refine ⟨h.1, h.2.1, fun μ => ?_⟩
  obtain ⟨ν, h | h⟩ := h.2.2
  · rw [h]
    by_cases hν : μ = ν
    · subst hν
      simp only [Pi.add_apply, Pi.single_eq_same, abs_le]
      constructor <;> omega
    · simp [hν]
  · rw [h]
    by_cases hν : μ = ν
    · subst hν
      simp only [Pi.add_apply, Pi.single_eq_same, abs_le]
      constructor <;> omega
    · simp [hν]

/-- **A product of order-connected sets is nearest-neighbour connected**: move one coordinate at a
time towards the target. -/
theorem pi_nconn {s : Fin d → Set ℤ} (hs : ∀ μ, (s μ).OrdConnected) :
    ∀ X ∈ Set.pi univ s, ∀ Y ∈ Set.pi univ s,
      Relation.ReflTransGen (NStep (Set.pi univ s)) X Y := by
  intro X₀ hX₀ Y hY
  suffices h : ∀ n : ℕ, ∀ X ∈ Set.pi univ s, ∑ μ, (X μ - Y μ).natAbs = n →
      Relation.ReflTransGen (NStep (Set.pi univ s)) X Y from h _ X₀ hX₀ rfl
  intro n
  induction n with
  | zero =>
    intro X _ hn
    have : X = Y := funext fun μ => by
      have := (Finset.sum_eq_zero_iff.1 hn) μ (Finset.mem_univ μ)
      omega
    rw [this]
  | succ n ih =>
    intro X hX hn
    obtain ⟨μ, -, hμ⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ μ, (X μ - Y μ).natAbs ≠ 0)
    set δ : ℤ := if X μ < Y μ then 1 else -1 with hδ
    set X' : Fin d → ℤ := X + Pi.single μ δ with hX'
    have hX'μ : X' μ = X μ + δ := by simp [hX']
    have hX'ν : ∀ ν, ν ≠ μ → X' ν = X ν := fun ν hν => by simp [hX', hν]
    have hδμ : (X' μ - Y μ).natAbs + 1 = (X μ - Y μ).natAbs := by
      rw [hX'μ, hδ]
      split_ifs with hlt <;> omega
    have hmem : X' ∈ Set.pi univ s := by
      intro ν _
      by_cases hν : ν = μ
      · subst hν
        rw [hX'μ]
        refine (hs ν).uIcc_subset (hX ν (mem_univ _)) (hY ν (mem_univ _)) ?_
        rw [Set.mem_uIcc, hδ]
        split_ifs with hlt
        · left; constructor <;> omega
        · right; constructor <;> omega
      · rw [hX'ν ν hν]
        exact hX ν (mem_univ _)
    have hsum : ∑ ν, (X' ν - Y ν).natAbs = n := by
      have e1 := Finset.sum_erase_add Finset.univ (fun ν => (X ν - Y ν).natAbs)
        (Finset.mem_univ μ)
      have e2 := Finset.sum_erase_add Finset.univ (fun ν => (X' ν - Y ν).natAbs)
        (Finset.mem_univ μ)
      have e3 : ∑ ν ∈ Finset.univ.erase μ, (X' ν - Y ν).natAbs =
          ∑ ν ∈ Finset.univ.erase μ, (X ν - Y ν).natAbs :=
        Finset.sum_congr rfl fun ν hν => by rw [hX'ν ν (Finset.ne_of_mem_erase hν)]
      omega
    refine Relation.ReflTransGen.head ⟨hX, hmem, μ, ?_⟩ (ih X' hmem hsum)
    by_cases hlt : X μ < Y μ
    · left
      simp [hX', hδ, hlt]
    · right
      funext ν
      by_cases hν : ν = μ
      · subst hν; simp [hX', hδ, hlt]
      · simp [hX', hν]

/-- **Three order-connected sets of `ℤ` that meet pairwise have a common point** (the median of
three points of the pairwise intersections). -/
theorem exists_mem_three {A B C : Set ℤ} (hA : A.OrdConnected) (hB : B.OrdConnected)
    (hC : C.OrdConnected) {a b c : ℤ} (ha : a ∈ A ∩ B) (hb : b ∈ A ∩ C) (hc : c ∈ B ∩ C) :
    ∃ x, x ∈ A ∧ x ∈ B ∧ x ∈ C := by
  refine ⟨max (min a b) (min (max a b) c), ?_, ?_, ?_⟩
  · refine hA.uIcc_subset ha.1 hb.1 ?_
    simp only [Set.mem_uIcc, max_def, min_def]
    split_ifs <;> omega
  · refine hB.uIcc_subset ha.2 hc.1 ?_
    simp only [Set.mem_uIcc, max_def, min_def]
    split_ifs <;> omega
  · refine hC.uIcc_subset hb.2 hc.2 ?_
    simp only [Set.mem_uIcc, max_def, min_def]
    split_ifs <;> omega

/-- **Two intervals that overlap or touch, met by an order-connected set**, contain points of the
set at distance `≤ 1` (clamp one point into the other interval and back). -/
theorem exists_near_two {A : Set ℤ} (hA : A.OrdConnected) {l u l' u' a b : ℤ} (ha : a ∈ A)
    (ha' : l ≤ a ∧ a ≤ u) (hb : b ∈ A) (hb' : l' ≤ b ∧ b ≤ u') (h1 : l' ≤ u + 1)
    (h2 : l ≤ u' + 1) :
    ∃ x y, x ∈ A ∧ (l ≤ x ∧ x ≤ u) ∧ y ∈ A ∧ (l' ≤ y ∧ y ≤ u') ∧ |x - y| ≤ 1 := by
  have hxA : max l (min u b) ∈ A := by
    refine hA.uIcc_subset ha hb ?_
    simp only [Set.mem_uIcc, max_def, min_def]
    split_ifs <;> omega
  have hyA : max l' (min u' (max l (min u b))) ∈ A := by
    refine hA.uIcc_subset hb hxA ?_
    simp only [Set.mem_uIcc, max_def, min_def]
    split_ifs <;> omega
  refine ⟨_, _, hxA, ?_, hyA, ?_, ?_⟩
  · simp only [max_def, min_def]
    split_ifs <;> omega
  · simp only [max_def, min_def]
    split_ifs <;> omega
  · rw [abs_le]
    simp only [max_def, min_def]
    split_ifs <;> omega

/-- The trace of a box on a product is the product of the traces. -/
theorem pi_inter_box (Hs : Fin d → Set ℤ) (lo hi : Fin d → ℤ) :
    Set.pi univ Hs ∩ box lo hi = Set.pi univ fun μ => Hs μ ∩ Icc (lo μ) (hi μ) := by
  ext X
  simp only [box, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies]
  exact ⟨fun h μ => ⟨h.1 μ, h.2 μ⟩, fun h => ⟨fun μ => (h μ).1, fun μ => (h μ).2⟩⟩

/-- **The boxes overlapping in every coordinate**: if `H = ∏_μ H_μ` (each `H_μ` order connected)
and any two boxes of the family that meet `H` overlap in every coordinate, the set
`H ∩ ⋃_i B_i` is nearest-neighbour connected. -/
theorem nconn_inter_iUnion {ι : Type*} {Hs : Fin d → Set ℤ} (hH : ∀ μ, (Hs μ).OrdConnected)
    (lo hi : ι → Fin d → ℤ)
    (hov : ∀ i j, (Set.pi univ Hs ∩ box (lo i) (hi i)).Nonempty →
      (Set.pi univ Hs ∩ box (lo j) (hi j)).Nonempty → ∀ μ, lo j μ ≤ hi i μ ∧ lo i μ ≤ hi j μ) :
    ∀ X ∈ Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i),
      ∀ Y ∈ Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i),
        Relation.ReflTransGen (NStep (Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i))) X Y := by
  set S := Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i) with hS
  have hsub : ∀ i, Set.pi univ Hs ∩ box (lo i) (hi i) ⊆ S := fun i X hX =>
    ⟨hX.1, Set.mem_iUnion.2 ⟨i, hX.2⟩⟩
  have hconn : ∀ i, ∀ X ∈ Set.pi univ Hs ∩ box (lo i) (hi i),
      ∀ Y ∈ Set.pi univ Hs ∩ box (lo i) (hi i), Relation.ReflTransGen (NStep S) X Y := by
    intro i X hX Y hY
    rw [pi_inter_box] at hX hY
    have h := pi_nconn (fun μ => (hH μ).inter ordConnected_Icc) X hX Y hY
    rw [← pi_inter_box] at h
    exact Relation.ReflTransGen.mono (fun _ _ (hst : NStep _ _ _) => hst.mono (hsub i)) _ _ h
  rintro X ⟨hXH, hXU⟩ Y ⟨hYH, hYU⟩
  obtain ⟨i, hXi⟩ := Set.mem_iUnion.1 hXU
  obtain ⟨j, hYj⟩ := Set.mem_iUnion.1 hYU
  have hov' := hov i j ⟨X, hXH, hXi⟩ ⟨Y, hYH, hYj⟩
  have hXi' := mem_box.1 hXi
  have hYj' := mem_box.1 hYj
  have key : ∀ μ, ∃ z, z ∈ Hs μ ∧ z ∈ Icc (lo i μ) (hi i μ) ∧ z ∈ Icc (lo j μ) (hi j μ) := by
    intro μ
    refine exists_mem_three (hH μ) ordConnected_Icc ordConnected_Icc
      (a := X μ) (b := Y μ) (c := max (lo i μ) (lo j μ)) ⟨hXH μ (mem_univ _), hXi' μ⟩
      ⟨hYH μ (mem_univ _), hYj' μ⟩ ⟨?_, ?_⟩
    · have := hov' μ; have := hXi' μ; have := hYj' μ
      simp only [Set.mem_Icc, max_def]
      split_ifs <;> omega
    · have := hov' μ; have := hXi' μ; have := hYj' μ
      simp only [Set.mem_Icc, max_def]
      split_ifs <;> omega
  choose Z hZH hZi hZj using key
  have hZi' : Z ∈ Set.pi univ Hs ∩ box (lo i) (hi i) :=
    ⟨fun μ _ => hZH μ, mem_box.2 fun μ => hZi μ⟩
  have hZj' : Z ∈ Set.pi univ Hs ∩ box (lo j) (hi j) :=
    ⟨fun μ _ => hZH μ, mem_box.2 fun μ => hZj μ⟩
  exact (hconn i X ⟨hXH, hXi⟩ Z hZi').trans (hconn j Z hZj' Y ⟨hYH, hYj⟩)

/-- **The boxes overlapping or touching in every coordinate**: if `H = ∏_μ H_μ` (each `H_μ` order
connected) and any two boxes of the family that meet `H` overlap or touch in every coordinate, the
set `H ∩ ⋃_i B_i` is king connected. -/
theorem kconn_inter_iUnion {ι : Type*} {Hs : Fin d → Set ℤ} (hH : ∀ μ, (Hs μ).OrdConnected)
    (lo hi : ι → Fin d → ℤ)
    (htouch : ∀ i j, (Set.pi univ Hs ∩ box (lo i) (hi i)).Nonempty →
      (Set.pi univ Hs ∩ box (lo j) (hi j)).Nonempty →
        ∀ μ, lo j μ ≤ hi i μ + 1 ∧ lo i μ ≤ hi j μ + 1) :
    ∀ X ∈ Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i),
      ∀ Y ∈ Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i),
        Relation.ReflTransGen (KStep (Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i))) X Y := by
  set S := Set.pi univ Hs ∩ ⋃ i, box (lo i) (hi i) with hS
  have hsub : ∀ i, Set.pi univ Hs ∩ box (lo i) (hi i) ⊆ S := fun i X hX =>
    ⟨hX.1, Set.mem_iUnion.2 ⟨i, hX.2⟩⟩
  have hconn : ∀ i, ∀ X ∈ Set.pi univ Hs ∩ box (lo i) (hi i),
      ∀ Y ∈ Set.pi univ Hs ∩ box (lo i) (hi i), Relation.ReflTransGen (KStep S) X Y := by
    intro i X hX Y hY
    rw [pi_inter_box] at hX hY
    have h := pi_nconn (fun μ => (hH μ).inter ordConnected_Icc) X hX Y hY
    rw [← pi_inter_box] at h
    exact Relation.ReflTransGen.mono (fun _ _ (hst : NStep _ _ _) => (hst.mono (hsub i)).kStep) _ _ h
  rintro X ⟨hXH, hXU⟩ Y ⟨hYH, hYU⟩
  obtain ⟨i, hXi⟩ := Set.mem_iUnion.1 hXU
  obtain ⟨j, hYj⟩ := Set.mem_iUnion.1 hYU
  have ht := htouch i j ⟨X, hXH, hXi⟩ ⟨Y, hYH, hYj⟩
  have hXi' := mem_box.1 hXi
  have hYj' := mem_box.1 hYj
  have key : ∀ μ, ∃ x y, x ∈ Hs μ ∧ (lo i μ ≤ x ∧ x ≤ hi i μ) ∧ y ∈ Hs μ ∧
      (lo j μ ≤ y ∧ y ≤ hi j μ) ∧ |x - y| ≤ 1 := fun μ =>
    exists_near_two (hH μ) (hXH μ (mem_univ _)) (hXi' μ) (hYH μ (mem_univ _)) (hYj' μ)
      (ht μ).1 (ht μ).2
  choose x y hxH hxi hyH hyj hxy using key
  have hxi' : x ∈ Set.pi univ Hs ∩ box (lo i) (hi i) :=
    ⟨fun μ _ => hxH μ, mem_box.2 hxi⟩
  have hyj' : y ∈ Set.pi univ Hs ∩ box (lo j) (hi j) :=
    ⟨fun μ _ => hyH μ, mem_box.2 hyj⟩
  refine (hconn i X ⟨hXH, hXi⟩ x hxi').trans (Relation.ReflTransGen.head ?_
    (hconn j y hyj' Y ⟨hYH, hYj⟩))
  exact ⟨hsub i hxi', hsub j hyj', hxy⟩

end Balaban.LargeField.ZBox
