/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFDouble
public import Balaban.Polymer.Hole

/-!
# The geometry of the record gas (A6-4)

The sites of the record gas are the points of the doubled torus, with the king graph (distinct
points at index distance `≤ 1`, `kingGraph`, degree `≤ 3^d`). The support `dblNbhd ω Y` of a record
with cubes `Y` (an `ω`-component) is connected (`isAnimal_dblNbhd`): every ball of the index
distance is connected (`reach_ball`), and the balls of radius `ω - 1` around the doubled images of
two points of `Y` at distance `< ω` meet. Its size is at most `(2ω - 1)^d |Y|`
(`card_dblNbhd_le`), a ball of radius `m` having at most `(2m + 1)^d` points (`card_ball_le`).

* `kingGraph`, `kingGraph_degree_le`, `card_ball_le`;
* `reach_ball`, **`isAnimal_dblNbhd`**, `card_dblNbhd_le`;
* the supports of the couplings: `mem_comps_two_of_isAnimal`, **`isAnimal_dblNbhd_two`**,
  `card_dblNbhd_two_le`.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.Polymer

namespace Balaban.RootFSpine

section King

variable (d n : ℕ) [NeZero n]

/-- **The king graph on the torus**: distinct points at index distance `≤ 1`. -/
def kingGraph : SimpleGraph (Torus d n) where
  Adj a b := a ≠ b ∧ supDist a b ≤ 1
  symm := ⟨fun a b h => ⟨h.1.symm, by rw [supDist_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance : (kingGraph d n).LocallyFinite := fun _ => Fintype.ofFinite _

variable {d n}

open Classical in
/-- **A ball of the index distance of radius `m` has at most `(2m + 1)^d` points.** -/
theorem card_ball_le (c : Torus d n) (m : ℕ) :
    (Finset.univ.filter fun b : Torus d n => supDist c b ≤ m).card ≤ (2 * m + 1) ^ d := by
  have hsub : (Finset.univ.filter fun b : Torus d n => supDist c b ≤ m) ⊆
      (Finset.univ : Finset (Fin d → Fin (2 * m + 1))).image
        (fun δ => fun i => c i + ((((δ i : ℕ) : ℤ) - m : ℤ) : ZMod n)) := by
    intro b hb
    have h := supDist_le_iff.1 (Finset.mem_filter.1 hb).2
    have ht : ∀ i, ∃ t : ℤ, |t| ≤ m ∧ (t : ZMod n) = b i - c i := fun i =>
      (cycNorm_le_iff (b i - c i) m).1 (by rw [cycNorm_sub_comm]; exact h i)
    choose t ht1 ht2 using ht
    refine Finset.mem_image.2 ⟨fun i => ⟨(t i + m).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := abs_le.1 (ht1 i)
      omega
    · funext i
      have h1 := abs_le.1 (ht1 i)
      have h2 : (((t i + m).toNat : ℕ) : ℤ) - m = t i := by omega
      simp only
      rw [h2, ht2 i]
      ring
  calc _ ≤ ((Finset.univ : Finset (Fin d → Fin (2 * m + 1))).image _).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d → Fin (2 * m + 1))).card := Finset.card_image_le
    _ = (2 * m + 1) ^ d := by simp

open Classical in
/-- The king graph has degree at most `3^d`. -/
theorem kingGraph_degree_le (a : Torus d n) : (kingGraph d n).degree a ≤ 3 ^ d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((kingGraph d n).neighborFinset a).card ≤
      (Finset.univ.filter fun b : Torus d n => supDist a b ≤ 1).card := by
        refine Finset.card_le_card fun b hb => ?_
        rw [SimpleGraph.mem_neighborFinset] at hb
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (show a ≠ b ∧ supDist a b ≤ 1 from hb).2⟩
    _ ≤ (2 * 1 + 1) ^ d := card_ball_le a 1
    _ = 3 ^ d := by norm_num

/-- **Every ball of the index distance is connected in the king graph**: the centre reaches every
point of the ball inside the ball. -/
theorem reach_ball (c : Torus d n) (m : ℕ) {p : Torus d n} (hp : supDist c p ≤ m) :
    Relation.ReflTransGen
      (fun a b => supDist c a ≤ m ∧ supDist c b ≤ m ∧ (kingGraph d n).Adj a b) c p := by
  induction m generalizing p with
  | zero =>
    have : c = p := supDist_eq_zero.1 (Nat.le_zero.1 hp)
    subst this
    exact Relation.ReflTransGen.refl
  | succ m ih =>
    obtain ⟨w, hw1, hw2⟩ := exists_split (a := m) (b := 1) hp
    have h1 : Relation.ReflTransGen (fun a b => supDist c a ≤ m + 1 ∧ supDist c b ≤ m + 1 ∧
        (kingGraph d n).Adj a b) c w :=
      Relation.ReflTransGen.mono (fun a b hab => ⟨Nat.le_succ_of_le hab.1,
        Nat.le_succ_of_le hab.2.1, hab.2.2⟩) _ _ (ih hw1)
    by_cases hwp : w = p
    · subst hwp
      exact h1
    · exact h1.tail ⟨Nat.le_succ_of_le hw1, hp,
        (show (kingGraph d n).Adj w p from ⟨hwp, hw2⟩)⟩

end King

section Supp

variable {d n : ℕ} [NeZero n]

/-- **The support of a record is connected**: for an `ω`-component `Y` (`ω ≥ 1`), the
`(ω - 1)`-neighbourhood of `2·Y` in the doubled torus is connected in the king graph. -/
theorem isAnimal_dblNbhd {ω : ℕ} (hω : 1 ≤ ω) {X Y : Finset (Torus d n)}
    (hY : Y ∈ comps ω X) : IsAnimal (kingGraph d (2 * n)) (dblNbhd ω Y) := by
  classical
  set D := dblNbhd ω Y with hD
  set Rel := fun a b : Torus d (2 * n) => a ∈ D ∧ b ∈ D ∧ (kingGraph d (2 * n)).Adj a b
  have hsymm : ∀ a b, Relation.ReflTransGen Rel a b → Relation.ReflTransGen Rel b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      exact (Relation.ReflTransGen.single ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩).trans ih
  have hmemD : ∀ x ∈ Y, ∀ p, supDist (tDouble x) p ≤ ω - 1 → p ∈ D := fun x hx p hp =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, hp⟩
  have hball : ∀ x ∈ Y, ∀ p, supDist (tDouble x) p ≤ ω - 1 →
      Relation.ReflTransGen Rel (tDouble x) p := fun x hx p hp =>
    Relation.ReflTransGen.mono (fun a b hab => ⟨hmemD x hx a hab.1, hmemD x hx b hab.2.1,
      hab.2.2⟩) _ _ (reach_ball (tDouble x) (ω - 1) hp)
  have hchain : ∀ x ∈ Y, ∀ y, Linked ω (X : Set (Torus d n)) x y → y ∈ Y →
      Relation.ReflTransGen Rel (tDouble x) (tDouble y) := by
    intro x hx y hxy
    induction hxy with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail b c hxb hbc ih =>
      intro hc
      have hb : b ∈ Y := (mem_comp_iff hY hx).2 ⟨hbc.1, hxb⟩
      have h1 : supDist (tDouble b) (tDouble c) ≤ (ω - 1) + (ω - 1) := by
        have := (supDist_tDouble_le_iff b c (ω - 1)).2 (by have := hbc.2.2; omega)
        omega
      obtain ⟨w, hw1, hw2⟩ := exists_split h1
      refine (ih hb).trans ((hball b hb w hw1).trans (hsymm _ _ (hball c hc w ?_)))
      rw [supDist_comm]
      exact hw2
  rw [isAnimal_iff]
  obtain ⟨x₀, hx₀⟩ := comp_nonempty hY
  refine ⟨⟨tDouble x₀, hmemD x₀ hx₀ _ (by rw [supDist_self]; exact Nat.zero_le _)⟩, ?_⟩
  intro p hp q hq
  obtain ⟨x, hx, hxp⟩ := (Finset.mem_filter.1 hp).2
  obtain ⟨y, hy, hyq⟩ := (Finset.mem_filter.1 hq).2
  have hxy := ((mem_comp_iff hY hx).1 hy).2
  exact (hsymm _ _ (hball x hx p hxp)).trans ((hchain x hx y hxy hy).trans (hball y hy q hyq))

/-- **The size of the support of a record**: at most `(2ω - 1)^d |Y|`. -/
theorem card_dblNbhd_le (ω : ℕ) (Y : Finset (Torus d n)) :
    (dblNbhd ω Y).card ≤ (2 * (ω - 1) + 1) ^ d * Y.card := by
  classical
  have hsub : dblNbhd ω Y ⊆ Y.biUnion fun x =>
      Finset.univ.filter fun b : Torus d (2 * n) => supDist (tDouble x) b ≤ ω - 1 := by
    intro w hw
    obtain ⟨x, hx, hxw⟩ := (Finset.mem_filter.1 hw).2
    exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxw⟩⟩
  calc (dblNbhd ω Y).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ Y, (Finset.univ.filter fun b : Torus d (2 * n) =>
          supDist (tDouble x) b ≤ ω - 1).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Y, (2 * (ω - 1) + 1) ^ d := Finset.sum_le_sum fun x _ => card_ball_le _ _
    _ = (2 * (ω - 1) + 1) ^ d * Y.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **A king-connected set of cubes is a single `2`-component of itself.** -/
theorem mem_comps_two_of_isAnimal {X : Finset (Torus d n)} (hX : IsAnimal (kingGraph d n) X) :
    X ∈ comps 2 X := by
  classical
  obtain ⟨x₀, hx₀⟩ := hX.1
  refine mem_comps_iff.2 ⟨x₀, hx₀, ?_⟩
  ext y
  rw [mem_linkClass]
  constructor
  · intro hy
    refine ⟨hy, ?_⟩
    have hp := ((isAnimal_iff (kingGraph d n) X).1 hX).2 x₀ hx₀ y hy
    refine Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, hab.2.1, ?_⟩) _ _ hp
    have := (show a ≠ b ∧ supDist a b ≤ 1 from hab.2.2).2
    omega
  · exact fun h => h.1

/-- **The support of a coupling is connected**: for a king-connected set `X` of cubes, the
`1`-neighbourhood of `2·X` in the doubled torus is connected. -/
theorem isAnimal_dblNbhd_two {X : Finset (Torus d n)} (hX : IsAnimal (kingGraph d n) X) :
    IsAnimal (kingGraph d (2 * n)) (dblNbhd 2 X) :=
  isAnimal_dblNbhd (by norm_num) (mem_comps_two_of_isAnimal hX)

/-- The support of a coupling has at most `3^d` sites per cube. -/
theorem card_dblNbhd_two_le (X : Finset (Torus d n)) :
    (dblNbhd 2 X).card ≤ 3 ^ d * X.card := by
  have := card_dblNbhd_le 2 X
  simpa using this

end Supp

end Balaban.RootFSpine
