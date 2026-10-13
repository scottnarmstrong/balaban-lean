/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyHull
import Mathlib.Tactic.Linarith

/-!
# Non-vacuity of the hull: a circle of sixteen sites

`d = 1`, `L = 2`, `N₁ = 8`, `m₀ = m₁ = 0`, `K = 1`: the fine torus has `16` sites, the cells of level
`1` have side `2` and the `π′_1` boxes have side `4`.  The root is the cell `{0, 1}`.

* `J = {(1, 2), (1, 4)}`: the patches `{2, 3}` and `{4, 5}`.  The root cell touches the first patch
  (sites `1` and `2`) and the first patch touches the second (sites `3` and `4`); the hypothesis
  `RootConnected` holds, the hull is a polymer, contains the root cube, and satisfies the size and
  count bounds.
* `J' = {(1, 8)}`: the patch `{8, 9}` is far from the root cell.  The hull has the sites
  `{14, 15, 0, 1, 2, 3} ∪ {6, …, 11}`, which is not connected, so the hull is not a polymer and
  `RootConnected` fails: the hypothesis of `isPolyDom_hullOf` cannot be dropped.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

namespace DetCauchyHullWitness

/-- The torus of sixteen sites. -/
abbrev T : Type := CTorus 1 2 8 0 1

/-- The site `k`. -/
def pt (k : ℕ) : T := fun _ => (k : ZMod ((8 * 2 ^ 0) * 2 ^ 1))

/-- The root. -/
def z0 : RootIdx 1 2 8 0 1 := 0

theorem hN : (2 : ℕ) ^ 0 ∣ 8 := by norm_num

theorem rootCube_val : (rootCube (m₀ := 0) z0).1 = pt 0 := by
  funext μ
  simp [rootCube, rootSite, z0, cbase, pt]

theorem rootSet_eq : rootSet 0 z0 = box (pt 0) 2 := by
  unfold rootSet; rw [rootCube_val]; rfl

theorem pt_mem_box (a j s : ℕ) (hj : j < s) : pt (a + j) ∈ box (pt a) s := by
  refine ⟨fun _ => j, fun _ => hj, ?_⟩
  funext μ; simp [pt, natT]

theorem near_succ (k : ℕ) : Near 1 1 (pt k) (pt (k + 1)) := by
  refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
  funext μ; simp [pt]

theorem mem_Pset_two (k : ℕ) (hk : k % 2 = 0) (hk' : k + 1 < 16) :
    pt (k + 1) ∈ Pset 0 ((1 : ℕ), pt k) := by
  intro μ
  simp only [pt]
  rw [ZMod.val_natCast, ZMod.val_natCast]
  show (k + 1) % 16 / 2 ^ (1 + 0) = k % 16 / 2 ^ (1 + 0)
  rw [Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt (by omega)]
  omega

/-- The patches `{2, 3}` and `{4, 5}`. -/
def Jnear : Finset (ℕ × T) := {((1 : ℕ), pt 2), ((1 : ℕ), pt 4)}

/-- The patch `{8, 9}`. -/
def Jfar : Finset (ℕ × T) := {((1 : ℕ), pt 8)}

theorem Jnear_layer : ∀ P ∈ Jnear, P.1 ≤ 1 := by
  intro P hP
  simp only [Jnear, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl <;> exact le_rfl

theorem Jfar_layer : ∀ P ∈ Jfar, P.1 ≤ 1 := by
  intro P hP
  simp only [Jfar, Finset.mem_singleton] at hP
  subst hP; exact le_rfl

theorem rootConnected_near : RootConnected 0 z0 Jnear := by
  have h1 : ((1 : ℕ), pt 2) ∈ Jnear := by simp [Jnear]
  have h2 : ((1 : ℕ), pt 4) ∈ Jnear := by simp [Jnear]
  have t01 : MooreTouch (nodeSet 0 z0 none) (nodeSet 0 z0 (some ((1 : ℕ), pt 2))) :=
    ⟨pt 1, by rw [show nodeSet 0 z0 none = rootSet 0 z0 from rfl, rootSet_eq]; exact pt_mem_box 0 1 2 (by norm_num),
      pt 2, self_mem_Pset _, near_succ 1⟩
  have t12 : MooreTouch (nodeSet 0 z0 (some ((1 : ℕ), pt 2)))
      (nodeSet 0 z0 (some ((1 : ℕ), pt 4))) :=
    ⟨pt 3, mem_Pset_two 2 (by norm_num) (by norm_num), pt 4, self_mem_Pset _, near_succ 3⟩
  have j0 : JNode Jnear none := Or.inl rfl
  have j1 : JNode Jnear (some ((1 : ℕ), pt 2)) := Or.inr ⟨_, h1, rfl⟩
  have j2 : JNode Jnear (some ((1 : ℕ), pt 4)) := Or.inr ⟨_, h2, rfl⟩
  intro P hP
  simp only [Jnear, Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · exact Relation.ReflTransGen.single ⟨j0, j1, t01⟩
  · exact (Relation.ReflTransGen.single ⟨j0, j1, t01⟩).tail ⟨j1, j2, t12⟩

/-- The sites of the hull of the far patch are in `{14, 15, 0, …, 3} ∪ {6, …, 11}`. -/
theorem box_ok : ∀ (b : ZMod 16) (w w' : Fin 4), b.val % 2 = 0 →
    ((b + (w' : ℕ)).val / 2 = 0 ∨ (b + (w' : ℕ)).val / 2 = 4) →
    ((b + (w : ℕ)).val < 4 ∨ 14 ≤ (b + (w : ℕ)).val ∨
      (6 ≤ (b + (w : ℕ)).val ∧ (b + (w : ℕ)).val < 12)) := by
  decide +kernel

theorem step_ok : ∀ x x' : ZMod 16, (x.val < 4 ∨ 14 ≤ x.val) →
    (x'.val < 4 ∨ 14 ≤ x'.val ∨ (6 ≤ x'.val ∧ x'.val < 12)) → (x' = x + 1 ∨ x = x' + 1) →
    (x'.val < 4 ∨ 14 ≤ x'.val) := by
  decide +kernel

theorem root_cell_ok : ∀ j : Fin 2, (((0 : ℕ) : ZMod 16) + ((j : ℕ) : ZMod 16)).val / 2 = 0 := by
  decide +kernel

theorem cellSide_eq : cellSide 2 0 0 1 = 2 := by norm_num [cellSide]

theorem sites_far_allowed {x : T} (hx : x ∈ sitesOf (hullOf 0 z0 Jfar)) :
    ((x 0).val < 4 ∨ 14 ≤ (x 0).val ∨ (6 ≤ (x 0).val ∧ (x 0).val < 12)) := by
  unfold hullOf at hx
  rw [sitesOf_piHull hN] at hx
  obtain ⟨b, ⟨hba, s, ⟨w', hw', hs⟩, hsS⟩, ⟨w, hw, hxb⟩⟩ := Set.mem_iUnion₂.1 hx
  have hs0 : (s 0).val / 2 = 0 ∨ (s 0).val / 2 = 4 := by
    rcases hsS with h | h
    · rw [rootSet_eq] at h
      obtain ⟨u, hu, rfl⟩ := h
      left
      have h2 : u 0 < 2 := hu 0
      exact root_cell_ok ⟨u 0, h2⟩
    · obtain ⟨P, hP, hsP⟩ := Set.mem_iUnion₂.1 h
      simp only [Jfar, Finset.mem_singleton] at hP
      subst hP
      right
      have e : (s 0).val / 2 = ((pt 8) 0).val / 2 := hsP 0
      rw [e]
      decide +kernel
  have hb2 : (b 0).val % 2 = 0 := by
    have := hba 0
    rwa [cellSide_eq] at this
  have hw0 : w 0 < 4 := by
    have := hw 0
    rw [cellSide_eq] at this
    omega
  have hw0' : w' 0 < 4 := by
    have := hw' 0
    rw [cellSide_eq] at this
    omega
  have hx0 : x 0 = b 0 + ((w 0 : ℕ) : ZMod 16) := by rw [hxb]; rfl
  have hs0' : s 0 = b 0 + ((w' 0 : ℕ) : ZMod 16) := by rw [hs]; rfl
  rw [hx0]
  exact box_ok (b 0) ⟨w 0, hw0⟩ ⟨w' 0, hw0'⟩ hb2 (hs0' ▸ hs0)

theorem not_isPolyDom_far : ¬ IsPolyDom 0 1 (sitesOf (hullOf 0 z0 Jfar)) := by
  rintro ⟨-, -, hconn⟩
  have h0 : pt 0 ∈ sitesOf (hullOf 0 z0 Jfar) := by
    refine subset_sitesOf_piHull hN _ (Or.inl ?_)
    rw [rootSet_eq]; exact mem_box_self _ (by norm_num)
  have h8 : pt 8 ∈ sitesOf (hullOf 0 z0 Jfar) := by
    refine subset_sitesOf_piHull hN _ (Or.inr (Set.mem_iUnion₂.2 ⟨((1 : ℕ), pt 8), ?_, ?_⟩))
    · simp [Jfar]
    · exact self_mem_Pset _
  have key : ∀ x y : T, Relation.ReflTransGen
      (fun a b : T => a ∈ sitesOf (hullOf 0 z0 Jfar) ∧ b ∈ sitesOf (hullOf 0 z0 Jfar) ∧ Nbr a b)
      x y → ((x 0).val < 4 ∨ 14 ≤ (x 0).val) → ((y 0).val < 4 ∨ 14 ≤ (y 0).val) := by
    intro x y h
    induction h with
    | refl => exact id
    | @tail b c _ hbc ih =>
      intro hx
      have hb := ih hx
      obtain ⟨μ, hμ⟩ := hbc.2.2
      have hμ0 : μ = 0 := Subsingleton.elim _ _
      subst hμ0
      refine step_ok (b 0) (c 0) hb (sites_far_allowed hbc.2.1) ?_
      rcases hμ with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
  have h0v : (pt 0 0).val < 4 := by decide +kernel
  have h8v : ¬((pt 8 0).val < 4 ∨ 14 ≤ (pt 8 0).val) := by decide +kernel
  exact h8v (key _ _ (hconn _ h0 _ h8) (Or.inl h0v))

theorem notRootConnected_far : ¬ RootConnected 0 z0 Jfar := fun h =>
  not_isPolyDom_far (isPolyDom_hullOf hN le_rfl z0 Jfar Jfar_layer h)

end DetCauchyHullWitness

open DetCauchyHullWitness in
/-- **Non-vacuity of the hull package.**  On the circle of sixteen sites there are a root `z` and
a set `J` of two Moore-adjacent patches, connected to the root, whose hull is a polymer containing
the root cube and satisfying the size and count bounds; and a set `J'` not connected to the root
whose hull is not a polymer. -/
theorem detCauchyHull_witness :
    ∃ (z : RootIdx 1 2 8 0 1) (J J' : Finset (ℕ × CTorus 1 2 8 0 1)),
      J.card = 2 ∧ (∀ P ∈ J, P.1 ≤ 1) ∧ RootConnected 0 z J ∧
        IsPolyDom 0 1 (sitesOf (hullOf 0 z J)) ∧ rootCube (m₀ := 0) z ∈ hullOf 0 z J ∧
        dExt (hullOf 0 z J) ≤ (2 * (1 : ℕ) * 2 : ℝ) * J.card + 0 ∧
        (hullOf 0 z J).card ≤ 2 ^ 1 * 2 ^ 1 * (J.card + 1) ∧
      (∀ P ∈ J', P.1 ≤ 1) ∧ ¬ RootConnected 0 z J' ∧
        ¬ IsPolyDom 0 1 (sitesOf (hullOf 0 z J')) := by
  have hcard : Jnear.card = 2 := by
    unfold Jnear
    rw [Finset.card_pair]
    intro h
    have := congrArg (fun p : ℕ × T => (p.2 0).val) h
    revert this
    decide +kernel
  refine ⟨z0, Jnear, Jfar, hcard, Jnear_layer, rootConnected_near,
    isPolyDom_hullOf hN le_rfl z0 Jnear Jnear_layer rootConnected_near,
    rootCube_mem_hullOf z0 Jnear, ?_, card_hullOf_le hN z0 Jnear Jnear_layer, Jfar_layer,
    notRootConnected_far, not_isPolyDom_far⟩
  have := dExt_hullOf_le hN le_rfl z0 Jnear Jnear_layer rootConnected_near
  simpa using this

end Balaban.Fluctuation
