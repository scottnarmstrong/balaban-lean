/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseDefectWalkTransport
public import Balaban.Polymer.TwoTorusDet
import Mathlib.Tactic.Linarith

/-!
# The polymer hull of the sites visited by a walk

A walk of `m` steps of range `r` visits at most `m + 1` sites, connected by steps with
`‖z_{i+1} - z_i‖_∞ ≤ r`.  The ℓ∞ balls of radius `r` about its sites form a nearest-neighbour
connected set `T`; the cells of side `L^{m₁}` that meet `T` give a set of parameter cubes `J`
(patches `Pset m₁ (0, b)`), connected to the root, with `|J| ≤ (2r+1)^d (m+1)`.  Its hull
`hullOf m₀ z J` is the polymer attached to the walk; it is a polymer of the small-field class and
has size at most `2 d L (2r+1)^d (m + 1)` (`dExt_hullOf_le`).

* `ball_chain`, `ball_chain_at`: a point of the box of radius `r` about `s` is joined to `s` by
  nearest-neighbour steps inside the box;
* `card_torusBall_le`: the ball has at most `(2r+1)^d` points.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.Polymer Balaban.Fluctuation Balaban.Polymer.TwoTorusStep

section Ball

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Nearest-neighbour steps inside the box of radius `r` join the origin to every point of the
box: the point with centred coordinates `v` is reached from `0`. -/
theorem ball_chain {r : ℕ} (hn : 2 * r + 1 < n) (v : Fin d → ℤ) (hv : ∀ μ, |v μ| ≤ r) :
    Relation.ReflTransGen
      (fun a b : Torus d n => InBox d r n a ∧ InBox d r n b ∧ Nbr a b)
      (0 : Torus d n) (fun μ => ((v μ : ℤ) : ZMod n)) := by
  suffices h : ∀ N : ℕ, ∀ v : Fin d → ℤ, (∀ μ, |v μ| ≤ r) → ∑ μ, (v μ).natAbs = N →
      Relation.ReflTransGen
        (fun a b : Torus d n => InBox d r n a ∧ InBox d r n b ∧ Nbr a b)
        (0 : Torus d n) (fun μ => ((v μ : ℤ) : ZMod n)) from h _ v hv rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro v hv hN
  have hbox : ∀ w : Fin d → ℤ, (∀ μ, |w μ| ≤ r) →
      InBox d r n (fun μ => ((w μ : ℤ) : ZMod n)) :=
    fun w hw μ => inBox_of_int hn _ (w μ) rfl (hw μ)
  by_cases h0 : ∀ μ, v μ = 0
  · have : (fun μ => ((v μ : ℤ) : ZMod n)) = 0 := funext fun μ => by simp [h0 μ]
    rw [this]
  · push Not at h0
    obtain ⟨μ, hμ⟩ := h0
    obtain ⟨ε, hε, hlt⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (v μ - ε).natAbs < (v μ).natAbs := by
      rcases lt_or_gt_of_ne hμ with h | h
      · exact ⟨-1, Or.inr rfl, by omega⟩
      · exact ⟨1, Or.inl rfl, by omega⟩
    set v' : Fin d → ℤ := Function.update v μ (v μ - ε) with hv'
    have hvμ : (v μ).natAbs ≤ r := by
      have := hv μ; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
    have hv'b : ∀ ν, |v' ν| ≤ r := by
      intro ν
      by_cases h : ν = μ
      · subst h
        simp only [hv', Function.update_self]
        rw [Int.abs_eq_natAbs]; exact_mod_cast hlt.le.trans hvμ
      · simp only [hv', Function.update_of_ne h]; exact hv ν
    have hsum : ∑ ν, (v' ν).natAbs < ∑ ν, (v ν).natAbs := by
      refine Finset.sum_lt_sum (fun ν _ => ?_) ⟨μ, Finset.mem_univ _, ?_⟩
      · by_cases h : ν = μ
        · subst h; simp only [hv', Function.update_self]; exact hlt.le
        · simp [hv', Function.update_of_ne h]
      · simpa [hv'] using hlt
    have hchain := ih _ (by omega) v' hv'b rfl
    refine hchain.tail ⟨hbox v' hv'b, hbox v hv, μ, ?_⟩
    rcases hε with rfl | rfl
    · left
      funext ν
      by_cases h : ν = μ
      · subst h; simp [hv']
      · simp [hv', Function.update_of_ne h, Pi.single_eq_of_ne h]
    · right
      funext ν
      by_cases h : ν = μ
      · subst h; simp [hv']
      · simp [hv', Function.update_of_ne h, Pi.single_eq_of_ne h]

omit [NeZero n] in
/-- **A point of the ball about `s` is joined to `s` inside the ball.** -/
theorem ball_chain_at {r : ℕ} (hn : 2 * r + 1 < n) (s t : Torus d n)
    (ht : InBox d r n (t - s)) :
    Relation.ReflTransGen
      (fun a b : Torus d n => InBox d r n (a - s) ∧ InBox d r n (b - s) ∧ Nbr a b) s t := by
  have hv : (fun μ => ((((t - s) μ).valMinAbs : ℤ) : ZMod n)) = t - s :=
    funext fun μ => ZMod.coe_valMinAbs _
  have hch := ball_chain (d := d) hn (fun μ => ((t - s) μ).valMinAbs) ht
  have hl : Relation.ReflTransGen
      (fun a b : Torus d n => InBox d r n (a - s) ∧ InBox d r n (b - s) ∧ Nbr a b)
      ((0 : Torus d n) + s) ((fun μ => ((((t - s) μ).valMinAbs : ℤ) : ZMod n)) + s) := by
    refine Relation.ReflTransGen.lift (fun x : Torus d n => x + s) ?_ _ _ hch
    rintro a b ⟨ha, hb, μ, h⟩
    refine ⟨by simpa using ha, by simpa using hb, μ, ?_⟩
    rcases h with h | h
    · left; rw [h]; exact add_right_comm _ _ _
    · right; rw [h]; exact add_right_comm _ _ _
  have he : (fun μ => ((((t - s) μ).valMinAbs : ℤ) : ZMod n)) + s = t := by
    rw [hv]; exact sub_add_cancel t s
  rw [zero_add, he] at hl
  exact hl

open scoped Classical in
/-- **The ball of radius `r` has at most `(2r+1)^d` points.** -/
theorem card_torusBall_le {r : ℕ} (s : Torus d n) :
    (Finset.univ.filter fun y : Torus d n => InBox d r n (y - s)).card ≤ (2 * r + 1) ^ d := by
  classical
  have hcard : (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) r).card =
      (2 * r + 1) ^ d := by
    rw [Fintype.card_piFinset]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun y => fun μ => ((y - s) μ).valMinAbs) ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro μ
    exact abs_le.1 (hy μ)
  · intro y _ y' _ h
    have : y - s = y' - s := funext fun μ => by
      rw [← ZMod.coe_valMinAbs ((y - s) μ), ← ZMod.coe_valMinAbs ((y' - s) μ)]
      exact congrArg (fun z : ℤ => (z : ZMod n)) (congrFun h μ)
    exact sub_left_injective this

end Ball

section Label

open scoped Classical

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- **The `r`-neighbourhood of a finite set of sites**: the sites at ℓ∞ distance at most `r` from
one of them. -/
noncomputable def ballNbhd (r : ℕ) (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)) :
    Finset (Balaban.Localization.CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun y => ∃ a ∈ A, InBox d r ((N₁ * L ^ m₁) * L ^ K) (y - a)

/-- **The parameter cubes of a finite set of sites**: the patches `Pset m₁ (0, b)` of the cells of
side `L^{m₁}` that meet the `r`-neighbourhood of `A`. -/
noncomputable def walkJ (r : ℕ) (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)) :
    Finset (ℕ × Balaban.Localization.CTorus d L N₁ m₁ K) :=
  (ballNbhd r A).image fun y => (0, cbase (L ^ (0 + m₁)) y)

theorem mem_ballNbhd {r : ℕ} {A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)} {y : Balaban.Localization.CTorus d L N₁ m₁ K} :
    y ∈ ballNbhd r A ↔ ∃ a ∈ A, InBox d r ((N₁ * L ^ m₁) * L ^ K) (y - a) := by
  simp [ballNbhd]

theorem subset_ballNbhd {r : ℕ} {A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)} {a : Balaban.Localization.CTorus d L N₁ m₁ K}
    (ha : a ∈ A) : a ∈ ballNbhd r A :=
  mem_ballNbhd.2 ⟨a, ha, fun μ => by simp⟩

theorem ballNbhd_mono {r : ℕ} {A B : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)} (h : A ⊆ B) :
    ballNbhd r A ⊆ ballNbhd r B := fun y hy => by
  obtain ⟨a, ha, hya⟩ := mem_ballNbhd.1 hy
  exact mem_ballNbhd.2 ⟨a, h ha, hya⟩

/-- The neighbourhood of `A` has at most `|A| (2r+1)^d` sites. -/
theorem card_ballNbhd_le (r : ℕ) (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)) :
    (ballNbhd r A).card ≤ A.card * (2 * r + 1) ^ d := by
  have h : ballNbhd r A ⊆ A.biUnion fun a =>
      Finset.univ.filter fun y : Balaban.Localization.CTorus d L N₁ m₁ K => InBox d r ((N₁ * L ^ m₁) * L ^ K) (y - a) := by
    intro y hy
    obtain ⟨a, ha, hya⟩ := mem_ballNbhd.1 hy
    exact Finset.mem_biUnion.2 ⟨a, ha, by simpa using hya⟩
  refine (Finset.card_le_card h).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ a ∈ A, (Finset.univ.filter fun y : Balaban.Localization.CTorus d L N₁ m₁ K =>
        InBox d r ((N₁ * L ^ m₁) * L ^ K) (y - a)).card ≤ ∑ _a ∈ A, (2 * r + 1) ^ d :=
      Finset.sum_le_sum fun a _ => card_torusBall_le a
    _ = A.card * (2 * r + 1) ^ d := by simp

theorem card_walkJ_le (r : ℕ) (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)) :
    (walkJ r A).card ≤ A.card * (2 * r + 1) ^ d :=
  Finset.card_image_le.trans (card_ballNbhd_le r A)

theorem layer_walkJ_le (r : ℕ) (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)) :
    ∀ P ∈ walkJ r A, P.1 ≤ K := by
  intro P hP
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hP
  exact Nat.zero_le _

end Label

section Connected

open scoped Classical

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- A site lies in the patch of the cell of side `L^{m₁}` that contains it. -/
theorem mem_Pset_cell (x : Balaban.Localization.CTorus d L N₁ m₁ K) :
    x ∈ Pset m₁ ((0, cbase (L ^ (0 + m₁)) x) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ K) := by
  intro μ
  have hpos : 0 < L ^ (0 + m₁) := Nat.pos_of_ne_zero (NeZero.ne _)
  show (x μ).val / L ^ (0 + m₁) = ((cbase (L ^ (0 + m₁)) x) μ).val / L ^ (0 + m₁)
  rw [cbase_val, Nat.mul_div_cancel_left _ hpos]

omit [NeZero N₁] [NeZero L] in
theorem near_refl {n : ℕ} (x : Torus d n) : Near 1 1 x x :=
  ⟨0, fun μ => by simp, by funext μ; simp⟩

omit [NeZero N₁] [NeZero L] in
theorem near_of_nbr {n : ℕ} {u v : Torus d n} (h : Nbr u v) : Near 1 1 u v := by
  obtain ⟨μ, h | h⟩ := h
  · refine ⟨fun ν => if ν = μ then 1 else 0, fun ν => ?_, ?_⟩
    · by_cases hν : ν = μ <;> simp [hν]
    · rw [h]; funext ν
      by_cases hν : ν = μ
      · subst hν; simp
      · simp [hν]
  · refine ⟨fun ν => if ν = μ then -1 else 0, fun ν => ?_, ?_⟩
    · by_cases hν : ν = μ <;> simp [hν]
    · rw [h]; funext ν
      by_cases hν : ν = μ
      · subst hν; simp
      · simp [hν]

/-- **The parameter cubes of a connected set of sites are connected to the root.**  Let `A` be a
set of sites containing the site `x` of the root cube of `z`, such that each site of `A` is reached
from `x` inside `A` by steps of ℓ∞ length at most `r`.  Then the patches `walkJ r A` are connected
to the root cube by Moore adjacency. -/
theorem rootConnected_walkJ (m₀ : ℕ) {r : ℕ}
    (hn : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K) (z : RootIdx d L N₁ m₁ K)
    {A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)}
    {x : Balaban.Localization.CTorus d L N₁ m₁ K} (hxA : x ∈ A) (hxz : x ∈ rootSet m₀ z)
    (hA : ∀ a ∈ A, Relation.ReflTransGen (fun p q : Balaban.Localization.CTorus d L N₁ m₁ K =>
      p ∈ A ∧ q ∈ A ∧ InBox d r ((N₁ * L ^ m₁) * L ^ K) (q - p)) x a) :
    RootConnected m₀ z (walkJ r A) := by
  set T := ballNbhd r A with hT
  set RT := fun u v : Balaban.Localization.CTorus d L N₁ m₁ K => u ∈ T ∧ v ∈ T ∧ Nbr u v with hRT
  have hedge : ∀ p q, p ∈ A → InBox d r ((N₁ * L ^ m₁) * L ^ K) (q - p) →
      Relation.ReflTransGen RT p q := by
    intro p q hp hpq
    refine Relation.ReflTransGen.mono (fun a b ⟨ha, hb, hab⟩ => ?_) p q
      (ball_chain_at hn p q hpq)
    exact ⟨mem_ballNbhd.2 ⟨p, hp, ha⟩, mem_ballNbhd.2 ⟨p, hp, hb⟩, hab⟩
  have hxa : ∀ a, Relation.ReflTransGen (fun p q : Balaban.Localization.CTorus d L N₁ m₁ K =>
      p ∈ A ∧ q ∈ A ∧ InBox d r ((N₁ * L ^ m₁) * L ^ K) (q - p)) x a →
      Relation.ReflTransGen RT x a := by
    intro a h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact ih.trans (hedge _ _ hbc.1 hbc.2.2)
  have hxT : ∀ t ∈ T, Relation.ReflTransGen RT x t := by
    intro t ht
    obtain ⟨a, ha, hta⟩ := mem_ballNbhd.1 ht
    exact (hxa a (hA a ha)).trans (hedge a t ha hta)
  -- the nodes
  intro P hP
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hP
  set g : Balaban.Localization.CTorus d L N₁ m₁ K → Option (ℕ × Balaban.Localization.CTorus d L N₁ m₁ K) :=
    fun y => some (0, cbase (L ^ (0 + m₁)) y) with hg
  have hgJ : ∀ y ∈ T, JNode (walkJ r A) (g y) := fun y hy =>
    Or.inr ⟨_, Finset.mem_image_of_mem _ hy, rfl⟩
  have hstep : ∀ u v, RT u v → JNode (walkJ r A) (g u) ∧ JNode (walkJ r A) (g v) ∧
      MooreTouch (nodeSet m₀ z (g u)) (nodeSet m₀ z (g v)) := by
    rintro u v ⟨hu, hv, huv⟩
    exact ⟨hgJ u hu, hgJ v hv, u, mem_Pset_cell u, v, mem_Pset_cell v, near_of_nbr huv⟩
  have hfirst : (JNode (walkJ r A) none ∧ JNode (walkJ r A) (g x) ∧
      MooreTouch (nodeSet m₀ z none) (nodeSet m₀ z (g x))) :=
    ⟨Or.inl rfl, hgJ x (subset_ballNbhd hxA), x, hxz, x, mem_Pset_cell x, near_refl x⟩
  exact Relation.ReflTransGen.head hfirst
    (Relation.ReflTransGen.lift g (fun u v h => hstep u v h) _ _ (hxT y hy))

/-- **The hull of a connected set of sites is a polymer.** -/
theorem isPolyDom_walkHull {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {r : ℕ}
    (hn : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K) (z : RootIdx d L N₁ m₁ K)
    {A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)}
    {x : Balaban.Localization.CTorus d L N₁ m₁ K} (hxA : x ∈ A) (hxz : x ∈ rootSet m₀ z)
    (hA : ∀ a ∈ A, Relation.ReflTransGen (fun p q : Balaban.Localization.CTorus d L N₁ m₁ K =>
      p ∈ A ∧ q ∈ A ∧ InBox d r ((N₁ * L ^ m₁) * L ^ K) (q - p)) x a) :
    Balaban.SmallField.Def6.IsPolyDom m₀ K (sitesOf (hullOf m₀ z (walkJ r A))) :=
  isPolyDom_hullOf hN hL z (walkJ r A) (layer_walkJ_le r A)
    (rootConnected_walkJ m₀ hn z hxA hxz hA)

/-- **The size of the hull of a connected set of sites**: at most
`2 d L (2r+1)^d` times the number of sites, by `dExt_hullOf_le`. -/
theorem dExt_walkHull_le {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {r : ℕ}
    (hn : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K) (z : RootIdx d L N₁ m₁ K)
    {A : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)}
    {x : Balaban.Localization.CTorus d L N₁ m₁ K} (hxA : x ∈ A) (hxz : x ∈ rootSet m₀ z)
    (hA : ∀ a ∈ A, Relation.ReflTransGen (fun p q : Balaban.Localization.CTorus d L N₁ m₁ K =>
      p ∈ A ∧ q ∈ A ∧ InBox d r ((N₁ * L ^ m₁) * L ^ K) (q - p)) x a) :
    dExt (hullOf m₀ z (walkJ r A)) ≤ (2 * d * L * (2 * r + 1) ^ d : ℝ) * A.card := by
  have h := dExt_hullOf_le hN hL z (walkJ r A) (layer_walkJ_le r A)
    (rootConnected_walkJ m₀ hn z hxA hxz hA)
  have hc : ((walkJ r A).card : ℝ) ≤ (A.card : ℝ) * (2 * r + 1) ^ d := by
    exact_mod_cast card_walkJ_le r A
  have h0 : (0 : ℝ) ≤ 2 * d * L := by positivity
  calc dExt (hullOf m₀ z (walkJ r A)) ≤ (2 * d * L : ℝ) * (walkJ r A).card + 0 := h
    _ ≤ (2 * d * L : ℝ) * ((A.card : ℝ) * (2 * r + 1) ^ d) := by
        rw [add_zero]; exact mul_le_mul_of_nonneg_left hc h0
    _ = (2 * d * L * (2 * r + 1) ^ d : ℝ) * A.card := by ring

end Connected



end Balaban.LargeField.Base
