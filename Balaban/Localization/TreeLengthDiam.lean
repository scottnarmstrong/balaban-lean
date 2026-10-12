/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
public import Balaban.LargeField.Geometry.Distance
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The covering size is at least the distance divided by the cell side

For a set `X` on the fine torus with a chosen family of aligned boxes of side `L a_j`
(`a_j = L ^ (j + m₀ + m₁)`) and a connected structure `(W, E)` inside `X` meeting every chosen
box, two points `y, x ∈ X` satisfy `d(y, x) ≤ |E| + 2 (L a_j - 1)` in the index distance
`supDist` of the cube-torus file.  Each bond costs `1 / a_j`, hence
`treeLenCovOne m₀ j X ≥ d(y, x) / a_j - 2 L`.

This file proves geometry only.  The coefficient bounds and the regional estimate that use
this inequality are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.LargeField Finset

section Walk

variable {d n : ℕ} [NeZero n]

theorem cycNorm_single_le (μ i : Fin d) :
    cycNorm n ((Pi.single μ (1 : ZMod n) : Fin d → ZMod n) i) ≤ 1 := by
  by_cases hi : i = μ
  · subst hi
    rw [Pi.single_eq_same]
    exact (cycNorm_le_iff (1 : ZMod n) 1).2 ⟨1, by simp, by simp⟩
  · rw [Pi.single_eq_of_ne hi, (cycNorm_zero_iff (0 : ZMod n)).2 rfl]
    exact zero_le_one

theorem supDist_le_one_of_nbr {x y : Torus d n} (h : Nbr x y) : supDist x y ≤ 1 := by
  rw [supDist_le_iff]
  intro i
  obtain ⟨μ, h | h⟩ := h
  · subst h
    have : x i - (x + (Pi.single μ 1 : Fin d → ZMod n)) i = -((Pi.single μ (1 : ZMod n) : Fin d → ZMod n) i) := by
      simp
    rw [this, cycNorm_neg]
    exact cycNorm_single_le μ i
  · subst h
    have : (y + (Pi.single μ 1 : Fin d → ZMod n)) i - y i = ((Pi.single μ (1 : ZMod n) : Fin d → ZMod n) i) := by
      simp
    rw [this]
    exact cycNorm_single_le μ i

/-- Points joined by a chain of bonds of `E` (each a nearest-neighbour pair) are at distance at
most `|E|`: a shortest chain uses each bond at most once. -/
theorem supDist_le_card_of_reach {E : Finset (Torus d n × Torus d n)}
    (hE : ∀ p ∈ E, Nbr p.1 p.2) {x y : Torus d n}
    (h : Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x y) :
    supDist x y ≤ E.card := by
  classical
  let G : SimpleGraph (Torus d n) := SimpleGraph.fromRel (fun a b => (a, b) ∈ E)
  have hr : G.Reachable x y := by
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ hbc ih =>
      refine ih.trans ?_
      by_cases hbc' : b = c
      · subst hbc'; exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hbc', hbc⟩)
  obtain ⟨p, hp⟩ := hr.exists_isPath
  have hlen : ∀ {u v : Torus d n} (q : G.Walk u v), supDist u v ≤ q.length := by
    intro u v q
    induction q with
    | nil => simp [supDist_self]
    | cons hadj q ih =>
      rename_i a b c
      have h1 : supDist a b ≤ 1 := by
        rw [SimpleGraph.fromRel_adj] at hadj
        rcases hadj.2 with h | h
        · exact supDist_le_one_of_nbr (hE _ h)
        · rw [supDist_comm]; exact supDist_le_one_of_nbr (hE _ h)
      calc supDist a c ≤ supDist a b + supDist b c := supDist_triangle _ _ _
        _ ≤ 1 + (SimpleGraph.Walk.length _) := add_le_add h1 ih
        _ = _ := by simp [SimpleGraph.Walk.length_cons, add_comm]
  refine (hlen p).trans ?_
  have hnd : p.edges.Nodup := hp.isTrail.edges_nodup
  have hsub : p.edges.toFinset ⊆ E.image (fun q => s(q.1, q.2)) := by
    intro e he
    have he' : e ∈ G.edgeSet := p.edges_subset_edgeSet (List.mem_toFinset.1 he)
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at he'
      rcases he'.2 with h | h
      · exact Finset.mem_image.2 ⟨(a, b), h, rfl⟩
      · exact Finset.mem_image.2 ⟨(b, a), h, Sym2.eq_swap⟩
  calc p.length = p.edges.length := (SimpleGraph.Walk.length_edges p).symm
    _ = p.edges.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (E.image (fun q => s(q.1, q.2))).card := Finset.card_le_card hsub
    _ ≤ E.card := Finset.card_image_le

end Walk

section Cov

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (m₀ j : ℕ)

/-- Two points of one aligned box of side `s` are at distance at most `s - 1`. -/
theorem supDist_le_of_mem_box {n : ℕ} [NeZero n] {b z z' : Torus d n} {s : ℕ}
    (hz : z ∈ box b s) (hz' : z' ∈ box b s) : supDist z z' ≤ s - 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨w', hw', rfl⟩ := hz'
  rw [supDist_le_iff]
  intro i
  rw [cycNorm_le_iff]
  refine ⟨(w i : ℤ) - w' i, ?_, by simp⟩
  have h1 := hw i
  have h2 := hw' i
  rw [abs_le]
  constructor <;> omega

/-- **Distance bound for an admissible structure.**  If `y, x ∈ X`, `𝒦` is a chosen family of
`X` at scale `j` and `(W, E)` is a connected structure meeting every chosen box, then
`supDist y x ≤ |E| + 2 (L a_j - 1)`, `a_j = L ^ (j + m₀ + m₁)`. -/
theorem supDist_le_card_add {X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hch : ChosenOne m₀ j X 𝒦) (hc : ConnStruct W E) (hmeet : MeetsOne m₀ j 𝒦 W)
    {y x : CTorus d L N₁ m₁ K} (hy : y ∈ X) (hx : x ∈ X) :
    supDist y x ≤ E.card + 2 * (L * cellSide L m₀ m₁ j - 1) := by
  obtain ⟨b, hb, hyb⟩ := hch.2 y hy
  obtain ⟨b', hb', hxb⟩ := hch.2 x hx
  obtain ⟨wy, hwy, hwyb⟩ := hmeet b hb
  obtain ⟨wx, hwx, hwxb⟩ := hmeet b' hb'
  have h1 := supDist_le_of_mem_box hyb hwyb
  have h2 := supDist_le_of_mem_box hxb hwxb
  have h3 : supDist wy wx ≤ E.card :=
    supDist_le_card_of_reach (fun p hp => (hc.2.1 p hp).2.2) (hc.2.2 wy hwy wx hwx)
  calc supDist y x ≤ supDist y wy + supDist wy x := supDist_triangle _ _ _
    _ ≤ supDist y wy + (supDist wy wx + supDist wx x) :=
        Nat.add_le_add_left (supDist_triangle _ _ _) _
    _ ≤ (L * cellSide L m₀ m₁ j - 1) + (E.card + (L * cellSide L m₀ m₁ j - 1)) := by
        rw [supDist_comm wx x]
        exact Nat.add_le_add h1 (Nat.add_le_add h3 h2)
    _ = _ := by ring

/-- **Size at least diameter** (T1).  If the admissible set defining `treeLenCovOne m₀ j X` is
nonempty (it is for every polymer of `𝒟_j`), then for all `y, x ∈ X`
`supDist y x / a_j - 2 L ≤ treeLenCovOne m₀ j X`, `a_j = L ^ (j + m₀ + m₁)`. -/
theorem treeLenCovOne_ge_dist {X : Set (CTorus d L N₁ m₁ K)}
    (hX : ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W)
    {y x : CTorus d L N₁ m₁ K} (hy : y ∈ X) (hx : x ∈ X) :
    (supDist y x : ℝ) / (L : ℝ) ^ (j + m₀ + m₁) - 2 * L ≤ treeLenCovOne m₀ j X := by
  obtain ⟨𝒦, W, E, hch, hc, -, hmeet, hcost⟩ := treeLenCovOne_attained m₀ j X hX
  rw [← hcost]
  have hd := supDist_le_card_add m₀ j hch hc hmeet hy hx
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hpos : (0 : ℝ) < (L : ℝ) ^ (j + m₀ + m₁) := by positivity
  have hcs : ((cellSide L m₀ m₁ j : ℕ) : ℝ) = (L : ℝ) ^ (j + m₀ + m₁) := by
    unfold cellSide; push_cast; rfl
  have hs : 1 ≤ L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
  have hd' : (supDist y x : ℝ) ≤ E.card + 2 * (L * (L : ℝ) ^ (j + m₀ + m₁)) := by
    have : ((supDist y x : ℕ) : ℝ) ≤ ((E.card + 2 * (L * cellSide L m₀ m₁ j - 1) : ℕ) : ℝ) := by
      exact_mod_cast hd
    have e : ((L * cellSide L m₀ m₁ j - 1 : ℕ) : ℝ) ≤ L * (L : ℝ) ^ (j + m₀ + m₁) := by
      rw [Nat.cast_sub hs]; push_cast; rw [hcs]; linarith
    push_cast [Nat.cast_sub hs] at this ⊢
    rw [hcs] at this
    linarith
  have hcost' : bondCost (scaleW L m₀ m₁ j) E = E.card * ((L : ℝ) ^ (j + m₀ + m₁))⁻¹ := by
    unfold bondCost scaleW
    rw [Finset.sum_const, nsmul_eq_mul, show m₀ + m₁ + j = j + m₀ + m₁ by ring]
  rw [hcost', div_sub' (by positivity), div_le_iff₀ hpos]
  have : (E.card : ℝ) * ((L : ℝ) ^ (j + m₀ + m₁))⁻¹ * (L : ℝ) ^ (j + m₀ + m₁) = E.card := by
    field_simp
  nlinarith [this]

end Cov

end Balaban.Localization
