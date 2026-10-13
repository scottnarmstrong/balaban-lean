/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModUnion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Unions along an active-overlap tree

The landed `G3_dcov` bounds the modular covering size of a union of two labels whose intersection
contains a full cell of `Ω`:
`D(X₁ ∪ X₂) ≤ D(X₁) + D(X₂) + 2dL`.  This file folds it over a finite family of labels
`X₀, …, X_n` in which every `X_i`, `i ≥ 1`, has an *active* overlap (a full cell of `Ω`) with some
earlier `X_m`, `m < i` (an enumeration of a tree of active overlaps, or of any connected overlap
graph):

* `dcovMod_union_range_le`: `⋃_{i ≤ n} X_i` is in `𝒟_j(mod Ω^c)` and
  `D(⋃ X_i) ≤ Σ_i D(X_i) + 2dL · n`;
* `dcovMod_biUnion_le_of_activeTree`: the same for a finite family indexed by a finite type with a
  connected graph of active overlaps (`2dL` per vertex minus one).

Overlap only inside a retained hole is *not* enough (`notes/phase1/VMOD-41.md` §2).  These are
counting lemmas on the cover size; nothing about the gas estimate is proved here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- **Fold of `G3_dcov` along an enumerated active-overlap tree.** -/
theorem dcovMod_union_range_le {Ω : Set (CTorus d L N₁ m₁ K)} (X : ℕ → Set (CTorus d L N₁ m₁ K))
    (hX : ∀ i, DjMod m₀ j Ω (X i)) (n : ℕ)
    (hov : ∀ i, 1 ≤ i → i ≤ n → ∃ m, m < i ∧ ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
      box t (cellSide L m₀ m₁ j) ⊆ X i ∩ X m ∩ Ω) :
    DjMod m₀ j Ω (⋃ i ∈ Finset.range (n + 1), X i) ∧
      dcovMod m₀ j Ω (⋃ i ∈ Finset.range (n + 1), X i) ≤
        ∑ i ∈ Finset.range (n + 1), dcovMod m₀ j Ω (X i) + cG d L * n := by
  induction n with
  | zero => simpa using hX 0
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi hin => hov i hi (by omega))
    obtain ⟨m, hm, t, ht, hbox⟩ := hov (n + 1) (by omega) le_rfl
    have hmem : X m ⊆ ⋃ i ∈ Finset.range (n + 1), X i := fun x hx =>
      Set.mem_biUnion (Finset.mem_range.2 (by omega)) hx
    have hcube : ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
        box t (cellSide L m₀ m₁ j) ⊆ (⋃ i ∈ Finset.range (n + 1), X i) ∩ X (n + 1) ∩ Ω :=
      ⟨t, ht, fun x hx => ⟨⟨hmem (hbox hx).1.2, (hbox hx).1.1⟩, (hbox hx).2⟩⟩
    obtain ⟨h1, h2⟩ := G3_dcov ih1 (hX (n + 1)) hcube
    have hu : (⋃ i ∈ Finset.range (n + 1 + 1), X i) =
        (⋃ i ∈ Finset.range (n + 1), X i) ∪ X (n + 1) := by
      rw [Finset.range_add_one (n := n + 1), Finset.set_biUnion_insert]
      rw [Set.union_comm]
    rw [hu, Finset.sum_range_succ]
    refine ⟨h1, ?_⟩
    push_cast
    linarith

/-- In a connected graph every vertex other than the root has a neighbour strictly closer to it. -/
theorem exists_adj_dist_lt {ι : Type*} {G : SimpleGraph ι} (hG : G.Connected) {i r : ι}
    (h : i ≠ r) : ∃ w, G.Adj i w ∧ G.dist w r < G.dist i r := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i r
  cases p with
  | nil => exact absurd rfl h
  | cons hadj q =>
    refine ⟨_, hadj, ?_⟩
    have := SimpleGraph.dist_le q
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- **Union along an active-overlap tree (indexed form).**  A finite non-empty family
`(X_i)_{i ∈ ι}` of labels in `𝒟_j(mod Ω^c)`, with a connected graph `G` on `ι` such that every
edge `{i, i'}` has a full cell of `Ω` in `X_i ∩ X_{i'}`, has union in `𝒟_j(mod Ω^c)` and
`D(⋃ X_i) ≤ Σ_i D(X_i) + 2dL (|ι| - 1)`. -/
theorem dcovMod_biUnion_le_of_activeTree {ι : Type*} [Fintype ι] [Nonempty ι]
    {Ω : Set (CTorus d L N₁ m₁ K)} (X : ι → Set (CTorus d L N₁ m₁ K))
    (hX : ∀ i, DjMod m₀ j Ω (X i)) (G : SimpleGraph ι) (hG : G.Connected)
    (hov : ∀ i i', G.Adj i i' → ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
      box t (cellSide L m₀ m₁ j) ⊆ X i ∩ X i' ∩ Ω) :
    DjMod m₀ j Ω (⋃ i, X i) ∧
      dcovMod m₀ j Ω (⋃ i, X i) ≤
        ∑ i, dcovMod m₀ j Ω (X i) + cG d L * ((Fintype.card ι : ℝ) - 1) := by
  classical
  obtain ⟨r⟩ := ‹Nonempty ι›
  set N := Fintype.card ι with hNdef
  have hN : 0 < N := Fintype.card_pos
  set e : ι ≃ Fin N := Fintype.equivFin ι with he
  set f : Fin N → ℕ := fun a => G.dist (e.symm a) r with hf
  set σ := Tuple.sort f with hσ
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  -- the enumeration
  let v : ℕ → ι := fun m => if h : m < N then e.symm (σ ⟨m, h⟩) else r
  have hv : ∀ m (h : m < N), v m = e.symm (σ ⟨m, h⟩) := fun m h => by simp [v, h]
  -- the position of a vertex
  have hpos : ∀ i : ι, ∃ m, ∃ h : m < N, v m = i := by
    intro i
    refine ⟨(σ.symm (e i)).val, (σ.symm (e i)).isLt, ?_⟩
    rw [hv _ (σ.symm (e i)).isLt]; simp
  have hdist_v : ∀ m (h : m < N), G.dist (v m) r = (f ∘ σ) ⟨m, h⟩ := fun m h => by
    rw [hv m h]; rfl
  have hv0 : v 0 = r := by
    have h0 : (f ∘ σ) ⟨0, hN⟩ = 0 := by
      obtain ⟨a, ha⟩ := σ.surjective (e r)
      have : f (e r) = 0 := by simp [hf]
      have hle := hmono (Fin.zero_le a)
      have : (f ∘ σ) ⟨0, hN⟩ ≤ f (e r) := by
        rw [← ha] at *; simpa [Function.comp] using hle
      omega
    rw [← hG.dist_eq_zero_iff, hdist_v 0 hN, h0]
  have hY : ∀ m, DjMod m₀ j Ω (X (v m)) := fun m => hX _
  have hovv : ∀ i, 1 ≤ i → i ≤ N - 1 → ∃ m, m < i ∧ ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧
      box t (cellSide L m₀ m₁ j) ⊆ X (v i) ∩ X (v m) ∩ Ω := by
    intro i hi hiN
    have hiN' : i < N := by omega
    have hne : v i ≠ r := by
      intro h
      have h1 : v i = v 0 := h.trans hv0.symm
      rw [hv i hiN', hv 0 hN] at h1
      have := σ.injective (e.symm.injective h1)
      have := congrArg Fin.val this
      simp at this; omega
    obtain ⟨w, hadj, hlt⟩ := exists_adj_dist_lt hG hne
    obtain ⟨m, hm, hmw⟩ := hpos w
    refine ⟨m, ?_, hov _ _ (hmw ▸ hadj)⟩
    by_contra hge
    push Not at hge
    have := hmono (show (⟨i, hiN'⟩ : Fin N) ≤ ⟨m, hm⟩ from hge)
    rw [← hdist_v i hiN', ← hdist_v m hm, hmw] at this
    omega
  obtain ⟨h1, h2⟩ := dcovMod_union_range_le (fun m => X (v m)) hY (N - 1) hovv
  have hU : (⋃ i ∈ Finset.range (N - 1 + 1), X (v i)) = ⋃ i, X i := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨m, -, hx⟩; exact ⟨_, hx⟩
    · rintro ⟨i, hx⟩
      obtain ⟨m, hm, rfl⟩ := hpos i
      exact ⟨m, by omega, hx⟩
  have hS : ∀ g : ι → ℝ, ∑ m ∈ Finset.range (N - 1 + 1), g (v m) = ∑ i, g i := by
    intro g
    rw [Nat.sub_add_cancel hN, ← Fin.sum_univ_eq_sum_range (fun m => g (v m)) N]
    calc ∑ a : Fin N, g (v a) = ∑ a : Fin N, g (e.symm (σ a)) :=
          Finset.sum_congr rfl fun a _ => by rw [hv a a.isLt]
      _ = ∑ a : Fin N, g (e.symm a) := Equiv.sum_comp σ (fun a => g (e.symm a))
      _ = ∑ i, g i := Equiv.sum_comp e.symm g
  rw [hU] at h1 h2
  refine ⟨h1, ?_⟩
  rw [hS (fun i => dcovMod m₀ j Ω (X i))] at h2
  have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hN]; simp
  rw [this] at h2
  exact h2

end Balaban.Fluctuation
