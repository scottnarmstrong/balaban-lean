/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Lattice.Blocks
public import Balaban.Green.BallSums
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Generating sets and layers (GREEN.md §1.2)

A *generating set* on the fine torus `Torus d (N₀ * L ^ k)` is a decreasing family
`Ω₁ ⊇ Ω₂ ⊇ … ⊇ Ω_k`, `Ω_{k+1} = ∅`, of finite sets of sites, each `Ω_j` a union of `j`-blocks
(blocks of side `L ^ j`, `Balaban.blockMap`), with the separation condition (S):
`dist(Ω_jᶜ, Ω_{j+1}) > ϱ L ^ j` (`ℓ¹` torus distance `Balaban.Green.torusDist`).

Dictionary to the `η`-units of GREEN.md. We work on the fine torus with *unit lattice spacing*
(`η = 1`), the fine torus having side `ℓ = N₀ L ^ k`. Thus `ℓ_j = L ^ j η` of GREEN.md is `L ^ j`
here, `ℓ(x) = L ^ j` on layer `j`, GREEN.md's `ℓ_j⁻¹ dist` is `L⁻ʲ dist`, and (S) reads
`dist(Ω_jᶜ, Ω_{j+1}) > ϱ L ^ j` with `ϱ = R M`. The mass of GREEN.md (unit-scale units, `ℓ_k = 1`)
is `ν`; the mass in the present fine units is `ν L⁻²ᵏ`. Index conventions: `Ω : ℕ → Finset _` is
used only at the indices `1 ≤ j ≤ k + 1`.

Main definitions:
* `Balaban.Multiscale.GeneratingSet`: the structure;
* `Balaban.Multiscale.GeneratingSet.layer`: `Ω_j ∖ Ω_{j+1}`, the layer-`j` region;
* `Balaban.Multiscale.GeneratingSet.layerIndex`, `spacing`: the multiscale spacing `ℓ(x) = L ^ j` on
  layer `j` (value `1` off `Ω₁`, where the source does not define it).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset

variable {d L N₀ k : ℕ}

/-- `ℓ = N₀ L ^ k = L ^ j * (N₀ L ^ (k - j))` for `j ≤ k`: the `j`-blocks tile the fine torus. -/
theorem side_eq {j : ℕ} (h : j ≤ k) : N₀ * L ^ k = L ^ j * (N₀ * L ^ (k - j)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

/-- The `j`-block map of the fine torus `Torus d (N₀ * L ^ k)`: blocks of side `L ^ j`. -/
def jBlock (d L N₀ k j : ℕ) (x : Torus d (N₀ * L ^ k)) : Torus d (N₀ * L ^ (k - j)) :=
  blockMap (L ^ j) (N₀ * L ^ (k - j)) x

/-- A set of sites is a union of `j`-blocks. -/
def IsBlockUnion (L N₀ k j : ℕ) (S : Finset (Torus d (N₀ * L ^ k))) : Prop :=
  ∀ x x' : Torus d (N₀ * L ^ k), jBlock d L N₀ k j x = jBlock d L N₀ k j x' → (x ∈ S ↔ x' ∈ S)

/-- A **generating set** (GREEN.md §1.2) with separation constant `ϱ`. -/
structure GeneratingSet (d L N₀ k : ℕ) [NeZero N₀] [NeZero L] (ϱ : ℝ) where
  /-- The domains `Ω_j`, used for `1 ≤ j ≤ k + 1`. -/
  Ω : ℕ → Finset (Torus d (N₀ * L ^ k))
  /-- `Ω_{k+1} = ∅`. -/
  top : Ω (k + 1) = ∅
  /-- The family is decreasing. -/
  subset : ∀ j, 1 ≤ j → j ≤ k → Ω (j + 1) ⊆ Ω j
  /-- Each `Ω_j` is a union of `j`-blocks. -/
  blockUnion : ∀ j, 1 ≤ j → j ≤ k → IsBlockUnion L N₀ k j (Ω j)
  /-- Separation (S): `dist(Ω_jᶜ, Ω_{j+1}) > ϱ L ^ j` for `1 ≤ j < k`. -/
  separation : ∀ j, 1 ≤ j → j < k → ∀ x, x ∉ Ω j → ∀ y ∈ Ω (j + 1),
    ϱ * (L : ℝ) ^ j < Green.torusDist d (N₀ * L ^ k) x y

namespace GeneratingSet

variable [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

/-- The layer-`j` region `Ω_j ∖ Ω_{j+1}` (a disjoint union of `j`-blocks). -/
def layer (j : ℕ) : Finset (Torus d (N₀ * L ^ k)) := G.Ω j \ G.Ω (j + 1)

theorem mem_layer {j : ℕ} {x : Torus d (N₀ * L ^ k)} :
    x ∈ G.layer j ↔ x ∈ G.Ω j ∧ x ∉ G.Ω (j + 1) := by
  simp [layer]

/-- The family is decreasing: `Ω_j ⊆ Ω_i` for `1 ≤ i ≤ j ≤ k + 1`. -/
theorem Ω_antitone {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ k + 1) : G.Ω j ⊆ G.Ω i := by
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j hij ih => exact (G.subset j (hi.trans hij) (by omega)).trans (ih (by omega))

theorem layer_subset {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) : G.layer j ⊆ G.Ω 1 := by
  intro x hx
  exact G.Ω_antitone le_rfl hj1 (by omega) (G.mem_layer.1 hx).1

/-- Distinct layers are disjoint. -/
theorem layer_disjoint {j j' : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (hj' : 1 ≤ j') (hj'k : j' ≤ k)
    (hne : j ≠ j') {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) : x ∉ G.layer j' := by
  intro hx'
  rw [mem_layer] at hx hx'
  rcases lt_or_gt_of_ne hne with h | h
  · exact hx.2 (G.Ω_antitone (by omega) (by omega) (by omega) hx'.1)
  · exact hx'.2 (G.Ω_antitone (by omega) (by omega) (by omega) hx.1)

/-- Every site of `Ω₁` lies in some layer `j`, `1 ≤ j ≤ k`. -/
theorem exists_layer {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ G.layer j := by
  classical
  have hex : ∃ n, x ∉ G.Ω (n + 1) := ⟨k, by simp [G.top]⟩
  set n := Nat.find hex with hn
  have hnk : n ≤ k := Nat.find_min' hex (by simp [G.top])
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    have := Nat.find_spec hex
    rw [← hn, h0] at this
    exact this hx
  refine ⟨n, hn1, hnk, G.mem_layer.2 ⟨?_, Nat.find_spec hex⟩⟩
  have := Nat.find_min hex (m := n - 1) (by omega)
  have e : n - 1 + 1 = n := by omega
  rw [e] at this
  simpa using this

/-- The index `j` of the layer containing `x` (`0` if `x ∉ Ω₁`). -/
noncomputable def layerIndex (x : Torus d (N₀ * L ^ k)) : ℕ := by
  classical
  exact if h : ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ G.layer j then Classical.choose h else 0

theorem layerIndex_eq {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) : G.layerIndex x = j := by
  classical
  have h : ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ G.layer j := ⟨j, hj, hjk, hx⟩
  unfold layerIndex
  simp only [h, ↓reduceDIte]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  by_contra hne
  exact G.layer_disjoint h1 h2 hj hjk hne h3 hx

/-- For `x ∈ Ω₁` the layer index lies in `[1, k]` and `x` lies in that layer. -/
theorem layerIndex_spec {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    1 ≤ G.layerIndex x ∧ G.layerIndex x ≤ k ∧ x ∈ G.layer (G.layerIndex x) := by
  obtain ⟨j, hj, hjk, hxj⟩ := G.exists_layer hx
  rw [G.layerIndex_eq hj hjk hxj]
  exact ⟨hj, hjk, hxj⟩

/-- The multiscale spacing `ℓ(x) = L ^ j` for `x` in layer `j` (unit fine spacing). -/
noncomputable def spacing (x : Torus d (N₀ * L ^ k)) : ℝ := (L : ℝ) ^ G.layerIndex x

theorem spacing_eq {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) : G.spacing x = (L : ℝ) ^ j := by
  rw [spacing, G.layerIndex_eq hj hjk hx]

end GeneratingSet

end Balaban.Multiscale
