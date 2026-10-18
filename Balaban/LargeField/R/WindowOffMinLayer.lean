/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.MinimalGenSet
public import Balaban.LargeField.R.ChiBridgeHist
public import Balaban.LargeField.R.PsiZeroWindowGeom
public import Balaban.Fluctuation.LocalPairDepth
public import Balaban.LargeField.Background.Factorization

/-!
# Minimal generating sets on two presentations of one torus; layers and interface pairs

Bookkeeping for the comparison of the window datum with the data of the pieces (P7 (2.14)):

* `minLayer_torusCast`: the layers `Ω_n(X)` of P3's minimal generating set (Definition II.2.2) do
  not depend on the presentation `M₁ N₁ L^q` of the side of the fine torus: for
  `M₁ N₁ L^q = M₁ N₁' L^{q'}` and `j ≤ q, q'` the layers correspond through the identification of
  the tori;
* `layerIndex_eq_of_Ω_iff`: two sites with the same membership in all layers `Ω_q`, `q ≥ 1`, of two
  generating sets (the second of level at most the first) have the same layer index;
* `interfacePair_supDist_le`: the two sites of an interface pair of (R1) are within
  `2 L^ℓ + 1` of each other, `ℓ` the layer index of the first.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Cast

variable {d : ℕ}

theorem winOff_blockMap_torusCast {a b : ℕ} (h : a = b) (P m : ℕ) (x : Torus d a) :
    blockMap P m (torusCast h x) = blockMap P m x := by
  subst h; rfl

theorem winOff_torusCast_trans {a b c : ℕ} (h : a = b) (h' : b = c) (x : Torus d a) :
    torusCast h' (torusCast h x) = torusCast (h.trans h') x := by
  subst h; subst h'; rfl

end Cast

section MinLayer

variable {d M1 N₁ N₁' L q q' : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero N₁']

/-- The cube sides agree: `N₁ L^{q-n} = N₁' L^{q'-n}`. -/
theorem cubeSide_eq_of_fine_eq (h : M1 * N₁ * L ^ q = M1 * N₁' * L ^ q') {n : ℕ} (hn : n ≤ q)
    (hn' : n ≤ q') : N₁ * L ^ (q - n) = N₁' * L ^ (q' - n) := by
  have h1 := (fine_eq_cube (M1 := M1) (N₁ := N₁) (L := L) hn).symm.trans
    (h.trans (fine_eq_cube (M1 := M1) (N₁ := N₁') (L := L) hn'))
  have hpos : 0 < L ^ n * M1 := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  exact Nat.eq_of_mul_eq_mul_left hpos h1

/-- The `𝒞_n`-cube index is carried by the identification of the tori. -/
theorem fineCubeIdx_torusCast (h : M1 * N₁ * L ^ q = M1 * N₁' * L ^ q') {n : ℕ} (hn : n ≤ q)
    (hn' : n ≤ q') (x : Torus d (M1 * N₁ * L ^ q)) :
    fineCubeIdx M1 N₁' L q' n (torusCast h x) =
      torusCast (cubeSide_eq_of_fine_eq h hn hn') (fineCubeIdx M1 N₁ L q n x) := by
  unfold fineCubeIdx
  rw [winOff_blockMap_torusCast, torusCast_blockMap_right]

theorem minLayerAux_torusCast (h : M1 * N₁ * L ^ q = M1 * N₁' * L ^ q') {j : ℕ} (hj : j ≤ q)
    (hj' : j ≤ q') {X : Finset (Torus d (M1 * N₁ * L ^ q))}
    {X' : Finset (Torus d (M1 * N₁' * L ^ q'))} (hX : ∀ x, x ∈ X ↔ torusCast h x ∈ X') :
    ∀ (t : ℕ) (x : Torus d (M1 * N₁ * L ^ q)),
      x ∈ minLayerAux M1 N₁ L q j X t ↔ torusCast h x ∈ minLayerAux M1 N₁' L q' j X' t := by
  intro t
  induction t with
  | zero =>
    intro x
    simp only [minLayerAux]
    rw [mem_cubeInterior, mem_cubeInterior]
    constructor
    · intro hx y' hy'
      have e1 : torusCast h (torusCast h.symm y') = y' := torusCast_cast_symm h y'
      rw [← e1] at hy' ⊢
      rw [fineCubeIdx_torusCast h hj hj', fineCubeIdx_torusCast h hj hj'] at hy'
      exact (hX _).1 (hx _ (torusCast_injective _ hy'))
    · intro hx y hy
      refine (hX y).2 (hx _ ?_)
      rw [fineCubeIdx_torusCast h hj hj', fineCubeIdx_torusCast h hj hj', hy]
  | succ t ih =>
    intro x
    simp only [minLayerAux]
    have hn : j - (t + 1) ≤ q := by omega
    have hn' : j - (t + 1) ≤ q' := by omega
    rw [mem_nearStep, mem_nearStep]
    constructor
    · rintro ⟨y, hy, hd⟩
      refine ⟨torusCast h y, (ih y).1 hy, ?_⟩
      rw [fineCubeIdx_torusCast h hn hn', fineCubeIdx_torusCast h hn hn', supDist_torusCast_eq]
      exact hd
    · rintro ⟨y', hy', hd⟩
      have e1 : torusCast h (torusCast h.symm y') = y' := torusCast_cast_symm h y'
      rw [← e1] at hy' hd
      refine ⟨_, (ih _).2 hy', ?_⟩
      rw [fineCubeIdx_torusCast h hn hn', fineCubeIdx_torusCast h hn hn', supDist_torusCast_eq]
        at hd
      exact hd

/-- **Minimal generating sets on two presentations of one torus**: for
`M₁ N₁ L^q = M₁ N₁' L^{q'}`, `j ≤ q, q'` and sets corresponding through the identification of the
tori, the layers `Ω_n(X)` correspond. -/
theorem minLayer_torusCast (h : M1 * N₁ * L ^ q = M1 * N₁' * L ^ q') {j : ℕ} (hj : j ≤ q)
    (hj' : j ≤ q') {X : Finset (Torus d (M1 * N₁ * L ^ q))}
    {X' : Finset (Torus d (M1 * N₁' * L ^ q'))} (hX : ∀ x, x ∈ X ↔ torusCast h x ∈ X') (n : ℕ)
    (x : Torus d (M1 * N₁ * L ^ q)) :
    x ∈ minLayer M1 N₁ L q j X n ↔ torusCast h x ∈ minLayer M1 N₁' L q' j X' n := by
  unfold minLayer
  split_ifs with hn
  · exact minLayerAux_torusCast h hj hj' hX _ x
  · simp

end MinLayer

section Layers

variable {d L N₀ k N₀' k' : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ ϱ' : ℝ}

/-- **Equal layer indices from equal layers**: if `x` and `x'` lie in the same layers `Ω_q`,
`q ≥ 1`, of `G` and `G'` (the level of `G'` at most that of `G`), their layer indices agree. -/
theorem layerIndex_eq_of_Ω_iff (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀' k' ϱ')
    (hk : k' ≤ k) {x : Torus d (N₀ * L ^ k)} {x' : Torus d (N₀' * L ^ k')}
    (h : ∀ q, 1 ≤ q → (x ∈ G.Ω q ↔ x' ∈ G'.Ω q)) : G.layerIndex x = G'.layerIndex x' := by
  by_cases hx : x' ∈ G'.Ω 1
  · obtain ⟨h1, h2, h3⟩ := G'.layerIndex_spec hx
    rw [G'.mem_layer] at h3
    refine G.layerIndex_eq h1 (h2.trans hk) (G.mem_layer.2 ⟨(h _ h1).2 h3.1, fun h4 => h3.2 ?_⟩)
    exact (h _ (by omega)).1 h4
  · rw [layerIndex_of_not_mem G' hx, layerIndex_of_not_mem G (fun h1 => hx ((h 1 le_rfl).1 h1))]

/-- **The two sites of an interface pair are close**: within `2 L^ℓ + 1`, `ℓ` the layer index of
the first. -/
theorem interfacePair_supDist_le (G : GeneratingSet d L N₀ k ϱ) {x x' : Torus d (N₀ * L ^ k)}
    (hp : IsInterfacePair G x x') : supDist x x' ≤ 2 * L ^ G.layerIndex x + 1 := by
  classical
  obtain ⟨-, -, hl, z, hz, z', hz', hzz⟩ := hp
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hb : ∀ w u, u ∈ blockSet G w → supDist w u ≤ L ^ G.layerIndex w := by
    intro w u hu
    unfold blockSet at hu
    by_cases hw : w ∈ G.Ω 1
    · simp only [hw, ite_true] at hu
      exact Balaban.Localization.supDist_le_of_mem_blk (G.layerIndex_spec hw).2.1 hu
    · simp only [hw, ite_false, Finset.mem_singleton] at hu
      rw [hu, supDist_self]; exact Nat.zero_le _
  have h1 := hb x z hz
  have h2 := hb x' z' hz'
  have h3 := Adj.supDist_le_one hzz
  have h4 : L ^ G.layerIndex x' ≤ L ^ G.layerIndex x :=
    Nat.pow_le_pow_right hL (by rcases hl with h | h <;> omega)
  have t1 := supDist_triangle x z x'
  have t2 := supDist_triangle z z' x'
  rw [supDist_comm z' x'] at t2
  omega

end Layers

end Balaban.LargeField
