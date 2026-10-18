/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Composition
public import Balaban.Green.BlockDistance
public import Balaban.Multiscale.PathMetricBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A generating set restricted to a neighbourhood of a set of sites

For a generating set `G`, a set of sites `X` and radii `ρ_n` with
`ρ_{n+1} + (ϱ_B + d) L^n ≤ ρ_n`, the layers
`Ω^B_n = {x ∈ Ω_n : the n-block of x lies within ℓ¹-distance ρ_n of X}`
form a generating set `G_B` with separation `ϱ_B ≤ ϱ` (`exists_restrictGen`), and `G_B ≺ G`.
It is the sub-generating set through which two backgrounds of different generating sets are
compared on a ball (P2 §4, the composition with `𝔹_j ≺ 𝔹'_k`; P7 (2.14)).

* `restrictGen_layerIndex_eq`: at a site whose `G`-block is within `ρ_n` of `X` the two layer
  indices agree;
* `restrictGen_far_of_layer_ne`, `restrictGen_far_of_not_mem`: the sites where the layers differ
  and the sites of `Ω₁ ∖ Ω^B_1` are far from `X`;
* `pathDist_ge_torusDist`: the path metric dominates `L^{-k}` times the `ℓ¹` distance.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- Sites of one `n`-block (`n ≤ k`) are at `ℓ¹` distance at most `d L^n`. -/
theorem torusDist_le_of_mem_blk (G : GeneratingSet d L N₀ k ϱ) {n : ℕ} (hn : n ≤ k)
    {x y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.blk n x) :
    Green.torusDist d (N₀ * L ^ k) x y ≤ d * (L : ℝ) ^ n := by
  have h := GeneratingSet.mem_blk.1 hy
  unfold jBlock at h
  have := Green.torusDist_le_of_blockMap_eq (side_eq (N₀ := N₀) (L := L) (k := k) hn)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n) h.symm
  push_cast at this
  exact this

/-- **The restricted generating set.**  The sites of `Ω_n` whose `n`-block lies within `ℓ¹` distance
`ρ_n` of `X` form a generating set with separation `ϱ_B`, if `0 ≤ ϱ_B ≤ ϱ` and
`ρ_{n+1} + (ϱ_B + d) L^n ≤ ρ_n` for `1 ≤ n < k`. -/
theorem exists_restrictGen (G : GeneratingSet d L N₀ k ϱ) {ϱB : ℝ} (hϱB0 : 0 ≤ ϱB) (hϱB : ϱB ≤ ϱ)
    (X : Finset (Torus d (N₀ * L ^ k))) (ρ : ℕ → ℝ)
    (hρ : ∀ n, 1 ≤ n → n < k → ρ (n + 1) + (ϱB + d) * (L : ℝ) ^ n ≤ ρ n) :
    ∃ GB : GeneratingSet d L N₀ k ϱB, ∀ n x, x ∈ GB.Ω n ↔
      x ∈ G.Ω n ∧ ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n := by
  classical
  have hL0 : (0 : ℝ) ≤ L := by positivity
  refine ⟨{ Ω := fun n => (G.Ω n).filter fun x =>
              ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n
            top := ?_, subset := ?_, blockUnion := ?_, separation := ?_ }, fun n x => by simp⟩
  · ext x
    simp [G.top]
  · intro j hj1 hjk x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨G.subset j hj1 hjk hx.1, fun y hy => ?_⟩
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hy' : y ∈ G.blk (j + 1) x :=
        GeneratingSet.mem_blk.2 (GeneratingSet.jBlock_succ_eq (by omega) (GeneratingSet.mem_blk.1 hy))
      obtain ⟨z, hz, hdz⟩ := hx.2 y hy'
      refine ⟨z, hz, hdz.trans ?_⟩
      have h1 := hρ j hj1 hlt
      have h2 : 0 ≤ (ϱB + d) * (L : ℝ) ^ j := by positivity
      linarith
    · have hjk' : j = k := le_antisymm hjk hge
      subst hjk'
      have h1 := hx.1
      rw [G.top] at h1
      simp at h1
  · intro j hj1 hjk x x' hxx'
    simp only [Finset.mem_filter]
    have hb : G.blk j x = G.blk j x' := by
      ext y
      simp only [GeneratingSet.mem_blk, hxx']
    rw [G.blockUnion j hj1 hjk x x' hxx', hb]
  · intro j hj1 hjk x hx y hy
    simp only [Finset.mem_filter] at hx hy
    by_cases hxj : x ∈ G.Ω j
    · have hx' : ¬ ∀ y ∈ G.blk j x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ j :=
        fun h => hx ⟨hxj, h⟩
      push Not at hx'
      obtain ⟨y', hy', hfar⟩ := hx'
      obtain ⟨z, hz, hzy⟩ := hy.2 y (GeneratingSet.mem_blk.2 rfl)
      have h1 := hfar z hz
      have h2 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) z y y'
      have h3 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) y x y'
      have h4 := torusDist_le_of_mem_blk G hjk.le hy'
      have h5 := hρ j hj1 hjk
      rw [torusDist_comm' x y]
      linarith
    · have h1 := G.separation j hj1 hjk x hxj y hy.1
      have h2 : ϱB * (L : ℝ) ^ j ≤ ϱ * (L : ℝ) ^ j :=
        mul_le_mul_of_nonneg_right hϱB (by positivity)
      linarith

section Props

variable {G : GeneratingSet d L N₀ k ϱ} {ϱB : ℝ} {GB : GeneratingSet d L N₀ k ϱB}
  {X : Finset (Torus d (N₀ * L ^ k))} {ρ : ℕ → ℝ}

theorem restrictGen_precedes
    (hGB : ∀ n x, x ∈ GB.Ω n ↔
      x ∈ G.Ω n ∧ ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n) :
    Precedes GB G :=
  fun i _ _ x hx => ((hGB i x).1 hx).1

/-- At a site of `Ω₁` whose block (of its `G`-layer) lies within `ρ_n` of `X`, the site is in
`Ω^B_1` and the layer indices agree. -/
theorem restrictGen_layerIndex_eq
    (hGB : ∀ n x, x ∈ GB.Ω n ↔
      x ∈ G.Ω n ∧ ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1)
    (hdeep : ∀ y ∈ G.blk (G.layerIndex x) x, ∃ z ∈ X,
      Green.torusDist d (N₀ * L ^ k) z y ≤ ρ (G.layerIndex x)) :
    x ∈ GB.Ω 1 ∧ GB.layerIndex x = G.layerIndex x := by
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hx
  have hxl := G.mem_layer.1 hxn
  have h1 : x ∈ GB.Ω (G.layerIndex x) := (hGB _ x).2 ⟨hxl.1, hdeep⟩
  have h2 : x ∉ GB.Ω (G.layerIndex x + 1) := fun h => hxl.2 ((hGB _ x).1 h).1
  have hB : x ∈ GB.layer (G.layerIndex x) := GB.mem_layer.2 ⟨h1, h2⟩
  exact ⟨GB.layer_subset hn1 hnk hB, GB.layerIndex_eq hn1 hnk hB⟩

/-- A site of `Ω^B_1` is within `ρ_1` of `X`. -/
theorem restrictGen_near
    (hGB : ∀ n x, x ∈ GB.Ω n ↔
      x ∈ G.Ω n ∧ ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ GB.Ω 1) :
    ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z x ≤ ρ 1 :=
  ((hGB 1 x).1 hx).2 x (GeneratingSet.mem_blk.2 rfl)

/-- The sites of `Ω^B_1` where the two layer indices differ are at distance `> ρ_far` from `X`, if
`ρ_far + d L^n ≤ ρ_n` for `1 ≤ n ≤ k`. -/
theorem restrictGen_far_of_layer_ne
    (hGB : ∀ n x, x ∈ GB.Ω n ↔
      x ∈ G.Ω n ∧ ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n)
    {ρfar : ℝ} (hρfar : ∀ n, 1 ≤ n → n ≤ k → ρfar + d * (L : ℝ) ^ n ≤ ρ n)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ GB.Ω 1) (hne : GB.layerIndex x ≠ G.layerIndex x) :
    ∀ z ∈ X, ρfar < Green.torusDist d (N₀ * L ^ k) z x := by
  have hp := restrictGen_precedes hGB
  obtain ⟨hm1, hmk, hxm⟩ := GB.layerIndex_spec hx
  have hxG := hp.mem_Ω1 hx
  obtain ⟨hn1, hnk, hxn⟩ := G.layerIndex_spec hxG
  have hle := hp.layerIndex_le hx
  have hlt : GB.layerIndex x < G.layerIndex x := lt_of_le_of_ne hle hne
  have hxG' : x ∈ G.Ω (GB.layerIndex x + 1) :=
    G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 hxn).1
  have hxB : x ∉ GB.Ω (GB.layerIndex x + 1) := (GB.mem_layer.1 hxm).2
  have hfail : ¬ ∀ y ∈ G.blk (GB.layerIndex x + 1) x, ∃ z ∈ X,
      Green.torusDist d (N₀ * L ^ k) z y ≤ ρ (GB.layerIndex x + 1) :=
    fun h => hxB ((hGB _ x).2 ⟨hxG', h⟩)
  push Not at hfail
  obtain ⟨y, hy, hfar⟩ := hfail
  intro z hz
  have h1 := hfar z hz
  have h2 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) z x y
  have h3 := torusDist_le_of_mem_blk G (n := GB.layerIndex x + 1) (by omega) hy
  have h4 := hρfar (GB.layerIndex x + 1) (by omega) (by omega)
  linarith

/-- The sites of `Ω₁ ∖ Ω^B_1` are at distance `> ρ_far` from `X`. -/
theorem restrictGen_far_of_not_mem
    (hGB : ∀ n x, x ∈ GB.Ω n ↔
      x ∈ G.Ω n ∧ ∀ y ∈ G.blk n x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ n)
    {ρfar : ℝ} (hρfar : ∀ n, 1 ≤ n → n ≤ k → ρfar + d * (L : ℝ) ^ n ≤ ρ n)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hnx : x ∉ GB.Ω 1) :
    ∀ z ∈ X, ρfar < Green.torusDist d (N₀ * L ^ k) z x := by
  have hk := one_le_of_mem_Ω1 hx
  have hfail : ¬ ∀ y ∈ G.blk 1 x, ∃ z ∈ X, Green.torusDist d (N₀ * L ^ k) z y ≤ ρ 1 :=
    fun h => hnx ((hGB 1 x).2 ⟨hx, h⟩)
  push Not at hfail
  obtain ⟨y, hy, hfar⟩ := hfail
  intro z hz
  have h1 := hfar z hz
  have h2 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) z x y
  have h3 := torusDist_le_of_mem_blk G (n := 1) hk hy
  have h4 := hρfar 1 le_rfl hk
  linarith

end Props

omit [NeZero L] in
/-- The radii `ρ_n = r₀ - (ϱ_B + d) L^n` satisfy the gap condition of `exists_restrictGen`. -/
theorem restrict_radii_gap (hL : 2 ≤ L) {ϱB : ℝ} (hϱB0 : 0 ≤ ϱB) (r₀ : ℝ) (n : ℕ) :
    (r₀ - (ϱB + d) * (L : ℝ) ^ (n + 1)) + (ϱB + d) * (L : ℝ) ^ n ≤
      r₀ - (ϱB + d) * (L : ℝ) ^ n := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h0 : 0 ≤ (ϱB + d) * (L : ℝ) ^ n := by positivity
  have e : (ϱB + d) * (L : ℝ) ^ (n + 1) = (ϱB + d) * (L : ℝ) ^ n * L := by ring
  rw [e]
  nlinarith

/-- `ρ_far = r₀ - (ϱ_B + 2d) L^k` against the radii `ρ_n = r₀ - (ϱ_B + d) L^n`, `n ≤ k`. -/
theorem restrict_radii_far {ϱB : ℝ} (hϱB0 : 0 ≤ ϱB) (r₀ : ℝ) {n : ℕ} (hnk : n ≤ k) :
    (r₀ - (ϱB + 2 * d) * (L : ℝ) ^ k) + d * (L : ℝ) ^ n ≤ r₀ - (ϱB + d) * (L : ℝ) ^ n := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : (L : ℝ) ^ n ≤ (L : ℝ) ^ k := pow_le_pow_right₀ hL1 hnk
  have h2 : 0 ≤ ϱB + 2 * d := by positivity
  nlinarith

/-- **The path metric dominates the `ℓ¹` distance on the scale `L^k`**: every bond of `Ω₁` costs at
least `L^{-k}`. -/
theorem pathDist_ge_torusDist (G : GeneratingSet d L N₀ k ϱ') (y z : Torus d (N₀ * L ^ k)) :
    ENNReal.ofReal (Green.torusDist d (N₀ * L ^ k) y z / (L : ℝ) ^ k) ≤ G.pathDist y z := by
  have hLk : (0 : ℝ) < (L : ℝ) ^ k := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h := G.ofReal_sub_le_pathDist (fun w => Green.torusDist d (N₀ * L ^ k) y w / (L : ℝ) ^ k)
    (fun x x' hx hx' hadj => ?_) y z
  · simpa [torusDist_self'] using h
  · have hsx : G.spacing x ≤ (L : ℝ) ^ k :=
      pow_le_pow_right₀ hL1 (G.layerIndex_spec hx).2.1
    have hsx' : G.spacing x' ≤ (L : ℝ) ^ k :=
      pow_le_pow_right₀ hL1 (G.layerIndex_spec hx').2.1
    have hmax : max (G.spacing x) (G.spacing x') ≤ (L : ℝ) ^ k := max_le hsx hsx'
    have hpos : 0 < max (G.spacing x) (G.spacing x') :=
      lt_of_lt_of_le (spacing_pos G) (le_max_left _ _)
    have hd1 := Adj.torusDist_le hadj
    have t1 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) y x x'
    have t2 := torusDist_triangle' (d := d) (L := L) (N₀ := N₀) (k := k) y x' x
    rw [torusDist_comm' x' x] at t2
    have habs : |Green.torusDist d (N₀ * L ^ k) y x - Green.torusDist d (N₀ * L ^ k) y x'| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    unfold GeneratingSet.bondCost
    rw [← sub_div, abs_div, abs_of_pos hLk, div_le_div_iff₀ hLk hpos]
    calc |Green.torusDist d (N₀ * L ^ k) y x - Green.torusDist d (N₀ * L ^ k) y x'| *
          max (G.spacing x) (G.spacing x') ≤ 1 * (L : ℝ) ^ k :=
          mul_le_mul habs hmax hpos.le zero_le_one
      _ = _ := by ring

end Balaban.Background
