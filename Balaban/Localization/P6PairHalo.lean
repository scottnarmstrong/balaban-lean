/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.StepGenSetsFlow
public import Balaban.Localization.CubeAligned
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The haloed common auxiliary set `F♯` of the P6 mixed pair (VMOD-11 §1.1, (1.3)-(1.4))

For the step `k → k+1` of the region calculus (`RegionStep`), `K = k + 1`, `ρ' = ⌊R_{k-1}⌋`,
`Z = Z_kᶜ` (VMOD-11 notation; `st.Z` here is `Z_k`), `U = Z^≈`, `W = Z^{≈2}` (`stepW`),
`A₀ = cl_{π_K} U` (the `π_K`-cubes meeting `U`) and `A = Halo¹_{π_K} A₀`.

* `p6Halo`: the fine set of `A`;
* `p6_halo_subset_W`: `A ⊆ W` (as fine sets);
* `p6_halo_collar`: `B(x, L · P₀) ⊆ A` for every fine site `x` over `U` (`P₀ = L^k c M₁`);
* `p6_halo_far`: the fine distance between `Wᶜ` and `A` is `> 5 L M₁ L^k` (the interface (1.4));
* `GeneratingSet.addTop`, `p6Fsharp`: the generating set `F♯` with `Ω_n(F♯) = Ω_n(𝔹_k(W))` for
  `n ≤ k` and `Ω_K(F♯) = A` (`p6_fsharp_generating`);
* `p6_fsharp_cubeAligned`: `F♯` is cube aligned.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization

set_option linter.unusedSectionVars false

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]

/-! ### The halo as a set of `π_K`-cubes and as a fine set -/

/-- `A = Halo¹_{π_K}(cl_{π_K} Z^≈)` as a set of `π_K`-cubes, for the region `Z = Z_kᶜ`
(`Z` here is the large-field region `Z_k`, the complement is taken inside): the cubes within
index distance `1` of a cube meeting `Z^≈ = thick ρ' (Z_kᶜ)`. -/
def p6HaloCubes (L n1 ρ' : ℕ) [NeZero n1] (Z : Set (Torus d n0)) : Set (Torus d n1) :=
  nbhd 1 (blockMap L n1 '' thick ρ' Zᶜ)

/-- The fine set of `A`. -/
noncomputable def p6Halo (M1 c n1 L k ρ' : ℕ) [NeZero L] [NeZero M1] [NeZero c] [NeZero n1]
    (Z : Set (Torus d n0)) :
    Finset (Torus d (M1 * (c * n1) * L ^ (k + 1))) :=
  fineK1 M1 c n1 L k (p6HaloCubes L n1 ρ' Z)

theorem mem_p6Halo {ρ' : ℕ} {Z : Set (Torus d n0)} {x : Torus d (M1 * (c * n1) * L ^ (k + 1))} :
    x ∈ p6Halo M1 c n1 L k ρ' Z ↔
      blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ p6HaloCubes L n1 ρ' Z := by
  unfold p6Halo; exact mem_fineK1

/-- The cube-side positivity used throughout. -/
theorem p6_P0_pos : 0 < L ^ k * (c * M1) :=
  Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne c; positivity)

/-- A site of the halo `A` lies over a `π_k`-cube within `ρ' + 2L` of `Z_kᶜ`. -/
theorem p6_halo_near (hn : n0 = L * n1) {ρ' : ℕ} (Z : Set (Torus d n0))
    {x : Torus d (M1 * (c * n1) * L ^ (k + 1))} (hx : x ∈ p6Halo M1 c n1 L k ρ' Z) :
    blockMap (L ^ k * (c * M1)) n0 x ∈ nbhd (ρ' + 2 * L) Zᶜ := by
  rw [mem_p6Halo] at hx
  obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ := mem_nbhd.1 hx
  obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hu
  refine mem_nbhd.2 ⟨z, hz, ?_⟩
  have h1 := blockMap_k_succ (M1 := M1) (c := c) (L := L) (k := k) hn x
  have h2 := supDist_le_blockMap hn (blockMap (L ^ k * (c * M1)) n0 x) u
  rw [h1] at h2
  have h3 : L * supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x)
      (blockMap L n1 u) ≤ L * 1 := Nat.mul_le_mul_left _ ha
  have h4 := supDist_triangle (blockMap (L ^ k * (c * M1)) n0 x) u z
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hdz' : supDist u z ≤ ρ' + 1 := hdz
  omega

/-- **`p6_halo_subset_W`** (VMOD-11 (1.3), `A ⊂ W`): the halo lies in `W = Z^{≈2}`, provided
`2L ≤ ρ' + 2` (`r = ρ' + 1 > 2L + 1`). -/
theorem p6_halo_subset_W (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 2 * L ≤ ρ' + 2)
    (Z : Set (Torus d n0)) :
    p6Halo M1 c n1 L k ρ' Z ⊆ stepW M1 c n1 L k ρ' Z := by
  intro x hx
  have h := p6_halo_near hn Z hx
  unfold stepW
  rw [mem_fineK, thick2_eq]
  exact nbhd_mono (by omega) subset_rfl h

/-- A fine site over `U = Z^≈` has its whole ball of radius `L P₀ = P₁` in the halo `A`
(VMOD-11 (1.3), `B(x, L M ℓ_k) ⊂ A`). -/
theorem p6_halo_collar (hn : n0 = L * n1) {ρ' : ℕ} (Z : Set (Torus d n0))
    {x : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : blockMap (L ^ k * (c * M1)) n0 x ∈ thick ρ' Zᶜ)
    {y : Torus d (M1 * (c * n1) * L ^ (k + 1))} (hy : supDist x y ≤ L * (L ^ k * (c * M1))) :
    y ∈ p6Halo M1 c n1 L k ρ' Z := by
  rw [mem_p6Halo]
  refine mem_nbhd.2 ⟨blockMap L n1 (blockMap (L ^ k * (c * M1)) n0 x), ⟨_, hx, rfl⟩, ?_⟩
  rw [blockMap_k_succ (M1 := M1) (c := c) (L := L) (k := k) hn x]
  have hD : L * (L ^ k * (c * M1)) ≤ L ^ (k + 1) * (c * M1) := by
    rw [pow_succ]; exact le_of_eq (by ring)
  have := cubes_close (M1 := M1) (c := c) (n1 := n1) (L := L) (k := k) hD hy
  rw [supDist_comm]
  exact this

/-- **`p6_halo_far`, sup-distance form** (VMOD-11 (1.3)-(1.4)): a fine site outside `W = Z^{≈2}`
and a fine site of the halo `A` are at fine sup-distance `≥ P₀ (ρ' + 2 - 2L) + 1 - P₀`,
`P₀ = L^k c M₁`; this exceeds `(r - 2L - 2) P₀` for `r = ρ' + 1`. -/
theorem p6_halo_far_sup (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 2 * L ≤ ρ' + 2)
    (Z : Set (Torus d n0)) {x y : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : x ∉ stepW M1 c n1 L k ρ' Z) (hy : y ∈ p6Halo M1 c n1 L k ρ' Z) :
    (L ^ k * (c * M1)) * (ρ' + 3 - 2 * L) + 1 ≤ supDist x y + L ^ k * (c * M1) := by
  have hP : M1 * (c * n1) * L ^ (k + 1) = (L ^ k * (c * M1)) * n0 := by rw [hn]; ring
  have hPpos := p6_P0_pos (M1 := M1) (c := c) (L := L) (k := k)
  have hsub := p6_halo_near hn Z hy
  clear hy
  unfold stepW at hx
  rw [mem_fineK, thick2_eq] at hx
  -- coarse distance of the two cubes
  obtain ⟨z, hz, hdz⟩ := mem_nbhd.1 hsub
  have ht : ρ' + 3 - 2 * L ≤ supDist (blockMap (L ^ k * (c * M1)) n0 x)
      (blockMap (L ^ k * (c * M1)) n0 y) := by
    by_contra hlt
    push Not at hlt
    apply hx
    refine mem_nbhd.2 ⟨z, hz, ?_⟩
    have := supDist_triangle (blockMap (L ^ k * (c * M1)) n0 x)
      (blockMap (L ^ k * (c * M1)) n0 y) z
    omega
  have h1 := supDist_blockMap_le (d := d) hP x y
  have h2 : (ρ' + 3 - 2 * L) ≤ (supDist x y + L ^ k * (c * M1) - 1) / (L ^ k * (c * M1)) :=
    ht.trans h1
  rw [Nat.le_div_iff_mul_le hPpos] at h2
  have h3 : (ρ' + 3 - 2 * L) * (L ^ k * (c * M1)) = (L ^ k * (c * M1)) * (ρ' + 3 - 2 * L) :=
    mul_comm _ _
  omega

/-- **`p6_halo_far`, `ℓ¹` form** (VMOD-11 (1.4)): for `ρ' ≥ 3L` and `c ≥ 5`, a site outside `W` is
at `ℓ¹` distance `> 5 L M₁ L^k` from every site of the halo `A`. -/
theorem p6_halo_far (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) {x y : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hx : x ∉ stepW M1 c n1 L k ρ' Z) (hy : y ∈ p6Halo M1 c n1 L k ρ' Z) :
    minSep L M1 * (L : ℝ) ^ k < Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x y := by
  have hL0 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h := p6_halo_far_sup (M1 := M1) (c := c) hn (by omega) Z hx hy
  have hdist : (supDist x y : ℝ) ≤ Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x y :=
    supDist_le_torusDist x y
  have hP0 : 0 < L ^ k * (c * M1) := p6_P0_pos (M1 := M1) (c := c) (L := L) (k := k)
  have e : ρ' + 3 - 2 * L = (ρ' + 3 - 2 * L - 2) + 2 := by omega
  have hq : L + 1 ≤ ρ' + 3 - 2 * L - 2 := by omega
  have key : L ^ k * M1 * (5 * L) < (L ^ k * (c * M1)) * (ρ' + 3 - 2 * L - 2) + 1 := by
    have h1 : 5 * L ≤ c * (ρ' + 3 - 2 * L - 2) := by nlinarith
    have h2 : L ^ k * M1 * (5 * L) ≤ L ^ k * M1 * (c * (ρ' + 3 - 2 * L - 2)) :=
      Nat.mul_le_mul_left _ h1
    have h3 : L ^ k * M1 * (c * (ρ' + 3 - 2 * L - 2)) =
        (L ^ k * (c * M1)) * (ρ' + 3 - 2 * L - 2) := by ring
    omega
  have hreal : ((L ^ k * (c * M1) : ℕ) : ℝ) * ((ρ' + 3 - 2 * L : ℕ) : ℝ) + 1 ≤
      (supDist x y : ℝ) + ((L ^ k * (c * M1) : ℕ) : ℝ) := by exact_mod_cast h
  have e2 : ((ρ' + 3 - 2 * L : ℕ) : ℝ) = ((ρ' + 3 - 2 * L - 2 : ℕ) : ℝ) + 2 := by
    exact_mod_cast e
  have key' : ((L ^ k * M1 * (5 * L) : ℕ) : ℝ) <
      ((L ^ k * (c * M1) : ℕ) : ℝ) * ((ρ' + 3 - 2 * L - 2 : ℕ) : ℝ) + 1 := by exact_mod_cast key
  unfold minSep
  push_cast at hreal key' e2 ⊢
  rw [e2] at hreal
  have hPr : (0 : ℝ) ≤ (L : ℝ) ^ k * ((c : ℝ) * M1) := by positivity
  nlinarith [hreal, key', hdist, hPr]

/-! ### Adding a top layer; the old set `H⁻` and `F♯` -/

/-- Add a top layer `A` (a union of `(k+1)`-blocks inside `Ω_k`, at distance `> ϱ L^k` from
`Ω_kᶜ`) to a generating set of depth `k + 1`: `Ω_n` is unchanged for `n ≠ k + 1` and
`Ω_{k+1} = A`. -/
noncomputable def _root_.Balaban.Multiscale.GeneratingSet.addTop {N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ (k + 1) ϱ) (A : Finset (Torus d (N₀ * L ^ (k + 1))))
    (hAblock : IsBlockUnion L N₀ (k + 1) (k + 1) A) (hAsub : 1 ≤ k → A ⊆ G.Ω k)
    (hAsep : 1 ≤ k → ∀ x, x ∉ G.Ω k → ∀ y ∈ A,
      ϱ * (L : ℝ) ^ k < Green.torusDist d (N₀ * L ^ (k + 1)) x y) :
    GeneratingSet d L N₀ (k + 1) ϱ := by
  classical
  exact
  { Ω := fun n => if n = k + 1 then A else G.Ω n
    top := by
      have h : ¬ (k + 1 + 1 = k + 1) := by omega
      simp only [h, ↓reduceIte]
      exact G.top
    subset := by
      intro j hj1 hjk
      by_cases hj : j = k + 1
      · subst hj
        have h : ¬ (k + 1 + 1 = k + 1) := by omega
        simp only [h, ↓reduceIte, G.top]
        exact Finset.empty_subset _
      · have hjk' : j ≤ k := by omega
        simp only [hj, ↓reduceIte]
        by_cases hj1' : j + 1 = k + 1
        · have hjk'' : j = k := by omega
          subst hjk''
          simp only [↓reduceIte]
          exact hAsub hj1
        · simp only [hj1', ↓reduceIte]
          exact G.subset j hj1 hjk
    blockUnion := by
      intro j hj1 hjk x x' hxx'
      by_cases hj : j = k + 1
      · subst hj
        simpa using hAblock x x' hxx'
      · simpa [hj] using G.blockUnion j hj1 hjk x x' hxx'
    separation := by
      intro j hj1 hjk x hx y hy
      have hj : j ≠ k + 1 := by omega
      simp only [hj, ↓reduceIte] at hx
      by_cases hj1' : j + 1 = k + 1
      · have hjk'' : j = k := by omega
        subst hjk''
        simp only [↓reduceIte] at hy
        exact hAsep hj1 x hx y hy
      · simp only [hj1', ↓reduceIte] at hy
        exact G.separation j hj1 hjk x hx y hy }

theorem _root_.Balaban.Multiscale.GeneratingSet.addTop_Ω {N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ (k + 1) ϱ) (A : Finset (Torus d (N₀ * L ^ (k + 1))))
    (hAblock : IsBlockUnion L N₀ (k + 1) (k + 1) A) (hAsub : 1 ≤ k → A ⊆ G.Ω k)
    (hAsep : 1 ≤ k → ∀ x, x ∉ G.Ω k → ∀ y ∈ A,
      ϱ * (L : ℝ) ^ k < Green.torusDist d (N₀ * L ^ (k + 1)) x y) (n : ℕ) :
    (G.addTop A hAblock hAsub hAsep).Ω n = if n = k + 1 then A else G.Ω n := rfl

/-- **The old operator set** `H⁻ = 𝔹_k(W_k)`, viewed at depth `K = k + 1` with empty top domain
(`W_k = (Z_kᶜ)^{≈2}`, `stepW`). -/
noncomputable def p6Hold (M1 c n1 L k ρ' : ℕ) [NeZero L] [NeZero M1] [NeZero c] [NeZero n1]
    (Z : Set (Torus d n0)) : GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  minimalGenSet (Nat.le_succ k) (stepW M1 c n1 L k ρ' Z)

theorem p6Hold_Ω {ρ' : ℕ} (Z : Set (Torus d n0)) (n : ℕ) :
    (p6Hold M1 c n1 L k ρ' Z).Ω n = minLayer M1 (c * n1) L (k + 1) k (stepW M1 c n1 L k ρ' Z) n :=
  rfl

/-- `Ω_k(H⁻) = W_k` (`W_k` is a union of `𝒞_k`-cubes), and `Ω_K(H⁻) = ∅`. -/
theorem p6Hold_Ω_k (hn : n0 = L * n1) {ρ' : ℕ} (Z : Set (Torus d n0)) :
    (p6Hold M1 c n1 L k ρ' Z).Ω k = stepW M1 c n1 L k ρ' Z := by
  rw [p6Hold_Ω, minLayer_self]
  exact (isCubeUnion_fineK hn _).cubeInterior_eq

theorem p6Hold_Ω_top {ρ' : ℕ} (Z : Set (Torus d n0)) :
    (p6Hold M1 c n1 L k ρ' Z).Ω (k + 1) = ∅ := by
  rw [p6Hold_Ω]; exact minLayer_of_gt _ (Nat.lt_succ_self k)

/-- **`F♯`** (VMOD-11 §1): `Ω_n(F♯) = Ω_n(H⁻)` for `n ≤ k` and `Ω_K(F♯) = A`, the halo.
Source premises: `n_k = L n_{k+1}`, `ρ' = ⌊R_{k-1}⌋ ≥ 3L`, `c ≥ 5`. -/
noncomputable def p6Fsharp (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) :
    GeneratingSet d L (M1 * (c * n1)) (k + 1) (minSep L M1) :=
  (p6Hold M1 c n1 L k ρ' Z).addTop (p6Halo M1 c n1 L k ρ' Z)
    ((isCubeUnion_fineK1 _).isBlockUnion le_rfl)
    (fun _ => by
      rw [p6Hold_Ω_k hn]
      exact p6_halo_subset_W hn (by omega) Z)
    (fun _ x hx y hy => by
      rw [p6Hold_Ω_k hn] at hx
      exact p6_halo_far hn hρ hc Z hx hy)

/-- **`p6_fsharp_generating`** (VMOD-11 §1, (1.3)-(1.4)): `F♯` is a generating set (of depth
`K = k + 1` with separation `5 L M₁`; this is the type of `p6Fsharp`) with
`Ω_n(F♯) = Ω_n(H⁻)` for `n ≤ k` and `Ω_K(F♯) = A = Halo¹_{π_K}(cl_{π_K} Z^≈)`, and `A ⊆ W`. -/
theorem p6_fsharp_generating (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) :
    (∀ n, n ≤ k → (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).Ω n =
        (p6Hold M1 c n1 L k ρ' Z).Ω n) ∧
      (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).Ω (k + 1) =
        p6Halo M1 c n1 L k ρ' Z ∧
      p6Halo M1 c n1 L k ρ' Z ⊆ stepW M1 c n1 L k ρ' Z := by
  refine ⟨fun n hnk => ?_, ?_, p6_halo_subset_W hn (by omega) Z⟩
  · have h : n ≠ k + 1 := by omega
    unfold p6Fsharp
    rw [GeneratingSet.addTop_Ω]; simp [h]
  · unfold p6Fsharp
    rw [GeneratingSet.addTop_Ω]; simp

theorem p6Fsharp_Ω_of_le (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) {n : ℕ} (hnk : n ≤ k) :
    (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).Ω n =
      (p6Hold M1 c n1 L k ρ' Z).Ω n :=
  (p6_fsharp_generating hn hρ hc Z).1 n hnk

theorem p6Fsharp_Ω_top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) :
    (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z).Ω (k + 1) =
      p6Halo M1 c n1 L k ρ' Z :=
  (p6_fsharp_generating hn hρ hc Z).2.1

/-! ### Cube alignment -/

omit [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1] in
/-- Sites of the same cell of side `a` lie in the same block of side `P` when `a ∣ P`. -/
theorem blockMap_eq_of_sameCell {n m a P : ℕ} {x x' : Torus d n} (h : SameCell a x x')
    (hP : a ∣ P) : blockMap P m x = blockMap P m x' := by
  obtain ⟨t, rfl⟩ := hP
  funext μ
  unfold blockMap blockCoord
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h μ]

/-- Membership in a layer of a minimal generating set depends only on the `𝒞_n`-cube of the site. -/
theorem minLayer_iff_of_fineCubeIdx_eq {q j n : ℕ} {N₁ : ℕ} [NeZero N₁]
    (X : Finset (Torus d (M1 * N₁ * L ^ q))) {x x' : Torus d (M1 * N₁ * L ^ q)}
    (hc : fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n x') :
    x ∈ minLayer M1 N₁ L q j X n ↔ x' ∈ minLayer M1 N₁ L q j X n := by
  rcases lt_trichotomy n j with h1 | h1 | h1
  · rw [minLayer_of_lt X h1, mem_nearStep, mem_nearStep, hc]
  · subst h1
    rw [minLayer_self, mem_cubeInterior, mem_cubeInterior, hc]
  · rw [minLayer_of_gt X h1]; simp

/-- **`p6_fsharp_cubeAligned`**: `F♯` is cube aligned (`Ω_j` is a union of cells of side
`M₁ ℓ_j = L^(j + m₁)`), for `M₁ = L^m₁`, `m₁ ≥ 2`. -/
theorem p6_fsharp_cubeAligned (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) {m₁ : ℕ} (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) :
    CubeAligned (p6Fsharp (M1 := M1) (c := c) (L := L) (k := k) hn hρ hc Z) m₁ := by
  refine ⟨hm₁, by rw [hM1]; exact Dvd.intro _ rfl, ?_⟩
  intro j hj1 hjK x x' hcell
  by_cases hj : j = k + 1
  · subst hj
    rw [p6Fsharp_Ω_top, mem_p6Halo, mem_p6Halo]
    have hdvd : L ^ (k + 1 + m₁) ∣ L ^ (k + 1) * (c * M1) := by
      rw [hM1, show L ^ (k + 1) * (c * L ^ m₁) = L ^ (k + 1 + m₁) * c by rw [pow_add]; ring]
      exact Dvd.intro _ rfl
    rw [blockMap_eq_of_sameCell (m := n1) hcell hdvd]
  · have hjk : j ≤ k := by omega
    rw [p6Fsharp_Ω_of_le hn hρ hc Z hjk, p6Hold_Ω]
    refine minLayer_iff_of_fineCubeIdx_eq _ ?_
    unfold fineCubeIdx
    refine blockMap_eq_of_sameCell hcell ?_
    rw [hM1, ← pow_add]

end Balaban.LargeField
