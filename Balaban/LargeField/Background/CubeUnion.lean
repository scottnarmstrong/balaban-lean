module

public import Balaban.LargeField.Background.MinimalGenSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Unions of cubes and comparison of minimal generating sets

A set `X` of sites of the level-`q` torus is a *union of `𝒞_n`-cubes* (`IsCubeUnion`) if
membership depends only on `fineCubeIdx n`. Fine sets of sets of `π_n`-cubes
(`cubePre`) are unions of `𝒞_n`-cubes when `π_n`-cubes are unions of `𝒞_n`-cubes
(`isCubeUnion_cubePre`); then `Ω_n(X) = X` (P3 (4.4)) and `𝔹_j(X) ≺ 𝔹_k(X)` for `j ≤ k`
(`minLayer_le_minLayer`; used for `𝔹_j(W_k) ≺ 𝔹_k(W_k)` in Definition II.2.4 (iii)).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

set_option linter.unusedSectionVars false

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

variable (M1 N₁ L q) in
/-- `X` is a union of `𝒞_n`-cubes. -/
def IsCubeUnion (n : ℕ) (X : Finset (Torus d (M1 * N₁ * L ^ q))) : Prop :=
  ∀ x y, fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n y → (x ∈ X ↔ y ∈ X)

section CubeUnion

variable {n j : ℕ} {X Y : Finset (Torus d (M1 * N₁ * L ^ q))}

theorem IsCubeUnion.cubeInterior_eq (h : IsCubeUnion M1 N₁ L q n X) :
    cubeInterior M1 N₁ L q n X = X := by
  ext x
  rw [mem_cubeInterior]
  constructor
  · intro hx; exact hx x rfl
  · intro hx y hy; exact (h y x hy).2 hx

theorem IsCubeUnion.inter (hX : IsCubeUnion M1 N₁ L q n X) (hY : IsCubeUnion M1 N₁ L q n Y) :
    IsCubeUnion M1 N₁ L q n (X ∩ Y) := fun x y h => by
  simp only [Finset.mem_inter, hX x y h, hY x y h]

theorem IsCubeUnion.union (hX : IsCubeUnion M1 N₁ L q n X) (hY : IsCubeUnion M1 N₁ L q n Y) :
    IsCubeUnion M1 N₁ L q n (X ∪ Y) := fun x y h => by
  simp only [Finset.mem_union, hX x y h, hY x y h]

theorem IsCubeUnion.isBlockUnion (hn : n ≤ q) (h : IsCubeUnion M1 N₁ L q n X) :
    IsBlockUnion L (M1 * N₁) q n X := fun x x' hx =>
  h x x' (blockMap_fineCubeIdx_eq hn hx)

/-- A `𝒞_n`-cube is a union of `𝒞_j`-cubes, `j ≤ n`. -/
theorem fineCubeIdx_eq_of_le (hjn : j ≤ n) (hn : n ≤ q) {x y : Torus d (M1 * N₁ * L ^ q)}
    (h : fineCubeIdx M1 N₁ L q j x = fineCubeIdx M1 N₁ L q j y) :
    fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n y := by
  have hcomp : ∀ z : Torus d (M1 * N₁ * L ^ q), fineCubeIdx M1 N₁ L q n z =
      blockMap (L ^ (n - j)) (N₁ * L ^ (q - n)) (fineCubeIdx M1 N₁ L q j z) := by
    intro z
    unfold fineCubeIdx
    have h1 : N₁ * L ^ (q - j) = L ^ (n - j) * (N₁ * L ^ (q - n)) := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjn
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hn
      have e1 : j + t - j = t := by omega
      have e2 : j + t + s - j = t + s := by omega
      have e3 : j + t + s - (j + t) = s := by omega
      rw [e1, e2, e3, pow_add]; ring
    rw [blockMap_comp (fine_eq_cube (hjn.trans hn)) h1]
    congr 1
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjn
    rw [Nat.add_sub_cancel_left, pow_add]; ring
  rw [hcomp x, hcomp y, h]

theorem IsCubeUnion.of_le (hjn : j ≤ n) (hn : n ≤ q) (h : IsCubeUnion M1 N₁ L q n X) :
    IsCubeUnion M1 N₁ L q j X := fun x y hxy => h x y (fineCubeIdx_eq_of_le hjn hn hxy)

/-- A union of `𝒞_j`-cubes lies in each of its layers `Ω_n`, `n ≤ j`. -/
theorem IsCubeUnion.subset_minLayer (h : IsCubeUnion M1 N₁ L q j X) {n : ℕ} (hnj : n ≤ j) :
    X ⊆ minLayer M1 N₁ L q j X n := by
  have key : ∀ t n : ℕ, n + t = j → X ⊆ minLayer M1 N₁ L q j X n := by
    intro t
    induction t with
    | zero =>
      intro n hn
      have : n = j := by omega
      subst this
      rw [minLayer_self, h.cubeInterior_eq]
    | succ t ih =>
      intro n hn
      exact (ih (n + 1) (by omega)).trans (minLayer_succ_subset X)
  exact key (j - n) n (by omega)

/-- **Definition II.2.4 (iii)** (comparison of the minimal sets of `X` at scales `j ≤ k`): for a
union of `𝒞_k`-cubes `X`, `Ω_n(𝔹_j(X)) ⊆ Ω_n(𝔹_k(X))`. -/
theorem minLayer_le_minLayer (hjk : j ≤ n) (hnq : n ≤ q) (hX : IsCubeUnion M1 N₁ L q n X)
    (m : ℕ) : minLayer M1 N₁ L q j X m ⊆ minLayer M1 N₁ L q n X m := by
  have hXj : IsCubeUnion M1 N₁ L q j X := hX.of_le hjk hnq
  by_cases hmj : j < m
  · rw [minLayer_of_gt X hmj]; exact Finset.empty_subset _
  · push Not at hmj
    have key : ∀ t m : ℕ, m + t = j →
        minLayer M1 N₁ L q j X m ⊆ minLayer M1 N₁ L q n X m := by
      intro t
      induction t with
      | zero =>
        intro m hm
        have : m = j := by omega
        subst this
        rw [minLayer_self, hXj.cubeInterior_eq]
        exact hX.subset_minLayer hjk
      | succ t ih =>
        intro m hm
        have hmj' : m < j := by omega
        rw [minLayer_of_lt X hmj']
        have hmn : m < n := by omega
        rw [minLayer_of_lt X hmn]
        exact nearStep_mono (ih (m + 1) (by omega))
    exact key (j - m) m (by omega)

end CubeUnion

section CubePre

variable (M1 N₁ L q) in
/-- The fine set of a set `A` of cubes of side `P` (`blockMap P m`). -/
noncomputable def cubePre (P m : ℕ) (A : Set (Torus d m)) : Finset (Torus d (M1 * N₁ * L ^ q)) := by
  classical
  exact univ.filter fun x => blockMap P m x ∈ A

theorem mem_cubePre {P m : ℕ} {A : Set (Torus d m)} {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ cubePre M1 N₁ L q P m A ↔ blockMap P m x ∈ A := by
  classical
  simp [cubePre]

/-- Fine sets of sets of `π_n`-cubes (side `L ^ n c M1`, `c` a positive integer) are unions of
`𝒞_n`-cubes. -/
theorem isCubeUnion_cubePre {n c m : ℕ} (hn : n ≤ q) (hm : N₁ * L ^ (q - n) = c * m)
    (A : Set (Torus d m)) :
    IsCubeUnion M1 N₁ L q n (cubePre M1 N₁ L q (L ^ n * (c * M1)) m A) := by
  intro x y h
  have hc : ∀ z : Torus d (M1 * N₁ * L ^ q), blockMap (L ^ n * (c * M1)) m z =
      blockMap c m (fineCubeIdx M1 N₁ L q n z) := by
    intro z
    unfold fineCubeIdx
    have : NeZero m := by
      refine ⟨fun h0 => ?_⟩
      have := NeZero.ne (N₁ * L ^ (q - n))
      rw [hm, h0] at this; simp at this
    rw [blockMap_comp (fine_eq_cube hn) hm]
    congr 1; ring
  rw [mem_cubePre, mem_cubePre, hc x, hc y, h]

end CubePre

end Balaban.LargeField
