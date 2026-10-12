module

public import Balaban.LargeField.Region.Generating
public import Balaban.LargeField.Geometry.Coarsen
public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# P3's minimal generating sets (Part II, Definition II.2.2 and Lemma II.2.3)

On the fine torus `Torus d (M1 * N₁ * L ^ q)` (so `N₀ = M1 * N₁`, `ℓ = N₀ L ^ q`) let `𝒞_n` be the
partition into cubes of side `s_n = M1 L ^ n` (`n ≤ q`); the index of the cube of a site is
`fineCubeIdx n x = blockMap (L ^ n * M1) (N₁ * L ^ (q - n)) x`. For a set `X` of sites and a scale
`j ≤ q` put

* `Ω_j(X)` the union of the `𝒞_j`-cubes contained in `X` (`cubeInterior`; it is `X` when `X` is a
  union of `𝒞_j`-cubes, e.g. of `π_j`-cubes, which is P3 (4.4));
* `Ω_n(X)` for `n < j` the union of the `𝒞_n`-cubes at cube-index distance `≤ 5L` from a
  site of `Ω_{n+1}(X)` (`nearStep`; P3 (4.5)-(4.6));
* `Ω_n(X) = ∅` for `n > j`.

`minimalGenSet` packages these layers as a `Balaban.Multiscale.GeneratingSet` on the level-`q`
torus with separation `5 L M1` (Lemma II.2.3 (a)); the case `j < q` is the family `𝔹_j(X)` seen
on a finer torus (all layers above `j` empty). Monotonicity (b), range and locality (c) and
disjoint unions (d) follow.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

set_option linter.unusedSectionVars false

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- `ℓ = M1 N₁ L ^ q = (L ^ n M1) (N₁ L ^ (q - n))` for `n ≤ q`. -/
theorem fine_eq_cube {n : ℕ} (hn : n ≤ q) :
    M1 * N₁ * L ^ q = (L ^ n * M1) * (N₁ * L ^ (q - n)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

/-- The index of the `𝒞_n`-cube (side `M1 L ^ n`) of a site. -/
def fineCubeIdx (M1 N₁ L q n : ℕ) (x : Torus d (M1 * N₁ * L ^ q)) : Torus d (N₁ * L ^ (q - n)) :=
  blockMap (L ^ n * M1) (N₁ * L ^ (q - n)) x

theorem fineCubeIdx_eq_comp {n : ℕ} (hn : n ≤ q) (x : Torus d (M1 * N₁ * L ^ q)) :
    fineCubeIdx M1 N₁ L q n x =
      blockMap M1 (N₁ * L ^ (q - n)) (jBlock d L (M1 * N₁) q n x) := by
  unfold fineCubeIdx jBlock
  rw [blockMap_comp (fine_eq_cube hn |>.trans (by ring)) (by ring)]


theorem blockMap_fineCubeIdx_eq {n : ℕ} (hn : n ≤ q) {x x' : Torus d (M1 * N₁ * L ^ q)}
    (h : jBlock d L (M1 * N₁) q n x = jBlock d L (M1 * N₁) q n x') :
    fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n x' := by
  rw [fineCubeIdx_eq_comp hn, fineCubeIdx_eq_comp hn, h]

section Layers

variable (M1 N₁ L q) in
/-- `Ω_j(X)`: the union of the `𝒞_j`-cubes contained in `X` (P3 (4.4)). -/
def cubeInterior (j : ℕ) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    Finset (Torus d (M1 * N₁ * L ^ q)) := by
  classical
  exact univ.filter fun x => ∀ y, fineCubeIdx M1 N₁ L q j y = fineCubeIdx M1 N₁ L q j x → y ∈ X

variable (M1 N₁ L q) in
/-- One recursion step (P3 (4.5)-(4.6)): the union of the `𝒞_n`-cubes at cube-index distance
`≤ 5 L` from a site of `A`. -/
def nearStep (n : ℕ) (A : Finset (Torus d (M1 * N₁ * L ^ q))) :
    Finset (Torus d (M1 * N₁ * L ^ q)) := by
  classical
  exact univ.filter fun x => ∃ y ∈ A,
    supDist (fineCubeIdx M1 N₁ L q n x) (fineCubeIdx M1 N₁ L q n y) ≤ 5 * L

variable (M1 N₁ L q) in
/-- The layers `Ω_j(X), Ω_{j-1}(X), …` by recursion (`t = 0` is `Ω_j`). -/
def minLayerAux (j : ℕ) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    ℕ → Finset (Torus d (M1 * N₁ * L ^ q))
  | 0 => cubeInterior M1 N₁ L q j X
  | t + 1 => nearStep M1 N₁ L q (j - (t + 1)) (minLayerAux j X t)

variable (M1 N₁ L q) in
/-- **The layers `Ω_n(X)` of P3's minimal generating set** `𝔹_j(X)` (Definition II.2.2). -/
def minLayer (j : ℕ) (X : Finset (Torus d (M1 * N₁ * L ^ q))) (n : ℕ) :
    Finset (Torus d (M1 * N₁ * L ^ q)) := by
  classical
  exact if n ≤ j then minLayerAux M1 N₁ L q j X (j - n) else ∅

end Layers

section LayerFacts

variable {j : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q)))

theorem minLayer_self : minLayer M1 N₁ L q j X j = cubeInterior M1 N₁ L q j X := by
  simp [minLayer, minLayerAux]

theorem minLayer_of_gt {n : ℕ} (h : j < n) : minLayer M1 N₁ L q j X n = ∅ := by
  simp [minLayer, not_le.mpr h]

theorem minLayer_of_lt {n : ℕ} (h : n < j) :
    minLayer M1 N₁ L q j X n = nearStep M1 N₁ L q n (minLayer M1 N₁ L q j X (n + 1)) := by
  have e : j - n = (j - (n + 1)) + 1 := by omega
  have e2 : j - (j - (n + 1) + 1) = n := by omega
  have h1 : n ≤ j := h.le
  have h2 : n + 1 ≤ j := h
  simp [minLayer, h1, h2, e, minLayerAux, e2]

theorem mem_cubeInterior {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ cubeInterior M1 N₁ L q j X ↔
      ∀ y, fineCubeIdx M1 N₁ L q j y = fineCubeIdx M1 N₁ L q j x → y ∈ X := by
  classical
  simp [cubeInterior]

theorem mem_nearStep {n : ℕ} {A : Finset (Torus d (M1 * N₁ * L ^ q))}
    {x : Torus d (M1 * N₁ * L ^ q)} :
    x ∈ nearStep M1 N₁ L q n A ↔ ∃ y ∈ A,
      supDist (fineCubeIdx M1 N₁ L q n x) (fineCubeIdx M1 N₁ L q n y) ≤ 5 * L := by
  classical
  simp [nearStep]

theorem cubeInterior_subset : cubeInterior M1 N₁ L q j X ⊆ X := fun x hx =>
  (mem_cubeInterior X).1 hx x rfl

theorem subset_nearStep {n : ℕ} (A : Finset (Torus d (M1 * N₁ * L ^ q))) :
    A ⊆ nearStep M1 N₁ L q n A := fun x hx =>
  (mem_nearStep).2 ⟨x, hx, by rw [supDist_self]; exact Nat.zero_le _⟩

theorem minLayer_succ_subset {n : ℕ} :
    minLayer M1 N₁ L q j X (n + 1) ⊆ minLayer M1 N₁ L q j X n := by
  by_cases h : n < j
  · rw [minLayer_of_lt X h]; exact subset_nearStep _
  · have : j < n + 1 ∨ j = n := by omega
    rcases this with h1 | h1
    · rw [minLayer_of_gt X h1]; exact Finset.empty_subset _
    · subst h1; rw [minLayer_of_gt X (Nat.lt_succ_self _)]; exact Finset.empty_subset _

theorem minLayer_blockUnion {n : ℕ} (hn : n ≤ q) {x x' : Torus d (M1 * N₁ * L ^ q)}
    (h : jBlock d L (M1 * N₁) q n x = jBlock d L (M1 * N₁) q n x') :
    x ∈ minLayer M1 N₁ L q j X n ↔ x' ∈ minLayer M1 N₁ L q j X n := by
  have hc : fineCubeIdx M1 N₁ L q n x = fineCubeIdx M1 N₁ L q n x' := blockMap_fineCubeIdx_eq hn h
  rcases lt_trichotomy n j with h1 | h1 | h1
  · rw [minLayer_of_lt X h1, mem_nearStep, mem_nearStep, hc]
  · subst h1
    rw [minLayer_self, mem_cubeInterior, mem_cubeInterior, hc]
  · rw [minLayer_of_gt X h1]; simp

/-- The step of the recursion separates: a site outside `nearStep n A` is at fine `ℓ¹` distance
`> 5 L M1 L ^ n` from every site of `A`. -/
theorem torusDist_gt_of_not_mem_nearStep {n : ℕ} (hn : n ≤ q)
    {A : Finset (Torus d (M1 * N₁ * L ^ q))} {x y : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∉ nearStep M1 N₁ L q n A) (hy : y ∈ A) :
    (5 * L * M1 : ℝ) * (L : ℝ) ^ n < Green.torusDist d (M1 * N₁ * L ^ q) x y := by
  have h1 : 5 * L + 1 ≤ supDist (fineCubeIdx M1 N₁ L q n x) (fineCubeIdx M1 N₁ L q n y) := by
    by_contra hlt
    exact hx (mem_nearStep.2 ⟨y, hy, by omega⟩)
  have hN : 0 < L ^ n * M1 := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have h2 := torusDist_lower (d := d) (fine_eq_cube hn) hN x y
  unfold fineCubeIdx at h1
  have h3 : ((L ^ n * M1 : ℕ) : ℝ) * ((5 * L + 1 : ℕ) : ℝ) ≤
      ((L ^ n * M1 : ℕ) : ℝ) * (supDist (blockMap (L ^ n * M1) (N₁ * L ^ (q - n)) x)
        (blockMap (L ^ n * M1) (N₁ * L ^ (q - n)) y) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast h1) (Nat.cast_nonneg _)
  push_cast at h3 h2
  nlinarith [h2, h3]

end LayerFacts

/-- The separation constant `ϱ₃ = 5 L M1` of the minimal generating sets. -/
noncomputable def minSep (L M1 : ℕ) : ℝ := 5 * L * M1

/-- **Lemma II.2.3 (a)** (P3 (4.4)-(4.6)): the minimal generating set `𝔹_j(X)` of a set `X` of
sites, `j ≤ q`, as a `GeneratingSet` on the level-`q` torus with separation `5 L M1`. -/
noncomputable def minimalGenSet {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) :
    GeneratingSet d L (M1 * N₁) q (minSep L M1) where
  Ω := minLayer M1 N₁ L q j X
  top := minLayer_of_gt X (by omega)
  subset := fun n _ _ => minLayer_succ_subset X
  blockUnion := fun n _ hn x x' h => minLayer_blockUnion X hn h
  separation := by
    intro n hn1 hnq x hx y hy
    have hnj : n < j := by
      by_contra hge
      rw [minLayer_of_gt X (by omega : j < n + 1)] at hy
      exact absurd hy (Finset.notMem_empty _)
    rw [minLayer_of_lt X hnj] at hx
    exact torusDist_gt_of_not_mem_nearStep hnq.le hx hy

theorem minimalGenSet_Ω {j : ℕ} (hj : j ≤ q) (X : Finset (Torus d (M1 * N₁ * L ^ q))) (n : ℕ) :
    (minimalGenSet hj X).Ω n = minLayer M1 N₁ L q j X n := rfl


/-! ### Lemma II.2.3 (b): monotonicity -/

section Mono

variable {j : ℕ} {X X' : Finset (Torus d (M1 * N₁ * L ^ q))}

theorem cubeInterior_mono (h : X ⊆ X') :
    cubeInterior M1 N₁ L q j X ⊆ cubeInterior M1 N₁ L q j X' := fun _ hx =>
  mem_cubeInterior X' |>.2 fun y hy => h ((mem_cubeInterior X).1 hx y hy)

theorem nearStep_mono {n : ℕ} {A A' : Finset (Torus d (M1 * N₁ * L ^ q))} (h : A ⊆ A') :
    nearStep M1 N₁ L q n A ⊆ nearStep M1 N₁ L q n A' := fun _ hx => by
  obtain ⟨y, hy, hd⟩ := mem_nearStep.1 hx
  exact mem_nearStep.2 ⟨y, h hy, hd⟩

theorem minLayerAux_mono (h : X ⊆ X') (t : ℕ) :
    minLayerAux M1 N₁ L q j X t ⊆ minLayerAux M1 N₁ L q j X' t := by
  induction t with
  | zero => exact cubeInterior_mono h
  | succ t ih => exact nearStep_mono ih

theorem minLayer_mono (h : X ⊆ X') (n : ℕ) :
    minLayer M1 N₁ L q j X n ⊆ minLayer M1 N₁ L q j X' n := by
  classical
  unfold minLayer
  split_ifs
  · exact minLayerAux_mono h _
  · exact Finset.Subset.refl _

/-- **Lemma II.2.3 (b)** (monotonicity): `X ⊆ X'` gives `𝔹_j(X) ≺ 𝔹_j(X')`. -/
theorem minimalGenSet_mono (hj : j ≤ q) (h : X ⊆ X') :
    Background.Precedes (minimalGenSet hj X) (minimalGenSet hj X') :=
  fun n _ _ => minLayer_mono h n

end Mono

/-! ### Lemma II.2.3 (c): range and locality -/

section Range

variable {j : ℕ} (X : Finset (Torus d (M1 * N₁ * L ^ q)))

private theorem mul_sub_add (c P : ℕ) (hc : 1 ≤ c) : (c - 1) * P + P = c * P := by
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem five_le {M1 j : ℕ} (hL : 2 ≤ L) :
    (5 * L + 1) * (M1 * L ^ j) ≤ (L - 1) * (11 * M1 * L ^ j) := by
  obtain ⟨e, rfl⟩ : ∃ e, L = e + 2 := ⟨L - 2, by omega⟩
  have : e + 2 - 1 = e + 1 := by omega
  rw [this]
  nlinarith [Nat.zero_le (M1 * (e + 2) ^ j), Nat.zero_le e]

/-- A site of the `n`-th step of the recursion is within `(5 L + 1) M1 L ^ n` of the previous
layer. -/
theorem supDist_le_of_mem_nearStep {n : ℕ} (hn : n ≤ q)
    {x y : Torus d (M1 * N₁ * L ^ q)}
    (hd : supDist (fineCubeIdx M1 N₁ L q n x) (fineCubeIdx M1 N₁ L q n y) ≤ 5 * L) :
    supDist x y ≤ (5 * L + 1) * (M1 * L ^ n) := by
  have h := supDist_le_blockMap (d := d) (fine_eq_cube hn) x y
  unfold fineCubeIdx at hd
  have hN : (L ^ n * M1) * supDist (blockMap (L ^ n * M1) (N₁ * L ^ (q - n)) x)
      (blockMap (L ^ n * M1) (N₁ * L ^ (q - n)) y) ≤ (L ^ n * M1) * (5 * L) :=
    Nat.mul_le_mul_left _ hd
  have hN1 : L ^ n * M1 - 1 ≤ L ^ n * M1 := Nat.sub_le _ _
  calc supDist x y ≤ (L ^ n * M1) * (5 * L) + L ^ n * M1 := by omega
    _ = (5 * L + 1) * (M1 * L ^ n) := by ring

theorem exists_near_aux (hj : j ≤ q) : ∀ (t n : ℕ), n + t = j →
    ∀ x ∈ minLayer M1 N₁ L q j X n, ∃ y ∈ X,
      (L - 1) * supDist x y + (5 * L + 1) * (M1 * L ^ n) ≤ (5 * L + 1) * (M1 * L ^ j) := by
  intro t
  induction t with
  | zero =>
    intro n hn x hx
    have : n = j := by omega
    subst this
    rw [minLayer_self] at hx
    exact ⟨x, cubeInterior_subset X hx, by simp [supDist_self]⟩
  | succ t ih =>
    intro n hn x hx
    have hnj : n < j := by omega
    rw [minLayer_of_lt X hnj, mem_nearStep] at hx
    obtain ⟨y, hy, hd⟩ := hx
    obtain ⟨x0, hx0, h0⟩ := ih (n + 1) (by omega) y hy
    refine ⟨x0, hx0, ?_⟩
    have h1 := supDist_le_of_mem_nearStep (d := d) (by omega : n ≤ q) hd
    have h2 := supDist_triangle x y x0
    have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have h3 : (L - 1) * supDist x x0 ≤ (L - 1) * ((5 * L + 1) * (M1 * L ^ n)) +
        (L - 1) * supDist y x0 := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (h2.trans (Nat.add_le_add_right h1 _))
    have h4 := mul_sub_add L ((5 * L + 1) * (M1 * L ^ n)) hL1
    have h5 : L * ((5 * L + 1) * (M1 * L ^ n)) = (5 * L + 1) * (M1 * L ^ (n + 1)) := by ring
    omega

/-- **Lemma II.2.3 (c)** (range), precise form: a site of `Ω_n(X)` is within `ρ` of `X` with
`(L - 1) ρ + (5 L + 1) M1 L ^ n ≤ (5 L + 1) M1 L ^ j`; in particular for `L ≥ 2` within
`11 M1 L ^ j` (the value `r_q` of the document). -/
theorem exists_near_of_mem_minLayer (hj : j ≤ q) {n : ℕ} (hnj : n ≤ j)
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ minLayer M1 N₁ L q j X n) :
    ∃ y ∈ X, (L - 1) * supDist x y + (5 * L + 1) * (M1 * L ^ n) ≤
      (5 * L + 1) * (M1 * L ^ j) :=
  exists_near_aux X hj (j - n) n (by omega) x hx

theorem exists_near_of_mem_minLayer' (hL : 2 ≤ L) (hj : j ≤ q) {n : ℕ} (hnj : n ≤ j)
    {x : Torus d (M1 * N₁ * L ^ q)} (hx : x ∈ minLayer M1 N₁ L q j X n) :
    ∃ y ∈ X, supDist x y ≤ 11 * M1 * L ^ j := by
  obtain ⟨y, hy, h⟩ := exists_near_of_mem_minLayer X hj hnj hx
  refine ⟨y, hy, ?_⟩
  have h1 : (L - 1) * supDist x y ≤ (L - 1) * (11 * M1 * L ^ j) := by
    have := five_le (M1 := M1) (j := j) hL
    omega
  exact Nat.le_of_mul_le_mul_left h1 (by omega)

theorem local_aux (hL : 2 ≤ L) (hj : j ≤ q) {X' : Finset (Torus d (M1 * N₁ * L ^ q))} :
    ∀ (t n : ℕ), n + t = j → ∀ (x : Torus d (M1 * N₁ * L ^ q)) (r : ℕ),
      (5 * L + 1) * (M1 * L ^ j) + (L - 1) * (M1 * L ^ j) ≤
        (L - 1) * r + (5 * L + 1) * (M1 * L ^ n) →
      (∀ y, supDist x y ≤ r → y ∈ X → y ∈ X') →
      x ∈ minLayer M1 N₁ L q j X n → x ∈ minLayer M1 N₁ L q j X' n := by
  have hB : 0 < M1 * L ^ j := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  intro t
  induction t with
  | zero =>
    intro n hn x r hr hag hx
    have : n = j := by omega
    subst this
    rw [minLayer_self] at hx ⊢
    have hrB : M1 * L ^ n ≤ r := by
      have h1 : (L - 1) * (M1 * L ^ n) ≤ (L - 1) * r := by omega
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    refine (mem_cubeInterior X').2 fun y hy => ?_
    have hxy : supDist y x ≤ L ^ n * M1 - 1 := by
      have := supDist_le_of_blockMap_eq (d := d) (fine_eq_cube hj) (x := y) (y := x) hy
      exact this
    rw [supDist_comm] at hxy
    refine hag y ?_ ((mem_cubeInterior X).1 hx y hy)
    have : L ^ n * M1 = M1 * L ^ n := Nat.mul_comm _ _
    omega
  | succ t ih =>
    intro n hn x r hr hag hx
    have hnj : n < j := by omega
    rw [minLayer_of_lt X hnj, mem_nearStep] at hx
    rw [minLayer_of_lt X' hnj, mem_nearStep]
    obtain ⟨y, hy, hd⟩ := hx
    have h1 := supDist_le_of_mem_nearStep (d := d) (by omega : n ≤ q) hd
    have hPn : (5 * L + 1) * (M1 * L ^ n) ≤ r := by
      by_contra hlt
      push Not at hlt
      have h2 : (L - 1) * r < (L - 1) * ((5 * L + 1) * (M1 * L ^ n)) :=
        Nat.mul_lt_mul_of_pos_left hlt (by omega)
      have h3 := mul_sub_add L ((5 * L + 1) * (M1 * L ^ n)) (by omega)
      have h4 : L * ((5 * L + 1) * (M1 * L ^ n)) = (5 * L + 1) * (M1 * L ^ (n + 1)) := by ring
      have h5 : (5 * L + 1) * (M1 * L ^ (n + 1)) ≤ (5 * L + 1) * (M1 * L ^ j) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hnj))
      have h6 : (L - 1) * (M1 * L ^ j) ≥ 1 * 1 :=
        Nat.mul_le_mul (by omega) hB
      omega
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + (5 * L + 1) * (M1 * L ^ n) := ⟨r - (5 * L + 1) * (M1 * L ^ n), by omega⟩
    have h3 := mul_sub_add L ((5 * L + 1) * (M1 * L ^ n)) (by omega)
    have h4 : L * ((5 * L + 1) * (M1 * L ^ n)) = (5 * L + 1) * (M1 * L ^ (n + 1)) := by ring
    have hy' : y ∈ minLayer M1 N₁ L q j X' (n + 1) := by
      refine ih (n + 1) (by omega) y r' ?_ ?_ hy
      · rw [Nat.mul_add] at hr
        omega
      · intro w hw hwX
        refine hag w ?_ hwX
        have := supDist_triangle x y w
        omega
    exact ⟨y, hy', hd⟩

/-- **Lemma II.2.3 (c)** (locality): whether `x` lies in `Ω_n(X)` depends only on `X` within
sup-distance `12 M1 L ^ j` of `x` (the document's `r_q = 11 M1 L ^ j` plus the width `M1 L ^ j` of
the cube in the definition of `Ω_j`). -/
theorem minLayer_local (hL : 2 ≤ L) (hj : j ≤ q) {X' : Finset (Torus d (M1 * N₁ * L ^ q))}
    {n : ℕ} (hnj : n ≤ j) {x : Torus d (M1 * N₁ * L ^ q)}
    (h : ∀ y, supDist x y ≤ 12 * M1 * L ^ j → (y ∈ X ↔ y ∈ X')) :
    x ∈ minLayer M1 N₁ L q j X n ↔ x ∈ minLayer M1 N₁ L q j X' n := by
  have h5 := five_le (M1 := M1) (j := j) hL
  have hB : 0 < M1 * L ^ j := Nat.pos_of_ne_zero (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have key : (5 * L + 1) * (M1 * L ^ j) + (L - 1) * (M1 * L ^ j) ≤
      (L - 1) * (12 * M1 * L ^ j) + (5 * L + 1) * (M1 * L ^ n) := by
    have e : (L - 1) * (12 * M1 * L ^ j) = (L - 1) * (11 * M1 * L ^ j) + (L - 1) * (M1 * L ^ j) := by
      ring
    omega
  constructor
  · exact local_aux X hL hj (j - n) n (by omega) x _ key fun y hy hyX => (h y hy).1 hyX
  · exact local_aux X' hL hj (j - n) n (by omega) x _ key fun y hy hyX => (h y hy).2 hyX

/-- Sites at `π`-cube index distance `≤ 1` are within sup-distance `P`. -/
theorem supDist_blockMap_le_one {P m' : ℕ} [NeZero m'] (hP : M1 * N₁ * L ^ q = P * m')
    {D : ℕ} (hD : D ≤ P) (x y : Torus d (M1 * N₁ * L ^ q)) (hxy : supDist x y ≤ D) :
    supDist (blockMap P m' x) (blockMap P m' y) ≤ 1 := by
  have h := supDist_blockMap_le (d := d) hP x y
  refine h.trans ?_
  have hPpos : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · exfalso
      have : 0 < M1 * N₁ * L ^ q := Nat.pos_of_ne_zero (by
        have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne N₁; positivity)
      rw [hP, h0] at this; simp at this
    · exact h0
  have : (supDist x y + P - 1) / P < 2 := by
    rw [Nat.div_lt_iff_lt_mul hPpos]; omega
  omega

/-- **Lemma II.2.3 (c)** (locality in `π_j`-cubes): `Ω_n(X) ∩ E` depends only on `X ∩ E^{∼1}`.
Here the `π_j`-cubes have side `L ^ j M` with `12 M1 ≤ M` (`M = L ^ m0 M1`, `L ^ m0 ≥ 12`). -/
theorem minLayer_local_pi (hL : 2 ≤ L) (hj : j ≤ q) {M : ℕ} (hM : 12 * M1 ≤ M)
    {m' : ℕ} [NeZero m'] (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m')
    {X' : Finset (Torus d (M1 * N₁ * L ^ q))} {n : ℕ} (hnj : n ≤ j)
    {x : Torus d (M1 * N₁ * L ^ q)}
    (h : ∀ y, supDist (blockMap (L ^ j * M) m' x) (blockMap (L ^ j * M) m' y) ≤ 1 →
      (y ∈ X ↔ y ∈ X')) :
    x ∈ minLayer M1 N₁ L q j X n ↔ x ∈ minLayer M1 N₁ L q j X' n := by
  refine minLayer_local X hL hj hnj fun y hy => h y ?_
  refine supDist_blockMap_le_one hP (D := 12 * M1 * L ^ j) ?_ x y hy
  calc 12 * M1 * L ^ j = L ^ j * (12 * M1) := by ring
    _ ≤ L ^ j * M := Nat.mul_le_mul_left _ hM

/-- **Lemma II.2.3 (c)** (range): the sites of the data of `𝔹_j(X)` (`Ω₁ ∪ C(Ω₁)`) lie within
`11 M1 L ^ j + 1` of `X`. -/
theorem dataSites_near (hL : 2 ≤ L) (hj : j ≤ q) {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ Background.dataSites (minimalGenSet hj X)) :
    ∃ y ∈ X, supDist x y ≤ 11 * M1 * L ^ j + 1 := by
  have hΩ : ∀ z ∈ (minimalGenSet hj X).Ω 1, ∃ y ∈ X, supDist z y ≤ 11 * M1 * L ^ j := by
    intro z hz
    rw [minimalGenSet_Ω] at hz
    by_cases h1 : 1 ≤ j
    · exact exists_near_of_mem_minLayer' X hL hj h1 hz
    · rw [minLayer_of_gt X (by omega)] at hz
      exact absurd hz (Finset.notMem_empty _)
  rcases (Background.mem_dataSites _).1 hx with h | h
  · obtain ⟨y, hy, hd⟩ := hΩ x h
    exact ⟨y, hy, by omega⟩
  · obtain ⟨-, x', hx', hadj⟩ := (Background.mem_collar _).1 h
    obtain ⟨y, hy, hd⟩ := hΩ x' hx'
    have h1 : supDist x x' ≤ 1 := by
      have h2 := supDist_le_torusDist x x'
      have h3 := Multiscale.Adj.torusDist_le hadj.symm
      have : (supDist x x' : ℝ) ≤ 1 := h2.trans h3
      exact_mod_cast this
    exact ⟨y, hy, (supDist_triangle x x' y).trans (by omega)⟩

/-- **Lemma II.2.3 (c)** (range, in `π_j`-cubes): the data sites `Ω₁ ∪ C(Ω₁)` of `𝔹_j(X)` lie in
`X^{∼1}`: each is in the `π_j`-cube of, or an adjacent `π_j`-cube to, a site of `X`
(`π_j`-cubes of side `L ^ j M`, `12 M1 ≤ M`). -/
theorem minimalGenSet_range (hL : 2 ≤ L) (hj : j ≤ q) {M : ℕ} (hM : 12 * M1 ≤ M) {m' : ℕ}
    [NeZero m'] (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m') {x : Torus d (M1 * N₁ * L ^ q)}
    (hx : x ∈ Background.dataSites (minimalGenSet hj X)) :
    ∃ y ∈ X, supDist (blockMap (L ^ j * M) m' x) (blockMap (L ^ j * M) m' y) ≤ 1 := by
  obtain ⟨y, hy, hd⟩ := dataSites_near X hL hj hx
  refine ⟨y, hy, supDist_blockMap_le_one hP (D := 11 * M1 * L ^ j + 1) ?_ x y hd⟩
  have hB : 1 ≤ M1 * L ^ j := Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have h1 : L ^ j * (12 * M1) ≤ L ^ j * M := Nat.mul_le_mul_left _ hM
  have h2 : L ^ j * (12 * M1) = 12 * (M1 * L ^ j) := by ring
  have h3 : 11 * M1 * L ^ j = 11 * (M1 * L ^ j) := by ring
  omega

end Range

/-! ### Lemma II.2.3 (d): disjoint unions -/

section Union

variable {j : ℕ}

theorem nearStep_union {n : ℕ} (A B : Finset (Torus d (M1 * N₁ * L ^ q))) :
    nearStep M1 N₁ L q n (A ∪ B) = nearStep M1 N₁ L q n A ∪ nearStep M1 N₁ L q n B := by
  ext x
  simp only [Finset.mem_union, mem_nearStep, or_and_right, exists_or]

/-- Two sites whose `π`-cubes are at index distance `≥ 3` are at sup-distance `≥ 2P + 1`. -/
theorem two_mul_add_one_le_supDist {P m' : ℕ} [NeZero m'] (hP : M1 * N₁ * L ^ q = P * m')
    {x y : Torus d (M1 * N₁ * L ^ q)}
    (h : 3 ≤ supDist (blockMap P m' x) (blockMap P m' y)) : 2 * P + 1 ≤ supDist x y := by
  have hPpos : 0 < P := by
    rcases Nat.eq_zero_or_pos P with h0 | h0
    · exfalso
      have : 0 < M1 * N₁ * L ^ q := Nat.pos_of_ne_zero (by
        have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne N₁; positivity)
      rw [hP, h0] at this; simp at this
    · exact h0
  have h1 := (supDist_blockMap_le (d := d) hP x y)
  have h2 : 3 ≤ (supDist x y + P - 1) / P := h.trans h1
  rw [Nat.le_div_iff_mul_le hPpos] at h2
  omega

theorem cubeInterior_union (hj : j ≤ q) {M : ℕ} (hM : M1 ≤ M) {m' : ℕ} [NeZero m']
    (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m') {X₁ X₂ : Finset (Torus d (M1 * N₁ * L ^ q))}
    (hfar : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂,
      3 ≤ supDist (blockMap (L ^ j * M) m' x₁) (blockMap (L ^ j * M) m' x₂)) :
    cubeInterior M1 N₁ L q j (X₁ ∪ X₂) =
      cubeInterior M1 N₁ L q j X₁ ∪ cubeInterior M1 N₁ L q j X₂ := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hxX := cubeInterior_subset _ hx
    have key : ∀ (Y Z : Finset (Torus d (M1 * N₁ * L ^ q))),
        (∀ a ∈ Y, ∀ b ∈ Z, 2 * (L ^ j * M) + 1 ≤ supDist a b) →
        x ∈ Y → x ∈ cubeInterior M1 N₁ L q j (Y ∪ Z) → x ∈ cubeInterior M1 N₁ L q j Y := by
      intro Y Z hYZ hxY hxYZ
      refine (mem_cubeInterior Y).2 fun y hy => ?_
      have hyYZ := (mem_cubeInterior _).1 hxYZ y hy
      rcases Finset.mem_union.1 hyYZ with h | h
      · exact h
      · exfalso
        have h1 := hYZ x hxY y h
        have h2 : supDist y x ≤ L ^ j * M1 - 1 := by
          unfold fineCubeIdx at hy
          exact supDist_le_of_blockMap_eq (d := d) (fine_eq_cube hj) hy
        rw [supDist_comm] at h2
        have h3 : L ^ j * M1 ≤ L ^ j * M := Nat.mul_le_mul_left _ hM
        omega
    rcases Finset.mem_union.1 hxX with h | h
    · exact Finset.mem_union_left _ (key X₁ X₂ (fun a ha b hb =>
        two_mul_add_one_le_supDist hP (hfar a ha b hb)) h hx)
    · refine Finset.mem_union_right _ (key X₂ X₁ (fun a ha b hb => ?_) h ?_)
      · rw [supDist_comm]
        exact two_mul_add_one_le_supDist hP (hfar b hb a ha)
      · rwa [Finset.union_comm] at hx
  · exact Finset.union_subset (cubeInterior_mono Finset.subset_union_left)
      (cubeInterior_mono Finset.subset_union_right)

theorem minLayerAux_union (hj : j ≤ q) {M : ℕ} (hM : M1 ≤ M) {m' : ℕ} [NeZero m']
    (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m') {X₁ X₂ : Finset (Torus d (M1 * N₁ * L ^ q))}
    (hfar : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂,
      3 ≤ supDist (blockMap (L ^ j * M) m' x₁) (blockMap (L ^ j * M) m' x₂)) (t : ℕ) :
    minLayerAux M1 N₁ L q j (X₁ ∪ X₂) t =
      minLayerAux M1 N₁ L q j X₁ t ∪ minLayerAux M1 N₁ L q j X₂ t := by
  induction t with
  | zero => exact cubeInterior_union hj hM hP hfar
  | succ t ih =>
    show nearStep _ _ _ _ _ (minLayerAux M1 N₁ L q j (X₁ ∪ X₂) t) = _
    rw [ih, nearStep_union]
    rfl

/-- **Lemma II.2.3 (d)** (disjoint unions): if the `π_j`-cubes of `X₁` and `X₂` are at index
distance `≥ 3` then `Ω_n(X₁ ∪ X₂) = Ω_n(X₁) ∪ Ω_n(X₂)`. -/
theorem minLayer_union (hj : j ≤ q) {M : ℕ} (hM : M1 ≤ M) {m' : ℕ} [NeZero m']
    (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m') {X₁ X₂ : Finset (Torus d (M1 * N₁ * L ^ q))}
    (hfar : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂,
      3 ≤ supDist (blockMap (L ^ j * M) m' x₁) (blockMap (L ^ j * M) m' x₂)) (n : ℕ) :
    minLayer M1 N₁ L q j (X₁ ∪ X₂) n = minLayer M1 N₁ L q j X₁ n ∪ minLayer M1 N₁ L q j X₂ n := by
  classical
  unfold minLayer
  split_ifs
  · exact minLayerAux_union hj hM hP hfar _
  · simp

/-- **Lemma II.2.3 (d)**: the data sites of `𝔹_j(X₁)` and `𝔹_j(X₂)` are at sup-distance `≥ 2`
(so they are disjoint and no bond joins them) when the `π_j`-cubes of `X₁`, `X₂` are at index
distance `≥ 3`, `L ^ m0 ≥ 14` (`14 M1 ≤ M`). -/
theorem dataSites_far (hL : 2 ≤ L) (hj : j ≤ q) {M : ℕ} (hM : 14 * M1 ≤ M) {m' : ℕ} [NeZero m']
    (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m') {X₁ X₂ : Finset (Torus d (M1 * N₁ * L ^ q))}
    (hfar : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂,
      3 ≤ supDist (blockMap (L ^ j * M) m' x₁) (blockMap (L ^ j * M) m' x₂))
    {u w : Torus d (M1 * N₁ * L ^ q)} (hu : u ∈ Background.dataSites (minimalGenSet hj X₁))
    (hw : w ∈ Background.dataSites (minimalGenSet hj X₂)) : 2 ≤ supDist u w := by
  obtain ⟨x₁, h₁, d₁⟩ := dataSites_near X₁ hL hj hu
  obtain ⟨x₂, h₂, d₂⟩ := dataSites_near X₂ hL hj hw
  have h3 := two_mul_add_one_le_supDist hP (hfar x₁ h₁ x₂ h₂)
  have h4 := supDist_triangle x₁ u x₂
  have h5 := supDist_triangle u w x₂
  have h6 := supDist_comm x₁ u
  have h7 := supDist_comm w x₂
  have hB : 1 ≤ M1 * L ^ j := Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne L; have := NeZero.ne M1; positivity)
  have h8 : L ^ j * (14 * M1) ≤ L ^ j * M := Nat.mul_le_mul_left _ hM
  have h9 : L ^ j * (14 * M1) = 14 * (M1 * L ^ j) := by ring
  have h10 : 11 * M1 * L ^ j = 11 * (M1 * L ^ j) := by ring
  omega

end Union

/-- **Lemma II.2.3 (d)** (disjoint unions): the layers of `𝔹_j(X₁ ∪ X₂)` are the unions of those
of `𝔹_j(X₁)`, `𝔹_j(X₂)` and the data sites of the two are at sup-distance `≥ 2`, when the
`π_j`-cubes of `X₁`, `X₂` are at index distance `≥ 3` (`14 M1 ≤ M`). -/
theorem minimalGenSet_disjoint {j : ℕ} (hL : 2 ≤ L) (hj : j ≤ q) {M : ℕ} (hM : 14 * M1 ≤ M) {m' : ℕ}
    [NeZero m'] (hP : M1 * N₁ * L ^ q = (L ^ j * M) * m')
    {X₁ X₂ : Finset (Torus d (M1 * N₁ * L ^ q))}
    (hfar : ∀ x₁ ∈ X₁, ∀ x₂ ∈ X₂,
      3 ≤ supDist (blockMap (L ^ j * M) m' x₁) (blockMap (L ^ j * M) m' x₂)) :
    (∀ n, (minimalGenSet hj (X₁ ∪ X₂)).Ω n =
      (minimalGenSet hj X₁).Ω n ∪ (minimalGenSet hj X₂).Ω n) ∧
    ∀ u ∈ Background.dataSites (minimalGenSet hj X₁), ∀ w ∈ Background.dataSites (minimalGenSet hj X₂),
      2 ≤ supDist u w :=
  ⟨fun n => minLayer_union hj (by omega : M1 ≤ M) hP hfar n,
    fun _ hu _ hw => dataSites_far hL hj hM hP hfar hu hw⟩

end Balaban.LargeField
