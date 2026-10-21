/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.GsSpecDef
public import Balaban.LargeField.Background.MinimalGenSet

/-!
# The local generating set `𝔹_j(X̂)` of a class polymer (ruling R13)

Early file (imported by `Def6v2`): the specification `HatSpec` of the generating set attached to a
level-`j` polymer `X` by the small-field class (ruling R13, 2026-10-21): it is the minimal generating
set `𝔹_j(X̂)` of P3 (4.4)–(4.6) (the layers `minLayer` of `LargeField.minimalGenSet`) of the set

`X̂ = X` thickened by `⌊L/2⌋` cells of `𝒟_j` in every direction.

It contains `X` and the `π'_j`-cube `□(y)` (side `L` cells) whose central cell is the cell of `y`
(P1 p. 152) for every `y ∈ X`, and therefore the neighbours `y + L^j e_μ` read by the irrelevant part
of the term of `(j, y, X)` (`stPlus_mem_cubeAt`); it is invariant under the paving symmetries of
scale `j` (the cube `□(y)` alone is not, for `L` even).  The cover set
`X ∪ □(y)` of every label `(j, y, X)` of the class chain lies in the top layer of `𝔹_j(X̂)`.  The
cubes `𝒞_n` of `𝔹_j(X̂)` have side `L^{m₁ + s} L^n`, `s = hatScale L m₁ ϱ` the least exponent for
which the minimal set has the separation `ϱ` of the class (`ϱ ≤ 5 L L^{m₁ + s}`).

* `torusCast`: the identification of two tori with equal side through the values of the coordinates
  (moved here from `GsSpecPoly`, unchanged);
* `hatSet`, `hatScale`, `HatSpec`; `hatSpec_of_le` (nothing is asked when `m₀ ≤ s`).

The specification is stated through the layers, on the torus of side `L^{m₁+s} N₁' L^k`
(`N₁' L^{m₁+s} = N₁ L^{m₁}`), so that it needs no generating-set cast; it is the cast local set
`castG hc (localB j … X̂ hsep)` of `GsSpecHatCast` (`hatSpec_castLocalB`, `HatSpec.eq_castLocalB`).
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Finset

section Cast

variable {d : ℕ}

/-- The identification of two tori with equal side (`ZMod` coordinates through their values). -/
def torusCast {a b : ℕ} (y : Torus d a) : Torus d b := fun μ => (((y μ).val : ℕ) : ZMod b)

theorem torusCast_torusCast {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) (y : Torus d a) :
    (torusCast (torusCast y : Torus d b) : Torus d a) = y := by
  subst h
  funext μ
  simp [torusCast]

theorem torusCast_val {a b : ℕ} [NeZero a] (h : a = b) (y : Torus d a) (μ : Fin d) :
    ((torusCast y : Torus d b) μ).val = (y μ).val := by
  subst h
  simp [torusCast]

end Cast

section Hat

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The set `X̂`** of a level-`j` polymer `X`: `X` thickened by `⌊L/2⌋` cells of `𝒟_j` (side
`c = cellSide L m₀ m₁ j`) in every direction, `⋃_{y ∈ X} box (cbase_c y - ⌊L/2⌋ c, (2⌊L/2⌋ + 1) c)`.
It contains the `π'_j`-cube `□(y)` (side `L c`, base `cbase_c y - ⌊L/2⌋ c`) of every `y ∈ X`
(`cubeAt_subset_hatSet`), and it is invariant under the paving symmetries of scale `j`. -/
def hatSet (m₀ j : ℕ) (X : Set (CTorus d L N₁ m₁ k)) : Set (CTorus d L N₁ m₁ k) :=
  {z | ∃ y ∈ X, z ∈ box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
    ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j)}

open Classical in
/-- **The cube exponent of the local generating sets of the class**: the least `s` with
`ϱ ≤ 5 L ⋅ L^{m₁ + s}` (the separation of the minimal generating set with cubes of side
`L^{m₁+s} L^n`, `LargeField.minSep`); `0` if there is none. -/
noncomputable def hatScale (L m₁ : ℕ) (ϱ : ℝ) : ℕ :=
  if h : ∃ s : ℕ, ϱ ≤ LargeField.minSep L (L ^ (m₁ + s)) then Nat.find h else 0

open Classical in
/-- **The specification `HatSpec` of the generating set of a class polymer** (ruling R13): when the
cube exponent `s = hatScale L m₁ ϱ` is below `m₀` (the cubes of `𝔹_j` are strictly finer than the
cells of `𝒟_j`, side `L^{m₁+s+j}` against `L^{m₀+m₁+j}`; the class chain has `s ≤ 4 < 7 ≤ m₀`) and
the minimal set has the separation `ϱ`, then on the torus of side `L^{m₁+s} N₁' L^k`
(`N₁' L^{m₁+s} = N₁ L^{m₁}`) the layers of `G` are those of the minimal generating set `𝔹_j(X̂)` of
P3 (4.4)–(4.6): `Ω_j` the union of the `𝒞_j`-cubes inside `X̂`, `Ω_n` for `n < j` the union of the
`𝒞_n`-cubes at cube-index distance `≤ 5L` from `Ω_{n+1}`, nothing above `j`. -/
def HatSpec (m₀ j : ℕ) (X : Set (CTorus d L N₁ m₁ k))
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) : Prop :=
  hatScale L m₁ ϱ < m₀ → ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)) →
    ∀ (N₁' : ℕ) [NeZero N₁'], N₁' * L ^ (m₁ + hatScale L m₁ ϱ) = N₁ * L ^ m₁ →
      ∀ (n : ℕ) (x : CTorus d L N₁ m₁ k), x ∈ G.Ω n ↔
        (torusCast x : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁' * L ^ k)) ∈
          LargeField.minLayer (L ^ (m₁ + hatScale L m₁ ϱ)) N₁' L k j
            (Finset.univ.filter fun y : Torus d (L ^ (m₁ + hatScale L m₁ ϱ) * N₁' * L ^ k) =>
              (torusCast y : CTorus d L N₁ m₁ k) ∈ hatSet m₀ j X) n

/-- **`HatSpec` holds trivially when the cubes are not finer than the cells** (`m₀ ≤ s`): the class
then asks nothing of its generating sets beyond `GsSpecStrong` (e.g. the witnesses with `m₀ = 0`). -/
theorem hatSpec_of_le {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ k)}
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} (h : m₀ ≤ hatScale L m₁ ϱ) : HatSpec m₀ j X G :=
  fun hlt => absurd hlt (not_lt.2 h)

/-- The cube exponent satisfies the separation when some exponent does. -/
theorem minSep_hatScale {L m₁ : ℕ} {ϱ : ℝ} {s : ℕ} (hs : ϱ ≤ LargeField.minSep L (L ^ (m₁ + s))) :
    ϱ ≤ LargeField.minSep L (L ^ (m₁ + hatScale L m₁ ϱ)) := by
  classical
  have h : ∃ s : ℕ, ϱ ≤ LargeField.minSep L (L ^ (m₁ + s)) := ⟨s, hs⟩
  unfold hatScale
  split_ifs
  exact Nat.find_spec h

/-- The cube exponent is at most every exponent with the separation. -/
theorem hatScale_le {L m₁ : ℕ} {ϱ : ℝ} {s : ℕ} (hs : ϱ ≤ LargeField.minSep L (L ^ (m₁ + s))) :
    hatScale L m₁ ϱ ≤ s := by
  classical
  have h : ∃ s : ℕ, ϱ ≤ LargeField.minSep L (L ^ (m₁ + s)) := ⟨s, hs⟩
  unfold hatScale
  split_ifs
  exact Nat.find_min' h hs

/-- **`y ∈ □(y)`**: the `π'_j`-cube centred at the cell of `y` contains `y`. -/
theorem self_mem_cubeAt {m₀ j : ℕ} (y : CTorus d L N₁ m₁ k) :
    y ∈ box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j) := by
  have hcs : 0 < cellSide L m₀ m₁ j := cellSide_pos m₀ m₁ j
  refine ⟨fun μ => L / 2 * cellSide L m₀ m₁ j + (y μ).val % cellSide L m₀ m₁ j,
    fun μ => ?_, ?_⟩
  · have h1 : (y μ).val % cellSide L m₀ m₁ j < cellSide L m₀ m₁ j := Nat.mod_lt _ hcs
    have h2 : L / 2 + 1 ≤ L := by have := NeZero.pos L; omega
    calc L / 2 * cellSide L m₀ m₁ j + (y μ).val % cellSide L m₀ m₁ j
        < L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j := by omega
      _ = (L / 2 + 1) * cellSide L m₀ m₁ j := by ring
      _ ≤ L * cellSide L m₀ m₁ j := Nat.mul_le_mul_right _ h2
  · have e : (fun μ => L / 2 * cellSide L m₀ m₁ j + (y μ).val % cellSide L m₀ m₁ j) =
        (fun _ => L / 2 * cellSide L m₀ m₁ j) + fun μ => (y μ).val % cellSide L m₀ m₁ j := rfl
    rw [e, natT_add, cbase_eq_sub]
    abel

/-- `X ⊆ X̂`. -/
theorem subset_hatSet (m₀ j : ℕ) (X : Set (CTorus d L N₁ m₁ k)) : X ⊆ hatSet m₀ j X :=
  fun y hy => ⟨y, hy, box_mono _
    (Nat.mul_le_mul_right _ (by omega : L ≤ 2 * (L / 2) + 1)) (self_mem_cubeAt y)⟩

omit [NeZero L] [NeZero N₁] in
/-- `□(y) ⊆ X̂` for `y ∈ X`. -/
theorem cubeAt_subset_hatSet (m₀ j : ℕ) {X : Set (CTorus d L N₁ m₁ k)}
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X) :
    box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j) ⊆ hatSet m₀ j X :=
  fun _ hz => ⟨y, hy, box_mono _
    (Nat.mul_le_mul_right _ (by omega : L ≤ 2 * (L / 2) + 1)) hz⟩

omit [NeZero L] [NeZero N₁] in
/-- `X̂` is monotone in `X`. -/
theorem hatSet_mono (m₀ j : ℕ) {X Y : Set (CTorus d L N₁ m₁ k)} (h : X ⊆ Y) :
    hatSet m₀ j X ⊆ hatSet m₀ j Y := by
  rintro z ⟨y, hy, hz⟩
  exact ⟨y, h hy, hz⟩

end Hat

end Balaban.SmallField.GsSpec
