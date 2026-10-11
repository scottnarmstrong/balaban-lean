/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.GeneratingSet
public import Balaban.Multiscale.Coercivity
public import Balaban.Background.BlockGeometry
public import Balaban.Background.Bump
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cube alignment, the cast of tori and `dropTop` (LOCALIZATION.md §1.1, §1.1b)

* `Balaban.Localization.castT`: the identification of two tori `Torus d n` and `Torus d n'` with
  `n = n'`; its properties are proved by `subst`.
* `Balaban.Localization.CubeAligned G m₁`: every `Ω_j` is a union of cubes of side
  `M₁ L ^ j = L ^ (j + m₁)` (cubes are the classes of `(x μ).val / L ^ (j + m₁)`), `m₁ ≥ 2`, and
  `L ^ m₁ ∣ N₀` (so that the cubes tile the torus).
* `Balaban.Multiscale.GeneratingSet.dropTop`: the generating set `𝔹_k` of the same torus obtained
  from `𝔹_{k+1}` by forgetting the top layer, as a `GeneratingSet d L (N₀ * L) k ϱ`, with the cast
  lemmas `dropTop_mem_Ω`, `dropTop_layer_of_lt`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background

variable {d : ℕ}

/-- The identification of the tori of equal side. -/
def castT {n n' : ℕ} (h : n = n') (x : Torus d n) : Torus d n' := h ▸ x

section Cast

variable {n n' : ℕ} (h : n = n')

theorem castT_rfl (x : Torus d n) : castT rfl x = x := rfl

theorem castT_val (x : Torus d n) (μ : Fin d) : ((castT h x) μ).val = (x μ).val := by
  subst h; rfl

theorem castT_add (x y : Torus d n) : castT h (x + y) = castT h x + castT h y := by
  subst h; rfl

theorem castT_sub (x y : Torus d n) : castT h (x - y) = castT h x - castT h y := by
  subst h; rfl

theorem castT_single (μ : Fin d) : castT h (Pi.single μ 1 : Torus d n) = Pi.single μ 1 := by
  subst h; rfl

theorem castT_intTorus (w : Fin d → ℤ) : castT h (intTorus w : Torus d n) = intTorus w := by
  subst h; rfl

theorem castT_injective : Function.Injective (castT (d := d) h) := by
  subst h; exact fun _ _ e => e

theorem castT_surjective : Function.Surjective (castT (d := d) h) := by
  subst h; exact fun y => ⟨y, rfl⟩

theorem castT_symm (x : Torus d n) (y : Torus d n') : castT h x = y ↔ x = castT h.symm y := by
  subst h; rfl

theorem castT_castT (x : Torus d n) : castT h.symm (castT h x) = x := by
  subst h; rfl

theorem torusDist_castT [NeZero n] [NeZero n'] (x y : Torus d n) :
    Green.torusDist d n' (castT h x) (castT h y) = Green.torusDist d n x y := by
  subst h; rfl

/-- The cast as an embedding. -/
def castEmb : Torus d n ↪ Torus d n' := ⟨castT h, castT_injective h⟩

end Cast

/-- Two sites are in the same cell of side `a` if their residues have equal quotient by `a`
in every coordinate. -/
def SameCell {n : ℕ} (a : ℕ) (x y : Torus d n) : Prop := ∀ μ, (x μ).val / a = (y μ).val / a

theorem SameCell.refl {n : ℕ} (a : ℕ) (x : Torus d n) : SameCell a x x := fun _ => rfl

theorem SameCell.symm {n a : ℕ} {x y : Torus d n} (h : SameCell a x y) : SameCell a y x :=
  fun μ => (h μ).symm

theorem SameCell.trans {n a : ℕ} {x y z : Torus d n} (h : SameCell a x y) (h' : SameCell a y z) :
    SameCell a x z := fun μ => (h μ).trans (h' μ)

theorem SameCell.mono {n a b : ℕ} (hab : a ∣ b) {x y : Torus d n} (h : SameCell a x y) :
    SameCell b x y := by
  intro μ
  obtain ⟨c, rfl⟩ := hab
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h μ]


theorem castT_castT_symm {n n' : ℕ} (h : n = n') (y : Torus d n') :
    castT h (castT h.symm y) = y := by
  subst h; rfl

section Cells

variable {L N₀ k : ℕ} [NeZero N₀] [NeZero L]

omit [NeZero N₀] [NeZero L] in
/-- Equal cells of side `L ^ m` give equal `m`-blocks. -/
theorem jBlock_eq_of_sameCell {m : ℕ} {x y : Torus d (N₀ * L ^ k)}
    (h : SameCell (L ^ m) x y) : jBlock d L N₀ k m x = jBlock d L N₀ k m y := by
  funext μ
  unfold jBlock
  rw [blockMap_apply, blockMap_apply]
  unfold blockCoord
  rw [h μ]

/-- Equal `m`-blocks give equal cells of side `L ^ m`. -/
theorem sameCell_of_jBlock_eq {m : ℕ} (hm : m ≤ k) {x y : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k m x = jBlock d L N₀ k m y) : SameCell (L ^ m) x y :=
  fun μ => val_div_eq_of_jBlock_eq hm h μ

end Cells

/-- **Def-L1 (cube alignment).**  Every `Ω_j` (`1 ≤ j ≤ k`) is a union of the cubes of side
`M₁ ℓ_j = L ^ (j + m₁)` (the classes of `SameCell (L ^ (j + m₁))`), `M₁ = L ^ m₁`, `m₁ ≥ 2`, and
the cubes tile the torus (`L ^ m₁ ∣ N₀`). -/
structure CubeAligned {L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ k ϱ) (m₁ : ℕ) : Prop where
  two_le : 2 ≤ m₁
  dvd : L ^ m₁ ∣ N₀
  union : ∀ j, 1 ≤ j → j ≤ k → ∀ x x' : Torus d (N₀ * L ^ k),
    SameCell (L ^ (j + m₁)) x x' → (x ∈ G.Ω j ↔ x' ∈ G.Ω j)

namespace CubeAligned

variable {L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {m₁ : ℕ}

/-- A cube-aligned set is block-aligned (`Ω_j` is a union of `j`-blocks). -/
theorem blockUnion' (hG : CubeAligned G m₁) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    {x x' : Torus d (N₀ * L ^ k)} (h : SameCell (L ^ j) x x') : x ∈ G.Ω j ↔ x' ∈ G.Ω j :=
  hG.union j hj hjk x x' (h.mono (pow_dvd_pow L (Nat.le_add_right j m₁)))

/-- Layers are unions of cubes of the same layer. -/
theorem mem_layer_iff (hG : CubeAligned G m₁) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k)
    {x x' : Torus d (N₀ * L ^ k)} (h : SameCell (L ^ (j + m₁)) x x') :
    x ∈ G.layer j ↔ x' ∈ G.layer j := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, hG.union j hj hjk x x' h]
  rcases Nat.lt_or_ge j k with hlt | hge
  · rw [hG.union (j + 1) (by omega) (by omega) x x'
      (h.mono (pow_dvd_pow L (by omega)))]
  · have : j = k := le_antisymm hjk hge
    subst this
    simp [G.top]

end CubeAligned

end Balaban.Localization

namespace Balaban.Multiscale.GeneratingSet

open Balaban Balaban.Localization Balaban.Background

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem side_succ_eq (N₀ L k : ℕ) : N₀ * L ^ (k + 1) = (N₀ * L) * L ^ k := by ring

/-- The domains of `dropTop`: `Ω_j` transported to the torus of side `(N₀ L) L ^ k` for `j ≤ k`,
empty above. -/
def dropTopΩ (G : GeneratingSet d L N₀ (k + 1) ϱ) (j : ℕ) :
    Finset (Torus d ((N₀ * L) * L ^ k)) :=
  if j ≤ k then (G.Ω j).map (castEmb (side_succ_eq N₀ L k)) else ∅

theorem mem_dropTopΩ (G : GeneratingSet d L N₀ (k + 1) ϱ) (j : ℕ)
    (x : Torus d ((N₀ * L) * L ^ k)) :
    x ∈ dropTopΩ G j ↔ j ≤ k ∧ castT (side_succ_eq N₀ L k).symm x ∈ G.Ω j := by
  unfold dropTopΩ
  split_ifs with hj
  · rw [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hj, ?_⟩
      have : castT (side_succ_eq N₀ L k).symm (castEmb (side_succ_eq N₀ L k) a) = a :=
        castT_castT _ a
      rw [this]; exact ha
    · rintro ⟨-, hx⟩
      exact ⟨_, hx, castT_castT_symm _ x⟩
  · simp [hj]

theorem castT_mem_dropTopΩ (G : GeneratingSet d L N₀ (k + 1) ϱ) (j : ℕ)
    (y : Torus d (N₀ * L ^ (k + 1))) :
    castT (side_succ_eq N₀ L k) y ∈ dropTopΩ G j ↔ j ≤ k ∧ y ∈ G.Ω j := by
  rw [mem_dropTopΩ, castT_castT]

/-- **`dropTop`**: the generating set `𝔹_k` (layers `1..k`, `Ω_{k+1} = ∅`) of the same torus,
as a generating set on `Torus d ((N₀ L) L ^ k)`, identified with `Torus d (N₀ L ^ (k+1))` by
`castT (side_succ_eq N₀ L k)`.  The fields are inherited from `G` with the same `ϱ`. -/
def dropTop (G : GeneratingSet d L N₀ (k + 1) ϱ) : GeneratingSet d L (N₀ * L) k ϱ where
  Ω := dropTopΩ G
  top := by simp [dropTopΩ]
  subset := by
    intro j hj1 hjk
    by_cases h : j + 1 ≤ k
    · intro x hx
      rw [mem_dropTopΩ] at hx ⊢
      exact ⟨hjk, G.subset j hj1 (by omega) hx.2⟩
    · intro x hx
      rw [mem_dropTopΩ] at hx
      omega
  blockUnion := by
    intro j hj1 hjk x x' hxx'
    rw [mem_dropTopΩ, mem_dropTopΩ]
    have hc : SameCell (L ^ j) (castT (side_succ_eq N₀ L k).symm x)
        (castT (side_succ_eq N₀ L k).symm x') := by
      intro μ
      rw [castT_val, castT_val]
      exact val_div_eq_of_jBlock_eq hjk hxx' μ
    have := G.blockUnion j hj1 (by omega) _ _ (jBlock_eq_of_sameCell hc)
    rw [this]
  separation := by
    intro j hj1 hjk x hx y hy
    rw [mem_dropTopΩ] at hx hy
    have hx' : castT (side_succ_eq N₀ L k).symm x ∉ G.Ω j := fun h => hx ⟨by omega, h⟩
    have := G.separation j hj1 (by omega) _ hx' _ hy.2
    rwa [← torusDist_castT (side_succ_eq N₀ L k), castT_castT_symm, castT_castT_symm] at this

/-- The layers of `dropTop` below the top are those of `G` (the cast lemma). -/
theorem dropTop_layer_of_lt (G : GeneratingSet d L N₀ (k + 1) ϱ) {j : ℕ} (hj : j < k)
    (y : Torus d (N₀ * L ^ (k + 1))) :
    castT (side_succ_eq N₀ L k) y ∈ (dropTop G).layer j ↔ y ∈ G.layer j := by
  rw [mem_layer, mem_layer]
  change castT (side_succ_eq N₀ L k) y ∈ dropTopΩ G j ∧ castT (side_succ_eq N₀ L k) y ∉
    dropTopΩ G (j + 1) ↔ _
  rw [castT_mem_dropTopΩ, castT_mem_dropTopΩ]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h1, fun h => h2 ⟨by omega, h⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by omega, h1⟩, fun h => h2 h.2⟩

/-- The top layer of `dropTop` is `Ω_k`. -/
theorem dropTop_layer_top (G : GeneratingSet d L N₀ (k + 1) ϱ)
    (y : Torus d (N₀ * L ^ (k + 1))) :
    castT (side_succ_eq N₀ L k) y ∈ (dropTop G).layer k ↔ y ∈ G.Ω k := by
  rw [mem_layer]
  change castT (side_succ_eq N₀ L k) y ∈ dropTopΩ G k ∧ castT (side_succ_eq N₀ L k) y ∉
    dropTopΩ G (k + 1) ↔ _
  rw [castT_mem_dropTopΩ, castT_mem_dropTopΩ]
  simp

end Balaban.Multiscale.GeneratingSet
