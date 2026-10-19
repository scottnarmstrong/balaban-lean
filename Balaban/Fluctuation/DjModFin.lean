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
# Labels with the `π'`-cube structure required through the active sites only (ruling R11)

`DjModFin`: nonempty, nearest-neighbour connected, containing or missing every component of the
holes `Ω^c`, of finite modular size; the sites of `X ∩ Ω` then lie in `π'_j`-cubes inside `X`
(`DjModFin.exists_box`).  The landed class `DjMod` is `DjModFin` plus the `π'_j`-cubes through the
sites of the holes (`djMod_iff_djModFin`).  The counting properties (G1) (`DjModFin.cellCount_le`) and
(G3) (`djModFin_union`) hold with the constants of the landed labels.  Used by the valid labels of
the boundary terms (`Def7.FineValidAt`) and by the transfer across a new hole
(`Spine/LFBdryHole.lean`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-! ### Labels whose `π'`-cube structure is required through the active sites only -/

/-- **What R11 drops.**  A set belongs to the landed `𝒟_j(mod Ω^c)` exactly when it belongs to
`DjModFin` and, in addition, every site of `X ∩ Ω^c` lies in a `π'_j`-cube contained in `X`. -/
theorem djMod_iff_djModFin {Ω X : Set (CTorus d L N₁ m₁ K)} :
    DjMod m₀ j Ω X ↔ DjModFin m₀ j Ω X ∧ ∀ z ∈ X ∩ Ωᶜ, ∃ b, Aligned (cellSide L m₀ m₁ j) b ∧
      z ∈ box b (L * cellSide L m₀ m₁ j) ∧ box b (L * cellSide L m₀ m₁ j) ⊆ X := by
  constructor
  · intro h
    exact ⟨h.djModFin, fun z hz => h.1.2.1 z hz.1⟩
  · rintro ⟨h, hc⟩
    refine ⟨⟨h.1, fun z hz => ?_, h.2.1⟩, h.2.2.1⟩
    by_cases hzΩ : z ∈ Ω
    · exact h.exists_box ⟨hz, hzΩ⟩
    · exact hc z ⟨hz, hzΩ⟩

/-! ### (G1) and (G3) for the labels of R11 -/

open Classical in
/-- **(G1) for the labels of R11**: `n_π(X ∩ Ω) ≤ c₁ (1 + d^cov_j(X mod Ω^c))`, as
`G1_cellCount` for the landed labels (the count reads only an admissible pair). -/
theorem DjModFin.cellCount_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω X : Set (CTorus d L N₁ m₁ K)}
    (h : DjModFin m₀ j Ω X) :
    (cellCount (cellSide L m₀ m₁ j) (X ∩ Ω) : ℝ) ≤ c1 d L * (1 + dcovMod m₀ j Ω X) := by
  obtain ⟨𝒦, W, E, hE, hcost⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_ne_top h.2.2.2)
  rw [← hcost]
  exact cellCount_le_of_admissible hN hj hE

omit [NeZero N₁] [NeZero L] in
/-- Containing or missing every component of `Ω^c` is stable under unions. -/
theorem comp_union_of_comp {Ω X₁ X₂ : Set (CTorus d L N₁ m₁ K)}
    (h₁ : ∀ z ∈ Ωᶜ, OmegaComp Ω z ⊆ X₁ ∨ Disjoint (OmegaComp Ω z) X₁)
    (h₂ : ∀ z ∈ Ωᶜ, OmegaComp Ω z ⊆ X₂ ∨ Disjoint (OmegaComp Ω z) X₂) :
    ∀ z ∈ Ωᶜ, OmegaComp Ω z ⊆ X₁ ∪ X₂ ∨ Disjoint (OmegaComp Ω z) (X₁ ∪ X₂) := by
  intro z hz
  rcases h₁ z hz with h | h
  · exact Or.inl (h.trans Set.subset_union_left)
  · rcases h₂ z hz with h' | h'
    · exact Or.inl (h'.trans Set.subset_union_right)
    · exact Or.inr (Set.disjoint_union_right.2 ⟨h, h'⟩)

/-- **(G3) for the labels of R11**: two labels sharing a site of `Ω` have a union in `DjModFin` of
size at most the sum plus `c_G = 2 d L`. -/
theorem djModFin_union {Ω X₁ X₂ : Set (CTorus d L N₁ m₁ K)} (h₁ : DjModFin m₀ j Ω X₁)
    (h₂ : DjModFin m₀ j Ω X₂) {t : CTorus d L N₁ m₁ K} (ht1 : t ∈ X₁) (ht2 : t ∈ X₂)
    (htΩ : t ∈ Ω) :
    DjModFin m₀ j Ω (X₁ ∪ X₂) ∧
      dcovMod m₀ j Ω (X₁ ∪ X₂) ≤ dcovMod m₀ j Ω X₁ + dcovMod m₀ j Ω X₂ + cG d L := by
  obtain ⟨𝒦₁, W₁, E₁, hA₁, he₁⟩ :=
    exists_admissible_eq_dcovMod (exists_admissible_of_ne_top h₁.2.2.2)
  obtain ⟨𝒦₂, W₂, E₂, hA₂, he₂⟩ :=
    exists_admissible_eq_dcovMod (exists_admissible_of_ne_top h₂.2.2.2)
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_union_admissible hA₁ hA₂ ht1 ht2 htΩ
  refine ⟨⟨⟨t, Or.inl ht1⟩, siteConnected_union h₁.2.1 h₂.2.1 ht1 ht2,
    comp_union_of_comp h₁.2.2.1 h₂.2.2.1, dcovModE_ne_top ⟨𝒦, W, E, hA⟩⟩, ?_⟩
  rw [← he₁, ← he₂]
  exact (dcovMod_le_of_admissible hA).trans hc

end Balaban.Fluctuation
