/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCount
public import Balaban.Fluctuation.SizeModG4
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A polymer is determined by its cubes in `Ω` and the components of `Ω^c` it contains

For `X ∈ 𝒟_j(mod Ω^c)` meeting `Ω` (`Ω` a union of `π_j`-cubes), `X` is the union of its
`π_j`-cubes in `Ω` and of the components of `Ω^c` through the cubes of `Ω^c` next to them
(`X_eq_recon`); for a union `S` of `π_j`-cubes, `S` is the union of its cubes (`S_eq_recon`).
This is the second step of the entropy count (G2).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

open Classical in
/-- The bases of the `π_j`-cubes contained in `Z`. -/
noncomputable def cellsIn (m₀ j : ℕ) (Z : Set (CTorus d L N₁ m₁ K)) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun t => Aligned (cellSide L m₀ m₁ j) t ∧ box t (cellSide L m₀ m₁ j) ⊆ Z

open Classical in
/-- The bases of the `π_j`-cubes of `Ω^c` contained in `X` and next to a cube of `X ∩ Ω`. -/
noncomputable def Uset (m₀ j : ℕ) (Ω X : Set (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun u => Aligned (cellSide L m₀ m₁ j) u ∧
    box u (cellSide L m₀ m₁ j) ⊆ X ∩ Ωᶜ ∧ ∃ t ∈ cellsIn (m₁ := m₁) (K := K) m₀ j (X ∩ Ω),
      Near 1 (cellSide L m₀ m₁ j) t u

/-- The set built from cubes `T` and components through the cubes `U`. -/
def reconSet (m₀ j : ℕ) (Ω : Set (CTorus d L N₁ m₁ K)) (T U : Finset (CTorus d L N₁ m₁ K)) :
    Set (CTorus d L N₁ m₁ K) :=
  (⋃ t ∈ T, box t (cellSide L m₀ m₁ j)) ∪ ⋃ u ∈ U, OmegaComp Ω u

theorem mem_cellsIn {Z : Set (CTorus d L N₁ m₁ K)} {t : CTorus d L N₁ m₁ K} :
    t ∈ cellsIn (L := L) m₀ j Z ↔ Aligned (cellSide L m₀ m₁ j) t ∧
      box t (cellSide L m₀ m₁ j) ⊆ Z := by
  classical
  simp [cellsIn]

omit [NeZero N₁] [NeZero L] in
theorem rc_symm {Ω : Set (CTorus d L N₁ m₁ K)} {x y : CTorus d L N₁ m₁ K}
    (h : Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) x y) :
    Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) y x :=
  rtg_symm (fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩) h

omit [NeZero N₁] [NeZero L] in
theorem comp_eq_of_rtg {Ω : Set (CTorus d L N₁ m₁ K)} {z z' : CTorus d L N₁ m₁ K}
    (h : Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) z z') :
    OmegaComp Ω z = OmegaComp Ω z' := by
  ext y
  constructor
  · rintro ⟨hy, hzy⟩
    exact ⟨hy, (rc_symm h).trans hzy⟩
  · rintro ⟨hy, hzy⟩
    exact ⟨hy, h.trans hzy⟩

omit [NeZero N₁] [NeZero L] in
theorem mem_comp_self {Ω : Set (CTorus d L N₁ m₁ K)} {z : CTorus d L N₁ m₁ K} (hz : z ∈ Ωᶜ) :
    z ∈ OmegaComp Ω z := ⟨hz, Relation.ReflTransGen.refl⟩

omit [NeZero N₁] [NeZero L] in
theorem rtg_box_compl {Ω : Set (CTorus d L N₁ m₁ K)} {b : CTorus d L N₁ m₁ K} {s : ℕ}
    (hb : box b s ⊆ Ωᶜ) {x y : CTorus d L N₁ m₁ K} (hx : x ∈ box b s) (hy : y ∈ box b s) :
    Relation.ReflTransGen (fun u v => u ∈ Ωᶜ ∧ v ∈ Ωᶜ ∧ Nbr u v) x y :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1.2⟩) x y (chain_in_box b s Ωᶜ hb hx hy)

/-- A cube is contained in `Ω` or in `Ω^c`. -/
theorem cell_dichotomy (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω : Set (CTorus d L N₁ m₁ K)}
    (hΩ : IsPiUnion m₀ j Ω) {b : CTorus d L N₁ m₁ K} (hb : Aligned (cellSide L m₀ m₁ j) b) :
    box b (cellSide L m₀ m₁ j) ⊆ Ω ∨ box b (cellSide L m₀ m₁ j) ⊆ Ωᶜ := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  by_cases h : ∃ z ∈ box b (cellSide L m₀ m₁ j), z ∈ Ω
  · left
    obtain ⟨z, hz, hzΩ⟩ := h
    obtain ⟨b', hb'al, hzb', hsub⟩ := hΩ z hzΩ
    have e1 := cbase_eq_of_mem_box hdvd hb hz
    have e2 := cbase_eq_of_mem_box hdvd hb'al hzb'
    rw [← e1, e2]; exact hsub
  · right
    intro z hz hzΩ
    exact h ⟨z, hz, hzΩ⟩

theorem X_eq_recon (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {Ω X : Set (CTorus d L N₁ m₁ K)}
    (hΩ : IsPiUnion m₀ j Ω) (hX : DjMod m₀ j Ω X) {t0 : CTorus d L N₁ m₁ K}
    (ht0X : box t0 (cellSide L m₀ m₁ j) ⊆ X) (ht0Ω : box t0 (cellSide L m₀ m₁ j) ⊆ Ω) :
    X = reconSet m₀ j Ω (cellsIn m₀ j (X ∩ Ω)) (Uset m₀ j Ω X) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hcellX : ∀ z ∈ X, box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X := by
    intro z hz
    obtain ⟨b, hb1, hb2, hb3⟩ := hX.1.2.1 z hz
    exact (cell_subset_cube hdvd ha0 hb1 hb2).trans hb3
  have hcompX : ∀ z ∈ X, z ∈ Ωᶜ → OmegaComp Ω z ⊆ X := by
    intro z hz hzΩ
    rcases hX.2 z hzΩ with h | h
    · exact h
    · exact (Set.disjoint_left.1 h (mem_comp_self hzΩ) hz).elim
  have hne : (X ∩ Ω).Nonempty :=
    ⟨t0, ht0X (mem_box_self t0 ha0), ht0Ω (mem_box_self t0 ha0)⟩
  ext z
  constructor
  · intro hz
    by_cases hzΩ : z ∈ Ω
    · left
      refine Set.mem_iUnion₂.2 ⟨cbase (cellSide L m₀ m₁ j) z, mem_cellsIn.2 ⟨aligned_cbase z, ?_⟩,
        mem_box_cbase ha0 z⟩
      intro y hy
      refine ⟨hcellX z hz hy, ?_⟩
      rcases cell_dichotomy hN hj hΩ (aligned_cbase (a := cellSide L m₀ m₁ j) z) with h | h
      · exact h hy
      · exact absurd hzΩ (h (mem_box_cbase ha0 z))
    · right
      rcases G4_subset hX.1 hne hz with ⟨-, h⟩ | ⟨z', hz'Ω, ⟨s, hs, hsz'⟩, hzc⟩
      · exact absurd h hzΩ
      · have hz'c : z' ∈ OmegaComp Ω z := ⟨hz'Ω, rc_symm hzc.2⟩
        have hz'X : z' ∈ X := hcompX z hz hzΩ hz'c
        set u := cbase (cellSide L m₀ m₁ j) z' with hu
        have hus : box u (cellSide L m₀ m₁ j) ⊆ Ωᶜ := by
          rcases cell_dichotomy hN hj hΩ (aligned_cbase (a := cellSide L m₀ m₁ j) z') with h | h
          · exact absurd (h (mem_box_cbase ha0 z')) hz'Ω
          · exact h
        refine Set.mem_iUnion₂.2 ⟨u, ?_, ?_⟩
        · classical
          simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨aligned_cbase z', fun y hy => ⟨hcellX z' hz'X hy, hus hy⟩,
            cbase (cellSide L m₀ m₁ j) s, mem_cellsIn.2 ⟨aligned_cbase s, ?_⟩,
            near_cbase_of_nbr hdvd ha0 hsz'⟩
          intro y hy
          refine ⟨hcellX s hs.1 hy, ?_⟩
          rcases cell_dichotomy hN hj hΩ (aligned_cbase (a := cellSide L m₀ m₁ j) s) with h | h
          · exact h hy
          · exact absurd hs.2 (h (mem_box_cbase ha0 s))
        · rw [comp_eq_of_rtg (rtg_box_compl hus (mem_box_self u ha0) (mem_box_cbase ha0 z'))]
          exact hzc
  · rintro (hz | hz)
    · obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hz
      exact ((mem_cellsIn.1 ht).2 hzt).1
    · obtain ⟨u, hu, hzu⟩ := Set.mem_iUnion₂.1 hz
      have hu' : Aligned (cellSide L m₀ m₁ j) u ∧ box u (cellSide L m₀ m₁ j) ⊆ X ∩ Ωᶜ := by
        classical
        have := (Finset.mem_filter.1 hu).2
        exact ⟨this.1, this.2.1⟩
      have huX : u ∈ X := (hu'.2 (mem_box_self u ha0)).1
      have huc : u ∈ Ωᶜ := (hu'.2 (mem_box_self u ha0)).2
      exact hcompX u huX huc hzu

/-- A union `S` of `π_j`-cubes is the union of its cubes. -/
theorem S_eq_recon (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {S : Set (CTorus d L N₁ m₁ K)}
    (hS : IsPiUnion m₀ j S) (Ω : Set (CTorus d L N₁ m₁ K)) :
    S = reconSet m₀ j Ω (cellsIn m₀ j S) ∅ := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN hj
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  ext z
  constructor
  · intro hz
    left
    obtain ⟨b, hb1, hb2, hb3⟩ := hS z hz
    refine Set.mem_iUnion₂.2 ⟨b, mem_cellsIn.2 ⟨hb1, hb3⟩, hb2⟩
  · rintro (hz | hz)
    · obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hz
      exact (mem_cellsIn.1 ht).2 hzt
    · obtain ⟨u, hu, -⟩ := Set.mem_iUnion₂.1 hz
      simp at hu

end Balaban.Fluctuation
