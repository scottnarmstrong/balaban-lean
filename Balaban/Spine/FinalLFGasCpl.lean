/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFGasGeom
public import Balaban.Spine.FinalLFBdryLocal

/-!
# The supports of the couplings of the record gas (A6-4)

A coupling of the record gas is a boundary term `ℬ^{(k)}(X, 𝔸)` on a valid boundary domain `X`
(`FineValidAt`): its fine set is nearest-neighbour connected, so `X` is connected in the king graph
of the cubes (`isAnimal_king_of_fineValidAt`; adjacent sites lie in cubes at index distance `≤ 1`,
`cube_supDist_le_one_of_nbr`). Its support in the gas is `dblNbhd 2 X`, the `1`-neighbourhood of
`2·X` in the doubled torus: connected (`isAnimal_dblNbhd_two`), with at most `3^d |X|` sites
(`card_dblNbhd_two_le`), and it meets the support of every record whose cubes meet `X`
(`not_disjoint_dblNbhd_of_inter`).

* `castT_castT_symm`, **`isAnimal_king_of_fineValidAt`**, **`isAnimal_cplSupp`**,
  `not_disjoint_dblNbhd_of_inter`.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Polymer

namespace Balaban.RootFSpine

theorem castT_castT_symm {d a b : ℕ} (h : a = b) (x : Torus d b) :
    Localization.castT h (Localization.castT h.symm x) = x := by
  subst h; rfl

section Cpl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero M] [NeZero S.L]

/-- **A valid boundary domain is connected in the king graph of the cubes.** -/
theorem isAnimal_king_of_fineValidAt (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))} (hX : FineValidAt F k Om X) :
    IsAnimal (kingGraph S.d (n k)) X := by
  obtain ⟨hne, hconn, -, -⟩ := hX
  set f : Localization.CTorus S.d S.L F.N₁ m₁ K → Torus S.d (n k) :=
    fun u => cubeMap n S.L M K k (Localization.castT F.side u) with hf
  have hmem : ∀ u ∈ d7Pull F k (X : Set (Torus S.d (n k))), f u ∈ X := fun u hu => hu
  have hsite : ∀ c ∈ X, ∃ u ∈ d7Pull F k (X : Set (Torus S.d (n k))), f u = c := by
    intro c hc
    obtain ⟨x, hx⟩ := exists_site_of_cube (M := M) hnn hkK c
    refine ⟨Localization.castT F.side.symm x, ?_, ?_⟩
    · change cubeMap n S.L M K k (Localization.castT F.side
        (Localization.castT F.side.symm x)) ∈ (X : Set (Torus S.d (n k)))
      rw [castT_castT_symm, hx]
      exact hc
    · change cubeMap n S.L M K k (Localization.castT F.side
        (Localization.castT F.side.symm x)) = c
      rw [castT_castT_symm, hx]
  have hpath : ∀ u ∈ d7Pull F k (X : Set (Torus S.d (n k))), ∀ w,
      Relation.ReflTransGen (fun a b => a ∈ d7Pull F k (X : Set (Torus S.d (n k))) ∧
        b ∈ d7Pull F k (X : Set (Torus S.d (n k))) ∧ Localization.Nbr a b) u w →
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ (kingGraph S.d (n k)).Adj a b)
        (f u) (f w) := by
    intro u _ w h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      by_cases he : f b = f c
      · rw [← he]; exact ih
      · exact ih.tail ⟨hmem b hbc.1, hmem c hbc.2.1,
          (show (kingGraph S.d (n k)).Adj (f b) (f c) from
            ⟨he, cube_supDist_le_one_of_nbr F hnn hkK hbc.2.2⟩)⟩
  rw [isAnimal_iff]
  refine ⟨?_, fun c hc c' hc' => ?_⟩
  · obtain ⟨u, hu⟩ := hne
    exact ⟨f u, hmem u hu⟩
  · obtain ⟨u, hu, rfl⟩ := hsite c hc
    obtain ⟨u', hu', rfl⟩ := hsite c' hc'
    exact hpath u hu u' (hconn u hu u' hu')

/-- **The support of a coupling on a valid boundary domain is connected** in the doubled torus. -/
theorem isAnimal_cplSupp (F : FineSizeFrame S n M K m₀ m₁)
    (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {Om : Set (Torus S.d (n k))} {X : Finset (Torus S.d (n k))} (hX : FineValidAt F k Om X) :
    IsAnimal (kingGraph S.d (2 * n k)) (dblNbhd 2 X) :=
  isAnimal_dblNbhd_two (isAnimal_king_of_fineValidAt F hnn hkK hX)

end Cpl

/-- The support of a coupling meets the support of every record whose cubes meet its domain. -/
theorem not_disjoint_dblNbhd_of_inter {d n ω : ℕ} [NeZero n] {X Y : Finset (Torus d n)}
    (h : (X ∩ Y).Nonempty) : ¬ Disjoint (dblNbhd 2 X) (dblNbhd ω Y) := by
  obtain ⟨x, hx⟩ := h
  rw [Finset.mem_inter] at hx
  refine Finset.not_disjoint_iff.2 ⟨tDouble x, ?_, ?_⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx.1,
      by rw [supDist_self]; exact Nat.zero_le _⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx.2,
      by rw [supDist_self]; exact Nat.zero_le _⟩

end Balaban.RootFSpine
