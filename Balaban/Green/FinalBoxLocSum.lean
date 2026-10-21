/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCore
public import Balaban.Polymer.MayerSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local form of a sum of rooted terms (A6-3, box localization, item (L4), generic part)

The exponent of the fluctuation integrand on the box is a finite sum `∑_a τ_a` of terms, each a
function of the field on blocks and spin components, `u : Λ × Fin N → ℂ`, that reads the field only
on the blocks of a root set `R_a` (after the localization of the background, stage 1).  The cut
family `T(s)` has patches `P_i = B_i × Fin N` (`blockPatch`).  The rooted Lemma AE expands every term
(`rootedExpansion_linField`); `localFormOf` collects the coefficients by the region
`Y(a, C) = R_a ∪ ⋃_{i ∈ C} B_i` (`rootRegion`) of the term and of the rooted family `C`, the value
`τ_a(φ₀)` at the centre going to `Y = R_a`:

  `W_Y(w) = ∑_a ([R_a = Y] τ_a(φ₀) + ∑_{C ≠ ∅ rooted at R_a, Y(a, C) = Y} coef_C(τ_a; w))`.

* `sum_localFormOf`: `∑_Y W_Y(w) = ∑_a τ_a(φ₀ + T(1) w)` when every term has the rooted expansion at
  `w`;
* `localFormOf_congr`: `W_Y(w)` only depends on `w` on `Y × Fin N` (for every `w, w'`);
* `localFormOf_eq_zero_of_not_isAnimal`: `W_Y = 0` unless `Y` is a nonempty connected set of
  blocks, when the roots and the patches are;
* `sum_norm_localFormOf_le`: `∑_{Y ∋ x} ‖W_Y‖ e^{α|Y|}` is at most the sum over the terms rooted at
  `x` of `‖τ_a(φ₀)‖ e^{α|R_a|}` and over the pairs `(a, C)` with `x ∈ Y(a, C)` of
  `‖coef_C‖ e^{α|Y(a, C)|}`;
* `localFormOf_congr_param`: locality in an external parameter (the source), given the locality of
  each term on its root.
-/

@[expose] public section

namespace Balaban.Green

open Finset Balaban.Localization Balaban.Analysis

section Sites

variable {Λ : Type*} [DecidableEq Λ] {N : ℕ} {ι : Type*}

/-- The sites `R × Fin N` of a set of blocks. -/
def blockSites (N : ℕ) (R : Finset Λ) : Set (Λ × Fin N) := {p | p.1 ∈ R}

/-- The patches `B_i × Fin N` of a family of block patches. -/
def blockPatch (N : ℕ) (PB : ι → Finset Λ) : ι → Set (Λ × Fin N) :=
  fun i => blockSites N (PB i)

/-- The region `R ∪ ⋃_{i ∈ C} B_i` of a root and a family of cells. -/
def rootRegion (R : Finset Λ) (PB : ι → Finset Λ) (C : Finset ι) : Finset Λ :=
  R ∪ C.biUnion PB

theorem subset_rootRegion (R : Finset Λ) (PB : ι → Finset Λ) (C : Finset ι) :
    R ⊆ rootRegion R PB C := Finset.subset_union_left

theorem patch_subset_rootRegion (R : Finset Λ) (PB : ι → Finset Λ) {C : Finset ι} {i : ι}
    (hi : i ∈ C) : PB i ⊆ rootRegion R PB C :=
  fun _ hx => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hx⟩)

theorem patchReg_blockPatch_subset (PB : ι → Finset Λ) (R : Finset Λ) (C : Finset ι) :
    patchReg (blockPatch N PB) C ⊆ blockSites N (rootRegion R PB C) := by
  rintro p ⟨i, hi, hp⟩
  exact patch_subset_rootRegion R PB hi hp

omit [DecidableEq Λ] in
theorem not_disjoint_of_blockSites_inter {A B : Finset Λ}
    (h : (blockSites N A ∩ blockSites N B).Nonempty) : ¬ Disjoint A B := by
  obtain ⟨p, hpA, hpB⟩ := h
  exact Finset.not_disjoint_iff.2 ⟨p.1, hpA, hpB⟩

variable {V : Type*} (H : SimpleGraph Λ)

/-- **The region of a rooted family is connected**: if the root and the patches are nonempty
connected sets of blocks and every cell of `C` is joined to the root through overlapping patches,
then `R ∪ ⋃_{i ∈ C} B_i` is a nonempty connected set. -/
theorem isAnimal_rootRegion {R : Finset Λ} (hR : Polymer.IsAnimal H R) {PB : ι → Finset Λ}
    {C : Finset ι} (hPB : ∀ i ∈ C, Polymer.IsAnimal H (PB i))
    (hC : IsRootedFamily (blockPatch N PB) (blockSites N R) C) :
    Polymer.IsAnimal H (rootRegion R PB C) := by
  classical
  let cs : Option ι → Finset Λ := fun o => o.elim R PB
  let D : Finset (Option ι) := insert none (C.image some)
  have hunion : Polymer.unionCs cs D = rootRegion R PB C := by
    ext x
    simp only [Polymer.unionCs, D, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image,
      rootRegion, Finset.mem_union]
    constructor
    · rintro ⟨o, ho, hx⟩
      rcases ho with rfl | ⟨i, hi, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨i, hi, hx⟩
    · rintro (hx | ⟨i, hi, hx⟩)
      · exact ⟨none, Or.inl rfl, hx⟩
      · exact ⟨some i, Or.inr ⟨i, hi, rfl⟩, hx⟩
  have hnone : none ∈ D := Finset.mem_insert_self _ _
  have hsome : ∀ i ∈ C, some i ∈ D := fun i hi =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hi)
  -- every element of the family reaches the root
  have hreach : ∀ i ∈ C, Polymer.Reach cs D none (some i) := by
    intro i hi
    obtain ⟨j, hj, hjS, hji⟩ := hC i hi
    have h0 : Polymer.Reach cs D none (some j) :=
      Relation.ReflTransGen.single ⟨hnone, hsome j hj, fun hd => by
        have := not_disjoint_of_blockSites_inter (N := N)
          (show (blockSites N (PB j) ∩ blockSites N R).Nonempty from hjS)
        exact this hd.symm⟩
    have hchain : ∀ i', Relation.ReflTransGen (CellAdj (blockPatch N PB) C) j i' →
        Polymer.Reach cs D (some j) (some i') := by
      intro i' h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih =>
        obtain ⟨hb, hc, hbcP⟩ := hbc
        exact ih.tail ⟨hsome _ hb, hsome _ hc,
          not_disjoint_of_blockSites_inter (N := N) hbcP⟩
    exact Relation.ReflTransGen.trans h0 (hchain i hji)
  have hconn : Polymer.ConnSet cs D := by
    refine ⟨⟨none, hnone⟩, fun s hs s' hs' => ?_⟩
    have hto : ∀ t ∈ D, Polymer.Reach cs D none t := by
      intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht'
      · exact Relation.ReflTransGen.refl
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht'
        exact hreach i hi
    exact Relation.ReflTransGen.trans (Polymer.Reach.symm cs (hto s hs)) (hto s' hs')
  have hS : ∀ t ∈ D, Polymer.IsAnimal H (cs t) := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht'
    · exact hR
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht'
      exact hPB i hi
  rw [← hunion]
  exact Polymer.isAnimal_unionCs_of_connSet H cs hconn hS

end Sites

section Form

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Type*} [Fintype A]

open Classical in
/-- **The local form of a sum of rooted terms**: the coefficients of the rooted Lemma AE of every
term `τ_a` (root `R_a`), collected by the region `Y(a, C) = R_a ∪ ⋃_{i ∈ C} B_i`, with the value
`τ_a(φ₀)` at the centre at `Y = R_a`. -/
noncomputable def localFormOf (τ : A → (Λ × Fin N → ℂ) → ℂ) (RA : A → Finset Λ)
    (PB : ι → Finset Λ) (φ₀ : Λ × Fin N → ℂ) (T : (ι → ℂ) → Λ × Fin N → Λ × Fin N → ℂ)
    (Y : Finset Λ) (w : Λ × Fin N → ℂ) : ℂ :=
  ∑ a, ((if RA a = Y then τ a φ₀ else 0) +
    ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
        IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧ rootRegion (RA a) PB C = Y),
      rootedCoef (τ a) φ₀ T w C)

variable {τ : A → (Λ × Fin N → ℂ) → ℂ} {RA : A → Finset Λ} {PB : ι → Finset Λ}
  {φ₀ : Λ × Fin N → ℂ} {T : (ι → ℂ) → Λ × Fin N → Λ × Fin N → ℂ}

open Classical in
/-- **The sum of the local form is the sum of the terms**, when every term has the rooted
expansion at `w`. -/
theorem sum_localFormOf {w : Λ × Fin N → ℂ}
    (hexp : ∀ a, τ a (linField φ₀ T (fun _ => 1) w) = τ a φ₀ +
      ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
        IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C), rootedCoef (τ a) φ₀ T w C) :
    ∑ Y, localFormOf τ RA PB φ₀ T Y w = ∑ a, τ a (linField φ₀ T (fun _ => 1) w) := by
  unfold localFormOf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hexp a, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq]; simp
  · rw [← Finset.sum_fiberwise_of_maps_to (g := fun C => rootRegion (RA a) PB C)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext C
    simp [and_assoc]

/-- **Locality in the variable**: `W_Y(w)` only depends on `w` on `Y × Fin N`. -/
theorem localFormOf_congr {R : ℝ} (hR : 1 < R) (hT : CutDecoupling (blockPatch N PB) R T)
    (Y : Finset Λ) {w w' : Λ × Fin N → ℂ} (hww : ∀ p : Λ × Fin N, p.1 ∈ Y → w p = w' p) :
    localFormOf τ RA PB φ₀ T Y w = localFormOf τ RA PB φ₀ T Y w' := by
  classical
  unfold localFormOf
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun C hC => ?_
  obtain ⟨-, -, hY⟩ := (Finset.mem_filter.1 hC).2
  refine rootedCoef_congr hT hR (τ a) φ₀ C fun p hp => hww p ?_
  have := patchReg_blockPatch_subset (N := N) PB (RA a) C hp
  rw [hY] at this
  exact this

/-- **Support on connected sets**: if every root and every patch is a nonempty connected set of
blocks, `W_Y = 0` unless `Y` is one. -/
theorem localFormOf_eq_zero_of_not_isAnimal (H : SimpleGraph Λ)
    (hRA : ∀ a, Polymer.IsAnimal H (RA a)) (hPB : ∀ i, Polymer.IsAnimal H (PB i))
    {Y : Finset Λ} (hY : ¬ Polymer.IsAnimal H Y) (w : Λ × Fin N → ℂ) :
    localFormOf τ RA PB φ₀ T Y w = 0 := by
  classical
  unfold localFormOf
  refine Finset.sum_eq_zero fun a _ => ?_
  have h1 : (if RA a = Y then τ a φ₀ else 0) = 0 := by
    split_ifs with h
    · exact absurd (h ▸ hRA a) hY
    · rfl
  rw [h1, zero_add]
  refine Finset.sum_eq_zero fun C hC => ?_
  obtain ⟨-, hrooted, hreg⟩ := (Finset.mem_filter.1 hC).2
  exact absurd (hreg ▸ isAnimal_rootRegion H (hRA a) (fun i _ => hPB i) hrooted) hY

open Classical in
/-- **The summed bound of the local form**: for every block `x` and rate `α ≥ 0`,
`∑_{Y ∋ x} ‖W_Y‖ e^{α|Y|}` is at most the sum over the terms rooted at `x` of
`‖τ_a(φ₀)‖ e^{α|R_a|}` and over the pairs `(a, C)`, `C ≠ ∅` rooted at `R_a` with `x ∈ Y(a, C)`, of
`‖coef_C‖ e^{α|Y(a, C)|}`. -/
theorem sum_norm_localFormOf_le (w : Λ × Fin N → ℂ) (x : Λ) (α : ℝ) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset Λ => x ∈ Y),
        ‖localFormOf τ RA PB φ₀ T Y w‖ * Real.exp (α * (Y.card : ℝ)) ≤
      ∑ a, ((if x ∈ RA a then ‖τ a φ₀‖ * Real.exp (α * ((RA a).card : ℝ)) else 0) +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
          IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧
            x ∈ rootRegion (RA a) PB C),
          ‖rootedCoef (τ a) φ₀ T w C‖ *
            Real.exp (α * ((rootRegion (RA a) PB C).card : ℝ))) := by
  classical
  -- the norm of each `W_Y` is at most the sum of the norms of its pieces
  have hW : ∀ Y, ‖localFormOf τ RA PB φ₀ T Y w‖ ≤
      ∑ a, ((if RA a = Y then ‖τ a φ₀‖ else 0) +
        ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
          IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧ rootRegion (RA a) PB C = Y),
          ‖rootedCoef (τ a) φ₀ T w C‖) := by
    intro Y
    unfold localFormOf
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_le _ _))
    split_ifs <;> simp
  calc ∑ Y ∈ Finset.univ.filter (fun Y : Finset Λ => x ∈ Y),
        ‖localFormOf τ RA PB φ₀ T Y w‖ * Real.exp (α * (Y.card : ℝ))
      ≤ ∑ Y ∈ Finset.univ.filter (fun Y : Finset Λ => x ∈ Y),
          ∑ a, ((if RA a = Y then ‖τ a φ₀‖ * Real.exp (α * (Y.card : ℝ)) else 0) +
            ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
              IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧
                rootRegion (RA a) PB C = Y),
              ‖rootedCoef (τ a) φ₀ T w C‖ * Real.exp (α * (Y.card : ℝ))) := by
        refine Finset.sum_le_sum fun Y _ => ?_
        refine (mul_le_mul_of_nonneg_right (hW Y) (Real.exp_pos _).le).trans (le_of_eq ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [add_mul, Finset.sum_mul]
        congr 1
        split_ifs <;> simp
    _ = ∑ a, ∑ Y ∈ Finset.univ.filter (fun Y : Finset Λ => x ∈ Y),
          ((if RA a = Y then ‖τ a φ₀‖ * Real.exp (α * (Y.card : ℝ)) else 0) +
            ∑ C ∈ Finset.univ.filter (fun C : Finset ι => C.Nonempty ∧
              IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧
                rootRegion (RA a) PB C = Y),
              ‖rootedCoef (τ a) φ₀ T w C‖ * Real.exp (α * (Y.card : ℝ))) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_ite_eq]
          by_cases hx : x ∈ RA a <;> simp [hx]
        · rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun C : Finset ι =>
              C.Nonempty ∧ IsRootedFamily (blockPatch N PB) (blockSites N (RA a)) C ∧
                x ∈ rootRegion (RA a) PB C))
            (g := fun C => rootRegion (RA a) PB C)
            (t := Finset.univ.filter (fun Y : Finset Λ => x ∈ Y))
            (fun C hC => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hC).2.2.2⟩)]
          refine Finset.sum_congr rfl fun Y _ => ?_
          rw [Finset.filter_filter]
          refine Finset.sum_congr ?_ fun C hC => ?_
          · ext C
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, h3 ▸ (Finset.mem_filter.1 ‹Y ∈ _›).2⟩, h3⟩
            · rintro ⟨⟨h1, h2, -⟩, h3⟩; exact ⟨h1, h2, h3⟩
          · rw [(Finset.mem_filter.1 hC).2.2]

/-- **Locality in an external parameter**: if each term, as a function of a parameter `g`, only
depends on `g` through a relation `Ag` attached to its root, and `Ag` is monotone in the region,
then `W_Y` only depends on `g` through `Ag Y`. -/
theorem localFormOf_congr_param {G : Type*} (τg : G → A → (Λ × Fin N → ℂ) → ℂ)
    (Ag : Finset Λ → G → G → Prop)
    (hmono : ∀ {Y Y' : Finset Λ} {g g' : G}, Y ⊆ Y' → Ag Y' g g' → Ag Y g g')
    (hτ : ∀ a g g', Ag (RA a) g g' → τg g a = τg g' a) (Y : Finset Λ) {g g' : G}
    (hgg : Ag Y g g') (w : Λ × Fin N → ℂ) :
    localFormOf (τg g) RA PB φ₀ T Y w = localFormOf (τg g') RA PB φ₀ T Y w := by
  classical
  unfold localFormOf
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hY : RA a ⊆ Y
  · have hag := hτ a g g' (hmono hY hgg)
    rw [hag]
  · have h2 : ¬ RA a = Y := fun h => hY (h ▸ subset_refl _)
    rw [Finset.filter_false_of_mem fun C _ hp => by
      obtain ⟨-, -, hreg⟩ := hp
      exact hY (hreg ▸ subset_rootRegion (RA a) PB C)]
    simp [h2]

end Form

end Balaban.Green
