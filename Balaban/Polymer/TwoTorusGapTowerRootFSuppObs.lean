/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerRootFSuppTower
public import Balaban.Polymer.TwoTorusGapTowerSitesAnimal

/-!
# The observable sum of the step identity in Root-F's indexing by polymers (blocker 7)

The step identity of the tower sums the observable coefficients `mObs y i θ T'` over all sets `T'` of
`π_{k+1}`-cubes.  A set `T'` with `IsPolyDom 1 (k + 1) (sitesOf T')` has the sites of an animal `X` of
cells (`exists_animal_of_isPolyDom`), so `T' = Ycub X` (`sitesOf_injective`); hence, if the
coefficient vanishes off such sets (the support clause of `towerGapScale_resum_fromTowerG_supp`),
`∑_{T'} f T' = ∑_{X ∈ P} f (Ycub X)` (`sum_cubeSets_eq_sum_polymers`), the sum over the polymers of
the torus of the cells indexed as in Root-F.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer

section Obs

variable {d L N₁ m₁ k K : ℕ} [NeZero N₁] [NeZero L] [NeZero K]

/-- The sites of a set of cubes are the sites of the cells of the cubes. -/
theorem sitesOf_eq_cells
    (hn : (N₁ * L ^ m₁) * L ^ (k + 1) = cellSide L 1 m₁ (k + 1) * K)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    sitesOf T' = {x : CTorus d L N₁ m₁ (k + 1) |
      (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
        ↑((T'.image fun (b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) j => ((((b.1 j).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).image
          fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs)} := by
  have ha := cellSide_pos (L := L) 1 m₁ (k + 1)
  have : NeZero (cellSide L 1 m₁ (k + 1)) := ⟨ha.ne'⟩
  have hdvd : cellSide L 1 m₁ (k + 1) ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := ⟨K, hn⟩
  ext x
  rw [Set.mem_ofPred_eq, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
    refine ⟨_, Finset.mem_image.2 ⟨b, hb, rfl⟩, ?_⟩
    funext μ
    rw [cell_eq_of_mem_box_aligned hn b.2.1 hxb μ]
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
    refine mem_sitesOf.2 ⟨b, hb, ?_⟩
    have hsame : ∀ μ, (x μ).val / cellSide L 1 m₁ (k + 1) =
        (b.1 μ).val / cellSide L 1 m₁ (k + 1) := by
      intro μ
      have h1 := ZMod.valMinAbs_inj.1 (congrFun hcx μ)
      have hK : ∀ z : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)),
          z.val / cellSide L 1 m₁ (k + 1) < K := fun z => by
        rw [Nat.div_lt_iff_lt_mul ha]
        exact lt_of_lt_of_eq (ZMod.val_lt z) (by rw [hn, mul_comm])
      have := (ZMod.natCast_eq_natCast_iff' _ _ K).1 h1.symm
      rwa [Nat.mod_eq_of_lt (hK _), Nat.mod_eq_of_lt (hK _)] at this
    have h2 := mem_box_cbase_of_sameCell ha hsame
    have h3 : cbase (cellSide L 1 m₁ (k + 1)) b.1 = b.1 :=
      cbase_eq_of_mem_box hdvd b.2.1 (mem_box_self _ ha)
    rwa [h3] at h2

/-- A set of cubes whose sites form a domain `𝒟_{k+1}` has the sites of an animal of cells. -/
theorem exists_animal_of_isPolyDom
    (hn : (N₁ * L ^ m₁) * L ^ (k + 1) = cellSide L 1 m₁ (k + 1) * K)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (h : IsPolyDom 1 (k + 1) (sitesOf T')) :
    ∃ Y : Finset (Fin d → ZMod K), IsAnimal (blockGraph d K) Y ∧
      sitesOf T' = {x : CTorus d L N₁ m₁ (k + 1) |
        (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
          ↑(Y.image fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs)} := by
  have ha := cellSide_pos (L := L) 1 m₁ (k + 1)
  have hset := sitesOf_eq_cells hn T'
  set Y := T'.image fun (b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ) j => ((((b.1 j).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K) with hY
  refine ⟨Y, ?_, hset⟩
  have hmem : ∀ x, x ∈ sitesOf T' ↔
      (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
        Y.image fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs := fun x => by
    rw [hset]; simp
  rw [← isPolymer_cellsOf_iff hn ha Y]
  obtain ⟨hne, -, hconn⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmem x).1 hx⟩⟩
  · intro x hx y hxy
    have hx' := (Finset.mem_filter.1 hx).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have : (fun μ => (((((y μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) =
        (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) :=
      funext fun μ => by rw [hxy μ]
    rw [this]; exact hx'
  · intro x hx y hy
    have hxS := (hmem x).2 (Finset.mem_filter.1 hx).2
    have hyS := (hmem y).2 (Finset.mem_filter.1 hy).2
    refine Relation.ReflTransGen.lift (fun x => x) ?_ x y (hconn x hxS y hyS)
    rintro u v ⟨hu, hv, hnb⟩
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmem u).1 hu⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (hmem v).1 hv⟩, hnb⟩

/-- **The sum over cube sets is the sum over polymers.**  If `f` vanishes off the sets whose sites
form a domain `𝒟_{k+1}`, then `∑_{T'} f T' = ∑_{X ∈ P} f (Ycub X)`, where `P` is the set of images of
the animals of the block torus and `Ycub X` the cubes of the cells of `X`. -/
theorem sum_cubeSets_eq_sum_polymers (hN : L ^ 1 ∣ N₁)
    (hn : (N₁ * L ^ m₁) * L ^ (k + 1) = cellSide L 1 m₁ (k + 1) * K)
    (P : Finset (Finset (Fin d → ℤ)))
    (hP : ∀ X, X ∈ P ↔ ∃ Y, IsAnimal (blockGraph d K) Y ∧
      X = Y.image (fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs))
    (Ycub : Finset (Fin d → ℤ) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hYs : ∀ X, X ∈ P → sitesOf (Ycub X) = {x : CTorus d L N₁ m₁ (k + 1) |
      (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
        (↑X : Set (Fin d → ℤ))})
    (f : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ) → ℂ)
    (hf : ∀ T', f T' ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf T')) :
    ∑ T', f T' = ∑ X ∈ P, f (Ycub X) := by
  have ha := cellSide_pos (L := L) 1 m₁ (k + 1)
  have hinj : Set.InjOn Ycub ↑P := by
    intro X hX X' hX' he
    have h1 := hYs X hX
    have h2 := hYs X' hX'
    rw [he] at h1
    have hs : {x : CTorus d L N₁ m₁ (k + 1) |
        (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
          (↑X : Set (Fin d → ℤ))} = {x : CTorus d L N₁ m₁ (k + 1) |
        (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
          (↑X' : Set (Fin d → ℤ))} := h1.symm.trans h2
    have key : ∀ (A B : Finset (Fin d → ℤ)), A ∈ P → {x : CTorus d L N₁ m₁ (k + 1) |
        (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
          (↑A : Set (Fin d → ℤ))} = {x : CTorus d L N₁ m₁ (k + 1) |
        (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
          (↑B : Set (Fin d → ℤ))} → A ⊆ B := by
      intro A B hA hAB x hx
      obtain ⟨Y, -, rfl⟩ := (hP A).1 hA
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨z, hz⟩ := exists_site (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hn ha b
      have hz' : z ∈ {x : CTorus d L N₁ m₁ (k + 1) |
          (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) ∈
            (↑(Y.image fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs) : Set (Fin d → ℤ))} := by
        show _ ∈ (↑(Y.image fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs) : Set (Fin d → ℤ))
        have : (fun μ => (((((z μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) =
            fun μ => (b μ).valMinAbs := funext fun μ => by rw [← congrFun hz μ]
        rw [this]
        exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hb)
      rw [hAB] at hz'
      have : (fun μ => (((((z μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) : ZMod K)).valMinAbs) =
          fun μ => (b μ).valMinAbs := funext fun μ => by rw [← congrFun hz μ]
      have hz'' : _ ∈ (↑B : Set (Fin d → ℤ)) := hz'
      rwa [this] at hz''
    exact Finset.Subset.antisymm (key X X' hX hs) (key X' X hX' hs.symm)
  rw [← Finset.sum_image (f := f) hinj]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun T' _ hT' => ?_
  by_contra hne
  obtain ⟨Y, hY, hsites⟩ := exists_animal_of_isPolyDom hn T' (hf T' hne)
  have hXP : Y.image (fun (b : Fin d → ZMod K) μ => (b μ).valMinAbs) ∈ P := (hP _).2 ⟨Y, hY, rfl⟩
  refine hT' (Finset.mem_image.2 ⟨_, hXP, ?_⟩)
  exact sitesOf_injective hN le_rfl ((hYs _ hXP).trans hsites.symm)

end Obs

end Balaban.Polymer.TwoTorusStep
