/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyHull
public import Balaban.Fluctuation.LocalClassDensityLevel

/-!
# The polymers of the new level from cube sets of index one (`StepTowerNewLabelsHull`)

The coefficient family `e(θ, T′)` of the class chain at the tower
(`e0CoeffFamily_class_exists_tower_struct_step`) is indexed by finite sets `T′` of level-`(k+1)`
cubes of block index `1` (side `L^{k+1+1+m₁}`), supported on rooted polymers of `𝒟_{k+1}` of
index `1`.  The class indexes its terms by the polymers of `𝒟_{k+1}` of index `P.m₀ = C.m₀`
(P1 (2.26)): unions of `π′_{k+1}`-cubes of side `L^{k+1+P.m₀+m₁+1}`.  This file regroups the first
into the second through the `π′`-hull `sitesOf (piHull m₀ S)` of `DetCauchyHull.lean` (the union of
the aligned `π′_{k+1}`-boxes meeting `S`):

* `isPolyDom_sitesOf_piHull`, `isPolyDom_sitesOf_piHull_of_isPolyDom`: the hull of a nonempty
  nearest-neighbour connected set (in particular of a polymer of any index) is a polymer of index
  `m₀`;
* `rootHull_mem`: if the root cube of the block of `y` lies in `T` and `sitesOf T` is a polymer of
  index one, then the hull of `sitesOf T` is a polymer of index `m₀` containing `y`;
* `finsum_polysAt_regroup`: the sum over the polymers `Y ∋ y` of the members of a finite family
  regrouped by any map `R` into polymers containing `y` is the sum of the family;
* `exists_rawSub_proj`: a continuous linear projection of the raw data onto the subspace `rawSub`
  of raw data of data (used to evaluate the coefficients, defined on `rawSub`, at all pairs of
  fields).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6

section Hull

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The `π′`-hull of a connected set is a polymer.**  If `S` is nonempty and nearest-neighbour
connected inside itself, the union of the aligned `π′_K`-boxes of index `m₀` meeting `S` is a
polymer of `𝒟_K` of index `m₀` (nonempty, a union of `π′_K`-cubes, connected). -/
theorem isPolyDom_sitesOf_piHull (hN : L ^ m₀ ∣ N₁) {S : Set (CTorus d L N₁ m₁ K)}
    (hne : S.Nonempty)
    (hconn : ∀ x ∈ S, ∀ y ∈ S,
      Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Nbr a b) x y) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ S)) := by
  set X := sitesOf (piHull m₀ S) with hX
  have hSX : S ⊆ X := subset_sitesOf_piHull hN S
  have hsymm : ∀ a b : CTorus d L N₁ m₁ K, (a ∈ X ∧ b ∈ X ∧ Nbr a b) →
      (b ∈ X ∧ a ∈ X ∧ Nbr b a) :=
    fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hbox : ∀ b ∈ piBases m₀ S, ∀ x ∈ box b (L * cellSide L m₀ m₁ K),
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) b x := by
    intro b hb x hx
    have hβ : box b (L * cellSide L m₀ m₁ K) ⊆ X := by
      rw [hX, sitesOf_piHull hN]
      exact Set.subset_iUnion₂ (s := fun b (_ : b ∈ piBases m₀ S) =>
        box b (L * cellSide L m₀ m₁ K)) b hb
    obtain ⟨w, hw, rfl⟩ := hx
    have := reach_box b w (box b (L * cellSide L m₀ m₁ K))
      (fun w' hw' => mem_box_add b (fun μ => lt_of_le_of_lt (hw' μ) (hw μ)))
    exact Relation.ReflTransGen.mono (fun a c h => ⟨hβ h.2.1, hβ h.2.2, h.1.2⟩) _ _ this
  have hS : ∀ x ∈ X, ∃ s ∈ S,
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) x s := by
    intro x hx
    rw [hX, sitesOf_piHull hN] at hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨s, hsb, hsS⟩ := hb.2
    exact ⟨s, hsS, (rtg_symm hsymm (hbox b hb x hxb)).trans (hbox b hb s hsb)⟩
  refine ⟨hne.mono hSX, ⟨_, chosenOne_piHull hN S⟩, fun x hx y hy => ?_⟩
  obtain ⟨s, hs, hxs⟩ := hS x hx
  obtain ⟨s', hs', hys'⟩ := hS y hy
  refine (hxs.trans ?_).trans (rtg_symm hsymm hys')
  exact Relation.ReflTransGen.mono (fun a b h => ⟨hSX h.1, hSX h.2.1, h.2.2⟩) _ _
    (hconn s hs s' hs')

/-- **The `π′`-hull of index `m₀` of a polymer of any index `m₀′` and level `j` is a polymer of
index `m₀`** (of `𝒟_K`). -/
theorem isPolyDom_sitesOf_piHull_of_isPolyDom (hN : L ^ m₀ ∣ N₁) {m₀' j : ℕ}
    {S : Set (CTorus d L N₁ m₁ K)}
    (hS : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀' j S) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ S)) :=
  isPolyDom_sitesOf_piHull hN hS.1 hS.2.2

/-- **The hull of a rooted polymer of index one contains the block of the root.**  If the root
cube of the `L^K`-block of `y` lies in the set `T` of cubes of index one and `sitesOf T` is a
polymer of index one, then the `π′`-hull of index `m₀` of `sitesOf T` is a polymer of index `m₀`
containing `y`. -/
theorem rootHull_mem (hN : L ^ m₀ ∣ N₁) (y : CTorus d L N₁ m₁ K)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)}
    (hT : rootCube (m₀ := 1) (blockIndex y) ∈ T)
    (hp : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) 1 K (sitesOf T)) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf (piHull m₀ (sitesOf T))) ∧
      y ∈ sitesOf (piHull m₀ (sitesOf T)) := by
  have hpoly := isPolyDom_sitesOf_piHull_of_isPolyDom (m₀ := m₀) (K := K) hN hp
  refine ⟨hpoly, (mem_iff_blockBase_mem_of_isPolyDom hN hpoly y).2 ?_⟩
  rw [← rootSite_blockIndex]
  exact subset_sitesOf_piHull hN _ (mem_sitesOf.2 ⟨_, hT, rootSite_mem_box_rootCube _⟩)

open Classical in
/-- **Regrouping a finite family into the polymers of a site.**  If every non-zero member `f i` of
a finite family is assigned (by `R`) a polymer of index `m₀` containing `y`, the sum over the
polymers `Y ∋ y` of the members assigned to `Y` is the sum of the family. -/
theorem finsum_polysAt_regroup {ι : Type*} [Fintype ι] (R : ι → Set (CTorus d L N₁ m₁ K))
    (f : ι → ℂ) (y : CTorus d L N₁ m₁ K)
    (hsupp : ∀ i, f i ≠ 0 →
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (R i) ∧ y ∈ R i) :
    ∑ᶠ Y ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K y,
        ∑ i ∈ Finset.univ.filter (fun i => R i = Y), f i = ∑ i, f i := by
  have hfin : (polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K y).Finite :=
    Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set s := Finset.univ.filter (fun i => R i ∈ polysAt (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
    m₀ K y) with hs
  have hfib := Finset.sum_fiberwise_of_maps_to (s := s) (t := hfin.toFinset) (g := R)
    (fun i hi => by simpa [hs] using hi) f
  have hin : ∀ X ∈ hfin.toFinset,
      ∑ i ∈ Finset.univ.filter (fun i => R i = X), f i =
        ∑ i ∈ s.filter (fun i => R i = X), f i := by
    intro X hX
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
    constructor
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      simpa using hX
    · exact fun h => h.2
  rw [Finset.sum_congr rfl hin, hfib]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  by_contra h
  obtain ⟨h1, h2⟩ := hsupp i h
  exact hi (by simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h1, h2⟩)

end Hull

section Proj

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **A continuous linear projection of the raw data onto `rawSub`**, the identity on `rawSub`
(the raw data of data: constant on the layer blocks, zero off the data sites). -/
theorem exists_rawSub_proj (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    ∃ π : RawData d L (N₁ * L ^ m₁) K N →L[ℂ] rawSub N G,
      ∀ r (h : r ∈ rawSub N G), π r = ⟨r, h⟩ := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (rawSub N G)
  refine ⟨LinearMap.toContinuousLinearMap (Submodule.projectionOnto _ q hq), fun r h => ?_⟩
  exact Submodule.projectionOnto_apply_left hq ⟨r, h⟩

end Proj

end Balaban.Inhabited
