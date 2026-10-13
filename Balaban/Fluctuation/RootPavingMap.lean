/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeSystem
public import Balaban.Polymer.MarkedCubes
public import Balaban.SmallField.Def6InfPaving
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The paving action on cube sets and the root map (ROOT.md §2, package `RootPavingMap`)

Fixed geometry of the level-`K` cubes of the torus `CTorus d L N₁ m₁ K`.  The canonical
coefficients of Theorem 3.1 are indexed by a coarse site `z` (the block `B(z)` at which the energy
term is rooted) and a finite set `T` of level-`K` cubes; a term of the inductive class is indexed
by a root site `y` and a polymer `X`.  The assignment `(z, T) ↦ (rootSite z, sitesOf T)` is the
direct one.  This file contains:

* the action of the paving symmetries (`pavingSymGroup`) on level-`K` cubes and on finite cube
  sets, with `sitesOf (r • T) = r '' sitesOf T`;
* invariance of `IsPolyDom`, of `sizeJ` and of `dExt` under these symmetries;
* the root site `rootSite z` (the base of the block `B(z)`), the root cube `rootCube z`, and the
  covariance of the root under the symmetries;
* the fibre statement: at most one pair `(z, T)` over a given `(y, X)`;
* the abstract rooted sum `rootedSum e y X`, its bound `‖rootedSum e y X‖ ≤ B exp(-κ sizeJ X)`
  (premise: the active-size identity of the parallel package `RootActiveSize`), and its
  covariance.

No generating set of class terms is chosen.  The output terms of the class (`Tm_out`), their
field domains, the anchor of the physical marks at the root cube, the rooted determinant
expansion and the covariance of the coefficient values are separate packages and are not proved
here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

section Group

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- A paving symmetry maps aligned boxes of side `a` (aligned at `s`) onto such boxes, for
`s ∣ a`, `s ∣ cellSide` and `s ∣` the torus size.  (Both `r` and `r⁻¹`.) -/
theorem goodMap_of_mem_pavingSymGroup (s a : ℕ) (hs : s ∣ cellSide L m₀ m₁ K)
    (hsn : s ∣ (N₁ * L ^ m₁) * L ^ K) (ha : s ∣ a)
    {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) :
    GoodMap s a r ∧ GoodMap s a r⁻¹ := by
  have hcs : ZMod.castHom hsn (ZMod s)
      ((cellSide L m₀ m₁ K : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = 0 := by
    rw [map_natCast]; exact (ZMod.natCast_eq_zero_iff _ _).2 hs
  have hgen : ∀ g ∈ ({g | ∃ μ, g = transBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
        (cellSide L m₀ m₁ K) μ} ∪
      {g | ∃ μ, g = flipBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (cellSide L m₀ m₁ K) μ} ∪
      {g | ∃ μ ν, g = swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) μ ν} :
      Set (Equiv.Perm (CTorus d L N₁ m₁ K))), GoodMap s a g ∧ GoodMap s a g⁻¹ := by
    rintro g ((⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩)
    · have ht : ∀ i, ZMod.castHom hsn (ZMod s)
          (((cellSide L m₀ m₁ K) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)) i) = 0 := by
        intro i
        by_cases h : i = μ
        · subst h
          have : ((cellSide L m₀ m₁ K) • (Pi.single i 1 : CTorus d L N₁ m₁ K)) i =
              ((cellSide L m₀ m₁ K : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by simp
          rw [this, hcs]
        · simp [Pi.single_eq_of_ne h]
      refine ⟨good_addRight hsn _ _ ht, ?_⟩
      have : (transBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (cellSide L m₀ m₁ K) μ)⁻¹ =
          Equiv.addRight (-((cellSide L m₀ m₁ K) • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) := by
        ext x; simp [transBy, Equiv.Perm.inv_def]
      rw [this]
      refine good_addRight hsn _ _ fun i => ?_
      rw [Pi.neg_apply, map_neg, ht i, neg_zero]
    · have hf : GoodMap s a
          (flipBy (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (cellSide L m₀ m₁ K) μ) := by
        refine good_flip μ _ _ (fun x => rfl) hsn hcs ha fun x => ?_
        ext i
        by_cases h : i = μ
        · subst h; simp [flipBy]
        · simp [flipBy, Function.update_of_ne h]
      exact ⟨hf, hf⟩
    · have hf : GoodMap s a (swapJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) μ ν) :=
        good_swap μ ν _ hsn (fun x => rfl)
      exact ⟨hf, hf⟩
  refine Subgroup.closure_induction (p := fun r _ => GoodMap s a r ∧ GoodMap s a r⁻¹)
    ?_ ?_ ?_ ?_ hr
  · exact hgen
  · exact ⟨GoodMap.one _ _, by rw [inv_one]; exact GoodMap.one _ _⟩
  · intro x y _ _ hx hy
    exact ⟨hx.1.mul hy.1, by rw [mul_inv_rev]; exact hy.2.mul hx.2⟩
  · intro x _ hx
    exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

end Group

section CubeAction

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The level-`K` cube containing the image of the base of the cube `b` under the permutation
`r`.  For `r` in the paving symmetry group this is the image cube of `b` (`box_cubeMap`). -/
def cubeMap (r : Equiv.Perm (CTorus d L N₁ m₁ K)) (b : 𝔅) : 𝔅 :=
  ⟨cbase (cellSide L m₀ m₁ K) (r b.1), aligned_cbase _, Set.subset_univ _⟩

theorem cubeMap_val (r : Equiv.Perm (CTorus d L N₁ m₁ K)) (b : 𝔅) :
    (cubeMap r b).1 = cbase (cellSide L m₀ m₁ K) (r b.1) := rfl

/-- Two aligned level-`K` boxes with the same sites have the same base. -/
theorem eq_of_box_eq (hN : L ^ m₀ ∣ N₁) {b b' : CTorus d L N₁ m₁ K}
    (hb : Aligned (cellSide L m₀ m₁ K) b) (hb' : Aligned (cellSide L m₀ m₁ K) b')
    (h : box b (cellSide L m₀ m₁ K) = box b' (cellSide L m₀ m₁ K)) : b = b' := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have h1 := cbase_eq_of_mem_box hdvd hb (mem_box_self b ha0)
  have h2 : b ∈ box b' (cellSide L m₀ m₁ K) := h ▸ mem_box_self b ha0
  exact h1.symm.trans (cbase_eq_of_mem_box hdvd hb' h2)

/-- **T1.** A paving symmetry maps the level-`K` box of the cube `b` onto the level-`K` box of the
cube `cubeMap r b`. -/
theorem box_cubeMap (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (b : 𝔅) :
    box (cubeMap r b).1 (cellSide L m₀ m₁ K) = r '' box b.1 (cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  obtain ⟨b', hb', himg⟩ :=
    (goodMap_of_mem_pavingSymGroup (cellSide L m₀ m₁ K) (cellSide L m₀ m₁ K) dvd_rfl hdvd
      dvd_rfl hr).1.boxes b.1 b.2.1
  have hmem : r b.1 ∈ box b' (cellSide L m₀ m₁ K) :=
    himg ▸ ⟨b.1, mem_box_self _ ha0, rfl⟩
  have : (cubeMap r b).1 = b' := cbase_eq_of_mem_box hdvd hb' hmem
  rw [this, himg]

theorem cubeMap_inv (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (b : 𝔅) :
    cubeMap r⁻¹ (cubeMap r b) = b := by
  apply Subtype.ext
  refine eq_of_box_eq hN (cubeMap r⁻¹ (cubeMap r b)).2.1 b.2.1 ?_
  rw [box_cubeMap hN (inv_mem hr), box_cubeMap hN hr, ← Set.image_comp]
  ext x
  simp [Equiv.Perm.inv_def]

/-- **T1.** The permutation of the level-`K` cubes induced by a paving symmetry. -/
def cubePerm (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) :
    Equiv.Perm 𝔅 where
  toFun := cubeMap r
  invFun := cubeMap r⁻¹
  left_inv b := cubeMap_inv hN hr b
  right_inv b := by
    have := cubeMap_inv hN (inv_mem hr) b
    rwa [inv_inv] at this

open Classical in
/-- The image `r • T` of a finite set of level-`K` cubes under the paving symmetry `r`. -/
noncomputable def cubeAct (r : Equiv.Perm (CTorus d L N₁ m₁ K)) (T : Finset 𝔅) : Finset 𝔅 :=
  T.image (cubeMap r)

theorem mem_cubeAct {r : Equiv.Perm (CTorus d L N₁ m₁ K)} {T : Finset 𝔅} {c : 𝔅} :
    c ∈ cubeAct r T ↔ ∃ b ∈ T, cubeMap r b = c := by
  classical
  simp [cubeAct]

theorem cubeAct_eq_image_perm (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (T : Finset 𝔅) :
    cubeAct r T = T.image (cubePerm hN hr) := by
  classical
  ext c; simp [mem_cubeAct, cubePerm]

/-- **T1.** `sitesOf (r • T) = r '' sitesOf T`. -/
theorem sitesOf_cubeAct (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (T : Finset 𝔅) :
    sitesOf (cubeAct r T) = r '' sitesOf T := by
  ext x
  simp only [mem_sitesOf, mem_cubeAct, Set.mem_image]
  constructor
  · rintro ⟨c, ⟨b, hb, rfl⟩, hx⟩
    rw [box_cubeMap hN hr] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, ⟨b, hb, hy⟩, rfl⟩
  · rintro ⟨y, ⟨b, hb, hy⟩, rfl⟩
    refine ⟨cubeMap r b, ⟨b, hb, rfl⟩, ?_⟩
    rw [box_cubeMap hN hr]
    exact ⟨y, hy, rfl⟩

theorem cubeAct_cubeAct (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (T : Finset 𝔅) :
    cubeAct r⁻¹ (cubeAct r T) = T := by
  ext c
  simp only [mem_cubeAct]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    rwa [cubeMap_inv hN hr]
  · intro hc
    exact ⟨cubeMap r c, ⟨c, hc, rfl⟩, cubeMap_inv hN hr c⟩

end CubeAction

section Transport

variable {d n : ℕ}

/-- The family of boxes obtained by moving a family `𝒦` of boxes by the permutation `e`. -/
def imgFam (s a : ℕ) (e : Equiv.Perm (Torus d n)) (𝒦 : Set (Torus d n)) : Set (Torus d n) :=
  {b' | Aligned s b' ∧ ∃ b ∈ 𝒦, e '' box b a = box b' a}

theorem imgFam_sub {s a : ℕ} {e : Equiv.Perm (Torus d n)} {X 𝒦 : Set (Torus d n)}
    (h : ∀ b ∈ 𝒦, Aligned s b ∧ box b a ⊆ X) :
    ∀ b' ∈ imgFam s a e 𝒦, Aligned s b' ∧ box b' a ⊆ e '' X := by
  rintro b' ⟨hb', b, hb, hbb⟩
  exact ⟨hb', by rw [← hbb]; exact Set.image_mono (h b hb).2⟩

theorem imgFam_cover {s a : ℕ} {e : Equiv.Perm (Torus d n)} (he : GoodMap s a e)
    {X 𝒦 : Set (Torus d n)} (hal : ∀ b ∈ 𝒦, Aligned s b)
    (h : ∀ z ∈ X, ∃ b ∈ 𝒦, z ∈ box b a) :
    ∀ z ∈ e '' X, ∃ b' ∈ imgFam s a e 𝒦, z ∈ box b' a := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨b, hb, hzb⟩ := h z hz
  obtain ⟨b', hb', hbb⟩ := he.boxes b (hal b hb)
  exact ⟨b', ⟨hb', b, hb, hbb⟩, by rw [← hbb]; exact ⟨z, hzb, rfl⟩⟩

theorem imgFam_meets {s a : ℕ} {e : Equiv.Perm (Torus d n)} {𝒦 : Set (Torus d n)}
    {W : Finset (Torus d n)} (h : ∀ b ∈ 𝒦, ∃ x ∈ W, x ∈ box b a) :
    ∀ b' ∈ imgFam s a e 𝒦, ∃ x ∈ W.image e, x ∈ box b' a := by
  classical
  rintro b' ⟨-, b, hb, hbb⟩
  obtain ⟨x, hx, hxb⟩ := h b hb
  exact ⟨e x, Finset.mem_image_of_mem _ hx, by rw [← hbb]; exact ⟨x, hxb, rfl⟩⟩

theorem connStruct_image {s a : ℕ} {e : Equiv.Perm (Torus d n)} (he : GoodMap s a e)
    {W : Finset (Torus d n)} {E : Finset (Torus d n × Torus d n)} (h : ConnStruct W E) :
    ConnStruct (W.image e) (E.image (Prod.map e e)) := by
  classical
  obtain ⟨hne, hE, hc⟩ := h
  refine ⟨hne.image _, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨h1, h2, h3⟩ := hE q hq
    exact ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, he.nbr _ _ h3⟩
  · intro x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hy
    refine (hc x0 hx0 y0 hy0).lift e ?_
    intro p q hpq
    rcases hpq with hpq | hpq
    · exact Or.inl (Finset.mem_image.2 ⟨(p, q), hpq, rfl⟩)
    · exact Or.inr (Finset.mem_image.2 ⟨(q, p), hpq, rfl⟩)

theorem siteConnected_image {s a : ℕ} {e : Equiv.Perm (Torus d n)} (he : GoodMap s a e)
    {X : Set (Torus d n)}
    (hc : ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen (fun p q => p ∈ X ∧ q ∈ X ∧ Nbr p q) x y) :
    ∀ x ∈ e '' X, ∀ y ∈ e '' X,
      Relation.ReflTransGen (fun p q => p ∈ e '' X ∧ q ∈ e '' X ∧ Nbr p q) x y := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine (hc x hx y hy).lift e ?_
  rintro p q ⟨hp, hq, hpq⟩
  exact ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩, he.nbr _ _ hpq⟩

theorem bondCost_image_const (ω : Torus d n → Torus d n → ℝ) (c : ℝ) (hω : ∀ x y, ω x y = c)
    (e : Equiv.Perm (Torus d n)) (E : Finset (Torus d n × Torus d n)) :
    bondCost ω (E.image (Prod.map e e)) = bondCost ω E := by
  classical
  have hinj : Function.Injective (Prod.map e e) := fun p q h => by
    have := Prod.ext_iff.1 h
    exact Prod.ext (e.injective this.1) (e.injective this.2)
  unfold bondCost
  simp only [hω, Finset.sum_const, Finset.card_image_of_injective _ hinj]

end Transport

section Invariance

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The set of admissible values defining `sizeJ` is unchanged by a paving symmetry. -/
theorem sizeJ_image (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (X : Set (CTorus d L N₁ m₁ K)) :
    sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (r '' X) =
      sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K X := by
  have key : ∀ (r : Equiv.Perm (CTorus d L N₁ m₁ K)),
      r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K →
      ∀ X : Set (CTorus d L N₁ m₁ K),
      {x | ∃ 𝒦 W E, ChosenOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K X 𝒦 ∧
          ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ K 𝒦 W ∧
          x = bondCost (scaleW L m₀ m₁ K) E} ⊆
      {x | ∃ 𝒦 W E, ChosenOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K (r '' X) 𝒦 ∧
          ConnStruct W E ∧ (↑W ⊆ r '' X) ∧ MeetsOne m₀ K 𝒦 W ∧
          x = bondCost (scaleW L m₀ m₁ K) E} := by
    intro r hr X x ⟨𝒦, W, E, hch, hcs, hW, hm, hx⟩
    have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
    have he := (pavingSymGroup_goodMap (m₀ := m₀) (j := K) hN le_rfl hr)
    classical
    refine ⟨imgFam (cellSide L m₀ m₁ K) (L * cellSide L m₀ m₁ K) r 𝒦, W.image r,
      E.image (Prod.map r r), ⟨imgFam_sub hch.1, imgFam_cover he (fun b hb => (hch.1 b hb).1)
        hch.2⟩, connStruct_image he hcs, ?_, imgFam_meets hm, ?_⟩
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨w, hW hw, rfl⟩
    · rw [hx]
      exact (bondCost_image_const _ _ (fun _ _ => rfl) r E).symm
  unfold sizeJ treeLenCovOne
  congr 1
  apply Set.Subset.antisymm
  · have := key r⁻¹ (inv_mem hr) (r '' X)
    have h2 : (⇑(r⁻¹)) '' (r '' X) = X := by
      rw [Set.image_image]; simp [Equiv.Perm.inv_def]
    rwa [h2] at this
  · exact key r hr X

/-- **T2.** `IsPolyDom` is invariant under the paving symmetries (both directions). -/
theorem isPolyDom_image_iff (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (X : Set (CTorus d L N₁ m₁ K)) :
    IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (r '' X) ↔
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K X := by
  refine ⟨fun h => ?_, fun h => isPolyDom_image_of_mem_pavingSymGroup hN le_rfl h hr⟩
  have := isPolyDom_image_of_mem_pavingSymGroup hN le_rfl h (inv_mem hr)
  have h2 : (⇑(r⁻¹)) '' (r '' X) = X := by
    rw [Set.image_image]; simp [Equiv.Perm.inv_def]
  rwa [h2] at this

/-- Site-connectedness transfers along a paving symmetry. -/
theorem siteConnected_image_iff (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (X : Set (CTorus d L N₁ m₁ K)) :
    SiteConnected (r '' X) ↔ SiteConnected X := by
  have h2 : (⇑(r⁻¹)) '' (r '' X) = X := by
    rw [Set.image_image]; simp [Equiv.Perm.inv_def]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := siteConnected_image (pavingSymGroup_goodMap (m₀ := m₀) (j := K) hN le_rfl
      (inv_mem hr)) h
    rwa [h2] at this
  · exact siteConnected_image (pavingSymGroup_goodMap (m₀ := m₀) (j := K) hN le_rfl hr) h

/-- The modular covering size at `Ω = univ` is invariant under the paving symmetries. -/
theorem dcovModE_univ_image (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (X : Set (CTorus d L N₁ m₁ K)) :
    dcovModE m₀ K Set.univ (r '' X) = dcovModE m₀ K Set.univ X := by
  classical
  have key : ∀ (r : Equiv.Perm (CTorus d L N₁ m₁ K)),
      r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K →
      ∀ X : Set (CTorus d L N₁ m₁ K),
      dcovModE m₀ K Set.univ (r '' X) ≤ dcovModE m₀ K Set.univ X := by
    intro r hr X
    have he := (pavingSymGroup_goodMap (m₀ := m₀) (j := K) hN le_rfl hr)
    unfold dcovModE
    refine le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E => le_iInf fun h => ?_
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hcov : ∀ z ∈ X, ∃ b ∈ 𝒦, z ∈ box b (L * cellSide L m₀ m₁ K) := by
      intro z hz
      have := h2 ⟨hz, Set.mem_univ z⟩
      simpa using this
    have hcov' := imgFam_cover he (fun b hb => (h1 b hb).1) hcov
    refine iInf_le_of_le (imgFam (cellSide L m₀ m₁ K) (L * cellSide L m₀ m₁ K) r 𝒦)
      (iInf_le_of_le (W.image r) (iInf_le_of_le (E.image (Prod.map r r))
        (iInf_le_of_le ⟨imgFam_sub h1, ?_, connStruct_image he h3, ?_, imgFam_meets h5⟩ ?_)))
    · rintro z ⟨hz, -⟩
      obtain ⟨b, hb, hzb⟩ := hcov' z hz
      exact Set.mem_iUnion₂.2 ⟨b, hb, hzb⟩
    · intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨w, h4 hw, rfl⟩
    · exact le_of_eq (congrArg ENNReal.ofReal (bondCost_image_const _ _ (fun _ _ => rfl) r E))
  apply le_antisymm (key r hr X)
  have := key r⁻¹ (inv_mem hr) (r '' X)
  have h2 : (⇑(r⁻¹)) '' (r '' X) = X := by
    rw [Set.image_image]; simp [Equiv.Perm.inv_def]
  rwa [h2] at this

/-- **T2.** `d_univ` of a set of sites is invariant under the paving symmetries. -/
theorem dOmega_univ_image (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (S : Set (CTorus d L N₁ m₁ K)) :
    dOmega m₀ K Set.univ (r '' S) = dOmega m₀ K Set.univ S := by
  classical
  have hY : ∀ S : Set (CTorus d L N₁ m₁ K), Yhat Set.univ S = S := by
    intro S; simp [Yhat]
  unfold dOmega
  rw [hY, hY]
  by_cases hc : SiteConnected S
  · have hc' := (siteConnected_image_iff hN hr S).2 hc
    simp only [hc, hc', ↓reduceIte]
    exact dcovModE_univ_image hN hr S
  · have hc' : ¬ SiteConnected (r '' S) := fun h => hc ((siteConnected_image_iff hN hr S).1 h)
    simp only [hc, hc', ↓reduceIte]

/-- **T2.** `dExt (r • T) = dExt T`. -/
theorem dExt_cubeAct (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (T : Finset 𝔅) :
    dExt (cubeAct r T) = dExt T := by
  unfold dExt
  rw [sitesOf_cubeAct hN hr, dOmega_univ_image hN hr]

end Invariance

section Root

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The index type of the roots of Theorem 3.1: a site of the next-scale torus, as typed in the
landed statements (`z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))` for `K = k + 1`). -/
abbrev RootIdx (d L N₁ m₁ K : ℕ) : Type := Torus d (N₁ * L ^ m₁ * L ^ (K - K))

theorem val_lt_rootIdx (z : RootIdx d L N₁ m₁ K) (μ : Fin d) : (z μ).val < N₁ * L ^ m₁ := by
  have := ZMod.val_lt (z μ)
  simpa using this

/-- **The root site of the coarse block `B(z)`**: the base `L^K z` of the block of side `L^K` of
the fine torus lying over the coarse site `z` (the `L^K`-aligned corner of `B(z)`). -/
def rootSite (z : RootIdx d L N₁ m₁ K) : CTorus d L N₁ m₁ K :=
  fun μ => ((L ^ K * (z μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))

/-- The coarse site of the block of side `L^K` containing the fine site `x`. -/
def blockIndex (x : CTorus d L N₁ m₁ K) : RootIdx d L N₁ m₁ K :=
  fun μ => (((x μ).val / L ^ K : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ (K - K)))

theorem rootSite_val (z : RootIdx d L N₁ m₁ K) (μ : Fin d) :
    (rootSite z μ).val = L ^ K * (z μ).val := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have : L ^ K * (z μ).val < (N₁ * L ^ m₁) * L ^ K := by
    calc L ^ K * (z μ).val < L ^ K * (N₁ * L ^ m₁) :=
          Nat.mul_lt_mul_of_pos_left (val_lt_rootIdx z μ) hL
      _ = (N₁ * L ^ m₁) * L ^ K := mul_comm _ _
  simp only [rootSite]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt this]

theorem rootSite_injective : Function.Injective (rootSite (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (K := K)) := by
  intro z z' h
  funext μ
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have h1 := congrArg (fun x : CTorus d L N₁ m₁ K => (x μ).val) h
  simp only [rootSite_val] at h1
  exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left hL h1)

theorem blockIndex_rootSite (z : RootIdx d L N₁ m₁ K) : blockIndex (rootSite z) = z := by
  funext μ
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  simp only [blockIndex, rootSite_val, Nat.mul_div_cancel_left _ hL]
  exact ZMod.natCast_zmod_val _

theorem rootSite_blockIndex (x : CTorus d L N₁ m₁ K) :
    rootSite (blockIndex x) = blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K x := by
  funext μ
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have hlt : (x μ).val / L ^ K < N₁ * L ^ m₁ * L ^ (K - K) := by
    rw [Nat.sub_self, pow_zero, mul_one]
    exact (Nat.div_lt_iff_lt_mul hL).2 (ZMod.val_lt (x μ))
  have hv : ((blockIndex x μ)).val = (x μ).val / L ^ K := by
    simp only [blockIndex]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  simp only [rootSite, hv, blockBase, cbase]

theorem blockBase_rootSite (z : RootIdx d L N₁ m₁ K) :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (rootSite z) = rootSite z := by
  rw [← rootSite_blockIndex, blockIndex_rootSite]

/-- **The root cube**: the level-`K` cube containing the root site of `B(z)`. -/
def rootCube (z : RootIdx d L N₁ m₁ K) : 𝔅 :=
  ⟨cbase (cellSide L m₀ m₁ K) (rootSite z), aligned_cbase _, Set.subset_univ _⟩

theorem rootSite_mem_box_rootCube (z : RootIdx d L N₁ m₁ K) :
    rootSite z ∈ box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K) :=
  mem_box_cbase (cellSide_pos (L := L) m₀ m₁ K) _

/-- **T3.** The root site of `B(z)` lies in the sites of `T` iff its root cube lies in `T`. -/
theorem rootSite_mem_sitesOf_iff (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    (T : Finset 𝔅) : rootSite z ∈ sitesOf T ↔ rootCube z ∈ T := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  constructor
  · intro h
    obtain ⟨b, hb, hmem⟩ := mem_sitesOf.1 h
    have : b = rootCube z :=
      Subtype.ext (cbase_eq_of_mem_box hdvd b.2.1 hmem).symm
    rwa [← this]
  · intro h
    exact mem_sitesOf.2 ⟨_, h, rootSite_mem_box_rootCube z⟩

/-- The action of a permutation of the fine torus on roots: the root of the transformed block,
i.e. the coarse site of the block containing `r (rootSite z)`. -/
def rootAct (r : Equiv.Perm (CTorus d L N₁ m₁ K)) (z : RootIdx d L N₁ m₁ K) :
    RootIdx d L N₁ m₁ K :=
  blockIndex (r (rootSite z))

/-- **T3.** The root of the transformed block is `blockBase L K (r (rootSite z))`. -/
theorem rootSite_rootAct (r : Equiv.Perm (CTorus d L N₁ m₁ K)) (z : RootIdx d L N₁ m₁ K) :
    rootSite (rootAct r z) =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r (rootSite z)) :=
  rootSite_blockIndex _

omit [NeZero L] in
theorem pow_dvd_cellSide : L ^ K ∣ cellSide L m₀ m₁ K :=
  pow_dvd_pow L (by omega)

omit [NeZero N₁] [NeZero L] in
theorem pow_dvd_torus : L ^ K ∣ (N₁ * L ^ m₁) * L ^ K := dvd_mul_left _ _

/-- A paving symmetry maps the `L^K`-block of a site onto the `L^K`-block of its image. -/
theorem image_box_blockBase {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (y : CTorus d L N₁ m₁ K) :
    r '' box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K y) (L ^ K) =
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y)) (L ^ K) := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨b', hb', himg⟩ :=
    (goodMap_of_mem_pavingSymGroup (L ^ K) (L ^ K) (pow_dvd_cellSide (m₀ := m₀)) pow_dvd_torus
      dvd_rfl hr).1.boxes (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K y)
      (aligned_cbase _)
  have hmem : r y ∈ box b' (L ^ K) :=
    himg ▸ ⟨y, mem_box_cbase hL y, rfl⟩
  have : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y) = b' :=
    cbase_eq_of_mem_box pow_dvd_torus hb' hmem
  rw [this, himg]

/-- **T3 (covariance).** If `y ∈ X` and `X` is a union of `L^K`-blocks, then the root
`blockBase L K (r y)` of the transformed block lies in `r '' X`. -/
theorem blockBase_mem_image {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {X : Set (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X, ∀ w, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K x → w ∈ X)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ X) :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y) ∈ r '' X := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have h0 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y) ∈
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y)) (L ^ K) :=
    mem_box_self _ hL
  rw [← image_box_blockBase (m₀ := m₀) hr y] at h0
  obtain ⟨w, hw, hwe⟩ := h0
  refine ⟨w, hX y hy w ?_, hwe⟩
  exact cbase_eq_of_mem_box pow_dvd_torus (aligned_cbase _) hw

/-- The `L^K`-block of the preimage of the root of the image block is the block of `y`. -/
theorem blockBase_inv_blockBase {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (y : CTorus d L N₁ m₁ K) :
    blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K
        (r⁻¹ (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y))) =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K y := by
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  have h0 : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y) ∈
      box (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y)) (L ^ K) :=
    mem_box_self _ hL
  rw [← image_box_blockBase (m₀ := m₀) hr y] at h0
  obtain ⟨w, hw, hwe⟩ := h0
  have : r⁻¹ (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y)) = w := by
    rw [← hwe]; simp [Equiv.Perm.inv_def]
  rw [this]
  exact cbase_eq_of_mem_box pow_dvd_torus (aligned_cbase _) hw

theorem cbase_val {n : ℕ} [NeZero n] {a : ℕ} (z : Torus d n) (μ : Fin d) :
    ((cbase a z) μ).val = a * ((z μ).val / a) := by
  have hlt : a * ((z μ).val / a) < n :=
    lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  simp only [cbase]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- A polymer of `𝒟_K` is a union of `L^K`-blocks. -/
theorem blockUnion_of_isPolyDom (hN : L ^ m₀ ∣ N₁) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K X) :
    ∀ x ∈ X, ∀ w, blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K w =
      blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K x → w ∈ X := by
  intro x hx w hw
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have hL : 0 < L ^ K := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨-, ⟨𝒦, h1, h2⟩, -⟩ := hX
  obtain ⟨b, hb, hxb⟩ := h2 x hx
  obtain ⟨c, hc⟩ := (pow_dvd_cellSide (L := L) (K := K) (m₀ := m₀) (m₁ := m₁))
  have hsame : cbase (cellSide L m₀ m₁ K) w = cbase (cellSide L m₀ m₁ K) x := by
    funext μ
    have hμ := congrArg (fun t : CTorus d L N₁ m₁ K => (t μ).val) hw
    simp only [blockBase, cbase_val] at hμ
    have hq : (w μ).val / L ^ K = (x μ).val / L ^ K := Nat.eq_of_mul_eq_mul_left hL hμ
    simp only [cbase]
    rw [hc, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hq]
  have hwx : w ∈ box (cbase (cellSide L m₀ m₁ K) x) (cellSide L m₀ m₁ K) := by
    rw [← hsame]; exact mem_box_cbase ha0 w
  exact (h1 b hb).2 (cell_subset_cube hdvd ha0 (h1 b hb).1 hxb hwx)

end Root

section Rooted

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- **T4 (fibre, (R4)).** Over a fixed pair `(y, X)` there is at most one pair `(z, T)` with
`rootSite z = y` and `sitesOf T = X`. -/
theorem fibre_subsingleton (hN : L ^ m₀ ∣ N₁) (y : CTorus d L N₁ m₁ K)
    (X : Set (CTorus d L N₁ m₁ K)) :
    {p : RootIdx d L N₁ m₁ K × Finset 𝔅 | rootSite p.1 = y ∧ sitesOf p.2 = X}.Subsingleton := by
  rintro ⟨z, T⟩ ⟨h1, h2⟩ ⟨z', T'⟩ ⟨h1', h2'⟩
  have hz : z = z' := rootSite_injective (h1.trans h1'.symm)
  have hT : T = T' := sitesOf_injective hN (le_refl K) (h2.trans h2'.symm)
  rw [hz, hT]

open Classical in
/-- **The rooted sum** `Σ_{z : rootSite z = y} Σ_{T : sitesOf T = X} e z T` of a coefficient
family `e` indexed by a root `z` and a finite set `T` of level-`K` cubes. -/
noncomputable def rootedSum (e : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ)
    (y : CTorus d L N₁ m₁ K) (X : Set (CTorus d L N₁ m₁ K)) : ℂ :=
  ∑ z ∈ Finset.univ.filter (fun z => rootSite z = y),
    ∑ T ∈ Finset.univ.filter (fun T : Finset 𝔅 => sitesOf T = X), e z T

/-- At most one summand of the rooted sum is non-zero. -/
theorem rootedSum_nonzero_subsingleton (hN : L ^ m₀ ∣ N₁)
    (e : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ) (y : CTorus d L N₁ m₁ K)
    (X : Set (CTorus d L N₁ m₁ K)) :
    {p : RootIdx d L N₁ m₁ K × Finset 𝔅 |
      rootSite p.1 = y ∧ sitesOf p.2 = X ∧ e p.1 p.2 ≠ 0}.Subsingleton := by
  intro p hp q hq
  exact fibre_subsingleton hN y X ⟨hp.1, hp.2.1⟩ ⟨hq.1, hq.2.1⟩

/-- If `(z, T)` lies over `(y, X)`, the rooted sum is `e z T`. -/
theorem rootedSum_eq_of_pair (hN : L ^ m₀ ∣ N₁)
    (e : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ) {y : CTorus d L N₁ m₁ K}
    {X : Set (CTorus d L N₁ m₁ K)} {z : RootIdx d L N₁ m₁ K} {T : Finset 𝔅}
    (hz : rootSite z = y) (hT : sitesOf T = X) : rootedSum e y X = e z T := by
  classical
  unfold rootedSum
  have h1 : Finset.univ.filter (fun z' : RootIdx d L N₁ m₁ K => rootSite z' = y) = {z} := by
    ext z'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => rootSite_injective (h.trans hz.symm), fun h => h ▸ hz⟩
  have h2 : Finset.univ.filter (fun T' : Finset 𝔅 => sitesOf T' = X) = {T} := by
    ext T'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => sitesOf_injective hN (le_refl K) (h.trans hT.symm), fun h => h ▸ hT⟩
  rw [h1, h2]
  simp

/-- `rootedSum e (rootSite z) (sitesOf T) = e z T`. -/
theorem rootedSum_rootSite_sitesOf (hN : L ^ m₀ ∣ N₁)
    (e : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ) (z : RootIdx d L N₁ m₁ K) (T : Finset 𝔅) :
    rootedSum e (rootSite z) (sitesOf T) = e z T :=
  rootedSum_eq_of_pair hN e rfl rfl

/-- The rooted sum vanishes when no pair lies over `(y, X)`. -/
theorem rootedSum_eq_zero (e : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)}
    (h : ¬ ∃ (z : RootIdx d L N₁ m₁ K) (T : Finset 𝔅), rootSite z = y ∧ sitesOf T = X) :
    rootedSum e y X = 0 := by
  classical
  unfold rootedSum
  refine Finset.sum_eq_zero fun z hz => Finset.sum_eq_zero fun T hT => ?_
  exact absurd ⟨z, T, (Finset.mem_filter.1 hz).2, (Finset.mem_filter.1 hT).2⟩ h

/-- **T5 (covariance).** If `e' (r z) (r • T) = e z T`, then the rooted sum at the root
`blockBase L K (r y)` of the transformed block and the polymer `r '' X` equals the rooted sum at
`(y, X)`, for an `L^K`-aligned site `y`. -/
theorem rootedSum_covariant (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {e e' : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ}
    (hcov : ∀ z T, e' (rootAct r z) (cubeAct r T) = e z T)
    {y : CTorus d L N₁ m₁ K}
    (hy : blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K y = y)
    (X : Set (CTorus d L N₁ m₁ K)) :
    rootedSum e' (blockBase (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L K (r y)) (r '' X) =
      rootedSum e y X := by
  by_cases hex : ∃ (z : RootIdx d L N₁ m₁ K) (T : Finset 𝔅), rootSite z = y ∧ sitesOf T = X
  · obtain ⟨z, T, hz, hT⟩ := hex
    rw [rootedSum_eq_of_pair hN e hz hT,
      rootedSum_eq_of_pair hN e' (z := rootAct r z) (T := cubeAct r T) ?_ ?_, hcov]
    · rw [rootSite_rootAct, hz]
    · rw [sitesOf_cubeAct hN hr, hT]
  · rw [rootedSum_eq_zero e hex]
    refine rootedSum_eq_zero e' ?_
    rintro ⟨z', T', hz', hT'⟩
    refine hex ⟨rootAct r⁻¹ z', cubeAct r⁻¹ T', ?_, ?_⟩
    · rw [rootSite_rootAct, hz', blockBase_inv_blockBase hr, hy]
    · rw [sitesOf_cubeAct hN (inv_mem hr), hT']
      ext x; simp [Equiv.Perm.inv_def]

/-- **T5 (bound).** If `‖e z T‖ ≤ B exp(-κ dExt T)` for all `z, T`, and a non-zero `e z T` has
`dExt T = sizeJ (sitesOf T)` (the active-size identity of `RootActiveSize`), then
`‖rootedSum e y X‖ ≤ B exp(-κ sizeJ X)`. -/
theorem rootedSum_norm_le_of_activeSize (hN : L ^ m₀ ∣ N₁)
    {e : RootIdx d L N₁ m₁ K → Finset 𝔅 → ℂ} {B κ : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z T, ‖e z T‖ ≤ B * Real.exp (-κ * dExt T))
    (hsize : ∀ z T, e z T ≠ 0 →
      dExt T = sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (sitesOf T))
    (y : CTorus d L N₁ m₁ K) (X : Set (CTorus d L N₁ m₁ K)) :
    ‖rootedSum e y X‖ ≤
      B * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K X) := by
  by_cases hex : ∃ (z : RootIdx d L N₁ m₁ K) (T : Finset 𝔅), rootSite z = y ∧ sitesOf T = X
  · obtain ⟨z, T, hz, hT⟩ := hex
    rw [rootedSum_eq_of_pair hN e hz hT]
    by_cases h0 : e z T = 0
    · rw [h0, norm_zero]; positivity
    · have := hbound z T
      rwa [hsize z T h0, hT] at this
  · rw [rootedSum_eq_zero e hex, norm_zero]; positivity

end Rooted

end Balaban.Fluctuation
