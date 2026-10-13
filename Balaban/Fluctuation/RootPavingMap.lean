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

end Balaban.Fluctuation
