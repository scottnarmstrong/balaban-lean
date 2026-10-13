/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.BoxTransport
public import Balaban.Fluctuation.RootPavingMap
public import Balaban.SmallField.Def6Terms
public import Balaban.Fluctuation.CubeSystem
public import Balaban.Fluctuation.InteractionEnergy
public import Balaban.Fluctuation.LevelLocalCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The geometry of one renormalization step on two tori

Two tori `CTorus d L N₁ m₁ K` and `CTorus d L N₁' m₁ K` of sides `N₁ L^m₁ L^K` and
`N₁' L^m₁ L^K` are identified on a centred box `{c | ∀ μ, |valMinAbs (c μ)| ≤ r}` by
`Balaban.Polymer.boxMap`.  This file shows that the lattice geometry of the step is carried by
this identification:

* aligned boxes (cells and `π'`-cubes) go to aligned boxes with the corresponding base point
  (`image_box_boxMap`, `aligned_boxMap`);
* the finite sets of cubes `CubeB m₀ j univ` correspond through `cubeMap`, with
  `sitesOf` of the image equal to the image of `sitesOf` (`sitesOf_image_cubeMap`);
* the predicates `IsDj`, `IsPolyDom` and the functionals `sizeJ`, `dOmega` (at `Ω = univ`) of a
  set inside the box agree with those of its image; `dExt` agrees whenever `dOmega` is finite;
* the root sites, root cubes and block indices of corresponding coarse sites correspond.

No divisibility between `N₁` and `N₁'` is used: only `L^m₀ ∣ N₁` and `L^m₀ ∣ N₁'` (so that the
cell side divides both torus sides), and the box bound `2 r + L * cellSide < min` of the two sides.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale

/-! ### Generic lemmas on two tori `Torus d n`, `Torus d n'` -/

section Generic

variable {d n n' r : ℕ}

theorem boxMap_inj {hm' : 2 * r + 1 < n'} {a b : Torus d n} (ha : InBox d r n a)
    (hb : InBox d r n b) (h : boxMap n n' a = boxMap n n' b) : a = b := by
  rw [← boxMap_boxMap hm' ha, h, boxMap_boxMap hm' hb]

theorem step_boxMap_iff (hm : 2 * r + 1 < n) (hm' : 2 * r + 1 < n') {a b : Torus d n}
    (ha : InBox d r n a) (hb : InBox d r n b) (μ : Fin d) :
    b = a + Pi.single μ 1 ↔ boxMap n n' b = boxMap n n' a + Pi.single μ 1 := by
  rw [step_iff hm ha hb, step_iff hm' (inBox_boxMap hm' ha) (inBox_boxMap hm' hb)]
  have e1 : (fun ν => (boxMap n n' b ν).valMinAbs) = fun ν => (b ν).valMinAbs :=
    funext (valMinAbs_boxMap hm' hb)
  have e2 : (fun ν => (boxMap n n' a ν).valMinAbs) = fun ν => (a ν).valMinAbs :=
    funext (valMinAbs_boxMap hm' ha)
  rw [e1, e2]

/-- Nearest-neighbour adjacency is preserved and reflected inside the box. -/
theorem nbr_boxMap_iff (hm : 2 * r + 1 < n) (hm' : 2 * r + 1 < n') {a b : Torus d n}
    (ha : InBox d r n a) (hb : InBox d r n b) :
    Nbr a b ↔ Nbr (boxMap n n' a) (boxMap n n' b) := by
  unfold Nbr
  exact exists_congr fun μ => or_congr (step_boxMap_iff hm hm' ha hb μ)
    (step_boxMap_iff hm hm' hb ha μ)

/-- `boxMap` is additive on a translation by `natT w` that stays inside the box. -/
theorem boxMap_add_natT {a : ℕ} (hn : 2 * r + a < n) {b : Torus d n} {w : Fin d → ℕ}
    (hw : ∀ μ, w μ < a) (hb : InBox d r n b) (hbw : InBox d r n (b + natT w)) :
    boxMap n n' (b + natT w) = boxMap n n' b + natT w := by
  funext μ
  have h1 := hb μ
  have h2 := hbw μ
  have h3 := hw μ
  have hc : ((((b + natT w : Torus d n) μ).valMinAbs : ℤ) : ZMod n) =
      (((b μ).valMinAbs + (w μ : ℤ) : ℤ) : ZMod n) := by
    rw [ZMod.coe_valMinAbs]
    push_cast
    simp [natT]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  have h4 : ((b μ).valMinAbs + (w μ : ℤ)) - ((b + natT w : Torus d n) μ).valMinAbs = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd hc ?_
    rw [abs_le] at h1 h2
    rw [abs_lt]
    constructor <;> omega
  have h5 : ((b + natT w : Torus d n) μ).valMinAbs = (b μ).valMinAbs + (w μ : ℤ) := by omega
  show ((((b + natT w : Torus d n) μ).valMinAbs : ℤ) : ZMod n') = _
  rw [h5]
  simp [natT, boxMap]

/-- The image of an aligned box inside the centred box is the box over the image base point. -/
theorem image_box_boxMap {a : ℕ} (hn : 2 * r + a < n) (ha : 0 < a) {b : Torus d n}
    (hbox : ∀ x ∈ box b a, InBox d r n x) :
    boxMap n n' '' box b a = box (boxMap n n' b) a := by
  have hb : InBox d r n b := hbox b (mem_box_self b ha)
  ext x'
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, boxMap_add_natT hn hw hb (hbox _ ⟨w, hw, rfl⟩)⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨b + natT w, ⟨w, hw, rfl⟩, boxMap_add_natT hn hw hb (hbox _ ⟨w, hw, rfl⟩)⟩

/-- Alignment is preserved by `boxMap`, if the grid side divides both torus sides. -/
theorem aligned_boxMap [NeZero n] [NeZero n'] {a : ℕ} (ha : a ∣ n) (ha' : a ∣ n')
    {b : Torus d n} (hb : Aligned a b) : Aligned a (boxMap n n' b) := by
  intro μ
  have h1 := hb μ
  have hv : (a : ℤ) ∣ (b μ).valMinAbs := by
    have e : (((b μ).val : ℤ) : ZMod n) = (((b μ).valMinAbs : ℤ) : ZMod n) := by
      rw [ZMod.coe_valMinAbs]; simp
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at e
    have h2 : (a : ℤ) ∣ ((b μ).val : ℤ) := by
      exact_mod_cast Nat.dvd_of_mod_eq_zero h1
    have h3 : (a : ℤ) ∣ (n : ℤ) := by exact_mod_cast ha
    have h4 := dvd_add (dvd_trans h3 e) h2
    simpa using h4
  have h5 : (a : ℤ) ∣ (n' : ℤ) := by exact_mod_cast ha'
  have h6 : (((boxMap n n' b μ).val : ℕ) : ℤ) = (b μ).valMinAbs % (n' : ℤ) := by
    show ((((b μ).valMinAbs : ℤ) : ZMod n').val : ℤ) = _
    exact ZMod.val_intCast _
  have h7 : (a : ℤ) ∣ (((boxMap n n' b μ).val : ℕ) : ℤ) := by
    rw [h6, Int.emod_def]
    exact dvd_sub hv (dvd_mul_of_dvd_left h5 _)
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp h7)

theorem image_image_boxMap (hm' : 2 * r + 1 < n') {X : Set (Torus d n)}
    (hX : ∀ x ∈ X, InBox d r n x) : boxMap n' n '' (boxMap n n' '' X) = X := by
  rw [Set.image_image]
  conv_rhs => rw [← Set.image_id X]
  exact Set.image_congr (fun x hx => boxMap_boxMap hm' (hX x hx))

theorem connStruct_image (hm : 2 * r + 1 < n) (hm' : 2 * r + 1 < n') {W : Finset (Torus d n)}
    {E : Finset (Torus d n × Torus d n)} (hW : ∀ w ∈ W, InBox d r n w) (h : ConnStruct W E) :
    ConnStruct (W.image (boxMap n n')) (E.image (Prod.map (boxMap n n') (boxMap n n'))) := by
  obtain ⟨hne, hE, hconn⟩ := h
  refine ⟨hne.image _, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨h1, h2, h3⟩ := hE q hq
    exact ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2,
      (nbr_boxMap_iff hm hm' (hW _ h1) (hW _ h2)).1 h3⟩
  · intro x hx y hy
    obtain ⟨x, hx1, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y, hy1, rfl⟩ := Finset.mem_image.1 hy
    refine Relation.ReflTransGen.lift (boxMap n n') ?_ _ _ (hconn x hx1 y hy1)
    intro u v huv
    rcases huv with h | h
    · exact Or.inl (Finset.mem_image_of_mem (Prod.map (boxMap n n') (boxMap n n')) h)
    · exact Or.inr (Finset.mem_image_of_mem (Prod.map (boxMap n n') (boxMap n n')) h)

theorem bondCost_scaleW_image {L m₀ m₁ j : ℕ} (hm' : 2 * r + 1 < n') {W : Finset (Torus d n)}
    {E : Finset (Torus d n × Torus d n)} (hW : ∀ w ∈ W, InBox d r n w)
    (hE : ∀ p ∈ E, p.1 ∈ W ∧ p.2 ∈ W) :
    bondCost (scaleW L m₀ m₁ j) (E.image (Prod.map (boxMap n n') (boxMap n n'))) =
      bondCost (scaleW L m₀ m₁ j) E := by
  have hinj : Set.InjOn (Prod.map (boxMap n n') (boxMap n n')) (E : Set (Torus d n × Torus d n)) := by
    intro p hp q hq h
    have hp' := hE p hp
    have hq' := hE q hq
    have h1 : boxMap n n' p.1 = boxMap n n' q.1 := congrArg Prod.fst h
    have h2 : boxMap n n' p.2 = boxMap n n' q.2 := congrArg Prod.snd h
    exact Prod.ext (boxMap_inj (hm' := hm') (hW _ hp'.1) (hW _ hq'.1) h1)
      (boxMap_inj (hm' := hm') (hW _ hp'.2) (hW _ hq'.2) h2)
  simp only [bondCost, scaleW, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_image_of_injOn hinj]

end Generic


/-! ### Base points of cells, block indices, root sites -/

section Coord

variable {d n n' r : ℕ}

/-- The base point of the cell containing a site of the box goes to the base point of the cell
containing the image, provided the cell stays inside the box. -/
theorem cbase_boxMap [NeZero n] [NeZero n'] {a : ℕ} (ha : a ∣ n) (ha' : a ∣ n') (ha0 : 0 < a)
    (hn : 2 * r + a < n) (x : Torus d n) (hbox : ∀ y ∈ box (cbase a x) a, InBox d r n y) :
    boxMap n n' (cbase a x) = cbase a (boxMap n n' x) := by
  have himg : boxMap n n' '' box (cbase a x) a = box (boxMap n n' (cbase a x)) a :=
    image_box_boxMap hn ha0 hbox
  have hx' : boxMap n n' x ∈ box (boxMap n n' (cbase a x)) a := by
    rw [← himg]; exact ⟨x, mem_box_cbase ha0 x, rfl⟩
  exact (cbase_eq_of_mem_box ha' (aligned_boxMap ha ha' (aligned_cbase x)) hx').symm

theorem blockCoord_intCast {n a c : ℕ} [NeZero n] (hn : n = a * c) (ha : 0 < a) (ξ : ℤ) :
    blockCoord a c ((ξ : ℤ) : ZMod n) = ((ξ / (a : ℤ) : ℤ) : ZMod c) := by
  have h1 : (((ξ : ZMod n).val : ℕ) : ℤ) = ξ % (n : ℤ) := ZMod.val_intCast ξ
  have h3 : (n : ℤ) = (a : ℤ) * c := by exact_mod_cast hn
  have h2 : ξ = ξ % (n : ℤ) + (a : ℤ) * ((c : ℤ) * (ξ / (n : ℤ))) := by
    have := Int.emod_add_mul_ediv ξ (n : ℤ)
    linear_combination (-1 : ℤ) * this + (ξ / (n : ℤ)) * h3
  have h4 : ξ / (a : ℤ) = (ξ % (n : ℤ)) / (a : ℤ) + (c : ℤ) * (ξ / (n : ℤ)) := by
    conv_lhs => rw [h2]
    rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast ha.ne')]
  have h5 : (((ξ : ZMod n).val / a : ℕ) : ℤ) = (ξ % (n : ℤ)) / (a : ℤ) := by
    rw [Int.natCast_div, h1]
  unfold blockCoord
  rw [show (((ξ : ZMod n).val / a : ℕ) : ZMod c) = ((((ξ : ZMod n).val / a : ℕ) : ℤ) : ZMod c) from
    (Int.cast_natCast _).symm, h5, h4]
  push_cast
  simp

theorem rootCoord_intCast {n a c : ℕ} [NeZero c] (hn : n = a * c) (ζ : ℤ) :
    ((a * ((ζ : ZMod c).val) : ℕ) : ZMod n) = ((a * ζ : ℤ) : ZMod n) := by
  have h1 : (((ζ : ZMod c).val : ℕ) : ℤ) = ζ % (c : ℤ) := ZMod.val_intCast ζ
  have h3 : (n : ℤ) = (a : ℤ) * c := by exact_mod_cast hn
  rw [show ((a * ((ζ : ZMod c).val) : ℕ) : ZMod n) = (((a * ((ζ : ZMod c).val) : ℕ) : ℤ) : ZMod n)
    from (Int.cast_natCast _).symm]
  refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ⟨ζ / (c : ℤ), ?_⟩
  push_cast
  rw [h1, h3, Int.emod_def]
  ring

/-- The block of a site inside the box, in centred coordinates: the block map commutes with
`boxMap` when the block indices of the box stay inside the box `|valMinAbs| ≤ rc` of the coarse
tori (`r < L^j * rc`). -/
theorem jBlock_boxMap {L N₀ N₀' k j rc : ℕ} [NeZero L] [NeZero N₀] [NeZero N₀'] (hj : j ≤ k)
    (hrc : r < L ^ j * rc) (hc : 2 * rc + 1 < N₀ * L ^ (k - j))
    (x : Torus d (N₀ * L ^ k))
    (hx : InBox d r (N₀ * L ^ k) x) :
    jBlock d L N₀' k j (boxMap (N₀ * L ^ k) (N₀' * L ^ k) x) =
      boxMap (N₀ * L ^ (k - j)) (N₀' * L ^ (k - j)) (jBlock d L N₀ k j x) := by
  have ha : 0 < L ^ j := pow_pos (NeZero.pos L) j
  funext μ
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = (x μ).valMinAbs := ⟨_, rfl⟩
  have hxμ : x μ = ((ξ : ℤ) : ZMod (N₀ * L ^ k)) := by rw [hξ, ZMod.coe_valMinAbs]
  have hξr : |ξ| ≤ r := by rw [hξ]; exact hx μ
  have hq : |ξ / ((L ^ j : ℕ) : ℤ)| ≤ rc := by
    have hapos : (0 : ℤ) < ((L ^ j : ℕ) : ℤ) := by exact_mod_cast ha
    have hrc' : (r : ℤ) < ((L ^ j : ℕ) : ℤ) * rc := by exact_mod_cast hrc
    rw [abs_le] at hξr ⊢
    constructor
    · exact (Int.le_ediv_iff_mul_le hapos).2 (by nlinarith)
    · exact (Int.ediv_lt_iff_lt_mul hapos).2 (by nlinarith) |>.le
  have e1 : jBlock d L N₀ k j x μ = (((ξ / ((L ^ j : ℕ) : ℤ) : ℤ)) : ZMod (N₀ * L ^ (k - j))) := by
    show blockCoord (L ^ j) _ (x μ) = _
    rw [hxμ]
    exact blockCoord_intCast (side_eq hj) ha ξ
  have e2 : boxMap (N₀ * L ^ k) (N₀' * L ^ k) x μ = ((ξ : ℤ) : ZMod (N₀' * L ^ k)) := by
    show (((x μ).valMinAbs : ℤ) : ZMod (N₀' * L ^ k)) = _
    rw [← hξ]
  show blockCoord (L ^ j) _ (boxMap (N₀ * L ^ k) (N₀' * L ^ k) x μ) =
    (((jBlock d L N₀ k j x μ).valMinAbs : ℤ) : ZMod (N₀' * L ^ (k - j)))
  rw [e2, e1, valMinAbs_intCast_of_abs_le hc hq]
  exact blockCoord_intCast (side_eq hj) ha ξ

end Coord

/-! ### The step geometry on `CTorus` -/

section Step

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {m₀ j r : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "𝓑" => InBox d r ((N₁ * L ^ m₁) * L ^ K)

theorem two_r_one_lt {n : ℕ}
    (hr : 2 * r + L * cellSide L m₀ m₁ j < n) : 2 * r + 1 < n := by
  have := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos (L := L) m₀ m₁ j)
  omega

theorem two_r_cell_lt {n : ℕ}
    (hr : 2 * r + L * cellSide L m₀ m₁ j < n) : 2 * r + cellSide L m₀ m₁ j < n := by
  have := Nat.le_mul_of_pos_left (cellSide L m₀ m₁ j) (Nat.pos_of_ne_zero (NeZero.ne L))
  omega

omit [NeZero N₁] [NeZero N₁'] in
/-- The image of a `π'`-cube inside the box is the `π'`-cube over the image base point. -/
theorem image_box_cube (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) {b : CTorus d L N₁ m₁ K}
    (hbX : box b (L * cellSide L m₀ m₁ j) ⊆ X) :
    bm '' box b (L * cellSide L m₀ m₁ j) = box (bm b) (L * cellSide L m₀ m₁ j) :=
  image_box_boxMap hr (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j))
    (fun x hx => hX x (hbX hx))

theorem family_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) {𝒦 : Set (CTorus d L N₁ m₁ K)}
    (h𝒦 : ∀ b ∈ 𝒦, Aligned (cellSide L m₀ m₁ j) b ∧ box b (L * cellSide L m₀ m₁ j) ⊆ X) :
    ∀ b' ∈ bm '' 𝒦, Aligned (cellSide L m₀ m₁ j) b' ∧
      box b' (L * cellSide L m₀ m₁ j) ⊆ bm '' X := by
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨aligned_boxMap (cellSide_dvd (K := K) (m₁ := m₁) hN hj)
    (cellSide_dvd (K := K) (m₁ := m₁) hN' hj) (h𝒦 b hb).1, ?_⟩
  rw [← image_box_cube hr hX (h𝒦 b hb).2]
  exact Set.image_mono (h𝒦 b hb).2

omit [NeZero N₁] [NeZero N₁'] in
theorem mem_box_image (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) {b z : CTorus d L N₁ m₁ K}
    (hbX : box b (L * cellSide L m₀ m₁ j) ⊆ X) (hz : z ∈ box b (L * cellSide L m₀ m₁ j)) :
    bm z ∈ box (bm b) (L * cellSide L m₀ m₁ j) := by
  rw [← image_box_cube hr hX hbX]
  exact ⟨z, hz, rfl⟩

theorem chosenOne_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) {𝒦 : Set (CTorus d L N₁ m₁ K)}
    (h : ChosenOne m₀ j X 𝒦) : ChosenOne m₀ j (bm '' X) (bm '' 𝒦) := by
  refine ⟨family_image hN hN' hj hr hX h.1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨b, hb, hzb⟩ := h.2 z hz
  exact ⟨bm b, Set.mem_image_of_mem _ hb, mem_box_image hr hX (h.1 b hb).2 hzb⟩

omit [NeZero N₁] [NeZero N₁'] in
theorem siteConnected_image (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) (h : SiteConnected X) :
    SiteConnected (bm '' X) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine Relation.ReflTransGen.lift bm ?_ _ _ (h x hx y hy)
  rintro u v ⟨hu, hv, huv⟩
  exact ⟨Set.mem_image_of_mem _ hu, Set.mem_image_of_mem _ hv,
    (nbr_boxMap_iff (two_r_one_lt hr) (two_r_one_lt hr') (hX u hu) (hX v hv)).1 huv⟩

theorem isDj_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) (h : IsDj m₀ j X) :
    IsDj m₀ j (bm '' X) := by
  refine ⟨h.1.image _, ?_, siteConnected_image hr hr' hX h.2.2⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨b, hb, hzb, hbX⟩ := h.2.1 z hz
  refine ⟨bm b, aligned_boxMap (cellSide_dvd (K := K) (m₁ := m₁) hN hj)
    (cellSide_dvd (K := K) (m₁ := m₁) hN' hj) hb, mem_box_image hr hX hbX hzb, ?_⟩
  rw [← image_box_cube hr hX hbX]
  exact Set.image_mono hbX

omit [NeZero N₁] [NeZero N₁'] in
theorem inBox_image (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    ∀ x ∈ bm '' X, InBox d r ((N₁' * L ^ m₁) * L ^ K) x := by
  rintro _ ⟨c, hc, rfl⟩
  exact inBox_boxMap (two_r_one_lt hr') (hX c hc)

omit [NeZero N₁] [NeZero N₁'] in
theorem siteConnected_image_iff (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    SiteConnected (bm '' X) ↔ SiteConnected X := by
  refine ⟨fun h => ?_, siteConnected_image hr hr' hX⟩
  have h' := siteConnected_image (N₁ := N₁') (N₁' := N₁) hr' hr (inBox_image hr' hX) h
  rwa [image_image_boxMap (two_r_one_lt hr') hX] at h'

/-- `𝒟_j`-membership of a set inside the box is the same on the two tori. -/
theorem isDj_image_iff (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    IsDj m₀ j (bm '' X) ↔ IsDj m₀ j X := by
  refine ⟨fun h => ?_, isDj_image hN hN' hj hr hr' hX⟩
  have h' := isDj_image (N₁ := N₁') (N₁' := N₁) hN' hN hj hr' hr (inBox_image hr' hX) h
  rwa [image_image_boxMap (two_r_one_lt hr') hX] at h'

theorem isPolyDom_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) (h : IsPolyDom m₀ j X) :
    IsPolyDom m₀ j (bm '' X) := by
  obtain ⟨hne, ⟨𝒦, h𝒦⟩, hconn⟩ := h
  exact ⟨hne.image _, ⟨bm '' 𝒦, chosenOne_image hN hN' hj hr hX h𝒦⟩,
    siteConnected_image hr hr' hX hconn⟩

/-- `IsPolyDom` of a set inside the box is the same on the two tori. -/
theorem isPolyDom_image_iff (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    IsPolyDom m₀ j (bm '' X) ↔ IsPolyDom m₀ j X := by
  refine ⟨fun h => ?_, isPolyDom_image hN hN' hj hr hr' hX⟩
  have h' := isPolyDom_image (N₁ := N₁') (N₁' := N₁) hN' hN hj hr' hr (inBox_image hr' hX) h
  rwa [image_image_boxMap (two_r_one_lt hr') hX] at h'

theorem treeLenCovOne_set_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) {x : ℝ}
    (hx : ∃ (𝒦 : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K))
      (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W ∧
        x = bondCost (scaleW L m₀ m₁ j) E) :
    ∃ (𝒦 : Set (CTorus d L N₁' m₁ K)) (W : Finset (CTorus d L N₁' m₁ K))
      (E : Finset (CTorus d L N₁' m₁ K × CTorus d L N₁' m₁ K)),
      ChosenOne m₀ j (bm '' X) 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ bm '' X) ∧ MeetsOne m₀ j 𝒦 W ∧
        x = bondCost (scaleW L m₀ m₁ j) E := by
  obtain ⟨𝒦, W, E, hch, hc, hW, hm, rfl⟩ := hx
  have hWX : ∀ w ∈ W, 𝓑 w := fun w hw => hX w (hW hw)
  refine ⟨bm '' 𝒦, W.image bm, E.image (Prod.map bm bm), chosenOne_image hN hN' hj hr hX hch,
    connStruct_image (two_r_one_lt hr) (two_r_one_lt hr') hWX hc, ?_, ?_,
    (bondCost_scaleW_image (two_r_one_lt hr') hWX
      (fun p hp => ⟨(hc.2.1 p hp).1, (hc.2.1 p hp).2.1⟩)).symm⟩
  · rw [Finset.coe_image]; exact Set.image_mono hW
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hxW, hxb⟩ := hm b hb
    exact ⟨bm x, Finset.mem_image_of_mem _ hxW, mem_box_image hr hX (hch.1 b hb).2 hxb⟩

/-- The covering size `treeLenCovOne` of a set inside the box is the same on the two tori. -/
theorem treeLenCovOne_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    treeLenCovOne m₀ j (bm '' X) = treeLenCovOne m₀ j X := by
  unfold treeLenCovOne
  congr 1
  ext x
  constructor
  · intro hx
    have h' := treeLenCovOne_set_image (N₁ := N₁') (N₁' := N₁) hN' hN hj hr' hr
      (inBox_image hr' hX) hx
    rw [image_image_boxMap (two_r_one_lt hr') hX] at h'
    exact h'
  · exact treeLenCovOne_set_image hN hN' hj hr hr' hX

/-- `sizeJ` of a set inside the box is the same on the two tori. -/
theorem sizeJ_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    sizeJ m₀ j (bm '' X) = sizeJ m₀ j X :=
  treeLenCovOne_image hN hN' hj hr hr' hX

theorem dcovModE_univ_image_le (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    dcovModE m₀ j Set.univ (bm '' X) ≤ dcovModE m₀ j Set.univ X := by
  unfold dcovModE
  refine le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E => le_iInf fun h => ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hWX : ∀ w ∈ W, 𝓑 w := fun w hw => hX w (h4 hw)
  have hcov : ∀ z ∈ X, ∃ b ∈ 𝒦, z ∈ box b (L * cellSide L m₀ m₁ j) := by
    intro z hz
    have := h2 ⟨hz, Set.mem_univ z⟩
    simpa using this
  have hadm : ModAdmissible m₀ j Set.univ (bm '' X) (bm '' 𝒦) (W.image bm)
      (E.image (Prod.map bm bm)) := by
    refine ⟨family_image hN hN' hj hr hX h1, ?_,
      connStruct_image (two_r_one_lt hr) (two_r_one_lt hr') hWX h3, ?_, ?_⟩
    · rintro _ ⟨⟨z, hz, rfl⟩, -⟩
      obtain ⟨b, hb, hzb⟩ := hcov z hz
      exact Set.mem_iUnion₂.2 ⟨bm b, Set.mem_image_of_mem _ hb,
        mem_box_image hr hX (h1 b hb).2 hzb⟩
    · rw [Finset.coe_image]; exact Set.image_mono h4
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨x, hxW, hxb⟩ := h5 b hb
      exact ⟨bm x, Finset.mem_image_of_mem _ hxW, mem_box_image hr hX (h1 b hb).2 hxb⟩
  refine iInf_le_of_le (bm '' 𝒦) (iInf_le_of_le (W.image bm)
    (iInf_le_of_le (E.image (Prod.map bm bm)) (iInf_le_of_le hadm ?_)))
  exact ENNReal.ofReal_le_ofReal (bondCost_scaleW_image (two_r_one_lt hr') hWX
    (fun p hp => ⟨(h3.2.1 p hp).1, (h3.2.1 p hp).2.1⟩)).le

/-- The modular covering size at `Ω = univ` of a set inside the box is the same on the two tori. -/
theorem dcovModE_univ_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    dcovModE m₀ j Set.univ (bm '' X) = dcovModE m₀ j Set.univ X := by
  refine le_antisymm (dcovModE_univ_image_le hN hN' hj hr hr' hX) ?_
  have h' := dcovModE_univ_image_le (N₁ := N₁') (N₁' := N₁) hN' hN hj hr' hr (inBox_image hr' hX)
  rwa [image_image_boxMap (two_r_one_lt hr') hX] at h'

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
theorem yhat_univ (X : Set (CTorus d L N₁ m₁ K)) : Yhat Set.univ X = X := by
  ext y; simp [Yhat]

/-- `d_Ω` at `Ω = univ` of a set inside the box is the same on the two tori. -/
theorem dOmega_univ_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X, 𝓑 x) :
    dOmega m₀ j Set.univ (bm '' X) = dOmega m₀ j Set.univ X := by
  unfold dOmega
  rw [yhat_univ, yhat_univ]
  by_cases hc : SiteConnected X
  · have hc' := siteConnected_image hr hr' hX hc
    simp only [hc, hc', ↓reduceIte]
    exact dcovModE_univ_image hN hN' hj hr hr' hX
  · have hc' : ¬ SiteConnected (bm '' X) := fun h => hc ((siteConnected_image_iff hr hr' hX).1 h)
    simp only [hc, hc', ↓reduceIte]

/-! ### Finite sets of cubes -/

/-- **The correspondence of cubes.**  The cube `b` of the first torus goes to the cube with base
point `boxMap b` of the second torus.  It is defined on all cubes; only `L^m₀ ∣ N₁`,
`L^m₀ ∣ N₁'` and `j ≤ K` (so that the cell side divides both torus sides) are used to see that
the image is aligned. -/
def cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ) :
    CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) m₀ j Set.univ :=
  ⟨bm b.1, aligned_boxMap (cellSide_dvd (K := K) (m₁ := m₁) hN hj)
    (cellSide_dvd (K := K) (m₁ := m₁) hN' hj) b.2.1, Set.subset_univ _⟩

theorem cubeMap_val (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ) :
    (cubeMap hN hN' hj b).1 = bm b.1 := rfl

/-- **`sitesOf` of the image of a finite set of cubes.**  If the sites of `T` lie in the centred
box `|valMinAbs| ≤ r`, then `sitesOf` of the corresponding set of cubes is the `boxMap`-image of
`sitesOf T`. -/
theorem sitesOf_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) :
    sitesOf (T.image (cubeMap hN hN' hj)) = bm '' sitesOf T := by
  have hbox : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L m₀ m₁ j), 𝓑 x :=
    fun b hb x hx => hT x (mem_sitesOf.2 ⟨b, hb, hx⟩)
  ext x'
  constructor
  · intro h
    obtain ⟨b', hb', hx'⟩ := mem_sitesOf.1 h
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
    rw [cubeMap_val, ← image_box_boxMap (two_r_cell_lt hr) (cellSide_pos m₀ m₁ j) (hbox b hb)]
      at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    exact ⟨x, mem_sitesOf.2 ⟨b, hb, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
    refine mem_sitesOf.2 ⟨cubeMap hN hN' hj b, Finset.mem_image_of_mem _ hb, ?_⟩
    rw [cubeMap_val, ← image_box_boxMap (two_r_cell_lt hr) (cellSide_pos m₀ m₁ j) (hbox b hb)]
    exact ⟨x, hxb, rfl⟩

omit [NeZero N₁] [NeZero N₁'] in
theorem sitesOf_subset_box_of_mem {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (K := K) m₀ j Set.univ)} (hT : ∀ x ∈ sitesOf T, 𝓑 x)
    {b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ} (hb : b ∈ T) :
    𝓑 b.1 :=
  hT _ (mem_sitesOf.2 ⟨b, hb, mem_box_self _ (cellSide_pos m₀ m₁ j)⟩)

/-- The correspondence of cubes is inverted by the correspondence in the other direction. -/
theorem cubeMap_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    {b : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ} (hb : 𝓑 b.1) :
    cubeMap hN' hN hj (cubeMap hN hN' hj b) = b :=
  Subtype.ext (boxMap_boxMap (two_r_one_lt hr') hb)

theorem image_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) :
    (T.image (cubeMap hN hN' hj)).image (cubeMap hN' hN hj) = T := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := T)]
  exact Finset.image_congr (fun b hb =>
    cubeMap_cubeMap hN hN' hj hr' (sitesOf_subset_box_of_mem hT hb))

theorem card_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) : (T.image (cubeMap hN hN' hj)).card = T.card := by
  refine Finset.card_image_of_injOn (fun b1 hb1 b2 hb2 h => ?_)
  have := congrArg (cubeMap hN' hN hj) h
  rwa [cubeMap_cubeMap hN hN' hj hr' (sitesOf_subset_box_of_mem hT hb1),
    cubeMap_cubeMap hN hN' hj hr' (sitesOf_subset_box_of_mem hT hb2)] at this

/-- `IsDj` of the sites of corresponding sets of cubes. -/
theorem isDj_sitesOf_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) :
    IsDj m₀ j (sitesOf (T.image (cubeMap hN hN' hj))) ↔ IsDj m₀ j (sitesOf T) := by
  rw [sitesOf_image_cubeMap hN hN' hj hr T hT]
  exact isDj_image_iff hN hN' hj hr hr' hT

/-- `IsPolyDom` of the sites of corresponding sets of cubes. -/
theorem isPolyDom_sitesOf_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) :
    IsPolyDom m₀ j (sitesOf (T.image (cubeMap hN hN' hj))) ↔ IsPolyDom m₀ j (sitesOf T) := by
  rw [sitesOf_image_cubeMap hN hN' hj hr T hT]
  exact isPolyDom_image_iff hN hN' hj hr hr' hT

/-- `sizeJ` of the sites of corresponding sets of cubes. -/
theorem sizeJ_sitesOf_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) :
    sizeJ m₀ j (sitesOf (T.image (cubeMap hN hN' hj))) = sizeJ m₀ j (sitesOf T) := by
  rw [sitesOf_image_cubeMap hN hN' hj hr T hT]
  exact sizeJ_image hN hN' hj hr hr' hT

/-- `d_Ω` at `Ω = univ` of the sites of corresponding sets of cubes (in `[0, ∞]`). -/
theorem dOmega_sitesOf_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) :
    dOmega m₀ j Set.univ (sitesOf (T.image (cubeMap hN hN' hj))) =
      dOmega m₀ j Set.univ (sitesOf T) := by
  rw [sitesOf_image_cubeMap hN hN' hj hr T hT]
  exact dOmega_univ_image hN hN' hj hr hr' hT

/-- **`dExt` of corresponding sets of cubes**, when `d_Ω` is finite.  (When `d_Ω = +∞` the
value of `dExt` is the constant `Mbig`, which depends on the number of sites of the torus; see
`dExt_image_cubeMap_of_top`.) -/
theorem dExt_image_cubeMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) (hfin : dOmega m₀ j Set.univ (sitesOf T) ≠ ⊤) :
    dExt (T.image (cubeMap hN hN' hj)) = dExt T := by
  have h := dOmega_sitesOf_image_cubeMap hN hN' hj hr hr' T hT
  rw [dExt_eq_toReal (by rw [h]; exact hfin), dExt_eq_toReal hfin, h]

/-- When `d_Ω = +∞`, both `dExt` values are the respective constants `Mbig`. -/
theorem dExt_image_cubeMap_of_top (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
    (hr : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (hr' : 2 * r + L * cellSide L m₀ m₁ j < (N₁' * L ^ m₁) * L ^ K)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ))
    (hT : ∀ x ∈ sitesOf T, 𝓑 x) (htop : dOmega m₀ j Set.univ (sitesOf T) = ⊤) :
    dExt T = Mbig d L N₁ m₁ K ∧ dExt (T.image (cubeMap hN hN' hj)) = Mbig d L N₁' m₁ K := by
  have h := dOmega_sitesOf_image_cubeMap hN hN' hj hr hr' T hT
  exact ⟨dExt_eq_Mbig htop, dExt_eq_Mbig (by rw [h]; exact htop)⟩

/-! ### Roots, blocks and block indices -/

/-- The block index of a fine site is carried by `boxMap` (on the coarse tori): the coarse index
of the block `B(x)` of side `L^K` is `⌊x / L^K⌋` in centred coordinates.  `rc` bounds the coarse
index in the box (`r < L^K * rc`). -/
theorem blockIndex_boxMap {rc : ℕ} (hrc : r < L ^ K * rc) (hc : 2 * rc + 1 < N₁ * L ^ m₁ * L ^ (K - K))
    (x : CTorus d L N₁ m₁ K) (hx : 𝓑 x) :
    blockIndex (bm x) = boxMap (N₁ * L ^ m₁ * L ^ (K - K)) (N₁' * L ^ m₁ * L ^ (K - K))
      (blockIndex x) :=
  jBlock_boxMap (N₀ := N₁ * L ^ m₁) (N₀' := N₁' * L ^ m₁) (le_refl K) hrc hc x hx

/-- The root site of a coarse site is carried by `boxMap`: the root site over the coarse site `z`
(`|valMinAbs z| ≤ rc`) of the first torus goes to the root site over `boxMap z`. -/
theorem rootSite_boxMap {rc : ℕ} (z : RootIdx d L N₁ m₁ K)
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (K - K)) z) (hr : L ^ K * rc ≤ r)
    (hs : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K) :
    rootSite (N₁ := N₁') (boxMap (N₁ * L ^ m₁ * L ^ (K - K)) (N₁' * L ^ m₁ * L ^ (K - K)) z) =
      bm (rootSite z) := by
  have hc0 : ∀ N : ℕ, [NeZero N] → NeZero (N * L ^ m₁ * L ^ (K - K)) := fun N _ =>
    ⟨by have := NeZero.pos N; have := NeZero.pos L; positivity⟩
  have := hc0 N₁
  have := hc0 N₁'
  have hn : ∀ N : ℕ, (N * L ^ m₁) * L ^ K = L ^ K * (N * L ^ m₁ * L ^ (K - K)) := fun N => by
    rw [Nat.sub_self, pow_zero, mul_one, mul_comm]
  funext μ
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = (z μ).valMinAbs := ⟨_, rfl⟩
  have hzμ : z μ = ((ζ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (K - K))) := by
    rw [hζ, ZMod.coe_valMinAbs]
  have hζr : |L ^ K * ζ| ≤ r := by
    have h1 : |ζ| ≤ rc := by rw [hζ]; exact hz μ
    have h2 : |((L ^ K : ℕ) : ℤ) * ζ| ≤ ((L ^ K * rc : ℕ) : ℤ) := by
      rw [abs_mul, Nat.abs_cast, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((L ^ K * rc : ℕ) : ℤ) ≤ r := by exact_mod_cast hr
    push_cast at h2 h3 ⊢
    exact h2.trans h3
  have e1 : rootSite z μ = ((((L ^ K : ℕ) : ℤ) * ζ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
    show ((L ^ K * (z μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = _
    rw [hzμ]
    exact rootCoord_intCast (hn N₁) ζ
  have e2 : rootSite (N₁ := N₁')
      (boxMap (N₁ * L ^ m₁ * L ^ (K - K)) (N₁' * L ^ m₁ * L ^ (K - K)) z) μ =
      ((((L ^ K : ℕ) : ℤ) * ζ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ K)) := by
    show ((L ^ K * ((((z μ).valMinAbs : ℤ) : ZMod (N₁' * L ^ m₁ * L ^ (K - K)))).val : ℕ) :
      ZMod ((N₁' * L ^ m₁) * L ^ K)) = _
    rw [← hζ]
    exact rootCoord_intCast (hn N₁') ζ
  rw [e2]
  show _ = (((rootSite z μ).valMinAbs : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ K))
  rw [e1]
  have : ((((L ^ K : ℕ) : ℤ) * ζ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)).valMinAbs =
      ((L ^ K : ℕ) : ℤ) * ζ := valMinAbs_intCast_of_abs_le hs (by exact_mod_cast hζr)
  rw [this]

/-- **The root cube of a coarse site.**  The root cube over `z` corresponds to the root cube over
`boxMap z` under `cubeMap`, if the cube lies in the box. -/
theorem cubeMap_rootCube (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {rc : ℕ}
    (z : RootIdx d L N₁ m₁ K) (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (K - K)) z)
    (hr : L ^ K * rc ≤ r) (hs : 2 * r + cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K)
    (hbox : ∀ y ∈ box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K), 𝓑 y) :
    cubeMap hN hN' (le_refl K) (rootCube (m₀ := m₀) z) =
      rootCube (m₀ := m₀) (N₁ := N₁')
        (boxMap (N₁ * L ^ m₁ * L ^ (K - K)) (N₁' * L ^ m₁ * L ^ (K - K)) z) := by
  have hs1 : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K := by
    have := cellSide_pos (L := L) m₀ m₁ K
    omega
  apply Subtype.ext
  show bm (cbase (cellSide L m₀ m₁ K) (rootSite z)) =
    cbase (cellSide L m₀ m₁ K) (rootSite (N₁ := N₁')
      (boxMap (N₁ * L ^ m₁ * L ^ (K - K)) (N₁' * L ^ m₁ * L ^ (K - K)) z))
  rw [rootSite_boxMap z hz hr hs1]
  exact cbase_boxMap (cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K))
    (cellSide_dvd (K := K) (m₁ := m₁) hN' (le_refl K)) (cellSide_pos m₀ m₁ K) hs _ hbox

theorem jBlock_cbase_eq {j : ℕ} (z : CTorus d L N₁ m₁ K) :
    jBlock d L (N₁ * L ^ m₁) K j (cbase (L ^ j) z) = jBlock d L (N₁ * L ^ m₁) K j z := by
  have : NeZero (N₁ * L ^ m₁ * L ^ (K - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  funext μ
  simp only [jBlock, blockMap_apply, blockCoord]
  have hlt : L ^ j * ((z μ).val / L ^ j) < N₁ * L ^ m₁ * L ^ K := by
    have := Nat.div_mul_le_self (z μ).val (L ^ j)
    have h2 := ZMod.val_lt (z μ)
    rw [mul_comm]; omega
  have : ((cbase (L ^ j) z) μ).val = L ^ j * ((z μ).val / L ^ j) := by
    simp only [cbase]; exact ZMod.val_natCast_of_lt hlt
  rw [this, Nat.mul_div_cancel_left _ hp]

/-- Membership in a `j`-block is membership in the aligned cell of side `L^j` over the cell base
of the site. -/
theorem jBlock_eq_iff_mem_box (hj : j ≤ K) (x y : CTorus d L N₁ m₁ K) :
    jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j y ↔
      x ∈ box (cbase (L ^ j) y) (L ^ j) := by
  have hdvd : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hj) _
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  constructor
  · intro h
    have hv : ∀ μ, (x μ).val / L ^ j = (y μ).val / L ^ j := fun μ => by
      have h1 := congrArg ZMod.val (congrFun h μ)
      have e : ∀ w : CTorus d L N₁ m₁ K, (jBlock d L (N₁ * L ^ m₁) K j w μ).val =
          (w μ).val / L ^ j := fun w => blockCoord_val (side_eq hj) _
      rwa [e, e] at h1
    have hc : cbase (L ^ j) x = cbase (L ^ j) y := by
      funext μ; simp only [cbase, hv μ]
    rw [← hc]
    exact mem_box_cbase hp x
  · intro h
    have hc := cbase_eq_of_mem_box hdvd (aligned_cbase y) h
    rw [← jBlock_cbase_eq (L := L) (j := j) x, hc, jBlock_cbase_eq]

/-- **The `j`-block of the fine torus** (`G.blk j y`, for any generating set): the block of `y`
goes to the block of `boxMap y`, if the block lies in the box. -/
theorem blk_image {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (G' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ) (hj : j ≤ K)
    (hs : 2 * r + L ^ j < (N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)
    (hbox : ∀ x ∈ box (cbase (L ^ j) y) (L ^ j), 𝓑 x) :
    bm '' (G.blk j y : Set (CTorus d L N₁ m₁ K)) = (G'.blk j (bm y) : Set (CTorus d L N₁' m₁ K)) := by
  have hdvd : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hj) _
  have hdvd' : L ^ j ∣ (N₁' * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hj) _
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have h1 : (G.blk j y : Set (CTorus d L N₁ m₁ K)) = box (cbase (L ^ j) y) (L ^ j) := by
    ext x; simp only [Finset.mem_coe, GeneratingSet.mem_blk]; exact jBlock_eq_iff_mem_box hj x y
  have h2 : (G'.blk j (bm y) : Set (CTorus d L N₁' m₁ K)) =
      box (cbase (L ^ j) (bm y)) (L ^ j) := by
    ext x; simp only [Finset.mem_coe, GeneratingSet.mem_blk]; exact jBlock_eq_iff_mem_box hj x _
  rw [h1, h2, image_box_boxMap hs hp hbox, cbase_boxMap hdvd hdvd' hp hs y hbox]

/-- **The sites of the block `B_{n+1}(z)`** (`blockSites`) over the coarse site `z` of a fine site
`y`: they correspond to the sites of the block over the coarse site `boxMap z`. -/
theorem blockSites_image {n rc : ℕ} (hn : n + 1 ≤ K)
    (hrc : r < L ^ (n + 1) * rc) (hc : 2 * rc + 1 < N₁ * L ^ m₁ * L ^ (K - (n + 1)))
    (hs : 2 * r + L ^ (n + 1) < (N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)
    (hbox : ∀ x ∈ box (cbase (L ^ (n + 1)) y) (L ^ (n + 1)), 𝓑 x) :
    bm '' (blockSites d L N₁ m₁ K n (jBlock d L (N₁ * L ^ m₁) K (n + 1) y) :
        Set (CTorus d L N₁ m₁ K)) =
      (blockSites d L N₁' m₁ K n (boxMap (N₁ * L ^ m₁ * L ^ (K - (n + 1)))
        (N₁' * L ^ m₁ * L ^ (K - (n + 1))) (jBlock d L (N₁ * L ^ m₁) K (n + 1) y)) :
        Set (CTorus d L N₁' m₁ K)) := by
  have hdvd : L ^ (n + 1) ∣ (N₁ * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hn) _
  have hdvd' : L ^ (n + 1) ∣ (N₁' * L ^ m₁) * L ^ K := Dvd.dvd.mul_left (pow_dvd_pow L hn) _
  have hp : 0 < L ^ (n + 1) := pow_pos (NeZero.pos L) _
  have hy : 𝓑 y := hbox y ((jBlock_eq_iff_mem_box hn y y).1 rfl)
  rw [← jBlock_boxMap (N₀ := N₁ * L ^ m₁) (N₀' := N₁' * L ^ m₁) hn hrc hc y hy]
  have h1 : (blockSites d L N₁ m₁ K n (jBlock d L (N₁ * L ^ m₁) K (n + 1) y) :
      Set (CTorus d L N₁ m₁ K)) = box (cbase (L ^ (n + 1)) y) (L ^ (n + 1)) := by
    ext x; simp only [Finset.mem_coe, blockSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact jBlock_eq_iff_mem_box hn x y
  have h2 : (blockSites d L N₁' m₁ K n (jBlock d L (N₁' * L ^ m₁) K (n + 1) (bm y)) :
      Set (CTorus d L N₁' m₁ K)) = box (cbase (L ^ (n + 1)) (bm y)) (L ^ (n + 1)) := by
    ext x; simp only [Finset.mem_coe, blockSites, Finset.mem_filter, Finset.mem_univ, true_and]
    exact jBlock_eq_iff_mem_box hn x _
  rw [h1, h2, image_box_boxMap hs hp hbox, cbase_boxMap hdvd hdvd' hp hs y hbox]

/-! ### The local cover of a site -/

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The neighbourhood `cellNbhd` of a cell inside the box goes to the neighbourhood of the image
cell. -/
theorem image_cellNbhd {n' : ℕ} {n : ℕ} (hL : 1 ≤ L) {c : ℕ} (hc : 0 < c) (B : Torus d n)
    (hn : 2 * r + ((L - 1) * c + L * c) < n) (hbox : ∀ x ∈ cellNbhd L c B, InBox d r n x) :
    boxMap n n' '' cellNbhd L c B = cellNbhd L c (boxMap n n' B) := by
  have hLc : 0 < L * c := Nat.mul_pos hL hc
  have hw : ∀ μ : Fin d, (fun _ : Fin d => (L - 1) * c) μ < (L - 1) * c + L * c :=
    fun _ => by show (L - 1) * c < (L - 1) * c + L * c; omega
  have hbox' : ∀ x ∈ box (B - natT fun _ : Fin d => (L - 1) * c) ((L - 1) * c + L * c),
      InBox d r n x := hbox
  have himg := image_box_boxMap (n' := n') hn (by omega) hbox'
  have hB : B = (B - natT fun _ : Fin d => (L - 1) * c) + natT fun _ : Fin d => (L - 1) * c := by
    abel
  have hb0 : InBox d r n (B - natT fun _ : Fin d => (L - 1) * c) :=
    hbox' _ (mem_box_self _ (by omega))
  have hBmem : B ∈ box (B - natT fun _ : Fin d => (L - 1) * c) ((L - 1) * c + L * c) := by
    have := mem_box_add (B - natT fun _ : Fin d => (L - 1) * c) hw
    rwa [← hB] at this
  have hadd := boxMap_add_natT (n' := n') hn hw hb0 (by
    rw [← hB]
    exact hbox' B hBmem)
  rw [← hB] at hadd
  have hsub : boxMap n n' (B - natT fun _ : Fin d => (L - 1) * c) =
      boxMap n n' B - natT fun _ : Fin d => (L - 1) * c := by
    rw [hadd]; abel
  show boxMap n n' '' box (B - natT fun _ : Fin d => (L - 1) * c) ((L - 1) * c + L * c) =
    box (boxMap n n' B - natT fun _ : Fin d => (L - 1) * c) ((L - 1) * c + L * c)
  rw [himg, hsub]

theorem corner_boxMap (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hs : 2 * r + cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ box (LocalCover.corner m₀ x) (cellSide L m₀ m₁ K), 𝓑 y) :
    bm (LocalCover.corner m₀ x) = LocalCover.corner m₀ (bm x) :=
  cbase_boxMap (cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K))
    (cellSide_dvd (K := K) (m₁ := m₁) hN' (le_refl K)) (cellSide_pos m₀ m₁ K) hs x hbox

/-- **The localization cube `X` of a site** goes to the localization cube of the image site. -/
theorem cube_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hs : 2 * r + L * cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K)
    (hsj : 2 * r + L * cellSide L m₀ m₁ j < (N₁ * L ^ m₁) * L ^ K)
    (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ LocalCover.cube m₀ j x, 𝓑 y)
    (hcell : ∀ y ∈ box (LocalCover.corner m₀ x) (cellSide L m₀ m₁ K), 𝓑 y) :
    bm '' LocalCover.cube m₀ j x = LocalCover.cube m₀ j (bm x) := by
  unfold LocalCover.cube
  rw [image_box_boxMap hsj (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L))
    (cellSide_pos m₀ m₁ j)) hbox, corner_boxMap hN hN' (two_r_cell_lt hs) x hcell]

/-- The chosen family of the local cover is carried by `boxMap`. -/
theorem fam_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hs : 2 * r + L * cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K)
    (hcell : ∀ y ∈ box (LocalCover.corner m₀ x) (cellSide L m₀ m₁ K), 𝓑 y) :
    bm '' LocalCover.fam m₀ x = LocalCover.fam m₀ (bm x) := by
  unfold LocalCover.fam
  rw [Set.image_singleton, corner_boxMap hN hN' (two_r_cell_lt hs) x hcell]

/-- The region `X₁` of the local cover (`nbhd`, `nbhdF`) is carried by `boxMap`, if it lies in
the box.  (For tori of `≤ 2L - 1` cells per direction the region is the whole torus; the
hypothesis `hbox` forces it to be a proper box.) -/
theorem nbhd_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hs : 2 * r + L * cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K)
    (hnb : 2 * r + ((L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K) <
      (N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ LocalCover.nbhd m₀ x, 𝓑 y)
    (hcell : ∀ y ∈ box (LocalCover.corner m₀ x) (cellSide L m₀ m₁ K), 𝓑 y) :
    bm '' LocalCover.nbhd m₀ x = LocalCover.nbhd m₀ (bm x) := by
  unfold LocalCover.nbhd
  rw [image_cellNbhd (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ K) _ hnb hbox,
    corner_boxMap hN hN' (two_r_cell_lt hs) x hcell]

theorem nbhdF_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hs : 2 * r + L * cellSide L m₀ m₁ K < (N₁ * L ^ m₁) * L ^ K)
    (hnb : 2 * r + ((L - 1) * cellSide L m₀ m₁ K + L * cellSide L m₀ m₁ K) <
      (N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K)
    (hbox : ∀ y ∈ LocalCover.nbhd m₀ x, 𝓑 y)
    (hcell : ∀ y ∈ box (LocalCover.corner m₀ x) (cellSide L m₀ m₁ K), 𝓑 y) :
    bm '' (LocalCover.nbhdF m₀ x : Set (CTorus d L N₁ m₁ K)) =
      (LocalCover.nbhdF m₀ (bm x) : Set (CTorus d L N₁' m₁ K)) := by
  rw [LocalCover.coe_nbhdF, LocalCover.coe_nbhdF]
  exact nbhd_image hN hN' hs hnb x hbox hcell

/-- The corner site of the block `B_{n+1}(z)` (`LocalCover.blockSite`) is carried by `boxMap`. -/
theorem blockSite_boxMap {n rc : ℕ} (hn1 : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (K - (n + 1))) z) (hr : L ^ (n + 1) * rc ≤ r)
    (hs : 2 * r + 1 < (N₁ * L ^ m₁) * L ^ K) :
    LocalCover.blockSite (N₁ := N₁') n
      (boxMap (N₁ * L ^ m₁ * L ^ (K - (n + 1))) (N₁' * L ^ m₁ * L ^ (K - (n + 1))) z) =
      bm (LocalCover.blockSite n z) := by
  have hc0 : ∀ N : ℕ, [NeZero N] → NeZero (N * L ^ m₁ * L ^ (K - (n + 1))) := fun N _ =>
    ⟨by have := NeZero.pos N; have := NeZero.pos L; positivity⟩
  have := hc0 N₁
  have := hc0 N₁'
  have hn : ∀ N : ℕ, (N * L ^ m₁) * L ^ K = L ^ (n + 1) * (N * L ^ m₁ * L ^ (K - (n + 1))) :=
    fun N => side_eq (N₀ := N * L ^ m₁) (L := L) hn1
  funext μ
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = (z μ).valMinAbs := ⟨_, rfl⟩
  have hzμ : z μ = ((ζ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) := by
    rw [hζ, ZMod.coe_valMinAbs]
  have hζr : |((L ^ (n + 1) : ℕ) : ℤ) * ζ| ≤ r := by
    have h1 : |ζ| ≤ rc := by rw [hζ]; exact hz μ
    have h2 : |((L ^ (n + 1) : ℕ) : ℤ) * ζ| ≤ ((L ^ (n + 1) * rc : ℕ) : ℤ) := by
      rw [abs_mul, Nat.abs_cast, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ((L ^ (n + 1) * rc : ℕ) : ℤ) ≤ r := by exact_mod_cast hr
    exact h2.trans h3
  have e1 : LocalCover.blockSite n z μ =
      ((((L ^ (n + 1) : ℕ) : ℤ) * ζ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
    show ((L ^ (n + 1) * (z μ).val : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = _
    rw [hzμ]
    exact rootCoord_intCast (hn N₁) ζ
  have e2 : LocalCover.blockSite (N₁ := N₁') n
      (boxMap (N₁ * L ^ m₁ * L ^ (K - (n + 1))) (N₁' * L ^ m₁ * L ^ (K - (n + 1))) z) μ =
      ((((L ^ (n + 1) : ℕ) : ℤ) * ζ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ K)) := by
    show ((L ^ (n + 1) * ((((z μ).valMinAbs : ℤ) :
      ZMod (N₁' * L ^ m₁ * L ^ (K - (n + 1))))).val : ℕ) :
      ZMod ((N₁' * L ^ m₁) * L ^ K)) = _
    rw [← hζ]
    exact rootCoord_intCast (hn N₁') ζ
  rw [e2]
  show _ = (((LocalCover.blockSite n z μ).valMinAbs : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ K))
  rw [e1]
  have : ((((L ^ (n + 1) : ℕ) : ℤ) * ζ : ℤ) :
      ZMod ((N₁ * L ^ m₁) * L ^ K)).valMinAbs = ((L ^ (n + 1) : ℕ) : ℤ) * ζ :=
    valMinAbs_intCast_of_abs_le hs hζr
  rw [this]

end Step

end Balaban.Polymer.TwoTorusStep
