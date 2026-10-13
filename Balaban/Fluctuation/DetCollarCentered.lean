/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.DetCollarHullSymm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The centred collar hull of a set of cubes, for odd block size

For a cube `b` of side `a` the landed collar box (`DetCollarHull.lean`) is the box of side `L a`
based at `b - a (1, …, 1)`.  It has the cube in its centre, and is invariant under the lattice
reflections, only for `L = 3`.  For odd `L = 2 q + 1` the centred collar box is the box of side
`L a` based at `b - q a (1, …, 1)`: the cube sits in the middle, with `q` cells on each side.

* `collarBaseC q a c = c - q a (1, …, 1)`, `detCollarHullC q T`: the sites of `T` together with
  the centred collar boxes of the cubes of `T`.
* `collarBaseC_one`, `detCollarHullC_one`, `detCollarHullC_three`: with `q = 1` (so `L = 3`) these
  are the landed `collarBase`, `detCollarHull`.
* `box_subset_collarBoxC`, `box_adj_subset_collarC`: the cube, and for `q ≥ 1` every cell at
  index distance one, lie in the centred collar box when `L ≥ q + 2`.
* `detCollarHullC_isDj`, `detCollarHullC_sizeJ_le`: polymer property and size bound, with the
  same constants `cG d L`, `collarB d L` as the landed hull.
* `collar_image_reflectC`: for `L = 2 q + 1`, a reflection maps the centred collar box of a
  cube onto the centred collar box of the reflected cube; `collar_image_genSymmC`,
  `detCollarHullC_cubeAct_genSymm`: the same for the whole generated group and the hull.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Background Balaban.Localization.DecEquiv

section Hull

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The base of the centred collar box of the cell based at `c`: `c - q a (1, …, 1)`. -/
def collarBaseC (q a : ℕ) (c : CTorus d L N₁ m₁ K) : CTorus d L N₁ m₁ K :=
  c - natT (fun _ => q * a)

/-- The bases of the centred collar boxes of a set of cubes. -/
noncomputable def collarBasesC (q : ℕ) (T : Finset 𝔅) : Finset (CTorus d L N₁ m₁ K) :=
  open Classical in T.image fun b => collarBaseC q (cellSide L m₀ m₁ K) b.1

/-- **The centred collar hull** of a set `T` of cubes: the sites of `T` and, for each cube of
`T`, the aligned box of side `L a` based at its base minus `q a (1, …, 1)`. -/
noncomputable def detCollarHullC (q : ℕ) (T : Finset 𝔅) : Set (CTorus d L N₁ m₁ K) :=
  sitesOf T ∪ ⋃ p ∈ collarBasesC q T, box p (L * cellSide L m₀ m₁ K)

omit [NeZero N₁] [NeZero L] in
theorem collarBaseC_apply (q a : ℕ) (c : CTorus d L N₁ m₁ K) (μ : Fin d) :
    collarBaseC q a c μ = c μ - ((q * a : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := rfl

/-- With `q = 1` the centred base is the landed collar base. -/
theorem collarBaseC_one {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (c : CTorus d L N₁ m₁ K) :
    collarBaseC 1 a c = collarBase a c := by
  funext μ
  rw [collarBaseC_apply, collarBase_apply ha, one_mul]

theorem collarBasesC_one (hN : L ^ m₀ ∣ N₁) (T : Finset 𝔅) :
    collarBasesC 1 T = collarBases T := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  unfold collarBasesC collarBases
  exact Finset.image_congr fun b _ => collarBaseC_one hdvd b.1

/-- **Consistency with the landed hull**: at `q = 1` (`L = 3`) the centred hull is the landed
collar hull. -/
theorem detCollarHullC_one (hN : L ^ m₀ ∣ N₁) (T : Finset 𝔅) :
    detCollarHullC 1 T = detCollarHull T := by
  unfold detCollarHullC detCollarHull
  rw [collarBasesC_one hN]

/-- At `L = 3` the centred hull is the landed collar hull. -/
theorem detCollarHullC_three (hL : L = 3) (hN : L ^ m₀ ∣ N₁) (T : Finset 𝔅) :
    detCollarHullC ((L - 1) / 2) T = detCollarHull T := by
  have : (L - 1) / 2 = 1 := by omega
  rw [this]; exact detCollarHullC_one hN T

omit [NeZero N₁] [NeZero L] in
theorem sitesOf_subset_detCollarHullC (q : ℕ) (T : Finset 𝔅) : sitesOf T ⊆ detCollarHullC q T :=
  Set.subset_union_left

omit [NeZero N₁] [NeZero L] in
/-- The cube of side `a` lies in its centred collar box when `L ≥ q + 1`. -/
theorem box_subset_collarBoxC {q a : ℕ} (hq : q + 1 ≤ L) (c : CTorus d L N₁ m₁ K) :
    box c a ⊆ box (collarBaseC q a c) (L * a) := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨(fun _ => q * a) + w, fun μ => ?_, ?_⟩
  · have h4 : (q + 1) * a ≤ L * a := Nat.mul_le_mul_right a hq
    have := hw μ
    simp only [Pi.add_apply]
    nlinarith
  · rw [natT_add]; unfold collarBaseC; abel

omit [NeZero N₁] [NeZero L] in
theorem mem_collarBasesC_of_mem {q : ℕ} {T : Finset 𝔅} {b : 𝔅} (hb : b ∈ T) :
    collarBaseC q (cellSide L m₀ m₁ K) b.1 ∈ collarBasesC q T := by
  classical
  exact Finset.mem_image.2 ⟨b, hb, rfl⟩

omit [NeZero N₁] [NeZero L] in
/-- A cube of `T` lies in the centred hull of `T`. -/
theorem box_subset_detCollarHullC {q : ℕ} {T : Finset 𝔅} {b : 𝔅} (hb : b ∈ T) :
    box b.1 (cellSide L m₀ m₁ K) ⊆ detCollarHullC q T :=
  fun _ hz => Or.inl (mem_sitesOf.2 ⟨b, hb, hz⟩)

omit [NeZero N₁] [NeZero L] in
/-- The box of side `L a` at the centred base of a cube of `T` lies in the centred hull. -/
theorem box_collarC_subset_detCollarHullC {q : ℕ} {T : Finset 𝔅} {b : 𝔅} (hb : b ∈ T) :
    box (collarBaseC q (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) ⊆
      detCollarHullC q T :=
  fun _ hz => Or.inr (Set.mem_iUnion₂.2 ⟨_, mem_collarBasesC_of_mem hb, hz⟩)

omit [NeZero N₁] [NeZero L] in
/-- The centred collar box contains the cells at index distance one (`q ≥ 1`, `L ≥ q + 2`). -/
theorem box_adj_subset_collarC {q : ℕ} (hq : 1 ≤ q) (hL : q + 2 ≤ L) {a : ℕ}
    (c : CTorus d L N₁ m₁ K) (q' : Fin d → ℤ) (hq' : ∀ μ, |q' μ| ≤ 1) :
    box (c + fun μ => (((a : ℤ) * q' μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ K))) a ⊆
      box (collarBaseC q a c) (L * a) := by
  rintro x ⟨w, hw, rfl⟩
  have ht : ∀ μ, (((q : ℤ) + q' μ).toNat : ℤ) = (q : ℤ) + q' μ := fun μ =>
    Int.toNat_of_nonneg (by have := abs_le.1 (hq' μ); omega)
  refine ⟨(fun μ => a * ((q : ℤ) + q' μ).toNat) + w, fun μ => ?_, ?_⟩
  · have h1 := abs_le.1 (hq' μ)
    have h2 : ((q : ℤ) + q' μ).toNat ≤ q + 1 := by omega
    have h3 : a * ((q : ℤ) + q' μ).toNat ≤ a * (q + 1) := Nat.mul_le_mul_left a h2
    have h4 : (q + 2) * a ≤ L * a := Nat.mul_le_mul_right a hL
    have := hw μ
    simp only [Pi.add_apply]
    nlinarith
  · funext μ
    have e2 : (((a * ((q : ℤ) + q' μ).toNat : ℕ) : ℤ)) = a * ((q : ℤ) + q' μ) := by
      push_cast; rw [ht]
    have e3 := congrArg (Int.cast : ℤ → ZMod (N₁ * L ^ m₁ * L ^ K)) e2
    push_cast at e3
    simp only [collarBaseC, Pi.add_apply, Pi.sub_apply, natT_apply]
    push_cast
    linear_combination (-1 : ZMod (N₁ * L ^ m₁ * L ^ K)) * e3

/-- Every site whose cell is equal or `*`-adjacent to the cell of a site of `T` lies in the
centred hull (`q ≥ 1`, `L ≥ q + 2`). -/
theorem cellNear_mem_detCollarHullC {q : ℕ} (hq : 1 ≤ q) (hL : q + 2 ≤ L)
    (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅}
    {x v : CTorus d L N₁ m₁ K} (hx : x ∈ sitesOf T) (hxv : CellNear m₀ K x v) :
    v ∈ detCollarHullC q T := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
  have e := cbase_eq_of_mem_box hdvd b.2.1 hxb
  obtain ⟨q', hq', hqv⟩ := hxv
  refine box_collarC_subset_detCollarHullC hb ?_
  refine box_adj_subset_collarC hq hL b.1 q' hq' ?_
  have hm := mem_box_cbase ha0 v
  rw [hqv, e] at hm
  exact hm

theorem aligned_collarBaseC {q a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K)
    {c : CTorus d L N₁ m₁ K} (hc : Aligned a c) : Aligned a (collarBaseC q a c) := fun μ => by
  have h1 := (aligned_coord_iff ha _).1 (hc μ)
  refine (aligned_coord_iff ha _).2 ?_
  simp only [collarBaseC_apply, map_sub, h1, map_natCast]
  simp

/-- **Polymer property of the centred hull** (any `q`, `L ≥ q + 1`). -/
theorem detCollarHullC_isDj {q : ℕ} (hq : q + 1 ≤ L) (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅}
    (hT : IsPolyDom m₀ K (sitesOf T)) :
    IsDj m₀ K (detCollarHullC q T) ∧
      treeLenCovOne m₀ K (detCollarHullC q T) ≤
        treeLenCovOne m₀ K (sitesOf T) + (collarBasesC q T).card * cG d L := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  refine thick_union (m₀ := m₀) (j := K) (isDj_of_isPolyDom hT) (collarBasesC q T) ?_
  intro p hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
  exact ⟨aligned_collarBaseC hdvd b.2.1, b.1, b.2.1, fun x hx =>
    ⟨mem_sitesOf.2 ⟨b, hb, hx⟩, box_subset_collarBoxC hq b.1 hx⟩⟩

/-- **Size of the centred hull**: same bounds, same constants as the landed hull. -/
theorem detCollarHullC_sizeJ_le {q : ℕ} (hq : q + 1 ≤ L) (hN : L ^ m₀ ∣ N₁) {T : Finset 𝔅}
    (hT : IsPolyDom m₀ K (sitesOf T)) :
    sizeJ m₀ K (detCollarHullC q T) ≤ dExt T + (T.card : ℝ) * cG d L ∧
      sizeJ m₀ K (detCollarHullC q T) ≤ (1 + collarB d L) * dExt T + collarB d L := by
  classical
  have hg : 0 ≤ cG d L := by unfold cG; positivity
  have h1 := (detCollarHullC_isDj hq hN hT).2
  have h2 : ((collarBasesC q T).card : ℝ) ≤ T.card := by
    exact_mod_cast (Finset.card_image_le : (collarBasesC q T).card ≤ T.card)
  have hd := dExt_eq_sizeJ_of_isPolyDom hT
  have h3 : sizeJ m₀ K (detCollarHullC q T) ≤ dExt T + (T.card : ℝ) * cG d L := by
    have h1' : sizeJ m₀ K (detCollarHullC q T) ≤ sizeJ m₀ K (sitesOf T) +
        ((collarBasesC q T).card : ℝ) * cG d L := h1
    rw [hd]
    nlinarith [mul_le_mul_of_nonneg_right h2 hg]
  refine ⟨h3, ?_⟩
  have h4 := card_le_dExt (m₀ := m₀) (j := K) hN (le_refl K) T
  have h5 : (T.card : ℝ) * cG d L ≤ collarB d L * (1 + dExt T) := by
    unfold collarB
    nlinarith [mul_le_mul_of_nonneg_right h4 hg]
  nlinarith

/-- The finset of sets of cubes with centred hull `X`. -/
noncomputable def detCollarFibreC (q : ℕ) (X : Set (CTorus d L N₁ m₁ K)) : Finset (Finset 𝔅) :=
  open Classical in Finset.univ.filter fun T => detCollarHullC q T = X

theorem mem_detCollarFibreC {q : ℕ} {X : Set (CTorus d L N₁ m₁ K)} {T : Finset 𝔅} :
    T ∈ detCollarFibreC q X ↔ detCollarHullC q T = X := by
  classical
  simp [detCollarFibreC]

end Hull

/-! ### Reflection and the generated group -/

section Symm

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- A translation maps the centred collar box of a cube onto that of the image cube. -/
theorem collar_image_translateC (q : ℕ) (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (b : 𝔅) :
    (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) ''
        box (collarBaseC q (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBaseC q (cellSide L m₀ m₁ K)
        (cubeMap (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1)
        (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have hg := genSymm_mem_pavingSymGroup (GenSymm.translate (n := K) (m₀ := m₀) t ht)
  have hcm : (cubeMap (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1 = b.1 + t :=
    cubeMap_val_eq hN hg b (aligned_add_of_dvd hdvd b.2.1 ht) (image_box_addRight t _ _)
  rw [hcm, image_box_addRight]
  congr 1
  funext μ
  simp only [collarBaseC_apply, Pi.add_apply]
  ring

/-- A coordinate permutation maps the centred collar box of a cube onto that of the image
cube. -/
theorem collar_image_coordPermC (q : ℕ) (hN : L ^ m₀ ∣ N₁) (π : Equiv.Perm (Fin d)) (b : 𝔅) :
    (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) ''
        box (collarBaseC q (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBaseC q (cellSide L m₀ m₁ K)
        (cubeMap (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1)
        (L * cellSide L m₀ m₁ K) := by
  have hg := genSymm_mem_pavingSymGroup (GenSymm.perm (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (n := K) (m₀ := m₀) π)
  have hcm : (cubeMap (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1 =
      coordPerm π b.1 :=
    cubeMap_val_eq hN hg b (fun μ => b.2.1 (π.symm μ)) (image_box_coordPerm π _ _)
  rw [hcm, image_box_coordPerm]
  congr 1

/-- **A reflection maps the centred collar box of a cube onto the centred collar box of the
reflected cube, for every odd `L = 2 q + 1`.** -/
theorem collar_image_reflectC {q : ℕ} (hL : L = 2 * q + 1) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (K + m₀ + m₁) ∣ c.val) (b : 𝔅) :
    (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) ''
        box (collarBaseC q (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBaseC q (cellSide L m₀ m₁ K)
        (cubeMap (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1)
        (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have hg := genSymm_mem_pavingSymGroup (GenSymm.reflect (n := K) (m₀ := m₀) μ₀ c hc)
  have hcm : (cubeMap (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1 =
      Function.update b.1 μ₀ (c - b.1 μ₀ - (cellSide L m₀ m₁ K : ZMod ((N₁ * L ^ m₁) * L ^ K))) :=
    cubeMap_val_eq hN hg b (aligned_refl_update hdvd b.2.1 μ₀ hc)
      (image_box_reflPerm μ₀ c b.1 ha0)
  have hLc : ((L : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = 2 * (q : ZMod _) + 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod ((N₁ * L ^ m₁) * L ^ K)) hL
    push_cast at this
    exact this
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  rw [hcm, image_box_reflPerm μ₀ c _ (Nat.mul_pos hLpos ha0)]
  congr 1
  funext i
  by_cases h : i = μ₀
  · subst h
    simp only [Function.update_self, collarBaseC_apply]
    push_cast
    linear_combination (-(cellSide L m₀ m₁ K : ZMod ((N₁ * L ^ m₁) * L ^ K))) * hLc
  · simp [Function.update_of_ne h, collarBaseC_apply]

/-- **Centred collar boxes under the generated group (odd `L`).** -/
theorem collar_image_genSymmC {q : ℕ} (hL : L = 2 * q + 1) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ) (b : 𝔅) :
    σ '' box (collarBaseC q (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBaseC q (cellSide L m₀ m₁ K) (cubeMap σ b).1) (L * cellSide L m₀ m₁ K) := by
  induction h generalizing b with
  | one => rw [cubeMap_one hN]; simp
  | translate t ht => exact collar_image_translateC q hN t ht b
  | perm π => exact collar_image_coordPermC q hN π b
  | reflect μ₀ c hc => exact collar_image_reflectC hL hN μ₀ c hc b
  | trans h1 h2 ih ih' =>
    rename_i σ σ'
    rw [← cubeMap_trans hN h1 h2]
    show (σ' ∘ σ) '' _ = _
    rw [Set.image_comp, ih b, ih' (cubeMap σ b)]

/-- If a paving symmetry maps the centred collar box of each cube onto that of the image cube,
it maps the centred hull of `T` onto the centred hull of `g • T`. -/
theorem detCollarHullC_cubeAct_of_collar {q : ℕ} (hN : L ^ m₀ ∣ N₁)
    {g : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hg : g ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (hcol : ∀ b : 𝔅, g '' box (collarBaseC q (cellSide L m₀ m₁ K) b.1)
        (L * cellSide L m₀ m₁ K) =
      box (collarBaseC q (cellSide L m₀ m₁ K) (cubeMap g b).1) (L * cellSide L m₀ m₁ K))
    (T : Finset 𝔅) : detCollarHullC q (cubeAct g T) = g '' detCollarHullC q T := by
  classical
  unfold detCollarHullC
  rw [Set.image_union, sitesOf_cubeAct hN hg, Set.image_iUnion₂]
  congr 1
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := mem_cubeAct.1 hc
    exact ⟨_, mem_collarBasesC_of_mem hb, by rw [hcol b]; exact hx⟩
  · rintro ⟨p, hp, hx⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
    rw [hcol b] at hx
    exact ⟨_, mem_collarBasesC_of_mem (mem_cubeAct.2 ⟨b, hb, rfl⟩), hx⟩

/-- **The centred collar hull commutes with every symmetry of the generated group when
`L = 2 q + 1`.** -/
theorem detCollarHullC_cubeAct_genSymm {q : ℕ} (hL : L = 2 * q + 1) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ) (T : Finset 𝔅) :
    detCollarHullC q (cubeAct σ T) = σ '' detCollarHullC q T :=
  detCollarHullC_cubeAct_of_collar hN (genSymm_mem_pavingSymGroup h)
    (collar_image_genSymmC hL hN h) T

end Symm

end Balaban.Fluctuation
