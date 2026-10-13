/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.DetSymmGroup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Symmetry of the collar hull and of the regrouped determinant terms

For a set `T` of cubes of the cover, `detCollarHull T` is the union of `sitesOf T` and of the
aligned boxes of side `L a` based at `b - a (1, …, 1)`, `b` a cube of `T`, `a` the cell side.
Here the hull is shown to commute with the lattice symmetries of `GenSymm`.

* `detCollarHull_cubeAct_translate`, `detCollarHull_cubeAct_coordPerm`: for translations by
  multiples of the cell side and for coordinate permutations, `H(σ • T) = σ '' H(T)`, for every `L`.
* `detCollarHull_cubeAct_reflect`: the same for an admissible reflection `x_μ ↦ c - 1 - x_μ`, but
  only for `L = 3` (hypothesis `hL : L = 3`).  The reflection of the box `[b - a, b - a + L a)` in
  the coordinate `μ` is the box based at `c - b + a - L a`, whereas the collar box of the reflected
  cube (base `c - b - a`) is based at `c - b - 2a`; these agree exactly when `L = 3`, when the box
  is the cube with one cell on each side.
* `detCollarHull_cubeAct_genSymm`: for `L = 3` and every `σ` of the generated group (induction on
  the generators, using `collar_image_genSymm`, the statement for the collar box of one cube).
* `cubeAct_mem_detCollarFibre_iff`, `image_cubeAct_detCollarFibre`: `σ •` maps the fibre of `X`
  bijectively onto the fibre of `σ '' X`; `detCollarGrouped_comp`: if `e' (σ • T) = e T` for all `T`
  then `detCollarGrouped e' (σ '' X) = detCollarGrouped e X`.
* `exists_detExpansionLocC_grouped_sym`: with the hypotheses of `exists_detExpansionLocC_sym` and
  `L = 3`, the regrouped terms satisfy `E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X`.

## What is not proved

All statements concern the chart data `D`, the zero class and the terms of the record; nothing
depends on the generator.  The inclusion of the class domain in the chart, the rate requirement
`λ_hull ≥ κ_out` and covariance under the spin rotations are not proved here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Background Balaban.Localization.DecEquiv

section Boxes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

omit [NeZero N₁] [NeZero L] in
/-- A translation maps the box `[p, p + s)` to the box `[p + t, p + t + s)`. -/
theorem image_box_addRight (t p : CTorus d L N₁ m₁ K) (s : ℕ) :
    (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) '' box p s = box (p + t) s := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by simp only [Equiv.coe_addRight]; abel⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨p + natT w, ⟨w, hw, rfl⟩, by simp only [Equiv.coe_addRight]; abel⟩

omit [NeZero N₁] [NeZero L] in
/-- A coordinate permutation maps the box `[p, p + s)` to the box based at the permuted base. -/
theorem image_box_coordPerm (π : Equiv.Perm (Fin d)) (p : CTorus d L N₁ m₁ K) (s : ℕ) :
    (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) '' box p s = box (coordPerm π p) s := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨w ∘ π.symm, fun μ => hw _, ?_⟩
    funext i
    simp [coordPerm, natT]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨p + natT (w ∘ π), ⟨w ∘ π, fun μ => hw _, rfl⟩, ?_⟩
    funext i
    simp [coordPerm, natT]

omit [NeZero N₁] [NeZero L] in
theorem image_box_reflPerm_subset (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (p : CTorus d L N₁ m₁ K) {s : ℕ} (hs : 0 < s) :
    (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) '' box p s ⊆
      box (Function.update p μ₀ (c - p μ₀ - (s : ZMod ((N₁ * L ^ m₁) * L ^ K)))) s := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  refine ⟨fun i => if i = μ₀ then s - 1 - w i else w i, fun i => ?_, ?_⟩
  · by_cases h : i = μ₀
    · simp only [h, ite_true]; have := hw μ₀; omega
    · simp only [h, ite_false]; exact hw i
  · funext i
    by_cases h : i = μ₀
    · subst h
      have h1 : w i ≤ s - 1 := by have := hw i; omega
      simp only [reflPerm, Equiv.coe_fn_mk, Function.update_self, Pi.add_apply, natT_apply,
        ite_true]
      rw [Nat.cast_sub h1, Nat.cast_sub (by omega : 1 ≤ s)]
      push_cast
      ring
    · simp [reflPerm, natT, h]

omit [NeZero N₁] [NeZero L] in
/-- The reflection `x_μ₀ ↦ c - 1 - x_μ₀` maps the box `[p, p + s)` to the box based at
`c - p_μ₀ - s` in the coordinate `μ₀`. -/
theorem image_box_reflPerm (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (p : CTorus d L N₁ m₁ K) {s : ℕ} (hs : 0 < s) :
    (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) '' box p s =
      box (Function.update p μ₀ (c - p μ₀ - (s : ZMod ((N₁ * L ^ m₁) * L ^ K)))) s := by
  refine Set.Subset.antisymm (image_box_reflPerm_subset μ₀ c p hs) fun x hx => ?_
  set p' := Function.update p μ₀ (c - p μ₀ - (s : ZMod ((N₁ * L ^ m₁) * L ^ K))) with hp'
  have h1 := image_box_reflPerm_subset μ₀ c p' hs ⟨x, hx, rfl⟩
  have hpp : Function.update p' μ₀ (c - p' μ₀ - (s : ZMod ((N₁ * L ^ m₁) * L ^ K))) = p := by
    funext i
    by_cases h : i = μ₀
    · subst h; simp only [hp', Function.update_self]; ring
    · simp [hp', h]
  rw [hpp] at h1
  refine ⟨_, h1, ?_⟩
  funext i
  by_cases h : i = μ₀
  · subst h; simp [reflPerm]
  · simp [reflPerm, h]

end Boxes

section Cubes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The coordinates of the base of the collar box of the cell based at `c` are `c - a`. -/
theorem collarBase_apply {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (c : CTorus d L N₁ m₁ K)
    (μ : Fin d) : collarBase a c μ = c μ - (a : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
  have hle : a ≤ (N₁ * L ^ m₁) * L ^ K := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) ha
  simp only [collarBase, pBase, Pi.add_apply, natT_apply, ite_true]
  rw [Nat.cast_sub hle, ZMod.natCast_self]
  ring

theorem aligned_coord_iff {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K)
    (x : ZMod ((N₁ * L ^ m₁) * L ^ K)) :
    x.val % a = 0 ↔ ZMod.castHom ha (ZMod a) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

theorem aligned_add_of_dvd {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) {b t : CTorus d L N₁ m₁ K}
    (hb : Aligned a b) (ht : ∀ μ, a ∣ (t μ).val) : Aligned a (b + t) := fun μ => by
  have h1 := (aligned_coord_iff ha _).1 (hb μ)
  have h2 := (aligned_coord_iff ha _).1 (Nat.mod_eq_zero_of_dvd (ht μ))
  exact (aligned_coord_iff ha _).2 (by simp only [Pi.add_apply, map_add, h1, h2, add_zero])

theorem aligned_refl_update {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) {b : CTorus d L N₁ m₁ K}
    (hb : Aligned a b) (μ₀ : Fin d) {c : ZMod ((N₁ * L ^ m₁) * L ^ K)} (hc : a ∣ c.val) :
    Aligned a (Function.update b μ₀ (c - b μ₀ - (a : ZMod ((N₁ * L ^ m₁) * L ^ K)))) :=
  fun i => by
  by_cases h : i = μ₀
  · subst h
    have h1 := (aligned_coord_iff ha _).1 (hb i)
    have h2 := (aligned_coord_iff ha _).1 (Nat.mod_eq_zero_of_dvd hc)
    refine (aligned_coord_iff ha _).2 ?_
    simp only [Function.update_self, map_sub, h1, h2, map_natCast, ZMod.natCast_self]
    simp
  · simpa only [Function.update_of_ne h] using hb i

theorem cubeMap_val_eq (hN : L ^ m₀ ∣ N₁) {g : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hg : g ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) (b : 𝔅)
    {P : CTorus d L N₁ m₁ K} (hP : Aligned (cellSide L m₀ m₁ K) P)
    (h : g '' box b.1 (cellSide L m₀ m₁ K) = box P (cellSide L m₀ m₁ K)) :
    (cubeMap g b).1 = P :=
  eq_of_box_eq hN (cubeMap g b).2.1 hP (by rw [box_cubeMap hN hg, h])

theorem cubeMap_trans (hN : L ^ m₀ ∣ N₁) {σ σ' : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (h : GenSymm L N₁ m₁ K K m₀ σ) (h' : GenSymm L N₁ m₁ K K m₀ σ') (b : 𝔅) :
    cubeMap σ' (cubeMap σ b) = cubeMap (σ.trans σ') b := by
  have hg := genSymm_mem_pavingSymGroup h
  have hg' := genSymm_mem_pavingSymGroup h'
  have hgg := genSymm_mem_pavingSymGroup (GenSymm.trans h h')
  apply Subtype.ext
  refine eq_of_box_eq hN (cubeMap σ' (cubeMap σ b)).2.1 (cubeMap (σ.trans σ') b).2.1 ?_
  rw [box_cubeMap hN hg', box_cubeMap hN hg, box_cubeMap hN hgg, ← Set.image_comp]
  rfl

theorem cubeMap_one (hN : L ^ m₀ ∣ N₁) (b : 𝔅) :
    cubeMap (1 : Equiv.Perm (CTorus d L N₁ m₁ K)) b = b := by
  apply Subtype.ext
  refine cubeMap_val_eq hN (one_mem _) b b.2.1 ?_
  simp

/-- A translation by a multiple of the cell side maps the collar box of a cube onto the collar
box of the image cube (any `L`). -/
theorem collar_image_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (b : 𝔅) :
    (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) ''
        box (collarBase (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBase (cellSide L m₀ m₁ K)
        (cubeMap (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1)
        (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have hg := genSymm_mem_pavingSymGroup (GenSymm.translate (n := K) (m₀ := m₀) t ht)
  have hcm : (cubeMap (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1 = b.1 + t :=
    cubeMap_val_eq hN hg b (aligned_add_of_dvd hdvd b.2.1 ht) (image_box_addRight t _ _)
  rw [hcm, image_box_addRight]
  congr 1
  funext μ
  simp only [collarBase_apply hdvd, Pi.add_apply]
  ring

/-- A coordinate permutation maps the collar box of a cube onto the collar box of the image
cube (any `L`). -/
theorem collar_image_coordPerm (hN : L ^ m₀ ∣ N₁) (π : Equiv.Perm (Fin d)) (b : 𝔅) :
    (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) ''
        box (collarBase (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBase (cellSide L m₀ m₁ K)
        (cubeMap (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1)
        (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have hg := genSymm_mem_pavingSymGroup (GenSymm.perm (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
    (n := K) (m₀ := m₀) π)
  have hcm : (cubeMap (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1 =
      coordPerm π b.1 :=
    cubeMap_val_eq hN hg b (fun μ => b.2.1 (π.symm μ)) (image_box_coordPerm π _ _)
  rw [hcm, image_box_coordPerm]
  congr 1


/-- **A reflection maps the collar box of a cube onto the collar box of the image cube when
`L = 3`**: the box `[b - a, b - a + 3a)` is the cube with one cell on each side. -/
theorem collar_image_reflect (hL : L = 3) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (K + m₀ + m₁) ∣ c.val) (b : 𝔅) :
    (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) ''
        box (collarBase (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBase (cellSide L m₀ m₁ K)
        (cubeMap (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1)
        (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have hg := genSymm_mem_pavingSymGroup (GenSymm.reflect (n := K) (m₀ := m₀) μ₀ c hc)
  have hcm : (cubeMap (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) b).1 =
      Function.update b.1 μ₀ (c - b.1 μ₀ - (cellSide L m₀ m₁ K : ZMod ((N₁ * L ^ m₁) * L ^ K))) :=
    cubeMap_val_eq hN hg b (aligned_refl_update hdvd b.2.1 μ₀ hc)
      (image_box_reflPerm μ₀ c b.1 ha0)
  rw [hcm, image_box_reflPerm μ₀ c _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) ha0)]
  congr 1
  funext i
  by_cases h : i = μ₀
  · subst h
    simp only [Function.update_self, collarBase_apply hdvd]
    subst hL
    push_cast
    ring
  · simp [Function.update_of_ne h, collarBase_apply hdvd]

/-- **Collar boxes under the generated group (`L = 3`).**  For every `σ` of the group generated by
the admissible translations, coordinate permutations and reflections, `σ` maps the collar box of
each cube onto the collar box of the image cube. -/
theorem collar_image_genSymm (hL : L = 3) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ) (b : 𝔅) :
    σ '' box (collarBase (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBase (cellSide L m₀ m₁ K) (cubeMap σ b).1) (L * cellSide L m₀ m₁ K) := by
  induction h generalizing b with
  | one => rw [cubeMap_one hN]; simp
  | translate t ht => exact collar_image_translate hN t ht b
  | perm π => exact collar_image_coordPerm hN π b
  | reflect μ₀ c hc => exact collar_image_reflect hL hN μ₀ c hc b
  | trans h1 h2 ih ih' =>
    rename_i σ σ'
    rw [← cubeMap_trans hN h1 h2]
    show (σ' ∘ σ) '' _ = _
    rw [Set.image_comp, ih b, ih' (cubeMap σ b)]

end Cubes

/-! ### The hull -/

section Hull

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- If a paving symmetry `g` maps the collar box of each cube onto the collar box of the image
cube, then it maps the collar hull of `T` onto the collar hull of `g • T`. -/
theorem detCollarHull_cubeAct_of_collar (hN : L ^ m₀ ∣ N₁) {g : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hg : g ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (hcol : ∀ b : 𝔅, g '' box (collarBase (cellSide L m₀ m₁ K) b.1) (L * cellSide L m₀ m₁ K) =
      box (collarBase (cellSide L m₀ m₁ K) (cubeMap g b).1) (L * cellSide L m₀ m₁ K))
    (T : Finset 𝔅) : detCollarHull (cubeAct g T) = g '' detCollarHull T := by
  classical
  unfold detCollarHull
  rw [Set.image_union, sitesOf_cubeAct hN hg, Set.image_iUnion₂]
  congr 1
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨p, hp, hx⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := mem_cubeAct.1 hc
    exact ⟨_, mem_collarBases_of_mem hb, by rw [hcol b]; exact hx⟩
  · rintro ⟨p, hp, hx⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hp
    rw [hcol b] at hx
    exact ⟨_, mem_collarBases_of_mem (mem_cubeAct.2 ⟨b, hb, rfl⟩), hx⟩

/-- **Translations by multiples of the cell side commute with the collar hull** (any `L`):
`H(σ • T) = σ '' H(T)`. -/
theorem detCollarHull_cubeAct_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (T : Finset 𝔅) :
    detCollarHull (cubeAct (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) T) =
      (Equiv.addRight t : Equiv.Perm (CTorus d L N₁ m₁ K)) '' detCollarHull T :=
  detCollarHull_cubeAct_of_collar hN
    (genSymm_mem_pavingSymGroup (GenSymm.translate (n := K) (m₀ := m₀) t ht))
    (collar_image_translate hN t ht) T

/-- **Coordinate permutations commute with the collar hull** (any `L`). -/
theorem detCollarHull_cubeAct_coordPerm (hN : L ^ m₀ ∣ N₁) (π : Equiv.Perm (Fin d))
    (T : Finset 𝔅) :
    detCollarHull (cubeAct (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) T) =
      (coordPerm π : Equiv.Perm (CTorus d L N₁ m₁ K)) '' detCollarHull T :=
  detCollarHull_cubeAct_of_collar hN
    (genSymm_mem_pavingSymGroup (GenSymm.perm (L := L) (N₁ := N₁) (m₁ := m₁) (K := K)
      (n := K) (m₀ := m₀) π))
    (collar_image_coordPerm hN π) T

/-- **Admissible reflections commute with the collar hull when `L = 3`.**  (For `L > 3` the
collar box based at `b - a` is not symmetric about the cell of `b`, and the reflection of the
box `[b - a, b - a + L a)` is based at `c - b + a - L a`, not at the collar base `c - b - 2a` of
the reflected cube.) -/
theorem detCollarHull_cubeAct_reflect (hL : L = 3) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (K + m₀ + m₁) ∣ c.val) (T : Finset 𝔅) :
    detCollarHull (cubeAct (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) T) =
      (reflPerm μ₀ c : Equiv.Perm (CTorus d L N₁ m₁ K)) '' detCollarHull T :=
  detCollarHull_cubeAct_of_collar hN
    (genSymm_mem_pavingSymGroup (GenSymm.reflect (n := K) (m₀ := m₀) μ₀ c hc))
    (collar_image_reflect hL hN μ₀ c hc) T

/-- **The collar hull commutes with every symmetry of the generated group when `L = 3`.** -/
theorem detCollarHull_cubeAct_genSymm (hL : L = 3) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ) (T : Finset 𝔅) :
    detCollarHull (cubeAct σ T) = σ '' detCollarHull T :=
  detCollarHull_cubeAct_of_collar hN (genSymm_mem_pavingSymGroup h)
    (collar_image_genSymm hL hN h) T

end Hull

/-! ### Fibres and the regrouped sums -/

section Fibre

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- `T` has hull `X` exactly when `σ • T` has hull `σ '' X`. -/
theorem cubeAct_mem_detCollarFibre_iff (hL : L = 3) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ)
    {X : Set (CTorus d L N₁ m₁ K)} {T : Finset 𝔅} :
    cubeAct σ T ∈ detCollarFibre m₀ (σ '' X) ↔ T ∈ detCollarFibre m₀ X := by
  rw [mem_detCollarFibre, mem_detCollarFibre, detCollarHull_cubeAct_genSymm hL hN h]
  exact σ.injective.image_injective.eq_iff

/-- `σ •` maps the fibre of `X` bijectively onto the fibre of `σ '' X`: image form. -/
theorem image_cubeAct_detCollarFibre (hL : L = 3) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ)
    (X : Set (CTorus d L N₁ m₁ K)) :
    (detCollarFibre m₀ X).image (cubeAct σ) = detCollarFibre m₀ (σ '' X) := by
  classical
  have hg := genSymm_mem_pavingSymGroup h
  ext T'
  rw [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact (cubeAct_mem_detCollarFibre_iff hL hN h).2 hT
  · intro hT'
    refine ⟨cubeAct σ⁻¹ T', ?_, ?_⟩
    · have e : cubeAct σ (cubeAct σ⁻¹ T') = T' := by
        simpa using cubeAct_cubeAct hN (inv_mem hg) T'
      exact (cubeAct_mem_detCollarFibre_iff hL hN h).1 (by rw [e]; exact hT')
    · simpa using cubeAct_cubeAct hN (inv_mem hg) T'

/-- **Regrouping is covariant**: if `e' (σ • T) = e T` for all `T`, then the regrouped families
satisfy `e⁺' (σ '' X) = e⁺ X` for `L = 3` and every `σ` of the generated group. -/
theorem detCollarGrouped_comp {E : Type*} [AddCommMonoid E] (hL : L = 3) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ)
    {e e' : Finset 𝔅 → E} (he : ∀ T, e' (cubeAct σ T) = e T) (X : Set (CTorus d L N₁ m₁ K)) :
    detCollarGrouped e' (σ '' X) = detCollarGrouped e X := by
  unfold detCollarGrouped
  rw [← image_cubeAct_detCollarFibre hL hN h X,
    Finset.sum_image (fun T _ T' _ e => cubeAct_injective hN (genSymm_mem_pavingSymGroup h) e)]
  exact Finset.sum_congr rfl fun T _ => he T

end Fibre

/-! ### The regrouped determinant terms -/

section Record

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- **Covariance of the regrouped determinant terms** under every symmetry of the generated
group, at `L = 3` (the collar hull is symmetric about the cube only for `L = 3`, see
`detCollarHull_cubeAct_reflect`).  With the hypotheses of `exists_detExpansionLocC_sym`: there are
records `E`, `E'` for the roots `z` and `rootAct σ z` and a lattice symmetry `Sy`, which maps the
data of the chart to data of the chart, with `E'.term (Sy.sym D) (σ • T) = E.term D T`
and `E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X`. -/
theorem exists_detExpansionLocC_grouped_sym
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (hG : IsLevel S.G' (k + 1)) (hL : L = 3) {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (h : GenSymm L N₁ m₁ (k + 1) (k + 1) m₀ σ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ (E : DetExpansionLocC S m₀ z eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))))
      (E' : DetExpansionLocC S m₀ (rootAct σ z) eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))))),
      ∃ Sy : LatSymm S.G' S.G' σ,
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
          XiCData S.G' S.a S.ν (k + 1) 1 eps (Sy.sym D)) ∧
        (∀ (D : BgData S.G' N) T, E'.term (Sy.sym D) (cubeAct σ T) = E.term D T) ∧
        ∀ (D : BgData S.G' N) (X : Set (CTorus d L N₁ m₁ (k + 1))),
          E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X := by
  obtain ⟨E, E', Sy, h1, h2⟩ := exists_detExpansionLocC_sym S hC hδc hMX hdm hα hsm hconn hN hz
    hG h z
  exact ⟨E, E', Sy, h1, h2, fun D X => detCollarGrouped_comp hL hN h (h2 D) X⟩

end Record

end Balaban.Fluctuation
