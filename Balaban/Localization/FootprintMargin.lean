/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledFieldLocal
public import Balaban.Localization.DecoupledBackgroundLocal
public import Balaban.Fluctuation.StepIdentityQuad
public import Balaban.Localization.DecoupledCovUnit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The footprint inclusion at one full-level step (FOOTPRINT.md, section 1)

Let `G` be a whole-lattice generating set of level `n` (`IsLevel G n`): every site lies in layer
`n`, with block side `ℓ = L ^ n`.  For an interaction box `□_z` (`intBox z`, half-width
`5/2 L ^ (n + m₁)`), this file proves, coordinate by coordinate on the periodic lifts, that

* `approxDep_coord_bound`: a site read by the approximate field at `u` is within `2 ℓ - 1` of `u`
  (the base of an active block is within `2 ℓ - 1` of `u`, from the support radius `3/2` of the
  spline);
* `resSites_coord_bound`: a row site of the residual at `x` (`x`, a nearest neighbour, a site of
  the block of `x`) is within `ℓ` of `x`;
* `resDep_subset_hatBox`, `approxDep_subset_hatBox`: every site read by the residual at a site of
  `□_z`, and by the approximate field at a row site of such a site, lies in the thickened box
  `□̂_z` (`hatBox z`), because `3 ℓ - 1 < 3 L ^ 2 ℓ`;
* `footprint_subset_component`: with the hypotheses of `hdich_aux`, for an eligible centre
  the thickened box lies in the component `Y₁`, so the footprints of the sites of `S_Y` lie in `Y₁`.

Only this geometric inclusion is proved.  The row-local comparison theorems and the physical
locality of the interaction terms (the open items OPEN-PHYSICAL-READS and OPEN-PAPER-REPLACEMENT
of `notes/phase1/FOOTPRINT.md`) are not proved here.

Consistency with `exists_outside_approxDep` (`SupportMarginExample.lean`).  There a site `x` on the
outer face of `X₁` reads a block base `q ∉ X₁`.  This does not contradict the inclusion above:
the inclusion concerns the sites `x` of an interaction box `□_z` with `□̂_z ⊆ Y₁`, and a site that
reads outside `X₁` lies in no such box (`not_exists_box_of_outside_approxDep` in
`FootprintFl.lean`: `x ∈ □_z` and `□̂_z ⊆ S` force `approxDep x ⊆ S`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Near

variable {S : ℕ}

/-- Two sites of the cyclic group `ZMod S` have lifts to `ℤ` (shifts of the representatives in
`[0, S)` by a multiple of `S`) at distance at most `r`. -/
def CoordNear (S : ℕ) (r : ℝ) (a b : ZMod S) : Prop :=
  ∃ p : ℤ, |((a.val : ℝ)) + p * (S : ℝ) - (b.val : ℝ)| ≤ r

theorem CoordNear.refl {r : ℝ} (hr : 0 ≤ r) (a : ZMod S) : CoordNear S r a a :=
  ⟨0, by simpa using hr⟩

theorem CoordNear.mono {r r' : ℝ} {a b : ZMod S} (h : CoordNear S r a b) (hr : r ≤ r') :
    CoordNear S r' a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hr⟩

theorem CoordNear.symm {r : ℝ} {a b : ZMod S} (h : CoordNear S r a b) : CoordNear S r b a := by
  obtain ⟨p, hp⟩ := h
  refine ⟨-p, ?_⟩
  rw [← abs_neg]
  convert hp using 2
  push_cast; ring

theorem CoordNear.trans {r r' : ℝ} {a b c : ZMod S} (h : CoordNear S r a b)
    (h' : CoordNear S r' b c) : CoordNear S (r + r') a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨p', hp'⟩ := h'
  refine ⟨p + p', ?_⟩
  have e : ((a.val : ℝ)) + ((p + p' : ℤ) : ℝ) * (S : ℝ) - (c.val : ℝ) =
      (((a.val : ℝ)) + p * (S : ℝ) - (b.val : ℝ)) + (((b.val : ℝ)) + p' * (S : ℝ) - (c.val : ℝ)) := by
    push_cast; ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add hp hp')

/-- If `a = b + s` for an integer `s` with `|s| ≤ 1`, the sites are at lift distance `≤ 1`. -/
theorem coordNear_step [NeZero S] (a b : ZMod S) (s : ℤ) (hs : |(s : ℝ)| ≤ 1) (h : a = b + (s : ZMod S)) :
    CoordNear S 1 a b := by
  have h1 : (((a.val : ℤ)) : ZMod S) = (((b.val : ℤ) + s : ℤ) : ZMod S) := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; exact h
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  refine ⟨t, ?_⟩
  have : ((a.val : ℝ)) + t * (S : ℝ) - (b.val : ℝ) = s := by
    have h2 : ((b.val : ℤ) + s - a.val : ℤ) = S * t := ht
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) h2
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_mul] at h3
    linarith
  rw [this]; exact hs

/-- Two sites with the same block coordinate `val / N` are at lift distance `≤ N - 1`. -/
theorem coordNear_of_div_eq {N : ℕ} (hN : 0 < N) {a b : ZMod S} (h : a.val / N = b.val / N) :
    CoordNear S ((N : ℝ) - 1) a b := by
  refine ⟨0, ?_⟩
  have ha := Nat.div_add_mod a.val N
  have hb := Nat.div_add_mod b.val N
  have hra := Nat.mod_lt a.val hN
  have hrb := Nat.mod_lt b.val hN
  rw [h] at ha
  have e : (a.val : ℝ) - b.val = (a.val % N : ℕ) - (b.val % N : ℕ) := by
    have h1 : (a.val : ℝ) = N * (b.val / N : ℕ) + (a.val % N : ℕ) := by exact_mod_cast ha.symm
    have h2 : (b.val : ℝ) = N * (b.val / N : ℕ) + (b.val % N : ℕ) := by exact_mod_cast hb.symm
    linarith
  have h3 : ((a.val % N : ℕ) : ℝ) ≤ N - 1 := by
    have : a.val % N + 1 ≤ N := hra
    have : ((a.val % N : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
    linarith
  have h4 : ((b.val % N : ℕ) : ℝ) ≤ N - 1 := by
    have : b.val % N + 1 ≤ N := hrb
    have : ((b.val % N : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
    linarith
  have h5 : (0 : ℝ) ≤ ((a.val % N : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : (0 : ℝ) ≤ ((b.val % N : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [e, abs_le]
  constructor <;> linarith

end Near

section Spline

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- An integer `D` with `-ℓ - 1/2 < D < 2 ℓ - 1/2` has `|D| ≤ 2 ℓ - 1`. -/
theorem abs_le_of_int_window (D : ℤ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h1 : (D : ℝ) < 2 * ℓ - 1 / 2)
    (h2 : -(ℓ : ℝ) - 1 / 2 < D) : |(D : ℝ)| ≤ 2 * ℓ - 1 := by
  have a : D < 2 * (ℓ : ℤ) := by
    have : (D : ℝ) < ((2 * (ℓ : ℤ) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have b : -(ℓ : ℤ) - 1 < D := by
    have : ((-(ℓ : ℤ) - 1 : ℤ) : ℝ) < D := by push_cast; linarith
    exact_mod_cast this
  have c : -(ℓ : ℤ) ≤ D := by omega
  have d' : D ≤ 2 * (ℓ : ℤ) - 1 := by omega
  have c' : ((-(ℓ : ℤ) : ℤ) : ℝ) ≤ D := by exact_mod_cast c
  have d'' : (D : ℝ) ≤ ((2 * (ℓ : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast d'
  push_cast at c' d''
  have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [abs_le]
  constructor <;> linarith

omit [NeZero N₀] in
/-- A coordinate factor of a bump is nonzero only if the site is within `2 L ^ m - 1` of the base
(some lift): this uses the support radius `3/2` of the spline and the centre `(L ^ m - 1)/2`. -/
theorem coordNear_of_perFac_ne_zero {m : ℕ} {y0 u : Torus d (N₀ * L ^ k)} (μ : Fin d)
    (h : perFac m y0 μ ((u μ).val : ℝ) ≠ 0) :
    CoordNear (N₀ * L ^ k) (2 * (L : ℝ) ^ m - 1) (u μ) (y0 μ) := by
  unfold perFac at h
  obtain ⟨p, hp⟩ := exists_of_perN_ne_zero h
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hl : (0 : ℝ) < (L : ℝ) ^ m := by positivity
  have e : (((u μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m +
      p * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) =
      (((u μ).val : ℝ) - bumpCentre m y0 μ + p * ((N₀ * L ^ k : ℕ) : ℝ)) / (L : ℝ) ^ m := by
    field_simp
  rw [e, abs_div, abs_of_pos hl, div_lt_iff₀ hl] at hp
  rw [abs_lt] at hp
  unfold bumpCentre at hp
  set D : ℤ := ((u μ).val : ℤ) + p * ((N₀ * L ^ k : ℕ) : ℤ) - ((y0 μ).val : ℤ) with hD
  have hDr : (D : ℝ) = ((u μ).val : ℝ) + p * ((N₀ * L ^ k : ℕ) : ℝ) - ((y0 μ).val : ℝ) := by
    rw [hD]; push_cast; ring
  have hl1 : 1 ≤ L ^ m := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hlr : ((L ^ m : ℕ) : ℝ) = (L : ℝ) ^ m := by push_cast; rfl
  refine ⟨p, ?_⟩
  have := abs_le_of_int_window D (L ^ m) hl1 (by rw [hlr, hDr]; linarith)
    (by rw [hlr, hDr]; linarith)
  rw [hlr, hDr] at this
  exact this

end Spline

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **Spline read** (FOOTPRINT (c)).  For a level-`n` generating set, a site `v` read by the
approximate field at `u` (that is, `v = u` or `v` the base of a block active at `u`) is, in each
coordinate, at lift distance at most `2 L ^ n - 1` from `u`. -/
theorem approxDep_coord_bound {n : ℕ} (hG : IsLevel G n) {u v : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hv : v ∈ approxDep G u) (μ : Fin d) :
    CoordNear (N₁ * L ^ m₁ * L ^ K) (2 * (L : ℝ) ^ n - 1) (u μ) (v μ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  unfold approxDep at hv
  rw [Finset.mem_insert, Finset.mem_image] at hv
  rcases hv with rfl | ⟨q, hq, rfl⟩
  · exact CoordNear.refl (by linarith) _
  · obtain ⟨hqb, hne⟩ := (mem_active G).1 hq
    obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_blockIdx G).1 hqb
    have hqn : q.1 = n := by
      by_contra hne'
      exact hG.not_mem_layer h1 hK hne' _ hl
    have hp : perFac q.1 q.2 μ ((u μ).val : ℝ) ≠ 0 := fun h0 => hne (by
      unfold bump
      exact Finset.prod_eq_zero (Finset.mem_univ μ) h0)
    have := coordNear_of_perFac_ne_zero (u := u) μ hp
    rw [hqn] at this
    exact this

/-- **Row sites** (FOOTPRINT (b)).  A row site of the residual at `x` in a level-`n` set (`x`, a
nearest neighbour of `x`, a site of the `n`-block of `x`) is at lift distance `≤ L ^ n`. -/
theorem resSites_coord_bound {n : ℕ} (hG : IsLevel G n) {x u : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hu : u ∈ resSites G x) (μ : Fin d) :
    CoordNear (N₁ * L ^ m₁ * L ^ K) ((L : ℝ) ^ n) (u μ) (x μ) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ n :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  unfold resSites at hu
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hu
  rcases hu with rfl | (hb | ⟨ν, rfl⟩) | ⟨ν, rfl⟩
  · exact CoordNear.refl (by linarith) _
  · rw [hG.layerIndex_eq, GeneratingSet.mem_blk] at hb
    have hnK := hG.bounds.2
    have hS := side_eq (L := L) (N₀ := N₁ * L ^ m₁) (k := K) hnK
    have hv := (blockMap_eq_iff_val hS _ _).1 hb μ
    exact (coordNear_of_div_eq (pow_pos hLpos n) hv).mono (by push_cast; linarith)
  · by_cases h : μ = ν
    · subst h
      exact (coordNear_step _ _ 1 (by norm_num) (by simp)).mono hL1
    · exact (coordNear_step _ _ 0 (by norm_num) (by simp [Pi.single_eq_of_ne h])).mono (by linarith)
  · by_cases h : μ = ν
    · subst h
      exact (coordNear_step _ _ (-1) (by norm_num) (by simp [sub_eq_add_neg])).mono hL1
    · exact (coordNear_step _ _ 0 (by norm_num) (by simp [Pi.single_eq_of_ne h])).mono (by linarith)

/-- Sites of one `j`-block, `j ≤ K`, are at lift distance `≤ L ^ j - 1` in every coordinate. -/
theorem jBlock_coord_bound {j : ℕ} (hj : j ≤ K) {x u : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hb : jBlock d L (N₁ * L ^ m₁) K j u = jBlock d L (N₁ * L ^ m₁) K j x) (μ : Fin d) :
    CoordNear (N₁ * L ^ m₁ * L ^ K) ((L : ℝ) ^ j - 1) (u μ) (x μ) := by
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hS := side_eq (L := L) (N₀ := N₁ * L ^ m₁) (k := K) hj
  have hv := (blockMap_eq_iff_val hS _ _).1 hb μ
  have := coordNear_of_div_eq (pow_pos hLpos j) hv
  push_cast at this
  exact this

/-- **Margin for a single site** (FOOTPRINT (a)-(d)).  Let `G` have level `n`, `z` be a centre of
the cover and `x ∈ □_z`.  A site `w` within lift distance `L ^ n` of `x` in every coordinate
has all its approximate-field reads `approxDep G w` inside `□̂_z`.  Only `L ≥ 1` is used: the
reads lie within `L ^ n + 2 L ^ n - 1 < 3 L ^ 2 L ^ n` of the box centre beyond `□_z`. -/
theorem approxDep_subset_hatBox_of_near {n : ℕ} (hG : IsLevel G n)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ intBox z) {w : Torus d (N₁ * L ^ m₁ * L ^ K)}
    (hw : ∀ μ, CoordNear (N₁ * L ^ m₁ * L ^ K) ((L : ℝ) ^ n) (w μ) (x μ)) :
    approxDep G w ⊆ hatBox z := by
  obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_cubeIdx G).1 hz
  have hz1 : z.1 = n := by
    by_contra hne
    exact hG.not_mem_layer h1 hK hne _ hl
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ hL1
  have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
  intro v hv
  unfold hatBox
  rw [mem_boxSet]
  intro μ
  obtain ⟨p0, h0⟩ := (mem_intBox.1 hx) μ
  obtain ⟨p, hp⟩ := ((approxDep_coord_bound hG hv μ).symm.trans (hw μ))
  refine ⟨p + p0, ?_⟩
  have e : ((v μ).val : ℝ) + ((p + p0 : ℤ) : ℝ) * (((N₁ * L ^ m₁ * L ^ K : ℕ)) : ℝ) -
      (((z.2 μ).val : ℝ) + ((L : ℝ) ^ (z.1 + m₁) - 1) / 2) =
      (((v μ).val : ℝ) + p * (((N₁ * L ^ m₁ * L ^ K : ℕ)) : ℝ) - ((x μ).val : ℝ)) +
      (((x μ).val : ℝ) + p0 * (((N₁ * L ^ m₁ * L ^ K : ℕ)) : ℝ) -
        (((z.2 μ).val : ℝ) + ((L : ℝ) ^ (z.1 + m₁) - 1) / 2)) := by
    push_cast; ring
  rw [e]
  refine lt_of_le_of_lt (abs_add_le _ _) ?_
  unfold hatRad
  rw [hz1] at h0 ⊢
  have : (L : ℝ) ^ n ≤ (L : ℝ) ^ 2 * (L : ℝ) ^ n := by nlinarith
  linarith

theorem resDep_subset_hatBox {n : ℕ} (hG : IsLevel G n)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ intBox z) : resDep G x ⊆ hatBox z := by
  classical
  intro v hv
  unfold resDep at hv
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.1 hv
  exact approxDep_subset_hatBox_of_near hG hz hx (resSites_coord_bound hG hu) hvu

/-- The reads of the approximate field at the row sites of a site of `□_z` lie in `□̂_z`. -/
theorem approxDep_resSites_subset_hatBox {n : ℕ} (hG : IsLevel G n)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ intBox z) {u : CTorus d L N₁ m₁ K} (hu : u ∈ resSites G x) :
    approxDep G u ⊆ hatBox z :=
  approxDep_subset_hatBox_of_near hG hz hx (resSites_coord_bound hG hu)

/-- Rows reading a site of the `j`-block of `x`, `j ≤ n` (for instance the `Hm` rows at level
`k = n - 1`, block side `L ^ k`): the reads of the approximate field there lie in `□̂_z`. -/
theorem approxDep_sameBlock_subset_hatBox {n j : ℕ} (hG : IsLevel G n) (hjn : j ≤ n)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ intBox z) {w : CTorus d L N₁ m₁ K}
    (hb : jBlock d L (N₁ * L ^ m₁) K j w = jBlock d L (N₁ * L ^ m₁) K j x) :
    approxDep G w ⊆ hatBox z := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hjle : (L : ℝ) ^ j ≤ (L : ℝ) ^ n := pow_le_pow_right₀ hL1 hjn
  refine approxDep_subset_hatBox_of_near hG hz hx fun μ => ?_
  exact (jBlock_coord_bound (hjn.trans hG.bounds.2) hb μ).mono (by linarith)

/-- **(FP) for the site `x`.**  If the sites `x` of `S_Y` read the residual, then the whole
footprint of the residual and the footprint of the approximate field at its row sites lie in `Y₁`. -/
theorem footprint_subset_component {n : ℕ} (hG : IsLevel G n)
    (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y₁ : Finset (CTorus d L N₁ m₁ K)) :
    (∀ x ∈ SY G X₁ 𝒞 Y₁, resDep G x ⊆ Y₁) ∧
    (∀ x ∈ SY G X₁ 𝒞 Y₁, ∀ u ∈ resSites G x, approxDep G u ⊆ Y₁) := by
  classical
  have key : ∀ x ∈ SY G X₁ 𝒞 Y₁, ∀ u ∈ resSites G x, approxDep G u ⊆ Y₁ := by
    intro x hx u hu v hv
    obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨hz, -, hsub⟩ := Finset.mem_filter.1 hzZ
    have hvh := approxDep_resSites_subset_hatBox hG hz hxz hu hv
    exact hsub ⟨v, by rw [hG.Ω_one]; exact Finset.mem_univ _⟩ hvh
  refine ⟨fun x hx v hv => ?_, key⟩
  unfold resDep at hv
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.1 hv
  exact key x hx u hu hvu

/-- The union form of (FP): the footprint of the residual on `S_Y` lies in `Y₁`. -/
theorem biUnion_resDep_subset {n : ℕ} (hG : IsLevel G n)
    (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y₁ : Finset (CTorus d L N₁ m₁ K)) :
    (SY G X₁ 𝒞 Y₁).biUnion (resDep G) ⊆ Y₁ := by
  intro v hv
  obtain ⟨x, hx, hvx⟩ := Finset.mem_biUnion.1 hv
  exact (footprint_subset_component hG X₁ 𝒞 Y₁).1 x hx hvx

/-- The union form of (FP) for the row sites `R_Y` of `S_Y`. -/
theorem biUnion_approxDep_rowSites_subset {n : ℕ} (hG : IsLevel G n)
    (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y₁ : Finset (CTorus d L N₁ m₁ K)) :
    ((SY G X₁ 𝒞 Y₁).biUnion (resSites G)).biUnion (approxDep G) ⊆ Y₁ := by
  intro v hv
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.1 hv
  obtain ⟨x, hx, hux⟩ := Finset.mem_biUnion.1 hu
  exact (footprint_subset_component hG X₁ 𝒞 Y₁).2 x hx u hux hvu

end Level

section Units

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The `unitQ` rows: sites with the same `L ^ k`-block (`unitBlock`) as `x`. -/
theorem approxDep_unitBlock_subset_hatBox (hG : IsLevel G (k + 1))
    {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox z) {w : CTorus d L N₁ m₁ (k + 1)} (hb : unitBlock w = unitBlock x) :
    approxDep G w ⊆ hatBox z :=
  approxDep_sameBlock_subset_hatBox hG (j := k + 1) le_rfl hz hx (jBlock_eq_of_unitBlock_eq hb)

/-- The `unitP` rows: fine sites of unit points in one `L`-block of the unit lattice lie in one
`L ^ (k+1)`-block (`unitBlock1_unitBlock`). -/
theorem approxDep_unitBlock1_subset_hatBox (hG : IsLevel G (k + 1))
    {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox z) {w : CTorus d L N₁ m₁ (k + 1)}
    (hb : unitBlock1 (unitBlock w) = unitBlock1 (unitBlock x)) :
    approxDep G w ⊆ hatBox z := by
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock] at hb
  exact approxDep_sameBlock_subset_hatBox hG (j := k + 1) le_rfl hz hx hb

/-- The `Hm` rows at level `k` (block side `L ^ k`), read at a site of the `k`-block of `x`. -/
theorem approxDep_hmBlock_subset_hatBox (hG : IsLevel G (k + 1))
    {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cubeIdx G) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ intBox z) {w : CTorus d L N₁ m₁ (k + 1)}
    (hb : jBlock d L (N₁ * L ^ m₁) (k + 1) k w = jBlock d L (N₁ * L ^ m₁) (k + 1) k x) :
    approxDep G w ⊆ hatBox z :=
  approxDep_sameBlock_subset_hatBox hG (Nat.le_succ k) hz hx hb

end Units

end Balaban.Localization
