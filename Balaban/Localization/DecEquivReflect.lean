/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivPermute

/-!
# Reflection symmetry of the periodized bump

The one-dimensional spline `bsp` and its periodization `perN` are even.  Consequently the bump
of the block of base `y₀` and scale `L ^ m` is reflection symmetric: if the coordinate `μ₀` of
the torus is reflected, `x_μ₀ ↦ c - 1 - x_μ₀`, and the base point is moved to the opposite corner
`y₀_μ₀ ↦ c - L ^ m - y₀_μ₀` of the image cube, the bump value is unchanged (`bump_reflect`),
for every `c` (no divisibility is needed for this identity).  This is the evenness needed for the
reflection clauses of `CoverSymm` and `BlockSymm` with the corner-corrected action on the centres.

The second half of the file constructs the reflection `x_μ₀ ↦ c - 1 - x_μ₀` of the fine torus as
an inhabitant of `LatSymm`, `CoverSymm (coverOf G)` and `BlockSymm G` for a level set `G`
(`IsLevel G n`), with the corner-corrected action
`(j, y₀) ↦ (j, y₀[μ₀ := c - sd j - y₀ μ₀])` on the centres (`reflectCentres`), where `sd j` is the
side of the cube (`L ^ (j + m₁)`) or of the block (`L ^ j`).  The exact divisibility needed is
* `LatSymm.ofReflectLevel`, `BlockSymm.ofReflect`: `L ^ n ∣ c.val`;
* `CoverSymm.ofReflect`: `L ^ (n + m₁) ∣ c.val`.

Covariance of the output terms of a step is not proved here, only that the symmetry data exist.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

theorem bsp_neg (t : ℝ) : bsp (-t) = bsp t := by
  rcases le_total t (-3 / 2) with h | h
  · rw [bsp_far_left h, bsp_far_right (by linarith)]
  rcases le_total t (-1 / 2) with h' | h'
  · rw [bsp_left h h', bsp_right (by linarith) (by linarith)]; ring
  rcases le_total t (1 / 2) with h'' | h''
  · rw [bsp_mid h' h'', bsp_mid (by linarith) (by linarith)]; ring
  rcases le_total t (3 / 2) with h3 | h3
  · rw [bsp_right h'' h3, bsp_left (by linarith) (by linarith)]; ring
  · rw [bsp_far_right h3, bsp_far_left (by linarith)]

theorem perN_neg (r α : ℝ) : perN r (-α) = perN r α := by
  unfold perN
  rw [← finsum_comp_equiv (Equiv.neg ℤ) (f := fun p : ℤ => bsp (α + p * r))]
  refine finsum_congr fun p => ?_
  simp only [Equiv.neg_apply]
  rw [← bsp_neg]
  congr 1
  push_cast; ring

theorem exists_val_eq {n : ℕ} [NeZero n] (u : ZMod n) (z : ℤ) (h : u = (z : ZMod n)) :
    ∃ e : ℤ, ((u.val : ℕ) : ℝ) = (z : ℝ) + (n : ℝ) * e := by
  have h1 : (((u.val : ℕ) : ℤ) : ZMod n) = ((z : ℤ) : ZMod n) := by
    rw [← h]; simp
  obtain ⟨e, he⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h1
  refine ⟨-e, ?_⟩
  have : (z : ℝ) - ((u.val : ℕ) : ℝ) = (n : ℝ) * e := by exact_mod_cast he
  push_cast; linarith

section Bump

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- **The periodized bump is reflection symmetric.**  Reflecting the coordinate `μ₀` by
`x ↦ c - 1 - x` and moving the base point of the block to the opposite corner
`y₀ ↦ c - L ^ m - y₀` of the image cube leaves the bump unchanged. -/
theorem bump_reflect (m : ℕ) (μ₀ : Fin d) (c : ZMod (N₀ * L ^ k))
    (y0 x : Torus d (N₀ * L ^ k)) :
    bump m (Function.update y0 μ₀ (c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) - y0 μ₀))
      (reflPerm μ₀ c x) = bump m y0 x := by
  unfold bump
  refine Finset.prod_congr rfl fun μ _ => ?_
  by_cases hμ : μ = μ₀
  · subst hμ
    simp only [reflPerm, Equiv.coe_fn_mk, Function.update_self]
    unfold perFac bumpCentre
    simp only [Function.update_self]
    obtain ⟨e1, h1⟩ := exists_val_eq (c - 1 - x μ) ((c.val : ℤ) - 1 - (x μ).val)
      (by push_cast; simp)
    obtain ⟨e2, h2⟩ := exists_val_eq (c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) - y0 μ)
      ((c.val : ℤ) - (L ^ m : ℕ) - (y0 μ).val) (by push_cast; simp)
    have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have key : ((((c - 1 - x μ).val : ℕ) : ℝ) - ((((c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) -
          y0 μ).val : ℕ) : ℝ) + (((L : ℝ) ^ m - 1) / 2))) / (L : ℝ) ^ m =
        -((((x μ).val : ℕ) : ℝ) - ((((y0 μ).val : ℕ) : ℝ) + (((L : ℝ) ^ m - 1) / 2))) /
          (L : ℝ) ^ m + ((e1 - e2 : ℤ) : ℝ) * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) := by
      rw [h1, h2]
      push_cast
      field_simp
      ring
    rw [key, perN_add_int_mul, neg_div, perN_neg]
  · have : Function.update y0 μ₀ (c - ((L ^ m : ℕ) : ZMod (N₀ * L ^ k)) - y0 μ₀) μ = y0 μ :=
      Function.update_of_ne hμ _ _
    simp only [reflPerm, Equiv.coe_fn_mk, Function.update_of_ne hμ]
    unfold perFac bumpCentre
    rw [this]

end Bump


/-! ### Arithmetic of the reflection -/

section ReflArith

variable {M : ℕ} [NeZero M]

theorem dvd_val_iff_castHom {s : ℕ} (hs : s ∣ M) (x : ZMod M) :
    s ∣ x.val ↔ ZMod.castHom hs (ZMod s) x = 0 := by
  have : NeZero s := ⟨by rintro rfl; exact NeZero.ne M (zero_dvd_iff.1 hs)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem dvd_val_refl_iff' {a t : ℕ} (hs : a ∣ M) (hat : a ∣ t) (c y : ZMod M)
    (hc : a ∣ c.val) : a ∣ (c - (t : ZMod M) - y).val ↔ a ∣ y.val := by
  rw [dvd_val_iff_castHom hs, dvd_val_iff_castHom hs]
  have hc' := (dvd_val_iff_castHom hs c).1 hc
  rw [map_sub, map_sub, hc', map_natCast, (ZMod.natCast_eq_zero_iff _ _).2 hat]
  simp

theorem dvd_val_refl_iff {s : ℕ} (hs : s ∣ M) (c y : ZMod M) (hc : s ∣ c.val) :
    s ∣ (c - (s : ZMod M) - y).val ↔ s ∣ y.val :=
  dvd_val_refl_iff' hs dvd_rfl c y hc

theorem val_add_pred {s : ℕ} (hs : s ∣ M) (hs0 : 0 < s) (q : ZMod M) (hq : s ∣ q.val) :
    (q + ((s - 1 : ℕ) : ZMod M)).val = q.val + (s - 1) := by
  obtain ⟨m', hm'⟩ := hs
  obtain ⟨u, hu⟩ := hq
  have hlt : q.val < M := ZMod.val_lt q
  have hsM : s - 1 < M := by
    have : 0 < m' := Nat.pos_of_ne_zero (fun h => NeZero.ne M (by rw [hm', h, mul_zero]))
    have : s ≤ s * m' := Nat.le_mul_of_pos_right _ this
    omega
  have hum : u + 1 ≤ m' := by
    by_contra hcon
    have : m' ≤ u := by omega
    have : s * m' ≤ s * u := Nat.mul_le_mul_left _ this
    omega
  have hlt2 : q.val + (s - 1) < M := by
    have : s * (u + 1) ≤ s * m' := Nat.mul_le_mul_left _ hum
    rw [mul_add, mul_one] at this
    omega
  have hv : ((s - 1 : ℕ) : ZMod M).val = s - 1 := ZMod.val_natCast_of_lt hsM
  rw [ZMod.val_add_of_lt (by rw [hv]; exact hlt2), hv]

theorem val_add_pred_div' {s a : ℕ} (hs : s ∣ M) (hsa : s ∣ a) (hs0 : 0 < s) (q : ZMod M)
    (hq : s ∣ q.val) : (q + ((s - 1 : ℕ) : ZMod M)).val / a = q.val / a := by
  obtain ⟨b, hb⟩ := hsa
  obtain ⟨u, hu⟩ := hq
  rw [val_add_pred hs hs0 q ⟨u, hu⟩, hb, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [hu, Nat.mul_add_div hs0, Nat.div_eq_of_lt (by omega : s - 1 < s), Nat.mul_div_cancel_left _ hs0]
  simp

theorem val_add_pred_div {s : ℕ} (hs : s ∣ M) (hs0 : 0 < s) (q : ZMod M) (hq : s ∣ q.val) :
    (q + ((s - 1 : ℕ) : ZMod M)).val / s = q.val / s :=
  val_add_pred_div' hs dvd_rfl hs0 q hq

theorem div_val_eq_iff {s m' : ℕ} (hℓ : M = s * m') (y w : ZMod M) :
    y.val / s = w.val / s ↔ blockCoord s m' y = blockCoord s m' w := by
  unfold blockCoord
  constructor
  · intro h; rw [h]
  · intro h
    have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
    have h1 : y.val / s < m' := Nat.div_lt_of_lt_mul (hℓ ▸ ZMod.val_lt y)
    have h2 : w.val / s < m' := Nat.div_lt_of_lt_mul (hℓ ▸ ZMod.val_lt w)
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h'

theorem div_val_refl_iff {s m' : ℕ} (hℓ : M = s * m') (hs0 : 0 < s) (c y w : ZMod M)
    (hc : s ∣ c.val) :
    (c - 1 - y).val / s = (c - 1 - w).val / s ↔ y.val / s = w.val / s := by
  rw [div_val_eq_iff hℓ, div_val_eq_iff hℓ]
  have key : ∀ z : ZMod M, blockCoord s m' (c - 1 - z) =
      -1 - blockCoord s m' z + ((c.val / s : ℕ) : ZMod m') := fun z => by
    rw [show c - 1 - z = (-1 - z) + c by ring, blockCoord_add_of_dvd hℓ _ _ hc,
      blockCoord_neg_one_sub hs0 hℓ]
  simp only [key, add_left_inj, sub_right_inj]

end ReflArith

/-! ### The reflection on the centres -/

section ReflCentres

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}

/-- The opposite-corner map `y₀ ↦ y₀[μ₀ := c - s - y₀ μ₀]` on the base points of cubes or blocks
of side `s`. -/
def reflBase {M : ℕ} (s : ℕ) (μ₀ : Fin d) (c : ZMod M) (y : Torus d M) : Torus d M :=
  Function.update y μ₀ (c - (s : ZMod M) - y μ₀)

theorem reflBase_reflBase {M : ℕ} (s : ℕ) (μ₀ : Fin d) (c : ZMod M) (y : Torus d M) :
    reflBase s μ₀ c (reflBase s μ₀ c y) = y := by
  funext i
  by_cases h : i = μ₀
  · subst h; simp [reflBase]
  · simp [reflBase, h]

/-- The action `(j, y₀) ↦ (j, y₀[μ₀ := c - sd j - y₀ μ₀])` on the centres; `sd j` is the side of the
cube (`L ^ (j + m₁)`) or of the block (`L ^ j`) of layer `j`.  It is an involution on every layer. -/
def reflectCentres (sd : ℕ → ℕ) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) :
    Equiv.Perm (ℕ × CTorus d L N₁ m₁ K) where
  toFun q := (q.1, reflBase (sd q.1) μ₀ c q.2)
  invFun q := (q.1, reflBase (sd q.1) μ₀ c q.2)
  left_inv q := by simp [reflBase_reflBase]
  right_inv q := by simp [reflBase_reflBase]

omit [NeZero N₁] [NeZero L] in
@[simp] theorem reflectCentres_apply (sd : ℕ → ℕ) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (q : ℕ × CTorus d L N₁ m₁ K) :
    reflectCentres (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) sd μ₀ c q =
      (q.1, reflBase (sd q.1) μ₀ c q.2) := rfl

/-- The centre map of the cover (cube side `L ^ (j + m₁)`). -/
abbrev reflectCover (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) :
    Equiv.Perm (ℕ × CTorus d L N₁ m₁ K) :=
  reflectCentres (fun j => L ^ (j + m₁)) μ₀ c

/-- The centre map of the blocks (block side `L ^ j`). -/
abbrev reflectBlock (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) :
    Equiv.Perm (ℕ × CTorus d L N₁ m₁ K) :=
  reflectCentres (fun j => L ^ j) μ₀ c

theorem eq_of_mem_layer (hG : IsLevel G n) {j : ℕ} (h1 : 1 ≤ j) (hk : j ≤ K)
    {x : CTorus d L N₁ m₁ K} (hl : x ∈ G.layer j) : j = n := by
  have := G.layerIndex_eq h1 hk hl
  rw [(hG x).2] at this
  exact this.symm

omit [NeZero N₁] [NeZero L] in
theorem reflPerm_symm (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) :
    (reflPerm μ₀ c).symm = reflPerm μ₀ c := rfl

theorem cubeBase_reflBase_iff {j : ℕ} (hj : j ≤ K) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (j + m₁) ∣ c.val) (y : CTorus d L N₁ m₁ K) :
    CubeBase m₁ j (reflBase (L ^ (j + m₁)) μ₀ c y) ↔ CubeBase m₁ j y := by
  unfold CubeBase
  refine forall_congr' fun μ => ?_
  by_cases h : μ = μ₀
  · subst h
    simp only [reflBase, Function.update_self, ← Nat.dvd_iff_mod_eq_zero]
    exact dvd_val_refl_iff (dvd_side hj) c (y μ) hc
  · simp [reflBase, h]

theorem isBase_reflBase_iff {j : ℕ} (hj : j ≤ K) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ j ∣ c.val) (y : CTorus d L N₁ m₁ K) :
    IsBase j (reflBase (L ^ j) μ₀ c y) ↔ IsBase j y := by
  unfold IsBase
  refine forall_congr' fun μ => ?_
  by_cases h : μ = μ₀
  · subst h
    simp only [reflBase, Function.update_self, ← Nat.dvd_iff_mod_eq_zero]
    exact dvd_val_refl_iff (dvd_side' hj) c (y μ) hc
  · simp [reflBase, h]

theorem inBox_refl_iff (j : ℕ) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (y0 x : CTorus d L N₁ m₁ K) (R : ℝ) :
    InBox m₁ j (reflBase (L ^ (j + m₁)) μ₀ c y0) R (reflPerm μ₀ c x) ↔ InBox m₁ j y0 R x := by
  unfold InBox
  refine forall_congr' fun μ => ?_
  by_cases h : μ = μ₀
  · subst h
    simp only [reflBase, reflPerm, Equiv.coe_fn_mk, Function.update_self]
    obtain ⟨e1, h1⟩ := exists_val_eq (c - 1 - x μ) ((c.val : ℤ) - 1 - (x μ).val)
      (by push_cast; simp)
    obtain ⟨e2, h2⟩ := exists_val_eq (c - ((L ^ (j + m₁) : ℕ) : ZMod _) - y0 μ)
      ((c.val : ℤ) - (L ^ (j + m₁) : ℕ) - (y0 μ).val) (by push_cast; simp)
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨-(p + e1 - e2), ?_⟩
      rw [← abs_neg]
      convert hp using 2
      rw [h1, h2]; push_cast; ring
    · rintro ⟨p, hp⟩
      refine ⟨-p - e1 + e2, ?_⟩
      rw [← abs_neg]
      convert hp using 2
      rw [h1, h2]; push_cast; ring
  · simp [reflBase, reflPerm, h]

theorem castT_reflect {n n' : ℕ} (h : n = n') (μ : Fin d) (c : ZMod n) (s : ℕ)
    (y x : Torus d n) :
    castT h (Function.update y μ (c - (s : ZMod n) - y μ)) =
      Function.update (castT h y) μ (castT h (fun _ => c) μ - (s : ZMod n') - castT h y μ) ∧
    castT h (Function.update x μ (c - 1 - x μ)) =
      Function.update (castT h x) μ (castT h (fun _ => c) μ - 1 - castT h x μ) := by
  subst h; exact ⟨rfl, rfl⟩

theorem cubeBump_reflect (j : ℕ) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (y0 x : CTorus d L N₁ m₁ K) :
    cubeBump m₁ j (reflBase (L ^ (j + m₁)) μ₀ c y0) (reflPerm μ₀ c x) = cubeBump m₁ j y0 x := by
  unfold cubeBump tor
  obtain ⟨h1, -⟩ := castT_reflect (cubeSide_eq N₁ L m₁ K) μ₀ c (L ^ (j + m₁)) y0 x
  obtain ⟨-, h2⟩ := castT_reflect (cubeSide_eq N₁ L m₁ K) μ₀ c (L ^ (j + m₁)) y0 x
  unfold reflBase reflPerm
  simp only [Equiv.coe_fn_mk]
  rw [h1, h2]
  exact bump_reflect (j + m₁) μ₀ _ _ _

theorem sameCell_refl_iff {s : ℕ} (hs : s ∣ (N₁ * L ^ m₁) * L ^ K) (hs0 : 0 < s) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : s ∣ c.val) (y q : CTorus d L N₁ m₁ K)
    (hq : ∀ μ, s ∣ (q μ).val) :
    SameCell s (reflPerm μ₀ c y) (reflBase s μ₀ c q) ↔ SameCell s y q := by
  unfold SameCell
  refine forall_congr' fun μ => ?_
  by_cases h : μ = μ₀
  · subst h
    simp only [reflBase, reflPerm, Equiv.coe_fn_mk, Function.update_self]
    obtain ⟨m', hm'⟩ := hs
    have e : c - (s : ZMod ((N₁ * L ^ m₁) * L ^ K)) - q μ =
        c - 1 - (q μ + ((s - 1 : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) := by
      rw [Nat.cast_sub hs0, Nat.cast_one]; ring
    rw [e, div_val_refl_iff hm' hs0 c _ _ hc, val_add_pred_div ⟨m', hm'⟩ hs0 _ (hq μ)]
  · simp [reflBase, reflPerm, h]

end ReflCentres


/-! ### The structures -/

section Structures

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}

/-- **(R1) The reflection `x_μ₀ ↦ c - 1 - x_μ₀` is a lattice symmetry of a level set** when
`L ^ n ∣ c.val`. -/
def LatSymm.ofReflectLevel (hG : IsLevel G n) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (hc : L ^ n ∣ c.val) : LatSymm G G (reflPerm μ₀ c) :=
  LatSymm.ofReflect n μ₀ c hc
    (fun i h1 hk x => by
      rw [level_mem_Ω hG h1 hk (reflPerm μ₀ c x), level_mem_Ω hG h1 hk x])
    (fun n' h1 hk hne => by
      obtain ⟨x, hx⟩ := hne
      have := G.layerIndex_eq h1 hk hx
      rw [(hG x).2] at this
      exact this.ge)

theorem refl_mem_cubeIdx_iff (hG : IsLevel G n) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (n + m₁) ∣ c.val)
    (q : ℕ × CTorus d L N₁ m₁ K) : reflectCover μ₀ c q ∈ cubeIdx G ↔ q ∈ cubeIdx G := by
  simp only [mem_cubeIdx, reflectCentres_apply]
  constructor
  · rintro ⟨hr, hl, hb⟩
    have hqn : q.1 = n := eq_of_mem_layer hG hr.1 hr.2 hl
    refine ⟨hr, by rw [hqn]; exact hG.mem_layer _, ?_⟩
    exact (cubeBase_reflBase_iff hr.2 μ₀ c (by rw [hqn]; exact hc) q.2).1 hb
  · rintro ⟨hr, hl, hb⟩
    have hqn : q.1 = n := eq_of_mem_layer hG hr.1 hr.2 hl
    refine ⟨hr, by rw [hqn]; exact hG.mem_layer _, ?_⟩
    exact (cubeBase_reflBase_iff hr.2 μ₀ c (by rw [hqn]; exact hc) q.2).2 hb

theorem refl_mem_blockIdx_iff (hG : IsLevel G n) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ n ∣ c.val)
    (q : ℕ × CTorus d L N₁ m₁ K) : reflectBlock μ₀ c q ∈ blockIdx G ↔ q ∈ blockIdx G := by
  simp only [mem_blockIdx, reflectCentres_apply]
  constructor
  · rintro ⟨hr, hl, hb⟩
    have hqn : q.1 = n := eq_of_mem_layer hG hr.1 hr.2 hl
    refine ⟨hr, by rw [hqn]; exact hG.mem_layer _, ?_⟩
    exact (isBase_reflBase_iff hr.2 μ₀ c (by rw [hqn]; exact hc) q.2).1 hb
  · rintro ⟨hr, hl, hb⟩
    have hqn : q.1 = n := eq_of_mem_layer hG hr.1 hr.2 hl
    refine ⟨hr, by rw [hqn]; exact hG.mem_layer _, ?_⟩
    exact (isBase_reflBase_iff hr.2 μ₀ c (by rw [hqn]; exact hc) q.2).2 hb

/-- **(R3) The reflection is compatible with the blocks of the interpolation of a level set**
when `L ^ n ∣ c.val`; the action on the block indices is `(j, y₀) ↦ (j, y₀[μ₀ := c - L ^ j - y₀ μ₀])`. -/
def BlockSymm.ofReflect (hG : IsLevel G n) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (hc : L ^ n ∣ c.val) : BlockSymm G (reflPerm μ₀ c) where
  τ := reflectBlock μ₀ c
  idx := refl_mem_blockIdx_iff hG μ₀ c hc
  layer := fun _ => rfl
  bump := fun q x => bump_reflect q.1 μ₀ c q.2 x
  base := fun q hq => by
    obtain ⟨⟨h1, hk⟩, hl, hb⟩ := (mem_blockIdx G).1 hq
    have hs0 : 0 < L ^ q.1 := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
    have hℓ := side_eq (N₀ := N₁ * L ^ m₁) (L := L) hk
    funext i
    rw [jBlock_apply, jBlock_apply, reflPerm_symm]
    by_cases h : i = μ₀
    · subst h
      simp only [reflectCentres_apply, reflBase, reflPerm, Equiv.coe_fn_mk,
        Function.update_self]
      have e : c - 1 - (c - ((L ^ q.1 : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) - q.2 i) =
          q.2 i + ((L ^ q.1 - 1 : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hs0.ne'), Nat.cast_one]; ring
      rw [e]
      unfold blockCoord
      rw [val_add_pred_div ⟨_, hℓ⟩ hs0 _ (Nat.dvd_of_mod_eq_zero (hb i))]
    · simp [reflectCentres_apply, reflBase, reflPerm, h]

theorem coverDenom_reflect (hG : IsLevel G n) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (hc : L ^ (n + m₁) ∣ c.val) (x : CTorus d L N₁ m₁ K) :
    coverDenom G (reflPerm μ₀ c x) = coverDenom G x := by
  unfold coverDenom
  refine (Finset.sum_equiv (reflectCover μ₀ c)
    (fun q => (refl_mem_cubeIdx_iff hG μ₀ c hc q).symm) fun q _ => ?_).symm
  exact (cubeBump_reflect q.1 μ₀ c q.2 x).symm

/-- **(R2) The reflection is compatible with the cover of a level set** when
`L ^ (n + m₁) ∣ c.val`; the action on the centres is
`(j, y₀) ↦ (j, y₀[μ₀ := c - L ^ (j + m₁) - y₀ μ₀])`. -/
def CoverSymm.ofReflect (hG : IsLevel G n) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (hc : L ^ (n + m₁) ∣ c.val) : CoverSymm (coverOf G) (reflPerm μ₀ c) where
  τ := reflectCover μ₀ c
  idx := refl_mem_cubeIdx_iff hG μ₀ c hc
  chi := fun q x => by
    show Balaban.Localization.chi G (q.1, reflBase (L ^ (q.1 + m₁)) μ₀ c q.2) (reflPerm μ₀ c x) =
      Balaban.Localization.chi G q x
    unfold Balaban.Localization.chi
    rw [coverDenom_reflect hG μ₀ c hc]
    exact congrArg (· / coverDenom G x) (cubeBump_reflect q.1 μ₀ c q.2 x)
  box := fun q x => by
    show reflPerm μ₀ c x ∈ intBox (q.1, reflBase (L ^ (q.1 + m₁)) μ₀ c q.2) ↔ x ∈ intBox q
    rw [mem_intBox, mem_intBox]
    exact inBox_refl_iff q.1 μ₀ c q.2 x _
  qset := fun q q' => by
    have hidx := refl_mem_cubeIdx_iff hG μ₀ c hc q'
    show (q'.1, reflBase (L ^ (q'.1 + m₁)) μ₀ c q'.2) ∈ (coverOf G).Qset
        (q.1, reflBase (L ^ (q.1 + m₁)) μ₀ c q.2) ↔ q' ∈ (coverOf G).Qset q
    rw [DecCover.mem_Qset, DecCover.mem_Qset]
    have hid : (coverOf G).cubeIdx = cubeIdx G := rfl
    rw [hid]
    have key : q' ∈ cubeIdx G → ∀ y : CTorus d L N₁ m₁ K,
        SameCell (L ^ (q'.1 + m₁)) (reflPerm μ₀ c y) (reflBase (L ^ (q'.1 + m₁)) μ₀ c q'.2) ↔
          SameCell (L ^ (q'.1 + m₁)) y q'.2 := fun h1 y => by
      obtain ⟨hr, -, hb⟩ := (mem_cubeIdx G).1 h1
      have hqn : q'.1 = n := fst_eq_of_mem_cubeIdx hG h1
      exact sameCell_refl_iff (dvd_side hr.2) (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L)))
        μ₀ c (by rw [hqn]; exact hc) y q'.2 (fun μ => Nat.dvd_of_mod_eq_zero (hb μ))
    constructor
    · rintro ⟨h1, y, hy1, hy2⟩
      have h1' : q' ∈ cubeIdx G := hidx.1 h1
      refine ⟨h1', reflPerm μ₀ c y, ?_, ?_⟩
      · refine (key h1' (reflPerm μ₀ c y)).1 ?_
        have : reflPerm μ₀ c (reflPerm μ₀ c y) = y := (reflPerm μ₀ c).symm_apply_apply y
        rw [this]; exact hy1
      · refine (inBox_refl_iff q.1 μ₀ c q.2 (reflPerm μ₀ c y) _).1 ?_
        have : reflPerm μ₀ c (reflPerm μ₀ c y) = y := (reflPerm μ₀ c).symm_apply_apply y
        rw [this]; exact hy2
    · rintro ⟨h1, y, hy1, hy2⟩
      exact ⟨hidx.2 h1, reflPerm μ₀ c y, (key h1 y).2 hy1,
        (inBox_refl_iff q.1 μ₀ c q.2 y _).2 hy2⟩

end Structures

end Balaban.Localization.DecEquiv
