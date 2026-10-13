/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivLatBg
public import Balaban.Localization.DecEquivTerms
public import Balaban.Fluctuation.CriticalPoint

/-!
# Translations as symmetries of the cover and of the interpolation blocks

The structures `LatSymm`, `CoverSymm`, `BlockSymm` (and `PolymerSymm`) of the covariance package
had only the identity as an inhabitant.  Here the translations `σ_t : x ↦ x + t` of the fine
torus `CTorus d L N₁ m₁ K` are constructed as inhabitants, for a whole-lattice generating set `G`
of level `n` (`IsLevel G n`: every site lies in the layer `n`).  This file is stated for level
sets only; it does not use any property of a particular generating set beyond `IsLevel`.

* `LatSymm.ofTranslateLevel`: `LatSymm G G σ_t` when `L ^ n ∣ t_μ` for all `μ`;
* `BlockSymm.ofTranslate`: `BlockSymm G σ_t` when `L ^ n ∣ t_μ` (the bumps `b_B` of the blocks
  are invariant under every translation; the base points are only needed in the index set);
* `CoverSymm.ofTranslate`: `CoverSymm (coverOf G) σ_t` when `L ^ (n + m₁) ∣ t_μ` (the cubes of
  the cover have side `L ^ (n + m₁)`).

Covariance of the output terms of a step is not proved here; only that the symmetry data exist.
`PolymerSymm` asks for the identities for every centre `q`, so a nonzero translation cannot
satisfy it in general; the part that does hold is `Pset_translate`.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

/-! ### Arithmetic of translations on `ZMod n` -/

section Arith

theorem val_add_split {n : ℕ} [NeZero n] (a b : ZMod n) :
    ∃ e : ℕ, (a + b).val + n * e = a.val + b.val :=
  ⟨(a.val + b.val) / n, by rw [ZMod.val_add]; exact Nat.mod_add_div _ _⟩

theorem mod_zero_add_iff {n a : ℕ} [NeZero n] (han : a ∣ n) (y t : ZMod n) (ht : a ∣ t.val) :
    (y + t).val % a = 0 ↔ y.val % a = 0 := by
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ han, ← Nat.dvd_iff_mod_eq_zero,
    ← Nat.dvd_iff_mod_eq_zero]
  exact Nat.dvd_add_left ht

theorem div_val_add {n a : ℕ} [NeZero n] (han : a ∣ n) (y t : ZMod n) (ht : a ∣ t.val) :
    ∃ c : ℕ, n = a * c ∧ (y + t).val / a = (y.val / a + t.val / a) % c ∧ y.val / a < c := by
  obtain ⟨c, hc⟩ := han
  have hapos : 0 < a := Nat.pos_of_ne_zero (fun h => NeZero.ne n (by rw [hc, h, zero_mul]))
  refine ⟨c, hc, ?_, ?_⟩
  · have key : (y.val + t.val) % n / a = ((y.val + t.val) / a) % c := by
      have := Nat.mod_mul_right_div_self (y.val + t.val) a c
      rwa [← hc] at this
    rw [ZMod.val_add, key, Nat.add_div_of_dvd_left ht]
  · apply Nat.div_lt_of_lt_mul
    rw [← hc]; exact ZMod.val_lt y

theorem sameCell_add_iff {d n a : ℕ} [NeZero n] (han : a ∣ n) (x y t : Torus d n)
    (ht : ∀ μ, a ∣ (t μ).val) :
    SameCell a (x + t) (y + t) ↔ SameCell a x y := by
  unfold SameCell
  refine forall_congr' fun μ => ?_
  obtain ⟨c, hc, hx, hxl⟩ := div_val_add han (x μ) (t μ) (ht μ)
  obtain ⟨c', hc', hy, hyl⟩ := div_val_add han (y μ) (t μ) (ht μ)
  have : c = c' := by
    have hapos : 0 < a := Nat.pos_of_ne_zero (fun h => NeZero.ne n (by rw [hc, h, zero_mul]))
    exact Nat.eq_of_mul_eq_mul_left hapos (hc.symm.trans hc')
  subst this
  simp only [Pi.add_apply]
  rw [hx, hy]
  constructor
  · intro h
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' ((t μ).val / a) h) hxl hyl
  · intro h; rw [h]

end Arith

/-! ### Invariance of the bumps -/

section Bumps

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- The periodized bump is covariant under every translation of the torus. -/
theorem bump_translate (m : ℕ) (y0 x t : Torus d (N₀ * L ^ k)) :
    bump m (y0 + t) (x + t) = bump m y0 x := by
  unfold bump
  refine Finset.prod_congr rfl fun μ _ => ?_
  unfold perFac bumpCentre
  obtain ⟨ex, hx⟩ := val_add_split (x μ) (t μ)
  obtain ⟨ey, hy⟩ := val_add_split (y0 μ) (t μ)
  simp only [Pi.add_apply]
  have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hxR : (((x μ + t μ).val : ℕ) : ℝ) = ((x μ).val : ℝ) + ((t μ).val : ℝ) -
      ((N₀ * L ^ k : ℕ) : ℝ) * ex := by
    have := congrArg (fun z : ℕ => (z : ℝ)) hx
    push_cast at this ⊢
    linarith
  have hyR : (((y0 μ + t μ).val : ℕ) : ℝ) = ((y0 μ).val : ℝ) + ((t μ).val : ℝ) -
      ((N₀ * L ^ k : ℕ) : ℝ) * ey := by
    have := congrArg (fun z : ℕ => (z : ℝ)) hy
    push_cast at this ⊢
    linarith
  have key : ((((x μ + t μ).val : ℕ) : ℝ) - ((((y0 μ + t μ).val : ℕ) : ℝ) +
        (((L : ℝ) ^ m - 1) / 2))) / (L : ℝ) ^ m =
      ((((x μ).val : ℕ) : ℝ) - ((((y0 μ).val : ℕ) : ℝ) + (((L : ℝ) ^ m - 1) / 2))) / (L : ℝ) ^ m +
        (((ey : ℤ) - (ex : ℤ) : ℤ) : ℝ) * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) := by
    rw [hxR, hyR]
    push_cast
    field_simp
    ring
  rw [key]
  exact perN_add_int_mul _ _ _

end Bumps

section Cube

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem cubeBump_translate (j : ℕ) (y0 x t : CTorus d L N₁ m₁ K) :
    cubeBump m₁ j (y0 + t) (x + t) = cubeBump m₁ j y0 x := by
  unfold cubeBump tor
  rw [castT_add, castT_add]
  exact bump_translate _ _ _ _

theorem inBox_add_iff (j : ℕ) (y0 x t : CTorus d L N₁ m₁ K) (R : ℝ) :
    InBox m₁ j (y0 + t) R (x + t) ↔ InBox m₁ j y0 R x := by
  unfold InBox
  refine forall_congr' fun μ => ?_
  obtain ⟨ex, hx⟩ := val_add_split (x μ) (t μ)
  obtain ⟨ey, hy⟩ := val_add_split (y0 μ) (t μ)
  simp only [Pi.add_apply]
  have hxR : (((x μ + t μ).val : ℕ) : ℝ) = ((x μ).val : ℝ) + ((t μ).val : ℝ) -
      (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) * ex := by
    have := congrArg (fun z : ℕ => (z : ℝ)) hx
    push_cast at this ⊢
    linarith
  have hyR : (((y0 μ + t μ).val : ℕ) : ℝ) = ((y0 μ).val : ℝ) + ((t μ).val : ℝ) -
      (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) * ey := by
    have := congrArg (fun z : ℕ => (z : ℝ)) hy
    push_cast at this ⊢
    linarith
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p - ex + ey, ?_⟩
    convert hp using 2
    rw [hxR, hyR]; push_cast; ring
  · rintro ⟨p, hp⟩
    refine ⟨p + ex - ey, ?_⟩
    convert hp using 2
    rw [hxR, hyR]; push_cast; ring

omit [NeZero N₁] [NeZero L] in
theorem dvd_side {j : ℕ} (hj : j ≤ K) : L ^ (j + m₁) ∣ (N₁ * L ^ m₁) * L ^ K := by
  refine (pow_dvd_pow L (by omega : j + m₁ ≤ m₁ + K)).trans ?_
  rw [pow_add]
  exact mul_dvd_mul_right (dvd_mul_left _ _) _

omit [NeZero N₁] [NeZero L] in
theorem dvd_side' {j : ℕ} (hj : j ≤ K) : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K :=
  (pow_dvd_pow L (by omega : j ≤ j + m₁)).trans (dvd_side hj)

theorem cubeBase_add_iff {j : ℕ} (hj : j ≤ K) (y t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (j + m₁) ∣ (t μ).val) : CubeBase m₁ j (y + t) ↔ CubeBase m₁ j y := by
  unfold CubeBase
  exact forall_congr' fun μ => mod_zero_add_iff (dvd_side hj) (y μ) (t μ) (ht μ)

theorem isBase_add_iff {j : ℕ} (hj : j ≤ K) (y t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ j ∣ (t μ).val) : IsBase j (y + t) ↔ IsBase j y := by
  unfold IsBase
  exact forall_congr' fun μ => mod_zero_add_iff (dvd_side' hj) (y μ) (t μ) (ht μ)

end Cube

/-! ### Level sets -/

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n : ℕ}

/-- For a level set the sets `Ω_i` are the whole torus for `i ≤ n` and empty above. -/
theorem level_mem_Ω (hG : IsLevel G n) {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ K + 1)
    (x : CTorus d L N₁ m₁ K) : x ∈ G.Ω i ↔ i ≤ n := by
  obtain ⟨hn1, hnk⟩ := hG.bounds
  have hxl := hG.mem_layer x
  rw [GeneratingSet.mem_layer] at hxl
  constructor
  · intro hx
    by_contra hlt
    exact hxl.2 (G.Ω_antitone (by omega) (by omega) hk hx)
  · intro hi
    exact G.Ω_antitone h1 hi (by omega) hxl.1

theorem fst_eq_of_mem_cubeIdx (hG : IsLevel G n) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : q.1 = n := by
  obtain ⟨⟨h1, hk⟩, hl, -⟩ := (mem_cubeIdx G).1 hq
  have := G.layerIndex_eq h1 hk hl
  rw [(hG q.2).2] at this
  exact this.symm

theorem fst_eq_of_mem_blockIdx (hG : IsLevel G n) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ blockIdx G) : q.1 = n := by
  obtain ⟨⟨h1, hk⟩, hl, -⟩ := (mem_blockIdx G).1 hq
  have := G.layerIndex_eq h1 hk hl
  rw [(hG q.2).2] at this
  exact this.symm

/-- **(T1) Translation by a vector divisible by `L ^ n` is a lattice symmetry of a level set.** -/
def LatSymm.ofTranslateLevel (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ n ∣ (t μ).val) : LatSymm G G (Equiv.addRight t) :=
  LatSymm.ofTranslate n t ht
    (fun i h1 hk x => by rw [level_mem_Ω hG h1 hk (x + t), level_mem_Ω hG h1 hk x])
    (fun n' h1 hk hne => by
      obtain ⟨x, hx⟩ := hne
      have := G.layerIndex_eq h1 hk hx
      rw [(hG x).2] at this
      exact this.ge)

/-- The action `(j, y₀) ↦ (j, y₀ + t)` on the centres. -/
def translateCentres (t : CTorus d L N₁ m₁ K) : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K) :=
  Equiv.prodCongr (Equiv.refl ℕ) (Equiv.addRight t)

omit [NeZero N₁] [NeZero L] in
@[simp] theorem translateCentres_apply (t : CTorus d L N₁ m₁ K) (q : ℕ × CTorus d L N₁ m₁ K) :
    translateCentres t q = (q.1, q.2 + t) := rfl

/-- Membership in the cube index set is preserved by `(j, y₀) ↦ (j, y₀ + t)`. -/
theorem translate_mem_cubeIdx_iff (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + m₁) ∣ (t μ).val) (q : ℕ × CTorus d L N₁ m₁ K) :
    translateCentres t q ∈ cubeIdx G ↔ q ∈ cubeIdx G := by
  have S := LatSymm.ofTranslateLevel hG t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ))
  simp only [mem_cubeIdx, translateCentres_apply]
  constructor
  · rintro ⟨hr, hl, hb⟩
    have hl' : q.2 ∈ G.layer q.1 := (S.mem_layer hr.1 hr.2 q.2).1 hl
    have hq : q.1 = n := by
      have := G.layerIndex_eq hr.1 hr.2 hl'
      rw [(hG q.2).2] at this; exact this.symm
    subst hq
    exact ⟨hr, hl', (cubeBase_add_iff hr.2 q.2 t ht).1 hb⟩
  · rintro ⟨hr, hl, hb⟩
    have hq : q.1 = n := by
      have := G.layerIndex_eq hr.1 hr.2 hl
      rw [(hG q.2).2] at this; exact this.symm
    subst hq
    exact ⟨hr, (S.mem_layer hr.1 hr.2 q.2).2 hl, (cubeBase_add_iff hr.2 q.2 t ht).2 hb⟩

/-- Membership in the block index set is preserved by `(j, y₀) ↦ (j, y₀ + t)`. -/
theorem translate_mem_blockIdx_iff (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ n ∣ (t μ).val) (q : ℕ × CTorus d L N₁ m₁ K) :
    translateCentres t q ∈ blockIdx G ↔ q ∈ blockIdx G := by
  have S := LatSymm.ofTranslateLevel hG t ht
  simp only [mem_blockIdx, translateCentres_apply]
  constructor
  · rintro ⟨hr, hl, hb⟩
    have hl' : q.2 ∈ G.layer q.1 := (S.mem_layer hr.1 hr.2 q.2).1 hl
    have hq : q.1 = n := by
      have := G.layerIndex_eq hr.1 hr.2 hl'
      rw [(hG q.2).2] at this; exact this.symm
    subst hq
    exact ⟨hr, hl', (isBase_add_iff hr.2 q.2 t ht).1 hb⟩
  · rintro ⟨hr, hl, hb⟩
    have hq : q.1 = n := by
      have := G.layerIndex_eq hr.1 hr.2 hl
      rw [(hG q.2).2] at this; exact this.symm
    subst hq
    exact ⟨hr, (S.mem_layer hr.1 hr.2 q.2).2 hl, (isBase_add_iff hr.2 q.2 t ht).2 hb⟩

/-- **(T3) Translation by a vector divisible by `L ^ n` is compatible with the blocks of the
interpolation of a level set.** -/
def BlockSymm.ofTranslate (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ n ∣ (t μ).val) : BlockSymm G (Equiv.addRight t) where
  τ := translateCentres t
  idx := translate_mem_blockIdx_iff hG t ht
  layer := fun _ => rfl
  bump := fun q x => bump_translate q.1 q.2 x t
  base := fun q _ => by
    show jBlock d L (N₁ * L ^ m₁) K q.1 ((Equiv.addRight t).symm ((Equiv.addRight t) q.2)) = _
    rw [Equiv.symm_apply_apply]

theorem coverDenom_translate (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + m₁) ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    coverDenom G (x + t) = coverDenom G x := by
  unfold coverDenom
  refine (Finset.sum_equiv (translateCentres t)
    (fun q => (translate_mem_cubeIdx_iff hG t ht q).symm) fun q _ => ?_).symm
  exact (cubeBump_translate q.1 q.2 x t).symm

/-- **(T2) Translation by a vector divisible by `L ^ (n + m₁)` is compatible with the cover of a
level set.** -/
def CoverSymm.ofTranslate (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + m₁) ∣ (t μ).val) : CoverSymm (coverOf G) (Equiv.addRight t) where
  τ := translateCentres t
  idx := translate_mem_cubeIdx_iff hG t ht
  chi := fun q x => by
    show Balaban.Localization.chi G (q.1, q.2 + t) (x + t) = Balaban.Localization.chi G q x
    unfold Balaban.Localization.chi
    rw [coverDenom_translate hG t ht]
    exact congrArg (· / coverDenom G x) (cubeBump_translate q.1 q.2 x t)
  box := fun q x => by
    show x + t ∈ intBox (q.1, q.2 + t) ↔ x ∈ intBox q
    rw [mem_intBox, mem_intBox]
    exact inBox_add_iff q.1 q.2 x t _
  qset := fun q q' => by
    have hidx := translate_mem_cubeIdx_iff hG t ht q'
    show (q'.1, q'.2 + t) ∈ (coverOf G).Qset (q.1, q.2 + t) ↔ q' ∈ (coverOf G).Qset q
    rw [DecCover.mem_Qset, DecCover.mem_Qset]
    have hid : (coverOf G).cubeIdx = cubeIdx G := rfl
    rw [hid]
    constructor
    · rintro ⟨h1, y, hy1, hy2⟩
      have h1' : q' ∈ cubeIdx G := hidx.1 h1
      have hq : q'.1 = n := fst_eq_of_mem_cubeIdx hG h1'
      have hq1 : q'.1 ≤ K := ((mem_cubeIdx G).1 h1').1.2
      refine ⟨h1', y - t, ?_, ?_⟩
      · refine (sameCell_add_iff (dvd_side hq1) (y - t) q'.2 t (fun μ => ?_)).1 ?_
        · rw [hq]; exact ht μ
        · simpa only [sub_add_cancel] using hy1
      · refine (inBox_add_iff q.1 q.2 (y - t) t _).1 ?_
        simpa only [sub_add_cancel] using hy2
    · rintro ⟨h1, y, hy1, hy2⟩
      have hq : q'.1 = n := fst_eq_of_mem_cubeIdx hG h1
      have hq1 : q'.1 ≤ K := ((mem_cubeIdx G).1 h1).1.2
      refine ⟨hidx.2 h1, y + t, ?_, (inBox_add_iff q.1 q.2 y t _).2 hy2⟩
      refine (sameCell_add_iff (dvd_side hq1) y q'.2 t (fun μ => ?_)).2 hy1
      rw [hq]; exact ht μ

/-- The parameter cubes `P(q)` are translated: `x + t ∈ P(j, y₀ + t) ↔ x ∈ P(j, y₀)` when
`j ≤ K` and `L ^ (j + m₁) ∣ t_μ` (the `pset` field of `PolymerSymm` for the centres of layer `j`). -/
theorem Pset_translate {j : ℕ} (hj : j ≤ K) (y t x : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (j + m₁) ∣ (t μ).val) :
    x + t ∈ Pset m₁ (j, y + t) ↔ x ∈ Pset m₁ (j, y) :=
  sameCell_add_iff (dvd_side hj) x y t ht

end Level

end Balaban.Localization.DecEquiv
