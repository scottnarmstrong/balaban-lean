/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivReflect
public import Balaban.Localization.DecEquivTranslatePolymer

/-!
# Reflections are compatible with the polymers of a level set

For a level set `G` (`IsLevel G n`), the reflection `x_μ₀ ↦ c - 1 - x_μ₀` with the corner-corrected
action `reflectCover μ₀ c` on the centres satisfies the two fields of `PolymerSymm` when
* `L ^ (n + m₀ + m₁) ∣ c.val` (the cell side `a_n` divides `c`), and
* `L ^ m₀ ∣ N₁` (the cell side divides the side of the torus).

The key facts: the reflection maps the box of side `s` with base `b` onto the box with base
`b[μ₀ := c - s - b μ₀]` (`mem_box_refl_iff`), and it commutes with the base `cbase a` of the cells
(`cbase_refl`, `cbase_reflBase`).

Covariance of the output terms of a step as class terms is not proved here.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Boxes

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁] [NeZero L] in
theorem reflPerm_reflPerm (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (x : CTorus d L N₁ m₁ K) : reflPerm μ₀ c (reflPerm μ₀ c x) = x :=
  (reflPerm μ₀ c).symm_apply_apply x

omit [NeZero N₁] [NeZero L] in
theorem mem_box_refl {a : ℕ} (ha : 0 < a) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (b x : CTorus d L N₁ m₁ K) (hx : x ∈ box b a) :
    reflPerm μ₀ c x ∈ box (reflBase a μ₀ c b) a := by
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨fun μ => if μ = μ₀ then a - 1 - w μ else w μ, fun μ => ?_, ?_⟩
  · have := hw μ
    by_cases h : μ = μ₀ <;> simp [h] <;> omega
  · funext μ
    by_cases h : μ = μ₀
    · subst h
      have h1 : w μ ≤ a - 1 := by have := hw μ; omega
      simp only [reflPerm, reflBase, Equiv.coe_fn_mk, Function.update_self, Pi.add_apply, natT,
        ite_true]
      rw [Nat.cast_sub h1, Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]
      ring
    · simp [reflPerm, reflBase, natT, h]

omit [NeZero N₁] [NeZero L] in
theorem mem_box_refl_iff {a : ℕ} (ha : 0 < a) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (b x : CTorus d L N₁ m₁ K) :
    reflPerm μ₀ c x ∈ box (reflBase a μ₀ c b) a ↔ x ∈ box b a := by
  refine ⟨fun h => ?_, mem_box_refl ha μ₀ c b x⟩
  have := mem_box_refl ha μ₀ c _ _ h
  rwa [reflPerm_reflPerm, reflBase_reflBase] at this

theorem aligned_reflBase_iff {a t : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (hat : a ∣ t)
    (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : a ∣ c.val) (b : CTorus d L N₁ m₁ K) :
    Aligned a (reflBase t μ₀ c b) ↔ Aligned a b := by
  unfold Aligned
  refine forall_congr' fun μ => ?_
  by_cases h : μ = μ₀
  · subst h
    simp only [reflBase, Function.update_self, ← Nat.dvd_iff_mod_eq_zero]
    exact dvd_val_refl_iff' ha hat c (b μ) hc
  · simp [reflBase, h]

/-- The reflection commutes with the base of the cells: `cbase a (σ z) = b[μ₀ := c - a - b μ₀]`
where `b = cbase a z`. -/
theorem cbase_refl {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : a ∣ c.val) (z : CTorus d L N₁ m₁ K) :
    cbase a (reflPerm μ₀ c z) = reflBase a μ₀ c (cbase a z) := by
  refine cbase_eq_of_mem_box ha ?_ ?_
  · exact (aligned_reflBase_iff ha dvd_rfl μ₀ c hc _).2 (aligned_cbase z)
  · exact mem_box_refl ha0 μ₀ c _ _ (mem_box_cbase ha0 z)

omit [NeZero N₁] [NeZero L] in
theorem reflBase_eq_refl {s : ℕ} (hs0 : 0 < s) (μ₀ : Fin d) (c : ZMod ((N₁ * L ^ m₁) * L ^ K))
    (y : CTorus d L N₁ m₁ K) :
    reflBase s μ₀ c y = reflPerm μ₀ c
      (Function.update y μ₀ (y μ₀ + ((s - 1 : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)))) := by
  funext μ
  by_cases h : μ = μ₀
  · subst h
    simp only [reflBase, reflPerm, Equiv.coe_fn_mk, Function.update_self]
    rw [Nat.cast_sub hs0, Nat.cast_one]; ring
  · simp [reflBase, reflPerm, h]

/-- The base of the cell of the opposite corner of a cube of side `s ∣ a`. -/
theorem cbase_reflBase {s a : ℕ} (hs : s ∣ (N₁ * L ^ m₁) * L ^ K) (hsa : s ∣ a)
    (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (hs0 : 0 < s) (ha0 : 0 < a) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : a ∣ c.val) (y : CTorus d L N₁ m₁ K)
    (hy : ∀ μ, s ∣ (y μ).val) :
    cbase a (reflBase s μ₀ c y) = reflBase a μ₀ c (cbase a y) := by
  rw [reflBase_eq_refl hs0, cbase_refl ha ha0 μ₀ c hc]
  congr 1
  funext μ
  by_cases h : μ = μ₀
  · subst h
    simp only [cbase, Function.update_self]
    rw [val_add_pred_div' hs hsa hs0 _ (hy μ)]
  · simp [cbase, h]

theorem mem_cellOf_iff {a : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    (b x : CTorus d L N₁ m₁ K) : x ∈ box (cbase a b) a ↔ cbase a x = cbase a b := by
  constructor
  · intro h; exact cbase_eq_of_mem_box ha (aligned_cbase b) h
  · intro h; rw [← h]; exact mem_box_cbase ha0 x

end Boxes

section Level

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {n m₀ : ℕ}

theorem cellOf_refl (hn : n ≤ K) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (n + m₀ + m₁) ∣ c.val)
    (y : CTorus d L N₁ m₁ K) (hy : CubeBase m₁ n y) (x : CTorus d L N₁ m₁ K) :
    reflPerm μ₀ c x ∈ cellOf L m₀ m₁ (n, reflBase (L ^ (n + m₁)) μ₀ c y) ↔
      x ∈ cellOf L m₀ m₁ (n, y) := by
  have hd : cellSide L m₀ m₁ n ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hn
  have hsa : L ^ (n + m₁) ∣ cellSide L m₀ m₁ n := (pow_dvd_pow L (by omega) : L ^ (n + m₁) ∣ L ^ (n + m₀ + m₁))
  have hpos : 0 < cellSide L m₀ m₁ n := cellSide_pos m₀ m₁ n
  have hspos : 0 < L ^ (n + m₁) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  unfold cellOf
  simp only
  rw [mem_cellOf_iff hd hpos, mem_cellOf_iff hd hpos, cbase_refl hd hpos μ₀ c hc,
    cbase_reflBase (dvd_side hn) hsa hd hspos hpos μ₀ c hc y
      (fun μ => Nat.dvd_of_mod_eq_zero (hy μ))]
  constructor
  · intro h
    have := congrArg (reflBase (cellSide L m₀ m₁ n) μ₀ c) h
    rwa [reflBase_reflBase, reflBase_reflBase] at this
  · intro h; rw [h]

theorem dcubes_refl (hG : IsLevel G n) (hn : n ≤ K) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (n + m₀ + m₁) ∣ c.val)
    (y : CTorus d L N₁ m₁ K) (hy : CubeBase m₁ n y) (b : CTorus d L N₁ m₁ K) :
    b ∈ Dcubes G m₀ (n, reflBase (L ^ (n + m₁)) μ₀ c y) ↔
      reflBase (L * cellSide L m₀ m₁ n) μ₀ c b ∈ Dcubes G m₀ (n, y) := by
  have hd : cellSide L m₀ m₁ n ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN hn
  have hpos : 0 < L * cellSide L m₀ m₁ n :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ n)
  have hc' : cellSide L m₀ m₁ n ∣ c.val := hc
  have hdLa : cellSide L m₀ m₁ n ∣ L * cellSide L m₀ m₁ n := dvd_mul_left _ _
  have key : ∀ z, reflPerm μ₀ c z ∈ box b (L * cellSide L m₀ m₁ n) ↔
      z ∈ box (reflBase (L * cellSide L m₀ m₁ n) μ₀ c b) (L * cellSide L m₀ m₁ n) := fun z => by
    have := mem_box_refl_iff hpos μ₀ c (reflBase (L * cellSide L m₀ m₁ n) μ₀ c b) z
    rwa [reflBase_reflBase] at this
  unfold Dcubes
  simp only [Set.mem_ofPred_eq]
  refine and_congr (aligned_reflBase_iff hd hdLa μ₀ c hc' b).symm (and_congr ?_ ?_)
  · constructor
    · intro h x hx
      exact (key x).1 (h ((cellOf_refl hn hN μ₀ c hc y hy x).2 hx))
    · intro h z hz
      have hz' := (cellOf_refl hn hN μ₀ c hc y hy (reflPerm μ₀ c z)).1
        (by rwa [reflPerm_reflPerm])
      have := (key (reflPerm μ₀ c z)).2 (h hz')
      rwa [reflPerm_reflPerm] at this
  · exact ⟨fun _ x hx => (hG.mem_layer x), fun _ x hx => (hG.mem_layer x)⟩

/-- **The sets `D(P)` are reflected** by a reflection of a level set. -/
theorem Dsites_refl (hG : IsLevel G n) (hn : n ≤ K) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (n + m₀ + m₁) ∣ c.val)
    (y : CTorus d L N₁ m₁ K) (hy : CubeBase m₁ n y) :
    Dsites G m₀ (n, reflBase (L ^ (n + m₁)) μ₀ c y) = (reflPerm μ₀ c) '' Dsites G m₀ (n, y) := by
  have hpos : 0 < L * cellSide L m₀ m₁ n :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ n)
  ext z
  obtain ⟨x, rfl⟩ : ∃ x, z = reflPerm μ₀ c x := ⟨reflPerm μ₀ c z, (reflPerm_reflPerm μ₀ c z).symm⟩
  rw [(reflPerm μ₀ c).injective.mem_set_image]
  unfold Dsites
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨b, hb, hx⟩
    refine ⟨reflBase (L * cellSide L m₀ m₁ n) μ₀ c b, (dcubes_refl hG hn hN μ₀ c hc y hy b).1 hb, ?_⟩
    have := mem_box_refl_iff hpos μ₀ c (reflBase (L * cellSide L m₀ m₁ n) μ₀ c b) x
    rw [reflBase_reflBase] at this
    exact this.1 hx
  · rintro ⟨b, hb, hx⟩
    refine ⟨reflBase (L * cellSide L m₀ m₁ n) μ₀ c b, ?_, (mem_box_refl_iff hpos μ₀ c b x).2 hx⟩
    rw [dcubes_refl hG hn hN μ₀ c hc y hy, reflBase_reflBase]
    exact hb

/-- **(P3) Reflections are compatible with the polymers of a level set** when
`L ^ (n + m₀ + m₁) ∣ c.val` and `L ^ m₀ ∣ N₁`. -/
theorem PolymerSymm.ofReflect (hG : IsLevel G n) (hN : L ^ m₀ ∣ N₁) (μ₀ : Fin d)
    (c : ZMod ((N₁ * L ^ m₁) * L ^ K)) (hc : L ^ (n + m₀ + m₁) ∣ c.val) :
    PolymerSymm G m₀ (reflPerm μ₀ c) (reflectCover μ₀ c) where
  pset := fun q hq x => by
    have hqn : q.1 = n := fst_eq_of_mem_cubeIdx hG hq
    obtain ⟨hr, -, hb⟩ := (mem_cubeIdx G).1 hq
    have hcs : L ^ (q.1 + m₁) ∣ c.val := by
      rw [hqn]; exact (pow_dvd_pow L (by omega)).trans hc
    exact sameCell_refl_iff (dvd_side hr.2) (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L)))
      μ₀ c hcs x q.2 (fun μ => Nat.dvd_of_mod_eq_zero (hb μ))
  dsites := fun q hq => by
    have hqn : q.1 = n := fst_eq_of_mem_cubeIdx hG hq
    obtain ⟨hr, -, hb⟩ := (mem_cubeIdx G).1 hq
    obtain ⟨j, y⟩ := q
    simp only at hqn
    subst hqn
    exact Dsites_refl hG hr.2 hN μ₀ c hc y hb

end Level

end Balaban.Localization.DecEquiv
