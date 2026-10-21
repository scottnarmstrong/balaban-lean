/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseHull
import Mathlib.Tactic.Linarith

/-!
# The polymer hull of a set of sites on two tori

For two tori identified on a centred box (`boxMap`), the ℓ∞ neighbourhood `ballNbhd r`, the
parameter cubes `walkJ r` and the hull `hullOf m₀ z (walkJ r A)` of a set `A` of sites of the box
correspond: `ballNbhd r (bm '' A) = bm '' ballNbhd r A`, `walkJ r (bm '' A)` is the image of
`walkJ r A` under `Prod.map id bm`, and
`hullOf m₀ (blockIndex (bm x)) (walkJ r (bm '' A)) = cubeMap '' hullOf m₀ (blockIndex x) (walkJ r A)`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.Polymer Balaban.Fluctuation Balaban.Polymer.TwoTorusStep

section Box

variable {d n n' : ℕ} [NeZero n] [NeZero n']

omit [NeZero n] [NeZero n'] in
/-- The centred coordinate of a difference of two points of the box of radius `R` is the
difference of their centred coordinates (the torus is wider than `4 R`). -/
theorem valMinAbs_sub_of_inBox {R : ℕ} (hn : 2 * (2 * R) + 1 < n) {x y : Torus d n}
    (hx : InBox d R n x) (hy : InBox d R n y) (μ : Fin d) :
    ((x - y) μ).valMinAbs = (x μ).valMinAbs - (y μ).valMinAbs := by
  have hxy : ((x - y) μ) = (((x μ).valMinAbs - (y μ).valMinAbs : ℤ) : ZMod n) := by
    push_cast
    rfl
  rw [hxy]
  refine valMinAbs_intCast_of_abs_le (r := 2 * R) hn ?_
  have h1 := abs_le.1 (hx μ)
  have h2 := abs_le.1 (hy μ)
  rw [abs_le]; push_cast; constructor <;> omega

omit [NeZero n] [NeZero n'] in
/-- **The ℓ∞ distance is preserved by `boxMap`.** -/
theorem inBox_sub_boxMap_iff {R r : ℕ} (hn : 2 * (2 * R) + 1 < n) (hn' : 2 * (2 * R) + 1 < n')
    {x y : Torus d n} (hx : InBox d R n x) (hy : InBox d R n y) :
    InBox d r n (x - y) ↔ InBox d r n' (boxMap n n' x - boxMap n n' y) := by
  have hx' := inBox_boxMap (by omega : 2 * R + 1 < n') hx
  have hy' := inBox_boxMap (by omega : 2 * R + 1 < n') hy
  have key : ∀ μ, ((boxMap n n' x - boxMap n n' y) μ).valMinAbs = ((x - y) μ).valMinAbs := by
    intro μ
    rw [valMinAbs_sub_of_inBox hn' hx' hy', valMinAbs_sub_of_inBox hn hx hy,
      valMinAbs_boxMap (by omega) hx, valMinAbs_boxMap (by omega) hy]
  constructor
  · intro h μ; rw [key]; exact h μ
  · intro h μ; rw [← key]; exact h μ

omit [NeZero n] [NeZero n'] in
/-- A point within `r` of a point of the box of radius `ρ` lies in the box of radius `ρ + r`. -/
theorem inBox_of_inBox_sub {ρ r : ℕ} (hn : 2 * (ρ + r) + 1 < n) {a t : Torus d n}
    (ha : InBox d ρ n a) (h : InBox d r n (t - a)) : InBox d (ρ + r) n t := by
  intro μ
  have h1 := abs_le.1 (ha μ)
  have h2 := abs_le.1 (h μ)
  refine inBox_of_int hn _ (((t - a) μ).valMinAbs + (a μ).valMinAbs) ?_ ?_
  · push_cast
    exact sub_add_cancel (t μ) (a μ)
  · rw [abs_le]; push_cast; constructor <;> omega

end Box

section TwoTori

open scoped Classical

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))

/-- **The ℓ∞ neighbourhood on two tori**: for a set `A` in the box of radius `ρ`,
`ballNbhd r (bm '' A) = bm '' ballNbhd r A`. -/
theorem ballNbhd_image {ρ r : ℕ} (hn : 2 * (2 * (ρ + r)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (2 * (ρ + r)) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hA : ∀ a ∈ A, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) a) :
    ballNbhd r (A.image bm) = (ballNbhd r A).image bm := by
  ext t'
  rw [Finset.mem_image]
  constructor
  · intro ht'
    obtain ⟨a', ha', h⟩ := mem_ballNbhd.1 ht'
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.1 ha'
    have haB : InBox d ρ ((N₁' * L ^ m₁) * L ^ (k + 1)) (bm a) :=
      inBox_boxMap (by omega) (hA a haA)
    have ht'B : InBox d (ρ + r) ((N₁' * L ^ m₁) * L ^ (k + 1)) t' :=
      inBox_of_inBox_sub (by omega) haB h
    refine ⟨bm' t', mem_ballNbhd.2 ⟨a, haA, ?_⟩, boxMap_boxMap (by omega) ht'B⟩
    have key := (inBox_sub_boxMap_iff (R := ρ + r) (r := r) (n := (N₁' * L ^ m₁) * L ^ (k + 1))
      (n' := (N₁ * L ^ m₁) * L ^ (k + 1)) hn' hn ht'B (inBox_mono (by omega) haB)).1 h
    rwa [boxMap_boxMap (by omega) (hA a haA)] at key
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨a, haA, h⟩ := mem_ballNbhd.1 ht
    have htB := inBox_of_inBox_sub (by omega) (hA a haA) h
    exact mem_ballNbhd.2 ⟨bm a, Finset.mem_image_of_mem _ haA,
      (inBox_sub_boxMap_iff (R := ρ + r) hn hn' htB (inBox_mono (by omega) (hA a haA))).1 h⟩

set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)

/-- **The cells of side `L^{m₁}` of the neighbourhood, on two tori**:
`walkJ r (bm '' A) = Prod.map id bm '' walkJ r A`. -/
theorem walkJ_image {ρ r : ℕ} (hn : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hA : ∀ a ∈ A, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) a) :
    walkJ r (A.image bm) = (walkJ r A).image (Prod.map id bm) := by
  have hT : ∀ t ∈ ballNbhd r A, InBox d (ρ + r) ((N₁ * L ^ m₁) * L ^ (k + 1)) t := by
    intro t ht
    obtain ⟨a, ha, h⟩ := mem_ballNbhd.1 ht
    exact inBox_of_inBox_sub (by omega) (hA a ha) h
  unfold walkJ
  rw [ballNbhd_image (ρ := ρ) (r := r) (by omega) (by omega) A hA, Finset.image_image,
    Finset.image_image]
  refine Finset.image_congr fun y hy => ?_
  have hyR := hT y hy
  have ha0 : 0 < L ^ (0 + m₁) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdv : L ^ (0 + m₁) ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := pow_dvd_side (Nat.zero_le _) N₁
  have hdv' : L ^ (0 + m₁) ∣ (N₁' * L ^ m₁) * L ^ (k + 1) := pow_dvd_side (Nat.zero_le _) N₁'
  have hc := cbase_boxMap hdv hdv' ha0 (r := ρ + r + L ^ (0 + m₁)) (by omega) y
    (fun z hz => inBox_of_mem_cell (by omega) hyR hz)
  simp only [Function.comp, Prod.map]
  rw [hc]
  rfl

/-- **The hull set on two tori.**  For a set `A` of sites of the box of radius `ρ` and a site `x₀`
of `A`, the union of the root cell of `x₀` and of the patches of `walkJ r A` goes to the
corresponding set of the second torus. -/
theorem hullSet_walkJ_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {ρ r : ℕ}
    (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hA : ∀ a ∈ A, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) a)
    {x₀ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ A)
    (hM1 : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hM1' : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hM2 : 2 * (ρ + r + L ^ (0 + m₁)) + 5 * (L * cellSide L 0 m₁ 0) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hM3 : 2 * (ρ + aK) + aK < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    hullSet m₀ (blockIndex (bm x₀)) (walkJ r (A.image bm)) =
      bm '' hullSet m₀ (blockIndex x₀) (walkJ r A) := by
  have hT : ∀ t ∈ ballNbhd r A, InBox d (ρ + r) ((N₁ * L ^ m₁) * L ^ (k + 1)) t := by
    intro t ht
    obtain ⟨a, ha, h⟩ := mem_ballNbhd.1 ht
    exact inBox_of_inBox_sub (by omega) (hA a ha) h
  unfold hullSet
  rw [walkJ_image (ρ := ρ) (r := r) hM1 hM1' A hA, Set.image_union, Set.image_iUnion₂,
    Finset.set_biUnion_finset_image]
  congr 1
  · rw [rootSet_blockIndex, rootSet_blockIndex]
    exact (cell_image hN hN' hM3 x₀ fun y hy => inBox_of_mem_cell (by omega) (hA x₀ hx₀) hy).symm
  · refine Set.iUnion₂_congr fun P hP => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hP
    have hyR := hT y hy
    have hb : CubeBase (K := k + 1) m₁ 0 (cbase (L ^ (0 + m₁)) y) := fun μ => by
      rw [cbase_val]; exact Nat.mul_mod_right _ _
    have hbR : InBox d (ρ + r + L ^ (0 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1))
        (cbase (L ^ (0 + m₁)) y) :=
      inBox_of_mem_cell (by omega) hyR
        (mem_box_self _ (Nat.pos_of_ne_zero (NeZero.ne _)))
    exact (pset_image (m₀ := 0) (j := 0) (N₁' := N₁') (Nat.zero_le _) hM2 hbR hb).symm

/-- **The polymer hull of a set of sites on two tori.**  For a set `A` of sites of the box of
radius `ρ` and a site `x₀ ∈ A`, the hull of the root cell of `x₀` and of the patches of
`walkJ r A` goes to the hull of the corresponding objects of the second torus:
`hullOf (blockIndex (bm x₀)) (walkJ r (bm '' A)) = cubeMap '' hullOf (blockIndex x₀) (walkJ r A)`.
Margins: `4 R₁ + 1`, `2 R₁ + 5 L L^{m₁}` and `2 (ρ + a_K) + a_K` below `N₁ L^{m₁} L^{k+1}`, and
`2 (R₂ + 2 L a_K) + L a_K` below `N₁ L^{m₁} L^{k+1}` and `N₁' L^{m₁} L^{k+1}`, with
`R₁ = ρ + r + L^{m₁}`, `R₂ = R₁ + a_K`. -/
theorem walkHull_image (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {ρ r : ℕ}
    (A : Finset (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hA : ∀ a ∈ A, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) a)
    {x₀ : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ A)
    (hM1 : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hM1' : 2 * (2 * (ρ + r + L ^ (0 + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hM2 : 2 * (ρ + r + L ^ (0 + m₁)) + 5 * (L * cellSide L 0 m₁ 0) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hM3 : 2 * (ρ + aK) + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (ρ + r + L ^ (0 + m₁) + aK + 2 * (L * aK)) + L * aK <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (ρ + r + L ^ (0 + m₁) + aK + 2 * (L * aK)) + L * aK <
      (N₁' * L ^ m₁) * L ^ (k + 1)) :
    hullOf m₀ (blockIndex (bm x₀)) (walkJ r (A.image bm)) =
      (hullOf m₀ (blockIndex x₀) (walkJ r A)).image
        (Balaban.Polymer.TwoTorusStep.cubeMap hN hN' (le_refl (k + 1))) := by
  have hT : ∀ t ∈ ballNbhd r A, InBox d (ρ + r) ((N₁ * L ^ m₁) * L ^ (k + 1)) t := by
    intro t ht
    obtain ⟨a, ha, h⟩ := mem_ballNbhd.1 ht
    exact inBox_of_inBox_sub (by omega) (hA a ha) h
  unfold hullOf
  rw [hullSet_walkJ_image hN hN' A hA hx₀ hM1 hM1' hM2 hM3]
  refine piHull_boxMap hN hN' hnH hnH' ?_
  intro x hx
  rcases hx with hx | hx
  · rw [rootSet_blockIndex] at hx
    exact inBox_mono (by omega) (inBox_of_mem_cell (by omega) (hA x₀ hx₀) hx)
  · obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hP
    have hb : CubeBase (K := k + 1) m₁ 0 (cbase (L ^ (0 + m₁)) y) := fun μ => by
      rw [cbase_val]; exact Nat.mul_mod_right _ _
    rw [pset_eq_box (Nat.zero_le _) hb] at hxP
    exact inBox_mono (by omega) (inBox_of_mem_cell (by omega) (hT y hy) hxP)

end TwoTori





end Balaban.LargeField.Base
