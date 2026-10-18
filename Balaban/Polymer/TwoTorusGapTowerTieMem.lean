/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsEv

/-!
# The label domains of the observable activity under the recentring map (blocker 7)

The labels of the observable activity of the tower correspond to the domains
`𝒴 = ⋃_z polyDom (nbhd (blockSite z)) ∪ ⋃_s polyDom (nbhd s)` of the local covers of the blocks
and of the sites (`obsTiltLabels_local_fromTowerG_rho`).  Since a block site is a site, `𝒴` is the
set of the domains of the local covers of all sites (`mem_obsLabelDomains_iff`).

`mem_obsLabelDomains_recentred_iff` (`hmemV` of the gap-scale step for these labels): for a set `Z`
of the recentred box of radius `R`, `φ '' Z` (`φ x = bm (x + tA) - tB`) is a domain of the second
torus iff `Z` is a domain of the first.  A domain `Z` of the cover of `x` contains the region of
`x` (`nbhd_subset_of_mem_polyDom`); for the converse direction the site `x'` of the second torus
is `φ x₀` for a point `x₀ ∈ Z`, the region of `x₀` lies in the box of radius
`R + 2 ((L - 1) a_K + L a_K)` (`inBox_of_mem_nbhd`), its image is the region of `x'`
(`nbhdF_recentred`), and since `φ` is injective on that box the region of `x₀` lies in `Z`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv

section TieMem

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

omit [NeZero N₁'] in
/-- **The region of the local cover of a site of the box lies in a larger box.**  If `x + t` lies
in the box of radius `R`, every point `y` of the region `nbhd x` has `y + t` in the box of radius
`R + 2 ((L - 1) a_K + L a_K)`. -/
theorem inBox_of_mem_nbhd {R : ℕ}
    (hn : 2 * (R + 2 * ((L - 1) * aK + L * aK)) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (t x y : CTorus d L N₁ m₁ (k + 1)) (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + t))
    (hy : y ∈ LocalCover.nbhd m₀ x) :
    InBox d (R + 2 * ((L - 1) * aK + L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + t) := by
  have hxx : x ∈ LocalCover.nbhd m₀ x := by
    have := LocalCover.mem_nbhdF_self m₀ x
    rwa [← Finset.mem_coe, LocalCover.coe_nbhdF] at this
  unfold LocalCover.nbhd cellNbhd at hxx hy
  have hx' := (mem_box_add_iff _ t x _).2 hxx
  have hy' := (mem_box_add_iff _ t y _).2 hy
  have hb := inBox_of_mem_box_left (by omega) hx hx'
  have h := inBox_of_mem_box_right (by omega) hb hy'
  rwa [show R + ((L - 1) * aK + L * aK) + ((L - 1) * aK + L * aK) =
    R + 2 * ((L - 1) * aK + L * aK) by ring] at h

omit [NeZero N₁'] in
/-- **The label domains of the observable activity are the domains of the site covers.**  The union
of the domains of the local covers of the block sites and of the sites `(x, i)` (`0 < N`) is the
set of the domains of the local covers of all sites. -/
theorem mem_obsLabelDomains_iff {N : ℕ} (hN0 : 0 < N) (Z : Set (CTorus d L N₁ m₁ (k + 1))) :
    Z ∈ ((Finset.univ.biUnion fun z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z))) ∪
      (Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1))) ↔
    ∃ x : CTorus d L N₁ m₁ (k + 1),
      Z ∈ polyDom (GA) (LocalCover.nbhdF m₀ x) m₀ k (LocalCover.fam m₀ x) := by
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨z, hz⟩ | ⟨s, hs⟩)
    · exact ⟨_, hz⟩
    · exact ⟨_, hs⟩
  · rintro ⟨x, hx⟩
    exact Or.inr ⟨(x, ⟨0, hN0⟩), hx⟩

/-- **The label domains of the observable activity under the recentring map** (`hmemV`).  For a set
`Z` whose translate by `tA` lies in the box of radius `R`, `φ '' Z`, `φ x = bm (x + tA) - tB`, is a
label domain of the observable activity on the second torus iff `Z` is one on the first. -/
theorem mem_obsLabelDomains_recentred_iff {N : ℕ} (hN0 : 0 < N)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val) {R : ℕ}
    (hn : 2 * (R + 2 * ((L - 1) * aK + L * aK)) + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (R + 2 * ((L - 1) * aK + L * aK)) + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (Z : Set (CTorus d L N₁ m₁ (k + 1)))
    (hZ : ∀ x ∈ Z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    (fun x => bm (x + tA) - tB) '' Z ∈
        ((Finset.univ.biUnion fun z : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
          polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z))) ∪
        (Finset.univ.biUnion fun s : CTorus d L N₁' m₁ (k + 1) × Fin N =>
          polyDom (GB) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1))) ↔
      Z ∈ ((Finset.univ.biUnion fun z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
          polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z))) ∪
        (Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
          polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1))) := by
  have hLa : 0 < L * aK :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos (L := L) m₀ m₁ (k + 1))
  have hef : (L - 1) * aK ≤ L * aK := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  rw [mem_obsLabelDomains_iff hN0, mem_obsLabelDomains_iff hN0]
  constructor
  · rintro ⟨x', hx'⟩
    have hsub := nbhd_subset_of_mem_polyDom hN' x' hx'
    have hx'n : x' ∈ LocalCover.nbhd m₀ x' := by
      have := LocalCover.mem_nbhdF_self m₀ x'
      rwa [← Finset.mem_coe, LocalCover.coe_nbhdF] at this
    obtain ⟨x0, hx0, rfl⟩ := hsub hx'n
    have hR' : ∀ y ∈ LocalCover.nbhd m₀ x0,
        InBox d (R + 2 * ((L - 1) * aK + L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) :=
      fun y hy => inBox_of_mem_nbhd (by omega) tA x0 y (hZ x0 hx0) hy
    have hF := nbhdF_recentred (R := R + 2 * ((L - 1) * aK + L * aK)) hN hN' tA tB htA htB
      (by omega) x0 (bm (x0 + tA) - tB) (sub_add_cancel _ _) hR'
    have hnZ : LocalCover.nbhd m₀ x0 ⊆ Z := by
      intro y hy
      have hyF : y ∈ LocalCover.nbhdF m₀ x0 := by
        rwa [← Finset.mem_coe, LocalCover.coe_nbhdF]
      have h1 : bm (y + tA) - tB ∈ LocalCover.nbhd m₀ (bm (x0 + tA) - tB) := by
        rw [← LocalCover.coe_nbhdF, hF, Finset.coe_image]
        exact ⟨y, hyF, rfl⟩
      obtain ⟨w, hw, hwe⟩ := hsub h1
      have hwy : w + tA = y + tA :=
        boxMap_inj (hm' := by omega) (inBox_mono (by omega) (hZ w hw)) (hR' y hy)
          (sub_left_inj.1 hwe)
      rw [← add_right_cancel hwy]
      exact hw
    exact ⟨x0, (mem_polyDom_site_recentred_iff hGA hGB hN hN' tA tB htA htB (by omega)
      (by omega) x0 _ (sub_add_cancel _ _) (fun y hy => hZ y (hnZ hy)) hZ).1 hx'⟩
  · rintro ⟨x, hx⟩
    have hsub := nbhd_subset_of_mem_polyDom hN x hx
    exact ⟨bm (x + tA) - tB, (mem_polyDom_site_recentred_iff hGA hGB hN hN' tA tB htA htB
      (by omega) (by omega) x _ (sub_add_cancel _ _) (fun y hy => hZ y (hsub hy)) hZ).2 hx⟩

end TieMem

end Balaban.Polymer.TwoTorusStep
