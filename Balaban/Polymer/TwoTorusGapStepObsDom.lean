/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepDetFamily
public import Balaban.Polymer.TwoTorusGapObsRecentreCoef

/-!
# The domain families of the observable under translation and recentring (item 24, blocker 7)

`polyDom_translate`: the domains `polyDom` of a cover are translated with the cover under an aligned
translation; `nbhdF_translate`, `fam_translate`: the local cover of a site is translated with the
site.  `mem_polyDom_site_recentred_iff`: the recentred form of `mem_polyDom_site_boxMap_iff`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv

section Trans

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ j : ℕ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The domains of a cover are translated with the cover.** -/
theorem polyDom_translate (hGp : IsLevel Gp K) (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val)
    {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hcov : CovSetup Gp m₀ j X 𝒦X)
    {X₁f X₁f' : Finset (CTorus d L N₁ m₁ K)}
    (hX : (↑X₁f' : Set (CTorus d L N₁ m₁ K)) = (Equiv.addRight t) '' (↑X₁f : Set _))
    (Y : Set (CTorus d L N₁ m₁ K)) :
    (Equiv.addRight t) '' Y ∈ polyDom Gp X₁f' m₀ j ((Equiv.addRight t) '' 𝒦X) ↔
      Y ∈ polyDom Gp X₁f m₀ j 𝒦X := by
  let S := LatSymm.ofTranslateLevel hGp t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ))
  let CS := CoverSymm.ofTranslate hGp t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ))
  let PS := PolymerSymm.ofTranslate hGp hN t ht
  unfold polyDom
  rw [mem_polymerDomains_iff_nonempty, mem_polymerDomains_iff_nonempty,
    X1_translate S ht hcov]
  have h := connFams_relabel (G := Gp) (m₀ := m₀)
    (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
    (fun i : ParIdx Gp (↑X₁f' : Set (CTorus d L N₁ m₁ K)) => i.1.1) (parEquiv CS PS hX)
    (fun _ => rfl) (fun i => i.1.2) PS S (X1 Gp m₀ j 𝒦X) Y
  rw [h]
  simp only [Finset.map_nonempty]

/-- The corner of the cell of a translated site is the translated corner. -/
theorem corner_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    LocalCover.corner m₀ (x + t) = LocalCover.corner m₀ x + t :=
  cbase_add_translate (cellSide_dvd hN (le_refl K)) x t (cellSide_dvd_translate (le_refl K) ht)

/-- **The region `X₁` of a translated site is the translated region.** -/
theorem nbhd_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    LocalCover.nbhd m₀ (x + t) = (Equiv.addRight t) '' LocalCover.nbhd m₀ x := by
  unfold LocalCover.nbhd cellNbhd
  rw [corner_translate hN t ht, image_box_translate]
  congr 1
  abel

theorem nbhdF_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    (↑(LocalCover.nbhdF m₀ (x + t)) : Set (CTorus d L N₁ m₁ K)) =
      (Equiv.addRight t) '' (↑(LocalCover.nbhdF m₀ x) : Set (CTorus d L N₁ m₁ K)) := by
  rw [LocalCover.coe_nbhdF, LocalCover.coe_nbhdF, nbhd_translate hN t ht]

theorem fam_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    LocalCover.fam m₀ (x + t) = (Equiv.addRight t) '' LocalCover.fam m₀ x := by
  unfold LocalCover.fam
  rw [corner_translate hN t ht, Set.image_singleton]
  rfl

end Trans

section Rec

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ R : ℕ}

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

/-- **The domains of the local cover in recentred form.**  Let `xs`, `xs'` be sites with
`xs' + tB = bm (xs + tA)`, the translated region of `xs` and the translated domain `Y` lie in the box
of radius `R`.  Then `φ '' Y`, `φ x = bm (x + tA) - tB`, is a domain of the local cover of `xs'` on the
second torus iff `Y` is a domain of the local cover of `xs` on the first. -/
theorem mem_polyDom_site_recentred_iff (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (xs : CTorus d L N₁ m₁ (k + 1)) (xs' : CTorus d L N₁' m₁ (k + 1))
    (hxs : xs' + tB = bm (xs + tA))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    (fun x => bm (x + tA) - tB) '' Y ∈
        polyDom (GB) (LocalCover.nbhdF m₀ xs') m₀ k (LocalCover.fam m₀ xs') ↔
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs) := by
  have hcovA := LocalCover.covSetup (m₀ := m₀) hGA hN (j := k) le_rfl xs
  have hcovB := LocalCover.covSetup (m₀ := m₀) hGB hN' (j := k) le_rfl xs'
  have e1 := polyDom_translate hGA hN tA htA hcovA
    (X₁f := LocalCover.nbhdF m₀ xs) (X₁f' := LocalCover.nbhdF m₀ (xs + tA))
    (nbhdF_translate hN tA htA xs) Y
  have e2 := polyDom_translate hGB hN' tB htB hcovB
    (X₁f := LocalCover.nbhdF m₀ xs') (X₁f' := LocalCover.nbhdF m₀ (xs' + tB))
    (nbhdF_translate hN' tB htB xs')
    ((fun x => bm (x + tA) - tB) '' Y)
  rw [← fam_translate hN tA htA] at e1
  rw [← fam_translate hN' tB htB, hxs] at e2
  have hbx : ∀ x ∈ LocalCover.nbhd m₀ (xs + tA), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rw [nbhd_translate hN tA htA]
    rintro _ ⟨x, hx, rfl⟩
    exact hX₁R x hx
  have hbY : ∀ y ∈ (Equiv.addRight tA) '' Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact hYR y hy
  have e3 := mem_polyDom_site_boxMap_iff (ϱ := ϱ) hN hN' hnF hnF' (xs + tA) hbx hbY
  have hset : (Equiv.addRight tB) '' ((fun x => bm (x + tA) - tB) '' Y) =
      bm '' ((Equiv.addRight tA) '' Y) := by
    rw [image_recentred, ← Set.image_comp]
    simp
  rw [← e1, ← e3, ← hset, ← e2]

end Rec

end Balaban.Polymer.TwoTorusStep
