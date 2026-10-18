/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetDetCrossTrace
import Mathlib.Tactic.Linarith

/-!
# The cross lemma for the activities of the determinant

P3 p. 78 for the determinant of the step: the activity `detActivityBg y Y` of a polymer `Y` is the
same for the step's level set `H` and for a local generating set `H'` whose top domain contains the
`8 M₁ L^{k+1}`-neighbourhood of the sites of `Y`, at two data of the charts agreeing there.

* `mixDiff_rootTraceBg_cross`: the mixed differences of the rooted trace with its background agree
  for cut sets with the same cubes, all deep in `R` (the cut points of the subsets correspond, with
  the same cubes and cardinalities; `rootTraceBg_cutPt_cross` at each of them);
* `detActivityBg_cross`: the activities agree (the cut sets with hull `Y` correspond: their cubes lie
  in the sites of `Y`, so they are cubes of both covers).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.LargeField Finset

/-! ### Cut sets with the same cubes -/

section Patches

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- A cut set has as many cubes as patches. -/
theorem card_patches (J : Finset (cubeIdx H)) : (patches J).card = J.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

open Classical in
/-- **The cut set of `H'` with the cubes of a cut set `I` of `H`**, inside a cut set `J'` with the
cubes of `J ⊇ I`, has the same cubes as `I`. -/
theorem patches_filter_of_subset {J I : Finset (cubeIdx H)} {J' : Finset (cubeIdx H')}
    (hJJ' : patches J = patches J') (hIJ : I ⊆ J) :
    patches (J'.filter fun P' : cubeIdx H' => P'.1 ∈ patches I) =
      patches I := by
  ext P
  rw [mem_patches, mem_patches]
  constructor
  · rintro ⟨h, hP⟩
    exact (mem_patches.1 (Finset.mem_filter.1 hP).2)
  · rintro ⟨h, hP⟩
    have hPJ' : P ∈ patches J' := hJJ' ▸ mem_patches.2 ⟨h, hIJ hP⟩
    obtain ⟨h', hP'⟩ := mem_patches.1 hPJ'
    exact ⟨h', Finset.mem_filter.2 ⟨hP', mem_patches.2 ⟨h, hP⟩⟩⟩

open Classical in
/-- The filter of a cut set by its own patches. -/
theorem filter_mem_patches_eq {J I : Finset (cubeIdx H)} (hIJ : I ⊆ J) :
    (J.filter fun P : cubeIdx H => P.1 ∈ patches I) = I := by
  ext P
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, hP⟩
    obtain ⟨_, hP'⟩ := mem_patches.1 hP
    exact hP'
  · intro hP
    exact ⟨hIJ hP, mem_patches.2 ⟨P.2, hP⟩⟩

end Patches

/-! ### The mixed differences and the activities -/

section Cross

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' ϱm ϱm' : ℝ} {m₀ : ℕ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ Kc' Cx' c₂' BG₂' δ₁' c₃ : ℝ}

variable (hlev : IsLevel H (k + 1)) {R : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hR : ∀ x ∈ R, x ∈ H'.Ω (k + 1))
  (hC : FlCore N H Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hC' : FlCore N H' Hm' a₁ ν c BG κ eps Kc' Cx' c₂' BG₂' δ₁')
  (hS3 : Dec2.DecSpecs d L (Dec2.selfKc d L) (Cchi d L) c₃ BG)
  (hM3 : c₃ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  {D : BgData H N} {D' : BgData H' N} (hD : XiCData H (compWeight L a₁) ν (k + 1) 1 eps D)
  (hD' : XiCData H' (compWeight L a₁) ν (k + 1) 1 eps D')
  (hdat : ∀ z ∈ R, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)

include hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hD hD' hdat

open Classical in
/-- **The mixed differences of the rooted traces of the step and of a local generating set agree**
for cut sets `J`, `J'` with the same cubes, all deep in `R ⊆ Ω_{k+1}(H')`, and a unit block lying in
`R`. -/
theorem mixDiff_rootTraceBg_cross {J : Finset (cubeIdx H)} {J' : Finset (cubeIdx H')}
    (hJJ' : patches J = patches J')
    (hdeep : ∀ P ∈ patches J, ∀ z, supDist z P.2 ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R)
    (y : unitPts H) (y' : unitPts H') (hyy : (y : UnitTorus d L N₁ m₁ k) = y')
    (hyR : ∀ x : CTorus d L N₁ m₁ (k + 1), unitBlock x = (y : UnitTorus d L N₁ m₁ k) → x ∈ R) :
    mixDiff J (rootTraceBg H (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ H) (unitP H) {y} D) =
      mixDiff J' (rootTraceBg H' (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ H') (unitP H')
        {y'} D') := by
  have hcard : J.card = J'.card := by rw [← card_patches, ← card_patches, hJJ']
  unfold mixDiff
  refine Finset.sum_nbij' (fun I => J'.filter fun P' : cubeIdx H' => P'.1 ∈ patches I)
    (fun I' => J.filter fun P : cubeIdx H => P.1 ∈ patches I')
    (fun I _ => Finset.mem_powerset.2 (Finset.filter_subset _ _))
    (fun I' _ => Finset.mem_powerset.2 (Finset.filter_subset _ _))
    (fun I hI => ?_) (fun I' hI' => ?_) (fun I hI => ?_)
  · have hIJ := Finset.mem_powerset.1 hI
    rw [patches_filter_of_subset hJJ' hIJ, filter_mem_patches_eq hIJ]
  · have hIJ' := Finset.mem_powerset.1 hI'
    rw [patches_filter_of_subset hJJ'.symm hIJ', filter_mem_patches_eq hIJ']
  · have hIJ := Finset.mem_powerset.1 hI
    have hpat := (patches_filter_of_subset hJJ' hIJ).symm
    have hcI : I.card = (J'.filter fun P' : cubeIdx H' => P'.1 ∈ patches I).card := by
      rw [← card_patches, ← card_patches (J := J'.filter _), ← hpat]
    have hF := rootTraceBg_cutPt_cross hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hpat
      (fun P hP => hdeep P (by
        obtain ⟨h, hP'⟩ := mem_patches.1 hP
        exact mem_patches.2 ⟨h, hIJ hP'⟩)) hD hD' hdat y y' hyy hyR
    rw [hcard, hcI, hF]

omit hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hD hD' hdat in
/-- The cubes of a cut set lie in the sites of its hull. -/
theorem base_mem_sitesOf_hull (hN : L ^ m₀ ∣ N₁) {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (y : unitPts G) {J : Finset (cubeIdx G)} {P : cubeIdx G} (hP : P ∈ J) :
    (P : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ sitesOf (hullOf m₀ (rootIdxOf y) (patches J)) := by
  have hbase : (P : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) :=
    mem_cubeP.2 (SameCell.refl _ _)
  exact subset_sitesOf_piHull hN (hullSet m₀ (rootIdxOf y) (patches J))
    (Or.inr (Set.mem_iUnion₂.2 ⟨P.1, mem_patches.2 ⟨P.2, hP⟩, mem_Pset_iff.2 hbase⟩))

omit hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hD hD' hdat in
/-- The sites of the root block lie in the sites of every hull. -/
theorem root_mem_sitesOf_hull (hN : L ^ m₀ ∣ N₁) {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (y : unitPts G) (J : Finset (cubeIdx G)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : unitBlock x = (y : UnitTorus d L N₁ m₁ k)) :
    x ∈ sitesOf (hullOf m₀ (rootIdxOf y) (patches J)) := by
  refine subset_sitesOf_piHull hN (hullSet m₀ (rootIdxOf y) (patches J)) (Or.inl ?_)
  rw [rootIdxOf_eq hx]
  exact mem_rootSet_blockIndex x

omit hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hD hD' hdat in
/-- Unit blocks of two generating sets with the same value have the same root index. -/
theorem rootIdxOf_cross {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
    {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (y : unitPts G) (y' : unitPts G')
    (hyy : (y : UnitTorus d L N₁ m₁ k) = y') : rootIdxOf y = rootIdxOf y' := by
  obtain ⟨x, -, hx⟩ := (mem_unitPts G).1 y.2
  rw [rootIdxOf_eq hx, rootIdxOf_eq (hx.trans hyy)]

open Classical in
/-- **The activities of the determinant of the step and of a local generating set agree** for a
polymer `Y` whose sites are deep in `R ⊆ Ω_{k+1}(H')` (P3 p. 78 for the determinant). -/
theorem detActivityBg_cross (hN : L ^ m₀ ∣ N₁) (y : unitPts H) (y' : unitPts H')
    (hyy : (y : UnitTorus d L N₁ m₁ k) = y')
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hYdeep : ∀ x ∈ sitesOf Y, ∀ z, supDist z x ≤ 8 * L ^ (k + 1 + m₁) → z ∈ R) :
    detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' y' Y := by
  have hroot := rootIdxOf_cross y y' hyy
  have hRmem : ∀ x ∈ sitesOf Y, x ∈ R := fun x hx =>
    hYdeep x hx x (by rw [supDist_self]; exact Nat.zero_le _)
  -- a cube of a cut set with hull `Y` is a cube of both covers
  have hcube : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)), P.2 ∈ sitesOf Y →
      (P ∈ cubeIdx H ↔ P ∈ cubeIdx H') := fun P hP =>
    mem_cubeIdx_iff_of_top hlev (hR _ (hRmem _ hP))
  have hJ' : ∀ J : Finset (cubeIdx H), hullOf m₀ (rootIdxOf y) (patches J) = Y →
      patches J = patches (Finset.univ.filter fun P' : cubeIdx H' => P'.1 ∈ patches J) := by
    intro J hJY
    ext P
    rw [mem_patches, mem_patches]
    constructor
    · rintro ⟨h, hP⟩
      have hP2 : P.2 ∈ sitesOf Y := hJY ▸ base_mem_sitesOf_hull hN y (P := ⟨P, h⟩) hP
      exact ⟨(hcube P hP2).1 h, Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_patches.2 ⟨h, hP⟩⟩⟩
    · rintro ⟨_, hP⟩
      exact mem_patches.1 (Finset.mem_filter.1 hP).2
  have hJ : ∀ J' : Finset (cubeIdx H'), hullOf m₀ (rootIdxOf y') (patches J') = Y →
      patches J' = patches (Finset.univ.filter fun P : cubeIdx H => P.1 ∈ patches J') := by
    intro J' hJY
    ext P
    rw [mem_patches, mem_patches]
    constructor
    · rintro ⟨h, hP⟩
      have hP2 : P.2 ∈ sitesOf Y := hJY ▸ base_mem_sitesOf_hull hN y' (P := ⟨P, h⟩) hP
      exact ⟨(hcube P hP2).2 h, Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_patches.2 ⟨h, hP⟩⟩⟩
    · rintro ⟨_, hP⟩
      exact mem_patches.1 (Finset.mem_filter.1 hP).2
  unfold detActivityBg
  refine Finset.sum_nbij' (fun J => Finset.univ.filter fun P' : cubeIdx H' => P'.1 ∈ patches J)
    (fun J' => Finset.univ.filter fun P : cubeIdx H => P.1 ∈ patches J')
    (fun J hJ0 => ?_) (fun J' hJ0' => ?_) (fun J hJ0 => ?_) (fun J' hJ0' => ?_) (fun J hJ0 => ?_)
  · have hJY := (Finset.mem_filter.1 hJ0).2
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    rw [← hJ' J hJY, ← hroot]
    exact hJY
  · have hJY := (Finset.mem_filter.1 hJ0').2
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    rw [← hJ J' hJY, hroot]
    exact hJY
  · have hJY := (Finset.mem_filter.1 hJ0).2
    rw [← hJ' J hJY]
    exact filter_mem_patches_eq (Finset.subset_univ J)
  · have hJY := (Finset.mem_filter.1 hJ0').2
    rw [← hJ J' hJY]
    exact filter_mem_patches_eq (Finset.subset_univ J')
  · have hJY := (Finset.mem_filter.1 hJ0).2
    refine mixDiff_rootTraceBg_cross hlev hR hC hC' hS3 hM3 hk hδc hcap hsm hmar hα hD hD' hdat
      (hJ' J hJY) (fun P hP z hz => ?_) y y' hyy (fun x hx => ?_)
    · obtain ⟨h, hP'⟩ := mem_patches.1 hP
      exact hYdeep _ (hJY ▸ base_mem_sitesOf_hull hN y (P := ⟨P, h⟩) hP') z hz
    · exact hRmem x (hJY ▸ root_mem_sitesOf_hull hN y J hx)

end Cross

end Balaban.Fluctuation
