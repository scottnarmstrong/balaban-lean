/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoCov
public import Balaban.Polymer.LocalIsoDecFix
public import Balaban.Polymer.TwoTorusDet
public import Balaban.Fluctuation.NewLevelCoeffBg
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the determinant part of the coefficient

For a generating set `G` of level `k + 1` and its image `H` under the box map (`OmegaIso G H ρ`),
the determinant activities `detActivityBg` of a unit point and of its image, at a polymer of the box
and its image under `cubeMap`, agree for data corresponding on the box of radius `ρ + 1`; so do the
determinant parts `newLevelDetBg` of the coefficient at corresponding masks.

* `decBgField_eq_dec2`, `decBgMult_eq_dec2`: the decoupled background field of the own cover is the
  field of `Dec2` for the pair `(coverOf G, G)` (`dec2_isDecBg_iff`);
* `mixDiff_map`: **the generic mixed difference** along an equivalence of the parameters;
* `OmegaIso.rootTraceBg_eq`: the rooted trace with its background;
* `OmegaIso.hullSet_image`, `OmegaIso.hullOf_image`: the hull of the root cube and of the patches
  of a set of parameter cubes (cubes of all levels of `G`);
* `OmegaIso.detActivityBg_eq`, `OmegaIso.newLevelDetBg_eq`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.Analysis Matrix

/-! ### The decoupled background field of the own cover -/

section Link

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem decBgField_eq_dec2 (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν ρb : ℝ)
    (s : DecParams G) (D : BgData G N) :
    decBgField G a ν ρb s D = Dec2.decBgField (coverOf G) G a ν ρb s D := by
  unfold decBgField Dec2.decBgField
  exact dite_existsUnique_equiv (P := fun p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) =>
      IsDecBg G a ν ρb s D p.1 p.2)
    (Q := fun p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => Dec2.IsDecBg (coverOf G) G a ν ρb s D p.1 p.2)
    (Equiv.refl _) (fun p => (dec2_isDecBg_iff' G a ν ρb s D p.1 p.2))
    (fun p => p.1) (fun p => p.1) (fun _ => rfl) 0
where
  dec2_isDecBg_iff' (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν ρb : ℝ)
      (s : DecParams G) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
      IsDecBg G a ν ρb s D φ α ↔ Dec2.IsDecBg (coverOf G) G a ν ρb s D φ α :=
    ⟨fun h => ⟨h.small, h.fixed, h.field⟩, fun h => ⟨h.small, h.fixed, h.field⟩⟩

theorem decBgMult_eq_dec2 (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν ρb : ℝ)
    (s : DecParams G) (D : BgData G N) :
    decBgMult G a ν ρb s D = Dec2.decBgMult (coverOf G) G a ν ρb s D := by
  unfold decBgMult Dec2.decBgMult
  exact dite_existsUnique_equiv (P := fun p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) =>
      IsDecBg G a ν ρb s D p.1 p.2)
    (Q := fun p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ) => Dec2.IsDecBg (coverOf G) G a ν ρb s D p.1 p.2)
    (Equiv.refl _) (fun p => (decBgField_eq_dec2.dec2_isDecBg_iff' G a ν ρb s D p.1 p.2))
    (fun p => p.2) (fun p => p.2) (fun _ => rfl) 0

end Link

/-! ### The generic mixed difference -/

section Mix

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

omit [Fintype ι] [Fintype ι'] in
/-- **The mixed difference along an equivalence of the parameters**: if `F'` at the cut point of
the image of `I` is `F` at the cut point of `I` for every `I ⊆ J`, the mixed differences agree. -/
theorem mixDiff_map (c : ι ≃ ι') (J : Finset ι) {F : (ι → ℂ) → ℂ} {F' : (ι' → ℂ) → ℂ}
    (hF : ∀ I ⊆ J, F' (cutPt (I.map c.toEmbedding)) = F (cutPt I)) :
    mixDiff (J.map c.toEmbedding) F' = mixDiff J F := by
  unfold mixDiff
  symm
  refine Finset.sum_bij (fun I _ => I.map c.toEmbedding)
    (fun I hI => Finset.mem_powerset.2 (Finset.map_subset_map.2 (Finset.mem_powerset.1 hI)))
    (fun I₁ _ I₂ _ h => Finset.map_injective _ h) (fun I' hI' => ?_) (fun I hI => ?_)
  · refine ⟨I'.map c.symm.toEmbedding, Finset.mem_powerset.2 ?_, ?_⟩
    · intro q hq
      obtain ⟨q', hq', rfl⟩ := Finset.mem_map.1 hq
      obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_map.1 (Finset.mem_powerset.1 hI' hq')
      simpa using hq₀
    · rw [Finset.map_map]; simp
  · rw [Finset.card_map, Finset.card_map, hF I (Finset.mem_powerset.1 hI)]

omit [Fintype ι] [Fintype ι'] in
/-- The cut point of the image of a set, at the image of a parameter. -/
theorem cutPt_map_apply (c : ι ≃ ι') (I : Finset ι) (q : ι) :
    cutPt (I.map c.toEmbedding) (c q) = cutPt I q := by
  unfold cutPt
  simp

end Mix

/-! ### The rooted trace, the hull and the activity -/

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ} {m₀ : ℕ}

local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bk'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "ck" => (Prod.map id bk : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1))
local notation "aK" => cellSide L m₀ m₁ (k + 1)

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'} {ρ : ℕ}

/-- **The rooted trace with its background** at corresponding unit points, cut parameters and data
corresponding on the box of radius `ρ + 1`. -/
theorem rootTraceBg_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT ν ρb : ℝ) (B : Finset (unitPts G))
    {D : BgData G N} {D' : BgData H N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {s : DecParams G} {s' : DecParams H} (hs : ∀ q : cubeIdx G, s' (hI.cubeEquiv q) = s q) :
    rootTraceBg H a aT ν ρb (unitQ H) (unitP H) (B.map hI.unitEquiv.toEmbedding) D' s' =
      rootTraceBg G a aT ν ρb (unitQ G) (unitP G) B D s := by
  obtain ⟨hF, hM⟩ := hI.decBgField_eq hI a ν ρb (s := s) (s' := s') hs hΨ hh
  unfold rootTraceBg
  refine hI.rootTrace_eq a aT ν B hs (fun x => ?_) (fun x => ?_)
  · funext i
    unfold barField
    simp only [coe_e, x.2, hI.mapsTo x.2, ↓reduceDIte]
    rw [decBgField_eq_dec2, decBgField_eq_dec2]
    exact hF x i
  · rw [decBgMult_eq_dec2, decBgMult_eq_dec2]
    exact hM x

/-- The root index of the image of a unit point. -/
theorem rootIdxOf_map (hI : OmegaIso G H ρ) {y : unitPts G} {x : G.Ω 1}
    (hx : unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = (y : UnitTorus d L N₁ m₁ k)) :
    rootIdxOf (hI.unitEquiv y) = blockIndex (bk (x : CTorus d L N₁ m₁ (k + 1))) := by
  rw [rootIdxOf_eq (hI.unitEquiv_site hx).symm, coe_e]

/-- The facts on the powers used for the hull. -/
theorem hull_pow_facts {j : ℕ} (hj : j ≤ k + 1) :
    L ^ (j + m₁) ≤ aK ∧ aK ≤ L * aK ∧ 0 < aK := by
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨?_, cellSide_le_mul, cellSide_pos m₀ m₁ (k + 1)⟩
  unfold cellSide
  exact Nat.pow_le_pow_right hL (by omega)

/-- **The hull set of the root cube and of the patches of a set of parameter cubes** goes to the
hull set of the image unit point and of the image set (cubes of all levels of `G`). -/
theorem hullSet_image (hI : OmegaIso G H ρ) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hroom : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (y : unitPts G) (J : Finset (cubeIdx G)) :
    hullSet m₀ (rootIdxOf (hI.unitEquiv y)) (patches (J.map hI.cubeEquiv.toEmbedding)) =
      bk '' hullSet m₀ (rootIdxOf y) (patches J) := by
  obtain ⟨x, hx⟩ := exists_site y
  obtain ⟨-, haL, ha0⟩ := hull_pow_facts (L := L) (m₀ := m₀) (m₁ := m₁) (j := k + 1) le_rfl
  have hxb := hI.boxG x x.2
  have hr0 : rootIdxOf y = blockIndex (x : CTorus d L N₁ m₁ (k + 1)) := rootIdxOf_eq hx
  have hcell : ∀ z ∈ box (cbase aK (x : CTorus d L N₁ m₁ (k + 1))) aK,
      InBox d (ρ + aK) ((N₁ * L ^ m₁) * L ^ (k + 1)) z :=
    fun z hz => inBox_of_mem_cell (by omega) hxb hz
  have hpat : patches (J.map hI.cubeEquiv.toEmbedding) = (patches J).image ck := by
    unfold patches
    rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
    rfl
  unfold hullSet
  rw [Set.image_union, Set.image_iUnion₂, hpat, Finset.set_biUnion_finset_image]
  congr 1
  · rw [hr0, hI.rootIdxOf_map hx, rootSet_blockIndex, rootSet_blockIndex]
    exact (cell_image hN hN' (by omega) _ hcell).symm
  · refine Set.iUnion₂_congr fun P hP => ?_
    obtain ⟨hPc, -⟩ := mem_patches.1 hP
    obtain ⟨⟨-, hj⟩, -, hbP⟩ := (mem_cubeIdx G).1 hPc
    obtain ⟨hjm, -, -⟩ := hull_pow_facts (L := L) (m₀ := m₀) (m₁ := m₁) hj
    have hcs : L * cellSide L 0 m₁ P.1 = L * L ^ (P.1 + m₁) := by
      unfold cellSide; rw [Nat.add_zero]
    have hLj : L * L ^ (P.1 + m₁) ≤ L * aK := Nat.mul_le_mul_left L hjm
    obtain ⟨j, y0⟩ := P
    exact (pset_image (m₀ := 0) (N₁' := N₁') hj (by rw [hcs]; omega) (hI.base_inBox hPc)
      hbP).symm

/-- The sites of the hull set lie in the box of radius `ρ + a_K`. -/
theorem hullSet_inBox (hI : OmegaIso G H ρ)
    (hroom : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (y : unitPts G) (J : Finset (cubeIdx G)) :
    ∀ z ∈ hullSet m₀ (rootIdxOf y) (patches J),
      InBox d (ρ + aK) ((N₁ * L ^ m₁) * L ^ (k + 1)) z := by
  obtain ⟨x, hx⟩ := exists_site y
  obtain ⟨-, haL, ha0⟩ := hull_pow_facts (L := L) (m₀ := m₀) (m₁ := m₁) (j := k + 1) le_rfl
  have hxb := hI.boxG x x.2
  rintro z (hz | hz)
  · rw [rootIdxOf_eq hx, rootSet_blockIndex] at hz
    exact inBox_of_mem_cell (by omega) hxb hz
  · obtain ⟨P, hP, hzP⟩ := Set.mem_iUnion₂.1 hz
    obtain ⟨hPc, -⟩ := mem_patches.1 hP
    obtain ⟨⟨-, hj⟩, -, hbP⟩ := (mem_cubeIdx G).1 hPc
    obtain ⟨hjm, -, -⟩ := hull_pow_facts (L := L) (m₀ := m₀) (m₁ := m₁) hj
    obtain ⟨j, y0⟩ := P
    exact inBox_mono (by omega) (pset_inBox hj hbP (hI.base_inBox hPc) (by omega) hzP)

/-- **The hull of `(y, J)` on two tori**: the hull of the image unit point and the image set of
parameter cubes is the `cubeMap`-image of the hull. -/
theorem hullOf_image (hI : OmegaIso G H ρ) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hroom : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hroom' : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (y : unitPts G) (J : Finset (cubeIdx G)) :
    hullOf m₀ (rootIdxOf (hI.unitEquiv y)) (patches (J.map hI.cubeEquiv.toEmbedding)) =
      (hullOf m₀ (rootIdxOf y) (patches J)).image (cubeMap hN hN' le_rfl) := by
  unfold hullOf
  rw [hI.hullSet_image hN hN' hroom y J]
  exact piHull_boxMap hN hN' hroom hroom' (hI.hullSet_inBox hroom y J)

/-- The sites of the hull lie in the box of radius `ρ + a_K + 2 L a_K`. -/
theorem hullOf_inBox (hI : OmegaIso G H ρ)
    (hroom : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (y : unitPts G) (J : Finset (cubeIdx G)) :
    ∀ x ∈ sitesOf (hullOf m₀ (rootIdxOf y) (patches J)),
      InBox d (ρ + aK + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := mem_sitesOf.1 hx
  obtain ⟨-, haL, ha0⟩ := hull_pow_facts (L := L) (m₀ := m₀) (m₁ := m₁) (j := k + 1) le_rfl
  exact inBox_of_mem_piHull (by omega) (hI.hullSet_inBox hroom y J) hc x hxc

/-- **The determinant activity of a unit point and a polymer** on two tori, for data corresponding
on the box of radius `ρ + 1` and a polymer whose sites lie in the box of radius
`ρ + a_K + 2 L a_K`. -/
theorem detActivityBg_eq (hI : OmegaIso G H ρ) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hroom : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hroom' : 2 * (ρ + aK + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (a : ℕ → ℝ) (aT ν ρb : ℝ) {D : BgData G N} {D' : BgData H N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h) (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hYr : ∀ x ∈ sitesOf Y, InBox d (ρ + aK + 2 * (L * aK)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    detActivityBg m₀ a aT ν ρb D' (hI.unitEquiv y) (Y.image (cubeMap hN hN' le_rfl)) =
      detActivityBg m₀ a aT ν ρb D y Y := by
  -- the image of the hull determines the hull
  have hinj : ∀ J : Finset (cubeIdx G),
      (hullOf m₀ (rootIdxOf y) (patches J)).image (cubeMap hN hN' le_rfl) =
        Y.image (cubeMap hN hN' le_rfl) ↔ hullOf m₀ (rootIdxOf y) (patches J) = Y := by
    intro J
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have h1 := image_image_cubeMap hN hN' le_rfl (r := ρ + aK + 2 * (L * aK)) hroom'
      (hullOf m₀ (rootIdxOf y) (patches J)) (hI.hullOf_inBox hroom y J)
    have h2 := image_image_cubeMap hN hN' le_rfl (r := ρ + aK + 2 * (L * aK)) hroom' Y hYr
    rw [← h1, ← h2, h]
  -- the activity
  unfold detActivityBg
  symm
  refine Finset.sum_bij (fun J _ => J.map hI.cubeEquiv.toEmbedding) (fun J hJ => ?_)
    (fun J₁ _ J₂ _ h => Finset.map_injective _ h) (fun J' hJ' => ?_) (fun J hJ => ?_)
  · obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    rw [hI.hullOf_image hN hN' hroom hroom' y J, hJY]
  · obtain ⟨-, hJY⟩ := Finset.mem_filter.1 hJ'
    refine ⟨J'.map hI.cubeEquiv.symm.toEmbedding, Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩, ?_⟩
    · have hmap : (J'.map hI.cubeEquiv.symm.toEmbedding).map hI.cubeEquiv.toEmbedding = J' := by
        rw [Finset.map_map]; simp
      rw [← hinj, ← hI.hullOf_image hN hN' hroom hroom', hmap, hJY]
    · rw [Finset.map_map]; simp
  · refine (mixDiff_map hI.cubeEquiv J fun I _ => ?_).symm
    rw [show ({hI.unitEquiv y} : Finset (unitPts H)) =
      ({y} : Finset (unitPts G)).map hI.unitEquiv.toEmbedding by simp]
    exact hI.rootTraceBg_eq a aT ν ρb {y} hΨ hh (fun q => cutPt_map_apply hI.cubeEquiv I q)

/-- **The determinant part of the coefficient on two tori**: at parameters whose raw data
correspond on the box of radius `ρ + 1`, masks corresponding under the bijection of the unit
points, and a polymer of the box and its image. -/
theorem newLevelDetBg_eq (hI : OmegaIso G H ρ) (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hroom : 2 * (ρ + cellSide L 1 m₁ (k + 1) + 2 * (L * cellSide L 1 m₁ (k + 1))) +
      L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hroom' : 2 * (ρ + cellSide L 1 m₁ (k + 1) + 2 * (L * cellSide L 1 m₁ (k + 1))) +
      L * cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (a : ℕ → ℝ) (aT ν ρb : ℝ) (Zb : Finset (unitPts G)) {θ : physParamBg N G}
    {θ' : physParamBg N H}
    (hΨ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hh : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (hTr : ∀ x ∈ sitesOf T, InBox d (ρ + cellSide L 1 m₁ (k + 1) +
      2 * (L * cellSide L 1 m₁ (k + 1))) ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    newLevelDetBg H a aT ν ρb (Zb.map hI.unitEquiv.toEmbedding) θ' (T.image (cubeMap hN hN' le_rfl)) =
      newLevelDetBg G a aT ν ρb Zb θ T := by
  unfold newLevelDetBg
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun y _ =>
    hI.detActivityBg_eq hN hN' hroom hroom' a aT ν ρb hΨ hh y T hTr

end OmegaIso

end Balaban.Polymer.LocalIso
