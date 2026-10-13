/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsExpansion
public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.RootMarkGeom
public import Balaban.Fluctuation.SizeModG4
public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Polymer.LabelRootUnion
public import Balaban.Fluctuation.ObsMeanBlock

/-!
# Cube labels of the polymer domains of the sharp hat expansion; multiplicity of the marks

For the observable marks of the zero-class step, the coordinate-derivative coefficients are
indexed by the polymer domains `Y` of the sharp hat expansion.  They are regrouped by the set of
`π'_K`-cubes contained in `Y`.

* Label map: `obsRowLabel m₀ K Y = blocksOf m₀ K univ Y`.  It contains the root cube of every
  site of `Y` (`rootCube_blockIndex_mem_obsRowLabel`), in particular of the source site when it
  lies in `Y` (every polymer domain of the expansion contains the source set); it contains the
  mark cube `S.cellOf m₀ u` as soon as `Y` contains a site of the unit point `u`
  (`cellOf_mem_obsRowLabel`); it is injective on the domains in `𝒟_K` (`obsRowLabel_injective`),
  so regrouping by the label has no fibre sum; and it has the size of the domain
  (`dExt_obsRowLabel_le`, `dExt_obsRowLabel_eq_sizeJ`).
* Multiplicity: the number of marks `(u, a)` whose mark cube is a given cube `c` is at most
  `N * L ^ (d * (m₀ + m₁ + 1))` (`card_markIdx_cell_le`).

The coefficients `a_Y`, the kernel bound and the `ObsMarks` inhabitant are NOT constructed here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Multiscale

section Label

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The cube label of a domain**: the set of `π'_K`-cubes contained in `Y`. -/
noncomputable def obsRowLabel (m₀ K : ℕ) (Y : Set (CTorus d L N₁ m₁ K)) :
    Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :=
  blocksOf m₀ K Set.univ Y

theorem obsRowLabel_def (Y : Set (CTorus d L N₁ m₁ K)) :
    obsRowLabel m₀ K Y = blocksOf m₀ K Set.univ Y := rfl

/-- The root cube of the block of any site of `Y` lies in the label of `Y`. -/
theorem rootCube_blockIndex_mem_obsRowLabel (hN : L ^ m₀ ∣ N₁)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsDj m₀ K Y) {y : CTorus d L N₁ m₁ K} (hy : y ∈ Y) :
    rootCube (m₀ := m₀) (blockIndex y) ∈ obsRowLabel m₀ K Y :=
  rootCube_mem_blocksOf_of_isDj hN hY ⟨y, hy, rfl⟩

/-- The sites of the label of `Y` are `Y`. -/
theorem sitesOf_obsRowLabel (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) : sitesOf (obsRowLabel m₀ K Y) = Y := by
  have := sitesOf_blocksOf (Ω := Set.univ) hN le_rfl isPiUnion_univ_aux hY.2.1
  rwa [Set.inter_univ] at this

/-- **Injectivity**: two domains in `𝒟_K` with the same label are equal. -/
theorem obsRowLabel_injective (hN : L ^ m₀ ∣ N₁) {Y Y' : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) (hY' : IsDj m₀ K Y') (h : obsRowLabel m₀ K Y = obsRowLabel m₀ K Y') :
    Y = Y' := by
  rw [← sitesOf_obsRowLabel hN hY, ← sitesOf_obsRowLabel hN hY', h]

/-- **Size, inequality form.**  For `Y ∈ 𝒟_K` the real size of the label is at most the
covariance tree length of `Y`. -/
theorem dExt_obsRowLabel_le (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) :
    dExt (obsRowLabel m₀ K Y) ≤ treeLenCovOne m₀ K Y := by
  have hs := sitesOf_obsRowLabel hN hY
  have hle : dOmega m₀ K Set.univ (sitesOf (obsRowLabel m₀ K Y)) ≤
      ENNReal.ofReal (treeLenCovOne m₀ K Y) := by
    rw [hs]
    simpa using G4_dOmega_le (Ω := Set.univ) hY (by simpa using hY.1)
  have hfin : dOmega m₀ K Set.univ (sitesOf (obsRowLabel m₀ K Y)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  rw [dExt_eq_toReal hfin]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (treeLenCovOne_nonneg _ _ _)] at this

/-- **Size, equality form.**  For a polymer `Y` (a nonempty domain of finite size) the real size
of the label is the size `d(Y)`. -/
theorem dExt_obsRowLabel_eq_sizeJ (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) (hP : IsPolyDom m₀ K Y) :
    dExt (obsRowLabel m₀ K Y) = sizeJ m₀ K Y := by
  have hs := sitesOf_obsRowLabel hN hY
  have := dExt_eq_sizeJ_of_isPolyDom (T := obsRowLabel m₀ K Y) (by rw [hs]; exact hP)
  rwa [hs] at this

/-- **Polymer domains of the expansion.**  Under the hypotheses of `isDj_of_polymerDomains`, the
label of a domain `Y` of the expansion contains the root cube of every site of `Y`, and in
particular of every site of the source set `X₁ ⊆ Y`. -/
theorem rootCube_mem_obsRowLabel_of_polymerDomains {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
    {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}
    (hN : L ^ m₀ ∣ N₁) {lev : ℕ} (hG : IsLevel G lev) (hS : CovSetup G m₀ j X 𝒦X)
    (hd : 3 ≤ d) (hc : ∀ i, c i ∈ cubeIdx G)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hlev : lev = K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polymerDomains c G m₀ (X1 G m₀ j 𝒦X))
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X1 G m₀ j 𝒦X) :
    rootCube (m₀ := m₀) (blockIndex x) ∈ obsRowLabel m₀ K Y := by
  subst hlev
  exact rootCube_blockIndex_mem_obsRowLabel hN (isDj_of_polymerDomains c hG hS hd hc hopt hY)
    (subset_of_mem_polymerDomains hY hx)

end Label

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ}

/-- **The mark cube lies in the label.**  If `Y ∈ 𝒟_{k+1}` contains a site `y` of the unit point
`u`, the mark cube `S.cellOf m₀ u` lies in `obsRowLabel m₀ (k+1) Y`; it is the root cube of the
block of `y`. -/
theorem cellOf_mem_obsRowLabel (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsDj m₀ (k + 1) Y) {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ Y) {u : S.U}
    (hu : unitPt S.hG' y = u) : S.cellOf m₀ u ∈ obsRowLabel m₀ (k + 1) Y := by
  have hb : u ∈ S.blockU (blockIndex y) := by
    subst hu
    have h1 : unitBlock1 (unitBlock y) = blockIndex y :=
      mem_fineBlock_iff_unitBlock1.1 (mem_fineBlock.2 rfl)
    simpa [StepSetting.blockU, unitPt] using h1
  rw [cellOf_eq_rootCube (S := S) hb]
  exact rootCube_blockIndex_mem_obsRowLabel hN hY hy

/-- The mark indices: a unit point and a component. -/
abbrev ObsMarkIdx (S : StepSetting d L N₁ m₁ k N ϱ) : Type := S.U × Fin N

/-- The mark cube of the index `(u, a)`: the cube `S.cellOf m₀ u` (the block of
`ObsMeanBlock.blockMark`). -/
noncomputable def obsMarkCube (m₀ : ℕ) (i : ObsMarkIdx S) :
    CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ :=
  S.cellOf m₀ i.1

/-- **Unit points per cube.**  At most `L ^ d * (L ^ (m₀ + m₁)) ^ d` unit points have a given
mark cube: the cube contains at most `(L ^ (m₀ + m₁)) ^ d` root blocks, each with at most `L ^ d`
unit points. -/
theorem card_unitPts_cell_le
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    (Finset.univ.filter fun u : S.U => S.cellOf m₀ u = c).card ≤
      L ^ d * (L ^ (m₀ + m₁)) ^ d := by
  classical
  set F := Finset.univ.filter fun z : RootIdx d L N₁ m₁ (k + 1) => rootCube (m₀ := m₀) z = c
  have hsub : (Finset.univ.filter fun u : S.U => S.cellOf m₀ u = c) ⊆ F.biUnion S.blockU := by
    intro u hu
    have hu' : S.cellOf m₀ u = c := (Finset.mem_filter.1 hu).2
    refine Finset.mem_biUnion.2 ⟨unitBlock1 (u : UnitTorus d L N₁ m₁ k), ?_, ?_⟩
    · have hb : u ∈ S.blockU (unitBlock1 (u : UnitTorus d L N₁ m₁ k)) := by
        simp [StepSetting.blockU]
      simpa [F, ← cellOf_eq_rootCube (S := S) hb] using hu'
    · simp [StepSetting.blockU]
  calc _ ≤ (F.biUnion S.blockU).card := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ F, (S.blockU z).card := Finset.card_biUnion_le
    _ ≤ ∑ z ∈ F, L ^ d := Finset.sum_le_sum fun z _ => card_blockU_le S z
    _ = F.card * L ^ d := by simp
    _ ≤ (L ^ (m₀ + m₁)) ^ d * L ^ d :=
        Nat.mul_le_mul_right _ (card_rootCube_fibre_le c)
    _ = L ^ d * (L ^ (m₀ + m₁)) ^ d := mul_comm _ _

/-- **Multiplicity of the marks.**  The number of marks `(u, a)` with mark cube `c` is at most
`N * (L ^ d * (L ^ (m₀ + m₁)) ^ d)`. -/
theorem card_markIdx_cell_le
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    (Finset.univ.filter fun i : ObsMarkIdx S => obsMarkCube S m₀ i = c).card ≤
      N * (L ^ d * (L ^ (m₀ + m₁)) ^ d) := by
  classical
  have h : (Finset.univ.filter fun i : ObsMarkIdx S => obsMarkCube S m₀ i = c) =
      (Finset.univ.filter fun u : S.U => S.cellOf m₀ u = c) ×ˢ (Finset.univ : Finset (Fin N)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, and_true]
    exact Iff.rfl
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact Nat.mul_le_mul_left _ (card_unitPts_cell_le S c)

/-- The same bound as `N * L ^ (d * (m₀ + m₁ + 1))`. -/
theorem card_markIdx_cell_le_pow
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    (Finset.univ.filter fun i : ObsMarkIdx S => obsMarkCube S m₀ i = c).card ≤
      N * L ^ (d * (m₀ + m₁ + 1)) := by
  refine (card_markIdx_cell_le S c).trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_add]
  congr 2
  ring

end Step

section Witness

open Balaban.Localization in
/-- **Non-vacuity of the multiplicity bound** at the step `hatWitnessStep` (`d = L = 3`,
`k = 1`, `N₁ = 9`), with `m₀ = 1`. -/
theorem card_markIdx_cell_le_hatWitnessStep (N m₁ : ℕ) (p₁ : ℝ)
    (c : CubeB (d := 3) (L := 3) (N₁ := 9) (m₁ := m₁) (K := 1 + 1) 1 (1 + 1) Set.univ) :
    (Finset.univ.filter fun i : ObsMarkIdx (Balaban.Inhabited.hatWitnessStep N m₁ p₁) =>
        obsMarkCube (Balaban.Inhabited.hatWitnessStep N m₁ p₁) 1 i = c).card ≤ N * 3 ^ (3 * (m₁ + 2)) := by
  have := card_markIdx_cell_le_pow (Balaban.Inhabited.hatWitnessStep N m₁ p₁) c
  convert this using 3
  ring

/-- **Non-vacuity of the label map** for the whole-torus domain: `Set.univ ∈ 𝒟_K`, its label
contains the root cube of every site, and the label determines the domain. -/
theorem obsRowLabel_univ {d L N₁ m₁ K m₀ : ℕ} [NeZero N₁] [NeZero L] (hN : L ^ m₀ ∣ N₁)
    (y : CTorus d L N₁ m₁ K) :
    IsDj m₀ K (Set.univ : Set (CTorus d L N₁ m₁ K)) ∧
      rootCube (m₀ := m₀) (blockIndex y) ∈ obsRowLabel m₀ K (Set.univ : Set (CTorus d L N₁ m₁ K)) ∧
      sitesOf (obsRowLabel m₀ K (Set.univ : Set (CTorus d L N₁ m₁ K))) = Set.univ := by
  have h := isDj_univ d L N₁ m₁ K m₀ K
  exact ⟨h, rootCube_blockIndex_mem_obsRowLabel hN h (Set.mem_univ y),
    sitesOf_obsRowLabel hN h⟩

end Witness

end Balaban.Fluctuation
