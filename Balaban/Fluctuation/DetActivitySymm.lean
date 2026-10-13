/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetOutputTerms
public import Balaban.Localization.DecEquivLatBg
import Mathlib.Tactic.Linarith

/-!
# Covariance of the determinant activities under the symmetries of the paving

Let `r` be a symmetry of the paving `π_{k+1}` (`pavingSymGroup`).  The activity
`detActivityBg D y Y` is a sum over the cut sets `J` with hull `Y` of the mixed differences of
`s ↦ rootTraceBg {y} D s`.  This file reduces the covariance
`detActivityBg (r D) (r y) (r Y) = detActivityBg D y Y` to one statement about the rooted trace,
which is **not proved**.

## What is proved

* `mixDiff_map`: the mixed differences of two functions related at the cut points by a
  relabelling `τ` of the parameters agree: `Δ_{τ J} F' = Δ_J F` if
  `F'(1_I ∘ τ⁻¹) = F(1_I)` for `I ⊆ J`.
* `hullOf_patches_map`: if `τ` moves the cube of each parameter by `r`
  (`Pset (τ P) = r '' Pset P`), then the hull of the relabelled cut set is the image of the hull:
  `hullOf (r z) (patches (τ J)) = r • hullOf z (patches J)` (from `piHull_image`; reflections are
  included, since only the sets of sites of the cubes enter).
* `cutActivity_relabel`: the assembly is covariant for every pair of functions of the cuts
  related by `τ` at the cut points.
* `detActivityBg_relabel_of_rootTraceBg`: the activities are covariant **if** the rooted trace
  with its background is covariant at the cut points:
  `rootTraceBg {y'} D' (1_I ∘ τ⁻¹) = rootTraceBg {y} D (1_I)`.
* `sum_detActivityBg_relabel_of_rootTraceBg`: the same for the sums over the unit blocks of
  `B(z)` and `B(r z)`, i.e. for the terms of the record `DetExpansionLocC`, in the form
  `e' (r z) (r T) = e z T` used by `rootedSum_covariant`.
* `rootTraceBg_sym_of_rootTrace`, `detActivityBg_sym_of_rootTrace`: for a lattice symmetry `σ`
  compatible with the cover and the blocks (`LatSymm`, `CoverSymm`, `BlockSymm`), the decoupled
  background is covariant (`decBg_sym`), and the hypothesis reduces to the covariance of the
  rooted trace **at fixed fields**:
  `rootTrace {y'} (s ∘ τ⁻¹) (φ ∘ σ⁻¹) (α ∘ σ⁻¹) = rootTrace {y} s φ α`.
* `rootAct_inv_rootAct`, `cubeAct_injective`: the actions on roots and on sets of cubes are
  injective.
* `detActivityBg_relabel_one`: the hypotheses hold for the identity.

## What is missing

The covariance of the rooted trace at fixed fields, that is of the diagonal entries of the
decoupled logarithm `decLog` on the unit lattice (with `unitQ`, `unitP`) under a lattice symmetry.
The landed covariance statements cover the cut operators and the decoupled Green's function
(`rm_Gs`), and the decoupled background (`decBg_sym`); there is none for the `x`-shifted Green's
function `Gsx`, for `decM`, `decN`, `decPi`, `decCov` or `decLog`.  Moreover the only landed
elements of `CoverSymm` and `BlockSymm` are the identity: no translation or rotation of the paving
has been shown to be compatible with the cover and the blocks of a level generating set.  So no
covariance of the activities is proved here for any symmetry other than the identity, neither for
translations nor for rotations and reflections.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv Finset Matrix

/-! ### Mixed differences under a relabelling -/

section Relabel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The cut point of the image of a set under a bijection of the parameters. -/
theorem cutPt_map (e : ι ≃ ι) (I : Finset ι) :
    cutPt (I.map e.toEmbedding) = fun P => cutPt I (e.symm P) := by
  funext P
  simp only [cutPt, Finset.mem_map_equiv]

omit [Fintype ι] in
/-- **Mixed differences under a relabelling of the parameters.**  If `F'(1_I ∘ e⁻¹) = F(1_I)` for
all `I ⊆ J`, then `Δ_{e J} F' = Δ_J F`. -/
theorem mixDiff_map (e : ι ≃ ι) {F F' : (ι → ℂ) → ℂ} (J : Finset ι)
    (hF : ∀ I ⊆ J, F' (fun P => cutPt I (e.symm P)) = F (cutPt I)) :
    mixDiff (J.map e.toEmbedding) F' = mixDiff J F := by
  unfold mixDiff
  refine (Finset.sum_equiv e.finsetCongr (fun I => ?_) fun I hI => ?_).symm
  · simp only [Finset.mem_powerset, Equiv.finsetCongr_apply, Finset.map_subset_map]
  · rw [Equiv.finsetCongr_apply, Finset.card_map, Finset.card_map, cutPt_map,
      hF I (Finset.mem_powerset.1 hI)]

end Relabel

/-! ### The actions on roots and on sets of cubes -/

section Actions

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- The action of a paving symmetry on roots is inverted by the action of its inverse. -/
theorem rootAct_inv_rootAct {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (z : RootIdx d L N₁ m₁ K) : rootAct r⁻¹ (rootAct r z) = z := by
  apply rootSite_injective
  rw [rootSite_rootAct, rootSite_rootAct, blockBase_inv_blockBase (m₀ := m₀) hr,
    blockBase_rootSite]

/-- The action of a paving symmetry on roots is injective. -/
theorem rootAct_injective {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) :
    Function.Injective (rootAct (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) r) :=
  fun z z' h => by
    rw [← rootAct_inv_rootAct hr z, h, rootAct_inv_rootAct hr z']

/-- The action of a paving symmetry on finite sets of cubes is injective. -/
theorem cubeAct_injective (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {A B : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)}
    (h : cubeAct r A = cubeAct r B) : A = B := by
  rw [← cubeAct_cubeAct hN hr A, h, cubeAct_cubeAct hN hr B]

end Actions

/-! ### The hull of a relabelled cut set -/

section Hull

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- The union of the cubes of a relabelled cut set is the image of the union of the cubes. -/
theorem iUnion_patches_map (τ : cubeIdx G ≃ cubeIdx G)
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hτ : ∀ P : cubeIdx G, Pset m₁ (τ P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
      r '' Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1)))
    (J : Finset (cubeIdx G)) :
    (⋃ Q ∈ patches (J.map τ.toEmbedding), Pset m₁ Q) = r '' ⋃ P ∈ patches J, Pset m₁ P := by
  rw [Set.image_iUnion₂]
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨Q, hQ, hx⟩
    obtain ⟨hQc, hQJ⟩ := mem_patches.1 hQ
    obtain ⟨P, hP, hPQ⟩ := Finset.mem_map.1 hQJ
    have hval : (τ P : ℕ × CTorus d L N₁ m₁ (k + 1)) = Q := congrArg Subtype.val hPQ
    refine ⟨P.1, mem_patches.2 ⟨P.2, hP⟩, ?_⟩
    rw [← hτ P, hval]
    exact hx
  · rintro ⟨P, hP, hx⟩
    obtain ⟨hPc, hPJ⟩ := mem_patches.1 hP
    refine ⟨(τ ⟨P, hPc⟩ : ℕ × CTorus d L N₁ m₁ (k + 1)),
      mem_patches.2 ⟨(τ ⟨P, hPc⟩).2, Finset.mem_map_of_mem _ hPJ⟩, ?_⟩
    rw [hτ ⟨P, hPc⟩]
    exact hx

/-- **The hull of a relabelled cut set.**  If the relabelling `τ` of the parameter cubes moves
the cube of each parameter by the paving symmetry `r`, then
`hullOf (r z) (patches (τ J)) = r • hullOf z (patches J)`. -/
theorem hullOf_patches_map (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (τ : cubeIdx G ≃ cubeIdx G)
    (hτ : ∀ P : cubeIdx G, Pset m₁ (τ P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
      r '' Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1)))
    (z : RootIdx d L N₁ m₁ (k + 1)) (J : Finset (cubeIdx G)) :
    hullOf m₀ (rootAct r z) (patches (J.map τ.toEmbedding)) =
      cubeAct r (hullOf m₀ z (patches J)) := by
  unfold hullOf
  rw [← piHull_image hN hr]
  congr 1
  unfold hullSet
  rw [rootSet_rootAct hN hr, Set.image_union, iUnion_patches_map τ hτ J]

end Hull

/-! ### Covariance of the assembly -/

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
/-- **Covariance of the assembly.**  Let `r` be a symmetry of the paving, `τ` a relabelling of
the parameter cubes which moves the cube of each parameter by `r`, and `y'` a unit block whose
root is the image of the root of `y`.  If two functions of the cuts are related by
`F'(1_I ∘ τ⁻¹) = F(1_I)` at the cut points, then
`cutActivity F' y' (r • Y) = cutActivity F y Y`. -/
theorem cutActivity_relabel (hN : L ^ m₀ ∣ N₁) {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (τ : cubeIdx G ≃ cubeIdx G)
    (hτ : ∀ P : cubeIdx G, Pset m₁ (τ P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
      r '' Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1)))
    {F F' : DecParams G → ℂ}
    (hF : ∀ I : Finset (cubeIdx G), F' (fun P => cutPt I (τ.symm P)) = F (cutPt I))
    {y y' : unitPts G} (hy : rootIdxOf y' = rootAct r (rootIdxOf y))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    cutActivity m₀ F' y' (cubeAct r Y) = cutActivity m₀ F y Y := by
  unfold cutActivity
  refine (Finset.sum_equiv τ.finsetCongr (fun J => ?_) fun J _ => ?_).symm
  · simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Equiv.finsetCongr_apply]
    rw [hy, hullOf_patches_map hN hr τ hτ]
    exact ⟨fun h => by rw [h], fun h => cubeAct_injective hN hr h⟩
  · rw [Equiv.finsetCongr_apply, mixDiff_map τ J fun I _ => hF I]

open Classical in
/-- **Covariance of the activities, reduced to the rooted trace.**  With `r`, `τ`, `y'` as in
`cutActivity_relabel`: if the rooted traces with their backgrounds of two data `D`, `D'` are
related at the cut points by `rootTraceBg {y'} D' (1_I ∘ τ⁻¹) = rootTraceBg {y} D (1_I)`, then
`detActivityBg D' y' (r • Y) = detActivityBg D y Y`.  The hypothesis is the covariance of the
rooted trace; it is not proved (see the module documentation). -/
theorem detActivityBg_relabel_of_rootTraceBg (hN : L ^ m₀ ∣ N₁)
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (τ : cubeIdx G ≃ cubeIdx G)
    (hτ : ∀ P : cubeIdx G, Pset m₁ (τ P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
      r '' Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1)))
    {a : ℕ → ℝ} {aT ν ρ : ℝ} {D D' : BgData G N} {y y' : unitPts G}
    (hy : rootIdxOf y' = rootAct r (rootIdxOf y))
    (hF : ∀ I : Finset (cubeIdx G),
      rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y'} D' (fun P => cutPt I (τ.symm P)) =
        rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D (cutPt I))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivityBg m₀ a aT ν ρ D' y' (cubeAct r Y) = detActivityBg m₀ a aT ν ρ D y Y := by
  rw [detActivityBg_eq_cutActivity, detActivityBg_eq_cutActivity]
  exact cutActivity_relabel hN hr τ hτ hF hy Y

open Classical in
/-- **The hypotheses hold for the identity** (the only symmetry for which the covariance of the
rooted trace is available): `r = 1`, `τ = 1`, `y' = y`, `D' = D`. -/
theorem detActivityBg_relabel_one (hN : L ^ m₀ ∣ N₁) (a : ℕ → ℝ) (aT ν ρ : ℝ) (D : BgData G N)
    (y : unitPts G) :
    (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) ∈
        pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1) ∧
      (∀ P : cubeIdx G, Pset m₁ ((Equiv.refl (cubeIdx G)) P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
        (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) ''
          Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1))) ∧
      rootIdxOf y = rootAct (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) (rootIdxOf y) ∧
      (∀ I : Finset (cubeIdx G),
        rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D
            (fun P => cutPt I ((Equiv.refl (cubeIdx G)).symm P)) =
          rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D (cutPt I)) ∧
      ∀ Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ),
        detActivityBg m₀ a aT ν ρ D y (cubeAct (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) Y) =
          detActivityBg m₀ a aT ν ρ D y Y := by
  have h1 : (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) ∈
      pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1) := one_mem _
  have h2 : ∀ P : cubeIdx G,
      Pset m₁ ((Equiv.refl (cubeIdx G)) P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
        (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) ''
          Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) := fun P => by simp
  have h3 : rootIdxOf y = rootAct (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) (rootIdxOf y) := by
    unfold rootAct
    rw [Equiv.Perm.coe_one, id, blockIndex_rootSite]
  have h4 : ∀ I : Finset (cubeIdx G),
      rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D
          (fun P => cutPt I ((Equiv.refl (cubeIdx G)).symm P)) =
        rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D (cutPt I) := fun _ => rfl
  exact ⟨h1, h2, h3, h4, fun Y =>
    detActivityBg_relabel_of_rootTraceBg hN h1 (Equiv.refl _) h2 h3 h4 Y⟩

end Assembly

/-! ### The terms of a block -/

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {m₀ : ℕ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

open Classical in
/-- **Covariance of the terms of a block, reduced to the rooted trace.**  Let `r` be a symmetry of
the paving, `τ` a relabelling of the parameter cubes which moves the cube of each parameter by
`r`, and `u` a bijection of the unit lattice which moves the `L`-block of each unit block by `r`.
If the rooted traces with their backgrounds of two data `D`, `D'` are related at the cut points
by `rootTraceBg {u y} D' (1_I ∘ τ⁻¹) = rootTraceBg {y} D (1_I)`, then the sums of the activities
over the unit blocks of `B(r z)` and of `B(z)` satisfy

`∑_{y' ∈ B(r z)} detActivityBg D' y' (r • T) = ∑_{y ∈ B(z)} detActivityBg D y T`,

which is the hypothesis `e' (r z) (r • T) = e z T` of `rootedSum_covariant` for the terms of the
record `DetExpansionLocC`. -/
theorem sum_detActivityBg_relabel_of_rootTraceBg (hN : L ^ m₀ ∣ N₁)
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (τ : cubeIdx S.G' ≃ cubeIdx S.G')
    (hτ : ∀ P : cubeIdx S.G', Pset m₁ (τ P : ℕ × CTorus d L N₁ m₁ (k + 1)) =
      r '' Pset m₁ (P : ℕ × CTorus d L N₁ m₁ (k + 1)))
    (u : S.U ≃ S.U)
    (hu : ∀ y : S.U, unitBlock1 ((u y : S.U) : UnitTorus d L N₁ m₁ k) =
      rootAct r (unitBlock1 (y : UnitTorus d L N₁ m₁ k)))
    {ρ : ℝ} {D D' : BgData S.G' N}
    (hF : ∀ (y : S.U) (I : Finset (cubeIdx S.G')),
      rootTraceBg S.G' S.a S.a₁ S.ν ρ (unitQ S.G') (unitP S.G') {u y} D'
          (fun P => cutPt I (τ.symm P)) =
        rootTraceBg S.G' S.a S.a₁ S.ν ρ (unitQ S.G') (unitP S.G') {y} D (cutPt I))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ∑ y' ∈ S.blockU (rootAct r z), detActivityBg m₀ S.a S.a₁ S.ν ρ D' y' (cubeAct r T) =
      ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν ρ D y T := by
  refine (Finset.sum_equiv u (fun y => ?_) fun y _ => ?_).symm
  · simp only [StepSetting.blockU, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hu y]
    exact ⟨fun h => by rw [h], fun h => rootAct_injective hr h⟩
  · refine (detActivityBg_relabel_of_rootTraceBg hN hr τ hτ ?_ (hF y) T).symm
    rw [rootIdxOf_eq_unitBlock1, rootIdxOf_eq_unitBlock1, hu y]

end Block

/-! ### Lattice symmetries: reduction to the rooted trace at fixed fields -/

section Lattice

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
  (S : LatSymm G G σ) (CS : CoverSymm (coverOf G) σ) (B : BlockSymm G σ)

include B in
/-- **Covariance of the rooted trace with its background, reduced to fixed fields.**  For a
lattice symmetry `σ` compatible with the cover and the blocks, the decoupled background of the
transported datum at the transported cuts is the transported background (`decBg_sym`).  Hence, if
the rooted trace at fixed fields is covariant for the cuts `s`,
`rootTrace Bs' (s ∘ τ⁻¹) (φ ∘ σ⁻¹) (α ∘ σ⁻¹) = rootTrace Bs s φ α` for all `φ`, `α`, then
`rootTraceBg Bs' (σ D) (s ∘ τ⁻¹) = rootTraceBg Bs D s`. -/
theorem rootTraceBg_sym_of_rootTrace {Bs Bs' : Finset (unitPts G)} (s : DecParams G)
    (hRT : ∀ (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ),
      rootTrace G a aT ν (unitQ G) (unitP G) Bs' (CS.par s) (symSite σ φ) (S.mul α) =
        rootTrace G a aT ν (unitQ G) (unitP G) Bs s φ α)
    (ρ : ℝ) (D : BgData G N) :
    rootTraceBg G a aT ν ρ (unitQ G) (unitP G) Bs' (S.sym D) (CS.par s) =
      rootTraceBg G a aT ν ρ (unitQ G) (unitP G) Bs D s := by
  unfold rootTraceBg
  obtain ⟨h1, h2⟩ := decBg_sym S CS B ρ s D (a := a) (ν := ν)
  rw [h1, h2]
  have hbar : barField G (S.sym D).Ψ (S.fld (decBgField G a ν ρ s D)) =
      symSite σ (barField G D.Ψ (decBgField G a ν ρ s D)) := by
    funext w i
    obtain ⟨x, rfl⟩ := σ.surjective w
    rw [S.barField_sym]
    simp [symSite]
  rw [hbar]
  exact hRT _ _

include B in
open Classical in
/-- **Covariance of the activities under a lattice symmetry, reduced to the rooted trace at fixed
fields.**  Let `σ` be a symmetry of the paving which is a lattice symmetry of the generating set
compatible with the cover and the blocks, and which maps the cube of each parameter `q` onto the
cube of `τ q`.  Let `y'` be a unit block whose root is the image of the root of `y`.  If the
rooted trace at fixed fields is covariant at the cut points,
`rootTrace {y'} (1_I ∘ τ⁻¹) (φ ∘ σ⁻¹) (α ∘ σ⁻¹) = rootTrace {y} 1_I φ α`, then
`detActivityBg (σ D) y' (σ • Y) = detActivityBg D y Y`.  The hypothesis `hRT` is the missing
covariance of the decoupled logarithm. -/
theorem detActivityBg_sym_of_rootTrace (hN : L ^ m₀ ∣ N₁)
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    (hpset : ∀ q ∈ cubeIdx G, Pset m₁ (CS.τ q) = σ '' Pset m₁ q)
    {y y' : unitPts G} (hy : rootIdxOf y' = rootAct σ (rootIdxOf y))
    (hRT : ∀ (I : Finset (cubeIdx G)) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
      (α : G.Ω 1 → ℂ),
      rootTrace G a aT ν (unitQ G) (unitP G) {y'} (CS.par (cutPt I)) (symSite σ φ) (S.mul α) =
        rootTrace G a aT ν (unitQ G) (unitP G) {y} (cutPt I) φ α)
    (ρ : ℝ) (D : BgData G N)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivityBg m₀ a aT ν ρ (S.sym D) y' (cubeAct σ Y) = detActivityBg m₀ a aT ν ρ D y Y := by
  refine detActivityBg_relabel_of_rootTraceBg hN hσ
    (CS.τ.subtypeEquiv fun q => (CS.idx q).symm) (fun P => hpset P.1 P.2) hy (fun I => ?_) Y
  exact rootTraceBg_sym_of_rootTrace S CS B (cutPt I) (hRT I) ρ D

end Lattice

end Balaban.Fluctuation
