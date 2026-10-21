/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyGraph
public import Balaban.Fluctuation.DetCauchyHull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The polymer activity of the rooted determinant term at fixed backgrounds (DET-CAUCHY, assembly)

Fields `φ`, `α` are fixed throughout.  **Not proved here:** the composed family with cut-dependent
backgrounds, the absorption of the prefactor, and the identification with the physical determinant
term.

## Bridge (T1)

The support theorem (`DetCauchyGraph`) works with parameter cubes `cubeIdx G` and chains of
centres whose thickened cubes are nearest-neighbour adjacent (`RootChain`).  The hull
(`DetCauchyHull`) works with the patches `Pset m₁ P` and asks that the root cube and the patches
of `J` be connected for Moore adjacency (`RootConnected`).  The two are related as follows.

* `patches J`: the underlying patches of a set `J` of parameter cubes.
* `rootIdxOf y`: the root index (coarse site of the block of side `L ^ (k+1)`) of a unit block `y`.
* `rootConnected_of_rootChain`: if every parameter cube of `J` lies in the footprint of a centre
  joined to `y` by a `RootChain`, then `RootConnected m₀ (rootIdxOf y) (patches J)`.  The proof
  uses `HatConn`: all cover cubes meeting the thickened cube of an active centre `q` lie in the
  footprint `𝒬(q) ⊆ J`, the sites of the thickened cube in `Ω₁` are nearest-neighbour connected,
  and consecutive sites of such a path lie in cubes that Moore-touch.  So **no extra hypothesis**
  is needed: the footprint adjacency of `paramGraph` is not Moore adjacency, but the footprint is
  Moore connected inside `J`.

## Activity (T2, T3)

`detActivity ... y Y` is the sum of the mixed differences `Δ_J` of the rooted trace of the block
`{y}` over the sets `J` of parameter cubes whose hull is `Y`.  The sum over all `Y` is the value
of the rooted trace at `s = 1` (`rootTrace_one_eq_sum_detActivity`); a non-zero activity is
supported on polymers containing the root cube (`detActivity_ne_zero_imp`).

## Decay (T4, T5)

With `Δ = detDeg d L + 1`, the rate `λ = κ - log 2 - 2 log Δ` (positive iff `e^κ > 2 Δ²`) and
the slope `a = 2 d L` and constant `b₀ = 0` of `dExt_hullOf_le`:
`‖detActivity y Y‖ ≤ M / (1 - e^{-λ}) · exp(-(λ / (2 d L)) dExt Y)`, `M = ½ N covBLog`
(`norm_detActivity_le`), and for `0 ≤ κ'' < λ / (2 d L)` the weighted sum over `Y` of
`‖detActivity y Y‖ exp(κ'' dExt Y)` is bounded (`sum_norm_detActivity_le`).  Requirement on `κ`
compared with DETCAUCHY §3: `κ > log 2 + 2 log D + 2 d L κ'` with `D = detDeg d L + 1` and
`b₀ = 0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField.Def6 Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

section Bridge

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
/-- The patches (the underlying `ℕ × CTorus` points) of a set of parameter cubes. -/
noncomputable def patches (J : Finset (cubeIdx G)) : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) :=
  J.image Subtype.val

theorem mem_patches {J : Finset (cubeIdx G)} {P : ℕ × CTorus d L N₁ m₁ (k + 1)} :
    P ∈ patches J ↔ ∃ h : P ∈ cubeIdx G, (⟨P, h⟩ : cubeIdx G) ∈ J := by
  classical
  simp only [patches, Finset.mem_image]
  constructor
  · rintro ⟨⟨P', h'⟩, hJ, rfl⟩
    exact ⟨h', hJ⟩
  · rintro ⟨h, hJ⟩
    exact ⟨⟨P, h⟩, hJ, rfl⟩

theorem card_patches_le (J : Finset (cubeIdx G)) : (patches J).card ≤ J.card := by
  classical
  exact Finset.card_image_le

theorem layer_le_of_mem_patches {J : Finset (cubeIdx G)} :
    ∀ P ∈ patches J, P.1 ≤ k + 1 := by
  intro P hP
  obtain ⟨h, -⟩ := mem_patches.1 hP
  exact ((mem_cubeIdx G).1 h).1.2

/-- The root index of a unit block: the coarse site of the block of side `L ^ (k+1)` that contains
its sites. -/
noncomputable def rootIdxOf (y : unitPts G) : RootIdx d L N₁ m₁ (k + 1) :=
  blockIndex (Classical.choose ((mem_unitPts G).1 y.2))

theorem blockIndex_eq_of_unitBlock_eq {x x' : CTorus d L N₁ m₁ (k + 1)}
    (h : unitBlock x = unitBlock x') : blockIndex x = blockIndex x' := by
  funext μ
  have h1 := (unitBlock_eq_iff _ _).1 h μ
  have key : ∀ z : ℕ, z / L ^ (k + 1) = z / L ^ k / L := fun z => by
    rw [Nat.div_div_eq_div_mul, ← pow_succ]
  simp only [blockIndex, key, h1]

theorem rootIdxOf_eq {y : unitPts G} {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : unitBlock x = (y : UnitTorus d L N₁ m₁ k)) : rootIdxOf y = blockIndex x := by
  have := (Classical.choose_spec ((mem_unitPts G).1 y.2)).2
  exact blockIndex_eq_of_unitBlock_eq (this.trans hx.symm)

/-- Every site lies in the root cube of its coarse block. -/
theorem mem_rootSet_blockIndex {K : ℕ} (x : CTorus d L N₁ m₁ K) :
    x ∈ rootSet m₀ (blockIndex x) := by
  show x ∈ box (cbase (cellSide L m₀ m₁ K) (rootSite (blockIndex x))) (cellSide L m₀ m₁ K)
  rw [rootSite_blockIndex, blockBase, cbase_cbase_of_dvd_hull (Nat.pos_of_ne_zero (NeZero.ne _))
    (pow_dvd_cellSide (m₀ := m₀))]
  exact mem_box_cbase (cellSide_pos m₀ m₁ K) x

variable (m₀) in
/-- The step relation of `RootConnected`: both ends are nodes (the root or a patch of `J'`) and
their site sets Moore-touch. -/
def rootStep (z : RootIdx d L N₁ m₁ (k + 1)) (J' : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))) :
    Option (ℕ × CTorus d L N₁ m₁ (k + 1)) → Option (ℕ × CTorus d L N₁ m₁ (k + 1)) → Prop :=
  fun A B => JNode J' A ∧ JNode J' B ∧ MooreTouch (nodeSet m₀ z A) (nodeSet m₀ z B)

omit [NeZero N₁] [NeZero L] in
theorem jnode_some {J' : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {P} (h : P ∈ J') :
    JNode J' (some P) := Or.inr ⟨P, h, rfl⟩

theorem jnode_of_actIn {J : Finset (cubeIdx G)} {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : ActIn G J q) {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hPc : P ∈ cubeIdx G)
    (hP : P ∈ Qset G q) : JNode (patches J) (some P) :=
  jnode_some (mem_patches.2 ⟨hPc, hq.2 (mem_QsetP.2 hP)⟩)

theorem rootStep_of_near {J : Finset (cubeIdx G)} {z : RootIdx d L N₁ m₁ (k + 1)}
    {P P' : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : JNode (patches J) (some P))
    (hP' : JNode (patches J) (some P')) {x x' : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ cubeP P) (hx' : x' ∈ cubeP P') (h : Near 1 1 x x') :
    Relation.ReflTransGen (rootStep m₀ z (patches J)) (some P) (some P') :=
  Relation.ReflTransGen.single ⟨hP, hP', x, mem_Pset_iff.2 hx, x', mem_Pset_iff.2 hx', h⟩

/-- Along a nearest-neighbour path in the thickened cube of an active centre, the cover cubes
containing the sites are connected by Moore-touching patches of `J`. -/
theorem rootStep_hat (hG : CubeAligned G m₁) {J : Finset (cubeIdx G)}
    {z : RootIdx d L N₁ m₁ (k + 1)} {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActIn G J q)
    {x x' : CTorus d L N₁ m₁ (k + 1)}
    (hpath : Relation.ReflTransGen (stepIn (hatI G q)) x x') :
    x ∈ hatI G q → ∀ P ∈ cubeIdx G, x ∈ cubeP P → ∀ P' ∈ cubeIdx G, x' ∈ cubeP P' →
      Relation.ReflTransGen (rootStep m₀ z (patches J)) (some P) (some P') := by
  induction hpath with
  | refl =>
    intro hx P hP hxP P' hP' hxP'
    have hxh := (mem_hatI_iff.1 hx).1
    exact rootStep_of_near (jnode_of_actIn hq hP (mem_Qset_of_mem_hat_cube hP hxh hxP))
      (jnode_of_actIn hq hP' (mem_Qset_of_mem_hat_cube hP' hxh hxP')) hxP hxP'
      (near_of_eq_or_adj (Or.inl rfl))
  | tail hab hbc ih =>
    rename_i b c
    intro hx P hP hxP P' hP' hcP'
    obtain ⟨hb, hc, hbcAdj⟩ := hbc
    obtain ⟨hbh, hbΩ⟩ := mem_hatI_iff.1 hb
    obtain ⟨hch, hcΩ⟩ := mem_hatI_iff.1 hc
    obtain ⟨Pb, hPb, hbP⟩ := exists_cube_of_mem_Omega hG hbΩ
    refine (ih hx P hP hxP Pb hPb hbP).tail ?_
    exact ⟨jnode_of_actIn hq hPb (mem_Qset_of_mem_hat_cube hPb hbh hbP),
      jnode_of_actIn hq hP' (mem_Qset_of_mem_hat_cube hP' hch hcP'), b, mem_Pset_iff.2 hbP, c,
      mem_Pset_iff.2 hcP', near_of_eq_or_adj (Or.inr hbcAdj)⟩

variable {a : ℕ → ℝ} {ν : ℝ}

/-- **The footprint of an active centre with connected thickened cube is Moore connected inside
`J`** (core of `rootStep_footprint`: connectivity of `□̂_q ∩ Ω₁` for this centre only).
**The footprint of an active centre is Moore connected inside `J`.**  Any two parameter cubes of
the footprint `𝒬(q) ⊆ J` are joined by a chain of Moore-touching patches of `J`. -/
theorem rootStep_footprint_of_conn (S : DGSetting G a ν) {J : Finset (cubeIdx G)}
    {z : RootIdx d L N₁ m₁ (k + 1)} {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActIn G J q)
    (hqc : ConnIn (hatI G q))
    {P P' : cubeIdx G} (hP : P ∈ QsetP G q) (hP' : P' ∈ QsetP G q) :
    Relation.ReflTransGen (rootStep m₀ z (patches J)) (some P.1) (some P'.1) := by
  have site : ∀ R : cubeIdx G, R ∈ QsetP G q → ∃ y ∈ hatI G q, y ∈ cubeP R.1 := by
    intro R hR
    obtain ⟨-, y, hy, hbox⟩ := mem_Qset.1 (mem_QsetP.1 hR)
    have hyc : y ∈ cubeP R.1 := mem_cubeP.2 hy
    exact ⟨y, mem_hatI_iff.2 ⟨mem_boxSet.2 hbox, cubeP_subset_Ω S R.2 hyc⟩, hyc⟩
  obtain ⟨y, hy, hyP⟩ := site P hP
  obtain ⟨y', hy', hyP'⟩ := site P' hP'
  exact rootStep_hat S.aligned hq (hqc y hy y' hy') hy P.1 P.2 hyP P'.1 P'.2 hyP'

/-- **The footprint of an active centre is Moore connected inside `J`.**  Any two parameter cubes of
the footprint `𝒬(q) ⊆ J` are joined by a chain of Moore-touching patches of `J`. -/
theorem rootStep_footprint (S : DGSetting G a ν) (hconn : HatConn G) {J : Finset (cubeIdx G)}
    {z : RootIdx d L N₁ m₁ (k + 1)} {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActIn G J q)
    {P P' : cubeIdx G} (hP : P ∈ QsetP G q) (hP' : P' ∈ QsetP G q) :
    Relation.ReflTransGen (rootStep m₀ z (patches J)) (some P.1) (some P'.1) :=
  rootStep_footprint_of_conn S hq (hconn q hq.1) hP hP'

/-- **T1, core**: connectivity of the thickened cubes of the centres with footprint in `J` in place
of `HatConn`.
**T1. The bridge.**  If every parameter cube of `J` lies in the footprint of a centre joined to
the block `y` by a `RootChain` (the conclusion of `exists_rootChain_of_mixDiff_ne_zero`), then the
root cube of `y` and the patches of `J` are connected for Moore adjacency (`RootConnected`). -/
theorem rootConnected_of_rootChain_of_conn (S : DGSetting G a ν) {J : Finset (cubeIdx G)}
    (hconnJ : ∀ q, ActIn G J q → ConnIn (hatI G q)) {y : unitPts G}
    (hJ : ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q) :
    RootConnected m₀ (rootIdxOf y) (patches J) := by
  have main : ∀ q q0, Relation.ReflTransGen (CentreLink G J) q q0 → HatAttached G y q0 →
      ActIn G J q0 → ∀ P ∈ QsetP G q,
        Relation.ReflTransGen (rootStep m₀ (rootIdxOf y) (patches J)) none (some P.1) := by
    intro q q0 hr hat hq0
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro P hP
      obtain ⟨x, hxb, hxh⟩ := hat
      obtain ⟨Px, hPx, hxP⟩ := exists_cube_of_mem_Omega S.aligned x.2
      have hPxQ : Px ∈ Qset G q0 := mem_Qset_of_mem_hat_cube hPx hxh hxP
      have hwQ : (⟨Px, hPx⟩ : cubeIdx G) ∈ QsetP G q0 := mem_QsetP.2 hPxQ
      have hroot : rootStep m₀ (rootIdxOf y) (patches J) none (some Px) := by
        refine ⟨Or.inl rfl, jnode_of_actIn hq0 hPx hPxQ, x, ?_, x, mem_Pset_iff.2 hxP,
          near_of_eq_or_adj (Or.inl rfl)⟩
        show (x : CTorus d L N₁ m₁ (k + 1)) ∈ rootSet m₀ (rootIdxOf y)
        rw [rootIdxOf_eq hxb]
        exact mem_rootSet_blockIndex _
      exact (Relation.ReflTransGen.single hroot).trans
        (rootStep_footprint_of_conn S hq0 (hconnJ q0 hq0) hwQ hP)
    | head hstep hrest ih =>
      rename_i q1 q2
      intro P hP
      obtain ⟨hq1, hq2, x, hx, x', hx', hxx'⟩ := hstep
      obtain ⟨hxh, hxΩ⟩ := mem_hatI_iff.1 hx
      obtain ⟨hxh', hxΩ'⟩ := mem_hatI_iff.1 hx'
      obtain ⟨Px, hPx, hxP⟩ := exists_cube_of_mem_Omega S.aligned hxΩ
      obtain ⟨Px', hPx', hxP'⟩ := exists_cube_of_mem_Omega S.aligned hxΩ'
      have h1 : (⟨Px, hPx⟩ : cubeIdx G) ∈ QsetP G q1 :=
        mem_QsetP.2 (mem_Qset_of_mem_hat_cube hPx hxh hxP)
      have h2 : (⟨Px', hPx'⟩ : cubeIdx G) ∈ QsetP G q2 :=
        mem_QsetP.2 (mem_Qset_of_mem_hat_cube hPx' hxh' hxP')
      refine ((ih _ h2).tail ?_).trans (rootStep_footprint_of_conn S hq1 (hconnJ q1 hq1) h1 hP)
      exact ⟨jnode_of_actIn hq2 hPx' (mem_Qset_of_mem_hat_cube hPx' hxh' hxP'),
        jnode_of_actIn hq1 hPx (mem_Qset_of_mem_hat_cube hPx hxh hxP), x', mem_Pset_iff.2 hxP', x,
        mem_Pset_iff.2 hxP, near_of_eq_or_adj (hxx'.imp Eq.symm Adj.symm)⟩
  intro P hP
  obtain ⟨hPc, hPJ⟩ := mem_patches.1 hP
  obtain ⟨q, ⟨hqa, q0, hat, h0, hr⟩, hpq⟩ := hJ _ hPJ
  exact main q q0 hr hat h0 _ hpq

/-- **T1. The bridge.**  If every parameter cube of `J` lies in the footprint of a centre joined to
the block `y` by a `RootChain` (the conclusion of `exists_rootChain_of_mixDiff_ne_zero`), then the
root cube of `y` and the patches of `J` are connected for Moore adjacency (`RootConnected`). -/
theorem rootConnected_of_rootChain (S : DGSetting G a ν) (hconn : HatConn G)
    {J : Finset (cubeIdx G)} {y : unitPts G}
    (hJ : ∀ p ∈ J, ∃ q, RootChain G J y q ∧ p ∈ QsetP G q) :
    RootConnected m₀ (rootIdxOf y) (patches J) :=
  rootConnected_of_rootChain_of_conn S (fun q hq => hconn q hq.1) hJ

end Bridge

section ActivityCore

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
/-- **The activity of the polymer `Y` for the root block `y` of a trace function `F`** (core): the
sum of the mixed differences `Δ_J F` over the sets `J` of parameter cubes whose hull (assigned to
the root index of `y` and the patches of `J`) is `Y`. -/
noncomputable def detActivityOf (m₀ : ℕ) (y : unitPts G) (F : DecParams G → ℂ)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
      (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y), mixDiff J F

open Classical in
/-- **T2. Resummation** (core): if `F 1` is the sum of its mixed differences, it is the sum of the
activities. -/
theorem sum_detActivityOf_eq (m₀ : ℕ) (y : unitPts G) {F : DecParams G → ℂ}
    (hsum : F (fun _ => 1) = ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, mixDiff J F) :
    F (fun _ => 1) = ∑ Y, detActivityOf m₀ y F Y := by
  rw [hsum]
  unfold detActivityOf
  exact (Finset.sum_fiberwise (Finset.univ : Finset (cubeIdx G)).powerset
    (fun J => hullOf m₀ (rootIdxOf y) (patches J)) (fun J => mixDiff J F)).symm

end ActivityCore

section Activity

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The activity of the polymer `Y` for the root block `y`** (fixed fields `φ`, `α`): the sum of
the mixed differences `Δ_J` of the rooted trace of `{y}` over the sets `J` of parameter cubes whose
hull (assigned to the root index of `y` and the patches of `J`) is `Y`. -/
noncomputable def detActivity (m₀ : ℕ) (a : ℕ → ℝ) (aT ν : ℝ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  detActivityOf m₀ y (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) Y

open Classical in
/-- **The meaning of `detActivity` is unchanged.**  The definition was refactored through the
core `detActivityOf`; this records that it equals its former body, the sum of the mixed
differences `Δ_J` of the rooted trace of `{y}` over the sets `J` of parameter cubes with hull `Y`. -/
theorem detActivity_eq_old (m₀ : ℕ) (a : ℕ → ℝ) (aT ν : ℝ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivity m₀ a aT ν φ α y Y =
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
          (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
        mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) := rfl

variable {a : ℕ → ℝ} {aT ν : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α : G.Ω 1 → ℂ}

open Classical in
/-- **T2. Resummation.**  The rooted trace of `{y}` at `s = 1` is the sum over all polymers of the
activities (the empty set `J = ∅` contributes to the hull of the root cube alone). -/
theorem sum_detActivity_eq (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hφ : IsConstraintFieldStrict G δ φ)
    (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))
    (y : unitPts G) :
    rootTrace G a aT ν (unitQ G) (unitP G) {y} (fun _ => 1) φ α =
      ∑ Y, detActivity m₀ a aT ν φ α y Y := by
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  obtain ⟨hsum, -⟩ := rootTrace_cut_expansion (N := N) S hκ hM hδ hsm hU {y} hφ hα
  exact sum_detActivityOf_eq m₀ y (F := fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) hsum

end Activity


section DecayCore

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}
variable (hdg : DGSetting G a ν) {κ : ℝ} {F : DecParams G → ℂ} {Mc : ℝ}

include hdg

/-- **The hull of a cut set with non-zero mixed difference.**  If `Δ_J` of the rooted trace of
`{y}` is non-zero, the hull of the root index of `y` and the patches of `J` contains the root cube,
is a polymer, and has size at most `2 d L |J|`. -/
theorem hull_facts_of_rootSupported (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁)
    {y : unitPts G} {J : Finset (cubeIdx G)} (hsupp : RootSupported {y} F)
    (hne : mixDiff J F ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ hullOf m₀ (rootIdxOf y) (patches J) ∧
      IsPolyDom m₀ (k + 1) (sitesOf (hullOf m₀ (rootIdxOf y) (patches J))) ∧
      dExt (hullOf m₀ (rootIdxOf y) (patches J)) ≤ (2 * d * L : ℝ) * J.card := by
  obtain ⟨y', hy', hJ⟩ := hsupp J hne
  rw [Finset.mem_singleton] at hy'
  subst hy'
  have hRC := rootConnected_of_rootChain (m₀ := m₀) hdg hconn hJ
  have hL : 2 ≤ L := by have := hdg.hL; omega
  refine ⟨rootCube_mem_hullOf _ _, isPolyDom_hullOf hN hL _ _ layer_le_of_mem_patches hRC, ?_⟩
  have h1 := dExt_hullOf_le hN hL (rootIdxOf y') (patches J) layer_le_of_mem_patches hRC
  have h2 : ((patches J).card : ℝ) ≤ J.card := by exact_mod_cast card_patches_le J
  have h3 : (0 : ℝ) ≤ 2 * d * L := by positivity
  nlinarith

open Classical in
/-- **T3. Support.**  A non-zero activity is supported on a polymer containing the root cube. -/
theorem detActivityOf_ne_zero_imp (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) {y : unitPts G}
    (hsupp : RootSupported {y} F)
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (h : detActivityOf m₀ y F Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) := by
  unfold detActivityOf at h
  obtain ⟨J, hJ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hY := (Finset.mem_filter.1 hJ).2
  obtain ⟨h1, h2, -⟩ := hull_facts_of_rootSupported (m₀ := m₀) hdg hconn hN hsupp hne
  rw [hY] at h1 h2
  exact ⟨h1, h2⟩

open Classical in
/-- **T4. Exponential decay of the activity in the size of the polymer.**  With
`Δ = detDeg d L + 1`, `z = Δ² · 2 / e^κ < 1` (that is, `e^κ > 2 Δ²`) and the rate
`λ = κ - log 2 - 2 log Δ = -log z`:
`‖detActivityOf y Y‖ ≤ M / (1 - z) · exp(-(λ / (2 d L)) dExt Y)` (core).
The slope is `a = 2 d L` and the constant `b₀ = 0` of `dExt_hullOf_le`. -/
theorem norm_detActivityOf_le (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) (y : unitPts G)
    (hsupp : RootSupported {y} F)
    (hbound : ∀ J : Finset (cubeIdx G), ‖mixDiff J F‖ ≤ Mc * (2 / Real.exp κ) ^ J.card)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ‖detActivityOf m₀ y F Y‖ ≤
      Mc / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
      Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt Y) := by
  set Δ : ℝ := ((detDeg d L + 1 : ℕ) : ℝ) with hΔ
  set zz : ℝ := Δ ^ 2 * (2 / Real.exp κ) with hzz
  have hΔ1 : (1 : ℝ) ≤ Δ := by rw [hΔ]; exact_mod_cast Nat.le_add_left 1 _
  have hzz0 : 0 < zz := by positivity
  have hd : (0 : ℝ) < 2 * d * L := by
    have h1 := hdg.hd; have h2 := hdg.hL
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  set x : ℝ := dExt Y / (2 * d * L) with hx
  set n : ℕ := ⌈x⌉₊ with hn
  -- the log of z
  have hlog : Real.log zz = -(κ - Real.log 2 - 2 * Real.log Δ) := by
    rw [hzz, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_div (by norm_num)
      (by positivity), Real.log_exp]
    push_cast; ring
  have hlt0 : Real.log zz < 0 := Real.log_neg hzz0 hz
  -- sum over the fibre
  have hmax : max (detDeg d L + 1) ({y} : Finset (unitPts G)).card = detDeg d L + 1 := by
    rw [Finset.card_singleton]; exact max_eq_left (by omega)
  have hz' : ((max (detDeg d L + 1) ({y} : Finset (unitPts G)).card : ℕ) : ℝ) ^ 2 *
      (2 / Real.exp κ) < 1 := by rw [hmax]; exact hz
  have htail := tail_norm_mixDiff_le_of hdg hsupp hbound n hz'
  rw [hmax] at htail
  have hstep1 : ‖detActivityOf m₀ y F Y‖ ≤
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
        ‖mixDiff J F‖ :=
    norm_sum_le _ _
  have hstep2 : ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
        ‖mixDiff J F‖ ≤
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter (fun J => n ≤ J.card),
        ‖mixDiff J F‖ := by
    rw [← Finset.sum_filter_ne_zero]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
    intro J hJ
    obtain ⟨hJ1, hJ2⟩ := Finset.mem_filter.1 hJ
    have hne : mixDiff J F ≠ 0 :=
      norm_ne_zero_iff.1 hJ2
    obtain ⟨-, -, hd'⟩ := hull_facts_of_rootSupported (m₀ := m₀) hdg hconn hN hsupp hne
    rw [(Finset.mem_filter.1 hJ1).2] at hd'
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), ?_⟩
    rw [hn]
    refine Nat.ceil_le.2 ?_
    rw [hx, div_le_iff₀ hd]
    linarith
  -- z ^ n ≤ exp (x log z)
  have hpow : zz ^ n ≤ Real.exp (x * Real.log zz) := by
    rw [← Real.exp_log hzz0, ← Real.exp_nat_mul, Real.exp_log hzz0]
    refine Real.exp_le_exp.2 ?_
    have hxn : x ≤ n := Nat.le_ceil x
    nlinarith
  have hxl : x * Real.log zz =
      -((κ - Real.log 2 - 2 * Real.log Δ) / (2 * d * L)) * dExt Y := by
    rw [hlog, hx]; field_simp
  have h1z : 0 < 1 - zz := by linarith
  have hMc : 0 ≤ Mc := by
    have := hbound ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  refine hstep1.trans (hstep2.trans (htail.trans ?_))
  rw [← hxl]
  calc Mc * (zz ^ n / (1 - zz))
      ≤ Mc * (Real.exp (x * Real.log zz) / (1 - zz)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow h1z.le) hMc
    _ = _ := by ring

open Classical in
/-- **T5. Summed form.**  For `0 ≤ κ''` with `κ'' · 2 d L < λ = κ - log 2 - 2 log Δ` (that is,
`κ'' < λ / (2 d L)`), the sum over all polymers of `‖detActivity y Y‖ · exp(κ'' dExt Y)` is at most
`M / (1 - Δ² · (2 / e^κ) · e^{2 d L κ''})` (core). -/
theorem sum_norm_detActivityOf_le (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) (y : unitPts G)
    (hsupp : RootSupported {y} F)
    (hbound' : ∀ J : Finset (cubeIdx G), ‖mixDiff J F‖ ≤ Mc * (2 / Real.exp κ) ^ J.card)
    {κ'' : ℝ} (hκ0 : 0 ≤ κ'')
    (hκ'' : κ'' * (2 * d * L) < κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) :
    ∑ Y, ‖detActivityOf m₀ y F Y‖ * Real.exp (κ'' * dExt Y) ≤
      Mc /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ * Real.exp (κ'' * (2 * d * L)))) := by
  set Δ : ℝ := ((detDeg d L + 1 : ℕ) : ℝ) with hΔ
  set E : ℝ := Real.exp (κ'' * (2 * d * L)) with hE
  set t : ℝ := 2 / Real.exp κ * E with ht
  have hΔ1 : (1 : ℝ) ≤ Δ := by rw [hΔ]; exact_mod_cast Nat.le_add_left 1 _
  have ht0 : 0 ≤ t := by positivity
  have hE1 : 0 < E := Real.exp_pos _
  have hzt : Δ ^ 2 * t < 1 := by
    have h0 : 0 < Δ ^ 2 * t := by positivity
    have hl : Real.log (Δ ^ 2 * t) = 2 * Real.log Δ + (Real.log 2 - κ) + κ'' * (2 * d * L) := by
      rw [ht, hE, Real.log_mul (by positivity) (by positivity), Real.log_pow,
        Real.log_mul (by positivity) (by positivity), Real.log_div (by norm_num) (by positivity),
        Real.log_exp, Real.log_exp]
      push_cast; ring
    have : Real.log (Δ ^ 2 * t) < 0 := by rw [hl]; linarith
    exact (Real.log_neg_iff h0).1 this
  have hM0 : 0 ≤ Mc := by
    have := hbound' ∅
    simp only [Finset.card_empty, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  -- per-polymer bound
  have hY : ∀ Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ), ‖detActivityOf m₀ y F Y‖ * Real.exp (κ'' * dExt Y) ≤
      ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
        ‖mixDiff J F‖ * E ^ J.card := by
    intro Y
    calc _ ≤ (∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
          (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
          ‖mixDiff J F‖) *
          Real.exp (κ'' * dExt Y) :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
          (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
          ‖mixDiff J F‖ *
            Real.exp (κ'' * dExt Y) := Finset.sum_mul _ _ _
      _ ≤ _ := by
        refine Finset.sum_le_sum fun J hJ => ?_
        by_cases hne : mixDiff J F = 0
        · rw [hne]; simp
        · obtain ⟨-, -, hd'⟩ :=
            hull_facts_of_rootSupported (m₀ := m₀) hdg hconn hN hsupp hne
          rw [(Finset.mem_filter.1 hJ).2] at hd'
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [hE, ← Real.exp_nat_mul]
          refine Real.exp_le_exp.2 ?_
          nlinarith
  -- resum over the polymers
  have hfib := Finset.sum_fiberwise (Finset.univ : Finset (cubeIdx G)).powerset
    (fun J => hullOf m₀ (rootIdxOf y) (patches J))
    (fun J => ‖mixDiff J F‖ * E ^ J.card)
  have hdeg := fun P => paramGraph_degree_le (G := G) hdg.aligned hdg.cover_sep hdg.hM
    (by have := hdg.hL; omega) P
  have hmax : max (detDeg d L + 1) 1 = detDeg d L + 1 := max_eq_left (by omega)
  have hfam := Polymer.sum_rooted_le_one (G := paramGraph G) (b := detDeg d L) (b_root := 1) hdeg
    (rootParam G y) (card_rootParam_le hdg.aligned y) ht0 (by rw [hmax]; exact hzt)
  rw [hmax] at hfam
  set R := Polymer.rootedSets (G := paramGraph G)
    ((rootParam G y : Finset (cubeIdx G)) : Set (cubeIdx G)) with hR
  have hRsub : R ⊆ (Finset.univ : Finset (cubeIdx G)).powerset :=
    fun J _ => Finset.mem_powerset.2 (Finset.subset_univ _)
  have hzero : ∀ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset, J ∉ R →
      ‖mixDiff J F‖ * E ^ J.card = 0 := by
    intro J _ hJR
    by_contra hne
    apply hJR
    have hne' : mixDiff J F ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    obtain ⟨y', hy', hJ⟩ := hsupp _ hne'
    rw [Finset.mem_singleton] at hy'
    subst hy'
    exact Polymer.mem_rootedSets.2 (rooted_of_rootChain hdg.aligned hJ)
  calc _ ≤ ∑ Y, ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
        (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
        ‖mixDiff J F‖ * E ^ J.card :=
        Finset.sum_le_sum fun Y _ => hY Y
    _ = ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset,
        ‖mixDiff J F‖ * E ^ J.card :=
        hfib
    _ = ∑ J ∈ R, ‖mixDiff J F‖ *
        E ^ J.card := (Finset.sum_subset hRsub hzero).symm
    _ ≤ ∑ J ∈ R, Mc * t ^ J.card := by
        refine Finset.sum_le_sum fun J _ => ?_
        calc _ ≤ Mc * (2 / Real.exp κ) ^ J.card * E ^ J.card :=
              mul_le_mul_of_nonneg_right (hbound' J) (by positivity)
          _ = Mc * t ^ J.card := by rw [ht, mul_pow]; ring
    _ = Mc * ∑ J ∈ R, t ^ J.card := by rw [Finset.mul_sum]
    _ ≤ Mc * (1 / (1 - Δ ^ 2 * t)) := mul_le_mul_of_nonneg_left hfam hM0
    _ = _ := by rw [mul_one_div]

end DecayCore

section Decay

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
variable (S : XSetting G a aT ν) {κ : ℝ} (hκ : 0 < κ)
  (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ : ℝ} (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hφ : IsConstraintFieldStrict G δ φ)
  {α : G.Ω 1 → ℂ}
  (hα : ∀ w, ‖α w‖ < coerciveConst d / (2 * (G.spacing (w : CTorus d L N₁ m₁ (k + 1))) ^ 2))

include S hκ hM hδ hsm hφ hα

/-- **The hull of a cut set with non-zero mixed difference.**  If `Δ_J` of the rooted trace of
`{y}` is non-zero, the hull of the root index of `y` and the patches of `J` contains the root cube,
is a polymer, and has size at most `2 d L |J|`. -/
theorem hull_facts_of_mixDiff_ne_zero (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁)
    {y : unitPts G} {J : Finset (cubeIdx G)}
    (hne : mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α) ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ hullOf m₀ (rootIdxOf y) (patches J) ∧
      IsPolyDom m₀ (k + 1) (sitesOf (hullOf m₀ (rootIdxOf y) (patches J))) ∧
      dExt (hullOf m₀ (rootIdxOf y) (patches J)) ≤ (2 * d * L : ℝ) * J.card :=
  hull_facts_of_rootSupported (m₀ := m₀) S.dg hconn hN
    (rootSupported_rootTrace S hκ hM hδ hsm hφ hα hconn {y}) hne

open Classical in
/-- **T3. Support.**  A non-zero activity is supported on a polymer containing the root cube. -/
theorem detActivity_ne_zero_imp (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) {y : unitPts G}
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (h : detActivity m₀ a aT ν φ α y Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) :=
  detActivityOf_ne_zero_imp (m₀ := m₀) S.dg hconn hN
    (rootSupported_rootTrace S hκ hM hδ hsm hφ hα hconn {y}) h

/-- The one-block bound of the mixed differences of the rooted trace. -/
theorem mixDiff_rootTrace_single_le (y : unitPts G) (J : Finset (cubeIdx G)) :
    ‖mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α)‖ ≤
      ((1 / 2 : ℝ) * N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ) *
        (2 / Real.exp κ) ^ J.card := by
  have hU := (isUnitLatticeB_unit (G := G)).toIsUnitLattice
  obtain ⟨-, hbound⟩ := rootTrace_cut_expansion (N := N) S hκ hM hδ hsm hU {y} hφ hα
  simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using hbound J

open Classical in
/-- **T4. Exponential decay of the activity in the size of the polymer.**  With
`Δ = detDeg d L + 1`, `z = Δ² · 2 / e^κ < 1` (that is, `e^κ > 2 Δ²`) and the rate
`λ = κ - log 2 - 2 log Δ = -log z`:
`‖detActivity y Y‖ ≤ M / (1 - z) · exp(-(λ / (2 d L)) dExt Y)`, `M = ½ N covBLog`.
The slope is `a = 2 d L` and the constant `b₀ = 0` of `dExt_hullOf_le`. -/
theorem norm_detActivity_le (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) (y : unitPts G)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ‖detActivity m₀ a aT ν φ α y Y‖ ≤
      (1 / 2 : ℝ) * N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
      Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt Y) :=
  norm_detActivityOf_le (m₀ := m₀) S.dg hconn hN y
    (rootSupported_rootTrace S hκ hM hδ hsm hφ hα hconn {y})
    (mixDiff_rootTrace_single_le S hκ hM hδ hsm hφ hα y) hz Y

open Classical in
/-- **T5. Summed form.**  For `0 ≤ κ''` with `κ'' · 2 d L < λ = κ - log 2 - 2 log Δ` (that is,
`κ'' < λ / (2 d L)`), the sum over all polymers of `‖detActivity y Y‖ · exp(κ'' dExt Y)` is at most
`M / (1 - Δ² · (2 / e^κ) · e^{2 d L κ''})`, `M = ½ N covBLog`. -/
theorem sum_norm_detActivity_le (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) (y : unitPts G)
    {κ'' : ℝ} (hκ0 : 0 ≤ κ'')
    (hκ'' : κ'' * (2 * d * L) < κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) :
    ∑ Y, ‖detActivity m₀ a aT ν φ α y Y‖ * Real.exp (κ'' * dExt Y) ≤
      (1 / 2 : ℝ) * N * covBLog d L (a k) (aT / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ * Real.exp (κ'' * (2 * d * L)))) :=
  sum_norm_detActivityOf_le (m₀ := m₀) S.dg hconn hN y
    (rootSupported_rootTrace S hκ hM hδ hsm hφ hα hconn {y})
    (mixDiff_rootTrace_single_le S hκ hM hδ hsm hφ hα y) hκ0 hκ''

end Decay


end Balaban.Fluctuation
