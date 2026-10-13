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

/-- **The footprint of an active centre is Moore connected inside `J`.**  Any two parameter cubes of
the footprint `𝒬(q) ⊆ J` are joined by a chain of Moore-touching patches of `J`. -/
theorem rootStep_footprint (S : DGSetting G a ν) (hconn : HatConn G) {J : Finset (cubeIdx G)}
    {z : RootIdx d L N₁ m₁ (k + 1)} {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActIn G J q)
    {P P' : cubeIdx G} (hP : P ∈ QsetP G q) (hP' : P' ∈ QsetP G q) :
    Relation.ReflTransGen (rootStep m₀ z (patches J)) (some P.1) (some P'.1) := by
  have site : ∀ R : cubeIdx G, R ∈ QsetP G q → ∃ y ∈ hatI G q, y ∈ cubeP R.1 := by
    intro R hR
    obtain ⟨-, y, hy, hbox⟩ := mem_Qset.1 (mem_QsetP.1 hR)
    have hyc : y ∈ cubeP R.1 := mem_cubeP.2 hy
    exact ⟨y, mem_hatI_iff.2 ⟨mem_boxSet.2 hbox, cubeP_subset_Ω S R.2 hyc⟩, hyc⟩
  obtain ⟨y, hy, hyP⟩ := site P hP
  obtain ⟨y', hy', hyP'⟩ := site P' hP'
  exact rootStep_hat S.aligned hq (hconn q hq.1 y hy y' hy') hy P.1 P.2 hyP P'.1 P'.2 hyP'

/-- **T1. The bridge.**  If every parameter cube of `J` lies in the footprint of a centre joined to
the block `y` by a `RootChain` (the conclusion of `exists_rootChain_of_mixDiff_ne_zero`), then the
root cube of `y` and the patches of `J` are connected for Moore adjacency (`RootConnected`). -/
theorem rootConnected_of_rootChain (S : DGSetting G a ν) (hconn : HatConn G)
    {J : Finset (cubeIdx G)} {y : unitPts G}
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
      exact (Relation.ReflTransGen.single hroot).trans (rootStep_footprint S hconn hq0 hwQ hP)
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
      refine ((ih _ h2).tail ?_).trans (rootStep_footprint S hconn hq1 h1 hP)
      exact ⟨jnode_of_actIn hq2 hPx' (mem_Qset_of_mem_hat_cube hPx' hxh' hxP'),
        jnode_of_actIn hq1 hPx (mem_Qset_of_mem_hat_cube hPx hxh hxP), x', mem_Pset_iff.2 hxP', x,
        mem_Pset_iff.2 hxP, near_of_eq_or_adj (hxx'.imp Eq.symm Adj.symm)⟩
  intro P hP
  obtain ⟨hPc, hPJ⟩ := mem_patches.1 hP
  obtain ⟨q, ⟨hqa, q0, hat, h0, hr⟩, hpq⟩ := hJ _ hPJ
  exact main q q0 hr hat h0 _ hpq

end Bridge

section Activity

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
/-- **The activity of the polymer `Y` for the root block `y`** (fixed fields `φ`, `α`): the sum of
the mixed differences `Δ_J` of the rooted trace of `{y}` over the sets `J` of parameter cubes whose
hull (assigned to the root index of `y` and the patches of `J`) is `Y`. -/
noncomputable def detActivity (m₀ : ℕ) (a : ℕ → ℝ) (aT ν : ℝ)
    (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (α : G.Ω 1 → ℂ) (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
      (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
    mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α)

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
  rw [hsum]
  unfold detActivity
  exact (Finset.sum_fiberwise (Finset.univ : Finset (cubeIdx G)).powerset
    (fun J => hullOf m₀ (rootIdxOf y) (patches J))
    (fun J => mixDiff J (fun s => rootTrace G a aT ν (unitQ G) (unitP G) {y} s φ α))).symm

end Activity

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
      dExt (hullOf m₀ (rootIdxOf y) (patches J)) ≤ (2 * d * L : ℝ) * J.card := by
  obtain ⟨y', hy', hJ⟩ := exists_rootChain_of_mixDiff_ne_zero S hκ hM hδ hsm hφ hα hconn {y} hne
  rw [Finset.mem_singleton] at hy'
  subst hy'
  have hRC := rootConnected_of_rootChain (m₀ := m₀) S.dg hconn hJ
  have hL : 2 ≤ L := by have := S.dg.hL; omega
  refine ⟨rootCube_mem_hullOf _ _, isPolyDom_hullOf hN hL _ _ layer_le_of_mem_patches hRC, ?_⟩
  have h1 := dExt_hullOf_le hN hL (rootIdxOf y') (patches J) layer_le_of_mem_patches hRC
  have h2 : ((patches J).card : ℝ) ≤ J.card := by exact_mod_cast card_patches_le J
  have h3 : (0 : ℝ) ≤ 2 * d * L := by positivity
  nlinarith

open Classical in
/-- **T3. Support.**  A non-zero activity is supported on a polymer containing the root cube. -/
theorem detActivity_ne_zero_imp (hconn : HatConn G) (hN : L ^ m₀ ∣ N₁) {y : unitPts G}
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (h : detActivity m₀ a aT ν φ α y Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) := by
  unfold detActivity at h
  obtain ⟨J, hJ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hY := (Finset.mem_filter.1 hJ).2
  obtain ⟨h1, h2, -⟩ := hull_facts_of_mixDiff_ne_zero (m₀ := m₀) S hκ hM hδ hsm hφ hα hconn hN hne
  rw [hY] at h1 h2
  exact ⟨h1, h2⟩

end Decay

end Balaban.Fluctuation
