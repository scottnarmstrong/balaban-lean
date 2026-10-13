/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecCovCutSupport
public import Balaban.Localization.DecLogZero
public import Balaban.Multiscale.ConstraintLocality
public import Balaban.Localization.BoxGeometry
import Mathlib.Tactic.Linarith

/-!
# Block diagonality of the decoupled logarithm

Continuation of `DecCovCutSupport.lean` (DET-CUT-FACTOR of `notes/phase1/ROOTDET.md` §2).

* `intMat_BD`: the entrywise integral over `x > 0` of a family of matrices that are block diagonal
  for every `x > 0` is block diagonal (no integrability is needed: a vanishing entry integrates to
  zero).
* `baseline_BD`: the baseline blocks `log a_k (1 - P) + log (a_k + aT/L²) P` of `decLog`.
* `decLog_BD_of_integrand`, `CovStanding.decLog_BD_of_respects`: `decLog` is block diagonal for the
  labels, under the two provisos of `DecCovCutSupport.lean` (named hypotheses).

The decay (forest) bound and the count of cut sets per cube set are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Set MeasureTheory Real

section Integral

variable {ι : Type*}

/-- The entrywise integral over `x > 0` of matrices that are block diagonal for every `x > 0` is
block diagonal. -/
theorem intMat_BD (c : ι → Prop) (F : ℝ → Matrix ι ι ℂ)
    (hF : ∀ x, 0 < x → BD c c (F x)) :
    BD c c (intMat (volume.restrict (Ioi (0 : ℝ))) F) := by
  intro i j h
  by_contra hc
  apply h
  show ∫ x, F x i j ∂(volume.restrict (Ioi (0 : ℝ))) = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  by_contra hne
  exact hc (hF x hx i j hne)

end Integral

section Respects

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}

/-- A non-zero entry of the block-averaging matrix of layer `j` (block side `L ^ m`, nested in the
`j`-blocks) joins two sites of the same `j`-block. -/
theorem layerBlockMatrix_cell {j m : ℕ} {y y' : CTorus d L N₁ m₁ (k + 1)}
    (hnest : ∀ z, jBlock d L (N₁ * L ^ m₁) (k + 1) m z = jBlock d L (N₁ * L ^ m₁) (k + 1) m y →
      jBlock d L (N₁ * L ^ m₁) (k + 1) j z = jBlock d L (N₁ * L ^ m₁) (k + 1) j y)
    (h : layerBlockMatrix G j m y y' ≠ 0) :
    jBlock d L (N₁ * L ^ m₁) (k + 1) j y' = jBlock d L (N₁ * L ^ m₁) (k + 1) j y := by
  unfold layerBlockMatrix blockProjMatrix at h
  by_cases hc : y ∈ G.layer j ∧ y' ∈ G.layer j
  · by_cases hb : blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) y =
        blockMap (L ^ m) ((N₁ * L ^ m₁) * L ^ (k + 1 - m)) y'
    · exact hnest y' hb.symm
    · simp [hc, hb] at h
  · simp [hc] at h

/-- A non-zero entry of the averaging form at a row `y` of `Ω₁` joins `y` to a site of its own
block in its layer. -/
theorem xAvg_ne_zero_cell (a : ℕ → ℝ) (s₁ s₂ : ℝ) {y y' : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ G.Ω 1) (h : xAvgMatrix G a s₁ s₂ y y' ≠ 0) :
    SameCell (L ^ (G.layerIndex y)) y y' := by
  obtain ⟨hj1, hjK, hyl⟩ := G.layerIndex_spec hy
  set j := G.layerIndex y with hj
  by_cases hjk : j ≤ k
  · rw [xAvg_apply_low G a s₁ s₂ hj1 hjk hyl] at h
    exact (sameCell_of_jBlock_eq hjK (layerBlockMatrix_cell (fun z hz => hz)
      (right_ne_zero_of_mul h))).symm
  · have hjk' : j = k + 1 := by omega
    rw [hjk'] at hyl hj1 hjK ⊢
    rw [xAvg_apply_top G a s₁ s₂ hyl] at h
    by_cases h1 : layerBlockMatrix G (k + 1) k y y' = 0
    · rw [h1, mul_zero, zero_add] at h
      exact (sameCell_of_jBlock_eq hjK (layerBlockMatrix_cell (fun z hz => hz)
        (right_ne_zero_of_mul h))).symm
    · exact (sameCell_of_jBlock_eq hjK (layerBlockMatrix_cell
        (fun z hz => GeneratingSet.jBlock_succ_eq (by omega) hz) h1)).symm

/-- A non-zero off-diagonal entry of the x-shifted Dirichlet operator joins nearest neighbours or
two sites of one block of the layer of the row. -/
theorem xDirichlet_ne_zero_near {y y' : G.Ω 1} (hyy : y ≠ y')
    (h : xDirichletOperator G a aT x ν α y y' ≠ 0) :
    (∃ μ : Fin d, (y' : CTorus d L N₁ m₁ (k + 1)) = (y : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1 ∨
        (y : CTorus d L N₁ m₁ (k + 1)) = (y' : CTorus d L N₁ m₁ (k + 1)) + Pi.single μ 1) ∨
      SameCell (L ^ (G.layerIndex (y : CTorus d L N₁ m₁ (k + 1))))
        (y : CTorus d L N₁ m₁ (k + 1)) (y' : CTorus d L N₁ m₁ (k + 1)) := by
  have hne : (y : CTorus d L N₁ m₁ (k + 1)) ≠ y' := fun e => hyy (Subtype.ext e)
  have h' : ((xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν) y y' : ℝ) ≠ 0 := by
    intro h0
    apply h
    unfold xDirichletOperator
    simp [Green.restrictOp, Matrix.diagonal_apply_ne _ hyy, h0]
  unfold xFullMatrix at h'
  rw [Matrix.add_apply] at h'
  by_cases h1 : latticeLaplacian d ((N₁ * L ^ m₁) * L ^ (k + 1)) ν y y' = 0
  · rw [h1, zero_add] at h'
    exact Or.inr (xAvg_ne_zero_cell a _ _ y.2 h')
  · exact Or.inl (latticeLaplacian_adj ν hne h1)

/-- A site of `Ω₁` that is joined, in the sense of `xDirichlet_ne_zero_near`, to a site of the
core box `C_z` lies in the thickened cube `□̂_z` (the margin between the core and the thickened
cube). -/
theorem mem_hatI_of_near (S : XSetting G a aT ν) {z : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hz : z ∈ cubeIdx G) {y y' : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ G.Ω 1)
    (hy' : y' ∈ coreBox z)
    (hnear : (∃ μ : Fin d, y' = y + Pi.single μ 1 ∨ y' = y - Pi.single μ 1) ∨
      SameCell (L ^ (G.layerIndex y)) y y') : y ∈ hatI G z := by
  classical
  obtain ⟨hj1, hjK, hyl⟩ := G.layerIndex_spec hy
  have hL : 1 ≤ L := by have := S.dg.hL; omega
  have hin := inner_of_near S.dg.cover_sep S.dg.hM hL hz hj1 hjK hyl
    (mem_boxSet.1 hy') hnear 0 (fun μ => by simp)
  have hy0 : y + (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = y := by
    have : (intTorus (0 : Fin d → ℤ) : CTorus d L N₁ m₁ (k + 1)) = 0 := by
      funext μ; simp [intTorus_apply]
    rw [this, add_zero]
  rw [hy0] at hin
  unfold hatI
  rw [Finset.mem_filter]
  exact ⟨box_subset_hatBox z hin, hy⟩

/-- **Proviso (i) holds for the actual operator.** For a union `Y'` of nearest-neighbour
components of `Yreg s`, the x-shifted Dirichlet operator has no matrix element from a site of the
core of `s` across the boundary of `Y'`. Inputs: the cover geometry (`XSetting`, which carries
`cover_sep`, `hM`, `hL`) and `HatConn` (the thickened cubes are nearest-neighbour connected inside
`Ω₁`). No union-of-blocks hypothesis on `Y'` is needed: the sites joined by the averaging form to a
core site lie in the same thickened cube. -/
theorem hRespects_of_hatConn (S : XSetting G a aT ν) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y') :
    HRespects G a aT x ν α s Y' := by
  classical
  intro y y' hne hcore
  by_cases hyy : y = y'
  · rw [hyy]
  unfold Core at hcore
  rw [Finset.mem_biUnion] at hcore
  obtain ⟨z, hzZ, hy'z⟩ := hcore
  have hz : z ∈ cubeIdx G := (Finset.mem_filter.1 hzZ).1
  have hnear := xDirichlet_ne_zero_near hyy hne
  have hnear' : (∃ μ : Fin d, (y' : CTorus d L N₁ m₁ (k + 1)) = (y : CTorus d L N₁ m₁ (k + 1)) +
        Pi.single μ 1 ∨ (y' : CTorus d L N₁ m₁ (k + 1)) = (y : CTorus d L N₁ m₁ (k + 1)) -
        Pi.single μ 1) ∨ SameCell (L ^ (G.layerIndex (y : CTorus d L N₁ m₁ (k + 1))))
        (y : CTorus d L N₁ m₁ (k + 1)) (y' : CTorus d L N₁ m₁ (k + 1)) := by
    rcases hnear with ⟨μ, h | h⟩ | h
    · exact Or.inl ⟨μ, Or.inl h⟩
    · exact Or.inl ⟨μ, Or.inr (eq_sub_of_add_eq h.symm)⟩
    · exact Or.inr h
  have hyI := mem_hatI_of_near S hz y.2 hy'z hnear'
  have hy'I : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ hatI G z := by
    unfold hatI
    rw [Finset.mem_filter]
    exact ⟨box_subset_hatBox z (coreBox_subset_box hy'z), y'.2⟩
  have hsub : hatI G z ⊆ Yreg G s := by
    intro x hx
    unfold hatI at hx
    rw [Finset.mem_filter] at hx
    unfold Yreg
    rw [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨⟨z, hzZ, hx.1⟩, hx.2⟩
  rcases connIn_dichotomy (hconn z hz) hsub hY with h | h
  · exact ⟨fun _ => h hy'I, fun _ => h hyI⟩
  · constructor
    · intro hyY; exact absurd hyY (Finset.disjoint_left.1 h hyI)
    · intro hyY; exact absurd hyY (Finset.disjoint_left.1 h hy'I)

end Respects

section UnitLabels

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)

/-- The label of a unit point `b` of the unit lattice: the block `b` lies in `Y'`. -/
abbrev unitLabel (Y' : Finset (CTorus d L N₁ m₁ (k + 1))) (b : unitPts G) : Prop :=
  ∀ y : G.Ω 1, unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = (b : UnitTorus d L N₁ m₁ k) →
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y'

/-- `Y'` is a union of `L ^ (k+1)`-blocks of the top layer: a site of `Ω₁` in the same
`(k+1)`-block as a site of `Y'` lies in `Y'`. -/
abbrev UnionOfBlocks (Y' : Finset (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ y y' : G.Ω 1, jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y : CTorus d L N₁ m₁ (k + 1)) =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁ m₁ (k + 1)) →
    (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y'

variable {G}

theorem unitQ_label {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : UnionOfBlocks G Y') :
    BD (unitLabel G Y') (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') (unitQ G) := by
  intro b y h
  have hb : unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = (b : UnitTorus d L N₁ m₁ k) := by
    by_contra hne
    exact h (by simp [unitQ, hne])
  constructor
  · intro hc; exact hc y hb
  · intro hy y' hy'
    exact hY y y' (jBlock_eq_of_unitBlock_eq (hb.trans hy'.symm)) hy

theorem unitP_label {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : UnionOfBlocks G Y') :
    BD (unitLabel G Y') (unitLabel G Y') (unitP G) := by
  have key : ∀ b b' : unitPts G,
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) →
      unitLabel G Y' b → unitLabel G Y' b' := by
    intro b b' hbb hc y' hy'
    obtain ⟨x, hx, hxb⟩ := (mem_unitPts G).1 b.2
    have hxΩ : x ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hx
    have hxY := hc ⟨x, hxΩ⟩ hxb
    refine hY ⟨x, hxΩ⟩ y' ?_ hxY
    show jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y'
    rw [← unitBlock1_unitBlock, ← unitBlock1_unitBlock, hxb, hy', hbb]
  intro b b' h
  have hbb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = unitBlock1 (b' : UnitTorus d L N₁ m₁ k) := by
    by_contra hne
    exact h (by simp [unitP, hne])
  exact ⟨key b b' hbb, key b' b hbb.symm⟩

end UnitLabels

section Decoupled

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν κ δ : ℝ}
  {α : G.Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]

omit [Fintype κι] in
/-- The baseline blocks of `decLog` are block diagonal when `P` is. -/
theorem baseline_BD (cκ : κι → Prop) (P : Matrix κι κι ℂ) (hP : BD cκ cκ P) (r r' : ℂ) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (r • (1 - liftOp N P) + r' • liftOp N P) :=
  ((BD.one _).sub (BD.liftOp hP)).smul r |>.add ((BD.liftOp hP).smul r')

/-- **`decLog` is block diagonal**, given block diagonality of the integrand `decCov - covA` for
all `x > 0` (that is the content of `decCov_sub_BD` under the provisos). -/
theorem decLog_BD_of_integrand (cκ : κι → Prop) (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ)
    (hP : BD cκ cκ P)
    (hint : ∀ x : ℝ, 0 < x →
      BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
        (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decLog G a aT ν α s φ Q P) := by
  unfold decLog
  exact (baseline_BD cκ P hP _ _).sub (intMat_BD _ _ hint)

/-- **`decLog` is block diagonal for a union `Y'` of nearest-neighbour components of `Yreg s`**,
under the two named provisos: `HRespects` for every `x > 0` and the label compatibility of `Q`, `P`
(`hQ`, `hP`). The standing hypotheses are `CovStanding` and `HatConn`. -/
theorem CovStanding.decLog_BD_of_respects {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hH : ∀ x : ℝ, 0 < x → HRespects G a aT x ν α s Y') (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decLog G a aT ν α s φ Q P) :=
  decLog_BD_of_integrand cκ Q P hP fun x hx =>
    H.decCov_sub_BD hx.le hconn hY (hH x hx) cκ hQ hP

/-- **`decLog` of the step is block diagonal** for the unit lattice. Hypotheses: `CovStanding` for
`Q = unitQ G`, `P = unitP G` (all `x ≥ 0`), `HatConn`, `Y'` a union of nearest-neighbour
components of `Yreg s`, and the named property `UnionOfBlocks G Y'` (when it holds: see the module
doc). The proviso (i) is discharged by `hRespects_of_hatConn`. -/
theorem CovStanding.decLog_BD_unit_of_unionOfBlocks
    (H : CovStanding G a aT ν α κ s δ φ (unitQ G) (unitP G)) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hYblk : UnionOfBlocks G Y') :
    BD (fun p : unitPts G × Fin N => unitLabel G Y' p.1)
      (fun p : unitPts G × Fin N => unitLabel G Y' p.1) (decLog G a aT ν α s φ (unitQ G) (unitP G)) :=
  H.decLog_BD_of_respects hconn hY
    (fun x hx => hRespects_of_hatConn (H.fam x hx.le).st hconn hY) (unitLabel G Y')
    (unitQ_label hYblk) (unitP_label hYblk)

end Decoupled

end Balaban.Localization
