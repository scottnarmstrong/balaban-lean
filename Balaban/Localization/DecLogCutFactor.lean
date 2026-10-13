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
# Block diagonality and locality of the decoupled logarithm

Continuation of `DecCovCutSupport.lean` (DET-CUT-FACTOR of `notes/phase1/ROOTDET.md` §2).

**Block diagonality.**

* `intMat_BD`: the entrywise integral over `x > 0` of matrices that are block diagonal for every
  `x > 0` is block diagonal (a vanishing entry integrates to zero; no integrability is needed).
* `baseline_BD`, `decLog_BD_of_integrand`: the baseline blocks `log a_k (1 - P) + log (a_k + b) P`
  and the whole of `decLog`.
* `CovStanding.decLog_BD_of_respects`: `decLog` is block diagonal for the labels of a union `Y'` of
  nearest-neighbour components of `Yreg s`, under the two provisos of `DecCovCutSupport.lean`.

**Proviso (i), discharged** (`hRespects_of_hatConn`). `HRespects` holds for the actual operator
`xDirichletOperator`, from `XSetting` (cover separation `cover_sep`, `hM`, `hL`) and `HatConn`
alone. A non-zero matrix element joins nearest neighbours (`latticeLaplacian_adj`) or two sites in
one block of the layer of the row (`xAvg_ne_zero_cell`); the site is then an interior point of the
cover box of any core site it is joined to (`inner_of_near`, `mem_hatI_of_near`), so it lies in the
thickened cube `□̂_z`, which is connected inside `Ω₁` and lies in one component or misses it
(`connIn_dichotomy`). No union-of-blocks hypothesis on `Y'` is needed for this proviso.

**Proviso (ii), for the unit lattice** (`unitQ_label`, `unitP_label`). With the label
`unitLabel G Y' b := the unit block b lies in Y'` the matrices `unitQ G`, `unitP G` respect the
labels if `Y'` is a union of `L^(k+1)`-blocks of the top layer (`UnionOfBlocks G Y'`: a site of `Ω₁`
in the same `(k+1)`-block as a site of `Y'` lies in `Y'`). Union of unit blocks alone does not
suffice, because `unitP` averages over the `L` unit blocks of one `(k+1)`-block. This property is
**not proved** to hold for a component of `Yreg s`; it is kept as the named hypothesis `hYblk`. The
mathematical reason it holds: a top-layer site lies in the thickened cube of a cube of scale
`q.1` only for `q.1 ≥ k` (layer bound), and then the cell index description of the box shows that
the thickened cube is a union of `L^(q.1+1)`-blocks (the thickening `3 L² ℓ_j` is a multiple of
the block side), hence of `L^(k+1)`-blocks; a component is a union of such thickened cubes
(`hatI` connected). That cell computation for the thickened radius is not formalized here.
`CovStanding.decLog_BD_unit_of_unionOfBlocks` is the resulting theorem (named hypotheses:
`CovStanding` at all `x ≥ 0`, `HatConn`, `UnionOfBlocks`). Any union of components (not only a
single one) works: only `IsNnComp (Yreg s) Y'` is used.

**Locality.** `BAgree` and its calculus (`mul`, `inv`, `liftOp`, ...): block diagonal matrices
with equal matrix elements on a block have products and inverses with equal matrix elements there.
`Gsx_agree` (from `Gsx_local`), `commK_Gsx_agree`, `CovStanding.decCov_sub_agree`,
`CovStanding.decLog_agree`: for two data `(s, α, φ)`, `(s', α', φ')` with `Y'` a union of
components of both `Yreg s` and `Yreg s'`, `sProd` agreeing on the cubes inside `Y'` and potentials
and fields agreeing on `Y'`, the matrices `decLog` have equal matrix elements between labelled
coarse sites. `CovStanding.decLog_row_eq_baseline`: for a coarse site whose label (relative to
`Y' = Yreg s`) is false the row of `decLog` is the cut-independent baseline.

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

/-- `UnionOfBlocks` is satisfiable: the empty set and the whole torus. -/
theorem unionOfBlocks_empty : UnionOfBlocks G (∅ : Finset (CTorus d L N₁ m₁ (k + 1))) :=
  fun _ _ _ h => absurd h (Finset.notMem_empty _)

theorem unionOfBlocks_univ : UnionOfBlocks G (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))) :=
  fun _ _ _ _ => Finset.mem_univ _

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

section Agree

variable {ι ι' ι'' : Type*}

/-- `M` and `M'` have the same matrix elements between sites carrying the labels `c`, `c'`. -/
abbrev BAgree (c : ι → Prop) (c' : ι' → Prop) (M M' : Matrix ι ι' ℂ) : Prop :=
  ∀ i j, c i → c' j → M i j = M' i j

theorem BAgree.rfl' {c : ι → Prop} {c' : ι' → Prop} (M : Matrix ι ι' ℂ) : BAgree c c' M M :=
  fun _ _ _ _ => Eq.refl _

theorem BAgree.add {c : ι → Prop} {c' : ι' → Prop} {M M' N N' : Matrix ι ι' ℂ}
    (h : BAgree c c' M M') (h' : BAgree c c' N N') : BAgree c c' (M + N) (M' + N') := by
  intro i j hi hj; simp [Matrix.add_apply, h i j hi hj, h' i j hi hj]

theorem BAgree.sub {c : ι → Prop} {c' : ι' → Prop} {M M' N N' : Matrix ι ι' ℂ}
    (h : BAgree c c' M M') (h' : BAgree c c' N N') : BAgree c c' (M - N) (M' - N') := by
  intro i j hi hj; simp [Matrix.sub_apply, h i j hi hj, h' i j hi hj]

theorem BAgree.smul {c : ι → Prop} {c' : ι' → Prop} {M M' : Matrix ι ι' ℂ} (r : ℂ)
    (h : BAgree c c' M M') : BAgree c c' (r • M) (r • M') := by
  intro i j hi hj; simp [Matrix.smul_apply, h i j hi hj]

theorem BAgree.transpose {c : ι → Prop} {c' : ι' → Prop} {M M' : Matrix ι ι' ℂ}
    (h : BAgree c c' M M') : BAgree c' c Mᵀ M'ᵀ := by
  intro i j hi hj; simp [Matrix.transpose_apply, h j i hj hi]

theorem BAgree.mul [Fintype ι'] {c : ι → Prop} {c' : ι' → Prop} {c'' : ι'' → Prop}
    {M M' : Matrix ι ι' ℂ} {N N' : Matrix ι' ι'' ℂ} (hM : BD c c' M) (hM' : BD c c' M')
    (h : BAgree c c' M M') (h' : BAgree c' c'' N N') : BAgree c c'' (M * N) (M' * N') := by
  intro i j hi hj
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : c' k
  · rw [h i k hi hk, h' k j hk hj]
  · have e1 : M i k = 0 := by
      by_contra hne; exact hk ((hM i k hne).1 hi)
    have e2 : M' i k = 0 := by
      by_contra hne; exact hk ((hM' i k hne).1 hi)
    rw [e1, e2, zero_mul, zero_mul]

theorem BAgree.liftOp {N : ℕ} [DecidableEq ι] [DecidableEq ι'] {c : ι → Prop} {c' : ι' → Prop}
    {M M' : Matrix ι ι' ℂ} (h : BAgree c c' M M') :
    BAgree (fun p : ι × Fin N => c p.1) (fun p : ι' × Fin N => c' p.1)
      (fun p q => if p.2 = q.2 then M p.1 q.1 else 0)
      (fun p q => if p.2 = q.2 then M' p.1 q.1 else 0) := by
  intro p q hp hq
  by_cases hpq : p.2 = q.2
  · simp only [hpq, ite_true]; exact h _ _ hp hq
  · simp [hpq]

/-- **The inverse of block-diagonal matrices that agree on the block `c` agrees there.** -/
theorem BAgree.inv [Fintype ι] [DecidableEq ι] {c : ι → Prop} {M M' : Matrix ι ι ℂ}
    (hM : BD c c M) (hM' : BD c c M') (hU : IsUnit M) (hU' : IsUnit M')
    (h : BAgree c c M M') : BAgree c c M⁻¹ M'⁻¹ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet' : IsUnit M'.det := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  have hX' : BD c c M'⁻¹ := hM'.inv hU'
  intro i j hi hj
  -- `M'⁻¹ (M' M⁻¹) = M⁻¹`
  have e1 : M⁻¹ = M'⁻¹ * (M' * M⁻¹) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet', Matrix.one_mul]
  have e2 : ∀ k, c k → (M' * M⁻¹) k j = (1 : Matrix ι ι ℂ) k j := by
    intro k hk
    rw [← Matrix.mul_nonsing_inv M hdet, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : c l
    · rw [h k l hk hl]
    · have e1 : M k l = 0 := by
        by_contra hne; exact hl ((hM k l hne).1 hk)
      have e2 : M' k l = 0 := by
        by_contra hne; exact hl ((hM' k l hne).1 hk)
      rw [e1, e2]
  have e3 : ∑ k, M'⁻¹ i k * (M' * M⁻¹) k j = ∑ k, M'⁻¹ i k * (1 : Matrix ι ι ℂ) k j := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : c k
    · rw [e2 k hk]
    · have : M'⁻¹ i k = 0 := by
        by_contra hne; exact hk ((hX' i k hne).1 hi)
      rw [this, zero_mul, zero_mul]
  rw [e1, Matrix.mul_apply, e3, ← Matrix.mul_apply, Matrix.mul_one]
end Agree

section DataAgree

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν κ κ' δ δ' : ℝ}
  {α α' : G.Ω 1 → ℂ} {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- Every interaction cube with a non-zero factor lies inside or outside a union of components of
`Yreg s` (the geometric input of `dg5x_local`). -/
theorem subI_or_disjI_of_comp (hconn : HatConn G) {Y' : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hY : IsNnComp (Yreg G s) Y') {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    (hs : sProd G s q ≠ 0) : SubI G (intBox q) Y' ∨ DisjI G (intBox q) Y' := by
  classical
  have hzZ : q ∈ Zs G s := Finset.mem_filter.2 ⟨hq, hs⟩
  have hsub : hatI G q ⊆ Yreg G s := by
    intro y hy
    unfold hatI at hy
    rw [Finset.mem_filter] at hy
    unfold Yreg
    rw [Finset.mem_filter, Finset.mem_biUnion]
    exact ⟨⟨q, hzZ, hy.1⟩, hy.2⟩
  rcases connIn_dichotomy (hconn q hq) hsub hY with h | h
  · left
    intro y hy
    exact h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox q hy, y.2⟩)
  · right
    intro y hy hyY
    exact Finset.disjoint_left.1 h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨box_subset_hatBox q hy, y.2⟩) hyY

/-- **Locality of `Gsx` in the cut parameters, the potential and the argument.** If `Y'` is a union
of components of both `Yreg s` and `Yreg s'`, the factors `sProd` agree on the cubes inside `Y'`
and the potentials agree on `Y'`, then `Gsx` has the same matrix elements `(y, y')`, `y ∈ Y'`. -/
theorem Gsx_agree (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G) (hα : AdmPot G α)
    (hα' : AdmPot G α') (hU : IsUnit (1 - Kcalx G a aT x ν α s))
    (hU' : IsUnit (1 - Kcalx G a aT x ν α' s'))
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    {y y' : G.Ω 1} (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') :
    Gsx G a aT x ν α s y y' = Gsx G a aT x ν α' s' y y' := by
  have h := Gsx_local S hx hα hα' hU hU' (Y := Y') (fun q hq hne => by
      rcases hne with h | h
      · exact subI_or_disjI_of_comp hconn hY hq h
      · exact subI_or_disjI_of_comp hconn hY' hq h) hs hA
    (f := Pi.single y' (1 : ℂ)) (f' := Pi.single y' (1 : ℂ)) (fun _ _ => rfl) y hy
  rwa [mulVec_single_apply, mulVec_single_apply] at h

/-- The x-shifted Dirichlet operators of two potentials agree between sites where the potentials
agree. -/
theorem xDirichlet_agree {y y' : G.Ω 1} (hyy : y = y' → α y = α' y) :
    xDirichletOperator G a aT x ν α y y' = xDirichletOperator G a aT x ν α' y y' := by
  unfold xDirichletOperator
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  by_cases h : y = y'
  · subst h; simp [hyy rfl]
  · simp [h]

section Assembly

variable (S : XSetting G a aT ν) (hx : 0 ≤ x) (hconn : HatConn G) (hα : AdmPot G α)
  (hα' : AdmPot G α')
  (hU : IsUnit (1 - Kcalx G a aT x ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x ν α' s'))
  {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
  (hY' : IsNnComp (Yreg G s') Y')
  (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
  (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
  (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y)

include S hx hconn hα hα' hU hU' hY hY' hs hA

/-- The commutator term `K_x(φ₀) G` has the same matrix elements on `Y'`. -/
theorem commK_Gsx_agree (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) :
    BAgree (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y')
      (commK (xDirichletOperator G a aT x ν α) (restrictField G φ) *
        liftOp N (Gsx G a aT x ν α s))
      (commK (xDirichletOperator G a aT x ν α') (restrictField G φ') *
        liftOp N (Gsx G a aT x ν α' s')) := by
  intro y q hy hq
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨p1, p2⟩ := p
  by_cases hp : (p1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y'
  · rw [commK_apply, commK_apply]
    have e1 := Gsx_agree S hx hconn hα hα' hU hU' hY hY' hs hA (y' := q.1) hp
    have e2 := xDirichlet_agree (a := a) (aT := aT) (x := x) (ν := ν) (α := α) (α' := α')
      (y := y) (y' := p1) (fun _ => hA y hy)
    have e3 : restrictField G φ y p2 = restrictField G φ' y p2 := by
      show φ (y : CTorus d L N₁ m₁ (k + 1)) p2 = φ' (y : CTorus d L N₁ m₁ (k + 1)) p2
      rw [hφ _ hy]
    have e4 : restrictField G φ p1 p2 = restrictField G φ' p1 p2 := by
      show φ (p1 : CTorus d L N₁ m₁ (k + 1)) p2 = φ' (p1 : CTorus d L N₁ m₁ (k + 1)) p2
      rw [hφ _ hp]
    simp only [liftOp, e1, e2, e3, e4]
  · have h0 : ∀ (β : G.Ω 1 → ℂ) (r : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ),
        IsNnComp (Yreg G r) Y' → AdmPot G β → IsUnit (1 - Kcalx G a aT x ν β r) →
        liftOp N (Gsx G a aT x ν β r) (p1, p2) q = 0 := by
      intro β r hr hβ hUr
      simp only [liftOp]
      split_ifs
      · by_contra hne
        exact hp ((Gsx_BD S hx hconn hβ hUr hr p1 q.1 hne).2 hq)
      · rfl
    rw [h0 α s hY hα hU, h0 α' s' hY' hα' hU', mul_zero, mul_zero]

end Assembly

section Main

variable {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

/-- **Locality of the correction `decCov - covA`.** Two data `(s, α, φ)`, `(s', α', φ')` with the
standing hypotheses; `Y'` a union of components of both `Yreg s` and `Yreg s'`; the cut factors
`sProd` agree on the cubes inside `Y'`, the potentials and fields agree on `Y'`; `Q`, `P` respect
the labels `cκ`. Then `decCov - covA` has the same matrix elements between labelled coarse sites
for both data (and both are block diagonal). -/
theorem CovStanding.decCov_sub_agree
    (H : CovStanding G a aT ν α κ s δ φ Q P) (H' : CovStanding G a aT ν α' κ' s' δ' φ' Q P)
    (hx : 0 ≤ x) (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BAgree (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))
      (decCov G a aT x ν α' s' φ' Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
  classical
  have S := (H.fam x hx).st
  have S' := (H'.fam x hx).st
  have hα := (H.fam x hx).pot
  have hα' := (H'.fam x hx).pot
  have hU := (H.fam x hx).isUnit_one_sub
  have hU' := (H'.fam x hx).isUnit_one_sub
  have hH := hRespects_of_hatConn (x := x) (α := α) S hconn hY
  have hH' := hRespects_of_hatConn (x := x) (α := α') S hconn hY'
  have hM := H.decM_isUnit' hx
  have hM' := H'.decM_isUnit' hx
  set cY : G.Ω 1 → Prop := fun y => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' with hcY
  set cYf : G.Ω 1 × Fin N → Prop := fun p => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Y' with hcYf
  -- block diagonality of the pieces, for both data
  have hGB := liftOp_Gsx_BD (N := N) S hx hconn hα hU hY
  have hGB' := liftOp_Gsx_BD (N := N) S' hx hconn hα' hU' hY'
  have hFM := fieldMul_BD (N := N) cY (restrictField G φ)
  have hFM' := fieldMul_BD (N := N) cY (restrictField G φ')
  have hRB := commK_Gsx_BD (N := N) (φ := φ) S hx hconn hα hU hY hH
  have hRB' := commK_Gsx_BD (N := N) (φ := φ') S' hx hconn hα' hU' hY' hH'
  have hMB := decM_BD (N := N) (φ := φ) S hx hconn hα hU hY hH
  have hMB' := decM_BD (N := N) (φ := φ') S' hx hconn hα' hU' hY' hH'
  have hNB := decN_BD (N := N) (φ := φ) S hx hconn hα hU hY hH
  have hNB' := decN_BD (N := N) (φ := φ') S' hx hconn hα' hU' hY' hH'
  have hMiB := hMB.inv hM
  have hMiB' := hMB'.inv hM'
  -- agreement of the pieces
  have hGag : BAgree cY cY (Gsx G a aT x ν α s) (Gsx G a aT x ν α' s') :=
    fun y y' hy _ => Gsx_agree S hx hconn hα hα' hU hU' hY hY' hs hA hy
  have hLag : BAgree cYf cYf (liftOp N (Gsx G a aT x ν α s)) (liftOp N (Gsx G a aT x ν α' s')) :=
    BAgree.liftOp hGag
  have hFMag : BAgree cYf cY (fieldMul (restrictField G φ)) (fieldMul (restrictField G φ')) := by
    intro p y hp hy
    unfold fieldMul
    by_cases h : p.1 = y
    · simp only [h, ite_true]
      show φ (y : CTorus d L N₁ m₁ (k + 1)) p.2 = φ' (y : CTorus d L N₁ m₁ (k + 1)) p.2
      rw [hφ _ hy]
    · simp [h]
  have hRag := commK_Gsx_agree (N := N) S hx hconn hα hα' hU hU' hY hY' hs hA hφ
  have hMag : BAgree cY cY (decM G a aT x ν α s φ) (decM G a aT x ν α' s' φ') := by
    unfold decM constraintM
    exact (BAgree.mul hFM.transpose hFM'.transpose hFMag.transpose hFMag).sub
      (BAgree.mul hRB hRB' hRag hFMag)
  have hNag : BAgree cY cYf (decN G a aT x ν α s φ) (decN G a aT x ν α' s' φ') := by
    unfold decN constraintN
    exact hFMag.transpose.sub hRag
  have hMiag := BAgree.inv hMB hMB' hM hM' hMag
  have hPiag : BAgree cYf cYf (decPi G a aT x ν α s φ) (decPi G a aT x ν α' s' φ') := by
    unfold decPi
    exact BAgree.mul ((hGB.mul hFM).mul hMiB) ((hGB'.mul hFM').mul hMiB')
      (BAgree.mul (hGB.mul hFM) (hGB'.mul hFM') (BAgree.mul hGB hGB' hLag hFMag) hMiag) hNag
  have hTB := hGB.sub (decPi_BD S hx hconn hα hU hY hH hM)
  have hTB' := hGB'.sub (decPi_BD S' hx hconn hα' hU' hY' hH' hM')
  have hTag := hLag.sub hPiag
  have hPl : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1) (liftOp N P) :=
    BD.liftOp hP
  have hAB : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
    unfold covA
    exact ((BD.one _).sub hPl).smul _ |>.add (hPl.smul _)
  have hQl : BD (fun p : κι × Fin N => cκ p.1) cYf (liftRect N Q) := BD.liftOp hQ
  unfold decCov
  rw [add_sub_cancel_left, add_sub_cancel_left]
  refine BAgree.smul _ ?_
  refine BAgree.mul (((hAB.mul hQl).mul hTB).mul hQl.transpose) (((hAB.mul hQl).mul hTB').mul hQl.transpose)
    (BAgree.mul ((hAB.mul hQl).mul hTB) ((hAB.mul hQl).mul hTB')
      (BAgree.mul (hAB.mul hQl) (hAB.mul hQl)
        (BAgree.mul hAB hAB (BAgree.rfl' _) (BAgree.rfl' _)) hTag) (BAgree.rfl' _)) (BAgree.rfl' _)

/-- **Locality of the decoupled logarithm.** Under the hypotheses of `CovStanding.decCov_sub_agree`
(for the cut parameters, potential and field), `decLog` has the same matrix elements between
labelled coarse sites for the two data. The baseline blocks do not depend on them, and the
`x`-integrands agree for every `x ≥ 0`. -/
theorem CovStanding.decLog_agree
    (H : CovStanding G a aT ν α κ s δ φ Q P) (H' : CovStanding G a aT ν α' κ' s' δ' φ' Q P)
    (hconn : HatConn G)
    {Y' : Finset (CTorus d L N₁ m₁ (k + 1))} (hY : IsNnComp (Yreg G s) Y')
    (hY' : IsNnComp (Yreg G s') Y')
    (hs : ∀ q ∈ cubeIdx G, SubI G (intBox q) Y' → sProd G s q = sProd G s' q)
    (hA : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y' → α y = α' y)
    (hφ : ∀ y : CTorus d L N₁ m₁ (k + 1), y ∈ Y' → φ y = φ' y) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y') Q) (hP : BD cκ cκ P) :
    BAgree (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (decLog G a aT ν α s φ Q P) (decLog G a aT ν α' s' φ' Q P) := by
  unfold decLog
  refine BAgree.sub (BAgree.rfl' _) ?_
  intro p q hp hq
  show ∫ x, _ ∂(volume.restrict (Ioi (0 : ℝ))) = ∫ x, _ ∂(volume.restrict (Ioi (0 : ℝ)))
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact H.decCov_sub_agree H' (Set.mem_Ioi.1 hx).le hconn hY hY' hs hA hφ cκ hQ hP p q hp hq

/-- Rows of a product vanish if the rows of the left factor do. -/
theorem mul_apply_eq_zero_of_row {ι ι' ι'' : Type*} [Fintype ι'] {M : Matrix ι ι' ℂ}
    {N : Matrix ι' ι'' ℂ} {i : ι} (h : ∀ j, M i j = 0) (j : ι'') : (M * N) i j = 0 := by
  simp [Matrix.mul_apply, h]

/-- **Outside the footprint the correction vanishes.** Take `Y' = Yreg s`, the union of all
components. For a coarse site whose label is false (its block does not lie in `Yreg s`), the
correction `decCov - covA` has no matrix elements in its row: `G_s` and `Π_s` have rows supported in
the core. -/
theorem CovStanding.decCov_sub_row_eq_zero {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hx : 0 ≤ x) (hconn : HatConn G)
    (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg G s) Q)
    (hP : BD cκ cκ P) {p : κι × Fin N} (hp : ¬ cκ p.1) (q : κι × Fin N) :
    (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) p q = 0 := by
  classical
  have hY : IsNnComp (Yreg G s) (Yreg G s) := ⟨subset_rfl, fun _ _ _ hy _ => hy⟩
  have hS := (H.fam x hx).st
  have hH := hRespects_of_hatConn (x := x) (α := α) hS hconn hY
  have hα := (H.fam x hx).pot
  have hU := (H.fam x hx).isUnit_one_sub
  have hM := H.decM_isUnit' hx
  have hPl : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1) (liftOp N P) :=
    BD.liftOp hP
  have hAB : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
    unfold covA
    exact ((BD.one _).sub hPl).smul _ |>.add (hPl.smul _)
  have hQl : BD (fun p : κι × Fin N => cκ p.1)
      (fun p : G.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg G s) (liftRect N Q) :=
    BD.liftOp hQ
  -- rows of the correction `liftOp Gsx - decPi` outside the core vanish
  have hT : ∀ (w : G.Ω 1 × Fin N), (w.1 : CTorus d L N₁ m₁ (k + 1)) ∉ Yreg G s → ∀ r,
      (liftOp N (Gsx G a aT x ν α s) - decPi G a aT x ν α s φ) w r = 0 := by
    intro w hw r
    have hcore : (w.1 : CTorus d L N₁ m₁ (k + 1)) ∉ Core G s := fun h => hw (mem_Yreg_of_mem_core _ h)
    have hL : ∀ r, liftOp N (Gsx G a aT x ν α s) w r = 0 := by
      intro r; simp only [liftOp]; split_ifs
      · exact Gsx_apply_eq_zero_of_not_core _ _ hcore
      · rfl
    rw [Matrix.sub_apply, hL r]
    unfold decPi
    rw [sub_eq_zero]
    refine (mul_apply_eq_zero_of_row (i := w) (fun r' => ?_) r).symm
    refine mul_apply_eq_zero_of_row (i := w) (fun r' => ?_) r'
    refine mul_apply_eq_zero_of_row (i := w) (fun r' => ?_) r'
    exact hL r'
  unfold decCov
  rw [add_sub_cancel_left, Matrix.smul_apply]
  refine smul_eq_zero_of_right _ ?_
  have hrow : ∀ y, ((covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q) *
      (liftOp N (Gsx G a aT x ν α s) - decPi G a aT x ν α s φ)) p y = 0 := by
    intro y
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases h : (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q) p w = 0
    · rw [h, zero_mul]
    · have hw : (w.1 : CTorus d L N₁ m₁ (k + 1)) ∉ Yreg G s := fun hw =>
        hp (((hAB.mul hQl) p w h).2 hw)
      rw [hT w hw y, mul_zero]
  exact mul_apply_eq_zero_of_row (fun r => mul_apply_eq_zero_of_row hrow r) q

/-- **`decLog` outside the footprint is the baseline.** For a coarse site whose label (relative to
`Yreg s`) is false, the row of `decLog` equals that of the cut-independent baseline blocks. -/
theorem CovStanding.decLog_row_eq_baseline {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) (hconn : HatConn G) (cκ : κι → Prop)
    (hQ : BD cκ (fun y : G.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg G s) Q)
    (hP : BD cκ cκ P) {p : κι × Fin N} (hp : ¬ cκ p.1) (q : κι × Fin N) :
    decLog G a aT ν α s φ Q P p q =
      (((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
        ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P) p q := by
  unfold decLog
  rw [Matrix.sub_apply]
  have : intMat (volume.restrict (Ioi (0 : ℝ)))
      (fun x => decCov G a aT x ν α s φ Q P -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) p q = 0 := by
    show ∫ x, _ ∂(volume.restrict (Ioi (0 : ℝ))) = 0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact H.decCov_sub_row_eq_zero (Set.mem_Ioi.1 hx).le hconn cκ hQ hP hp q
  rw [this, sub_zero]


end Main

end DataAgree

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
