/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovUnit
public import Balaban.Localization.DecEquivLat
public import Balaban.Background.EquivarianceLat
public import Balaban.Localization.DecEquivTranslateStep
public import Balaban.Localization.DecEquivPermuteStep

/-!
# Covariance of the unit-lattice incidence matrices under a lattice symmetry

Let `S : LatSymm G G σ` be a lattice symmetry of a generating set `G` of level `k + 1`. The
matrices `unitQ G` (block average, `Ω₁ → Λ`) and `unitP G` (projection onto the constants of the
`L`-blocks of the unit points) depend on the sites only through the two incidence relations
"the site lies in the `L ^ k`-block `b`" and "two unit points lie in the same `L`-block".

* `UnitBlockPres σ`: `σ` maps `L ^ k`-blocks of the fine torus to `L ^ k`-blocks.  This is the
  block clause of `LatSymm` at the scale `k` of the unit blocks; the field `LatSymm.block` only
  provides it for scales carrying a layer of `G`, so for a set of levels `k + 1` only (such as
  `lvTop`) it is a separate hypothesis, supplied by `TorusSymm` (`unitBlockPres_of_torusSymm`).
* `unitAct S hU`: the permutation of the unit points `unitPts G` induced by `σ`, characterised by
  `unitBlock (σ x) = unitAct y ↔ unitBlock x = y` (`unitBlock_unitAct_iff`).
* `unitQ_unitAct`, `unitP_unitAct`: entrywise covariance, and the matrix forms
  `unitQ_submatrix`, `unitP_submatrix`, `unitQ_mul_rm`, `unitQ_conj_rm`, `unitP_conj_rm`.
* `cutOperator_inv_sym`, `unitQ_cutInv_conj_sym`: the inverse of the cut operator is the
  transport of the inverse of the cut operator, also after conjugation with `unitQ`.
* Non-vacuity at `lvTop 3 m₁ k ϱ` for the translation `stepVec`.

Covariance of the root trace (`hRT`) and of the determinant terms is NOT proved here.  The
statements are not chart-sensitive and independent of the choice of generator.
-/

@[expose] public section

namespace Balaban.Localization.DetUnitIncidence

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.DecEquiv Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- A permutation of the fine torus maps the blocks of side `L ^ k` to blocks of side `L ^ k`
(the unit blocks `unitBlock`). -/
def UnitBlockPres (σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ x y, unitBlock (σ x) = unitBlock (σ y) ↔ unitBlock x = unitBlock y

omit [NeZero N₁] [NeZero L] in
theorem UnitBlockPres.one : UnitBlockPres (1 : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) :=
  fun _ _ => Iff.rfl

omit [NeZero N₁] [NeZero L] in
theorem UnitBlockPres.symm {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} (h : UnitBlockPres σ) :
    UnitBlockPres σ.symm := fun x y => by
  rw [← h (σ.symm x) (σ.symm y)]; simp

omit [NeZero N₁] [NeZero L] in
theorem unitBlock_eq_jBlock (x : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock x = jBlock d L (N₁ * L ^ m₁) (k + 1) k x := rfl

/-- A symmetry of the paved torus up to scale `j ≥ k` preserves the unit blocks. -/
theorem unitBlockPres_of_torusSymm {j : ℕ} (hj : k ≤ j)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (T : TorusSymm (L := L) (N₀ := N₁ * L ^ m₁) (k := k + 1) j σ) : UnitBlockPres σ := by
  intro x y
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [unitBlock_eq_iff, pow_zero, Nat.div_one]
    have e : ∀ x y : CTorus d L N₁ m₁ (0 + 1), (∀ i, (x i).val = (y i).val) ↔ x = y :=
      fun x y => ⟨fun h => funext fun i => ZMod.val_injective _ (h i), fun h i => by rw [h]⟩
    rw [e, e]
    exact σ.injective.eq_iff
  · rw [unitBlock_eq_jBlock, unitBlock_eq_jBlock]
    exact T.block k hk hj (by omega) x y

section Act

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}

/-- The image of a unit point under a map `τ` preserving the top layer and the unit blocks: the
unit block of `τ` of a representative. -/
noncomputable def unitImg (τ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
    (hτ : ∀ x, τ x ∈ G.layer (k + 1) ↔ x ∈ G.layer (k + 1))
    (y : unitPts G) : unitPts G :=
  ⟨unitBlock (τ (Classical.choose ((mem_unitPts G).1 y.2))),
    (mem_unitPts G).2 ⟨_, (hτ _).2 (Classical.choose_spec ((mem_unitPts G).1 y.2)).1, rfl⟩⟩

theorem unitImg_spec (τ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1)))
    (hτ : ∀ x, τ x ∈ G.layer (k + 1) ↔ x ∈ G.layer (k + 1)) (hU : UnitBlockPres τ)
    (y : unitPts G) {x : CTorus d L N₁ m₁ (k + 1)} (hx : unitBlock x = (y : UnitTorus d L N₁ m₁ k)) :
    unitBlock (τ x) = (unitImg G τ hτ y : UnitTorus d L N₁ m₁ k) := by
  have h0 := (Classical.choose_spec ((mem_unitPts G).1 y.2)).2
  exact (hU _ _).2 (hx.trans h0.symm)

variable (S : LatSymm G G σ) (hU : UnitBlockPres σ)

include S in
theorem layer_top_iff (τ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))) (hS : ∀ x, τ x = σ x) (x) :
    τ x ∈ G.layer (k + 1) ↔ x ∈ G.layer (k + 1) := by
  rw [hS]; exact S.mem_layer (by omega) le_rfl x

include S in
theorem layer_top_symm_iff (x) :
    σ.symm x ∈ G.layer (k + 1) ↔ x ∈ G.layer (k + 1) := by
  have := S.mem_layer (by omega) le_rfl (σ.symm x)
  simpa using this.symm

include S hU in
/-- **The action of a lattice symmetry on the unit points** (the permutation of the unit points
induced by `σ`). -/
noncomputable def unitAct : Equiv.Perm (unitPts G) where
  toFun := unitImg G σ (fun x => S.mem_layer (by omega) le_rfl x)
  invFun := unitImg G σ.symm (layer_top_symm_iff G S)
  left_inv y := by
    apply Subtype.ext
    obtain ⟨x, -, hx⟩ := (mem_unitPts G).1 y.2
    have h1 := unitImg_spec G σ (fun x => S.mem_layer (by omega) le_rfl x) hU y hx
    have h2 := unitImg_spec G σ.symm (layer_top_symm_iff G S) hU.symm
      (unitImg G σ (fun x => S.mem_layer (by omega) le_rfl x) y) h1
    simpa [hx] using h2.symm
  right_inv y := by
    apply Subtype.ext
    obtain ⟨x, -, hx⟩ := (mem_unitPts G).1 y.2
    have h1 := unitImg_spec G σ.symm (layer_top_symm_iff G S) hU.symm y hx
    have h2 := unitImg_spec G σ (fun x => S.mem_layer (by omega) le_rfl x) hU
      (unitImg G σ.symm (layer_top_symm_iff G S) y) h1
    simpa [hx] using h2.symm

/-- **Characterisation of the action.**  `σ` maps the unit block of `y` onto the unit block of
`unitAct y`: for every site `x`, `x` lies in the block of `y` iff `σ x` lies in the block of
`unitAct y`. -/
theorem unitBlock_unitAct_iff (y : unitPts G) (x : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock (σ x) = (unitAct G S hU y : UnitTorus d L N₁ m₁ k) ↔
      unitBlock x = (y : UnitTorus d L N₁ m₁ k) := by
  obtain ⟨x₀, -, hx₀⟩ := (mem_unitPts G).1 y.2
  have h1 : unitBlock (σ x₀) = (unitAct G S hU y : UnitTorus d L N₁ m₁ k) :=
    unitImg_spec G σ (fun x => S.mem_layer (by omega) le_rfl x) hU y hx₀
  rw [← h1, ← hx₀]
  exact hU x x₀

theorem unitAct_eq_iff (y y' : unitPts G) :
    unitAct G S hU y = y' ↔ ∀ x, unitBlock x = (y : UnitTorus d L N₁ m₁ k) →
      unitBlock (σ x) = (y' : UnitTorus d L N₁ m₁ k) := by
  constructor
  · rintro rfl x hx; exact (unitBlock_unitAct_iff G S hU y x).2 hx
  · intro h
    obtain ⟨x₀, -, hx₀⟩ := (mem_unitPts G).1 y.2
    apply Subtype.ext
    rw [← h x₀ hx₀]
    exact ((unitBlock_unitAct_iff G S hU y (x₀)).2 hx₀).symm

theorem unitAct_unitBlock {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.layer (k + 1)) :
    (unitAct G S hU ⟨unitBlock x, (mem_unitPts G).2 ⟨x, hx, rfl⟩⟩ : UnitTorus d L N₁ m₁ k) =
      unitBlock (σ x) :=
  ((unitBlock_unitAct_iff G S hU _ x).2 rfl).symm

/-! ### Incidence maps and block cardinalities -/

open Classical in
/-- The fibre of a unit point inside `Ω₁`. -/
noncomputable def unitFibre (y : unitPts G) : Finset (G.Ω 1) :=
  Finset.univ.filter fun x => unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = y

theorem mem_unitFibre {y : unitPts G} {x : G.Ω 1} :
    x ∈ unitFibre G y ↔ unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = y := by
  classical
  simp [unitFibre]

/-- First incidence relation: the block of `y` is carried onto the block of `unitAct y`. -/
theorem unitFibre_unitAct (y : unitPts G) :
    (unitFibre G y).map S.Ω1Equiv.toEmbedding = unitFibre G (unitAct G S hU y) := by
  ext x'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_unitFibre, LatSymm.coe_Ω1Equiv]
  rw [unitBlock_unitAct_iff]

/-- Block cardinalities are preserved. -/
theorem card_unitFibre_unitAct (y : unitPts G) :
    (unitFibre G (unitAct G S hU y)).card = (unitFibre G y).card := by
  rw [← unitFibre_unitAct G S hU y, Finset.card_map]

/-- Second incidence relation: two unit points lie in the same `L`-block iff their images do. -/
theorem unitBlock1_unitAct_iff (y y' : unitPts G) :
    unitBlock1 (unitAct G S hU y : UnitTorus d L N₁ m₁ k) =
        unitBlock1 (unitAct G S hU y' : UnitTorus d L N₁ m₁ k) ↔
      unitBlock1 (y : UnitTorus d L N₁ m₁ k) = unitBlock1 (y' : UnitTorus d L N₁ m₁ k) := by
  obtain ⟨x, hxl, hx⟩ := (mem_unitPts G).1 y.2
  obtain ⟨x', -, hx'⟩ := (mem_unitPts G).1 y'.2
  have e1 := (unitBlock_unitAct_iff G S hU y x).2 hx
  have e2 := (unitBlock_unitAct_iff G S hU y' x').2 hx'
  rw [← e1, ← e2, ← hx, ← hx', unitBlock1_unitBlock, unitBlock1_unitBlock,
    unitBlock1_unitBlock, unitBlock1_unitBlock]
  exact S.block (k + 1) (by omega) le_rfl ⟨x, hxl⟩ x x'

/-! ### Covariance of `unitQ` and `unitP` -/

theorem unitQ_unitAct (y : unitPts G) (x : G.Ω 1) :
    unitQ G (unitAct G S hU y) (S.Ω1Equiv x) = unitQ G y x := by
  unfold unitQ
  simp only [LatSymm.coe_Ω1Equiv]
  by_cases h : unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = y
  · have h' := (unitBlock_unitAct_iff G S hU y x).2 h
    simp [h, h']
  · have h' : ¬ unitBlock (σ (x : CTorus d L N₁ m₁ (k + 1))) =
        (unitAct G S hU y : UnitTorus d L N₁ m₁ k) :=
      fun h' => h ((unitBlock_unitAct_iff G S hU y x).1 h')
    simp [h, h']

theorem unitP_unitAct (y y' : unitPts G) :
    unitP G (unitAct G S hU y) (unitAct G S hU y') = unitP G y y' := by
  unfold unitP
  simp only [unitBlock1_unitAct_iff G S hU y y']

/-- Matrix form: `Q` is invariant under the simultaneous relabelling of rows (by `unitAct`) and
columns (by `Ω1Equiv`). -/
theorem unitQ_submatrix :
    (unitQ G).submatrix (unitAct G S hU) S.Ω1Equiv = unitQ G := by
  ext y x; exact unitQ_unitAct G S hU y x

theorem unitP_submatrix :
    (unitP G).submatrix (unitAct G S hU) (unitAct G S hU) = unitP G := by
  ext y y'; exact unitP_unitAct G S hU y y'

theorem unitQ_submatrix_symm :
    (unitQ G).submatrix (unitAct G S hU).symm S.Ω1Equiv.symm = unitQ G := by
  ext y x
  simpa using (unitQ_unitAct G S hU ((unitAct G S hU).symm y) (S.Ω1Equiv.symm x)).symm

theorem unitP_submatrix_symm :
    (unitP G).submatrix (unitAct G S hU).symm (unitAct G S hU).symm = unitP G := by
  ext y y'
  simpa using (unitP_unitAct G S hU ((unitAct G S hU).symm y) ((unitAct G S hU).symm y')).symm

/-- `reindex` form: `Q` is fixed by the reindexing `(unitAct, Ω1Equiv)`. -/
theorem reindex_unitQ :
    Matrix.reindex (unitAct G S hU) S.Ω1Equiv (unitQ G) = unitQ G := by
  simpa [Matrix.reindex_apply] using unitQ_submatrix_symm G S hU

theorem reindex_unitP :
    Matrix.reindex (unitAct G S hU) (unitAct G S hU) (unitP G) = unitP G := by
  simpa [Matrix.reindex_apply] using unitP_submatrix_symm G S hU

/-- `Q · rm(M) = (Q M)` relabelled: the form for conjugating products `Q M P`. -/
theorem unitQ_mul_rm (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) :
    unitQ G * rm S.Ω1Equiv M =
      (unitQ G * M).submatrix (unitAct G S hU).symm S.Ω1Equiv.symm := by
  conv_lhs => rw [← unitQ_submatrix_symm G S hU]
  rw [rm, Matrix.submatrix_mul_equiv]

theorem unitQ_mul_rm_unit (M : Matrix (G.Ω 1) (unitPts G) ℂ) :
    unitQ G * Matrix.submatrix M S.Ω1Equiv.symm (unitAct G S hU).symm =
      (unitQ G * M).submatrix (unitAct G S hU).symm (unitAct G S hU).symm := by
  conv_lhs => rw [← unitQ_submatrix_symm G S hU]
  rw [Matrix.submatrix_mul_equiv]

theorem unitP_mul_submatrix (N : Matrix (unitPts G) (unitPts G) ℂ) :
    unitP G * N.submatrix (unitAct G S hU).symm (unitAct G S hU).symm =
      (unitP G * N).submatrix (unitAct G S hU).symm (unitAct G S hU).symm := by
  conv_lhs => rw [← unitP_submatrix_symm G S hU]
  rw [Matrix.submatrix_mul_equiv]

theorem unitQ_conjTranspose_submatrix :
    (unitQ G)ᴴ.submatrix S.Ω1Equiv.symm (unitAct G S hU).symm = (unitQ G)ᴴ := by
  have := congrArg Matrix.conjTranspose (unitQ_submatrix_symm G S hU)
  rwa [Matrix.conjTranspose_submatrix] at this

/-- **Conjugation of a matrix on `Ω₁` by `Q`:** `Q · rm(M) · Q* = (Q M Q*)` relabelled. -/
theorem unitQ_conj_rm (M : Matrix (G.Ω 1) (G.Ω 1) ℂ) :
    unitQ G * rm S.Ω1Equiv M * (unitQ G)ᴴ =
      ((unitQ G * M * (unitQ G)ᴴ).submatrix (unitAct G S hU).symm (unitAct G S hU).symm) := by
  have h := unitQ_conjTranspose_submatrix G S hU
  calc unitQ G * rm S.Ω1Equiv M * (unitQ G)ᴴ
      = (unitQ G * M).submatrix (unitAct G S hU).symm S.Ω1Equiv.symm *
          (unitQ G)ᴴ.submatrix S.Ω1Equiv.symm (unitAct G S hU).symm := by
        rw [unitQ_mul_rm G S hU, h]
    _ = _ := Matrix.submatrix_mul_equiv _ _ _ _ _

/-- **Conjugation of a matrix on the unit points by `P`:** `P · N^σ · P = (P N P)^σ`. -/
theorem unitP_conj_submatrix (N : Matrix (unitPts G) (unitPts G) ℂ) :
    unitP G * N.submatrix (unitAct G S hU).symm (unitAct G S hU).symm * unitP G =
      (unitP G * N * unitP G).submatrix (unitAct G S hU).symm (unitAct G S hU).symm := by
  have h := unitP_submatrix_symm G S hU
  calc unitP G * N.submatrix (unitAct G S hU).symm (unitAct G S hU).symm * unitP G
      = (unitP G * N).submatrix (unitAct G S hU).symm (unitAct G S hU).symm *
          (unitP G).submatrix (unitAct G S hU).symm (unitAct G S hU).symm := by
        rw [unitP_mul_submatrix G S hU, h]
    _ = _ := Matrix.submatrix_mul_equiv _ _ _ _ _

end Act

/-! ### The cut operator -/

section Cut

variable (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))} (S : LatSymm G G σ) (hU : UnitBlockPres σ)

/-- The cut operator of the image is the transport of the cut operator (matrix form of
`cutOperator_sym`). -/
theorem cutOperator_rm (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    cutOperator G a ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α) =
      rm S.Ω1Equiv (cutOperator G a ν cut α) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply]
  exact cutOperator_sym S a ν cut α x y

/-- **The inverse of the cut operator is covariant**: with `Matrix.inv` (the nonsingular inverse,
so no invertibility assumption is needed), `(H_{σ cut, σ α})⁻¹ = rm σ (H_{cut, α}⁻¹)`, i.e.
`(H')⁻¹ (σ x) (σ y) = H⁻¹ x y`. -/
theorem cutOperator_inv_rm (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    (cutOperator G a ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α))⁻¹ =
      rm S.Ω1Equiv (cutOperator G a ν cut α)⁻¹ := by
  rw [cutOperator_rm G S, rm_inv]

theorem cutOperator_inv_apply (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    (cutOperator G a ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α))⁻¹ (S.Ω1Equiv x) (S.Ω1Equiv y) =
      (cutOperator G a ν cut α)⁻¹ x y := by
  rw [cutOperator_inv_rm G S, rm_apply]

/-- **Covariance of `Q H⁻¹ Q*`**: conjugation by `unitQ` turns the transport on `Ω₁` into the
transport `unitAct` on the unit points. -/
theorem unitQ_cutInv_conj (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)) (α : G.Ω 1 → ℂ) :
    unitQ G * (cutOperator G a ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α))⁻¹ * (unitQ G)ᴴ =
      (unitQ G * (cutOperator G a ν cut α)⁻¹ * (unitQ G)ᴴ).submatrix
        (unitAct G S hU).symm (unitAct G S hU).symm := by
  rw [cutOperator_inv_rm G S, unitQ_conj_rm G S hU]

end Cut

/-! ### Non-vacuity at the top level set of the step -/

section Inhabited

open Balaban.Inhabited Balaban.Inhabited.LevelStep Balaban.Fluctuation

variable (m₁ k : ℕ) (ϱ : ℝ)

private theorem hdv_stepVec (μ : Fin 3) : 3 ^ k ∣ (stepVec m₁ k μ).val :=
  (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)

/-- The translation `stepVec` preserves the unit blocks. -/
theorem unitBlockPres_stepVec :
    UnitBlockPres (d := 3) (L := 3) (N₁ := 3) (m₁ := m₁) (k := k)
      (Equiv.addRight (stepVec m₁ k)) :=
  unitBlockPres_of_torusSymm (j := k) le_rfl (TorusSymm.ofTranslate k (stepVec m₁ k)
    (hdv_stepVec m₁ k))

/-- The coordinate swap preserves the unit blocks. -/
theorem unitBlockPres_swap01 :
    UnitBlockPres (d := 3) (L := 3) (N₁ := 3) (m₁ := m₁) (k := k) (coordPerm swap01) :=
  unitBlockPres_of_torusSymm (j := k) le_rfl (TorusSymm.ofCoordPerm k swap01)

/-- The lattice symmetry of the top level set given by the translation `stepVec`. -/
noncomputable def stepTranslateSymm :=
  LatSymm.ofTranslateLevel (G := lvTop 3 m₁ k ϱ) isLevel_lvTop (stepVec m₁ k) fun μ =>
    (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)

/-- The lattice symmetry of the top level set given by the coordinate swap. -/
noncomputable def stepSwapSymm :=
  LatSymm.ofCoordPermLevel (G := lvTop 3 m₁ k ϱ) (m₁ := m₁) isLevel_lvTop swap01

theorem lvTop_zero_mem_layer : (0 : CTorus 3 3 3 m₁ (k + 1)) ∈ (lvTop 3 m₁ k ϱ).layer (k + 1) :=
  isLevel_lvTop.mem_layer 0

/-- **Instance of the entrywise covariance at the translation.** -/
theorem unitQ_unitAct_translate (y : unitPts (lvTop 3 m₁ k ϱ)) (x : (lvTop 3 m₁ k ϱ).Ω 1) :
    unitQ (lvTop 3 m₁ k ϱ)
        (unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) y)
        ((stepTranslateSymm m₁ k ϱ).Ω1Equiv x) = unitQ (lvTop 3 m₁ k ϱ) y x :=
  unitQ_unitAct _ _ _ y x

theorem unitP_unitAct_translate (y y' : unitPts (lvTop 3 m₁ k ϱ)) :
    unitP (lvTop 3 m₁ k ϱ)
        (unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) y)
        (unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) y') =
      unitP (lvTop 3 m₁ k ϱ) y y' :=
  unitP_unitAct _ _ _ y y'

theorem unitQ_submatrix_translate :
    (unitQ (lvTop 3 m₁ k ϱ)).submatrix
        (unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k))
        (stepTranslateSymm m₁ k ϱ).Ω1Equiv = unitQ (lvTop 3 m₁ k ϱ) :=
  unitQ_submatrix _ _ _

theorem unitQ_unitAct_swap (y : unitPts (lvTop 3 m₁ k ϱ)) (x : (lvTop 3 m₁ k ϱ).Ω 1) :
    unitQ (lvTop 3 m₁ k ϱ)
        (unitAct (lvTop 3 m₁ k ϱ) (stepSwapSymm m₁ k ϱ) (unitBlockPres_swap01 m₁ k) y)
        ((stepSwapSymm m₁ k ϱ).Ω1Equiv x) = unitQ (lvTop 3 m₁ k ϱ) y x :=
  unitQ_unitAct _ _ _ y x

private theorem val_stepVec_div (μ : Fin 3) : (stepVec m₁ k μ).val / 3 ^ k = 3 ^ (m₁ + 1) := by
  rw [stepVec_val, show k + 1 + m₁ = k + (m₁ + 1) by ring, pow_add,
    Nat.mul_div_cancel_left _ (by positivity)]

/-- The translation `stepVec` moves a unit point: `unitAct` is not the identity. -/
theorem unitAct_translate_ne_one :
    unitAct (lvTop 3 m₁ k ϱ) (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k) ≠ 1 := by
  intro h
  set G := lvTop 3 m₁ k ϱ
  set y : unitPts G := ⟨unitBlock (0 : CTorus 3 3 3 m₁ (k + 1)),
    (mem_unitPts G).2 ⟨0, lvTop_zero_mem_layer m₁ k ϱ, rfl⟩⟩
  have h1 := unitAct_unitBlock G (stepTranslateSymm m₁ k ϱ) (unitBlockPres_stepVec m₁ k)
    (lvTop_zero_mem_layer m₁ k ϱ)
  rw [h] at h1
  have h2 : unitBlock ((Equiv.addRight (stepVec m₁ k)) (0 : CTorus 3 3 3 m₁ (k + 1))) =
      unitBlock (0 : CTorus 3 3 3 m₁ (k + 1)) := h1.symm
  have h3 := (unitBlock_eq_iff _ _).1 h2 0
  simp only [Equiv.coe_addRight, Pi.add_apply, Pi.zero_apply, zero_add, ZMod.val_zero,
    Nat.zero_div] at h3
  rw [val_stepVec_div] at h3
  exact (pow_pos (by norm_num : (0 : ℕ) < 3) _).ne' h3

/-- The coordinate swap moves a unit point: `unitAct` is not the identity. -/
theorem unitAct_swap_ne_one :
    unitAct (lvTop 3 m₁ k ϱ) (stepSwapSymm m₁ k ϱ) (unitBlockPres_swap01 m₁ k) ≠ 1 := by
  intro h
  set G := lvTop 3 m₁ k ϱ
  set x₀ : CTorus 3 3 3 m₁ (k + 1) := Pi.single 0 (stepVec m₁ k 0)
  have hx₀ : x₀ ∈ G.layer (k + 1) := isLevel_lvTop.mem_layer x₀
  have h1 := unitAct_unitBlock G (stepSwapSymm m₁ k ϱ) (unitBlockPres_swap01 m₁ k) hx₀
  rw [h] at h1
  have h2 : unitBlock (coordPerm swap01 x₀) = unitBlock x₀ := h1.symm
  have h3 := (unitBlock_eq_iff _ _).1 h2 0
  have e : (swap01).symm 0 = 1 := by decide
  simp only [coordPerm, Equiv.coe_fn_mk, Function.comp_apply, e, x₀, Pi.single_apply] at h3
  simp at h3
  rw [val_stepVec_div] at h3
  exact (pow_pos (by norm_num : (0 : ℕ) < 3) _).ne h3

end Inhabited

end Balaban.Localization.DetUnitIncidence
