/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoX
public import Balaban.Fluctuation.RootDetChart
public import Balaban.Polymer.TwoTorusDecCov
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the decoupled covariance and the rooted trace

* **Generic reindexing** (any equivalences of the index types): `liftOp_submatrix`,
  `fieldMul_submatrix`, `commK_submatrix`, `constraintM_submatrix`, `constraintN_submatrix`,
  `liftRect_submatrix`, `covA_submatrix`, `intMat_submatrix`.
* **Under `OmegaIso G H ρ`** (level `k + 1`): the unit points (`OmegaIso.unitEquiv`, `unitQ`,
  `unitP`), the constrained operators `M_{x,s}`, `N_{x,s}`, `Π_{x,s}` (`decM_submatrix`,
  `decN_submatrix`, `decPi_submatrix`), the decoupled covariance `C_x(s)` (`decCov_submatrix`),
  the decoupled logarithm `𝕃(s)` (`decLog_submatrix`) and the rooted trace (`rootTrace_eq`), at
  corresponding potentials, cut parameters and fields.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Matrix MeasureTheory

/-! ### Generic reindexing -/

section Generic

variable {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
  [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] {N : ℕ}

/-- The equivalence of the vector-field indices. -/
def eN (N : ℕ) (f : ι' ≃ ι) : ι' × Fin N ≃ ι × Fin N := f.prodCongr (Equiv.refl (Fin N))

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] in
@[simp] theorem eN_apply (f : ι' ≃ ι) (p : ι' × Fin N) : eN N f p = (f p.1, p.2) := rfl

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] in
theorem liftOp_submatrix (M : Matrix ι ι ℂ) (f : ι' ≃ ι) :
    (liftOp N M).submatrix (eN N f) (eN N f) = liftOp N (M.submatrix f f) := by
  ext p q
  simp only [Matrix.submatrix_apply, liftOp, eN_apply]
  by_cases h : p.2 = q.2 <;> simp [h]

omit [Fintype ι] [Fintype ι'] in
theorem fieldMul_submatrix (φ : ι → Fin N → ℂ) (f : ι' ≃ ι) :
    (fieldMul φ).submatrix (eN N f) f = fieldMul (φ ∘ f) := by
  ext p y
  simp only [Matrix.submatrix_apply, fieldMul, eN_apply, Function.comp_apply,
    EmbeddingLike.apply_eq_iff_eq]

omit [Fintype ι] [Fintype ι'] in
theorem fieldMul_transpose_submatrix (φ : ι → Fin N → ℂ) (f : ι' ≃ ι) :
    (fieldMul φ)ᵀ.submatrix f (eN N f) = (fieldMul (φ ∘ f))ᵀ := by
  rw [← Matrix.transpose_submatrix, fieldMul_submatrix]

theorem commK_submatrix (M : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) (f : ι' ≃ ι) :
    (commK M φ).submatrix f (eN N f) = commK (M.submatrix f f) (φ ∘ f) := by
  unfold commK
  rw [show ((fieldMul φ)ᵀ * liftOp N M - M * (fieldMul φ)ᵀ).submatrix f (eN N f) =
      ((fieldMul φ)ᵀ * liftOp N M).submatrix f (eN N f) -
        (M * (fieldMul φ)ᵀ).submatrix f (eN N f) from rfl,
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N f), ← Matrix.submatrix_mul_equiv _ _ _ f,
    fieldMul_transpose_submatrix, liftOp_submatrix]

theorem constraintM_submatrix (H G : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) (f : ι' ≃ ι) :
    (constraintM H G φ).submatrix f f =
      constraintM (H.submatrix f f) (G.submatrix f f) (φ ∘ f) := by
  unfold constraintM
  rw [show ((fieldMul φ)ᵀ * fieldMul φ - commK H φ * liftOp N G * fieldMul φ).submatrix f f =
      ((fieldMul φ)ᵀ * fieldMul φ).submatrix f f -
        (commK H φ * liftOp N G * fieldMul φ).submatrix f f from rfl,
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N f), ← Matrix.submatrix_mul_equiv _ _ _ (eN N f),
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N f), fieldMul_transpose_submatrix,
    fieldMul_submatrix, commK_submatrix, liftOp_submatrix]

theorem constraintN_submatrix (H G : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) (f : ι' ≃ ι) :
    (constraintN H G φ).submatrix f (eN N f) =
      constraintN (H.submatrix f f) (G.submatrix f f) (φ ∘ f) := by
  unfold constraintN
  rw [show ((fieldMul φ)ᵀ - commK H φ * liftOp N G).submatrix f (eN N f) =
      (fieldMul φ)ᵀ.submatrix f (eN N f) - (commK H φ * liftOp N G).submatrix f (eN N f) from rfl,
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N f), fieldMul_transpose_submatrix, commK_submatrix,
    liftOp_submatrix]

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] [Fintype κ] [Fintype κ']
  [DecidableEq κ] [DecidableEq κ'] in
theorem liftRect_submatrix (Q : Matrix κ ι ℂ) (g : κ' ≃ κ) (f : ι' ≃ ι) :
    (liftRect N Q).submatrix (eN N g) (eN N f) = liftRect N (Q.submatrix g f) := by
  ext p q
  simp only [Matrix.submatrix_apply, liftRect, eN_apply]
  by_cases h : p.2 = q.2 <;> simp [h]

omit [Fintype κ] [Fintype κ'] in
theorem covA_submatrix (c b x : ℝ) (P : Matrix κ κ ℂ) (g : κ' ≃ κ) :
    (covA c b x P).submatrix g g = covA c b x (P.submatrix g g) := by
  unfold covA
  ext p q
  simp [Matrix.sub_apply, Matrix.one_apply, g.injective.eq_iff]

omit [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] in
theorem intMat_submatrix (μ : Measure ℝ) (F : ℝ → Matrix κ κ ℂ) (g : κ' → κ) :
    (intMat μ F).submatrix g g = intMat μ (fun x => (F x).submatrix g g) := rfl

end Generic

/-! ### Under `OmegaIso`: the unit points and the covariance -/

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bk'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
local notation "ck" => (Prod.map id bk : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1))

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'} {ρ : ℕ}

theorem room_k (hI : OmegaIso G H ρ) :
    2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) ∧
      2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
  have := hI.two_lt; omega

/-- The unit blocks at two sites of `Ω₁`. -/
theorem unitBlock_iff (hI : OmegaIso G H ρ) {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.Ω 1) : unitBlock (bk x) = unitBlock (bk y) ↔ unitBlock x = unitBlock y :=
  (jBlock_boxMap_iff (m₁ := m₁) (j := k) (K := k + 1) (Nat.le_succ k) hI.room_k.1 hI.room_k.2
    (hI.boxG x hx) (hI.boxG y hy)).symm

/-- The `L^{k+1}`-blocks of the unit blocks at two sites of `Ω₁`. -/
theorem unitBlock1_iff (hI : OmegaIso G H ρ) {x y : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.Ω 1)
    (hy : y ∈ G.Ω 1) : unitBlock1 (unitBlock (bk x)) = unitBlock1 (unitBlock (bk y)) ↔
      unitBlock1 (unitBlock x) = unitBlock1 (unitBlock y) := by
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock, unitBlock1_unitBlock, unitBlock1_unitBlock]
  exact (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) (K := k + 1) le_rfl hI.room_k.1
    hI.room_k.2 (hI.boxG x hx) (hI.boxG y hy)).symm

theorem unitBlock_map (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.Ω 1) :
    unitBlock (bk x) = bU (unitBlock x) :=
  unitBlock_boxMap hI.room_k.1 (hI.boxG x hx)

theorem mem_unitPts_map (hI : OmegaIso G H ρ) (b : unitPts G) :
    bU (b : UnitTorus d L N₁ m₁ k) ∈ unitPts H := by
  obtain ⟨x, hx, hxb⟩ := (mem_unitPts G).1 b.2
  have hx1 : x ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hx
  refine (mem_unitPts H).2 ⟨bk x, (hI.layer_iff (hI.inBox_succ hx1) (by omega) le_rfl).2 hx, ?_⟩
  rw [hI.unitBlock_map hx1, hxb]

/-- **The bijection of the unit points.** -/
def unitEquiv (hI : OmegaIso G H ρ) : unitPts G ≃ unitPts H :=
  Equiv.ofBijective (fun b => ⟨bU (b : UnitTorus d L N₁ m₁ k), hI.mem_unitPts_map b⟩)
    ⟨fun b₁ b₂ h => by
      obtain ⟨x₁, hx₁, hb₁⟩ := (mem_unitPts G).1 b₁.2
      obtain ⟨x₂, hx₂, hb₂⟩ := (mem_unitPts G).1 b₂.2
      have h1 : x₁ ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hx₁
      have h2 : x₂ ∈ G.Ω 1 := G.layer_subset (by omega) le_rfl hx₂
      have hv := congrArg Subtype.val h
      simp only at hv
      rw [← hb₁, ← hb₂, ← hI.unitBlock_map h1, ← hI.unitBlock_map h2] at hv
      exact Subtype.ext (hb₁.symm.trans (((hI.unitBlock_iff h1 h2).1 hv).trans hb₂)),
    fun b' => by
      obtain ⟨x', hx', hb'⟩ := (mem_unitPts H).1 b'.2
      have h1' : x' ∈ H.Ω 1 := H.layer_subset (by omega) le_rfl hx'
      obtain ⟨x, hxe⟩ := hI.e.surjective ⟨x', h1'⟩
      have hxv : bk (x : CTorus d L N₁ m₁ (k + 1)) = x' := by
        rw [← coe_e]; exact congrArg Subtype.val hxe
      have hxl : (x : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) :=
        (hI.layer_iff (hI.inBox_succ x.2) (by omega) le_rfl).1 (by rw [hxv]; exact hx')
      refine ⟨⟨unitBlock (x : CTorus d L N₁ m₁ (k + 1)), (mem_unitPts G).2 ⟨x, hxl, rfl⟩⟩, ?_⟩
      refine Subtype.ext ?_
      show bU (unitBlock (x : CTorus d L N₁ m₁ (k + 1))) = _
      rw [← hI.unitBlock_map x.2, hxv, hb']⟩

@[simp] theorem coe_unitEquiv (hI : OmegaIso G H ρ) (b : unitPts G) :
    ((hI.unitEquiv b : unitPts H) : UnitTorus d L N₁' m₁ k) = bU (b : UnitTorus d L N₁ m₁ k) :=
  rfl

/-- A unit point is the unit block of a site of `Ω₁`. -/
theorem exists_site (b : unitPts G) :
    ∃ x : G.Ω 1, unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = (b : UnitTorus d L N₁ m₁ k) := by
  obtain ⟨x, hx, hxb⟩ := (mem_unitPts G).1 b.2
  exact ⟨⟨x, G.layer_subset (by omega) le_rfl hx⟩, hxb⟩

theorem unitEquiv_site (hI : OmegaIso G H ρ) {b : unitPts G} {x : G.Ω 1}
    (hx : unitBlock (x : CTorus d L N₁ m₁ (k + 1)) = (b : UnitTorus d L N₁ m₁ k)) :
    ((hI.unitEquiv b : unitPts H) : UnitTorus d L N₁' m₁ k) =
      unitBlock ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ (k + 1)) := by
  rw [coe_unitEquiv, coe_e, hI.unitBlock_map x.2, hx]

/-- **The block average `Q_k` on the top layer.** -/
theorem unitQ_submatrix (hI : OmegaIso G H ρ) :
    (unitQ G).submatrix hI.unitEquiv.symm hI.e.symm = unitQ H := by
  ext b' y'
  obtain ⟨b, rfl⟩ := hI.unitEquiv.surjective b'
  obtain ⟨y, rfl⟩ := hI.e.surjective y'
  obtain ⟨x, hx⟩ := exists_site b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, unitQ]
  refine if_congr ?_ rfl rfl
  rw [hI.unitEquiv_site hx, coe_e, coe_e, ← hx]
  exact (hI.unitBlock_iff y.2 x.2).symm

/-- **The projection `P` onto the constants of the `L`-blocks of the unit lattice.** -/
theorem unitP_submatrix (hI : OmegaIso G H ρ) :
    (unitP G).submatrix hI.unitEquiv.symm hI.unitEquiv.symm = unitP H := by
  ext b' c'
  obtain ⟨b, rfl⟩ := hI.unitEquiv.surjective b'
  obtain ⟨c, rfl⟩ := hI.unitEquiv.surjective c'
  obtain ⟨x, hx⟩ := exists_site b
  obtain ⟨y, hy⟩ := exists_site c
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, unitP]
  refine if_congr ?_ rfl rfl
  rw [hI.unitEquiv_site hx, hI.unitEquiv_site hy, coe_e, coe_e, ← hx, ← hy]
  exact (hI.unitBlock1_iff x.2 y.2).symm

/-- The restriction to `Ω₁` of corresponding fields. -/
theorem restrictField_comp (hI : OmegaIso G H ρ) {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ} (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) :
    restrictField G φ ∘ hI.e.symm = restrictField H φ' := by
  funext x'
  obtain ⟨x, rfl⟩ := hI.e.surjective x'
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  exact (hφ x).symm

variable (a : ℕ → ℝ) (aT x₀ ν : ℝ)

/-- **`M_{x,s}`** at corresponding potentials, cut parameters and fields. -/
theorem decM_submatrix (hI : OmegaIso G H ρ) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) :
    (decM G a aT x₀ ν α s φ).submatrix hI.e.symm hI.e.symm = decM H a aT x₀ ν α' s' φ' := by
  unfold decM
  rw [constraintM_submatrix, hI.xDirichletOperator_submatrix a aT x₀ ν hα,
    hI.Gsx_submatrix a aT x₀ ν hα hs, hI.restrictField_comp hφ]

/-- **`N_{x,s}`** at corresponding data. -/
theorem decN_submatrix (hI : OmegaIso G H ρ) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) :
    (decN G a aT x₀ ν α s φ).submatrix hI.e.symm (eN N hI.e.symm) =
      decN H a aT x₀ ν α' s' φ' := by
  unfold decN
  rw [constraintN_submatrix, hI.xDirichletOperator_submatrix a aT x₀ ν hα,
    hI.Gsx_submatrix a aT x₀ ν hα hs, hI.restrictField_comp hφ]

/-- **`Π_{x,s}`** at corresponding data. -/
theorem decPi_submatrix (hI : OmegaIso G H ρ) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) :
    (decPi G a aT x₀ ν α s φ).submatrix (eN N hI.e.symm) (eN N hI.e.symm) =
      decPi H a aT x₀ ν α' s' φ' := by
  unfold decPi
  rw [← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, ← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm,
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N hI.e.symm), liftOp_submatrix, fieldMul_submatrix,
    ← Matrix.inv_submatrix_equiv, hI.decM_submatrix a aT x₀ ν hα hs hφ,
    hI.decN_submatrix a aT x₀ ν hα hs hφ, hI.Gsx_submatrix a aT x₀ ν hα hs,
    hI.restrictField_comp hφ]

/-- **The decoupled covariance `C_x(s)`** on the unit points, at corresponding data. -/
theorem decCov_submatrix (hI : OmegaIso G H ρ) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) :
    (decCov G a aT x₀ ν α s φ (unitQ G) (unitP G)).submatrix (eN N hI.unitEquiv.symm)
        (eN N hI.unitEquiv.symm) = decCov H a aT x₀ ν α' s' φ' (unitQ H) (unitP H) := by
  have hA : (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G))).submatrix
      (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) =
      covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP H)) := by
    rw [covA_submatrix, liftOp_submatrix, hI.unitP_submatrix]
  have hQ : (liftRect N (unitQ G)).submatrix (eN N hI.unitEquiv.symm) (eN N hI.e.symm) =
      liftRect N (unitQ H) := by
    rw [liftRect_submatrix, hI.unitQ_submatrix]
  have hQT : (liftRect N (unitQ G))ᵀ.submatrix (eN N hI.e.symm) (eN N hI.unitEquiv.symm) =
      (liftRect N (unitQ H))ᵀ := by
    rw [← Matrix.transpose_submatrix, hQ]
  have hM : (liftOp N (Gsx G a aT x₀ ν α s) - decPi G a aT x₀ ν α s φ).submatrix
      (eN N hI.e.symm) (eN N hI.e.symm) =
      liftOp N (Gsx H a aT x₀ ν α' s') - decPi H a aT x₀ ν α' s' φ' := by
    rw [submatrix_sub_apply, liftOp_submatrix, hI.Gsx_submatrix a aT x₀ ν hα hs,
      hI.decPi_submatrix a aT x₀ ν hα hs hφ]
  unfold decCov
  rw [show ∀ (A B : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ), (A + B).submatrix
      (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) =
      A.submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) +
        B.submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) from fun _ _ => rfl,
    submatrix_smul_apply, ← Matrix.submatrix_mul_equiv _ _ _ (eN N hI.unitEquiv.symm),
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N hI.e.symm),
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N hI.e.symm),
    ← Matrix.submatrix_mul_equiv _ _ _ (eN N hI.unitEquiv.symm), hA, hQ, hM, hQT]

/-- **The decoupled logarithm `𝕃(s)`** on the unit points, at corresponding data. -/
theorem decLog_submatrix (hI : OmegaIso G H ρ) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) :
    (decLog G a aT ν α s φ (unitQ G) (unitP G)).submatrix (eN N hI.unitEquiv.symm)
        (eN N hI.unitEquiv.symm) = decLog H a aT ν α' s' φ' (unitQ H) (unitP H) := by
  have hP : (liftOp N (unitP G)).submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) =
      liftOp N (unitP H) := by
    rw [liftOp_submatrix, hI.unitP_submatrix]
  have hI2 : (intMat (volume.restrict (Set.Ioi (0 : ℝ))) (fun x => decCov G a aT x ν α s φ
      (unitQ G) (unitP G) - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G)))).submatrix
        (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) =
      intMat (volume.restrict (Set.Ioi (0 : ℝ))) (fun x => decCov H a aT x ν α' s' φ'
        (unitQ H) (unitP H) - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP H))) := by
    rw [intMat_submatrix]
    congr 1
    funext x
    rw [submatrix_sub_apply, hI.decCov_submatrix a aT x ν hα hs hφ, covA_submatrix, hP]
  unfold decLog
  rw [submatrix_sub_apply, show ∀ (A B : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ),
      (A + B).submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) =
      A.submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) +
        B.submatrix (eN N hI.unitEquiv.symm) (eN N hI.unitEquiv.symm) from fun _ _ => rfl,
    submatrix_smul_apply, submatrix_smul_apply, submatrix_sub_apply, Matrix.submatrix_one_equiv,
    hP, hI2]

/-- The extension by `1` of corresponding parameters of the centres (own cover). -/
theorem extS_self_eq (hI : OmegaIso G H ρ) {s : DecParams G} {s' : DecParams H}
    (hs : ∀ q : cubeIdx G, s' (hI.cubeEquiv q) = s q) {P : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hP : P ∈ cubeIdx G) : extS H s' (ck P) = extS G s P := by
  have hP' : ck P ∈ cubeIdx H := hI.mem_cubeIdx_map hP
  unfold extS
  simp only [hP, hP', ↓reduceDIte]
  exact hs ⟨P, hP⟩

/-- **The rooted trace** at a set of unit points and its image, at corresponding cut
parameters, fields and potentials. -/
theorem rootTrace_eq (hI : OmegaIso G H ρ) (B : Finset (unitPts G)) {s : DecParams G}
    {s' : DecParams H} (hs : ∀ q : cubeIdx G, s' (hI.cubeEquiv q) = s q)
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ' (hI.e x) = φ x) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) :
    rootTrace H a aT ν (unitQ H) (unitP H) (B.map hI.unitEquiv.toEmbedding) s' φ' α' =
      rootTrace G a aT ν (unitQ G) (unitP G) B s φ α := by
  have hL := hI.decLog_submatrix a aT ν hα (fun P hP => hI.extS_self_eq hs hP) hφ
  unfold rootTrace
  rw [Finset.sum_map]
  congr 1
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  rw [← hL]
  simp

end OmegaIso

end Balaban.Polymer.LocalIso
