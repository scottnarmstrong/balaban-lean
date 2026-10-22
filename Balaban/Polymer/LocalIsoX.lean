/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoDec2
public import Balaban.Localization.DecoupledX
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the x-variant decoupled Green's operator

The determinant part of the coefficient reads the x-variant decoupled Green's operator
`G_{k,x,s}(A) = G*_{x,s}(A) (1 - 𝒦_{x,s}(A))⁻¹` of a generating set `G` of level `k + 1` (its own
cover).  For two sets carried onto each other by the box map (`OmegaIso G H ρ`), all its matrices
are reindexings of each other.

* `coverSum_submatrix`: **the generic cover sum** `∑_z s_z A_z` over the centres of a cover, for
  matrices `A_z` corresponding at corresponding centres (one lemma for all the sums over the cover);
* `layerBlockMatrix_corr`, `xAvgMatrix_corr`, `cutXFullMatrix_corr`: the entries of the x-variant
  forms at corresponding sites;
* `OmegaIso.cutXOperator_submatrix`, `OmegaIso.xDirichletOperator_submatrix`,
  `OmegaIso.cubeGx_submatrix`, `OmegaIso.Kzx_submatrix`, `OmegaIso.Gstarx_submatrix`,
  `OmegaIso.Kcalx_submatrix`, `OmegaIso.Gsx_submatrix`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' ϱc ϱc' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "cm" => (Prod.map id bm : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁' m₁ K)

namespace OmegaIso

variable {Gc : GeneratingSet d L (N₁ * L ^ m₁) K ϱc} {Hc : GeneratingSet d L (N₁' * L ^ m₁) K ϱc'}
  {ρ : ℕ}

/-- **The generic cover sum.**  For matrices `A_z` (on any index types related by `f`) that
correspond at corresponding centres of the cover of `Gc`, and cut parameters corresponding on the
centres, the sums `∑_z s_z A_z` over the centres correspond. -/
theorem coverSum_submatrix (hC : OmegaIso Gc Hc ρ) {ι ι' : Type*} (f : ι' ≃ ι)
    {A : ℕ × CTorus d L N₁ m₁ K → Matrix ι ι ℂ} {A' : ℕ × CTorus d L N₁' m₁ K → Matrix ι' ι' ℂ}
    (hA : ∀ q ∈ cubeIdx Gc, (A q).submatrix f f = A' (cm q))
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ cubeIdx Gc, s' (cm P) = s P) :
    (∑ q ∈ cubeIdx Gc, sProd Gc s q • A q).submatrix f f =
      ∑ q ∈ cubeIdx Hc, sProd Hc s' q • A' q := by
  rw [submatrix_finset_sum, ← hC.cubeIdx_image, Finset.sum_image hC.cm_injOn]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [submatrix_smul_apply, hA q hq, hC.sProd_eq hq hs]

end OmegaIso

/-! ### The x-variant forms -/

/-- The entries of `1_{layer j} P_m 1_{layer j}` at corresponding sites of the box. -/
theorem layerBlockMatrix_corr {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'} {ρ : ℕ} {j m : ℕ} (hm : m ≤ K)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {x y : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y)
    (hlx : bm x ∈ H.layer j ↔ x ∈ G.layer j) (hly : bm y ∈ H.layer j ↔ y ∈ G.layer j) :
    layerBlockMatrix H j m (bm x) (bm y) = layerBlockMatrix G j m x y := by
  unfold layerBlockMatrix
  have hjb := jBlock_boxMap_iff (m₁ := m₁) (j := m) (K := K) hm hn hn' hx hy
  unfold jBlock at hjb
  by_cases hxl : x ∈ G.layer j <;> by_cases hyl : y ∈ G.layer j
  · simp only [hxl, hyl, and_self, ite_true, hlx.2 hxl, hly.2 hyl]
    unfold blockProjMatrix
    exact if_congr hjb.symm rfl rfl
  · have : ¬ bm y ∈ H.layer j := fun h => hyl (hly.1 h)
    simp [hyl, this]
  · have : ¬ bm x ∈ H.layer j := fun h => hxl (hlx.1 h)
    simp [hxl, this]
  · have : ¬ bm x ∈ H.layer j := fun h => hxl (hlx.1 h)
    simp [hxl, this]

variable {k : ℕ}

local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "ck" => (Prod.map id bk : ℕ × CTorus d L N₁ m₁ (k + 1) → ℕ × CTorus d L N₁' m₁ (k + 1))

/-- The entries of the x-variant averaging form at corresponding sites of the box. -/
theorem xAvgMatrix_corr {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'} (a : ℕ → ℝ) (s₁ s₂ : ℝ) {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hlx : ∀ n, 1 ≤ n → n ≤ k + 1 → (bk x ∈ H.layer n ↔ x ∈ G.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ k + 1 → (bk y ∈ H.layer n ↔ y ∈ G.layer n)) :
    xAvgMatrix H a s₁ s₂ (bk x) (bk y) = xAvgMatrix G a s₁ s₂ x y := by
  unfold xAvgMatrix
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun n hnn => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hnn
      rw [layerBlockMatrix_corr (by omega) hn hn' hx hy (hlx n h1 (by omega))
        (hly n h1 (by omega))]
    · rw [layerBlockMatrix_corr (by omega) hn hn' hx hy (hlx (k + 1) (by omega) le_rfl)
        (hly (k + 1) (by omega) le_rfl)]
  · rw [layerBlockMatrix_corr le_rfl hn hn' hx hy (hlx (k + 1) (by omega) le_rfl)
      (hly (k + 1) (by omega) le_rfl)]

/-- **The full x-variant cut matrix at corresponding sites** (the x-variant of
`cutFullMatrix_corr`). -/
theorem cutXFullMatrix_corr {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {H : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'} (a : ℕ → ℝ) (aT x₀ ν : ℝ) {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)}
    {cut' : Finset (CTorus d L N₁' m₁ (k + 1) × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bk z, μ) ∈ cut'))
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hlx : ∀ n, 1 ≤ n → n ≤ k + 1 → (bk x ∈ H.layer n ↔ x ∈ G.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ k + 1 → (bk y ∈ H.layer n ↔ y ∈ G.layer n)) :
    cutXFullMatrix H a aT x₀ ν cut' (bk x) (bk y) = cutXFullMatrix G a aT x₀ ν cut x y := by
  have hfull := cutFullMatrix_corr (G := G) (H := H) a ν hn hn' hcut hx hy hlx hly
  have havg := avgMatrix_corr (G := G) (H := H) a hn hn' hx hy hlx hly
  unfold cutFullMatrix at hfull
  unfold cutXFullMatrix
  simp only [Matrix.add_apply] at hfull ⊢
  rw [xAvgMatrix_corr a _ _ hn hn' hx hy hlx hly]
  congr 1
  linarith

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ'} {ρ : ℕ}

/-- **The cut x-variant operators are reindexings of each other.** -/
theorem cutXOperator_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)}
    {cut' : Finset (CTorus d L N₁' m₁ (k + 1) × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bk z, μ) ∈ cut'))
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (cutXOperator G a aT x₀ ν cut α).submatrix hI.e.symm hI.e.symm =
      cutXOperator H a aT x₀ ν cut' α' := by
  ext x' y'
  obtain ⟨x, rfl⟩ := hI.e.surjective x'
  obtain ⟨y, rfl⟩ := hI.e.surjective y'
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have ⟨h1, h2⟩ := hI.two_lt
  unfold cutXOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [coe_e, coe_e, cutXFullMatrix_corr a aT x₀ ν (ρ := ρ) (by omega) (by omega) hcut
    (hI.boxG x x.2) (hI.boxG y y.2)
    (fun n h1 h2 => hI.layer_iff (hI.inBox_succ x.2) h1 h2)
    (fun n h1 h2 => hI.layer_iff (hI.inBox_succ y.2) h1 h2)]
  congr 1
  simp only [EmbeddingLike.apply_eq_iff_eq, hα]

/-- The x-variant Dirichlet operators. -/
theorem xDirichletOperator_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (xDirichletOperator G a aT x₀ ν α).submatrix hI.e.symm hI.e.symm =
      xDirichletOperator H a aT x₀ ν α' := by
  rw [← cutXOperator_empty, ← cutXOperator_empty]
  exact hI.cutXOperator_submatrix a aT x₀ ν (fun z _ μ => by simp) hα

/-- The x-variant cube resolvents of a centre of the box and of its image. -/
theorem cubeGx_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ) {j : ℕ}
    (hj : j ≤ k + 1) {y0 : CTorus d L N₁ m₁ (k + 1)}
    (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y0)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (cubeGx G a aT x₀ ν α ((j, y0) : ℕ × CTorus d L N₁ m₁ (k + 1))).submatrix hI.e.symm
        hI.e.symm = cubeGx H a aT x₀ ν α' ((j, bk y0) : ℕ × CTorus d L N₁' m₁ (k + 1)) := by
  unfold cubeGx cubeHx
  rw [← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, ← Matrix.inv_submatrix_equiv,
    hI.cutXOperator_submatrix a aT x₀ ν (fun z hz μ => hI.cubeCut_iff
      (fun w hw => hI.intBox_iff hj hy0 hw) hz μ) hα, hI.cD_submatrix hj hy0]

/-- The x-variant cube resolvent at a centre of the cover. -/
theorem cubeGx_cover_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x) :
    (cubeGx G a aT x₀ ν α q).submatrix hI.e.symm hI.e.symm = cubeGx H a aT x₀ ν α' (ck q) := by
  obtain ⟨⟨-, hj⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  obtain ⟨j, y0⟩ := q
  exact hI.cubeGx_submatrix a aT x₀ ν hj (hI.base_inBox hq) hα

/-- The partition weights of the own cover as multipliers on `Ω₁`. -/
theorem chiD_self_submatrix (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) : (chiD G q).submatrix hI.e.symm hI.e.symm = chiD H (ck q) :=
  hI.chiD_submatrix hI hq

/-- The x-variant commutators `K^x_z`. -/
theorem Kzx_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    (Kzx G a aT x₀ ν q).submatrix hI.e.symm hI.e.symm = Kzx H a aT x₀ ν (ck q) := by
  unfold Kzx
  rw [submatrix_sub_apply, ← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm,
    ← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, hI.chiD_self_submatrix hq,
    hI.xDirichletOperator_submatrix a aT x₀ ν (α := 0) (α' := 0) (fun _ => rfl)]

/-- **`G*_{x,s}(A)`.** -/
theorem Gstarx_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P) :
    (Gstarx G a aT x₀ ν α s).submatrix hI.e.symm hI.e.symm = Gstarx H a aT x₀ ν α' s' := by
  unfold Gstarx
  refine hI.coverSum_submatrix hI.e.symm (fun q hq => ?_) hs
  rw [← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, hI.chiD_self_submatrix hq,
    hI.cubeGx_cover_submatrix a aT x₀ ν hq hα]

/-- **`𝒦_{x,s}(A)`.** -/
theorem Kcalx_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P) :
    (Kcalx G a aT x₀ ν α s).submatrix hI.e.symm hI.e.symm = Kcalx H a aT x₀ ν α' s' := by
  unfold Kcalx
  refine hI.coverSum_submatrix hI.e.symm (fun q hq => ?_) hs
  rw [← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, hI.Kzx_submatrix a aT x₀ ν hq,
    hI.cubeGx_cover_submatrix a aT x₀ ν hq hα]

/-- **The x-variant decoupled Green's operator `G_{k,x,s}(A)`.** -/
theorem Gsx_submatrix (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs : ∀ P ∈ cubeIdx G, s' (ck P) = s P) :
    (Gsx G a aT x₀ ν α s).submatrix hI.e.symm hI.e.symm = Gsx H a aT x₀ ν α' s' := by
  unfold Gsx
  rw [← Matrix.submatrix_mul_equiv _ _ _ hI.e.symm, ← Matrix.inv_submatrix_equiv,
    submatrix_sub_apply, Matrix.submatrix_one_equiv, hI.Gstarx_submatrix a aT x₀ ν hα hs,
    hI.Kcalx_submatrix a aT x₀ ν hα hs]

end OmegaIso

end Balaban.Polymer.LocalIso
