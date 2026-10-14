/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairIndexMatch
public import Balaban.Polymer.TwoTorusDecSol

/-!
# CubeOpMatch: the cube operators of two generating sets on one torus

The replacement of P3 pp. 78-79 recomputes each term of the step on the local generator
`𝔹_{k+1}(Y)`.  Its second input (after the cover indices, `LocalPairIndexMatch.lean`) is that the
cube operators of the decoupled Green's function agree for two generating sets `H`, `H'` of the
same torus at a cube `□_z` near which their layers agree: the cut operator `H_z(A)` of the cube
is block diagonal (the cube is block aligned), so its inverse on the box block `□_z × □_z` is the
inverse of that block, and the block only reads the layers on the nearest-neighbour stencil of
`□_z` and the potential on `□_z`.  The matrices live on the different index spaces `H.Ω 1` and
`H'.Ω 1`; entries are compared at sites of both.  The abstract block transport
(`inv_block_transport`, `mul_apply_transport`) is the one of the two-tori comparison.

* `mem_Ω_one_cross`, `mem_cubeCut_cross`: `Ω₁` and the cube cut agree where the layers agree;
* `cutFullMatrix_apply_cross`, `cutOperator_apply_cross`, `cubeH_apply_cross`: the entries;
* `cubeG_mulVec_supp_of_aligned`, `cubeG_apply_cross`: the cube resolvent `G^{(z)} c_z`;
* `Dec2.cubeG_apply_cross`, `Dec2.chiD_cubeG_apply_cross`, `Dec2.Kz_cubeG_apply_cross`: the
  forms for two pairs `(C, H)`, `(C', H')` with `Dec2.CoverBase`, as they enter `G*_s` and `𝒦_s`;
* `level_localB_stencil_layer_iff`: the stencil hypothesis at the instance ambient level set
  versus `𝔹_{k+1}(Y) = localB (k + 1) … Y`, at sites whose stencil has its `𝒞_{k+1}`-cubes in `Y`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix
  Balaban.Fluctuation Balaban.LargeField Balaban.Polymer.TwoTorusStep

section Cross

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- **`Ω₁` agrees where the layers agree**: a site in the same layers `1 ≤ n ≤ K` of `H` and `H'`
lies in `Ω₁(H)` exactly when it lies in `Ω₁(H')`. -/
theorem mem_Ω_one_cross {y : CTorus d L N₁ m₁ K}
    (h : ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) :
    y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1 := by
  constructor
  · intro hy
    obtain ⟨n, hn1, hnK, hyn⟩ := H.exists_layer hy
    exact H'.layer_subset hn1 hnK ((h n hn1 hnK).1 hyn)
  · intro hy
    obtain ⟨n, hn1, hnK, hyn⟩ := H'.exists_layer hy
    exact H.layer_subset hn1 hnK ((h n hn1 hnK).2 hyn)

/-- **The cube cut agrees at a bond whose two ends lie in the same `Ω₁`.** -/
theorem mem_cubeCut_cross {Λ : Finset (CTorus d L N₁ m₁ K)} {z : CTorus d L N₁ m₁ K} {μ : Fin d}
    (hz : z ∈ H.Ω 1 ↔ z ∈ H'.Ω 1)
    (hz' : z + Pi.single μ 1 ∈ H.Ω 1 ↔ z + Pi.single μ 1 ∈ H'.Ω 1) :
    (z, μ) ∈ cubeCut H Λ ↔ (z, μ) ∈ cubeCut H' Λ := by
  rw [mem_cubeCut, mem_cubeCut, hz, hz']

/-- **The entries of `-Δ + ν + Q* a Q` with a cut removed**, for two generating sets: they agree
at `(x, y)` if the cuts agree at the bonds `(x, μ)`, `(x - e_μ, μ)`, `(y, μ)` and the layers of `H`
and `H'` agree at `x` and at `y`. -/
theorem cutFullMatrix_apply_cross (a : ℕ → ℝ) (ν : ℝ)
    {cut cut' : Finset (CTorus d L N₁ m₁ K × Fin d)} {x y : CTorus d L N₁ m₁ K}
    (hcx : ∀ μ : Fin d, ((x, μ) ∈ cut' ↔ (x, μ) ∈ cut) ∧
      ((x - Pi.single μ 1, μ) ∈ cut' ↔ (x - Pi.single μ 1, μ) ∈ cut))
    (hcy : ∀ μ : Fin d, (y, μ) ∈ cut' ↔ (y, μ) ∈ cut)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) :
    cutFullMatrix H' a ν cut' x y = cutFullMatrix H a ν cut x y := by
  unfold cutFullMatrix cutLaplacian
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have e1 : ∀ μ : Fin d, ((x, μ) ∈ cut') ↔ ((x, μ) ∈ cut) := fun μ => (hcx μ).1
  have e2 : ∀ μ : Fin d, ((x - Pi.single μ 1, μ) ∈ cut') ↔ ((x - Pi.single μ 1, μ) ∈ cut) :=
    fun μ => (hcx μ).2
  rw [sum_bondMatrix_apply, sum_bondMatrix_apply]
  simp only [e1, e2, hcy]
  congr 1
  unfold avgMatrix
  rw [Matrix.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.1 hn
  simp only [Matrix.smul_apply, smul_eq_mul]
  unfold layerProjMatrix
  simp only [hlx n hn1 hnK, hly n hn1 hnK]

/-- **The entries of the cut operator**, for two generating sets: under the hypotheses of
`cutFullMatrix_apply_cross` and `α' = α` at `x`, the entries at two sites of both `Ω₁` agree. -/
theorem cutOperator_apply_cross (a : ℕ → ℝ) (ν : ℝ)
    {cut cut' : Finset (CTorus d L N₁ m₁ K × Fin d)} {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1)
    (hy' : y ∈ H'.Ω 1)
    (hcx : ∀ μ : Fin d, ((x, μ) ∈ cut' ↔ (x, μ) ∈ cut) ∧
      ((x - Pi.single μ 1, μ) ∈ cut' ↔ (x - Pi.single μ 1, μ) ∈ cut))
    (hcy : ∀ μ : Fin d, (y, μ) ∈ cut' ↔ (y, μ) ∈ cut)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hαx : α' ⟨x, hx'⟩ = α ⟨x, hx⟩) :
    cutOperator H' a ν cut' α' ⟨x, hx'⟩ ⟨y, hy'⟩ = cutOperator H a ν cut α ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold cutOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [cutFullMatrix_apply_cross a ν hcx hcy hlx hly]
  by_cases hxy : x = y
  · subst hxy
    simp [hαx]
  · have h1 : ¬ (⟨x, hx'⟩ : H'.Ω 1) = ⟨y, hy'⟩ := fun h => hxy (congrArg Subtype.val h)
    have h2 : ¬ (⟨x, hx⟩ : H.Ω 1) = ⟨y, hy⟩ := fun h => hxy (congrArg Subtype.val h)
    simp [h1, h2]

/-- **The entries of the Dirichlet operator** `H_D(0)` of two generating sets agree at two sites
whose layers agree. -/
theorem dirichletOperator_apply_cross (a : ℕ → ℝ) (ν : ℝ) {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) :
    dirichletOperator H' a ν 0 ⟨x, hx'⟩ ⟨y, hy'⟩ = dirichletOperator H a ν 0 ⟨x, hx⟩ ⟨y, hy⟩ := by
  rw [← cutOperator_empty, ← cutOperator_empty]
  exact cutOperator_apply_cross a ν hx hx' hy hy' (fun μ => ⟨Iff.rfl, Iff.rfl⟩) (fun μ => Iff.rfl)
    hlx hly rfl

/-- **CubeOpMatch, the cube operator.**  If the layers of `H` and `H'` agree on the
nearest-neighbour stencil of every site of the interaction cube `□_z` and `α' = α` on `□_z`, the
entries of the cut operators `H_z(A)` of the cube at two sites of `□_z` (of both `Ω₁`) agree. -/
theorem cubeH_apply_cross (a : ℕ → ℝ) (ν : ℝ) {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    {q : ℕ × CTorus d L N₁ m₁ K}
    (hnb : ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ intBox q →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1)
    (hy' : y ∈ H'.Ω 1) (hxq : x ∈ intBox q) (hyq : y ∈ intBox q) :
    cubeH H' a ν α' q ⟨x, hx'⟩ ⟨y, hy'⟩ = cubeH H a ν α q ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hΩ : ∀ w ∈ intBox q, ∀ v : CTorus d L N₁ m₁ K,
      (v = w ∨ ∃ μ : Fin d, v = w + Pi.single μ 1 ∨ v = w - Pi.single μ 1) →
        (v ∈ H.Ω 1 ↔ v ∈ H'.Ω 1) := fun w hw v hv => mem_Ω_one_cross (hnb w hw v hv)
  have hcut : ∀ w ∈ intBox q, ∀ μ : Fin d,
      ((w, μ) ∈ cubeCut H' (intBox q) ↔ (w, μ) ∈ cubeCut H (intBox q)) ∧
        ((w - Pi.single μ 1, μ) ∈ cubeCut H' (intBox q) ↔
          (w - Pi.single μ 1, μ) ∈ cubeCut H (intBox q)) := by
    intro w hw μ
    refine ⟨(mem_cubeCut_cross (hΩ w hw w (Or.inl rfl))
      (hΩ w hw _ (Or.inr ⟨μ, Or.inl rfl⟩))).symm, (mem_cubeCut_cross
        (hΩ w hw _ (Or.inr ⟨μ, Or.inr rfl⟩)) ?_).symm⟩
    rw [sub_add_cancel]
    exact hΩ w hw w (Or.inl rfl)
  unfold cubeH
  exact cutOperator_apply_cross a ν hx hx' hy hy' (hcut x hxq) (fun μ => (hcut y hyq μ).1)
    (hnb x hxq x (Or.inl rfl)) (hnb y hyq y (Or.inl rfl)) (hα x hx hx' hxq).symm

/-- **`G^{(z)}(A) c_z f` is supported in the interaction cube** for a block-aligned cube with an
invertible cut operator (`Dec2.cubeG_supp` without the pair hypotheses). -/
theorem cubeG_mulVec_supp_of_aligned {a : ℕ → ℝ} {ν : ℝ} {α : H.Ω 1 → ℂ}
    {q : ℕ × CTorus d L N₁ m₁ K} (hΛ : BlockAligned H (intBox q))
    (hU : IsUnit (cubeH H a ν α q)) (f : H.Ω 1 → ℂ) (z : H.Ω 1)
    (hz : (z : CTorus d L N₁ m₁ K) ∉ intBox q) : (cubeG H a ν α q *ᵥ f) z = 0 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hH : cubeH H a ν α q *ᵥ (cubeG H a ν α q *ᵥ f) = cD H q *ᵥ f := by
    unfold cubeG
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  exact cutOperator_inv_supported H hΛ α hU (f := cD H q *ᵥ f)
    (fun w hw => by rw [cD_mulVec]; simp [hw]) hH z hz

/-- **CubeOpMatch, the cube resolvent.**  Let the cube `□_z` be block aligned for `H` and for `H'`,
with invertible cut operators, let the layers of `H` and `H'` agree on the nearest-neighbour
stencil of every site of `□_z` and `α' = α` on `□_z`.  Then the entries of
`G^{(z)}(A) c_z = H_z(A)⁻¹ c_z` agree at every two sites of both `Ω₁` (on the box block this is the
inverse of the common block of `H_z`; elsewhere both vanish). -/
theorem cubeG_apply_cross {a : ℕ → ℝ} {ν : ℝ} {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    {q : ℕ × CTorus d L N₁ m₁ K} (hΛ : BlockAligned H (intBox q))
    (hΛ' : BlockAligned H' (intBox q)) (hU : IsUnit (cubeH H a ν α q))
    (hU' : IsUnit (cubeH H' a ν α' q))
    (hnb : ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ intBox q →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1)
    (hy' : y ∈ H'.Ω 1) :
    cubeG H' a ν α' q ⟨x, hx'⟩ ⟨y, hy'⟩ = cubeG H a ν α q ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  have hΩ : ∀ w ∈ intBox q, (w ∈ H.Ω 1 ↔ w ∈ H'.Ω 1) := fun w hw =>
    mem_Ω_one_cross (hnb w hw w (Or.inl rfl))
  obtain ⟨ι, hι⟩ : ∃ ι : H.Ω 1 → H'.Ω 1, ∀ w : H.Ω 1, ι w =
      if h : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1 then ⟨w, h⟩ else ⟨x, hx'⟩ := ⟨_, fun _ => rfl⟩
  have hιv : ∀ w : H.Ω 1, (w : CTorus d L N₁ m₁ K) ∈ intBox q →
      ((ι w : H'.Ω 1) : CTorus d L N₁ m₁ K) = w := by
    intro w hw
    rw [hι, dite_eq_left ((hΩ w hw).1 w.2)]
  have hcore : ∀ u v : H.Ω 1, (u : CTorus d L N₁ m₁ K) ∈ intBox q →
      (v : CTorus d L N₁ m₁ K) ∈ intBox q →
      cubeG H' a ν α' q (ι u) (ι v) = cubeG H a ν α q u v := by
    intro u v hu hv
    unfold cubeG
    refine inv_block_transport (fun w : H.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ intBox q)
      (fun w : H'.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ intBox q) ι
      (fun w₁ w₂ h₁ h₂ h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
      (fun f z => cD_mulVec _ f z) (fun f z => cD_mulVec _ f z) (fun w₁ w₂ h₁ h₂ => ?_)
      (fun u hu w hw => cutOperator_mulVec_apply_of_not_mem H hΛ α hu w hw) hU hU'
      (fun f z hz => ?_) hu hv
    · exact Subtype.ext ((hιv w₁ h₁).symm.trans ((congrArg Subtype.val h).trans (hιv w₂ h₂)))
    · show ((ι w : H'.Ω 1) : CTorus d L N₁ m₁ K) ∈ intBox q
      rw [hιv w hw]; exact hw
    · refine ⟨⟨w', (hΩ w' hw').2 w'.2⟩, hw', Subtype.ext ?_⟩
      exact hιv ⟨w', (hΩ w' hw').2 w'.2⟩ hw'
    · have e₁ : ι w₁ = ⟨w₁, (hΩ w₁ h₁).1 w₁.2⟩ := Subtype.ext (hιv w₁ h₁)
      have e₂ : ι w₂ = ⟨w₂, (hΩ w₂ h₂).1 w₂.2⟩ := Subtype.ext (hιv w₂ h₂)
      rw [e₁, e₂]
      exact cubeH_apply_cross a ν hnb hα w₁.2 _ w₂.2 _ h₁ h₂
    · exact cubeG_mulVec_supp_of_aligned hΛ' hU' f z hz
  by_cases hyq : y ∈ intBox q
  · by_cases hxq : x ∈ intBox q
    · have e₁ : ι ⟨x, hx⟩ = ⟨x, hx'⟩ := Subtype.ext (hιv ⟨x, hx⟩ hxq)
      have e₂ : ι ⟨y, hy⟩ = ⟨y, hy'⟩ := Subtype.ext (hιv ⟨y, hy⟩ hyq)
      rw [← e₁, ← e₂]
      exact hcore _ _ hxq hyq
    · have e₁ := cubeG_mulVec_supp_of_aligned hΛ hU (Pi.single ⟨y, hy⟩ 1) ⟨x, hx⟩ hxq
      have e₂ := cubeG_mulVec_supp_of_aligned hΛ' hU' (Pi.single ⟨y, hy'⟩ 1) ⟨x, hx'⟩ hxq
      rw [cubeG_mulVec_single] at e₁ e₂
      rw [e₁, e₂]
  · rw [cubeG_apply_of_not_mem (G := H') q ⟨x, hx'⟩ ⟨y, hy'⟩ hyq,
      cubeG_apply_of_not_mem (G := H) q ⟨x, hx⟩ ⟨y, hy⟩ hyq]

end Cross

namespace Dec2

section Pair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {C C' : DecCover d L N₁ m₁ K}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν Kc Cx Kc' Cx' : ℝ}

/-- **CubeOpMatch for two pairs** `(C, H)`, `(C', H')` with `Dec2.CoverBase`: at a centre of both
covers, admissible potentials agreeing on `□_z` and layers agreeing on the stencil of `□_z`, the
entries of the cube resolvents agree at every two sites of both `Ω₁`. -/
theorem cubeG_apply_cross (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc' Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α')
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx) (hq' : q ∈ C'.cubeIdx)
    (hnb : ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ intBox q →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1)
    (hy' : y ∈ H'.Ω 1) :
    cubeG H' a ν α' q ⟨x, hx'⟩ ⟨y, hy'⟩ = cubeG H a ν α q ⟨x, hx⟩ ⟨y, hy⟩ :=
  Localization.cubeG_apply_cross (S.blockAligned q hq) (S'.blockAligned q hq')
    (Dec2.cubeH_isUnit S hαA hq) (Dec2.cubeH_isUnit S' hαB hq') hnb hα hx hx' hy hy'

/-- **The entries of `χ_z G^{(z)} c_z`** of two pairs agree at every two sites of both `Ω₁`, if
moreover the partition functions `χ_z` of the two covers agree on `□_z`. -/
theorem chiD_cubeG_apply_cross (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc' Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α')
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx) (hq' : q ∈ C'.cubeIdx)
    (hnb : ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hchi : ∀ x ∈ intBox q, C.chi q x = C'.chi q x)
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ intBox q →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1)
    (hy' : y ∈ H'.Ω 1) :
    (chiD C' H' q * cubeG H' a ν α' q) ⟨x, hx'⟩ ⟨y, hy'⟩ =
      (chiD C H q * cubeG H a ν α q) ⟨x, hx⟩ ⟨y, hy⟩ := by
  unfold Dec2.chiD
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul,
    Dec2.cubeG_apply_cross S S' hαA hαB hq hq' hnb hα hx hx' hy hy']
  by_cases hxq : x ∈ intBox q
  · simp only [hchi x hxq]
  · have e := Dec2.cubeG_supp S hαA hq (Pi.single ⟨y, hy⟩ 1) ⟨x, hx⟩ hxq
    rw [cubeG_mulVec_single] at e
    simp only [e, mul_zero]

/-- **The entries of `K_z G^{(z)} c_z`** of two pairs agree at every two sites of both `Ω₁`, under
the hypotheses of `chiD_cubeG_apply_cross` (`K_z = χ_z H_D - H_D χ_z`; at a site off `□_z` both
rows vanish, `rowSupp_Kz_cubeG`). -/
theorem Kz_cubeG_apply_cross (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc' Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α')
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx) (hq' : q ∈ C'.cubeIdx)
    (hnb : ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hchi : ∀ x ∈ intBox q, C.chi q x = C'.chi q x)
    (hα : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ intBox q →
      α ⟨x, hx⟩ = α' ⟨x, hx'⟩)
    {x y : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1) (hy : y ∈ H.Ω 1)
    (hy' : y ∈ H'.Ω 1) :
    (Kz C' H' a ν q * cubeG H' a ν α' q) ⟨x, hx'⟩ ⟨y, hy'⟩ =
      (Kz C H a ν q * cubeG H a ν α q) ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  have hΩ : ∀ w ∈ intBox q, (w ∈ H.Ω 1 ↔ w ∈ H'.Ω 1) := fun w hw =>
    mem_Ω_one_cross (hnb w hw w (Or.inl rfl))
  have hrow : ∀ (M : Matrix (H.Ω 1) (H.Ω 1) ℂ) (u v : H.Ω 1),
      (M *ᵥ Pi.single v 1) u = M u v := fun M u v => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hrow' : ∀ (M : Matrix (H'.Ω 1) (H'.Ω 1) ℂ) (u v : H'.Ω 1),
      (M *ᵥ Pi.single v 1) u = M u v := fun M u v => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  by_cases hxq : x ∈ intBox q
  · obtain ⟨ι, hι⟩ : ∃ ι : H.Ω 1 → H'.Ω 1, ∀ w : H.Ω 1, ι w =
        if h : (w : CTorus d L N₁ m₁ K) ∈ H'.Ω 1 then ⟨w, h⟩ else ⟨x, hx'⟩ := ⟨_, fun _ => rfl⟩
    have hιv : ∀ w : H.Ω 1, (w : CTorus d L N₁ m₁ K) ∈ intBox q →
        ((ι w : H'.Ω 1) : CTorus d L N₁ m₁ K) = w := by
      intro w hw
      rw [hι, dite_eq_left ((hΩ w hw).1 w.2)]
    have e₁ : ι ⟨x, hx⟩ = ⟨x, hx'⟩ := Subtype.ext (hιv ⟨x, hx⟩ hxq)
    rw [← e₁]
    refine mul_apply_transport (fun w : H.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ intBox q)
      (fun w : H'.Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ intBox q) ι
      (fun w₁ w₂ h₁ h₂ h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _ ?_ ?_ ?_
    · exact Subtype.ext ((hιv w₁ h₁).symm.trans ((congrArg Subtype.val h).trans (hιv w₂ h₂)))
    · show ((ι w : H'.Ω 1) : CTorus d L N₁ m₁ K) ∈ intBox q
      rw [hιv w hw]; exact hw
    · exact ⟨⟨w', (hΩ w' hw').2 w'.2⟩, hw', Subtype.ext (hιv ⟨w', (hΩ w' hw').2 w'.2⟩ hw')⟩
    · intro w hw
      have e := Dec2.cubeG_supp S hαA hq (Pi.single ⟨y, hy⟩ 1) w hw
      rw [hrow] at e
      rw [e, mul_zero]
    · intro w' hw'
      have e := Dec2.cubeG_supp S' hαB hq' (Pi.single ⟨y, hy'⟩ 1) w' hw'
      rw [hrow'] at e
      rw [e, mul_zero]
    · rintro ⟨w, hwΩ⟩ hw
      have hw' : w ∈ intBox q := hw
      have ew : ι ⟨w, hwΩ⟩ = ⟨w, (hΩ w hw').1 hwΩ⟩ := Subtype.ext (hιv ⟨w, hwΩ⟩ hw')
      rw [e₁, ew, Dec2.Kz_apply 0, Dec2.Kz_apply 0,
        Dec2.cubeG_apply_cross S S' hαA hαB hq hq' hnb hα hwΩ _ hy hy',
        dirichletOperator_apply_cross a ν hx hx' hwΩ _ (hnb x hxq x (Or.inl rfl))
          (hnb w hw' w (Or.inl rfl))]
      simp only [hchi x hxq, hchi w hw']
  · have e := Dec2.rowSupp_Kz_cubeG (α := α) S hq (Pi.single ⟨y, hy⟩ 1) ⟨x, hx⟩ hxq
    have e' := Dec2.rowSupp_Kz_cubeG (α := α') S' hq' (Pi.single ⟨y, hy'⟩ 1) ⟨x, hx'⟩ hxq
    rw [hrow] at e
    rw [hrow'] at e'
    rw [e, e']

end Pair

end Dec2

section LevelLocal

open Balaban.SmallField.GsSpec

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The stencil hypothesis at the local generator**: if every site of the nearest-neighbour
stencil of every site of `□_z` has its `𝒞_{k+1}`-cube in `Y`, the layers of the ambient level set
(`IsLevel 𝔹_{k+1} (k + 1)`) and of `𝔹_{k+1}(Y) = localB (k + 1) … Y` agree on that stencil (the
hypothesis `hnb` of `cubeG_apply_cross`). -/
theorem level_localB_stencil_layer_iff (hG' : IsLevel Gp (k + 1)) (hk : k + 1 ≤ k + 1)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {ϱl : ℝ} (hsep : ϱl ≤ minSep L (L ^ m₁))
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hdeep : ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ w : CTorus d L N₁ m₁ (k + 1),
          fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
              (torusCast w : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
            fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
              (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) → w ∈ Y) :
    ∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ k + 1 →
          (y ∈ Gp.layer n ↔ y ∈ (GsSpec.localB (k + 1) hk Y hsep).layer n) :=
  fun x hx y hy _ hn hnK => level_localB_layer_iff hG' hk Y hsep (hdeep x hx y hy) hn hnK

end LevelLocal

end Balaban.Localization
