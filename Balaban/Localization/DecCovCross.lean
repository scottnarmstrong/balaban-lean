/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairGs
public import Balaban.Localization.Dec2Covariance
public import Balaban.Localization.Decoupled2XLocal
public import Balaban.Localization.DecCovCutSupport
public import Balaban.Polymer.TwoTorusXGreen
import Mathlib.Tactic.Linarith

/-!
# The decoupled covariance of two generator pairs on a common component

Draft header; see the module doc below.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Balaban.Polymer.TwoTorusStep

/-! ### Generic block algebra -/

section Generic

variable {U A B C A' B' C' : Type*}

theorem sum_range_of_inj [Fintype U] [Fintype B] (f : U → B) (hf : Function.Injective f)
    (g : B → ℂ) (h0 : ∀ b, (∀ u, f u ≠ b) → g b = 0) : ∑ b, g b = ∑ u, g (f u) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (f := g) (g := f) (fun x _ y _ h => hf h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro b _ hb
  exact h0 b fun u hu => hb (Finset.mem_image.2 ⟨u, Finset.mem_univ _, hu⟩)

/-- **A product of two matrices on a block.**  The terms of the product at the rows `fA u`,
`fA' u` and columns `fC w`, `fC' w` vanish off the range of `fB`, `fB'`; the blocks of `M`, `N` and
`M'`, `N'` correspond. -/
theorem mul_block_corr' [Fintype B] [Fintype B'] {UA UB UC : Type*} [Fintype UB]
    (fA : UA → A) (fA' : UA → A') (fB : UB → B) (fB' : UB → B') (fC : UC → C) (fC' : UC → C')
    (hB : Function.Injective fB) (hB' : Function.Injective fB')
    (M : Matrix A B ℂ) (N : Matrix B C ℂ) (M' : Matrix A' B' ℂ) (N' : Matrix B' C' ℂ)
    (hM : ∀ u w b, (∀ v, fB v ≠ b) → M (fA u) b * N b (fC w) = 0)
    (hM' : ∀ u w b, (∀ v, fB' v ≠ b) → M' (fA' u) b * N' b (fC' w) = 0)
    (hMc : ∀ u v, M' (fA' u) (fB' v) = M (fA u) (fB v))
    (hNc : ∀ v w, N' (fB' v) (fC' w) = N (fB v) (fC w)) (u : UA) (w : UC) :
    (M' * N') (fA' u) (fC' w) = (M * N) (fA u) (fC w) := by
  have h1 : ∑ b, M (fA u) b * N b (fC w) = ∑ v, M (fA u) (fB v) * N (fB v) (fC w) :=
    sum_range_of_inj fB hB (fun b => M (fA u) b * N b (fC w)) (hM u w)
  have h2 : ∑ b, M' (fA' u) b * N' b (fC' w) =
      ∑ v, M' (fA' u) (fB' v) * N' (fB' v) (fC' w) :=
    sum_range_of_inj fB' hB' (fun b => M' (fA' u) b * N' b (fC' w)) (hM' u w)
  rw [Matrix.mul_apply, Matrix.mul_apply, h1, h2]
  exact Finset.sum_congr rfl fun v _ => by rw [hMc, hNc]

/-- **A product of two matrices on a block**, rows of the left factor supported on the block. -/
theorem mul_block_corr [Fintype B] [Fintype B'] {UA UB UC : Type*} [Fintype UB]
    (fA : UA → A) (fA' : UA → A') (fB : UB → B) (fB' : UB → B') (fC : UC → C) (fC' : UC → C')
    (hB : Function.Injective fB) (hB' : Function.Injective fB')
    (M : Matrix A B ℂ) (N : Matrix B C ℂ) (M' : Matrix A' B' ℂ) (N' : Matrix B' C' ℂ)
    (hM : ∀ u b, M (fA u) b ≠ 0 → ∃ v, fB v = b)
    (hM' : ∀ u b, M' (fA' u) b ≠ 0 → ∃ v, fB' v = b)
    (hMc : ∀ u v, M' (fA' u) (fB' v) = M (fA u) (fB v))
    (hNc : ∀ v w, N' (fB' v) (fC' w) = N (fB v) (fC w)) (u : UA) (w : UC) :
    (M' * N') (fA' u) (fC' w) = (M * N) (fA u) (fC w) :=
  mul_block_corr' fA fA' fB fB' fC fC' hB hB' M N M' N'
    (fun u w b hb => by
      by_contra h
      obtain ⟨v, hv⟩ := hM u b (left_ne_zero_of_mul h)
      exact hb v hv)
    (fun u w b hb => by
      by_contra h
      obtain ⟨v, hv⟩ := hM' u b (left_ne_zero_of_mul h)
      exact hb v hv) hMc hNc u w

/-- **The block of an inverse.**  If the rows `f u` of an invertible `M` read only columns in the
range of `f`, then the block of `M⁻¹` is the inverse of the block of `M`: `M_b M⁻¹_b = 1`. -/
theorem block_mul_inv_eq_one [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A]
    (f : U → A) (hf : Function.Injective f) (M : Matrix A A ℂ) (hU : IsUnit M)
    (hr : ∀ u b, M (f u) b ≠ 0 → ∃ v, f v = b) :
    (Matrix.of fun u v => M (f u) (f v)) * (Matrix.of fun u v => M⁻¹ (f u) (f v)) = 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  ext u w
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hdet) (f u)) (f w)
  rw [Matrix.mul_apply] at h
  have h1 : ∑ b, M (f u) b * M⁻¹ b (f w) = ∑ v, M (f u) (f v) * M⁻¹ (f v) (f w) := by
    refine sum_range_of_inj f hf (fun b => M (f u) b * M⁻¹ b (f w)) fun b hb => ?_
    by_contra h
    obtain ⟨v, hv⟩ := hr u b (left_ne_zero_of_mul h)
    exact hb v hv
  rw [h1] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [h]
  simp only [Matrix.one_apply, hf.eq_iff]

/-- **Corresponding blocks have corresponding inverse blocks.** -/
theorem inv_block_corr [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] (f : U → A) (f' : U → A') (hf : Function.Injective f)
    (hf' : Function.Injective f') (M : Matrix A A ℂ) (M' : Matrix A' A' ℂ) (hU : IsUnit M)
    (hU' : IsUnit M') (hr : ∀ u b, M (f u) b ≠ 0 → ∃ v, f v = b)
    (hr' : ∀ u b, M' (f' u) b ≠ 0 → ∃ v, f' v = b)
    (hc : ∀ u v, M' (f' u) (f' v) = M (f u) (f v)) (u v : U) :
    M'⁻¹ (f' u) (f' v) = M⁻¹ (f u) (f v) := by
  have h1 := block_mul_inv_eq_one f hf M hU hr
  have h2 := block_mul_inv_eq_one f' hf' M' hU' hr'
  have hb : (Matrix.of fun u v => M' (f' u) (f' v)) = Matrix.of fun u v => M (f u) (f v) := by
    ext u v; exact hc u v
  rw [hb] at h2
  have e1 := Matrix.inv_eq_right_inv h1
  have e2 := Matrix.inv_eq_right_inv h2
  have := congrFun (congrFun (e2.symm.trans e1) u) v
  simpa using this

end Generic

/-! ### The x-variant cube operators of two generating sets on one torus -/

section XCross

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- The entries of the averaging form of the x-variant at two sites agree for two generating sets
whose layers agree at the two sites. -/
theorem xAvgMatrix_apply_cross (a : ℕ → ℝ) (s₁ s₂ : ℝ) {x y : CTorus d L N₁ m₁ (k + 1)}
    (hlx : ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ H.layer n ↔ x ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) :
    xAvgMatrix H' a s₁ s₂ x y = xAvgMatrix H a s₁ s₂ x y := by
  unfold xAvgMatrix
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  unfold layerBlockMatrix
  have hj : ∀ j, 1 ≤ j → j ≤ k + 1 →
      ((x ∈ H'.layer j ∧ y ∈ H'.layer j) ↔ (x ∈ H.layer j ∧ y ∈ H.layer j)) :=
    fun j h1 h2 => and_congr (hlx j h1 h2).symm (hly j h1 h2).symm
  have hs : ∑ j ∈ Finset.Icc 1 k, a j / ((L : ℝ) ^ j) ^ 2 *
        (if x ∈ H'.layer j ∧ y ∈ H'.layer j then
          blockProjMatrix d (N₁ * L ^ m₁ * L ^ (k + 1)) (L ^ j) (N₁ * L ^ m₁ * L ^ (k + 1 - j)) x y
          else 0) =
      ∑ j ∈ Finset.Icc 1 k, a j / ((L : ℝ) ^ j) ^ 2 *
        (if x ∈ H.layer j ∧ y ∈ H.layer j then
          blockProjMatrix d (N₁ * L ^ m₁ * L ^ (k + 1)) (L ^ j) (N₁ * L ^ m₁ * L ^ (k + 1 - j)) x y
          else 0) := by
    refine Finset.sum_congr rfl fun j hjm => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hjm
    simp only [hj j h1 (by omega)]
  rw [hs]
  simp only [hj (k + 1) (by omega) le_rfl]

/-- **The entries of `-Δ + ν + (x-variant averaging form)` with a cut removed**, for two generating
sets (the x-variant of `cutFullMatrix_apply_cross`). -/
theorem cutXFullMatrix_apply_cross (a : ℕ → ℝ) (aT x ν : ℝ)
    {cut cut' : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)} {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)}
    (hcx : ∀ μ : Fin d, ((x₀, μ) ∈ cut' ↔ (x₀, μ) ∈ cut) ∧
      ((x₀ - Pi.single μ 1, μ) ∈ cut' ↔ (x₀ - Pi.single μ 1, μ) ∈ cut))
    (hcy : ∀ μ : Fin d, (y₀, μ) ∈ cut' ↔ (y₀, μ) ∈ cut)
    (hlx : ∀ n, 1 ≤ n → n ≤ k + 1 → (x₀ ∈ H.layer n ↔ x₀ ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ k + 1 → (y₀ ∈ H.layer n ↔ y₀ ∈ H'.layer n)) :
    cutXFullMatrix H' a aT x ν cut' x₀ y₀ = cutXFullMatrix H a aT x ν cut x₀ y₀ := by
  unfold cutXFullMatrix cutLaplacian
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have e1 : ∀ μ : Fin d, ((x₀, μ) ∈ cut') ↔ ((x₀, μ) ∈ cut) := fun μ => (hcx μ).1
  have e2 : ∀ μ : Fin d, ((x₀ - Pi.single μ 1, μ) ∈ cut') ↔ ((x₀ - Pi.single μ 1, μ) ∈ cut) :=
    fun μ => (hcx μ).2
  rw [sum_bondMatrix_apply, sum_bondMatrix_apply]
  simp only [e1, e2, hcy]
  congr 1
  exact xAvgMatrix_apply_cross a _ _ hlx hly

/-- **The entries of the cut x-variant operator** for two generating sets. -/
theorem cutXOperator_apply_cross (a : ℕ → ℝ) (aT x ν : ℝ)
    {cut cut' : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)} {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)} (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1) (hy : y₀ ∈ H.Ω 1)
    (hy' : y₀ ∈ H'.Ω 1)
    (hcx : ∀ μ : Fin d, ((x₀, μ) ∈ cut' ↔ (x₀, μ) ∈ cut) ∧
      ((x₀ - Pi.single μ 1, μ) ∈ cut' ↔ (x₀ - Pi.single μ 1, μ) ∈ cut))
    (hcy : ∀ μ : Fin d, (y₀, μ) ∈ cut' ↔ (y₀, μ) ∈ cut)
    (hlx : ∀ n, 1 ≤ n → n ≤ k + 1 → (x₀ ∈ H.layer n ↔ x₀ ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ k + 1 → (y₀ ∈ H.layer n ↔ y₀ ∈ H'.layer n))
    (hαx : α' ⟨x₀, hx'⟩ = α ⟨x₀, hx⟩) :
    cutXOperator H' a aT x ν cut' α' ⟨x₀, hx'⟩ ⟨y₀, hy'⟩ =
      cutXOperator H a aT x ν cut α ⟨x₀, hx⟩ ⟨y₀, hy⟩ := by
  unfold cutXOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [cutXFullMatrix_apply_cross a aT x ν hcx hcy hlx hly]
  by_cases hxy : x₀ = y₀
  · subst hxy
    simp [hαx]
  · have h1 : ¬ (⟨x₀, hx'⟩ : H'.Ω 1) = ⟨y₀, hy'⟩ := fun h => hxy (congrArg Subtype.val h)
    have h2 : ¬ (⟨x₀, hx⟩ : H.Ω 1) = ⟨y₀, hy⟩ := fun h => hxy (congrArg Subtype.val h)
    simp [h1, h2]

/-- **The entries of the x-variant operator** `H_{k,x}(α)` agree for two generating sets at two
sites whose layers agree, for potentials agreeing at the first site. -/
theorem xDirichletOperator_apply_cross (a : ℕ → ℝ) (aT x ν : ℝ) {α : H.Ω 1 → ℂ}
    {α' : H'.Ω 1 → ℂ} {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)} (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1)
    (hy : y₀ ∈ H.Ω 1) (hy' : y₀ ∈ H'.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ k + 1 → (x₀ ∈ H.layer n ↔ x₀ ∈ H'.layer n))
    (hly : ∀ n, 1 ≤ n → n ≤ k + 1 → (y₀ ∈ H.layer n ↔ y₀ ∈ H'.layer n))
    (hαx : α' ⟨x₀, hx'⟩ = α ⟨x₀, hx⟩) :
    xDirichletOperator H' a aT x ν α' ⟨x₀, hx'⟩ ⟨y₀, hy'⟩ =
      xDirichletOperator H a aT x ν α ⟨x₀, hx⟩ ⟨y₀, hy⟩ := by
  rw [← cutXOperator_empty, ← cutXOperator_empty]
  exact cutXOperator_apply_cross a aT x ν hx hx' hy hy' (fun μ => ⟨Iff.rfl, Iff.rfl⟩)
    (fun μ => Iff.rfl) hlx hly hαx

/-- **The entries of the x-variant cube operator** `H^{(z)}_x(A)` agree for two generating sets, if
the layers agree on the nearest-neighbour stencil of every site of the interaction cube and
`α' = α` on the cube. -/
theorem cubeHx_apply_cross (a : ℕ → ℝ) (aT x ν : ℝ) {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ}
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hnb : ∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1),
      x₀ ∈ intBox q → α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)} (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1) (hy : y₀ ∈ H.Ω 1)
    (hy' : y₀ ∈ H'.Ω 1) (hxq : x₀ ∈ intBox q) (hyq : y₀ ∈ intBox q) :
    cubeHx H' a aT x ν α' q ⟨x₀, hx'⟩ ⟨y₀, hy'⟩ = cubeHx H a aT x ν α q ⟨x₀, hx⟩ ⟨y₀, hy⟩ := by
  have hΩ : ∀ w ∈ intBox q, ∀ v : CTorus d L N₁ m₁ (k + 1),
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
  unfold cubeHx
  exact cutXOperator_apply_cross a aT x ν hx hx' hy hy' (hcut x₀ hxq)
    (fun μ => (hcut y₀ hyq μ).1) (hnb x₀ hxq x₀ (Or.inl rfl)) (hnb y₀ hyq y₀ (Or.inl rfl))
    (hα x₀ hx hx' hxq).symm

end XCross

/-! ### The cube resolvent of the x-variant for two pairs -/

namespace Dec2

section XPair

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {C C' : DecCover d L N₁ m₁ (k + 1)}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {H' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
variable {a : ℕ → ℝ} {aT x ν Cx Cx' : ℝ}

theorem cubeGx_apply_eq_inv_of_mem {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {α : G.Ω 1 → ℂ}
    (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (u b : G.Ω 1)
    (hb : (b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q) :
    cubeGx G a aT x ν α q u b = (cubeHx G a aT x ν α q)⁻¹ u b := by
  unfold cubeGx cD
  rw [Matrix.mul_diagonal]
  simp [hb]

/-- A row of the cube operator at a site of the cube only reads sites of the cube. -/
theorem cubeHx_row_in_box {ϱ₀ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {α : G.Ω 1 → ℂ} {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hΛ : BlockAligned G (intBox q))
    (y b : G.Ω 1) (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q)
    (hne : cubeHx G a aT x ν α q y b ≠ 0) : (b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q := by
  by_contra hb
  refine hne ?_
  have h := cutXOperator_mulVec_apply_of_mem (a := a) (aT := aT) (x := x) (ν := ν) (α := α)
    hΛ (u := Pi.single b 1) (fun z hz => by
      have : z ≠ b := fun h => hb (h ▸ hz)
      simp [this]) y hy
  rwa [mulVec_single_apply] at h

/-- **CubeOpMatch for the x-variant.**  The entries of the cube resolvent
`G^{(z)}_x(A) c_z` of two pairs agree at every two sites of both `Ω₁`, if the layers agree on the
stencil of the cube and `α' = α` on the cube. -/
theorem cubeGx_apply_cross (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (hq' : q ∈ C'.cubeIdx)
    (hnb : ∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1),
      x₀ ∈ intBox q → α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1) (hx₀' : x₀ ∈ H'.Ω 1)
    (hy₀ : y₀ ∈ H.Ω 1) (hy₀' : y₀ ∈ H'.Ω 1) :
    cubeGx H' a aT x ν α' q ⟨x₀, hx₀'⟩ ⟨y₀, hy₀'⟩ = cubeGx H a aT x ν α q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ := by
  classical
  have hΩ : ∀ w ∈ intBox q, (w ∈ H.Ω 1 ↔ w ∈ H'.Ω 1) := fun w hw =>
    mem_Ω_one_cross (hnb w hw w (Or.inl rfl))
  by_cases hyq : y₀ ∈ intBox q
  · by_cases hxq : x₀ ∈ intBox q
    · obtain ⟨f, hf⟩ : ∃ f : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ intBox q ∧ z ∈ H.Ω 1} → H.Ω 1,
          ∀ u, f u = ⟨u.1, u.2.2⟩ := ⟨_, fun _ => rfl⟩
      obtain ⟨f', hf'⟩ : ∃ f' : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ intBox q ∧ z ∈ H.Ω 1} →
          H'.Ω 1, ∀ u, f' u = ⟨u.1, (hΩ u.1 u.2.1).1 u.2.2⟩ := ⟨_, fun _ => rfl⟩
      have hfi : Function.Injective f := fun u v h => by
        have := congrArg Subtype.val h
        rw [hf, hf] at this
        exact Subtype.ext this
      have hfi' : Function.Injective f' := fun u v h => by
        have := congrArg Subtype.val h
        rw [hf', hf'] at this
        exact Subtype.ext this
      have key := inv_block_corr f f' hfi hfi' (cubeHx H a aT x ν α q) (cubeHx H' a aT x ν α' q)
        ((Matrix.isUnit_iff_isUnit_det _).2 ?_) ((Matrix.isUnit_iff_isUnit_det _).2 ?_) ?_ ?_ ?_
        ⟨x₀, hxq, hx₀⟩ ⟨y₀, hyq, hy₀⟩
      · simp only [hf, hf'] at key
        rw [cubeGx_apply_eq_inv_of_mem q _ _ hyq, cubeGx_apply_eq_inv_of_mem q _ _ hyq]
        exact key
      · exact (Matrix.isUnit_iff_isUnit_det _).1 (cubeHx_isUnit S hαA hx hq)
      · exact (Matrix.isUnit_iff_isUnit_det _).1 (cubeHx_isUnit S' hαB hx hq')
      · intro u b hne
        have hbq := cubeHx_row_in_box (a := a) (aT := aT) (x := x) (ν := ν) (S.blockAligned q hq) (f u) b (by rw [hf]; exact u.2.1) hne
        refine ⟨⟨b.1, hbq, b.2⟩, ?_⟩
        rw [hf]
      · intro u b hne
        have hbq := cubeHx_row_in_box (a := a) (aT := aT) (x := x) (ν := ν) (S'.blockAligned q hq') (f' u) b (by rw [hf']; exact u.2.1) hne
        refine ⟨⟨b.1, hbq, (hΩ _ hbq).2 b.2⟩, ?_⟩
        rw [hf']
      · intro u v
        simp only [hf, hf']
        exact cubeHx_apply_cross a aT x ν hnb hα u.2.2 ((hΩ _ u.2.1).1 u.2.2) v.2.2
          ((hΩ _ v.2.1).1 v.2.2) u.2.1 v.2.1
    · have e₁ := cubeGx_supp S hαA hx hq (Pi.single ⟨y₀, hy₀⟩ 1) ⟨x₀, hx₀⟩ hxq
      have e₂ := cubeGx_supp S' hαB hx hq' (Pi.single ⟨y₀, hy₀'⟩ 1) ⟨x₀, hx₀'⟩ hxq
      rw [cubeGx_mulVec_single] at e₁ e₂
      rw [e₁, e₂]
  · rw [cubeGx_apply_of_not_mem (G := H') q ⟨x₀, hx₀'⟩ ⟨y₀, hy₀'⟩ hyq,
      cubeGx_apply_of_not_mem (G := H) q ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ hyq]

/-- **The entries of `χ_z G^{(z)}_x c_z`** of two pairs agree at every two sites of both `Ω₁`, if
moreover the partition functions `χ_z` of the two covers agree on `□_z`. -/
theorem chiD_cubeGx_apply_cross (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (hq' : q ∈ C'.cubeIdx)
    (hnb : ∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hchi : ∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1),
      x₀ ∈ intBox q → α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1) (hx₀' : x₀ ∈ H'.Ω 1)
    (hy₀ : y₀ ∈ H.Ω 1) (hy₀' : y₀ ∈ H'.Ω 1) :
    (chiD C' H' q * cubeGx H' a aT x ν α' q) ⟨x₀, hx₀'⟩ ⟨y₀, hy₀'⟩ =
      (chiD C H q * cubeGx H a aT x ν α q) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ := by
  unfold Dec2.chiD
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul,
    cubeGx_apply_cross S S' hαA hαB hx hq hq' hnb hα hx₀ hx₀' hy₀ hy₀']
  by_cases hxq : x₀ ∈ intBox q
  · simp only [hchi x₀ hxq]
  · have e := cubeGx_supp S hαA hx hq (Pi.single ⟨y₀, hy₀⟩ 1) ⟨x₀, hx₀⟩ hxq
    rw [cubeGx_mulVec_single] at e
    simp only [e, mul_zero]

/-- **The entries of `K^x_z G^{(z)}_x c_z`** of two pairs agree at every two sites of both `Ω₁`,
under the hypotheses of `chiD_cubeGx_apply_cross`. -/
theorem Kzx_cubeGx_apply_cross (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ C.cubeIdx) (hq' : q ∈ C'.cubeIdx)
    (hnb : ∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hchi : ∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1),
      x₀ ∈ intBox q → α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ y₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1) (hx₀' : x₀ ∈ H'.Ω 1)
    (hy₀ : y₀ ∈ H.Ω 1) (hy₀' : y₀ ∈ H'.Ω 1) :
    (Kzx C' H' a aT x ν q * cubeGx H' a aT x ν α' q) ⟨x₀, hx₀'⟩ ⟨y₀, hy₀'⟩ =
      (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩ := by
  classical
  have hΩ : ∀ w ∈ intBox q, (w ∈ H.Ω 1 ↔ w ∈ H'.Ω 1) := fun w hw =>
    mem_Ω_one_cross (hnb w hw w (Or.inl rfl))
  by_cases hxq : x₀ ∈ intBox q
  · obtain ⟨f, hf⟩ : ∃ f : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ intBox q ∧ z ∈ H.Ω 1} → H.Ω 1,
        ∀ u, f u = ⟨u.1, u.2.2⟩ := ⟨_, fun _ => rfl⟩
    obtain ⟨f', hf'⟩ : ∃ f' : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ intBox q ∧ z ∈ H.Ω 1} →
        H'.Ω 1, ∀ u, f' u = ⟨u.1, (hΩ u.1 u.2.1).1 u.2.2⟩ := ⟨_, fun _ => rfl⟩
    have hfi : Function.Injective f := fun u v h => by
      have := congrArg Subtype.val h
      rw [hf, hf] at this
      exact Subtype.ext this
    have hfi' : Function.Injective f' := fun u v h => by
      have := congrArg Subtype.val h
      rw [hf', hf'] at this
      exact Subtype.ext this
    have key := mul_block_corr' (fun _ : Unit => (⟨x₀, hx₀⟩ : H.Ω 1))
      (fun _ : Unit => (⟨x₀, hx₀'⟩ : H'.Ω 1)) f f' (fun _ : Unit => (⟨y₀, hy₀⟩ : H.Ω 1))
      (fun _ : Unit => (⟨y₀, hy₀'⟩ : H'.Ω 1)) hfi hfi' (Kzx C H a aT x ν q)
      (cubeGx H a aT x ν α q) (Kzx C' H' a aT x ν q) (cubeGx H' a aT x ν α' q)
      (fun u w b hb => ?_) (fun u w b hb => ?_) (fun u v => ?_) (fun v w => ?_) () ()
    · exact key
    · have hbq : (b : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q := fun h =>
        hb ⟨b.1, h, b.2⟩ (by rw [hf])
      have e := cubeGx_supp S hαA hx hq (Pi.single ⟨y₀, hy₀⟩ 1) b hbq
      rw [cubeGx_mulVec_single] at e
      show _ * cubeGx H a aT x ν α q b ⟨y₀, hy₀⟩ = 0
      rw [e, mul_zero]
    · have hbq : (b : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q := fun h =>
        hb ⟨b.1, h, (hΩ _ h).2 b.2⟩ (by rw [hf'])
      have e := cubeGx_supp S' hαB hx hq' (Pi.single ⟨y₀, hy₀'⟩ 1) b hbq
      rw [cubeGx_mulVec_single] at e
      show _ * cubeGx H' a aT x ν α' q b ⟨y₀, hy₀'⟩ = 0
      rw [e, mul_zero]
    · show Kzx C' H' a aT x ν q ⟨x₀, hx₀'⟩ (f' v) = Kzx C H a aT x ν q ⟨x₀, hx₀⟩ (f v)
      simp only [hf, hf']
      rw [Kzx_apply a aT x ν 0, Kzx_apply a aT x ν 0,
        xDirichletOperator_apply_cross (α := (0 : H.Ω 1 → ℂ)) (α' := (0 : H'.Ω 1 → ℂ)) a aT x ν hx₀ hx₀' v.2.2 ((hΩ _ v.2.1).1 v.2.2)
          (hnb x₀ hxq x₀ (Or.inl rfl)) (hnb v.1 v.2.1 v.1 (Or.inl rfl)) rfl]
      simp only [hchi x₀ hxq, hchi v.1 v.2.1]
    · show cubeGx H' a aT x ν α' q (f' v) ⟨y₀, hy₀'⟩ = cubeGx H a aT x ν α q (f v) ⟨y₀, hy₀⟩
      simp only [hf, hf']
      exact cubeGx_apply_cross S S' hαA hαB hx hq hq' hnb hα _ _ _ _
  · have e := rowSupp_Kzx_cubeGx (α := α) (x := x) S hq (Pi.single ⟨y₀, hy₀⟩ 1) ⟨x₀, hx₀⟩ hxq
    have e' := rowSupp_Kzx_cubeGx (α := α') (x := x) S' hq' (Pi.single ⟨y₀, hy₀'⟩ 1) ⟨x₀, hx₀'⟩ hxq
    rw [mulVec_single_apply] at e e'
    rw [e, e']

/-! ### The blocks of `G*_{x,s}` and `𝒦_{x,s}` of a pair on a union of cubes -/

variable {α : H.Ω 1 → ℂ}

/-- The block identity for `G*_{x,s}`: `P G* = G* P = ∑_{z inner} s_z χ_z G^{(z)}_x c_z`. -/
theorem Gstarx_block (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    indY H T * Gstarx C H a aT x ν α s =
        ∑ q ∈ innerCentres C H T, C.sProd s q • (chiD C H q * cubeGx H a aT x ν α q) ∧
      Gstarx C H a aT x ν α s * indY H T =
        ∑ q ∈ innerCentres C H T, C.sProd s q • (chiD C H q * cubeGx H a aT x ν α q) := by
  have hM : ∀ q ∈ C.cubeIdx, RowSupp (chiD C H q * cubeGx H a aT x ν α q) (intBox q) ∧
      chiD C H q * cubeGx H a aT x ν α q * cD H q = chiD C H q * cubeGx H a aT x ν α q :=
    fun q hq => ⟨rowSupp_chi_cubeGx S hx hα hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  obtain ⟨hin, hout⟩ := blk_conditions (s := s) _ hM hdich
  exact sum_block_facts _ hin hout

/-- The block identity for `𝒦_{x,s}`: `P 𝒦 = 𝒦 P = ∑_{z inner} s_z K^x_z G^{(z)}_x c_z`. -/
theorem Kcalx_block (S : XCover C H a aT ν Cx)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    indY H T * Kcalx C H a aT x ν α s =
        ∑ q ∈ innerCentres C H T, C.sProd s q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) ∧
      Kcalx C H a aT x ν α s * indY H T =
        ∑ q ∈ innerCentres C H T, C.sProd s q • (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) := by
  have hM : ∀ q ∈ C.cubeIdx, RowSupp (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) (intBox q) ∧
      Kzx C H a aT x ν q * cubeGx H a aT x ν α q * cD H q =
        Kzx C H a aT x ν q * cubeGx H a aT x ν α q :=
    fun q hq => ⟨rowSupp_Kzx_cubeGx S hq, by rw [Matrix.mul_assoc, cubeGx_mul_cD]⟩
  obtain ⟨hin, hout⟩ := blk_conditions (s := s) _ hM hdich
  exact sum_block_facts _ hin hout

/-- `Gstarx` has no matrix element between `T` and its complement. -/
theorem Gstarx_BD (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) (Gstarx C H a aT x ν α s) := by
  intro u v h
  obtain ⟨h1, h2⟩ := Gstarx_block S hx hα (s := s) hdich
  have e := congrFun (congrFun (h1.trans h2.symm) u) v
  rw [indY_mul_apply, mul_indY_apply] at e
  by_contra hne
  apply h
  by_cases hu : (u : CTorus d L N₁ m₁ (k + 1)) ∈ T
  · have hv : (v : CTorus d L N₁ m₁ (k + 1)) ∉ T := fun hv => hne ⟨fun _ => hv, fun _ => hu⟩
    rw [ite_eq_left hu, ite_eq_right hv] at e; exact e
  · have hv : (v : CTorus d L N₁ m₁ (k + 1)) ∈ T := by
      by_contra hv; exact hne ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    rw [ite_eq_right hu, ite_eq_left hv] at e; exact e.symm

/-- `Kcalx` has no matrix element between `T` and its complement. -/
theorem Kcalx_BD (S : XCover C H a aT ν Cx)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) (Kcalx C H a aT x ν α s) := by
  intro u v h
  obtain ⟨h1, h2⟩ := Kcalx_block (x := x) (α := α) S (s := s) hdich
  have e := congrFun (congrFun (h1.trans h2.symm) u) v
  rw [indY_mul_apply, mul_indY_apply] at e
  by_contra hne
  apply h
  by_cases hu : (u : CTorus d L N₁ m₁ (k + 1)) ∈ T
  · have hv : (v : CTorus d L N₁ m₁ (k + 1)) ∉ T := fun hv => hne ⟨fun _ => hv, fun _ => hu⟩
    rw [ite_eq_left hu, ite_eq_right hv] at e; exact e
  · have hv : (v : CTorus d L N₁ m₁ (k + 1)) ∈ T := by
      by_contra hv; exact hne ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    rw [ite_eq_right hu, ite_eq_left hv] at e; exact e.symm

/-- **`Gsx` has no matrix element between `T` and its complement**, for a set `T` such that every
active interaction cube lies inside `T` or avoids it. -/
theorem Gsx_BD_of_dich (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) (Gsx C H a aT x ν α s) :=
  (Gstarx_BD S hx hα hdich).mul (((BD.one _).sub (Kcalx_BD (x := x) (α := α) S hdich)).inv hU)

theorem Gstarx_apply_of_mem (S : XCover C H a aT ν Cx) (hx : 0 ≤ x) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {u : H.Ω 1} (hu : (u : CTorus d L N₁ m₁ (k + 1)) ∈ T) (v : H.Ω 1) :
    Gstarx C H a aT x ν α s u v =
      ∑ q ∈ innerCentres C H T, C.sProd s q * (chiD C H q * cubeGx H a aT x ν α q) u v := by
  have h := congrFun (congrFun (Gstarx_block S hx hα hdich).1 u) v
  rw [indY_mul_apply, ite_eq_left hu, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

theorem Kcalx_apply_of_mem (S : XCover C H a aT ν Cx)
    {T : Finset (CTorus d L N₁ m₁ (k + 1))} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {u : H.Ω 1} (hu : (u : CTorus d L N₁ m₁ (k + 1)) ∈ T) (v : H.Ω 1) :
    Kcalx C H a aT x ν α s u v =
      ∑ q ∈ innerCentres C H T, C.sProd s q * (Kzx C H a aT x ν q * cubeGx H a aT x ν α q) u v := by
  have h := congrFun (congrFun (Kcalx_block (x := x) (α := α) S hdich).1 u) v
  rw [indY_mul_apply, ite_eq_left hu, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

variable {α' : H'.Ω 1 → ℂ} {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {T : Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **CrossGs for the x-variant, the entries of `G*_{x,s}`.** -/
theorem Gstarx_apply_cross (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
      α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1) (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1)
    (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) :
    Gstarx C' H' a aT x ν α' s' ⟨x₀, hx₀'⟩ ⟨z, hz'⟩ = Gstarx C H a aT x ν α s ⟨x₀, hx₀⟩ ⟨z, hz⟩ := by
  classical
  rw [Gstarx_apply_of_mem S hx hαA hdich (u := ⟨x₀, hx₀⟩) hxT,
    Gstarx_apply_of_mem S' hx hαB hdich' (u := ⟨x₀, hx₀'⟩) hxT]
  refine sum_inner_cross (fun q hq hc => ?_) hin'
  obtain ⟨hq', hcc, hnb, hchi⟩ := hin q hq hc
  refine ⟨hq', hcc, ?_⟩
  have hqT : SubI H (intBox q) T := (Finset.mem_filter.1 hq).2
  exact chiD_cubeGx_apply_cross S S' hαA hαB hx (Finset.mem_filter.1 hq).1
    (Finset.mem_filter.1 hq').1 hnb hchi
    (fun w hw hw' hwq => hα w hw hw' (hqT ⟨w, hw⟩ hwq)) hx₀ hx₀' hz hz'

/-- **CrossGs for the x-variant, the entries of `𝒦_{x,s}`.** -/
theorem Kcalx_apply_cross (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
      α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1) (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1)
    (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) :
    Kcalx C' H' a aT x ν α' s' ⟨x₀, hx₀'⟩ ⟨z, hz'⟩ = Kcalx C H a aT x ν α s ⟨x₀, hx₀⟩ ⟨z, hz⟩ := by
  classical
  rw [Kcalx_apply_of_mem (x := x) (α := α) S hdich (u := ⟨x₀, hx₀⟩) hxT,
    Kcalx_apply_of_mem (x := x) (α := α') S' hdich' (u := ⟨x₀, hx₀'⟩) hxT]
  refine sum_inner_cross (fun q hq hc => ?_) hin'
  obtain ⟨hq', hcc, hnb, hchi⟩ := hin q hq hc
  refine ⟨hq', hcc, ?_⟩
  have hqT : SubI H (intBox q) T := (Finset.mem_filter.1 hq).2
  exact Kzx_cubeGx_apply_cross S S' hαA hαB hx (Finset.mem_filter.1 hq).1
    (Finset.mem_filter.1 hq').1 hnb hchi
    (fun w hw hw' hwq => hα w hw hw' (hqT ⟨w, hw⟩ hwq)) hx₀ hx₀' hz hz'

/-- **The common block of a set `T` of sites** in `Ω₁(H)` and `Ω₁(H')`, if `T` meets the two
sets in the same sites: the injections of `{z ∈ T ∩ Ω₁(H)}` into `H.Ω 1` and `H'.Ω 1`. -/
theorem exists_block_maps {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1)) :
    ∃ (f : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} → H.Ω 1)
      (f' : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} → H'.Ω 1),
      (∀ u, f u = ⟨u.1, u.2.2⟩) ∧ (∀ u, f' u = ⟨u.1, (hTΩ u.1 u.2.1).1 u.2.2⟩) ∧
      Function.Injective f ∧ Function.Injective f' := by
  refine ⟨fun u => ⟨u.1, u.2.2⟩, fun u => ⟨u.1, (hTΩ u.1 u.2.1).1 u.2.2⟩, fun _ => rfl,
    fun _ => rfl, fun u v h => ?_, fun u v h => ?_⟩
  · have h2 := congrArg (fun p : H.Ω 1 => (p : CTorus d L N₁ m₁ (k + 1))) h
    exact Subtype.ext h2
  · have h2 := congrArg (fun p : H'.Ω 1 => (p : CTorus d L N₁ m₁ (k + 1))) h
    exact Subtype.ext h2

/-- **CrossGs for the x-variant: the entries of `G_{k,x,s}` on `T`.**  Under the hypotheses of
`Gstarx_apply_cross` (with the layers of `H`, `H'` agreeing at the sites of `T`), `1 - 𝒦_{x,s}`
invertible for both pairs, the entries of `G_{k,x,s}` at a site of `T` agree. -/
theorem Gsx_apply_cross (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
    (hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1))
    (hlay : ∀ y ∈ T, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C' H' a aT x ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
      α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1) (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1)
    (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) :
    Gsx C' H' a aT x ν α' s' ⟨x₀, hx₀'⟩ ⟨z, hz'⟩ = Gsx C H a aT x ν α s ⟨x₀, hx₀⟩ ⟨z, hz⟩ := by
  classical
  have hB := Gsx_BD_of_dich S hx hαA hU hdich
  have hB' := Gsx_BD_of_dich S' hx hαB hU' hdich'
  by_cases hzT : z ∈ T
  · obtain ⟨f, f', hf, hf', hfi, hfi'⟩ := exists_block_maps (H := H) (H' := H') hTΩ
    have hGB := Gstarx_BD S hx hαA hdich
    have hGB' := Gstarx_BD S' hx hαB hdich'
    have hKB := (BD.one _).sub (Kcalx_BD (x := x) (α := α) S hdich)
    have hKB' := (BD.one _).sub (Kcalx_BD (x := x) (α := α') S' hdich')
    have hsurj : ∀ b : H.Ω 1, (b : CTorus d L N₁ m₁ (k + 1)) ∈ T →
        ∃ v, f v = b := fun b hb => ⟨⟨b.1, hb, b.2⟩, by rw [hf]⟩
    have hsurj' : ∀ b : H'.Ω 1, (b : CTorus d L N₁ m₁ (k + 1)) ∈ T →
        ∃ v, f' v = b := fun b hb => ⟨⟨b.1, hb, (hTΩ _ hb).2 b.2⟩, by rw [hf']⟩
    have hlayU : ∀ u : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1},
        ∀ n, 1 ≤ n → n ≤ k + 1 → (u.1 ∈ H.layer n ↔ u.1 ∈ H'.layer n) :=
      fun u => hlay u.1 u.2.1
    have key := mul_block_corr f f' f f' f f' hfi hfi' (Gstarx C H a aT x ν α s)
      ((1 - Kcalx C H a aT x ν α s)⁻¹) (Gstarx C' H' a aT x ν α' s')
      ((1 - Kcalx C' H' a aT x ν α' s')⁻¹)
      (fun u b hne => hsurj b ((hGB _ _ hne).1 (by rw [hf]; exact u.2.1)))
      (fun u b hne => hsurj' b ((hGB' _ _ hne).1 (by rw [hf']; exact u.2.1)))
      (fun u v => by
        simp only [hf, hf']
        exact Gstarx_apply_cross S S' hαA hαB hx hdich hdich' hin hin' hα _ _ _ _ u.2.1)
      (fun v w => ?_) ⟨x₀, hxT, hx₀⟩ ⟨z, hzT, hz⟩
    · simp only [hf, hf'] at key
      exact key
    · refine inv_block_corr f f' hfi hfi' _ _ hU hU' (fun u b hne => ?_) (fun u b hne => ?_)
        (fun u v => ?_) v w
      · exact hsurj b ((hKB _ _ hne).1 (by rw [hf]; exact u.2.1))
      · exact hsurj' b ((hKB' _ _ hne).1 (by rw [hf']; exact u.2.1))
      · simp only [Matrix.sub_apply, Matrix.one_apply, hfi.eq_iff, hfi'.eq_iff]
        rw [show Kcalx C' H' a aT x ν α' s' (f' u) (f' v) = Kcalx C H a aT x ν α s (f u) (f v) by
          simp only [hf, hf']
          exact Kcalx_apply_cross S S' hαA hαB hx hdich hdich' hin hin' hα _ _ _ _ u.2.1]
  · have e1 : Gsx C H a aT x ν α s ⟨x₀, hx₀⟩ ⟨z, hz⟩ = 0 := by
      by_contra h
      exact hzT ((hB _ _ h).1 hxT)
    have e2 : Gsx C' H' a aT x ν α' s' ⟨x₀, hx₀'⟩ ⟨z, hz'⟩ = 0 := by
      by_contra h
      exact hzT ((hB' _ _ h).1 hxT)
    rw [e1, e2]

section CovCross

variable {N : ℕ} {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- The common block of a set `T`, together with its product with `Fin N`. -/
theorem exists_block_maps_N {T : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1)) :
    ∃ (f : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} → H.Ω 1)
      (f' : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} → H'.Ω 1)
      (g : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N → H.Ω 1 × Fin N)
      (g' : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N → H'.Ω 1 × Fin N),
      (∀ u, f u = ⟨u.1, u.2.2⟩) ∧ (∀ u, f' u = ⟨u.1, (hTΩ u.1 u.2.1).1 u.2.2⟩) ∧
      (∀ w, g w = (f w.1, w.2)) ∧ (∀ w, g' w = (f' w.1, w.2)) ∧
      Function.Injective f ∧ Function.Injective f' ∧ Function.Injective g ∧
      Function.Injective g' ∧
      (∀ b : H.Ω 1, (b : CTorus d L N₁ m₁ (k + 1)) ∈ T → ∃ v, f v = b) ∧
      (∀ b : H'.Ω 1, (b : CTorus d L N₁ m₁ (k + 1)) ∈ T → ∃ v, f' v = b) ∧
      (∀ b : H.Ω 1 × Fin N, (b.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T → ∃ v, g v = b) ∧
      (∀ b : H'.Ω 1 × Fin N, (b.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T → ∃ v, g' v = b) := by
  obtain ⟨f, f', hf, hf', hfi, hfi'⟩ := exists_block_maps (H := H) (H' := H') hTΩ
  refine ⟨f, f', fun w => (f w.1, w.2), fun w => (f' w.1, w.2), hf, hf', fun _ => rfl,
    fun _ => rfl, hfi, hfi', fun u v h => ?_, fun u v h => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, fun b hb => ?_⟩
  · exact Prod.ext (hfi (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
  · exact Prod.ext (hfi' (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2
  · exact ⟨⟨b.1, hb, b.2⟩, by rw [hf]⟩
  · exact ⟨⟨b.1, hb, (hTΩ _ hb).2 b.2⟩, by rw [hf']⟩
  · exact ⟨(⟨b.1.1, hb, b.1.2⟩, b.2), by simp only [hf]⟩
  · exact ⟨(⟨b.1.1, hb, (hTΩ _ hb).2 b.1.2⟩, b.2), by simp only [hf']⟩

/-- The entries of the multiplication by `φ₀` agree at a site where the fields agree. -/
theorem fieldMul_apply_cross {y₀ z : CTorus d L N₁ m₁ (k + 1)} (hy : y₀ ∈ H.Ω 1)
    (hy' : y₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1) (i : Fin N)
    (hφ0 : φ' y₀ = φ y₀) :
    fieldMul (restrictField H' φ') (⟨y₀, hy'⟩, i) ⟨z, hz'⟩ =
      fieldMul (restrictField H φ) (⟨y₀, hy⟩, i) ⟨z, hz⟩ := by
  unfold fieldMul restrictField
  by_cases h : y₀ = z
  · subst h
    simp [hφ0]
  · have h1 : ¬ (⟨y₀, hy'⟩ : H'.Ω 1) = ⟨z, hz'⟩ := fun e => h (congrArg Subtype.val e)
    have h2 : ¬ (⟨y₀, hy⟩ : H.Ω 1) = ⟨z, hz⟩ := fun e => h (congrArg Subtype.val e)
    simp [h1, h2]

variable (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
  (hF : FootLocalGeom C) (hF' : FootLocalGeom C')
  (hαA : AdmPot H α) (hαB : AdmPot H' α') (hx : 0 ≤ x)
  (hlay : ∀ y ∈ T, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
  (hU : IsUnit (1 - Kcalx C H a aT x ν α s)) (hU' : IsUnit (1 - Kcalx C' H' a aT x ν α' s'))
  (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
  (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
    SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
  (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
    q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
    (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
      (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
    (∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀))
  (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
    q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
  (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
    α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
  (hφ : ∀ y ∈ T, φ' y = φ y)
  (hH : HRespects C H a aT x ν α s T) (hH' : HRespects C' H' a aT x ν α' s' T)
include S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ hH hH'

/-- The entries of `K(φ₀) Ĝ_{k,x,s}` (the commutator of `H_{k,x}` with the multiplication by `φ₀`
times the lifted Green operator) at sites of `T` agree. -/
theorem commK_Gsx_apply_cross {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1)
    (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) (j : Fin N) :
    (commK (xDirichletOperator H' a aT x ν α') (restrictField H' φ') *
        liftOp N (Gsx C' H' a aT x ν α' s')) ⟨x₀, hx₀'⟩ (⟨z, hz'⟩, j) =
      (commK (xDirichletOperator H a aT x ν α) (restrictField H φ) *
        liftOp N (Gsx C H a aT x ν α s)) ⟨x₀, hx₀⟩ (⟨z, hz⟩, j) := by
  classical
  have hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1) := fun y hy => mem_Ω_one_cross (hlay y hy)
  obtain ⟨f, f', g, g', hf, hf', hg, hg', hfi, hfi', hgi, hgi', hs, hs', hsN, hsN'⟩ :=
    exists_block_maps_N (N := N) (H := H) (H' := H') hTΩ
  have key := mul_block_corr' (fun _ : Unit => (⟨x₀, hx₀⟩ : H.Ω 1))
    (fun _ : Unit => (⟨x₀, hx₀'⟩ : H'.Ω 1)) g g' (fun _ : Unit => ((⟨z, hz⟩, j) : H.Ω 1 × Fin N))
    (fun _ : Unit => ((⟨z, hz'⟩, j) : H'.Ω 1 × Fin N)) hgi hgi'
    (commK (xDirichletOperator H a aT x ν α) (restrictField H φ))
    (liftOp N (Gsx C H a aT x ν α s))
    (commK (xDirichletOperator H' a aT x ν α') (restrictField H' φ'))
    (liftOp N (Gsx C' H' a aT x ν α' s'))
    (fun u w b hb => ?_) (fun u w b hb => ?_) (fun u v => ?_) (fun v w => ?_) () ()
  · exact key
  · beta_reduce at *
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨y', i⟩ := b
    rw [Balaban.Localization.commK_apply] at h1
    have hxy := left_ne_zero_of_mul h1
    have hG : Gsx C H a aT x ν α s y' ⟨z, hz⟩ ≠ 0 := by
      intro h0; apply h2; simp [liftOp, h0]
    have hcore : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Core C s := by
      by_contra hc; exact hG (Gsx_apply_eq_zero_of_not_core hF y' _ hc)
    have hyT : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ T := (hH _ y' hxy hcore).1 hxT
    obtain ⟨v, hv⟩ := hsN (y', i) hyT
    exact hb v hv
  · beta_reduce at *
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨y', i⟩ := b
    rw [Balaban.Localization.commK_apply] at h1
    have hxy := left_ne_zero_of_mul h1
    have hG : Gsx C' H' a aT x ν α' s' y' ⟨z, hz'⟩ ≠ 0 := by
      intro h0; apply h2; simp [liftOp, h0]
    have hcore : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Core C' s' := by
      by_contra hc; exact hG (Gsx_apply_eq_zero_of_not_core hF' y' _ hc)
    have hyT : (y' : CTorus d L N₁ m₁ (k + 1)) ∈ T := (hH' _ y' hxy hcore).1 hxT
    obtain ⟨v, hv⟩ := hsN' (y', i) hyT
    exact hb v hv
  · show commK (xDirichletOperator H' a aT x ν α') (restrictField H' φ') ⟨x₀, hx₀'⟩ (g' v) =
      commK (xDirichletOperator H a aT x ν α) (restrictField H φ) ⟨x₀, hx₀⟩ (g v)
    rw [hg, hg', Balaban.Localization.commK_apply, Balaban.Localization.commK_apply, hf, hf']
    rw [xDirichletOperator_apply_cross a aT x ν hx₀ hx₀' v.1.2.2 ((hTΩ _ v.1.2.1).1 v.1.2.2)
      (hlay x₀ hxT) (hlay v.1.1 v.1.2.1) (hα x₀ hx₀ hx₀' hxT).symm]
    simp only [restrictField, hφ x₀ hxT, hφ v.1.1 v.1.2.1]
  · show liftOp N (Gsx C' H' a aT x ν α' s') (g' v) (⟨z, hz'⟩, j) =
      liftOp N (Gsx C H a aT x ν α s) (g v) (⟨z, hz⟩, j)
    unfold liftOp
    simp only [hg, hg', hf, hf']
    split_ifs
    · exact Gsx_apply_cross S S' hαA hαB hx hTΩ hlay hU hU' hdich hdich' hin hin' hα v.1.2.2
        ((hTΩ _ v.1.2.1).1 v.1.2.2) hz hz' v.1.2.1
    · rfl

/-- **The entries of `M_{x,s} = φ₀² - K_x(φ₀) Ĝ_{k,x,s} φ₀`** at sites of `T` agree. -/
theorem decM_apply_cross {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1)
    (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) (hzT : z ∈ T) :
    decM C' H' a aT x ν α' s' φ' ⟨x₀, hx₀'⟩ ⟨z, hz'⟩ =
      decM C H a aT x ν α s φ ⟨x₀, hx₀⟩ ⟨z, hz⟩ := by
  classical
  have hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1) := fun y hy => mem_Ω_one_cross (hlay y hy)
  obtain ⟨f, f', g, g', hf, hf', hg, hg', hfi, hfi', hgi, hgi', hs, hs', hsN, hsN'⟩ :=
    exists_block_maps_N (N := N) (H := H) (H' := H') hTΩ
  unfold decM constraintM
  simp only [Matrix.sub_apply]
  have hFM : ∀ (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (φ0 : CTorus d L N₁ m₁ (k + 1) →
      Fin N → ℂ) (b : G.Ω 1 × Fin N) (y : G.Ω 1),
      fieldMul (restrictField G φ0) b y ≠ 0 → b.1 = y := by
    intro G φ0 b y h
    by_contra hne
    exact h (by simp [fieldMul, hne])
  have hFM' : ∀ (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') (φ0 : CTorus d L N₁ m₁ (k + 1) →
      Fin N → ℂ) (b : G.Ω 1 × Fin N) (y : G.Ω 1),
      fieldMul (restrictField G φ0) b y ≠ 0 → b.1 = y := by
    intro G φ0 b y h
    by_contra hne
    exact h (by simp [fieldMul, hne])
  congr 1
  · -- the term `φ₀ᵀ φ₀`
    have key := mul_block_corr' (fun _ : Unit => (⟨x₀, hx₀⟩ : H.Ω 1))
      (fun _ : Unit => (⟨x₀, hx₀'⟩ : H'.Ω 1)) g g' (fun _ : Unit => (⟨z, hz⟩ : H.Ω 1))
      (fun _ : Unit => (⟨z, hz'⟩ : H'.Ω 1)) hgi hgi' (fieldMul (restrictField H φ))ᵀ
      (fieldMul (restrictField H φ)) (fieldMul (restrictField H' φ'))ᵀ
      (fieldMul (restrictField H' φ')) (fun u w b hb => ?_) (fun u w b hb => ?_)
      (fun u v => ?_) (fun v w => ?_) () ()
    · exact key
    · by_contra hne
      have h1 := left_ne_zero_of_mul hne
      rw [Matrix.transpose_apply] at h1
      have := hFM H φ b _ h1
      obtain ⟨v, hv⟩ := hsN b (by rw [this]; exact hxT)
      exact hb v hv
    · by_contra hne
      have h1 := left_ne_zero_of_mul hne
      rw [Matrix.transpose_apply] at h1
      have := hFM' H' φ' b _ h1
      obtain ⟨v, hv⟩ := hsN' b (by rw [this]; exact hxT)
      exact hb v hv
    · show (fieldMul (restrictField H' φ'))ᵀ ⟨x₀, hx₀'⟩ (g' v) =
        (fieldMul (restrictField H φ))ᵀ ⟨x₀, hx₀⟩ (g v)
      rw [Matrix.transpose_apply, Matrix.transpose_apply, hg, hg']
      obtain ⟨⟨w, hw⟩, i⟩ := v
      simp only [hf, hf']
      exact fieldMul_apply_cross _ _ _ _ i (hφ w hw.1)
    · show fieldMul (restrictField H' φ') (g' v) ⟨z, hz'⟩ = fieldMul (restrictField H φ) (g v) ⟨z, hz⟩
      rw [hg, hg']
      obtain ⟨⟨w, hw⟩, i⟩ := v
      simp only [hf, hf']
      exact fieldMul_apply_cross _ _ _ _ i (hφ w hw.1)
  · -- the term `K(φ₀) Ĝ φ₀`
    have key := mul_block_corr' (fun _ : Unit => (⟨x₀, hx₀⟩ : H.Ω 1))
      (fun _ : Unit => (⟨x₀, hx₀'⟩ : H'.Ω 1)) g g' (fun _ : Unit => (⟨z, hz⟩ : H.Ω 1))
      (fun _ : Unit => (⟨z, hz'⟩ : H'.Ω 1)) hgi hgi'
      (commK (xDirichletOperator H a aT x ν α) (restrictField H φ) *
        liftOp N (Gsx C H a aT x ν α s)) (fieldMul (restrictField H φ))
      (commK (xDirichletOperator H' a aT x ν α') (restrictField H' φ') *
        liftOp N (Gsx C' H' a aT x ν α' s')) (fieldMul (restrictField H' φ'))
      (fun u w b hb => ?_) (fun u w b hb => ?_) (fun u v => ?_) (fun v w => ?_) () ()
    · exact key
    · by_contra hne
      have h1 := right_ne_zero_of_mul hne
      have := hFM H φ b _ h1
      obtain ⟨v, hv⟩ := hsN b (by rw [this]; exact hzT)
      exact hb v hv
    · by_contra hne
      have h1 := right_ne_zero_of_mul hne
      have := hFM' H' φ' b _ h1
      obtain ⟨v, hv⟩ := hsN' b (by rw [this]; exact hzT)
      exact hb v hv
    · show (commK (xDirichletOperator H' a aT x ν α') (restrictField H' φ') *
          liftOp N (Gsx C' H' a aT x ν α' s')) ⟨x₀, hx₀'⟩ (g' v) =
        (commK (xDirichletOperator H a aT x ν α) (restrictField H φ) *
          liftOp N (Gsx C H a aT x ν α s)) ⟨x₀, hx₀⟩ (g v)
      rw [hg, hg']
      obtain ⟨⟨w, hw⟩, i⟩ := v
      simp only [hf, hf']
      exact commK_Gsx_apply_cross S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ
        hH hH' hx₀ hx₀' hw.2 ((hTΩ _ hw.1).1 hw.2) hxT i
    · show fieldMul (restrictField H' φ') (g' v) ⟨z, hz'⟩ = fieldMul (restrictField H φ) (g v) ⟨z, hz⟩
      rw [hg, hg']
      obtain ⟨⟨w, hw⟩, i⟩ := v
      simp only [hf, hf']
      exact fieldMul_apply_cross _ _ _ _ i (hφ w hw.1)

/-- **The entries of `N_{x,s} f = φ₀ f - K_x(φ₀) Ĝ_{k,x,s} f`** at sites of `T` agree. -/
theorem decN_apply_cross {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1)
    (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) (hzT : z ∈ T)
    (j : Fin N) :
    decN C' H' a aT x ν α' s' φ' ⟨x₀, hx₀'⟩ (⟨z, hz'⟩, j) =
      decN C H a aT x ν α s φ ⟨x₀, hx₀⟩ (⟨z, hz⟩, j) := by
  unfold decN constraintN
  simp only [Matrix.sub_apply, Matrix.transpose_apply]
  rw [commK_Gsx_apply_cross S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ
    hH hH' hx₀ hx₀' hz hz' hxT j, fieldMul_apply_cross hz hz' hx₀ hx₀' j (hφ z hzT)]

/-- **The entries of `Π_{x,s}`** at sites of `T` agree. -/
theorem decPi_apply_cross (hM : IsUnit (decM C H a aT x ν α s φ))
    (hM' : IsUnit (decM C' H' a aT x ν α' s' φ'))
    {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1)
    (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) (hzT : z ∈ T)
    (i j : Fin N) :
    decPi C' H' a aT x ν α' s' φ' (⟨x₀, hx₀'⟩, i) (⟨z, hz'⟩, j) =
      decPi C H a aT x ν α s φ (⟨x₀, hx₀⟩, i) (⟨z, hz⟩, j) := by
  classical
  have hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1) := fun y hy => mem_Ω_one_cross (hlay y hy)
  obtain ⟨f, f', g, g', hf, hf', hg, hg', hfi, hfi', hgi, hgi', hs, hs', hsN, hsN'⟩ :=
    exists_block_maps_N (N := N) (H := H) (H' := H') hTΩ
  have hG := Gsx_BD_of_dich S hx hαA hU hdich
  have hG' := Gsx_BD_of_dich S' hx hαB hU' hdich'
  have hMBD : BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) (decM C H a aT x ν α s φ) :=
    decM_BD_of_GsxBD hF hG hH
  have hMBD' : BD (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) (decM C' H' a aT x ν α' s' φ') :=
    decM_BD_of_GsxBD hF' hG' hH'
  have hNBD : BD (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (decN C H a aT x ν α s φ) := decN_BD_of_GsxBD hF hG hH
  have hNBD' : BD (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun p : H'.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (decN C' H' a aT x ν α' s' φ') := decN_BD_of_GsxBD hF' hG' hH'
  have hLG : BD (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (liftOp N (Gsx C H a aT x ν α s)) := BD.liftOp hG
  have hLG' : BD (fun p : H'.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun p : H'.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (liftOp N (Gsx C' H' a aT x ν α' s')) := BD.liftOp hG'
  have hFM := fieldMul_BD (N := N) (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (restrictField H φ)
  have hFM' := fieldMul_BD (N := N) (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T)
    (restrictField H' φ')
  have hI := hMBD.inv hM
  have hI' := hMBD'.inv hM'
  have hLF := hLG.mul hFM
  have hLF' := hLG'.mul hFM'
  have hLFI := hLF.mul hI
  have hLFI' := hLF'.mul hI'
  -- step a: `liftOp Ĝ · φ₀`
  have stepA : ∀ (u : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N)
      (w : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1}),
      (liftOp N (Gsx C' H' a aT x ν α' s') * fieldMul (restrictField H' φ')) (g' u) (f' w) =
        (liftOp N (Gsx C H a aT x ν α s) * fieldMul (restrictField H φ)) (g u) (f w) := by
    intro u w
    refine mul_block_corr g g' g g' f f' hgi hgi' _ _ _ _ (fun u b hne => ?_) (fun u b hne => ?_)
      (fun u v => ?_) (fun v w => ?_) u w
    · exact hsN b ((hLG _ _ hne).1 (by rw [hg]; simp only [hf]; exact u.1.2.1))
    · exact hsN' b ((hLG' _ _ hne).1 (by rw [hg']; simp only [hf']; exact u.1.2.1))
    · obtain ⟨⟨w1, hw1⟩, i1⟩ := u
      obtain ⟨⟨w2, hw2⟩, i2⟩ := v
      show liftOp N (Gsx C' H' a aT x ν α' s') (g' (⟨w1, hw1⟩, i1)) (g' (⟨w2, hw2⟩, i2)) =
        liftOp N (Gsx C H a aT x ν α s) (g (⟨w1, hw1⟩, i1)) (g (⟨w2, hw2⟩, i2))
      unfold liftOp
      simp only [hg, hg', hf, hf']
      split_ifs
      · exact Gsx_apply_cross S S' hαA hαB hx hTΩ hlay hU hU' hdich hdich' hin hin' hα hw1.2
          ((hTΩ _ hw1.1).1 hw1.2) hw2.2 ((hTΩ _ hw2.1).1 hw2.2) hw1.1
      · rfl
    · obtain ⟨⟨w1, hw1⟩, i1⟩ := v
      obtain ⟨w2, hw2⟩ := w
      show fieldMul (restrictField H' φ') (g' (⟨w1, hw1⟩, i1)) (f' ⟨w2, hw2⟩) =
        fieldMul (restrictField H φ) (g (⟨w1, hw1⟩, i1)) (f ⟨w2, hw2⟩)
      simp only [hg, hg', hf, hf']
      exact fieldMul_apply_cross _ _ _ _ i1 (hφ w1 hw1.1)
  -- the inverse of `M`
  have hMc : ∀ u v : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1},
      decM C' H' a aT x ν α' s' φ' (f' u) (f' v) = decM C H a aT x ν α s φ (f u) (f v) := by
    intro u v
    simp only [hf, hf']
    exact decM_apply_cross S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ hH hH'
      u.2.2 ((hTΩ _ u.2.1).1 u.2.2) v.2.2 ((hTΩ _ v.2.1).1 v.2.2) u.2.1 v.2.1
  have hInv : ∀ u v : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1},
      (decM C' H' a aT x ν α' s' φ')⁻¹ (f' u) (f' v) = (decM C H a aT x ν α s φ)⁻¹ (f u) (f v) :=
    fun u v => inv_block_corr f f' hfi hfi' _ _ hM hM'
      (fun u b hne => hs b ((hMBD _ _ hne).1 (by rw [hf]; exact u.2.1)))
      (fun u b hne => hs' b ((hMBD' _ _ hne).1 (by rw [hf']; exact u.2.1))) hMc u v
  -- step b: `(liftOp Ĝ · φ₀) M⁻¹`
  have stepB : ∀ (u : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N)
      (w : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1}),
      (liftOp N (Gsx C' H' a aT x ν α' s') * fieldMul (restrictField H' φ') *
          (decM C' H' a aT x ν α' s' φ')⁻¹) (g' u) (f' w) =
        (liftOp N (Gsx C H a aT x ν α s) * fieldMul (restrictField H φ) *
          (decM C H a aT x ν α s φ)⁻¹) (g u) (f w) := by
    intro u w
    refine mul_block_corr g g' f f' f f' hfi hfi' _ _ _ _ (fun u b hne => ?_) (fun u b hne => ?_)
      (fun u v => stepA u v) (fun v w => hInv v w) u w
    · exact hs b ((hLF _ _ hne).1 (by rw [hg]; simp only [hf]; exact u.1.2.1))
    · exact hs' b ((hLF' _ _ hne).1 (by rw [hg']; simp only [hf']; exact u.1.2.1))
  -- step c: times `N`
  have stepC : ∀ (u w : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N),
      decPi C' H' a aT x ν α' s' φ' (g' u) (g' w) = decPi C H a aT x ν α s φ (g u) (g w) := by
    intro u w
    unfold decPi
    refine mul_block_corr g g' f f' g g' hfi hfi' _ _ _ _ (fun u b hne => ?_) (fun u b hne => ?_)
      (fun u v => stepB u v) (fun v w => ?_) u w
    · exact hs b ((hLFI _ _ hne).1 (by rw [hg]; simp only [hf]; exact u.1.2.1))
    · exact hs' b ((hLFI' _ _ hne).1 (by rw [hg']; simp only [hf']; exact u.1.2.1))
    · obtain ⟨⟨w1, hw1⟩, i1⟩ := w
      show decN C' H' a aT x ν α' s' φ' (f' v) (g' (⟨w1, hw1⟩, i1)) =
        decN C H a aT x ν α s φ (f v) (g (⟨w1, hw1⟩, i1))
      simp only [hg, hg', hf, hf']
      exact decN_apply_cross S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ
        hH hH' v.2.2 ((hTΩ _ v.2.1).1 v.2.2) hw1.2 ((hTΩ _ hw1.1).1 hw1.2) v.2.1 hw1.1 i1
  have := stepC (⟨x₀, hxT, hx₀⟩, i) (⟨z, hzT, hz⟩, j)
  simpa only [hg, hg', hf, hf'] using this

omit hF hF' hφ hH hH' in
/-- The entries of the lifted Green operator at sites of `T` agree. -/
theorem liftOp_Gsx_apply_cross {x₀ z : CTorus d L N₁ m₁ (k + 1)} (hx₀ : x₀ ∈ H.Ω 1)
    (hx₀' : x₀ ∈ H'.Ω 1) (hz : z ∈ H.Ω 1) (hz' : z ∈ H'.Ω 1) (hxT : x₀ ∈ T) (i j : Fin N) :
    liftOp N (Gsx C' H' a aT x ν α' s') (⟨x₀, hx₀'⟩, i) (⟨z, hz'⟩, j) =
      liftOp N (Gsx C H a aT x ν α s) (⟨x₀, hx₀⟩, i) (⟨z, hz⟩, j) := by
  have hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1) := fun y hy => mem_Ω_one_cross (hlay y hy)
  unfold liftOp
  split_ifs
  · exact Gsx_apply_cross S S' hαA hαB hx hTΩ hlay hU hU' hdich hdich' hin hin' hα hx₀ hx₀' hz hz'
      hxT
  · rfl

/-- **The entries of the decoupled covariance `C_x(s)` of two pairs agree** on a component `T`
(general form, with two coarse index sets).  `Q`, `P` (resp. `Q'`, `P'`) are block diagonal for
the splitting `cκ` (resp. `cκ'`) of the coarse index set: rows of `Q` with `cκ κ` read exactly the
sites of `T`.  The coarse indices with `cκ`, `cκ'` are matched by the common block `UK` through
injections `e`, `e'` onto them, and `Q`, `Q'`, `P`, `P'` correspond on it. -/
theorem decCov_block_cross {κι κι' UK : Type*} [Fintype κι] [DecidableEq κι] [Fintype κι']
    [DecidableEq κι'] [Fintype UK]
    (hM : IsUnit (decM C H a aT x ν α s φ)) (hM' : IsUnit (decM C' H' a aT x ν α' s' φ'))
    (cκ : κι → Prop) (cκ' : κι' → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (Q' : Matrix κι' (H'.Ω 1) ℂ)
    (P : Matrix κι κι ℂ) (P' : Matrix κι' κι' ℂ) (e : UK → κι) (e' : UK → κι')
    (hei : Function.Injective e) (hei' : Function.Injective e')
    (hes : ∀ κ, cκ κ → ∃ v, e v = κ) (hes' : ∀ κ, cκ' κ → ∃ v, e' v = κ)
    (hec : ∀ v, cκ (e v)) (hec' : ∀ v, cκ' (e' v))
    (hQ : BD cκ (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q)
    (hQ' : BD cκ' (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q')
    (hP : BD cκ cκ P) (hP' : BD cκ' cκ' P')
    (hQQ : ∀ (v : UK) (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1),
      y ∈ T → Q' (e' v) ⟨y, hy'⟩ = Q (e v) ⟨y, hy⟩)
    (hPP : ∀ v w : UK, P' (e' v) (e' w) = P (e v) (e w)) (v w : UK) (i j : Fin N) :
    decCov C' H' a aT x ν α' s' φ' Q' P' (e' v, i) (e' w, j) =
      decCov C H a aT x ν α s φ Q P (e v, i) (e w, j) := by
  classical
  have hTΩ : ∀ y ∈ T, (y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1) := fun y hy => mem_Ω_one_cross (hlay y hy)
  obtain ⟨f, f', g, g', hf, hf', hg, hg', hfi, hfi', hgi, hgi', hs, hs', hsN, hsN'⟩ :=
    exists_block_maps_N (N := N) (H := H) (H' := H') hTΩ
  obtain ⟨h, hh⟩ : ∃ h : UK × Fin N → κι × Fin N, ∀ w, h w = (e w.1, w.2) := ⟨_, fun _ => rfl⟩
  obtain ⟨h', hh'⟩ : ∃ h' : UK × Fin N → κι' × Fin N, ∀ w, h' w = (e' w.1, w.2) :=
    ⟨_, fun _ => rfl⟩
  have hhi : Function.Injective h := fun u v e₀ => by
    rw [hh, hh] at e₀
    exact Prod.ext (hei (Prod.ext_iff.1 e₀).1) (Prod.ext_iff.1 e₀).2
  have hhi' : Function.Injective h' := fun u v e₀ => by
    rw [hh', hh'] at e₀
    exact Prod.ext (hei' (Prod.ext_iff.1 e₀).1) (Prod.ext_iff.1 e₀).2
  have hsK : ∀ b : κι × Fin N, cκ b.1 → ∃ w, h w = b := fun b hb => by
    obtain ⟨v, hv⟩ := hes b.1 hb
    exact ⟨(v, b.2), by rw [hh, hv]⟩
  have hsK' : ∀ b : κι' × Fin N, cκ' b.1 → ∃ w, h' w = b := fun b hb => by
    obtain ⟨v, hv⟩ := hes' b.1 hb
    exact ⟨(v, b.2), by rw [hh', hv]⟩
  have hG := Gsx_BD_of_dich S hx hαA hU hdich
  have hG' := Gsx_BD_of_dich S' hx hαB hU' hdich'
  have hA : BD (fun p : κι × Fin N => cκ p.1) (fun p : κι × Fin N => cκ p.1)
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := covA_BD (N := N) cκ hP _ _ _
  have hA' : BD (fun p : κι' × Fin N => cκ' p.1) (fun p : κι' × Fin N => cκ' p.1)
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P')) := covA_BD (N := N) cκ' hP' _ _ _
  have hQl : BD (fun p : κι × Fin N => cκ p.1)
      (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T) (liftRect N Q) :=
    BD.liftOp hQ
  have hQl' : BD (fun p : κι' × Fin N => cκ' p.1)
      (fun p : H'.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T) (liftRect N Q') :=
    BD.liftOp hQ'
  have hTm : BD (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun p : H.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ) :=
    (BD.liftOp hG).sub (decPi_BD_of_GsxBD hF hG hH hM)
  have hTm' : BD (fun p : H'.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (fun p : H'.Ω 1 × Fin N => (p.1 : CTorus d L N₁ m₁ (k + 1)) ∈ T)
      (liftOp N (Gsx C' H' a aT x ν α' s') - decPi C' H' a aT x ν α' s' φ') :=
    (BD.liftOp hG').sub (decPi_BD_of_GsxBD hF' hG' hH' hM')
  have hQt := hQl.transpose
  have hQt' := hQl'.transpose
  have hAQ := hA.mul hQl
  have hAQ' := hA'.mul hQl'
  have hAQT := hAQ.mul hTm
  have hAQT' := hAQ'.mul hTm'
  have hAQTQ := hAQT.mul hQt
  have hAQTQ' := hAQT'.mul hQt'
  -- the baseline `A`
  have cA : ∀ u v : UK × Fin N,
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P') (h' u) (h' v) =
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) (h u) (h v) := by
    rintro ⟨u1, i1⟩ ⟨v1, j1⟩
    simp only [hh, hh', covA, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
      liftOp, Matrix.one_apply, Prod.mk.injEq, hei.eq_iff, hei'.eq_iff]
    rw [hPP u1 v1]
  -- `A Q`
  have cAQ : ∀ (u : UK × Fin N)
      (w : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N),
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P') * liftRect N Q') (h' u) (g' w) =
        (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q) (h u) (g w) := by
    intro u w
    refine mul_block_corr h h' h h' g g' hhi hhi' _ _ _ _ (fun u b hne => ?_) (fun u b hne => ?_)
      (fun u v => cA u v) (fun v w => ?_) u w
    · exact hsK b ((hA _ _ hne).1 (by rw [hh]; exact hec _))
    · exact hsK' b ((hA' _ _ hne).1 (by rw [hh']; exact hec' _))
    · obtain ⟨v1, j1⟩ := v
      obtain ⟨⟨w1, hw1⟩, i1⟩ := w
      show liftRect N Q' (h' (v1, j1)) (g' (⟨w1, hw1⟩, i1)) =
        liftRect N Q (h (v1, j1)) (g (⟨w1, hw1⟩, i1))
      simp only [hh, hh', hg, hg', hf, hf', liftRect]
      split_ifs
      · exact hQQ v1 w1 hw1.2 ((hTΩ _ hw1.1).1 hw1.2) hw1.1
      · rfl
  -- `A Q (liftOp Ĝ - Π)`
  have cAQT : ∀ (u : UK × Fin N)
      (w : {z : CTorus d L N₁ m₁ (k + 1) // z ∈ T ∧ z ∈ H.Ω 1} × Fin N),
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P') * liftRect N Q' *
        (liftOp N (Gsx C' H' a aT x ν α' s') - decPi C' H' a aT x ν α' s' φ')) (h' u) (g' w) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
        (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ)) (h u) (g w) := by
    intro u w
    refine mul_block_corr h h' g g' g g' hgi hgi' _ _ _ _ (fun u b hne => ?_)
      (fun u b hne => ?_) (fun u v => cAQ u v) (fun v w => ?_) u w
    · exact hsN b ((hAQ _ _ hne).1 (by rw [hh]; exact hec _))
    · exact hsN' b ((hAQ' _ _ hne).1 (by rw [hh']; exact hec' _))
    · obtain ⟨⟨v1, hv1⟩, j1⟩ := v
      obtain ⟨⟨w1, hw1⟩, i1⟩ := w
      show (liftOp N (Gsx C' H' a aT x ν α' s') - decPi C' H' a aT x ν α' s' φ')
          (g' (⟨v1, hv1⟩, j1)) (g' (⟨w1, hw1⟩, i1)) =
        (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ)
          (g (⟨v1, hv1⟩, j1)) (g (⟨w1, hw1⟩, i1))
      simp only [Matrix.sub_apply, hg, hg', hf, hf']
      rw [liftOp_Gsx_apply_cross S S' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hv1.2
        ((hTΩ _ hv1.1).1 hv1.2) hw1.2 ((hTΩ _ hw1.1).1 hw1.2) hv1.1,
        decPi_apply_cross S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ hH hH'
          hM hM' hv1.2 ((hTΩ _ hv1.1).1 hv1.2) hw1.2 ((hTΩ _ hw1.1).1 hw1.2) hv1.1 hw1.1]
  -- `A Q (liftOp Ĝ - Π) Q*`
  have cAQTQ : ∀ (u w : UK × Fin N),
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P') * liftRect N Q' *
        (liftOp N (Gsx C' H' a aT x ν α' s') - decPi C' H' a aT x ν α' s' φ') *
          (liftRect N Q')ᵀ) (h' u) (h' w) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
        (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ) *
          (liftRect N Q)ᵀ) (h u) (h w) := by
    intro u w
    refine mul_block_corr h h' g g' h h' hgi hgi' _ _ _ _ (fun u b hne => ?_)
      (fun u b hne => ?_) (fun u v => cAQT u v) (fun v w => ?_) u w
    · exact hsN b ((hAQT _ _ hne).1 (by rw [hh]; exact hec _))
    · exact hsN' b ((hAQT' _ _ hne).1 (by rw [hh']; exact hec' _))
    · obtain ⟨⟨v1, hv1⟩, j1⟩ := v
      obtain ⟨w1, i1⟩ := w
      show (liftRect N Q')ᵀ (g' (⟨v1, hv1⟩, j1)) (h' (w1, i1)) =
        (liftRect N Q)ᵀ (g (⟨v1, hv1⟩, j1)) (h (w1, i1))
      simp only [Matrix.transpose_apply, hh, hh', hg, hg', hf, hf', liftRect]
      split_ifs
      · exact hQQ w1 v1 hv1.2 ((hTΩ _ hv1.1).1 hv1.2) hv1.1
      · rfl
  -- the whole product
  have cAll : ∀ (u w : UK × Fin N),
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P') * liftRect N Q' *
        (liftOp N (Gsx C' H' a aT x ν α' s') - decPi C' H' a aT x ν α' s' φ') *
          (liftRect N Q')ᵀ * covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P')) (h' u) (h' w) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
        (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ) *
          (liftRect N Q)ᵀ * covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) (h u) (h w) := by
    intro u w
    refine mul_block_corr h h' h h' h h' hhi hhi' _ _ _ _ (fun u b hne => ?_)
      (fun u b hne => ?_) (fun u v => cAQTQ u v) (fun v w => cA v w) u w
    · exact hsK b ((hAQTQ _ _ hne).1 (by rw [hh]; exact hec _))
    · exact hsK' b ((hAQTQ' _ _ hne).1 (by rw [hh']; exact hec' _))
  have e1 := cA (v, i) (w, j)
  have e2 := cAll (v, i) (w, j)
  simp only [hh, hh'] at e1 e2
  unfold decCov
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, e1, e2]

/-- **The entries of the decoupled covariance `C_x(s)` of two pairs agree** on a component `T`,
with a common coarse index set `κι`: with `Q`, `Q'`, `P`, `P'` block diagonal for a splitting `cκ`
of `κι` (rows of `Q` with `cκ κ` read exactly the sites of `T`) and agreeing there, the entries of
`C_x(s)` at two coarse indices with `cκ` agree. -/
theorem decCov_apply_cross {κι : Type*} [Fintype κι] [DecidableEq κι]
    (hM : IsUnit (decM C H a aT x ν α s φ)) (hM' : IsUnit (decM C' H' a aT x ν α' s' φ'))
    (cκ : κι → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (Q' : Matrix κι (H'.Ω 1) ℂ)
    (P P' : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q)
    (hQ' : BD cκ (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q')
    (hP : BD cκ cκ P) (hP' : BD cκ cκ P')
    (hQQ : ∀ (κ : κι) (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1),
      cκ κ → y ∈ T → Q' κ ⟨y, hy'⟩ = Q κ ⟨y, hy⟩)
    (hPP : ∀ κ κ' : κι, cκ κ → cκ κ' → P' κ κ' = P κ κ')
    {κ κ' : κι} (hκ : cκ κ) (hκ' : cκ κ') (i j : Fin N) :
    decCov C' H' a aT x ν α' s' φ' Q' P' (κ, i) (κ', j) =
      decCov C H a aT x ν α s φ Q P (κ, i) (κ', j) := by
  classical
  exact decCov_block_cross S S' hF hF' hαA hαB hx hlay hU hU' hdich hdich' hin hin' hα hφ hH hH' hM hM'
    cκ cκ Q Q' P P' (UK := {v : κι // cκ v}) (fun v => v.1) (fun v => v.1)
    (fun u v e₀ => Subtype.ext e₀) (fun u v e₀ => Subtype.ext e₀) (fun κ hκ => ⟨⟨κ, hκ⟩, rfl⟩)
    (fun κ hκ => ⟨⟨κ, hκ⟩, rfl⟩) (fun v => v.2) (fun v => v.2) hQ hQ' hP hP'
    (fun v y hy hy' hyT => hQQ v.1 y hy hy' v.2 hyT) (fun v w => hPP v.1 w.1 v.2 w.2)
    ⟨κ, hκ⟩ ⟨κ', hκ'⟩ i j

end CovCross

section SqrtCross

variable {N : ℕ} {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- **The entries of the square root `C^{1/2}(s)` of two pairs agree** on a component `T` (general
form, two coarse index sets matched by a common block `UK`): if the hypotheses of
`decCov_block_cross` hold for every `x > 0`, the entries of
`C^{1/2}(s) = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx` at the matched coarse indices agree (the integrands
agree pointwise on `(0, ∞)`; no integrability is needed). -/
theorem decCovSqrt_block_cross {κι κι' UK : Type*} [Fintype κι] [DecidableEq κι] [Fintype κι']
    [DecidableEq κι'] [Fintype UK]
    (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    (hF : FootLocalGeom C) (hF' : FootLocalGeom C')
    (hαA : AdmPot H α) (hαB : AdmPot H' α')
    (hlay : ∀ y ∈ T, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hU : ∀ x : ℝ, 0 < x → IsUnit (1 - Kcalx C H a aT x ν α s))
    (hU' : ∀ x : ℝ, 0 < x → IsUnit (1 - Kcalx C' H' a aT x ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
      α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    (hφ : ∀ y ∈ T, φ' y = φ y)
    (hH : ∀ x : ℝ, 0 < x → HRespects C H a aT x ν α s T)
    (hH' : ∀ x : ℝ, 0 < x → HRespects C' H' a aT x ν α' s' T)
    (hM : ∀ x : ℝ, 0 < x → IsUnit (decM C H a aT x ν α s φ))
    (hM' : ∀ x : ℝ, 0 < x → IsUnit (decM C' H' a aT x ν α' s' φ'))
    (cκ : κι → Prop) (cκ' : κι' → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (Q' : Matrix κι' (H'.Ω 1) ℂ)
    (P : Matrix κι κι ℂ) (P' : Matrix κι' κι' ℂ) (e : UK → κι) (e' : UK → κι')
    (hei : Function.Injective e) (hei' : Function.Injective e')
    (hes : ∀ κ, cκ κ → ∃ v, e v = κ) (hes' : ∀ κ, cκ' κ → ∃ v, e' v = κ)
    (hec : ∀ v, cκ (e v)) (hec' : ∀ v, cκ' (e' v))
    (hQ : BD cκ (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q)
    (hQ' : BD cκ' (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q')
    (hP : BD cκ cκ P) (hP' : BD cκ' cκ' P')
    (hQQ : ∀ (v : UK) (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1),
      y ∈ T → Q' (e' v) ⟨y, hy'⟩ = Q (e v) ⟨y, hy⟩)
    (hPP : ∀ v w : UK, P' (e' v) (e' w) = P (e v) (e w)) (v w : UK) (i j : Fin N) :
    decCovSqrt C' H' a aT ν α' s' φ' Q' P' (e' v, i) (e' w, j) =
      decCovSqrt C H a aT ν α s φ Q P (e v, i) (e w, j) := by
  unfold decCovSqrt
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  congr 1
  unfold intMat
  refine MeasureTheory.setIntegral_congr_fun
    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))) (fun y hy => ?_)
  unfold decSqrtInt
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [decCov_block_cross (x := y) S S' hF hF' hαA hαB (le_of_lt hy) hlay (hU y hy) (hU' y hy)
    hdich hdich' hin hin' hα hφ (hH y hy) (hH' y hy) (hM y hy) (hM' y hy) cκ cκ' Q Q' P P' e e'
    hei hei' hes hes' hec hec' hQ hQ' hP hP' hQQ hPP v w i j]

/-- **The entries of the square root `C^{1/2}(s)` of two pairs agree** on a component `T`, with a
common coarse index set `κι` (see `decCovSqrt_block_cross`). -/
theorem decCovSqrt_apply_cross {κι : Type*} [Fintype κι] [DecidableEq κι]
    (S : XCover C H a aT ν Cx) (S' : XCover C' H' a aT ν Cx')
    (hF : FootLocalGeom C) (hF' : FootLocalGeom C')
    (hαA : AdmPot H α) (hαB : AdmPot H' α')
    (hlay : ∀ y ∈ T, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hU : ∀ x : ℝ, 0 < x → IsUnit (1 - Kcalx C H a aT x ν α s))
    (hU' : ∀ x : ℝ, 0 < x → IsUnit (1 - Kcalx C' H' a aT x ν α' s'))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd s' q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd s q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd s' q = C.sProd s q ∧
      (∀ x₀ ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x₀ ∨ ∃ μ : Fin d, y = x₀ + Pi.single μ 1 ∨ y = x₀ - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x₀ ∈ intBox q, C.chi q x₀ = C'.chi q x₀))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd s' q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd s q ≠ 0)
    (hα : ∀ (x₀ : CTorus d L N₁ m₁ (k + 1)) (hx : x₀ ∈ H.Ω 1) (hx' : x₀ ∈ H'.Ω 1), x₀ ∈ T →
      α ⟨x₀, hx⟩ = α' ⟨x₀, hx'⟩)
    (hφ : ∀ y ∈ T, φ' y = φ y)
    (hH : ∀ x : ℝ, 0 < x → HRespects C H a aT x ν α s T)
    (hH' : ∀ x : ℝ, 0 < x → HRespects C' H' a aT x ν α' s' T)
    (hM : ∀ x : ℝ, 0 < x → IsUnit (decM C H a aT x ν α s φ))
    (hM' : ∀ x : ℝ, 0 < x → IsUnit (decM C' H' a aT x ν α' s' φ'))
    (cκ : κι → Prop) (Q : Matrix κι (H.Ω 1) ℂ) (Q' : Matrix κι (H'.Ω 1) ℂ)
    (P P' : Matrix κι κι ℂ)
    (hQ : BD cκ (fun y : H.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q)
    (hQ' : BD cκ (fun y : H'.Ω 1 => (y : CTorus d L N₁ m₁ (k + 1)) ∈ T) Q')
    (hP : BD cκ cκ P) (hP' : BD cκ cκ P')
    (hQQ : ∀ (κ : κι) (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1),
      cκ κ → y ∈ T → Q' κ ⟨y, hy'⟩ = Q κ ⟨y, hy⟩)
    (hPP : ∀ κ κ' : κι, cκ κ → cκ κ' → P' κ κ' = P κ κ')
    {κ κ' : κι} (hκ : cκ κ) (hκ' : cκ κ') (i j : Fin N) :
    decCovSqrt C' H' a aT ν α' s' φ' Q' P' (κ, i) (κ', j) =
      decCovSqrt C H a aT ν α s φ Q P (κ, i) (κ', j) := by
  classical
  exact decCovSqrt_block_cross S S' hF hF' hαA hαB hlay hU hU' hdich hdich' hin hin' hα hφ hH hH'
    hM hM' cκ cκ Q Q' P P' (UK := {v : κι // cκ v}) (fun v => v.1) (fun v => v.1)
    (fun u v e₀ => Subtype.ext e₀) (fun u v e₀ => Subtype.ext e₀) (fun κ hκ => ⟨⟨κ, hκ⟩, rfl⟩)
    (fun κ hκ => ⟨⟨κ, hκ⟩, rfl⟩) (fun v => v.2) (fun v => v.2) hQ hQ' hP hP'
    (fun v y hy hy' hyT => hQQ v.1 y hy hy' v.2 hyT) (fun v w => hPP v.1 w.1 v.2 w.2)
    ⟨κ, hκ⟩ ⟨κ', hκ'⟩ i j

end SqrtCross

end XPair

end Dec2

end Balaban.Localization
