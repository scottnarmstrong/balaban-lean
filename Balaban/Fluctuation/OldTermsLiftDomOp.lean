/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftDomAction

/-!
# The Euler-Lagrange system on a transported generating set

The Dirichlet operator `-Δ^D_{Ω₁} + Q* a Q + ν + α` of the background problem on `liftOldGS G` has
the same entries as on `G` under the relabeling `oldTorusEquiv` (the extra top layer is empty).
Hence the Euler-Lagrange system and its small solutions correspond.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Matrix Balaban Balaban.Localization Balaban.Multiscale Balaban.Background

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem latticeLaplacian_castT {n n' : ℕ} [NeZero n] [NeZero n'] (h : n = n') (ν : ℝ)
    (x y : Torus d n) :
    latticeLaplacian d n' ν (castT h x) (castT h y) = latticeLaplacian d n ν x y := by
  subst h; rfl

section
variable (G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ)

theorem liftOldGS_layerProjMatrix {j : ℕ} (hj : j ≤ k) (x y : CTorus d L (L * N₁) m₁ k) :
    layerProjMatrix (liftOldGS G) j (oldTorusEquiv x) (oldTorusEquiv y) =
      layerProjMatrix G j x y := by
  unfold layerProjMatrix
  simp only [liftOldGS_mem_layer G hj]
  refine if_congr Iff.rfl ?_ rfl
  unfold blockProjMatrix
  exact if_congr (oldTorusEquiv_jBlock_iff hj x y) rfl rfl

theorem liftOldGS_layerProjMatrix_top (x y : CTorus d L N₁ m₁ (k + 1)) :
    layerProjMatrix (liftOldGS G) (k + 1) x y = 0 := by
  unfold layerProjMatrix
  have : x ∉ (liftOldGS G).layer (k + 1) := by
    simp [GeneratingSet.layer, liftOldGS_Ω_top]
  simp [this]

theorem liftOldGS_avgMatrix (a : ℕ → ℝ) (x y : CTorus d L (L * N₁) m₁ k) :
    avgMatrix (liftOldGS G) a (oldTorusEquiv x) (oldTorusEquiv y) = avgMatrix G a x y := by
  unfold avgMatrix
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, liftOldGS_layerProjMatrix_top,
    smul_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [liftOldGS_layerProjMatrix G (Finset.mem_Icc.1 hj).2]

theorem liftOldGS_fullMatrix (a : ℕ → ℝ) (ν : ℝ) (x y : CTorus d L (L * N₁) m₁ k) :
    fullMatrix (liftOldGS G) a ν (oldTorusEquiv x) (oldTorusEquiv y) = fullMatrix G a ν x y := by
  unfold fullMatrix
  simp only [Matrix.add_apply, liftOldGS_avgMatrix]
  rw [oldTorusEquiv_apply x, oldTorusEquiv_apply y, latticeLaplacian_castT]

end

section
variable {G : GeneratingSet d L ((L * N₁) * L ^ m₁) k ϱ}
  (e : G.Ω 1 ≃ (liftOldGS G).Ω 1)
  (he : ∀ x, (e x : CTorus d L N₁ m₁ (k + 1)) = oldTorusEquiv x)

include he

theorem liftOldGS_dirichletOperator (a : ℕ → ℝ) (ν : ℝ) {α : G.Ω 1 → ℂ}
    {α' : (liftOldGS G).Ω 1 → ℂ} (hα : ∀ x, α' (e x) = α x) (x y : G.Ω 1) :
    dirichletOperator (liftOldGS G) a ν α' (e x) (e y) = dirichletOperator G a ν α x y := by
  unfold dirichletOperator
  simp only [Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply, Matrix.diagonal_apply,
    he, Matrix.map_apply, liftOldGS_fullMatrix, e.apply_eq_iff_eq, hα]

theorem liftOldGS_liftOp_mulVec (a : ℕ → ℝ) (ν : ℝ) {α : G.Ω 1 → ℂ}
    {α' : (liftOldGS G).Ω 1 → ℂ} (hα : ∀ x, α' (e x) = α x)
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) (x : G.Ω 1) (i : Fin N) :
    (liftOp N (dirichletOperator (liftOldGS G) a ν α') *ᵥ φ') (e x, i) =
      (liftOp N (dirichletOperator G a ν α) *ᵥ φ) (x, i) := by
  rw [liftOp_mulVec, liftOp_mulVec]
  simp only [Matrix.mulVec, dotProduct]
  refine (Fintype.sum_equiv e _ _ fun y => ?_).symm
  rw [liftOldGS_dirichletOperator e he a ν hα, hφ]

theorem liftOldGS_isEL_iff (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) {α : G.Ω 1 → ℂ} {α' : (liftOldGS G).Ω 1 → ℂ}
    (hα : ∀ x, α' (e x) = α x) :
    IsEL (liftOldGS G) a ν D' φ' α' ↔ IsEL G a ν D φ α := by
  unfold IsEL
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h x => ?_, fun h x' => ?_⟩
  · funext p
    obtain ⟨x, i⟩ := p
    rw [← liftOldGS_liftOp_mulVec e he a ν hα hφ, h, liftOldGS_source e he a ν D D' hΨ hh]
  · funext p'
    obtain ⟨x', i⟩ := p'
    obtain ⟨x, rfl⟩ := e.surjective x'
    rw [liftOldGS_liftOp_mulVec e he a ν hα hφ, h, liftOldGS_source e he a ν D D' hΨ hh]
  · simpa only [hφ] using h (e x)
  · obtain ⟨x, rfl⟩ := e.surjective x'
    simpa only [hφ] using h x

theorem liftOldGS_isSmallSolution_iff (a : ℕ → ℝ) (ν c₀ : ℝ) (D : BgData G N)
    (D' : BgData (liftOldGS G) N)
    (hΨ : ∀ x, D'.Ψ (oldTorusEquiv x) = D.Ψ x) (hh : ∀ x, D'.h (oldTorusEquiv x) = D.h x)
    {φ : G.Ω 1 × Fin N → ℂ} {φ' : (liftOldGS G).Ω 1 × Fin N → ℂ}
    (hφ : ∀ x i, φ' (e x, i) = φ (x, i)) {α : G.Ω 1 → ℂ} {α' : (liftOldGS G).Ω 1 → ℂ}
    (hα : ∀ x, α' (e x) = α x) :
    IsSmallSolution (liftOldGS G) a ν c₀ D' φ' α' ↔ IsSmallSolution G a ν c₀ D φ α := by
  unfold IsSmallSolution
  refine and_congr (liftOldGS_isEL_iff e he a ν D D' hΨ hh hφ hα) ⟨fun h x => ?_, fun h x' => ?_⟩
  · simpa only [he, liftOldGS_spacing, hα] using h (e x)
  · obtain ⟨x, rfl⟩ := e.surjective x'
    simpa only [he, liftOldGS_spacing, hα] using h x

end

end Balaban.Fluctuation
