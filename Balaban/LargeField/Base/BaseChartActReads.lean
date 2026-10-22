/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActLocal
public import Balaban.LargeField.Base.BaseChartAct
public import Balaban.LargeField.Base.BaseChartActAnalytic
public import Balaban.LargeField.Base.BaseBgFunctional
public import Balaban.LargeField.Base.BaseRecord
public import Balaban.Fluctuation.LocalPairDepth

/-!
# The chart activity is a functional of the background that reads a finite neighbourhood of the site

* `baseHamiltonian_ne_zero_dist`: a non-zero entry of the Hessian `H` joins sites at sup-distance
  `≤ L`;
* `chartSite_readsSeed`: if the rows of the whitening family `W(φ, α)` read `(φ, α)` within `ρ` of the
  row, then `(φ, α) ↦ V_x(φ, α, W(φ, α) ψ')` reads the field and the multiplier within `ρ + L` of `x`
  (`ReadsSeed`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Hessian

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **A non-zero entry of the Hessian joins sites at sup-distance `≤ L`.** -/
theorem dirichletOperator_ne_zero_dist (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) {x y : G.Ω 1} (h : dirichletOperator G a ν α x y ≠ 0) :
    supDist (x : Torus d (N₀ * L ^ 1)) y ≤ L := by
  classical
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  by_cases hxy : x = y
  · subst hxy; rw [supDist_self]; exact Nat.zero_le _
  have hxy' : (x : Torus d (N₀ * L ^ 1)) ≠ y := fun h' => hxy (Subtype.ext h')
  have hfull : fullMatrix G a ν x y ≠ 0 := by
    intro h0
    apply h
    simp [dirichletOperator, Green.restrictOp, Matrix.diagonal_apply_ne _ hxy, h0]
  unfold fullMatrix at hfull
  rw [Matrix.add_apply] at hfull
  by_cases h1 : latticeLaplacian d (N₀ * L ^ 1) ν x y = 0
  · rw [h1, zero_add] at hfull
    unfold avgMatrix at hfull
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.Icc_self,
      Finset.sum_singleton] at hfull
    have h2 := right_ne_zero_of_mul hfull
    unfold layerProjMatrix at h2
    by_cases hc : (x : Torus d (N₀ * L ^ 1)) ∈ G.layer 1 ∧ (y : Torus d (N₀ * L ^ 1)) ∈ G.layer 1
    · simp only [hc, and_self, ite_true] at h2
      unfold blockProjMatrix at h2
      by_cases hb : blockMap (L ^ 1) (N₀ * L ^ (1 - 1)) (x : Torus d (N₀ * L ^ 1)) =
          blockMap (L ^ 1) (N₀ * L ^ (1 - 1)) (y : Torus d (N₀ * L ^ 1))
      · have hcell : SameCell (L ^ 1) (x : Torus d (N₀ * L ^ 1)) y :=
          sameCell_of_jBlock_eq le_rfl hb
        have := Balaban.Localization.supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) 1) hcell
        simpa using this
      · simp only [hb, ite_false] at h2; exact absurd rfl h2
    · simp only [hc, ite_false] at h2; exact absurd rfl h2
  · obtain ⟨μ, hμ | hμ⟩ := latticeLaplacian_adj ν hxy' h1
    · have e1 : supDist (x : Torus d (N₀ * L ^ 1)) y ≤ 1 := by
        rw [hμ]; exact Balaban.LargeField.supDist_add_single_le _ μ
      omega
    · have e1 : supDist (x : Torus d (N₀ * L ^ 1)) y ≤ 1 := by
        rw [hμ, supDist_comm]; exact Balaban.LargeField.supDist_add_single_le _ μ
      omega

theorem baseHamiltonian_ne_zero_dist (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) {x y : G.Ω 1} (h : baseHamiltonian G a ν α (fun _ => 1) x y ≠ 0) :
    supDist (x : Torus d (N₀ * L ^ 1)) y ≤ L := by
  rw [baseHamiltonian_one] at h
  exact dirichletOperator_ne_zero_dist G a ν α h

end Hessian

section Reads

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- The sites within sup-distance `r` of `c`. -/
noncomputable def seedBall (c : Balaban.Localization.CTorus d L N₁ m₁ 1) (r : ℕ) :
    Finset (Balaban.Localization.CTorus d L N₁ m₁ 1) :=
  Finset.univ.filter fun z => supDist c z ≤ r

theorem mem_seedBall {c z : Balaban.Localization.CTorus d L N₁ m₁ 1} {r : ℕ} :
    z ∈ seedBall c r ↔ supDist c z ≤ r := by
  classical
  simp [seedBall]

/-- **The chart activity reads a finite neighbourhood of the site.**  If the rows of the whitening
family `W(φ, α)` read the field and the multiplier within sup-distance `ρ` of the row, then the
site exponent `V_x (φ, α, W(φ, α) ψ')` is a function of the decoupled background that reads the sites
within `ρ + L` of `x`. -/
theorem chartSite_readsSeed (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ) (a : ℕ → ℝ) (ν β : ℝ)
    (g ψ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (ρ : ℕ)
    (W : ((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) → Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ)
    (hW : ∀ (u u' : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) (p : G.Ω 1 × Fin N),
      (∀ y' : G.Ω 1, supDist (p.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) y' ≤ ρ →
        (∀ i, u.1 (y', i) = u'.1 (y', i)) ∧ u.2 y' = u'.2 y') → ∀ r, W u p r = W u' p r) :
    ReadsSeed G (seedBall (x : Balaban.Localization.CTorus d L N₁ m₁ 1) (ρ + L))
      (fun u => chartSite β (fun y i => u.1 (y, i))
        (baseHamiltonian G a ν u.2 (fun _ => 1)) g (W u *ᵥ ψ) x) := by
  classical
  intro u u' hφ hα
  set NB : Finset (G.Ω 1) := Finset.univ.filter fun y =>
    supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ L with hNB
  have hmemNB : ∀ y, y ∈ NB ↔ supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ L := by
    intro y; simp [hNB]
  have hseed : ∀ y : G.Ω 1, supDist (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y ≤ ρ + L →
      ((∀ i, u.1 (y, i) = u'.1 (y, i)) ∧ u.2 y = u'.2 y) := fun y hy =>
    ⟨hφ y (mem_seedBall.2 hy), hα y (mem_seedBall.2 hy)⟩
  refine chartSite_congr x NB ((hmemNB x).2 (by rw [supDist_self]; exact Nat.zero_le _)) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact (hmemNB y).2 (baseHamiltonian_ne_zero_dist G a ν u.2 hy)
  · intro y
    rw [baseHamiltonian_apply_diag G a ν u.2 _ x y, baseHamiltonian_apply_diag G a ν u'.2 _ x y]
    by_cases hxy : x = y
    · subst hxy
      rw [(hseed x (by rw [supDist_self]; exact Nat.zero_le _)).2]
    · simp [hxy]
  · intro i; rfl
  · intro y hy
    funext i
    exact (hseed y (by have := (hmemNB y).1 hy; omega)).1 i
  · intro y hy i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hW u u' (y, i) (fun y' hy' => hseed y' ?_) r]
    have h1 := (hmemNB y).1 hy
    have h2 := supDist_triangle (x : Balaban.Localization.CTorus d L N₁ m₁ 1) y y'
    simp only [] at hy'
    omega

end Reads

end Balaban.LargeField.Base
