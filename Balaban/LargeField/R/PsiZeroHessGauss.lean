/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessPair
public import Balaban.LargeField.R.PsiZeroHessGrad
public import Balaban.LargeField.R.ZeroDomainCoercive
public import Balaban.Fluctuation.CubeActionReal
public import Balaban.Multiscale.ConstraintKernel

/-!
# The Gaussian lower bound for the action of a top-layer datum (PSIZERO-HESS §5, rows 5-6)

`action_ge_actionG`: for a datum `D` vanishing off `Ω₁` with `h̃ = 0`, the real action `A(D, τ)` dominates the
multiscale action `A_G(Ω₁; ψ, φ̂)` of LF-1 (the bonds from `Ω₁` to its complement count `½` instead of `¼`).
Together with `lf1_gradient`, `top_pairSum_dirichlet` and `dirichlet_box_coercive` this gives
`A(tJv, τ) ≥ ½ γ_LF c_D L^{k(d-2)} t² ‖v‖²` (`action_top_ge`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Gauss

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The bond-difference sum of the complex image is the real bond term. -/
theorem bond_sum_cast (D : BgData G N) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ)) (x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    ∑ i, (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i) *
      (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i) =
      ((bondTerm φ μ x : ℝ) : ℂ) := by
  unfold bondTerm
  have e1 : ∀ i, barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i -
      barField G D.Ψ (toFieldC G φ) x i =
      (((φ (x + Pi.single μ 1) - φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
    intro i
    rw [barField_toFieldC D φ hout, barField_toFieldC D φ hout, ← Complex.ofReal_sub]
    rfl
  simp only [e1]
  exact sum_sq_complex _

open Classical in
/-- **The action dominates the multiscale action `A_G(Ω₁; ψ, φ)`** (mass `0`, `h = 0`). -/
theorem action_ge_actionG (hd : 2 ≤ d) (D : BgData G N) (hD : D.IsReal)
    (hDh : ∀ x i, D.h x i = 0) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ))
    (hΨ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ i,
      D.Ψ x i = ((ψ n (blkMap d L N₀ k n x) i : ℝ) : ℂ)) :
    actionG G a 0 0 (G.Ω 1) ψ φ ≤ action G a 0 D (toFieldC G φ) := by
  have hstar := cubeActionStar_eq_actionG (a := a) (G := G) hd (G.Ω 1) subset_rfl
    (fun n hn1 hnk x hx hxl y hy => blk_subset_Ω G hn1 hnk hxl hy) 0 D φ ψ 0 hout hΨ
    (fun x _ i => by rw [hDh]; simp)
  have hφim : ∀ (x : G.Ω 1) i, (toFieldC G φ (x, i)).im = 0 := fun x i => by simp [toFieldC]
  have hcast := action_cast (a := a) (ν := 0) D hD hφim
  set R : ℝ := 1 / 2 * ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        (1 - ((if x ∈ G.Ω 1 then 1 else 0) + (if x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0)) / 2) *
          bondTerm φ μ x else 0) with hR
  have hR0 : 0 ≤ R := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => ?_)
    by_cases hc : x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1
    · simp only [hc, ↓reduceIte]
      refine mul_nonneg ?_ (bondTerm_nonneg φ μ x)
      split_ifs <;> norm_num
    · simp only [hc, ↓reduceIte]; exact le_rfl
  have hbond : ∀ x μ, (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
      ∑ i, (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i) *
        (barField G D.Ψ (toFieldC G φ) (x + Pi.single μ 1) i - barField G D.Ψ (toFieldC G φ) x i)
      else 0) = ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then bondTerm φ μ x else 0 : ℝ) : ℂ) := by
    intro x μ
    split_ifs
    · exact bond_sum_cast D φ hout x μ
    · simp
  have key : ((action G a 0 D (toFieldC G φ) : ℝ) : ℂ) =
      ((actionG G a 0 0 (G.Ω 1) ψ φ + 1 / 4 * starBondE (G.Ω 1) φ + R : ℝ) : ℂ) := by
    rw [hcast]
    have hsplit : ∀ (x : Torus d (N₀ * L ^ k)) (μ : Fin d),
        (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then ((bondTerm φ μ x : ℝ) : ℂ) else 0) =
          (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
            starWeight (G.Ω 1) x μ * ((bondTerm φ μ x : ℝ) : ℂ) else 0) +
          ((if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
            (1 - ((if x ∈ G.Ω 1 then 1 else 0) + (if x + Pi.single μ 1 ∈ G.Ω 1 then 1 else 0)) / 2) *
              bondTerm φ μ x else 0 : ℝ) : ℂ) := by
      intro x μ
      by_cases h1 : x ∈ G.Ω 1 <;> by_cases h2 : x + Pi.single μ 1 ∈ G.Ω 1 <;>
        simp [h1, h2, starWeight] <;> ring
    have h2 : actionC G a 0 D (toFieldC G φ) =
        cubeActionStar G a 0 (G.Ω 1) D.Ψ D.h (toFieldC G φ) + ((R : ℝ) : ℂ) := by
      unfold actionC cubeActionStar cubeBlockTerm cubeBondStar cubeMassTerm
      simp only [bond_sum_cast D φ hout, Complex.ofReal_zero, zero_div, zero_mul, add_zero,
        Finset.coe_mem, ↓reduceIte]
      rw [hR]
      push_cast
      simp only [hsplit, Finset.sum_add_distrib, mul_add]
      ring
    rw [h2, hstar]
    push_cast
    ring
  have key' := Complex.ofReal_injective key
  have := starBondE_nonneg (G.Ω 1) φ
  linarith

end Gauss

end Balaban.LargeField
