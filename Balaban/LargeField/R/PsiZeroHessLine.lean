/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessTop
public import Balaban.Background.MinimizerExpansion
public import Balaban.Background.Minimizer

/-!
# The action along a data line (PSIZERO-HESS §5, row 2)

For a tangent datum `E` vanishing off `Ω₁` (with `h̃ = 0`) the action along the data line `D + tE` and a field
`φ₀ + τ`, where `(φ₀, α)` solves (EL) for `D`, is

`A(D + tE, φ₀ + τ) = A(D, φ₀) + t b₁ + A(tE, τ) - ⟨τ, α φ₀⟩`

(`actionC_line_pair`), with `b₁ = ∑_x w_x ⟨E(x), Ψ(x) - Qφ₀(x)⟩` the first variation (the envelope term).
It is the polarization of the block term; the bond term does not see `E` (`barField_line`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Matrix Finset

section Line

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The zero datum. -/
noncomputable def bgZero (G : GeneratingSet d L N₀ k ϱ) (N : ℕ) : BgData G N where
  Ψ := 0
  h := 0
  Ψ_layerConst := fun _ _ _ _ _ _ _ => rfl
  h_layerConst := fun _ _ _ _ _ _ _ => rfl
  Ψ_zero := fun _ _ => rfl
  h_zero := fun _ _ => rfl

/-- The first variation `b₁ = ∑_x w_x ∑_i E(x,i) (Ψ(x,i) - Qφ₀(x,i))` (complex form). -/
noncomputable def firstVar (a : ℕ → ℝ) (D E : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) : ℂ :=
  ∑ x : G.Ω 1, ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
      ∑ i, E.Ψ x i * (D.Ψ x i - blockAvg G φ x i)

theorem barField_line (D E : BgData G N) (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (t : ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) : barField G (D.lineAt E t).Ψ φ = barField G D.Ψ φ := by
  funext x i
  by_cases hx : x ∈ G.Ω 1
  · simp [barField, hx]
  · simp [barField, hx, BgData.lineAt, hE x hx]

theorem boundaryTerm_line (D E : Torus d (N₀ * L ^ k) → Fin N → ℂ) (t : ℂ) (p : G.Ω 1 × Fin N) :
    boundaryTerm G (D + t • E) p = boundaryTerm G D p + t * boundaryTerm G E p := by
  unfold boundaryTerm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem source_lineAt (D E : BgData G N) (t : ℂ) :
    source G a ν (D.lineAt E t) = source G a ν D + t • source G a ν E := by
  funext p
  have hb := boundaryTerm_line (G := G) D.Ψ E.Ψ t p
  simp only [source, qStar, BgData.lineAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb]
  ring

theorem blockAvg_zero : blockAvg G (0 : G.Ω 1 × Fin N → ℂ) = 0 := by
  have h0 : ∀ y i, svec G (0 : G.Ω 1 × Fin N → ℂ) y i = 0 := fun y i => by
    by_cases hy : y ∈ G.Ω 1
    · rw [svec_of_mem G _ ⟨y, hy⟩ i]; rfl
    · exact svec_of_not_mem G _ hy i
  funext x i
  simp [blockAvg, h0]

theorem barField_zero (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hΨ : ∀ x, x ∉ G.Ω 1 → Ψ x = 0) :
    barField G Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 := by
  funext x i
  by_cases hx : x ∈ G.Ω 1
  · simp [barField, hx]
  · simp [barField, hx, hΨ x hx]

/-- The data line at a fixed field: the bond and mass terms do not move, the block term is quadratic. -/
theorem actionC_line_self (D E : BgData G N) (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0)
    (hEh : ∀ x, E.h x = 0) (t : ℂ) (φ : G.Ω 1 × Fin N → ℂ) :
    actionC G a ν (D.lineAt E t) φ =
      actionC G a ν D φ + t * firstVar a D E φ + actionC G a ν ((bgZero G N).lineAt E t) 0 := by
  have hz : ∀ x, x ∉ G.Ω 1 → ((bgZero G N).lineAt E t).Ψ x = 0 := fun x hx => by
    simp [BgData.lineAt, bgZero, hE x hx]
  have hb0 : barField G ((bgZero G N).lineAt E t).Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 := by
    rw [barField_line (bgZero G N) E hE t]
    exact barField_zero _ (fun x _ => rfl)
  unfold actionC firstVar
  rw [barField_line D E hE t, hb0, blockAvg_zero]
  simp only [BgData.lineAt, bgZero, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hEh,
    mul_zero, add_zero, sub_zero, sub_self, Finset.sum_const_zero]
  simp only [Finset.mul_sum]
  simp only [ite_self, mul_zero, Finset.sum_const_zero, add_zero]
  have hblk : ∀ x : G.Ω 1, ∑ i : Fin N, 1 / 2 * (((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ((D.Ψ x i + t * E.Ψ x i - blockAvg G φ x i) * (D.Ψ x i + t * E.Ψ x i - blockAvg G φ x i))) =
      ∑ i : Fin N, 1 / 2 * (((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ((D.Ψ x i - blockAvg G φ x i) * (D.Ψ x i - blockAvg G φ x i))) +
      ∑ i : Fin N, t * (((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        (E.Ψ x i * (D.Ψ x i - blockAvg G φ x i))) +
      ∑ i : Fin N, 1 / 2 * (((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 : ℝ) : ℂ) *
        ((0 + t * E.Ψ x i) * (0 + t * E.Ψ x i))) := by
    intro x
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hblk, Finset.sum_add_distrib]
  ring

theorem source_zero_line (E : BgData G N) (t : ℂ) :
    source G a ν ((bgZero G N).lineAt E t) = t • source G a ν E := by
  have h0 : source G a ν (bgZero G N) = 0 := by
    funext p
    simp [source, qStar, bgZero, boundaryTerm]
  rw [source_lineAt, h0, zero_add]

/-- **The data-line identity (row 2).**  Let `(φ₀, α)` solve the Euler-Lagrange system for `D`
(`H₀ φ₀ - S = -α φ₀`) and let `E` be a tangent datum vanishing off `Ω₁` with `h̃ = 0`.  Then
`A(D + tE, φ₀ + τ) = A(D, φ₀) + t b₁ + A(tE, τ) - ⟨τ, α φ₀⟩`. -/
theorem actionC_line_pair (D E : BgData G N) (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0)
    (hEh : ∀ x, E.h x = 0) (t : ℂ) (φ τ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (hEL : ∀ p, (liftOp N (dirichletOperator G a ν 0) *ᵥ φ) p - source G a ν D p = -(α p.1 * φ p)) :
    actionC G a ν (D.lineAt E t) (φ + τ) =
      actionC G a ν D φ + t * firstVar a D E φ + actionC G a ν ((bgZero G N).lineAt E t) τ -
        pair G τ (fun p => α p.1 * φ p) := by
  have h1 := actionC_add (a := a) (ν := ν) (D.lineAt E t) φ τ
  have h2 := actionC_add (a := a) (ν := ν) ((bgZero G N).lineAt E t) 0 τ
  have h3 := actionC_line_self (a := a) (ν := ν) D E hE hEh t φ
  rw [zero_add, Matrix.mulVec_zero, source_zero_line] at h2
  have hS : liftOp N (dirichletOperator G a ν 0) *ᵥ φ - source G a ν (D.lineAt E t) =
      (fun p => -(α p.1 * φ p)) - t • source G a ν E := by
    funext p
    rw [source_lineAt]
    have := hEL p
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at this ⊢
    linear_combination this
  rw [hS, pair_sub_right] at h1
  have hp0 : pair G τ (0 : G.Ω 1 × Fin N → ℂ) = 0 := by simp [pair]
  have e1 : pair G τ (fun p => -(α p.1 * φ p)) = -pair G τ (fun p => α p.1 * φ p) := by
    have := pair_smul_right (G := G) τ (fun p => α p.1 * φ p) (-1)
    simp only [neg_one_mul] at this
    exact this
  rw [pair_sub_right, hp0] at h2
  rw [e1] at h1
  linear_combination h1 + h3 - h2

theorem isReal_lineAt {D E : BgData G N} (hD : D.IsReal) (hE : E.IsReal) (t : ℝ) :
    (D.lineAt E (t : ℂ)).IsReal := by
  intro x i
  refine ⟨?_, ?_⟩
  · simp [BgData.lineAt, (hD x i).1, (hE x i).1]
  · simp [BgData.lineAt, (hD x i).2, (hE x i).2]

theorem isReal_bgZero : (bgZero G N).IsReal := fun x i => by simp [bgZero]

/-- **The data-line identity for real data (row 2).** -/
theorem action_line_pair {D E : BgData G N} (hD : D.IsReal) (hE : E.IsReal)
    (hEo : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (hEh : ∀ x, E.h x = 0) (t : ℝ)
    {φ τ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0)
    (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) (α : G.Ω 1 → ℂ)
    (hEL : ∀ p, (liftOp N (dirichletOperator G a ν 0) *ᵥ φ) p - source G a ν D p = -(α p.1 * φ p)) :
    action G a ν (D.lineAt E (t : ℂ)) (φ + τ) =
      action G a ν D φ + t * (firstVar a D E φ).re + action G a ν ((bgZero G N).lineAt E (t : ℂ)) τ -
        (pair G τ (fun p => α p.1 * φ p)).re := by
  have h := actionC_line_pair (a := a) (ν := ν) D E hEo hEh (t : ℂ) φ τ α hEL
  have hφτ : ∀ (x : G.Ω 1) i, ((φ + τ) (x, i)).im = 0 := fun x i => by
    simp [hφ x i, hτ x i]
  rw [← action_cast (D.lineAt E (t : ℂ)) (isReal_lineAt hD hE t) hφτ,
    ← action_cast D hD hφ,
    ← action_cast ((bgZero G N).lineAt E (t : ℂ)) (isReal_lineAt isReal_bgZero hE t) hτ] at h
  have := congrArg Complex.re h
  simpa using this

end Line

end Balaban.LargeField
