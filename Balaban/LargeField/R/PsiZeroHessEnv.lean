/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessLine
public import Balaban.Background.Def5

/-!
# The effective action along a perturbation line (PSIZERO-HESS §5, row 3)

For a perturbation `v` supported in a box `Z` over the top layer, the data of `ψ + t v` are the data line
`D + t Jv` (`dataR_merge_line`).  Along it the effective action `F(t) = A(D_t, φ_*(D_t))` is sandwiched
(`effAction_sandwich`) between the upper bound `F(0) + t b₁ + A(tJv, 0)` (the field `φ_*(D)` as a competitor) and the
exact value `F(0) + t b₁ + A(tJv, τ_t) + ½ ∑ α |τ_t|²` (`τ_t = φ_*(D_t) - φ_*(D)`, the Lagrangian form of the
second variation).  This replaces the differentiation of the background field in (2.2)–(2.8): the envelope
formula and the Hessian lower bound follow from the sandwich.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Matrix Finset

section Env

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- The data of `ψ + t v` are the data line `D + t Jv`. -/
theorem dataR_merge_line (ψ : BlockField d L N₀ k N) {Z : Finset (Torus d (N₀ * L ^ (k - k)))}
    (v : SuppSpace Z N) (t : ℝ) :
    dataR G (mergeField Z ψ (restrictSupp Z ψ + t • v)) =
      (dataR G ψ).lineAt (topTangent G v) (t : ℂ) := by
  refine BgData.ext' ?_ ?_
  · funext x i
    by_cases hx : x ∈ dataSites G
    · rw [dataR_Ψ G _ hx i]
      simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [dataR_Ψ G _ hx i, topTangent_Ψ v hx i]
      by_cases hz : jBlock d L N₀ k k x ∈ Z
      · simp [liftR, mergeField_of_mem hz, restrictSupp, extSupp, hz]
      · simp [liftR, mergeField_of_not_mem hz, extSupp, hz]
    · simp [BgData.lineAt, (dataR G _).Ψ_zero x hx, (topTangent G v).Ψ_zero x hx]
  · funext x i
    by_cases hx : x ∈ G.Ω 1
    · simp [BgData.lineAt, dataR_h G _ hx i, topTangent_h]
    · simp [BgData.lineAt, (dataR G _).h_zero x hx, (topTangent G v).h_zero x hx]

theorem re_unit_cross {φ τ : G.Ω 1 × Fin N → ℂ} (hφ : IsRealUnitField G φ)
    (hσ : IsRealUnitField G (φ + τ)) (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) (x : G.Ω 1) :
    ∑ i, (τ (x, i)).re * (φ (x, i)).re = -(1 / 2) * ∑ i, ‖τ (x, i)‖ ^ 2 := by
  have sq : ∀ z : ℂ, z.im = 0 → ‖z‖ ^ 2 = z.re ^ 2 := fun z hz => by
    rw [Complex.sq_norm, Complex.normSq_apply, hz]; ring
  have h1 := (hφ x).2
  have h2 := (hσ x).2
  simp only [Pi.add_apply] at h2
  have e1 : ∑ i, ‖φ (x, i)‖ ^ 2 = ∑ i, (φ (x, i)).re ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq _ ((hφ x).1 i)
  have e2 : ∑ i, ‖φ (x, i) + τ (x, i)‖ ^ 2 = ∑ i, ((φ (x, i)).re + (τ (x, i)).re) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      rw [sq _ (by simp [(hφ x).1 i, hτ x i])]; simp
  have e3 : ∑ i, ‖τ (x, i)‖ ^ 2 = ∑ i, (τ (x, i)).re ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq _ (hτ x i)
  have e4 : ∑ i, ((φ (x, i)).re + (τ (x, i)).re) ^ 2 =
      ∑ i, (φ (x, i)).re ^ 2 + 2 * ∑ i, (τ (x, i)).re * (φ (x, i)).re + ∑ i, (τ (x, i)).re ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e3]
  linarith

theorem pair_alpha_re {φ τ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ (x : G.Ω 1) i, (φ (x, i)).im = 0)
    (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) (α : G.Ω 1 → ℂ) :
    (pair G τ (fun p => α p.1 * φ p)).re =
      ∑ x : G.Ω 1, (α x).re * ∑ i, (τ (x, i)).re * (φ (x, i)).re := by
  unfold pair
  rw [Complex.re_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, hφ x i, hτ x i]
  ring

/-- The Euler-Lagrange equation in the form used by the data-line identity. -/
theorem el_residual (H : BgHyp d L k ϱ a 0) {D : BgData G N}
    (hD : InUnionDomainR G (bgC1 d L N) 0 D) (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a 0 0) *ᵥ bgField G a 0 D) p - source G a 0 D p =
      -(bgMult G a 0 D p.1 * bgField G a 0 D p) := by
  obtain ⟨-, -, hs, -⟩ := theorem71 H hD
  have h := congrFun hs.1.1 p
  rw [H_alpha_apply] at h
  linear_combination h

/-- **The sandwich (row 3).**  Along the data line `D + tE` of a tangent datum `E` (real, vanishing off `Ω₁`,
`h̃ = 0`) the effective action is at most `F(0) + t b₁ + A(tE, 0)`, and equals
`F(0) + t b₁ + A(tE, τ) + ½ ∑ Re α_x |τ_x|²`, `τ = φ_*(D + tE) - φ_*(D)`. -/
theorem effAction_sandwich (H : BgHyp d L k ϱ a 0) {D E : BgData G N}
    (hD : InUnionDomainR G (bgC1 d L N) 0 D) (hE : E.IsReal)
    (hEo : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (hEh : ∀ x, E.h x = 0) (t : ℝ)
    (hDt : InUnionDomainR G (bgC1 d L N) 0 (D.lineAt E (t : ℂ))) :
    action G a 0 (D.lineAt E (t : ℂ)) (bgField G a 0 (D.lineAt E (t : ℂ))) ≤
        action G a 0 D (bgField G a 0 D) + t * (firstVar a D E (bgField G a 0 D)).re +
          action G a 0 ((bgZero G N).lineAt E (t : ℂ)) 0 ∧
      action G a 0 (D.lineAt E (t : ℂ)) (bgField G a 0 (D.lineAt E (t : ℂ))) =
        action G a 0 D (bgField G a 0 D) + t * (firstVar a D E (bgField G a 0 D)).re +
          (action G a 0 ((bgZero G N).lineAt E (t : ℂ))
              (bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D) +
            1 / 2 * ∑ x : G.Ω 1, (bgMult G a 0 D x).re *
              ∑ i, ‖(bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D) (x, i)‖ ^ 2) := by
  obtain ⟨-, hU0, -, -⟩ := theorem71 H hD
  obtain ⟨-, hUt, -, hMt, -⟩ := theorem71 H hDt
  have hDR : D.IsReal := by
    obtain ⟨δ, -, -, h⟩ := hD
    exact isReal_of_inDomainR h
  have hφim : ∀ (x : G.Ω 1) i, (bgField G a 0 D (x, i)).im = 0 := fun x i => (hU0 x).1 i
  have hτim : ∀ (x : G.Ω 1) i, ((bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D) (x, i)).im = 0 :=
    fun x i => by simp [(hUt x).1 i, hφim x i]
  have hEL := el_residual H hD
  have hline := fun (τ : G.Ω 1 × Fin N → ℂ) (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) =>
    action_line_pair (a := a) (ν := 0) hDR hE hEo hEh t hφim hτ (bgMult G a 0 D) hEL
  constructor
  · have h0 := hline 0 (fun x i => by simp)
    have hmin := (hMt (bgField G a 0 D) hU0).2
    rw [add_zero] at h0
    have hp : pair G (0 : G.Ω 1 × Fin N → ℂ) (fun p => bgMult G a 0 D p.1 * bgField G a 0 D p) = 0 := by
      simp [pair]
    rw [hp, Complex.zero_re, sub_zero] at h0
    have hw : 0 ≤ ∑ i, weightedSqNorm G fun x => bgField G a 0 D (x, i) -
        bgField G a 0 (D.lineAt E (t : ℂ)) (x, i) :=
      Finset.sum_nonneg fun i _ => weightedSqNorm_nonneg G _
    linarith
  · have h1 := hline _ hτim
    rw [add_sub_cancel] at h1
    rw [h1, pair_alpha_re hφim hτim]
    have hu : IsRealUnitField G (bgField G a 0 D + (bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D)) := by
      rw [add_sub_cancel]; exact hUt
    have hc : ∀ x : G.Ω 1, ∑ i, ((bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D) (x, i)).re *
        (bgField G a 0 D (x, i)).re = -(1 / 2) * ∑ i, ‖(bgField G a 0 (D.lineAt E (t : ℂ)) -
          bgField G a 0 D) (x, i)‖ ^ 2 := fun x => re_unit_cross hU0 hu hτim x
    simp only [hc]
    have : ∑ x : G.Ω 1, (bgMult G a 0 D x).re * (-(1 / 2) * ∑ i, ‖(bgField G a 0 (D.lineAt E (t : ℂ)) -
          bgField G a 0 D) (x, i)‖ ^ 2) = -(1 / 2 * ∑ x : G.Ω 1, (bgMult G a 0 D x).re *
            ∑ i, ‖(bgField G a 0 (D.lineAt E (t : ℂ)) - bgField G a 0 D) (x, i)‖ ^ 2) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [this]
    ring

end Env

end Balaban.LargeField
