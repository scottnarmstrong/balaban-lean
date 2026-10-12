/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessGauss
public import Balaban.Multiscale.CoercivitySharp
public import Balaban.Background.ExistenceBounds

/-!
# Absorption of the multiplier term (PSIZERO-HESS §5, row 6)

The quadratic form of the Lagrangian expansion, `A(tJv, τ) + ½ ∑ Re α |τ|²`, is at least `½ A(tJv, τ)` once the
multiplier satisfies `ℓ² |α| ≤ θ` with `θ (1 + 1/g) ≤ 1/8`, `g = ½ γ_LF c_D` (`quad_ge_half`).  The ingredients are
the coercivity `W(τ) ≤ 4 A(0, τ)` of the zero datum (`core_real_sharp`), the block triangle inequality
`A(0, τ) ≤ 2 A(tJv, τ) + t² ∑ w |Jv|²` and the Gaussian lower bound `action_top_ge`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset Matrix

section Coerc

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

theorem source_bgZero : source G a 0 (bgZero G N) = 0 := by
  funext p
  simp [source, qStar, bgZero, boundaryTerm]

theorem actionC_bgZero_zero : actionC G a 0 (bgZero G N) 0 = 0 := by
  have hb : barField G (bgZero G N).Ψ (0 : G.Ω 1 × Fin N → ℂ) = 0 :=
    barField_zero _ (fun x _ => rfl)
  unfold actionC
  rw [hb, blockAvg_zero]
  simp [bgZero]

/-- The action of the zero datum is the quadratic form of `H_D(0)`: `A(0, τ) = ½ ∑_i Re ⟨τ_i, H₀ τ_i⟩`. -/
theorem action_bgZero_eq {τ : G.Ω 1 × Fin N → ℂ} (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) :
    action G a 0 (bgZero G N) τ =
      1 / 2 * ∑ i, Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i)) := by
  have h := actionC_add (a := a) (ν := 0) (bgZero G N) 0 τ
  rw [zero_add, actionC_bgZero_zero, Matrix.mulVec_zero, source_bgZero, sub_zero, sub_zero] at h
  have hp : pair G τ (0 : G.Ω 1 × Fin N → ℂ) = 0 := by simp [pair]
  rw [hp, add_zero] at h
  have hc := action_cast (a := a) (ν := 0) (bgZero G N) isReal_bgZero hτ
  rw [← hc] at h
  have h2 := congrArg Complex.re h
  rw [Complex.ofReal_re] at h2
  rw [h2]
  have h3 : ((1 / 2 : ℂ) * pair G τ (liftOp N (dirichletOperator G a 0 0) *ᵥ τ)).re =
      1 / 2 * (pair G τ (liftOp N (dirichletOperator G a 0 0) *ᵥ τ)).re := by simp
  rw [h3, pair_re _ hτ]

/-- The weighted square norm `∑_i ‖ℓ⁻¹ τ_i‖²` of a vector field. -/
noncomputable def wsq (G : GeneratingSet d L N₀ k ϱ) (τ : G.Ω 1 × Fin N → ℂ) : ℝ :=
  ∑ i, weightedSqNorm G (fun x => τ (x, i))

theorem wsq_nonneg (τ : G.Ω 1 × Fin N → ℂ) : 0 ≤ wsq G τ :=
  Finset.sum_nonneg fun _ _ => weightedSqNorm_nonneg G _

/-- **Coercivity of the zero datum**: `‖ℓ⁻¹ τ‖² ≤ 4 A(0, τ)`. -/
theorem wsq_le_four_action {τ : G.Ω 1 × Fin N → ℂ} (ha : IsAdmissibleWeights k a)
    (hτ : ∀ (x : G.Ω 1) i, (τ (x, i)).im = 0) : wsq G τ ≤ 4 * action G a 0 (bgZero G N) τ := by
  rw [action_bgZero_eq hτ]
  unfold wsq
  have : ∀ i : Fin N, weightedSqNorm G (fun x => τ (x, i)) ≤
      2 * Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i)) := by
    intro i
    have h := multiscale_coercive_sharp_gen G (a := a) (ν := 0) le_rfl ha (θ := 0) le_rfl 0
      (fun x => by simp) (fun x => τ (x, i))
    have hDE := dirichletEnergy_nonneg G (fun x => τ (x, i))
    linarith
  calc ∑ i, weightedSqNorm G (fun x => τ (x, i))
      ≤ ∑ i, 2 * Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i)) :=
        Finset.sum_le_sum fun i _ => this i
    _ = 4 * (1 / 2 * ∑ i, Green.reQuad (dirichletOperator G a 0 0) (fun x => τ (x, i))) := by
        rw [← Finset.mul_sum]; ring

/-- A small multiplier costs at most `θ ‖ℓ⁻¹ τ‖²`. -/
theorem alpha_term_ge {α : G.Ω 1 → ℂ} {θ : ℝ} (hα : Small G α θ) (τ : G.Ω 1 × Fin N → ℂ) :
    -(θ * wsq G τ) ≤ ∑ x : G.Ω 1, (α x).re * ∑ i, ‖τ (x, i)‖ ^ 2 := by
  have e : -(θ * wsq G τ) = ∑ x : G.Ω 1, (-(θ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) *
      ∑ i, ‖τ (x, i)‖ ^ 2) := by
    unfold wsq weightedSqNorm
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine Finset.sum_le_sum fun x _ => ?_
  have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) := spacing_pos G
  have hre : -(θ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) ≤ (α x).re := by
    have h1 := Complex.abs_re_le_norm (α x)
    have h2 := hα x
    have : ‖α x‖ ≤ θ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith [neg_abs_le (α x).re]
  exact mul_le_mul_of_nonneg_right hre (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- `∑_{x ∈ Ω₁} w_x ‖E(x)‖²`, the block energy of a tangent datum. -/
noncomputable def normSqE (a : ℕ → ℝ) (E : BgData G N) : ℝ :=
  ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2

/-- **The block triangle inequality**: `A(0, τ) ≤ 2 A(tE, τ) + t² ∑ w |E|²`. -/
theorem action_triangle (ha : IsAdmissibleWeights k a) (E : BgData G N)
    (hE : ∀ x, x ∉ G.Ω 1 → E.Ψ x = 0) (hEh : ∀ x, E.h x = 0) (t : ℝ) (τ : G.Ω 1 × Fin N → ℂ) :
    action G a 0 (bgZero G N) τ ≤
      2 * action G a 0 ((bgZero G N).lineAt E (t : ℂ)) τ + t ^ 2 * normSqE a E := by
  have hb := barField_line (bgZero G N) E hE (t : ℂ) τ
  have hw : ∀ x : G.Ω 1, 0 ≤ a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
      ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2 := by
    intro x
    obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec x.2
    have := (ha _ hn1 hnk).1
    positivity
  unfold action normSqE
  rw [hb]
  simp only [BgData.lineAt, bgZero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add,
    hEh, mul_zero, sub_zero, zero_sub, norm_neg, zero_div, zero_mul, add_zero]
  have hB : 0 ≤ ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d,
      (if x ∈ G.Ω 1 ∨ x + Pi.single μ 1 ∈ G.Ω 1 then
        ∑ i, ‖barField G (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) τ (x + Pi.single μ 1) i -
          barField G 0 τ x i‖ ^ 2 else 0) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ => by
      split_ifs <;> positivity
  have hblk : ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖blockAvg G τ x i‖ ^ 2 ≤
      2 * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(t : ℂ) * E.Ψ x i - blockAvg G τ x i‖ ^ 2 +
        2 * (t ^ 2 * ∑ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2) := by
    have hi : ∀ (q e : ℂ), ‖q‖ ^ 2 ≤ 2 * ‖(t : ℂ) * e - q‖ ^ 2 + 2 * (t ^ 2 * ‖e‖ ^ 2) := by
      intro q e
      have h1 : ‖q‖ ≤ ‖(t : ℂ) * e - q‖ + ‖(t : ℂ) * e‖ := by
        calc ‖q‖ = ‖(t : ℂ) * e - ((t : ℂ) * e - q)‖ := by ring_nf
          _ ≤ ‖(t : ℂ) * e‖ + ‖(t : ℂ) * e - q‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      have h2 : ‖(t : ℂ) * e‖ ^ 2 = t ^ 2 * ‖e‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith [norm_nonneg q, norm_nonneg ((t : ℂ) * e - q), norm_nonneg ((t : ℂ) * e),
        sq_nonneg (‖(t : ℂ) * e - q‖ - ‖(t : ℂ) * e‖)]
    have hpt : ∀ x : G.Ω 1, (a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖blockAvg G τ x i‖ ^ 2 ≤
        2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(t : ℂ) * E.Ψ x i - blockAvg G τ x i‖ ^ 2) +
        2 * (t ^ 2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2)) := by
      intro x
      have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
        hi (blockAvg G τ x i) (E.Ψ x i)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at this
      have hwx := hw x
      nlinarith [mul_le_mul_of_nonneg_left this hwx]
    calc _ ≤ ∑ x : G.Ω 1, (2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) *
          ∑ i, ‖(t : ℂ) * E.Ψ x i - blockAvg G τ x i‖ ^ 2) +
        2 * (t ^ 2 * ((a (G.layerIndex (x : Torus d (N₀ * L ^ k))) /
        ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ k))) ^ 2) * ∑ i, ‖E.Ψ x i‖ ^ 2))) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  linarith

end Coerc

end Balaban.LargeField
