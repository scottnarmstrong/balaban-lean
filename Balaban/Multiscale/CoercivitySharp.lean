/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BlockPoincareSharp
public import Balaban.Multiscale.Coercivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# `d`-free multiscale coercivity G-1(a) (GREEN.md §3, §4.1)

Brief W2d, item 2. The versions of `Balaban/Multiscale/Coercivity.lean` that use the sharp block
Poincaré inequality `Balaban.blockPoincare_sharp` (constant `N² / 2`, independent of `d`). The
landed statements are untouched; everything here is new.

* `Balaban.Multiscale.coerciveConstSharp = 1 / 4`: the constant `c₁`, independent of `d`;
* `Balaban.Multiscale.core_real_sharp`: `½ E(φ) + ½ ∑ ℓ⁻² φ² ≤ φᵀ (-Δ + ν + Q* a Q) φ`;
* `Balaban.Multiscale.multiscale_coercive_sharp_gen`: for `θ ≥ 0` and `|α(x)| ≤ θ ℓ(x)⁻²`,
  `(1/2 - θ) (‖∂ũ‖² + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_D(α) u⟩`;
* `Balaban.Multiscale.multiscale_coercive_sharp`: the form of the landed
  `multiscale_coercive`: `c₁ = 1/4`, `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`;
* `Balaban.Multiscale.dirichletOperator_isCoercive_sharp`, `..._min_sharp`, `..._isUnit_sharp`.

No hypothesis `0 < d` is needed.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The `d`-free constant `c₁ = 1 / 4` of the multiscale coercivity. -/
noncomputable def coerciveConstSharp : ℝ := 1 / 4

theorem coerciveConstSharp_pos : 0 < coerciveConstSharp := by
  unfold coerciveConstSharp; norm_num

section Coercivity

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **Sharp block Poincaré on one layer**: with `ψ = 1_{layer j} φ` and `a_j ≥ 1/2`,
`½ L⁻²ʲ ‖ψ‖² ≤ ½ E_j(ψ) + a_j L⁻²ʲ ‖P_j ψ‖²`. -/
theorem layer_ineq_sharp {j : ℕ} (hjk : j ≤ k) {aj : ℝ} (ha : 1 / 2 ≤ aj)
    (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (1 / 2) / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 ≤
      (1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (aj / ((L : ℝ) ^ j) ^ 2) *
          ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) (layerPart G j φ) x) ^ 2 := by
  have hℓ := side_eq (N₀ := N₀) (L := L) hjk
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  set ψ := layerPart G j φ with hψ
  set E := innerEnergy (L ^ j) ψ with hE
  set V := ∑ x, (ψ x - blockProjection (L ^ j) (N₀ * L ^ (k - j)) ψ x) ^ 2 with hV
  set S := ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) ψ x) ^ 2 with hS
  have hP := blockPoincare_sharp hℓ hN ψ
  have hpy := sum_sq_eq_sum_sq_sub_add hℓ hN ψ
  push_cast at hP
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have h1 : (1 / 2) * V ≤ ((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) := by
    have hE0 : 0 ≤ ((L : ℝ) ^ j) ^ 2 * E := mul_nonneg hn.le (innerEnergy_nonneg _)
    nlinarith
  have h2 : (1 / 2) * S ≤ aj * S := mul_le_mul_of_nonneg_right ha hS0
  have key : (1 / 2) * (V + S) ≤ ((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) + aj * S := by
    nlinarith
  rw [hpy]
  have e : 1 / 2 * E + aj / ((L : ℝ) ^ j) ^ 2 * S =
      (((L : ℝ) ^ j) ^ 2 * (1 / 2 * E) + aj * S) / ((L : ℝ) ^ j) ^ 2 := by
    have hn0 : ((L : ℝ) ^ j) ^ 2 ≠ 0 := hn.ne'
    generalize ((L : ℝ) ^ j) ^ 2 = n at hn0 ⊢
    field_simp
  rw [e, div_mul_eq_mul_div]
  gcongr

/-- Real core of G-1(a), `d`-free: `½ E(φ) + ½ ∑ ℓ⁻² φ² ≤ φᵀ (-Δ + ν + Q* a Q) φ`. -/
theorem core_real_sharp {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (1 / 2) * latticeEnergy φ + (1 / 2) * ∑ x, invSqSpacing G x * φ x ^ 2 ≤
      φ ⬝ᵥ fullMatrix G a ν *ᵥ φ := by
  unfold fullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, latticeLaplacian_quadratic, avgMatrix_quadratic]
  have hE := sum_innerEnergy_le G φ
  have hlay : ∑ x, invSqSpacing G x * φ x ^ 2 =
      ∑ j ∈ Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ x, (layerPart G j φ x) ^ 2 := by
    unfold invSqSpacing
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  have hper : ∑ j ∈ Icc 1 k, (1 / 2) / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 ≤
      ∑ j ∈ Icc 1 k, ((1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (a j / ((L : ℝ) ^ j) ^ 2) *
          ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) (layerPart G j φ) x) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact layer_ineq_sharp G (mem_Icc.1 hj).2 (ha j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2).1 φ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hper
  have hlay' : (1 / 2) * ∑ x, invSqSpacing G x * φ x ^ 2 =
      ∑ j ∈ Icc 1 k, (1 / 2) / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 := by
    rw [hlay, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hν' : 0 ≤ ν * ∑ x, φ x ^ 2 := mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hlat : latticeEnergy φ = ∑ x, ∑ μ : Fin d, (φ (x + Pi.single μ 1) - φ x) ^ 2 := rfl
  rw [hlat] at hE ⊢
  rw [hlay']
  linarith

end Coercivity

section Complex

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **G-1(a), the quadratic form, `d`-free.** For `ν ≥ 0`, `a_j ∈ [1/2, 2]`, `θ ≥ 0` and
`|α(x)| ≤ θ ℓ(x)⁻²`: `(1/2 - θ) (‖∂ũ‖² + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_D(α) u⟩`. -/
theorem multiscale_coercive_sharp_gen {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) {θ : ℝ} (hθ0 : 0 ≤ θ) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ θ / (G.spacing x) ^ 2) (u : G.Ω 1 → ℂ) :
    (1 / 2 - θ) * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (dirichletOperator G a ν α) u := by
  rw [reQuad_dirichletOperator, reQuad_map_ofReal]
  have h1 := core_real_sharp G hν ha (fun x => (zeroExt (G.Ω 1) u x).re)
  have h2 := core_real_sharp G hν ha (fun x => (zeroExt (G.Ω 1) u x).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit : ∑ x, invSqSpacing G x * ‖zeroExt (G.Ω 1) u x‖ ^ 2 =
      ∑ x, invSqSpacing G x * (zeroExt (G.Ω 1) u x).re ^ 2 +
        ∑ x, invSqSpacing G x * (zeroExt (G.Ω 1) u x).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hαs : -(θ * weightedSqNorm G u) ≤ ∑ i, (α i).re * ‖u i‖ ^ 2 := by
    unfold weightedSqNorm
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hre : -(θ / (G.spacing i) ^ 2) ≤ (α i).re := by
      have := Complex.abs_re_le_norm (α i)
      have := hα i
      linarith [neg_abs_le (α i).re]
    have : -(θ * (‖u i‖ ^ 2 / (G.spacing i) ^ 2)) = -(θ / (G.spacing i) ^ 2) * ‖u i‖ ^ 2 := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hre (sq_nonneg _)
  have hE := dirichletEnergy_eq G u
  have hDE := dirichletEnergy_nonneg G u
  have hW := weightedSqNorm_nonneg G u
  nlinarith

/-- **G-1(a), the quadratic form, `d`-free, in the form of `multiscale_coercive`**:
`c₁ = 1/4` and `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`. -/
theorem multiscale_coercive_sharp {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) (u : G.Ω 1 → ℂ) :
    coerciveConstSharp * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (dirichletOperator G a ν α) u := by
  have h := multiscale_coercive_sharp_gen G hν ha (θ := 1 / 8) (by norm_num) α
    (fun x => by
      refine (hα x).trans (le_of_eq ?_)
      unfold coerciveConstSharp
      field_simp
      norm_num) u
  have hDE := dirichletEnergy_nonneg G u
  have hW := weightedSqNorm_nonneg G u
  unfold coerciveConstSharp
  nlinarith

/-- **G-1(a), coercivity, `d`-free.** If `γ ≤ ℓ(x)⁻²` on `Ω₁` and `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`, then
`H_D(α)` is `c₁ γ`-coercive, `c₁ = 1/4`. -/
theorem dirichletOperator_isCoercive_sharp {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) {γ : ℝ}
    (hγ : ∀ x : G.Ω 1, γ ≤ ((G.spacing x) ^ 2)⁻¹) :
    Green.IsCoercive (dirichletOperator G a ν α) (coerciveConstSharp * γ) := by
  intro u
  have h := multiscale_coercive_sharp G hν ha α hα u
  have hc := coerciveConstSharp_pos
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u x‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ x) (sq_nonneg _)
  have hDE := dirichletEnergy_nonneg G u
  nlinarith

/-- **G-1(a), global constant, `d`-free.** `H_D(α)` is `c₁ L⁻²ᵏ`-coercive, `c₁ = 1/4`. -/
theorem dirichletOperator_isCoercive_min_sharp {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) :
    Green.IsCoercive (dirichletOperator G a ν α)
      (coerciveConstSharp * (((L : ℝ) ^ k) ^ 2)⁻¹) := by
  refine dirichletOperator_isCoercive_sharp G hν ha α hα fun x => ?_
  have hp : 0 < G.spacing x := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G x.2) 2)

/-- **G-1(a), invertibility, `d`-free.** -/
theorem dirichletOperator_isUnit_sharp {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) :
    IsUnit (dirichletOperator G a ν α) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact Green.isUnit_of_isCoercive
    (mul_pos coerciveConstSharp_pos (inv_pos.2 (by positivity)))
    (dirichletOperator_isCoercive_min_sharp G hν ha α hα)

end Complex

end Balaban.Multiscale
