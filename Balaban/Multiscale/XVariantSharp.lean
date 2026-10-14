/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BlockPoincareSharp
public import Balaban.Multiscale.CoercivitySharp
public import Balaban.Multiscale.XVariant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# `d`-free coercivity of the x-variant, G-1(a′) (GREEN.md §4.1, re-review N-1)

Brief W2d, item 2 (x-variant). The versions of `Balaban/Multiscale/XVariant.lean` with the sharp
block Poincaré inequality. The Poincaré constant of the x-variant is `1/4` (instead of
`min (1/d) (1/4)`), and the admitted potential range is no longer cut down by `d`:

* `Balaban.Multiscale.top_ineq_sharp`: the blockwise inequality with constant `1/4`;
* `Balaban.Multiscale.xCore_real_sharp`:
  `½ ‖∂φ‖² + ¼ ‖ℓ⁻¹ φ‖² ≤ φᵀ (-Δ + ν + Q* a Q|_x) φ`;
* `Balaban.Multiscale.x_multiscale_coercive_sharp`: for `0 ≤ θ` and `|α₀(y)| ≤ θ ℓ(y)⁻²`,
  `(1/4 - θ) (‖∂ũ‖² + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_{k,x}(α₀) u⟩`, uniformly in `x ≥ 0`;
* `Balaban.Multiscale.xDirichletOperator_isCoercive_sharp`: for `0 ≤ θ < 1/4`, `H_{k,x}(α₀)` is
  `(1/4 - θ) γ`-coercive whenever `γ ≤ ℓ⁻²` on `Ω₁`;
* `Balaban.Multiscale.xDirichletOperator_isCoercive_N1`: the range of N-1: with `θ = a_{k+1}/12 ≤ 1/6`
  (that is `|α₀| ≤ a_{k+1} L⁻² / 12` on `Ω_{k+1}`, where `ℓ⁻² = L^{-2(k+1)}`, and the same relative
  bound `θ ℓ⁻²` on every layer), coercivity constant `γ / 12`;
* `Balaban.Multiscale.xDirichletOperator_isUnit_sharp`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

/-- The `d`-free Poincaré constant `1/4` of the x-variant. -/
noncomputable def xPoincareConstSharp : ℝ := 1 / 4

/-- **The blockwise inequality of G-1(a′), `d`-free** (constant `1/4`). -/
theorem top_ineq_sharp {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] (hL : 3 ≤ L) {s₁ s₂ : ℝ}
    (hs₁ : 0 ≤ s₁) (hs : 0 ≤ s₂ - s₁)
    (hcase : 1 / (4 * (L : ℝ) ^ 2) ≤ s₂ - s₁ ∨ 1 / 18 ≤ s₁)
    (ψ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    xPoincareConstSharp / ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ x, ψ x ^ 2 ≤
      (1 / 2) * innerEnergy (L ^ (k + 1)) ψ +
        (s₁ / ((L : ℝ) ^ k) ^ 2) *
          ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) ψ x) ^ 2 +
        ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) *
          ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hc0 : (0 : ℝ) < xPoincareConstSharp := by unfold xPoincareConstSharp; norm_num
  have hc4 : xPoincareConstSharp ≤ 1 / 4 := le_of_eq rfl
  have hcd : xPoincareConstSharp * 1 ≤ 1 := by unfold xPoincareConstSharp; norm_num
  have hl0 : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  have hl1 : ((L : ℝ) ^ (k + 1)) ^ 2 = ((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2 := by ring
  have hE1 := innerEnergy_nonneg (N := L ^ (k + 1)) ψ
  have hE0n := innerEnergy_nonneg (N := L ^ k) ψ
  have hE0 := innerEnergy_mono_pow (L := L) (k := k) ψ
  have hNk : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hNk1 : 0 < L ^ (k + 1) := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hℓk := side_eq (N₀ := N₀) (L := L) (k := k + 1) (j := k) (by omega)
  have hℓk1 := side_eq (N₀ := N₀) (L := L) (k := k + 1) (j := k + 1) le_rfl
  have hP0 := blockPoincare_sharp hℓk hNk ψ
  have hP1 := blockPoincare_sharp hℓk1 hNk1 ψ
  have hpy0 := sum_sq_eq_sum_sq_sub_add hℓk hNk ψ
  have hpy1 := sum_sq_eq_sum_sq_sub_add hℓk1 hNk1 ψ
  simp only [Nat.cast_pow] at hP0 hP1
  rw [hl1]
  rcases hcase with hcase | hcase
  · rw [hpy1]
    have hq : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
    have hP1' : ∑ x, (ψ x - blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 ≤
        ((1 : ℝ) / 2 : ℝ) * (((L : ℝ) ^ k) ^ 2 * (L : ℝ) ^ 2) * innerEnergy (L ^ (k + 1)) ψ := by
      rw [← hl1]; exact hP1
    have hS1 : 0 ≤ ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := top_real_one (d := 1) hc0 hcd hc4 hl0 hq hP1' hE1 hS1 hcase
    have h0 : 0 ≤ s₁ / ((L : ℝ) ^ k) ^ 2 *
        ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) ψ x) ^ 2 :=
      mul_nonneg (div_nonneg hs₁ hl0.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  · rw [hpy0]
    have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hS0 : 0 ≤ ∑ x, (blockProjection (L ^ k) (N₀ * L ^ (k + 1 - k)) ψ x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have := top_real_two (d := 1) hc0 hcd hc4 hl0 hL2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      hP0 hE0n hE0 hS0 hcase
    have h0 : 0 ≤ (s₂ - s₁) / ((L : ℝ) ^ k) ^ 2 *
        ∑ x, (blockProjection (L ^ (k + 1)) (N₀ * L ^ (k + 1 - (k + 1))) ψ x) ^ 2 :=
      mul_nonneg (div_nonneg hs hl0.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith

section Core

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- Core of `xCore_real_sharp` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xCore_real_sharp_of_ak (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    (1 / 2) * latticeEnergy φ + xPoincareConstSharp * ∑ y, invSqSpacing G y * φ y ^ 2 ≤
      φ ⬝ᵥ xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ φ := by
  obtain ⟨hs₁, hs, hcase⟩ := xSymbols_cases (L := L) hL hak.1 haT1 haT2 hx
  unfold xFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, latticeLaplacian_quadratic, xAvgMatrix_quadratic]
  have hE := sum_innerEnergy_le G φ
  rw [Finset.sum_Icc_succ_top (by omega)] at hE
  have hlay : ∑ y, invSqSpacing G y * φ y ^ 2 =
      ∑ j ∈ Icc 1 (k + 1), (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ y, (layerPart G j φ y) ^ 2 :=
    wsq_eq_sum_layers G φ
  rw [Finset.sum_Icc_succ_top (by omega)] at hlay
  have hper : ∑ j ∈ Icc 1 k, xPoincareConstSharp / ((L : ℝ) ^ j) ^ 2 *
        ∑ y, (layerPart G j φ y) ^ 2 ≤
      ∑ j ∈ Icc 1 k, ((1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (a j / ((L : ℝ) ^ j) ^ 2) *
          ∑ y, (blockProjection (L ^ j) (N₀ * L ^ (k + 1 - j)) (layerPart G j φ) y) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk := (Finset.mem_Icc.1 hj).2
    have h1 := layer_ineq_sharp G (j := j) (by omega) (ha j (Finset.mem_Icc.1 hj).1 hjk).1 φ
    refine le_trans ?_ h1
    have hs0 : 0 ≤ ∑ y, (layerPart G j φ y) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hq : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    refine mul_le_mul_of_nonneg_right ?_ hs0
    refine div_le_div_of_nonneg_right ?_ hq.le
    unfold xPoincareConstSharp; norm_num
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hper
  have htop := top_ineq_sharp (N₀ := N₀) hL hs₁ hs hcase (layerPart G (k + 1) φ)
  have hlay' : xPoincareConstSharp * ∑ y, invSqSpacing G y * φ y ^ 2 =
      ∑ j ∈ Icc 1 k, xPoincareConstSharp / ((L : ℝ) ^ j) ^ 2 * ∑ y, (layerPart G j φ y) ^ 2 +
        xPoincareConstSharp / ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ y, (layerPart G (k + 1) φ y) ^ 2 := by
    rw [hlay, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, div_eq_mul_inv]
    · rw [← mul_assoc, div_eq_mul_inv]
  have hν' : 0 ≤ ν * ∑ y, φ y ^ 2 := mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hlat : latticeEnergy φ = ∑ y, ∑ μ : Fin d, (φ (y + Pi.single μ 1) - φ y) ^ 2 := rfl
  rw [hlat] at hE ⊢
  rw [hlay']
  linarith

/-- **G-1(a′), real core, `d`-free.** For `ν ≥ 0`, `a_j ∈ [1/2, 2]` (`j ≤ k`), `a ∈ [1/2, 2]`,
`x ≥ 0`: `½ ‖∂φ‖² + ¼ ‖ℓ⁻¹ φ‖² ≤ φᵀ (-Δ + ν + Q* a Q|_x) φ`, uniformly in `x`. -/
theorem xCore_real_sharp (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x)
    (φ : Torus d (N₀ * L ^ (k + 1)) → ℝ) :
    (1 / 2) * latticeEnergy φ + xPoincareConstSharp * ∑ y, invSqSpacing G y * φ y ^ 2 ≤
      φ ⬝ᵥ xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν *ᵥ φ :=
  xCore_real_sharp_of_ak G hL hν ha (ha k hk le_rfl) haT1 haT2 hx φ

end Core

section Complex

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable (G : GeneratingSet d L N₀ (k + 1) ϱ)

/-- Core of `x_multiscale_coercive_sharp` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem x_multiscale_coercive_sharp_of_ak (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) (u : G.Ω 1 → ℂ) :
    (1 / 4 - θ) * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (xDirichletOperator G a aT x ν α) u := by
  rw [reQuad_xDirichletOperator, reQuad_map_ofReal]
  have h1 := xCore_real_sharp_of_ak G hL hν ha hak haT1 haT2 hx (fun y => (zeroExt (G.Ω 1) u y).re)
  have h2 := xCore_real_sharp_of_ak G hL hν ha hak haT1 haT2 hx (fun y => (zeroExt (G.Ω 1) u y).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit : ∑ y, invSqSpacing G y * ‖zeroExt (G.Ω 1) u y‖ ^ 2 =
      ∑ y, invSqSpacing G y * (zeroExt (G.Ω 1) u y).re ^ 2 +
        ∑ y, invSqSpacing G y * (zeroExt (G.Ω 1) u y).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
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
  have hq : xPoincareConstSharp = 1 / 4 := rfl
  rw [hq] at h1 h2
  nlinarith

/-- **G-1(a′), the quadratic form, `d`-free** (uniform in `x ≥ 0`): for `θ ≥ 0` and
`|α₀(y)| ≤ θ ℓ(y)⁻²`, `(1/4 - θ) (‖∂ũ‖² + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_{k,x}(α₀) u⟩`. -/
theorem x_multiscale_coercive_sharp (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) (u : G.Ω 1 → ℂ) :
    (1 / 4 - θ) * (dirichletEnergy G u + weightedSqNorm G u) ≤
      Green.reQuad (xDirichletOperator G a aT x ν α) u :=
  x_multiscale_coercive_sharp_of_ak G hL hν ha (ha k hk le_rfl) haT1 haT2 hx hθ0 α hα u

/-- Core of `xDirichletOperator_isCoercive_sharp` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xDirichletOperator_isCoercive_sharp_of_ak (hL : 3 ≤ L) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) ((1 / 4 - θ) * γ) := by
  intro u
  have h := x_multiscale_coercive_sharp_of_ak G hL hν ha hak haT1 haT2 hx hθ0 α hα u
  have hc : 0 < 1 / 4 - θ := by linarith
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u y‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ y) (sq_nonneg _)
  have hDE := dirichletEnergy_nonneg G u
  nlinarith

/-- **G-1(a′), coercivity, `d`-free**, for `0 ≤ θ < 1/4`, `|α₀(y)| ≤ θ ℓ(y)⁻²`, and
`γ ≤ ℓ(y)⁻²` on `Ω₁`: `H_{k,x}(α₀)` is `(1/4 - θ) γ`-coercive, uniformly in `x ≥ 0`. -/
theorem xDirichletOperator_isCoercive_sharp (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 4) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) ((1 / 4 - θ) * γ) :=
  xDirichletOperator_isCoercive_sharp_of_ak G hL hν ha (ha k hk le_rfl) haT1 haT2 hx hθ0 hθ α hα hγ

/-- Core of `xDirichletOperator_isCoercive_N1` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xDirichletOperator_isCoercive_N1_of_ak (hL : 3 ≤ L) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (aT / 12) / (G.spacing y) ^ 2) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) (γ / 12) := by
  have h := xDirichletOperator_isCoercive_sharp_of_ak G hL hν ha hak haT1 haT2 hx
    (θ := 1 / 6) (by norm_num) (by norm_num) α
    (fun y => (hα y).trans (by
      have hp : 0 < (G.spacing y) ^ 2 := by have := spacing_pos G (x := y.1); positivity
      exact div_le_div_of_nonneg_right (by linarith) hp.le)) hγ
  have e : (1 / 4 - 1 / 6 : ℝ) * γ = γ / 12 := by ring
  rwa [e] at h

/-- **The range of N-1** (GREEN.md re-review): with `|α₀(y)| ≤ (a_{k+1}/12) ℓ(y)⁻²`, that is
`|α₀| ≤ a_{k+1} L⁻² / 12` on `Ω_{k+1}` (`a_{k+1} = aT ∈ [1/2, 2]`; `a_{k+1}/12 ≤ 1/6 < 1/4`),
`H_{k,x}(α₀)` is `γ / 12`-coercive for every `γ ≤ ℓ⁻²` on `Ω₁`, uniformly in `x ≥ 0`. -/
theorem xDirichletOperator_isCoercive_N1 (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ}
    {ν : ℝ} (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT)
    (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (aT / 12) / (G.spacing y) ^ 2) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) (γ / 12) :=
  xDirichletOperator_isCoercive_N1_of_ak G hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα hγ

/-- Core of `xDirichletOperator_isUnit_sharp` with `1 ≤ k` replaced by the lower bound `1/2 ≤ a_k` (the only use of `k ≥ 1`); the weights `a_j`, `1 ≤ j ≤ k`, stay in `[1/2, 2]`. -/
theorem xDirichletOperator_isUnit_sharp_of_ak (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a)
    (hak : 1 / 2 ≤ a k ∧ a k ≤ 2) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2) :
    IsUnit (xDirichletOperator G a aT x ν α) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine Green.isUnit_of_isCoercive
    (γ := (1 / 4 - 1 / 8) * (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹)
    (mul_pos (by norm_num) (inv_pos.2 (by positivity)))
    (xDirichletOperator_isCoercive_sharp_of_ak G hL hν ha hak haT1 haT2 hx (θ := 1 / 8)
      (by norm_num) (by norm_num) α hα
      (γ := (((L : ℝ) ^ (k + 1)) ^ 2)⁻¹) fun y => ?_)
  have hp : 0 < G.spacing y := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G y.2) 2)

/-- **G-1(a′), invertibility, `d`-free**, for `|α₀(y)| ≤ ℓ(y)⁻² / 8`. -/
theorem xDirichletOperator_isUnit_sharp (hL : 3 ≤ L) (hk : 1 ≤ k) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2)
    (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2) :
    IsUnit (xDirichletOperator G a aT x ν α) :=
  xDirichletOperator_isUnit_sharp_of_ak G hL hν ha (ha k hk le_rfl) haT1 haT2 hx α hα

end Complex

end Balaban.Multiscale
