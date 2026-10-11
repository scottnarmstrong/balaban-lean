/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.CutOperator
public import Balaban.Multiscale.CoercivitySharp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coercivity of the cut operator: statement NC1 of LOCALIZATION.md §3.1

The proof of the landed `multiscale_coercive` / `multiscale_coercive_sharp`, run with a set `cut`
of removed bonds satisfying `CutAligned` (no removed bond lies inside a block of a layer).  The
cut removes non-negative bond terms of the form, but only bonds that are not inside layer blocks,
so the layer energies are still bounded by the retained energy
(`sum_innerEnergy_le_cut`), and every block Poincaré inequality is used verbatim.

* `Balaban.Multiscale.core_real_cut_sharp`, `core_real_cut`: the real core;
* `Balaban.Multiscale.multiscale_coercive_cut_sharp_gen`, `multiscale_coercive_cut_sharp`
  (**NC1**): `(1/2 - θ)(‖∂ũ‖²_cut + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_cut(α) u⟩`;
* `Balaban.Multiscale.cutOperator_isCoercive_sharp`, `cutOperator_isUnit_sharp`: coercivity and
  invertibility; the same with the `d`-dependent constants of the landed non-sharp version
  (`..._cut`, used by the Agmon estimate).
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Energy

variable (G : GeneratingSet d L N₀ k ϱ) {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}

/-- The layer energies add up to at most the retained energy, when no removed bond lies inside a
layer block. -/
theorem sum_innerEnergy_le_cut (hcut : CutAligned G cut) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    ∑ j ∈ Icc 1 k, innerEnergy (L ^ j) (layerPart G j φ) ≤ cutLatticeEnergy cut φ := by
  unfold innerEnergy cutLatticeEnergy
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun μ _ => ?_
  simp only [update_eq_add_single]
  by_cases hc : (x, μ) ∈ cut
  · simp only [hc, ↓reduceIte]
    refine Finset.sum_nonpos fun j hj => ?_
    by_cases hin : (x μ).val % L ^ j + 1 < L ^ j
    · simp only [hin, ↓reduceIte]
      have h1 := layerPart_sq_diff_le G (mem_Icc.1 hj).1 (mem_Icc.1 hj).2 φ x μ hin
      have h2 : x ∉ G.layer j := fun hx => hcut j hj x μ hc hx hin
      simpa [h2] using h1
    · simp [hin]
  · simp only [hc, ↓reduceIte]
    calc _ ≤ ∑ j ∈ Icc 1 k, (if x ∈ G.layer j then (φ (x + Pi.single μ 1) - φ x) ^ 2 else 0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          by_cases hin : (x μ).val % L ^ j + 1 < L ^ j
          · simp only [hin, ↓reduceIte]
            exact layerPart_sq_diff_le G (mem_Icc.1 hj).1 (mem_Icc.1 hj).2 φ x μ hin
          · simp only [hin, ↓reduceIte]
            split_ifs <;> positivity
      _ ≤ _ := sum_layer_ite_le G x (sq_nonneg _)

end Energy

section Core

variable (G : GeneratingSet d L N₀ k ϱ) {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}

/-- Real core of NC1, `d`-free: `½ E_cut(φ) + ½ ∑ ℓ⁻² φ² ≤ φᵀ (-Δ_cut + ν + Q* a Q) φ`. -/
theorem core_real_cut_sharp (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (1 / 2) * cutLatticeEnergy cut φ + (1 / 2) * ∑ x, invSqSpacing G x * φ x ^ 2 ≤
      φ ⬝ᵥ cutFullMatrix G a ν cut *ᵥ φ := by
  unfold cutFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, cutLaplacian_quadratic, avgMatrix_quadratic]
  have hE := sum_innerEnergy_le_cut G hcut φ
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
  rw [hlay']
  linarith

/-- Real core of NC1 with the `d`-dependent Poincaré constant of the landed non-sharp version:
`½ E_cut(φ) + c ∑ ℓ⁻² φ² ≤ φᵀ (-Δ_cut + ν + Q* a Q) φ`, `c = poincareConst d`. -/
theorem core_real_cut (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (φ : Torus d (N₀ * L ^ k) → ℝ) :
    (1 / 2) * cutLatticeEnergy cut φ + poincareConst d * ∑ x, invSqSpacing G x * φ x ^ 2 ≤
      φ ⬝ᵥ cutFullMatrix G a ν cut *ᵥ φ := by
  unfold cutFullMatrix
  rw [Matrix.add_mulVec, dotProduct_add, cutLaplacian_quadratic, avgMatrix_quadratic]
  have hE := sum_innerEnergy_le_cut G hcut φ
  have hlay : ∑ x, invSqSpacing G x * φ x ^ 2 =
      ∑ j ∈ Icc 1 k, (((L : ℝ) ^ j) ^ 2)⁻¹ * ∑ x, (layerPart G j φ x) ^ 2 := by
    unfold invSqSpacing
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x ∈ G.layer j <;> simp [layerPart, h]
  have hper : ∑ j ∈ Icc 1 k, poincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 ≤
      ∑ j ∈ Icc 1 k, ((1 / 2) * innerEnergy (L ^ j) (layerPart G j φ) +
        (a j / ((L : ℝ) ^ j) ^ 2) *
          ∑ x, (blockProjection (L ^ j) (N₀ * L ^ (k - j)) (layerPart G j φ) x) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact layer_ineq G hd (mem_Icc.1 hj).2 (ha j (mem_Icc.1 hj).1 (mem_Icc.1 hj).2).1 φ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hper
  have hlay' : poincareConst d * ∑ x, invSqSpacing G x * φ x ^ 2 =
      ∑ j ∈ Icc 1 k, poincareConst d / ((L : ℝ) ^ j) ^ 2 * ∑ x, (layerPart G j φ x) ^ 2 := by
    rw [hlay, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, div_eq_mul_inv]
  have hν' : 0 ≤ ν * ∑ x, φ x ^ 2 := mul_nonneg hν (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hlay']
  linarith

end Core

section Complex

variable (G : GeneratingSet d L N₀ k ϱ) {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}

private theorem hsplit_wsq (u : G.Ω 1 → ℂ) :
    ∑ x, invSqSpacing G x * ‖zeroExt (G.Ω 1) u x‖ ^ 2 =
      ∑ x, invSqSpacing G x * (zeroExt (G.Ω 1) u x).re ^ 2 +
        ∑ x, invSqSpacing G x * (zeroExt (G.Ω 1) u x).im ^ 2 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem pot_lower (u α : G.Ω 1 → ℂ) {θ : ℝ} (hα : ∀ x, ‖α x‖ ≤ θ / (G.spacing x) ^ 2) :
    -(θ * weightedSqNorm G u) ≤ ∑ i, (α i).re * ‖u i‖ ^ 2 := by
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

/-- **NC1, the quadratic form, `d`-free.** For `ν ≥ 0`, `a_j ∈ [1/2, 2]`, `θ ≥ 0`,
`|α(x)| ≤ θ ℓ(x)⁻²` and a cut that avoids the layer blocks:
`(1/2 - θ) (‖∂ũ‖²_cut + ‖ℓ⁻¹u‖²) ≤ Re ⟨u, H_cut(α) u⟩`. -/
theorem multiscale_coercive_cut_sharp_gen (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) {θ : ℝ} (hθ0 : 0 ≤ θ) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ θ / (G.spacing x) ^ 2) (u : G.Ω 1 → ℂ) :
    (1 / 2 - θ) * (cutEnergy cut (zeroExt (G.Ω 1) u) + weightedSqNorm G u) ≤
      Green.reQuad (cutOperator G a ν cut α) u := by
  rw [reQuad_cutOperator, reQuad_map_ofReal]
  have h1 := core_real_cut_sharp G hcut hν ha (fun x => (zeroExt (G.Ω 1) u x).re)
  have h2 := core_real_cut_sharp G hcut hν ha (fun x => (zeroExt (G.Ω 1) u x).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit := hsplit_wsq G u
  have hαs := pot_lower G u α hα
  have hE := cutEnergy_eq cut (zeroExt (G.Ω 1) u)
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  have hW := weightedSqNorm_nonneg G u
  nlinarith

/-- **NC1 in the form of LOCALIZATION.md §3.1.** If `|α(x)| ≤ ℓ(x)⁻² / 4`, then
`Re ⟨u, H_cut(α) u⟩ ≥ ½ ‖∂ũ‖²_cut + ¼ ‖ℓ⁻¹u‖²`. -/
theorem nc1_cut (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ (1 / 4) / (G.spacing x) ^ 2) (u : G.Ω 1 → ℂ) :
    (1 / 2) * cutEnergy cut (zeroExt (G.Ω 1) u) + (1 / 4) * weightedSqNorm G u ≤
      Green.reQuad (cutOperator G a ν cut α) u := by
  rw [reQuad_cutOperator, reQuad_map_ofReal]
  have h1 := core_real_cut_sharp G hcut hν ha (fun x => (zeroExt (G.Ω 1) u x).re)
  have h2 := core_real_cut_sharp G hcut hν ha (fun x => (zeroExt (G.Ω 1) u x).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit := hsplit_wsq G u
  have hαs := pot_lower G u α hα
  have hE := cutEnergy_eq cut (zeroExt (G.Ω 1) u)
  linarith

/-- **NC1, the quadratic form, `d`-free, in the form of `multiscale_coercive_sharp`**:
`c₁ = 1/4` and `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`; i.e. `Re ⟨u, H_cut u⟩ ≥ ¼ (‖∂ũ‖²_cut + ‖ℓ⁻¹u‖²)`. -/
theorem multiscale_coercive_cut_sharp (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) (u : G.Ω 1 → ℂ) :
    coerciveConstSharp * (cutEnergy cut (zeroExt (G.Ω 1) u) + weightedSqNorm G u) ≤
      Green.reQuad (cutOperator G a ν cut α) u := by
  have h := multiscale_coercive_cut_sharp_gen G hcut hν ha (θ := 1 / 8) (by norm_num) α
    (fun x => by
      refine (hα x).trans (le_of_eq ?_)
      unfold coerciveConstSharp
      field_simp
      norm_num) u
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  have hW := weightedSqNorm_nonneg G u
  unfold coerciveConstSharp
  nlinarith

/-- **NC1, coercivity, `d`-free.** If `γ ≤ ℓ(x)⁻²` on `Ω₁` and `|α(x)| ≤ c₁ ℓ(x)⁻² / 2`, the cut
operator is `c₁ γ`-coercive, `c₁ = 1/4`. -/
theorem cutOperator_isCoercive_sharp (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) {γ : ℝ}
    (hγ : ∀ x : G.Ω 1, γ ≤ ((G.spacing x) ^ 2)⁻¹) :
    Green.IsCoercive (cutOperator G a ν cut α) (coerciveConstSharp * γ) := by
  intro u
  have h := multiscale_coercive_cut_sharp G hcut hν ha α hα u
  have hc := coerciveConstSharp_pos
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u x‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ x) (sq_nonneg _)
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  nlinarith

/-- **NC1, global constant, `d`-free.** The cut operator is `c₁ L⁻²ᵏ`-coercive. -/
theorem cutOperator_isCoercive_min_sharp (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) :
    Green.IsCoercive (cutOperator G a ν cut α)
      (coerciveConstSharp * (((L : ℝ) ^ k) ^ 2)⁻¹) := by
  refine cutOperator_isCoercive_sharp G hcut hν ha α hα fun x => ?_
  have hp : 0 < G.spacing x := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G x.2) 2)

/-- **NC1, invertibility, `d`-free.** -/
theorem cutOperator_isUnit_sharp (hcut : CutAligned G cut) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConstSharp / (2 * (G.spacing x) ^ 2)) :
    IsUnit (cutOperator G a ν cut α) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  exact Green.isUnit_of_isCoercive
    (mul_pos coerciveConstSharp_pos (inv_pos.2 (by positivity)))
    (cutOperator_isCoercive_min_sharp G hcut hν ha α hα)

/-- The quadratic form with the `d`-dependent constants of the landed `multiscale_coercive`. -/
theorem multiscale_coercive_cut (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (u : G.Ω 1 → ℂ) :
    coerciveConst d * (cutEnergy cut (zeroExt (G.Ω 1) u) + weightedSqNorm G u) ≤
      Green.reQuad (cutOperator G a ν cut α) u := by
  rw [reQuad_cutOperator, reQuad_map_ofReal]
  have h1 := core_real_cut G hcut hd hν ha (fun x => (zeroExt (G.Ω 1) u x).re)
  have h2 := core_real_cut G hcut hd hν ha (fun x => (zeroExt (G.Ω 1) u x).im)
  have hw := sum_invSqSpacing_eq G u
  have hsplit := hsplit_wsq G u
  have hαs := pot_lower G u α (θ := coerciveConst d / 2) (fun x => by
    refine (hα x).trans (le_of_eq ?_)
    field_simp)
  have hE := cutEnergy_eq cut (zeroExt (G.Ω 1) u)
  have hc := coerciveConst_pos hd
  have hpc : poincareConst d = 2 * coerciveConst d := by unfold coerciveConst; ring
  have hle : poincareConst d ≤ 1 / 2 := min_le_right _ _
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  have hW := weightedSqNorm_nonneg G u
  rw [hpc] at h1 h2
  nlinarith

/-- Coercivity of the cut operator with the `d`-dependent constants. -/
theorem cutOperator_isCoercive (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {γ : ℝ}
    (hγ : ∀ x : G.Ω 1, γ ≤ ((G.spacing x) ^ 2)⁻¹) :
    Green.IsCoercive (cutOperator G a ν cut α) (coerciveConst d * γ) := by
  intro u
  have h := multiscale_coercive_cut G hcut hd hν ha α hα u
  have hc := coerciveConst_pos hd
  have hsq : γ * Green.sqNorm u ≤ weightedSqNorm G u := by
    unfold Green.sqNorm weightedSqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [div_eq_mul_inv, mul_comm (‖u x‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hγ x) (sq_nonneg _)
  have hDE := cutEnergy_nonneg cut (zeroExt (G.Ω 1) u)
  nlinarith

/-- Invertibility of the cut operator under the hypotheses of the landed non-sharp version. -/
theorem cutOperator_isUnit (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) :
    IsUnit (cutOperator G a ν cut α) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine Green.isUnit_of_isCoercive
    (mul_pos (coerciveConst_pos hd) (inv_pos.2 (by positivity)))
    (cutOperator_isCoercive G hcut hd hν ha α hα (γ := (((L : ℝ) ^ k) ^ 2)⁻¹) fun x => ?_)
  have hp : 0 < G.spacing x := spacing_pos G
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le (spacing_le G x.2) 2)

end Complex

end Balaban.Multiscale
