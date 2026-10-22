/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Basic
public import Balaban.LargeField.Base.BaseCarrierData

/-!
# The source pairing on the large-field sites

The source term of the boundary factor `b₀` (LFR Definition II.7.6, last item; OBS §4.2 item 1) is
the pairing `⟨g|_{Z'}, φ⟩ = ∑_{x ∈ Z'} ∑_i g_{x,i} φ_{x,i}` of the complex source with the unit spins.
Because `|φ_{x,i}| ≤ ‖φ_x‖ ≤ 1`, the modulus of the pairing, and so the real part of the exponent,
is at most the `ℓ¹` norm `‖g|_{Z'}‖_1` of the source on the sites (the proof of Lemma II.7.7 (b)).
The pairing is linear in `g` (hence entire), real for real sources and real spins, and reads the
source only on the sites.
-/

@[expose] public section

namespace Balaban.LargeField

open Classical

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The pairing `∑_{x ∈ Y} ∑_i g_{x,i} φ_{x,i}` of a complex source with real spins. -/
noncomputable def sourcePair (Y : Set ι) (g : ι × Fin N → ℂ)
    (φ : ι → EuclideanSpace ℝ (Fin N)) : ℂ :=
  ∑ i : ι × Fin N, if i.1 ∈ Y then g i * ((φ i.1 i.2 : ℝ) : ℂ) else 0

/-- The `ℓ¹` norm of the source on the sites `Y` (the form of `baseSourceNorm`). -/
noncomputable def sourceNorm (Y : Set ι) (g : ι × Fin N → ℂ) : ℝ :=
  ∑ i : ι × Fin N, if i.1 ∈ Y then ‖g i‖ else 0

/-- **The pairing is bounded by the `ℓ¹` norm of the source** for spins of norm at most one. -/
theorem norm_sourcePair_le (Y : Set ι) (g : ι × Fin N → ℂ) (φ : ι → EuclideanSpace ℝ (Fin N))
    (hφ : ∀ x, ‖φ x‖ ≤ 1) : ‖sourcePair Y g φ‖ ≤ sourceNorm Y g := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases hi : i.1 ∈ Y
  · simp only [hi, ↓reduceIte, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |φ i.1 i.2| ≤ 1 := (PiLp.norm_apply_le (φ i.1) i.2).trans (hφ i.1)
      |>.trans_eq' (by simp)
    calc ‖g i‖ * |φ i.1 i.2| ≤ ‖g i‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖g i‖ := mul_one _
  · simp [hi]

/-- The real part of the pairing is at most the `ℓ¹` norm of the source. -/
theorem re_sourcePair_le (Y : Set ι) (g : ι × Fin N → ℂ) (φ : ι → EuclideanSpace ℝ (Fin N))
    (hφ : ∀ x, ‖φ x‖ ≤ 1) : (sourcePair Y g φ).re ≤ sourceNorm Y g :=
  (Complex.re_le_norm _).trans (norm_sourcePair_le Y g φ hφ)

/-- The pairing is linear in the source, hence analytic. -/
theorem analyticOnNhd_sourcePair (Y : Set ι) (φ : ι → EuclideanSpace ℝ (Fin N)) (s : Set (ι × Fin N → ℂ)) :
    AnalyticOnNhd ℂ (fun g => sourcePair Y g φ) s := by
  intro g _
  unfold sourcePair
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  by_cases hi : i.1 ∈ Y
  · simp only [hi, ↓reduceIte]
    exact (((ContinuousLinearMap.proj i : (ι × Fin N → ℂ) →L[ℂ] ℂ).analyticAt g).mul
      analyticAt_const)
  · simp only [hi, ↓reduceIte]
    exact analyticAt_const

/-- The pairing of a real source with real spins is real. -/
theorem im_sourcePair_eq_zero (Y : Set ι) (g : ι × Fin N → ℂ) (φ : ι → EuclideanSpace ℝ (Fin N))
    (hg : ∀ i, (g i).im = 0) : (sourcePair Y g φ).im = 0 := by
  unfold sourcePair
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.1 ∈ Y <;> simp [hi, hg i]

/-- The pairing reads the source only on the sites of `Y`. -/
theorem sourcePair_congr (Y : Set ι) (g g' : ι × Fin N → ℂ) (φ : ι → EuclideanSpace ℝ (Fin N))
    (h : ∀ i : ι × Fin N, i.1 ∈ Y → g i = g' i) : sourcePair Y g φ = sourcePair Y g' φ := by
  unfold sourcePair
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.1 ∈ Y
  · simp [hi, h i hi]
  · simp [hi]

/-- The pairing vanishes at the zero source. -/
theorem sourcePair_zero (Y : Set ι) (φ : ι → EuclideanSpace ℝ (Fin N)) :
    sourcePair Y 0 φ = 0 := by
  unfold sourcePair
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.1 ∈ Y <;> simp [hi]

/-- **The relative modulus bound of the source factor**: `|e^{⟨g,φ⟩}| ≤ e^{‖g|_Y‖_1}`. -/
theorem norm_cexp_sourcePair_le (Y : Set ι) (g : ι × Fin N → ℂ)
    (φ : ι → EuclideanSpace ℝ (Fin N)) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖Complex.exp (sourcePair Y g φ)‖ ≤ Real.exp (sourceNorm Y g) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.2 (re_sourcePair_le Y g φ hφ)

section Carrier

open Balaban.Multiscale RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {k0 K : ℕ}
  {M : ℕ} [NeZero M]

/-- The carrier's source norm `‖g|_{Z'}‖_1` is the `ℓ¹` norm of the source on the sites of `Z'`. -/
theorem baseSourceNorm_eq_sourceNorm (H : RegionHistory S n R k0 K) (Z' : H.Comp 1)
    (g : GIdx S n M K N → ℂ) :
    baseSourceNorm M H Z' g = sourceNorm (baseZsites M H Z') g := rfl

end Carrier

end Balaban.LargeField
