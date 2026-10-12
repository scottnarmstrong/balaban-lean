/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvIdentity
import Mathlib.Tactic.Ring

/-!
# Real and complex forms of `A_D`; the whole-lattice case

* `actionRegionC_eq_ofReal`: for real data and a real field, the complex bilinear `A_D` is the
  complex number carried by the real form `actionRegionR`;
* `actionRegionC_univ`: for `D` the whole torus (so `Ω₁` is the whole torus and `st(D) = ∅`), `A_D`
  is the whole-lattice `actionC`, so the regional identity reduces to `lemma35_i_complete` /
  `lemma35_i_nuFree`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem cast_norm_sq_of_im {z : ℂ} (h : z.im = 0) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * z := by
  have h2 : ‖z‖ * ‖z‖ = z.re * z.re := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply, h, mul_zero, add_zero] at this
    rw [← sq, this]
  apply Complex.ext
  · simp [sq, h, h2]
  · simp [sq, h]

theorem svec_im_of_real {φ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ p, (φ p).im = 0)
    (y : Torus d (N₀ * L ^ K)) (i : Fin N) : (svec G φ y i).im = 0 := by
  by_cases hy : y ∈ G.Ω 1
  · rw [show svec G φ y i = φ (⟨y, hy⟩, i) from svec_of_mem G φ ⟨y, hy⟩ i]
    exact hφ _
  · rw [svec_of_not_mem G φ hy i]
    simp

theorem blockAvg_im_of_real {φ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ p, (φ p).im = 0)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) : (blockAvg G φ x i).im = 0 := by
  unfold blockAvg
  rw [Complex.im_ofReal_mul, Complex.im_sum]
  simp [svec_im_of_real hφ]

theorem barField_im_of_real {Dat : BgData G N} (hD : Dat.IsReal) {φ : G.Ω 1 × Fin N → ℂ}
    (hφ : ∀ p, (φ p).im = 0) (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    (barField G Dat.Ψ φ y i).im = 0 := by
  by_cases hy : y ∈ G.Ω 1
  · simp only [barField, hy, dite_true]
    exact hφ _
  · simp only [barField, hy, dite_false]
    exact (hD y i).1

/-- For real data and a real field, the complex bilinear `A_D` is the real `A_D`. -/
theorem actionRegionC_eq_ofReal (D : Region G) (a : ℕ → ℝ) (ν : ℝ) {Dat : BgData G N}
    (hD : Dat.IsReal) {φ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ p, (φ p).im = 0) :
    actionRegionC D a ν Dat φ = (actionRegionR D a ν Dat φ : ℂ) := by
  have e1 : ∀ x : Torus d (N₀ * L ^ K), ∑ i, (Dat.Ψ x i - blockAvg G φ x i) *
      (Dat.Ψ x i - blockAvg G φ x i) = ∑ i, ((‖Dat.Ψ x i - blockAvg G φ x i‖ : ℝ) : ℂ) ^ 2 :=
    fun x => Finset.sum_congr rfl fun i _ => by
      have : (Dat.Ψ x i - blockAvg G φ x i).im = 0 := by
        simp [(hD x i).1, blockAvg_im_of_real hφ]
      rw [cast_norm_sq_of_im this]
  have e2 : ∀ x : Torus d (N₀ * L ^ K), ∀ μ : Fin d,
      ∑ i, (barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i) *
        (barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i) =
      ∑ i, ((‖barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i‖ : ℝ) : ℂ) ^ 2 :=
    fun x μ => Finset.sum_congr rfl fun i _ => by
      have : (barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i).im = 0 := by
        simp [barField_im_of_real hD hφ]
      rw [cast_norm_sq_of_im this]
  have e3 : ∀ x : Torus d (N₀ * L ^ K), ∑ i, (svec G φ x i - Dat.h x i) *
      (svec G φ x i - Dat.h x i) = ∑ i, ((‖svec G φ x i - Dat.h x i‖ : ℝ) : ℂ) ^ 2 :=
    fun x => Finset.sum_congr rfl fun i _ => by
      have : (svec G φ x i - Dat.h x i).im = 0 := by
        simp [svec_im_of_real hφ, (hD x i).2]
      rw [cast_norm_sq_of_im this]
  unfold actionRegionC actionRegionR Region.blockPair Region.bondPair Region.massPair levelCoeff
  simp only [e1, e2, e3]
  push_cast
  ring

/-- For `D` the whole torus, `A_D` is the whole-lattice action `actionC`. -/
theorem actionRegionC_univ (D : Region G) (hD : D.sites = Finset.univ) (a : ℕ → ℝ) (ν : ℝ)
    (Dat : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    actionRegionC D a ν Dat φ = actionC G a ν Dat φ := by
  have hΩ : G.Ω 1 = Finset.univ := Finset.eq_univ_of_forall fun x => by
    have : x ∈ D.sites := by rw [hD]; exact Finset.mem_univ x
    exact D.sub_Ω this
  have hsum : ∀ F : Torus d (N₀ * L ^ K) → ℂ, ∑ x : G.Ω 1, F x = ∑ x, F x := fun F => by
    rw [Finset.sum_coe_sort (G.Ω 1) F, hΩ]
  have hm : ∑ x : G.Ω 1, ∑ i, (φ (x, i) - Dat.h x i) * (φ (x, i) - Dat.h x i) =
      ∑ x, ∑ i, (svec G φ x i - Dat.h x i) * (svec G φ x i - Dat.h x i) := by
    rw [← hsum (fun y => ∑ i, (svec G φ y i - Dat.h y i) * (svec G φ y i - Dat.h y i))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [svec_of_mem G φ x i]
  unfold actionRegionC actionC Region.blockPair Region.bondPair Region.massPair levelCoeff
    Region.starWeight
  rw [hD, hm, hsum (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      ∑ i, (Dat.Ψ x i - blockAvg G φ x i) * (Dat.Ψ x i - blockAvg G φ x i))]
  simp only [hΩ, Finset.mem_univ, true_or, ite_true]
  norm_num

end Balaban.LargeField.ActionConv
