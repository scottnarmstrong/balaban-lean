/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.KernelDecay
public import Balaban.Green.MassLipschitz

/-!
# Pairings of a decaying kernel with separated vectors

If a matrix `Gm` has entries bounded by `Ck exp(-ε dist/s)` for a torus distance `dist`, then the pairing
`f ⬝ Gm e` of two vectors whose supports are at distance at least `T₀·s` is at most
`card² Ck exp(-ε T₀) E` (`pair_small`), and `f ⬝ Gm Gm e` is at most `card³ Ck² exp(-ε T₀) E`
(`pair_small2`, by the triangle inequality of the distance).
-/

@[expose] public section

namespace Balaban.Flow

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem pair_small (Gm : Matrix ι ι ℂ) (dist : ι → ι → ℝ) {Ck ε E T₀ : ℝ} (hCk : 0 ≤ Ck)
    (hE0 : 0 ≤ E) (hε : 0 ≤ ε)
    (hG : ∀ x x', ‖Gm x x'‖ ≤ Ck * Real.exp (-ε * dist x x'))
    (f e : ι → ℂ) (hf : ∀ y, ‖f y‖ ≤ 1) (he : ∀ x, ‖e x‖ ≤ E)
    (hsep : ∀ y x, f y ≠ 0 → e x ≠ 0 → T₀ ≤ dist y x) :
    ‖f ⬝ᵥ (Gm *ᵥ e)‖ ≤ (Fintype.card ι : ℝ) ^ 2 * (Ck * Real.exp (-ε * T₀) * E) := by
  have hterm : ∀ y x, ‖f y * (Gm y x * e x)‖ ≤ Ck * Real.exp (-ε * T₀) * E := by
    intro y x
    by_cases h1 : f y = 0
    · simp [h1]; positivity
    by_cases h2 : e x = 0
    · simp [h2]; positivity
    have hd := hsep y x h1 h2
    have hexp : Real.exp (-ε * dist y x) ≤ Real.exp (-ε * T₀) :=
      Real.exp_le_exp.2 (by nlinarith)
    calc ‖f y * (Gm y x * e x)‖ = ‖f y‖ * (‖Gm y x‖ * ‖e x‖) := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ((Ck * Real.exp (-ε * T₀)) * E) := by
          gcongr
          · exact hf y
          · exact (hG y x).trans (by gcongr)
          · exact he x
      _ = _ := by ring
  unfold dotProduct Matrix.mulVec
  simp only [dotProduct, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y, ‖∑ x, f y * (Gm y x * e x)‖ ≤ ∑ y : ι, ∑ x : ι, Ck * Real.exp (-ε * T₀) * E :=
        Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hterm y x)
    _ = _ := by simp [sq]; ring

omit [DecidableEq ι] in
theorem pair_small2 (Gm : Matrix ι ι ℂ) (dist : ι → ι → ℝ) {Ck ε E T₀ : ℝ} (hCk : 0 ≤ Ck)
    (hE0 : 0 ≤ E) (hε : 0 ≤ ε)
    (hG : ∀ x x', ‖Gm x x'‖ ≤ Ck * Real.exp (-ε * dist x x'))
    (htri : ∀ y z x, dist y x ≤ dist y z + dist z x)
    (f e : ι → ℂ) (hf : ∀ y, ‖f y‖ ≤ 1) (he : ∀ x, ‖e x‖ ≤ E)
    (hsep : ∀ y x, f y ≠ 0 → e x ≠ 0 → T₀ ≤ dist y x) :
    ‖f ⬝ᵥ (Gm *ᵥ (Gm *ᵥ e))‖ ≤ (Fintype.card ι : ℝ) ^ 3 * (Ck ^ 2 * Real.exp (-ε * T₀) * E) := by
  have hterm : ∀ y z x, ‖f y * (Gm y z * (Gm z x * e x))‖ ≤ Ck ^ 2 * Real.exp (-ε * T₀) * E := by
    intro y z x
    by_cases h1 : f y = 0
    · simp [h1]; positivity
    by_cases h2 : e x = 0
    · simp [h2]; positivity
    have hd := hsep y x h1 h2
    have hexp : Real.exp (-ε * dist y z) * Real.exp (-ε * dist z x) ≤ Real.exp (-ε * T₀) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [htri y z x])
    calc ‖f y * (Gm y z * (Gm z x * e x))‖
        = ‖f y‖ * (‖Gm y z‖ * (‖Gm z x‖ * ‖e x‖)) := by rw [norm_mul, norm_mul, norm_mul]
      _ ≤ 1 * ((Ck * Real.exp (-ε * dist y z)) * ((Ck * Real.exp (-ε * dist z x)) * E)) := by
          gcongr
          · exact hf y
          · exact hG y z
          · exact hG z x
          · exact he x
      _ = Ck ^ 2 * (Real.exp (-ε * dist y z) * Real.exp (-ε * dist z x)) * E := by ring
      _ ≤ Ck ^ 2 * Real.exp (-ε * T₀) * E := by gcongr
  unfold dotProduct Matrix.mulVec
  simp only [dotProduct, Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y, ‖∑ z, ∑ x, f y * (Gm y z * (Gm z x * e x))‖
      ≤ ∑ y : ι, ∑ z : ι, ∑ x : ι, Ck ^ 2 * Real.exp (-ε * T₀) * E :=
        Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => hterm y z x))
    _ = _ := by simp [pow_succ]; ring

end Balaban.Flow
