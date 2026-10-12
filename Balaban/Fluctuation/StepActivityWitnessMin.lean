/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegUnit
public import Balaban.Fluctuation.CriticalPoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The constant unit field is not the minimizer for data with a nonzero perpendicular mean

For a whole-lattice generating set `G` of level `n` and `N = 2`, the action of a constant field
`c` (`constPhi`) is `½ w ∑_x ∑_i |Ψ(x)_i - c_i|²` (`action_constPhi`, `w = a_n L^{-2n}`, mass `0`).
If the constant unit field `e₀ = (1,0)` is a minimizer for real data `Ψ`, comparing it with the
rotated constants `(cos θ, sin θ)` gives `P(1 - cos θ) ≥ Q sin θ` for all `θ`, with
`P = ∑ Ψ_0`, `Q = ∑ Ψ_1`; hence `Q = 0` (`sum_perp_eq_zero`).  Used to show that the background
field of the step moves along the ray (`StepActivityWitnessNe`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited Finset

/-- If `Q sin θ ≤ P (1 - cos θ)` for all `θ`, then `Q = 0`. -/
theorem perp_zero_of_forall (P Q : ℝ) (h : ∀ θ : ℝ, Q * Real.sin θ ≤ P * (1 - Real.cos θ)) :
    Q = 0 := by
  by_contra hQ
  have hQ' : 0 < |Q| := abs_pos.2 hQ
  set t : ℝ := min 1 (|Q| / (2 * |P| + 2)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hsin : t - t ^ 3 / 6 < Real.sin t := Real.sin_gt_sub_cube ht0
  have hcos : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
  have hkey : |Q| * Real.sin t ≤ P * (1 - Real.cos t) := by
    rcases le_or_gt 0 Q with hq | hq
    · rw [abs_of_nonneg hq]; exact h t
    · rw [abs_of_neg hq]
      have := h (-t)
      rw [Real.sin_neg, Real.cos_neg] at this
      linarith
  have hc0 : 0 ≤ 1 - Real.cos t := by linarith [Real.cos_le_one t]
  have hP : P * (1 - Real.cos t) ≤ |P| * (t ^ 2 / 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self P) hc0).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg P))
  have h3 : t - t ^ 3 / 6 ≥ 3 * t / 4 := by nlinarith [mul_pos ht0 ht0]
  have h4 : |Q| * (3 * t / 4) ≤ |P| * (t ^ 2 / 2) :=
    calc |Q| * (3 * t / 4) ≤ |Q| * Real.sin t :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg Q)
      _ ≤ _ := hkey.trans hP
  have h5 : 3 * |Q| ≤ 2 * |P| * t := by
    have : t * (3 * |Q|) ≤ t * (2 * |P| * t) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  have h6 : t ≤ |Q| / (2 * |P| + 2) := min_le_right _ _
  have h7 : t * (2 * |P| + 2) ≤ |Q| := by rwa [le_div_iff₀ (by positivity)] at h6
  nlinarith [abs_nonneg P]

section Const

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The constant field `c` on `Ω₁`. -/
noncomputable def constPhi (G : GeneratingSet d L N₀ K ϱ) (c : Fin N → ℝ) :
    G.Ω 1 × Fin N → ℂ := fun p => (c p.2 : ℂ)

theorem svec_constPhi {n : ℕ} (hG : IsLevel G n) (c : Fin N → ℝ) (y : Torus d (N₀ * L ^ K))
    (i : Fin N) : svec G (constPhi G c) y i = (c i : ℂ) := by
  rw [svec_of_mem G _ ⟨y, (hG y).1⟩ i]
  rfl

theorem barField_constPhi {n : ℕ} (hG : IsLevel G n) (D : BgData G N) (c : Fin N → ℝ)
    (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    barField G D.Ψ (constPhi G c) y i = (c i : ℂ) := by
  rw [barField_eq_svec hG, svec_constPhi hG]

theorem blockAvg_constPhi {n : ℕ} (hG : IsLevel G n) (c : Fin N → ℝ) (x : Torus d (N₀ * L ^ K))
    (i : Fin N) : blockAvg G (constPhi G c) x i = (c i : ℂ) := by
  have hb : blockAvg G (constPhi G c) x i =
      blockMean G n (fun y => svec G (constPhi G c) y i) x := by
    unfold blockAvg blockMean
    rw [(hG x).2]
  rw [hb]
  have : (fun y => svec G (constPhi G c) y i) = fun _ => (c i : ℂ) :=
    funext fun y => svec_constPhi hG c y i
  rw [this]
  exact blockMean_const G (hG.bounds.2) _ x

theorem action_constPhi {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) (D : BgData G N)
    (c : Fin N → ℝ) :
    action G a 0 D (constPhi G c) = (1 / 2) * ∑ x : G.Ω 1, (a n / ((L : ℝ) ^ n) ^ 2) *
      ∑ i, ‖D.Ψ x i - (c i : ℂ)‖ ^ 2 := by
  unfold action
  have h1 : ∀ x : G.Ω 1, ∀ i, blockAvg G (constPhi G c) x i = (c i : ℂ) :=
    fun x i => blockAvg_constPhi hG c x i
  have h2 : ∀ (y : Torus d (N₀ * L ^ K)) (μ : Fin d) (i : Fin N),
      barField G D.Ψ (constPhi G c) (y + Pi.single μ 1) i -
        barField G D.Ψ (constPhi G c) y i = 0 := by
    intro y μ i
    rw [barField_constPhi hG, barField_constPhi hG, sub_self]
  have hl : ∀ x : Torus d (N₀ * L ^ K), G.layerIndex x = n := fun x => (hG x).2
  simp [h1, h2, hl]

theorem norm_sub_real_sq {z : ℂ} (hz : z.im = 0) (r : ℝ) : ‖z - (r : ℂ)‖ ^ 2 = (z.re - r) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [hz]
  ring

theorem isRealUnitField_rot (θ : ℝ) :
    IsRealUnitField G (constPhi G (N := 2) ![Real.cos θ, Real.sin θ]) := by
  intro x
  refine ⟨fun i => ?_, ?_⟩
  · simp [constPhi]
  · simp only [constPhi, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.cos_sq_add_sin_sq θ

/-- **If `e₀` is a minimizer for real data, the perpendicular component of the data sums to
zero.** -/
theorem sum_perp_eq_zero {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) (D : BgData G 2)
    (hreal : ∀ x i, (D.Ψ x i).im = 0) (hw : 0 < a n / ((L : ℝ) ^ n) ^ 2)
    (hmin : ∀ σ, IsRealUnitField G σ →
      action G a 0 D (constPhi G (N := 2) ![1, 0]) ≤ action G a 0 D σ) :
    ∑ x : G.Ω 1, (D.Ψ x 1).re = 0 := by
  set P : ℝ := ∑ x : G.Ω 1, (D.Ψ x 0).re with hP
  set Q : ℝ := ∑ x : G.Ω 1, (D.Ψ x 1).re with hQ
  refine perp_zero_of_forall P Q fun θ => ?_
  have h := hmin _ (isRealUnitField_rot (G := G) θ)
  rw [action_constPhi hG, action_constPhi hG] at h
  simp only [Fin.sum_univ_two] at h
  have hx : ∀ (r0 r1 : ℝ) (x : G.Ω 1),
      ‖D.Ψ x 0 - (( ![r0, r1] 0 : ℝ) : ℂ)‖ ^ 2 + ‖D.Ψ x 1 - (( ![r0, r1] 1 : ℝ) : ℂ)‖ ^ 2 =
        ((D.Ψ x 0).re - r0) ^ 2 + ((D.Ψ x 1).re - r1) ^ 2 := by
    intro r0 r1 x
    rw [norm_sub_real_sq (hreal x 0), norm_sub_real_sq (hreal x 1)]
    simp
  simp only [hx] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  have h1 := le_of_mul_le_mul_left h (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 := le_of_mul_le_mul_left h1 hw
  have hdiff : ∑ x : G.Ω 1, (((D.Ψ x 0).re - Real.cos θ) ^ 2 + ((D.Ψ x 1).re - Real.sin θ) ^ 2) -
      ∑ x : G.Ω 1, (((D.Ψ x 0).re - 1) ^ 2 + ((D.Ψ x 1).re - 0) ^ 2) =
      2 * (P * (1 - Real.cos θ) - Q * Real.sin θ) := by
    rw [← Finset.sum_sub_distrib]
    have : ∀ x : G.Ω 1, ((D.Ψ x 0).re - Real.cos θ) ^ 2 + ((D.Ψ x 1).re - Real.sin θ) ^ 2 -
        (((D.Ψ x 0).re - 1) ^ 2 + ((D.Ψ x 1).re - 0) ^ 2) =
        2 * ((D.Ψ x 0).re * (1 - Real.cos θ)) - 2 * ((D.Ψ x 1).re * Real.sin θ) := by
      intro x
      linear_combination Real.sin_sq_add_cos_sq θ
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
    ring
  nlinarith [hdiff, h2]

end Const

end Balaban.Fluctuation
