/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0CutoffSplit
public import Balaban.LargeField.LF1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The `R_1` gain and the per-cube arithmetic of the `Q_1`, `R_1`, `S_1` gains (Lemma II.7.8)

The remaining three witness types of Lemma II.7.8 (`LF-RECONSTRUCTION` §II.7.4, `BASE-KERNEL-4`
§4 item 6 (4.2a), (4.2b)), next to the block, bond and site gains of `BaseWitnessGain`.

* `rGain_pt`, `oneSiteGaussian_tailGe_le`, `lintegral_gaussHalf`: the fluctuation witness.  For
  `ψ'_0 ∈ ℝ^N` and `p_1 ≥ 0`,
  `(2π)^{-N/2} e^{-|ψ'_0|²/2} 1[|ψ'_0| ≥ p_1] ≤ e^{-p_1²/4} (2π)^{-N/2} e^{-|ψ'_0|²/4}`,
  the right side has integral `2^{N/2} e^{-p_1²/4}`, so the standard Gaussian gives the event
  `|ψ'_0| ≥ p_1` mass at most `2^{N/2} e^{-p_1²/4}` (P6 (3.4), second factor);
* `gainQ`, `gainR`, `gainS`: the exponents of one cube,
  `4 γ₀ p_0²/(6^d (9K_1)²)`, `p_1²/4`, `γ₀ p_0²/(4 · 6^d K_1²)`;
* `baseA3`: `A₃ = ¼ min{8γ₀A₀²/(6^d(9K_1)²), A₁²/8}` of row 9;
* `two_baseA3_le_gainQ`, `two_baseA3_le_gainR`, `two_baseA3_le_gainS`: with `p_j ≥ A_j λ^{p₀}`
  each exponent is at least `2 A₃ λ^{2p₀}`;
* `fiveShare_Q`, `fiveShare_R`, `fiveShare_S`: the premises `hQ`, `hR`, `hS` of
  `baseFirst_operator_majorant_of_fiveShares` for the gains `n · gainQ`, `n · gainR`, `n · gainS`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Balaban.LargeField

section RGain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **`R_1` witness, pointwise**: for `p ≥ 0`,
`(2π)^{-n/2} e^{-|x|²/2} 1[p ≤ |x|] ≤ e^{-p²/4} (2π)^{-n/2} e^{-|x|²/4}`. -/
theorem rGain_pt {p : ℝ} (hp : 0 ≤ p) (x : E) :
    (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2) *
        Set.indicator {x : E | p ≤ ‖x‖} (fun _ => (1 : ℝ)) x ≤
      Real.exp (-(p ^ 2 / 4)) *
        ((2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) := by
  have hc : 0 ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by positivity
  by_cases hx : p ≤ ‖x‖
  · rw [Set.indicator_of_mem (by exact hx), mul_one]
    have h1 : Real.exp (-(1 / 2) * ‖x‖ ^ 2) ≤
        Real.exp (-(1 / 4) * ‖x‖ ^ 2) * Real.exp (-(p ^ 2 / 4)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : p ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hp hx 2
      nlinarith
    calc _ ≤ (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          (Real.exp (-(1 / 4) * ‖x‖ ^ 2) * Real.exp (-(p ^ 2 / 4))) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = _ := by ring
  · rw [Set.indicator_of_notMem (by exact hx), mul_zero]
    positivity

/-- **`R_1` witness, integrated**: the standard Gaussian gives `{|x| ≥ p}` mass at most
`2^{n/2} e^{-p²/4}`, `n = dim E`. -/
theorem oneSiteGaussian_tailGe_le {p : ℝ} (hp : 0 ≤ p) :
    oneSiteGaussian E {x : E | p ≤ ‖x‖} ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(p ^ 2 / 4))) := by
  set c : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hmeas : MeasurableSet {x : E | p ≤ ‖x‖} := measurableSet_le measurable_const measurable_norm
  unfold oneSiteGaussian
  rw [withDensity_apply _ hmeas, ← lintegral_indicator hmeas]
  have hpt : ∀ x : E, Set.indicator {x : E | p ≤ ‖x‖}
      (fun x => ENNReal.ofReal (c * Real.exp (-(1 / 2) * ‖x‖ ^ 2))) x ≤
      ENNReal.ofReal (Real.exp (-(p ^ 2 / 4)) * c) *
        ENNReal.ofReal (Real.exp (-(1 / 4) * ‖x‖ ^ 2)) := by
    intro x
    by_cases hx : p ≤ ‖x‖
    · rw [Set.indicator_of_mem (by exact hx), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := rGain_pt (E := E) hp x
      rw [Set.indicator_of_mem (by exact hx), mul_one] at this
      calc c * Real.exp (-(1 / 2) * ‖x‖ ^ 2) ≤ _ := this
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (by exact hx)]
      exact zero_le
  calc _ ≤ ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(p ^ 2 / 4)) * c) *
        ENNReal.ofReal (Real.exp (-(1 / 4) * ‖x‖ ^ 2)) := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (-(p ^ 2 / 4)) * c) *
        ∫⁻ x : E, ENNReal.ofReal (1 * Real.exp (-(1 / 4) * ‖x‖ ^ 2)) := by
        rw [lintegral_const_mul _ (by fun_prop)]
        simp only [one_mul]
    _ = _ := by
        rw [lintegral_exp_neg_mul_sq_norm (b := 1 / 4) (by norm_num) (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h2π : 0 < 2 * Real.pi := by positivity
        have e1 : Real.pi / (1 / 4) = 2 * (2 * Real.pi) := by ring
        have e2 : -(Module.finrank ℝ E : ℝ) / 2 = -((Module.finrank ℝ E : ℝ) / 2) := by ring
        rw [hc, e1, e2, Real.rpow_neg h2π.le, Real.mul_rpow (by norm_num) h2π.le, one_mul]
        have hpos : 0 < (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) :=
          Real.rpow_pos_of_pos h2π _
        field_simp

end RGain

/-- The `R_1` witness for `ψ'_0 ∈ ℝ^N`: the standard Gaussian of `ℝ^N` gives `{|ψ'_0| ≥ p_1}` mass at
most `2^{N/2} e^{-p_1²/4}`. -/
theorem oneSiteGaussian_tailGe_le_euclid (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    oneSiteGaussian (EuclideanSpace ℝ (Fin N)) {x | p ≤ ‖x‖} ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) / 2) * Real.exp (-(p ^ 2 / 4))) := by
  have := oneSiteGaussian_tailGe_le (E := EuclideanSpace ℝ (Fin N)) hp
  simpa [finrank_euclideanSpace_fin] using this

section Arithmetic

/-- The exponent of one `Q_1` cube: `4 γ₀ p_0²/(6^d (9K_1)²)` (P6 (3.7), halved). -/
noncomputable def gainQ (d : ℕ) (γ₀ K₁ p₀ : ℝ) : ℝ := 4 * γ₀ / (6 ^ d * (9 * K₁) ^ 2) * p₀ ^ 2

/-- The exponent of one `R_1` cube: `p_1²/4`. -/
noncomputable def gainR (p₁ : ℝ) : ℝ := p₁ ^ 2 / 4

/-- The exponent of one `S_1` cube: `γ₀ p_0²/(4 · 6^d K_1²)` (P6 (3.8), halved). -/
noncomputable def gainS (d : ℕ) (γ₀ K₁ p₀ : ℝ) : ℝ := γ₀ / (4 * 6 ^ d * K₁ ^ 2) * p₀ ^ 2

/-- The constant `A₃ = ¼ min{8γ₀A₀²/(6^d(9K_1)²), A₁²/8}` (LF-RECONSTRUCTION row 9). -/
noncomputable def baseA3 (d : ℕ) (γ₀ K₁ A₀ A₁ : ℝ) : ℝ :=
  1 / 4 * min (8 * γ₀ * A₀ ^ 2 / (6 ^ d * (9 * K₁) ^ 2)) (A₁ ^ 2 / 8)

variable {d : ℕ} {γ₀ K₁ A₀ A₁ lam P : ℝ}

private theorem sq_ge_of_ge {A : ℝ} {p₀ : ℕ} (hA : 0 ≤ A) (hl : 0 ≤ lam)
    (hP : A * lam ^ p₀ ≤ P) : A ^ 2 * lam ^ (2 * p₀) ≤ P ^ 2 := by
  have h0 : 0 ≤ A * lam ^ p₀ := by positivity
  have := pow_le_pow_left₀ h0 hP 2
  calc A ^ 2 * lam ^ (2 * p₀) = (A * lam ^ p₀) ^ 2 := by ring
    _ ≤ P ^ 2 := this

theorem two_baseA3_le_gainQ {p₀ : ℕ} (hγ : 0 ≤ γ₀) (hK : 0 < K₁) (hA₀ : 0 ≤ A₀) (hl : 0 ≤ lam)
    (hP : A₀ * lam ^ p₀ ≤ P) (A₁ : ℝ) :
    2 * baseA3 d γ₀ K₁ A₀ A₁ * lam ^ (2 * p₀) ≤ gainQ d γ₀ K₁ P := by
  have hsq := sq_ge_of_ge hA₀ hl hP
  have hc : 0 ≤ γ₀ / (6 ^ d * (9 * K₁) ^ 2) := by positivity
  have hmin : min (8 * γ₀ * A₀ ^ 2 / (6 ^ d * (9 * K₁) ^ 2)) (A₁ ^ 2 / 8) ≤
      8 * (γ₀ / (6 ^ d * (9 * K₁) ^ 2)) * A₀ ^ 2 := by
    refine (min_le_left _ _).trans (le_of_eq ?_)
    ring
  unfold baseA3 gainQ
  have e : 4 * γ₀ / (6 ^ d * (9 * K₁) ^ 2) * P ^ 2 =
      4 * (γ₀ / (6 ^ d * (9 * K₁) ^ 2)) * P ^ 2 := by ring
  rw [e]
  have hl2 : 0 ≤ lam ^ (2 * p₀) := by positivity
  calc 2 * (1 / 4 * min (8 * γ₀ * A₀ ^ 2 / (6 ^ d * (9 * K₁) ^ 2)) (A₁ ^ 2 / 8)) * lam ^ (2 * p₀)
      ≤ 2 * (1 / 4 * (8 * (γ₀ / (6 ^ d * (9 * K₁) ^ 2)) * A₀ ^ 2)) * lam ^ (2 * p₀) := by
        gcongr
    _ = 4 * (γ₀ / (6 ^ d * (9 * K₁) ^ 2)) * (A₀ ^ 2 * lam ^ (2 * p₀)) := by ring
    _ ≤ 4 * (γ₀ / (6 ^ d * (9 * K₁) ^ 2)) * P ^ 2 := by gcongr

theorem two_baseA3_le_gainS {p₀ : ℕ} (hγ : 0 ≤ γ₀) (hK : 0 < K₁) (hA₀ : 0 ≤ A₀) (hl : 0 ≤ lam)
    (hP : A₀ * lam ^ p₀ ≤ P) (A₁ : ℝ) :
    2 * baseA3 d γ₀ K₁ A₀ A₁ * lam ^ (2 * p₀) ≤ gainS d γ₀ K₁ P := by
  have h1 := two_baseA3_le_gainQ (d := d) hγ hK hA₀ hl hP A₁
  refine h1.trans ?_
  unfold gainQ gainS
  have hc : 0 ≤ γ₀ / (6 ^ d * K₁ ^ 2) := by positivity
  have e1 : 4 * γ₀ / (6 ^ d * (9 * K₁) ^ 2) = 4 / 81 * (γ₀ / (6 ^ d * K₁ ^ 2)) := by ring
  have e2 : γ₀ / (4 * 6 ^ d * K₁ ^ 2) = 1 / 4 * (γ₀ / (6 ^ d * K₁ ^ 2)) := by ring
  rw [e1, e2]
  have hP2 : 0 ≤ P ^ 2 := sq_nonneg P
  have : 4 / 81 * (γ₀ / (6 ^ d * K₁ ^ 2)) ≤ 1 / 4 * (γ₀ / (6 ^ d * K₁ ^ 2)) :=
    mul_le_mul_of_nonneg_right (by norm_num) hc
  exact mul_le_mul_of_nonneg_right this hP2

theorem two_baseA3_le_gainR {p₀ : ℕ} (hA₁ : 0 ≤ A₁) (hl : 0 ≤ lam)
    (hP : A₁ * lam ^ p₀ ≤ P) (A₀ : ℝ) :
    2 * baseA3 d γ₀ K₁ A₀ A₁ * lam ^ (2 * p₀) ≤ gainR P := by
  have hsq := sq_ge_of_ge hA₁ hl hP
  unfold baseA3 gainR
  have hl2 : 0 ≤ lam ^ (2 * p₀) := by positivity
  calc 2 * (1 / 4 * min (8 * γ₀ * A₀ ^ 2 / (6 ^ d * (9 * K₁) ^ 2)) (A₁ ^ 2 / 8)) * lam ^ (2 * p₀)
      ≤ 2 * (1 / 4 * (A₁ ^ 2 / 8)) * lam ^ (2 * p₀) := by gcongr; exact min_le_right _ _
    _ = A₁ ^ 2 * lam ^ (2 * p₀) / 16 := by ring
    _ ≤ P ^ 2 / 4 := by
        have : 0 ≤ A₁ ^ 2 * lam ^ (2 * p₀) := by positivity
        linarith

/-- The premise `hQ` of `baseFirst_operator_majorant_of_fiveShares` for the gain `n · gainQ`. -/
theorem fiveShare_Q {p₀ : ℕ} (hγ : 0 ≤ γ₀) (hK : 0 < K₁) (hA₀ : 0 ≤ A₀) (hl : 0 ≤ lam)
    (hP : A₀ * lam ^ p₀ ≤ P) (A₁ n : ℝ) (hn : 0 ≤ n) :
    2 * baseA3 d γ₀ K₁ A₀ A₁ * lam ^ (2 * p₀) * n ≤ n * gainQ d γ₀ K₁ P := by
  rw [mul_comm n]
  exact mul_le_mul_of_nonneg_right (two_baseA3_le_gainQ hγ hK hA₀ hl hP A₁) hn

/-- The premise `hR` of `baseFirst_operator_majorant_of_fiveShares` for the gain `n · gainR`. -/
theorem fiveShare_R {p₀ : ℕ} (hA₁ : 0 ≤ A₁) (hl : 0 ≤ lam)
    (hP : A₁ * lam ^ p₀ ≤ P) (A₀ n : ℝ) (hn : 0 ≤ n) :
    2 * baseA3 d γ₀ K₁ A₀ A₁ * lam ^ (2 * p₀) * n ≤ n * gainR P := by
  rw [mul_comm n]
  exact mul_le_mul_of_nonneg_right (two_baseA3_le_gainR hA₁ hl hP A₀) hn

/-- The premise `hS` of `baseFirst_operator_majorant_of_fiveShares` for the gain `n · gainS`. -/
theorem fiveShare_S {p₀ : ℕ} (hγ : 0 ≤ γ₀) (hK : 0 < K₁) (hA₀ : 0 ≤ A₀) (hl : 0 ≤ lam)
    (hP : A₀ * lam ^ p₀ ≤ P) (A₁ n : ℝ) (hn : 0 ≤ n) :
    2 * baseA3 d γ₀ K₁ A₀ A₁ * lam ^ (2 * p₀) * n ≤ n * gainS d γ₀ K₁ P := by
  rw [mul_comm n]
  exact mul_le_mul_of_nonneg_right (two_baseA3_le_gainS hγ hK hA₀ hl hP A₁) hn

end Arithmetic

end Balaban.LargeField
