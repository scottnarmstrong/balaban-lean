module

public import Balaban.LargeField.Operators.Quiet
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Gaussian normalization and shell volumes (Lemma II.5.14)

* `lintegral_gaussT`: the Gaussian density `t_k(u, 0)` of the kernel of `T^{(k)}` integrates to `1`;
* `volume_shellSet_le`: for `0 < t ≤ 1/2` the shell `{u ∈ ℝ^N : ||u|² - 1| < t}` has volume at
  most `c_N t`, `c_N = N v_N (3/2)^{N/2}` (`cShell`), `N ≥ 2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- `∫ t_k(u, 0) du = 1`: the Gaussian density is normalized. -/
theorem lintegral_gaussT (N : ℕ) [NeZero N] {c : ℝ} (hc : 0 < c) :
    ∫⁻ u : EuclideanSpace ℝ (Fin N), ENNReal.ofReal (gaussT N c u 0) = 1 := by
  have hb : 0 < c / 2 := by positivity
  have h1 := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin N)) hb
  have hpos : 0 < (Real.pi / (c / 2)) ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) / 2) := by
    positivity
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin N) => Real.exp (-(c / 2) * ‖v‖ ^ 2)) := by
    by_contra hni
    rw [integral_undef hni] at h1
    exact hpos.ne h1
  have hfun : (fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u 0) =
      fun u => (c / (2 * Real.pi)) ^ ((N : ℝ) / 2) * Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
    funext u
    unfold gaussT
    simp
  have hint2 : Integrable (fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u 0) := by
    rw [hfun]; exact hint.const_mul _
  have hnn : 0 ≤ᵐ[volume] fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u 0 :=
    Filter.Eventually.of_forall fun u => gaussT_nonneg N c hc.le u 0
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 hnn, hfun, integral_const_mul, h1]
  have hfr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ) = N := by simp
  rw [hfr, ← Real.mul_rpow (by positivity) (by positivity)]
  have : c / (2 * Real.pi) * (Real.pi / (c / 2)) = 1 := by
    field_simp
  rw [this, Real.one_rpow, ENNReal.ofReal_one]

/-- `c_N = N v_N (3/2)^{N/2}`, `v_N` the volume of the unit ball of `ℝ^N` (Lemma II.5.14). -/
noncomputable def cShell (N : ℕ) : ℝ :=
  (N : ℝ) * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
    (3 / 2 : ℝ) ^ ((N : ℝ) / 2)

theorem rpow_sub_le (p t : ℝ) (hp : 1 ≤ p) (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    (1 + t) ^ p - (1 - t) ^ p ≤ 2 * p * (3 / 2) ^ p * t := by
  have hab : 1 - t < 1 + t := by linarith
  have hcont : ContinuousOn (fun x : ℝ => x ^ p) (Set.Icc (1 - t) (1 + t)) :=
    fun x hx => (Real.continuousAt_rpow_const x p (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ p) (Set.Ioo (1 - t) (1 + t)) :=
    fun x hx => (Real.differentiableAt_rpow_const_of_ne p (by linarith [hx.1])).differentiableWithinAt
  obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope (fun x : ℝ => x ^ p) hab hcont hdiff
  have hder : deriv (fun x : ℝ => x ^ p) ξ = p * ξ ^ (p - 1) := Real.deriv_rpow_const ξ p
  rw [hder] at hd
  have hlen : (1 + t) - (1 - t) = 2 * t := by ring
  rw [hlen] at hd
  have h1 : (1 + t) ^ p - (1 - t) ^ p = 2 * t * (p * ξ ^ (p - 1)) := by
    field_simp at hd ⊢
    linarith
  rw [h1]
  have h2 : ξ ^ (p - 1) ≤ (3 / 2 : ℝ) ^ (p - 1) :=
    Real.rpow_le_rpow (by linarith [hξ.1]) (by linarith [hξ.2]) (by linarith)
  have h3 : (3 / 2 : ℝ) ^ (p - 1) ≤ (3 / 2) ^ p :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hp0 : 0 ≤ p := by linarith
  calc 2 * t * (p * ξ ^ (p - 1)) ≤ 2 * t * (p * (3 / 2) ^ p) := by gcongr; exact h2.trans h3
    _ = 2 * p * (3 / 2) ^ p * t := by ring

/-- The shell `{u : ||u|² - 1| < t}` of `ℝ^N`. -/
def shellSet (N : ℕ) (t : ℝ) : Set (EuclideanSpace ℝ (Fin N)) := {u | |‖u‖ ^ 2 - 1| < t}

theorem sqrt_pow_nat (x : ℝ) (hx : 0 ≤ x) (N : ℕ) : (Real.sqrt x) ^ N = x ^ ((N : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- **Shell volume** (Lemma II.5.14): for `0 < t ≤ 1/2` the shell has volume at most `c_N t`. -/
theorem volume_shellSet_le (N : ℕ) (hN : 2 ≤ N) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    volume (shellSet N t) ≤ ENNReal.ofReal (cShell N * t) := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hball : ∀ r : ℝ, volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) r) =
      ENNReal.ofReal r ^ N * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) := by
    intro r
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
    simp
  have hcl : ∀ r : ℝ, volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) r) =
      ENNReal.ofReal r ^ N * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) := by
    intro r
    rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_ball]
    simp
  set V1 := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1) with hV1
  have hV1fin : V1 ≠ ∞ := (measure_ball_lt_top).ne
  have hsub : shellSet N t ⊆ (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (Real.sqrt (1 + t)) \
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) (Real.sqrt (1 - t))) := by
    intro u hu
    have hu' : |‖u‖ ^ 2 - 1| < t := hu
    rw [abs_lt] at hu'
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      exact Real.lt_sqrt_of_sq_lt (by linarith [hu'.2])
    · rw [Metric.mem_closedBall, dist_zero_right, not_le]
      have := Real.sqrt_lt_sqrt (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith [hu'.1] : 1 - t < ‖u‖ ^ 2)
      rwa [Real.sqrt_sq (norm_nonneg u)] at this
  have hsub2 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) (Real.sqrt (1 - t)) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin N)) (Real.sqrt (1 + t)) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    rw [mem_ball_zero_iff]
    exact hu.trans_lt (Real.sqrt_lt_sqrt (by linarith) (by linarith))
  have hvol : volume (shellSet N t) ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N))
      (Real.sqrt (1 + t))) - volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin N))
      (Real.sqrt (1 - t))) := by
    calc volume (shellSet N t) ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N))
          (Real.sqrt (1 + t)) \ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N))
          (Real.sqrt (1 - t))) := measure_mono hsub
      _ = _ := measure_sdiff hsub2 measurableSet_closedBall.nullMeasurableSet
            (by rw [hcl]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hV1fin)
  rw [hball, hcl, ← ENNReal.sub_mul (fun _ _ => hV1fin)] at hvol
  have hr1 : 0 ≤ Real.sqrt (1 + t) := Real.sqrt_nonneg _
  have hr2 : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
  rw [← ENNReal.ofReal_pow hr1, ← ENNReal.ofReal_pow hr2, ← ENNReal.ofReal_sub _ (by positivity),
    sqrt_pow_nat _ (by linarith) N, sqrt_pow_nat _ (by linarith) N] at hvol
  set v := V1.toReal with hv
  have hV1v : V1 = ENNReal.ofReal v := (ENNReal.ofReal_toReal hV1fin).symm
  have hp : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hdiff := rpow_sub_le ((N : ℝ) / 2) t hp ht ht1
  have hdiff0 : 0 ≤ (1 + t) ^ ((N : ℝ) / 2) - (1 - t) ^ ((N : ℝ) / 2) := by
    have : (1 - t) ^ ((N : ℝ) / 2) ≤ (1 + t) ^ ((N : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    linarith
  rw [hV1v, ← ENNReal.ofReal_mul hdiff0] at hvol
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  calc ((1 + t) ^ ((N : ℝ) / 2) - (1 - t) ^ ((N : ℝ) / 2)) * v
      ≤ (2 * ((N : ℝ) / 2) * (3 / 2) ^ ((N : ℝ) / 2) * t) * v := by gcongr
    _ = cShell N * t := by
        unfold cShell
        rw [← hv]
        ring

end Balaban.LargeField
