module

public import Balaban.LargeField.R.RRemovedChainIntegral
public import Balaban.LargeField.R.SmallFactorChi
public import Balaban.LargeField.R.Outcome
public import Balaban.LargeField.Operators.PiTools
import Mathlib.Tactic.Positivity

/-!
# The half Gaussian of the first kept outcome

For one unconstrained top block, the composed Gaussian normalization at half
its precision integrates to `2^(N/2)`. The finite product gives this factor
once per independent block. The weight `1 - chiTilde` is supported off the
sharp tilde window.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal Balaban Balaban.Multiscale RegionHistory

/-- The unnormalized half Gaussian is `2^(N/2)` times the normalized Gaussian
of precision `p/2`. -/
theorem half_gaussDens_eq {N : ℕ} {p : ℝ} (hp : 0 < p)
    (v m : EuclideanSpace ℝ (Fin N)) :
    (p / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
      Real.exp (-(p / 4) * ‖v - m‖ ^ 2) =
      (2 : ℝ) ^ ((N : ℝ) / 2) * gaussDens (p / 2) (v - m) := by
  unfold gaussDens
  rw [finrank_euclideanSpace_fin]
  have hconst : p / (2 * Real.pi) =
      2 * ((p / 2) / (2 * Real.pi)) := by ring
  rw [hconst, Real.mul_rpow (by norm_num) (by positivity)]
  have hexp : -(p / 4) * ‖v - m‖ ^ 2 = -((p / 2) / 2) * ‖v - m‖ ^ 2 := by ring
  rw [hexp]
  ring

/-- One unconstrained top block contributes exactly `2^(N/2)` to the lower
integral when half of the composed Gaussian is retained. -/
theorem lintegral_half_gaussDens {N : ℕ} {p : ℝ} (hp : 0 < p)
    (m : EuclideanSpace ℝ (Fin N)) :
    ∫⁻ v : EuclideanSpace ℝ (Fin N), ENNReal.ofReal
      ((p / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
        Real.exp (-(p / 4) * ‖v - m‖ ^ 2)) =
      ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) / 2)) := by
  simp_rw [half_gaussDens_eq hp]
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ ((N : ℝ) / 2))]
  rw [lintegral_const_mul]
  · rw [lintegral_gaussDens_shift (by positivity : 0 < p / 2) m, mul_one]
  · unfold gaussDens
    fun_prop

/-- Independent top blocks contribute one factor `2^(N/2)` each. -/
theorem lintegral_half_gaussDens_pi {ι : Type*} [Fintype ι] {N : ℕ}
    (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (m : ι → EuclideanSpace ℝ (Fin N)) :
    ∫⁻ v : ι → EuclideanSpace ℝ (Fin N),
      ∏ i, ENNReal.ofReal
        ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
          Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2))
        ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) / 2)) ^ Fintype.card ι := by
  classical
  rw [PiTools.lintegral_fintype_prod_eq_prod ι
    (fun i v => ENNReal.ofReal
      ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
        Real.exp (-(p i / 4) * ‖v - m i‖ ^ 2)))
    (fun i => by fun_prop)]
  simp_rw [lintegral_half_gaussDens (hp _) (m _)]
  simp

/-- The first kept weight vanishes on the landed tilde window set. -/
theorem kept_one_weight_support {S : Setting} {n : ℕ → ℕ}
    [∀ k, NeZero (n k)] {M K N : ℕ} [NeZero M] [NeZero S.L]
    (a : LocalHistory S n M K) (k : ℕ)
    (Z0 : Set (Torus S.d (M * n K * S.L ^ K))) (δ : ℝ)
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    Outcome.weight (chiTilde a k Z0 δ ψ) 0 0 0 0 Outcome.kappa1 ≠ 0 →
      ¬ ChiTildeProp a k Z0 δ ψ := by
  intro hweight hwindow
  have hchi : chiTilde a k Z0 δ ψ = 1 := charFn_eq_one hwindow
  simp [Outcome.weight, hchi] at hweight

end Balaban.LargeField
