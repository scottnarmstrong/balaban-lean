module

public import Balaban.LargeField.R.KeptOutcomeOneGain
public import Balaban.LargeField.R.KeptOutcomeGainIntegral

/-!
# The first kept outcome through the half Gaussian node integral

The cutoff weight is at most one. The node density contains the retained half
of the composed Gaussian; its integral is at most `2^(N/2)` per block. The
remaining half pays for the small factor of Lemma III.5.3 (a).
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- The `hid` estimate with the half Gaussian retained on independent top
blocks. `hpoint` is the physical kernel comparison with this Gaussian, and
`hgain` follows from `kept_one_ripe_half_exp_gain_of_conversion` when `q`
is the first outcome weight. -/
theorem kept_one_hid_of_half_gauss_nodes {ι : Type*} [Fintype ι] {N : ℕ}
    (p : ι → ℝ) (hp : ∀ i, 0 < p i)
    (m : ι → EuclideanSpace ℝ (Fin N))
    (F : (ι → EuclideanSpace ℝ (Fin N)) → ℝ≥0∞)
    (q Gwin Awin : (ι → EuclideanSpace ℝ (Fin N)) → ℝ)
    (Core : ℝ≥0∞) (bw Lc C γ : ℝ)
    (hpoint : ∀ v, F v ≤
      (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc)) *
        ENNReal.ofReal (Real.exp (-(Gwin v / 2) - Awin v)) *
          (ENNReal.ofReal (q v) *
            ∏ i, ENNReal.ofReal
              ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
                Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2))))
    (hq : ∀ v, 0 ≤ q v ∧ q v ≤ 1) (hqmeas : Measurable q)
    (hgain : ∀ v, q v ≠ 0 → γ ≤ Gwin v / 2 + Awin v + C) :
    ∫⁻ v : ι → EuclideanSpace ℝ (Fin N), F v
        ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N)))) ≤
      (Core * ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) / 2)) ^ Fintype.card ι) *
        ENNReal.ofReal (Real.exp bw * Real.exp Lc * Real.exp (C - γ)) := by
  classical
  have hρmeas : Measurable (fun v : ι → EuclideanSpace ℝ (Fin N) =>
      ENNReal.ofReal (q v) *
        ∏ i, ENNReal.ofReal
          ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
            Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2))) := by
    fun_prop
  have hρbound : (∫⁻ v : ι → EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal (q v) *
        ∏ i, ENNReal.ofReal
          ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
            Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2))
        ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) / 2)) ^ Fintype.card ι := by
    calc
      _ ≤ ∫⁻ v : ι → EuclideanSpace ℝ (Fin N),
        ∏ i, ENNReal.ofReal
          ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
            Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2))
          ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N)))) := by
          apply lintegral_mono
          intro v
          have hqle : ENNReal.ofReal (q v) ≤ 1 := by
            simpa using ENNReal.ofReal_le_ofReal (hq v).2
          calc
            _ ≤ (1 : ℝ≥0∞) *
                ∏ i, ENNReal.ofReal
                  ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
                    Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2)) := by
                  exact mul_le_mul_of_nonneg_right hqle zero_le
            _ = _ := one_mul _
      _ = _ := lintegral_half_gaussDens_pi p hp m
  apply kept_hid_gain_of_node_integral'
    (Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N)))) F
    (fun v => ENNReal.ofReal (q v) *
      ∏ i, ENNReal.ofReal
        ((p i / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
          Real.exp (-(p i / 4) * ‖v i - m i‖ ^ 2)))
    (fun v => Gwin v / 2) Awin Core
    (ENNReal.ofReal ((2 : ℝ) ^ ((N : ℝ) / 2)) ^ Fintype.card ι)
    bw Lc C γ hpoint (by
      intro v hv
      apply hgain v
      intro hz
      simp [hz] at hv) hρmeas hρbound

end Balaban.LargeField
