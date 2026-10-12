module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The change of variables of the Gaussian factors (Lemma II.5.13, step (1))

`lintegral_affine_pi`: for `z > 0` the substitution `u = z o - q` on `(ℝ^N)^β` has Jacobian
`z^{N #β}`; this turns the integral over the Gaussian variables into the numbers `m^w_k`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- Change of variables `u = z o - q` on `(ℝ^N)^β`, `z > 0`:
`z^{N #β} ∫ h(z o - q) do = ∫ h(u) du`. -/
theorem lintegral_affine_pi (N : ℕ) (β : Type*) [Fintype β] {z : ℝ} (hz : 0 < z)
    (q : β → EuclideanSpace ℝ (Fin N)) (h : (β → EuclideanSpace ℝ (Fin N)) → ℝ≥0∞)
    (hh : Measurable h) :
    ENNReal.ofReal (z ^ (N * Fintype.card β)) *
        ∫⁻ o : β → EuclideanSpace ℝ (Fin N), h (fun y => z • o y - q y)
          ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      ∫⁻ u, h u ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) := by
  classical
  have hvol : (Measure.pi fun _ : β => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      (volume : Measure (β → EuclideanSpace ℝ (Fin N))) := (volume_pi).symm
  rw [hvol]
  have hfin : Module.finrank ℝ (β → EuclideanSpace ℝ (Fin N)) = N * Fintype.card β := by
    rw [Module.finrank_pi_fintype]
    simp [Finset.sum_const, mul_comm]
  have hz0 : z ≠ 0 := hz.ne'
  have hmap := Measure.map_addHaar_smul (volume : Measure (β → EuclideanSpace ℝ (Fin N))) hz0
  have hmh' : Measurable (fun v : β → EuclideanSpace ℝ (Fin N) => h (v - q)) :=
    hh.comp (measurable_id.sub_const _)
  have e1 : ∫⁻ o : β → EuclideanSpace ℝ (Fin N), h (fun y => z • o y - q y) =
      ∫⁻ o : β → EuclideanSpace ℝ (Fin N), (fun v => h (v - q)) (z • o) := by
    refine lintegral_congr fun o => ?_
    rfl
  rw [e1, ← lintegral_map hmh' (measurable_const_smul z), hmap, lintegral_smul_measure]
  have e2 : ∫⁻ v : β → EuclideanSpace ℝ (Fin N), h (v - q) = ∫⁻ v, h v :=
    lintegral_sub_right_eq_self (μ := (volume : Measure (β → EuclideanSpace ℝ (Fin N)))) h q
  rw [e2, smul_eq_mul, ← mul_assoc, hfin]
  have : ENNReal.ofReal (z ^ (N * Fintype.card β)) *
      ENNReal.ofReal |(z ^ (N * Fintype.card β))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity)]
    simp
  rw [this, one_mul]

end Balaban.LargeField
