module

public import Balaban.LargeField.Operators.QuietInt
public import Balaban.LargeField.Operators.PiTools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gaussian tail and union bound for the block witnesses (Lemma II.7.8, block witness)

The block witness of a cube `□' ∈ P_1` costs, in `m^w_0 = ∫ ∏_y g_0(u_y) F^w_0(u) du`, the factor
`∫ g_0(u) 1[|u| ≥ 2 δ₀] du ≤ 2^{N/2} e^{-¼ c (2δ₀)²}` (`c = β a L^{d-2}`; half of the Gaussian
exponent for the gain, the other half for the integral; P6 (3.4), first factor).

* `lintegral_gaussT_tail`: the tail estimate for one block;
* `lintegral_gauss_prod_ind_le`: for a set `T` of blocks, the probability that all blocks of `T`
  have `|u_y| ≥ r` is at most `q^{#T}`;
* `lintegral_gauss_union_le`: the union bound over a family of disjoint groups of blocks:
  `∫ ∏_y g(u_y) ∏_{c} (∑_{y ∈ Y_c} 1[|u_y| ≥ r]) ≤ ∏_c (#Y_c) q`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- The tail of the Gaussian: `∫ t(u, 0) 1[r ≤ |u|] du ≤ 2^{N/2} e^{-c r²/4}`. -/
theorem lintegral_gaussT_tail (N : ℕ) [NeZero N] {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ u : EuclideanSpace ℝ (Fin N),
        ENNReal.ofReal (gaussT N c u 0) * (if r ≤ ‖u‖ then (1 : ℝ≥0∞) else 0) ≤
      ENNReal.ofReal (2 ^ ((N : ℝ) / 2) * Real.exp (-(c * r ^ 2 / 4))) := by
  classical
  have hc2 : 0 < c / 2 := by positivity
  have hpt : ∀ u : EuclideanSpace ℝ (Fin N),
      ENNReal.ofReal (gaussT N c u 0) * (if r ≤ ‖u‖ then (1 : ℝ≥0∞) else 0) ≤
        ENNReal.ofReal (2 ^ ((N : ℝ) / 2) * Real.exp (-(c * r ^ 2 / 4))) *
          ENNReal.ofReal (gaussT N (c / 2) u 0) := by
    intro u
    by_cases hu : r ≤ ‖u‖
    · simp only [hu, ↓reduceIte, mul_one]
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      unfold gaussT
      simp only [sub_zero]
      have h2pi : 0 < 2 * Real.pi := by positivity
      have e1 : (c / (2 * Real.pi)) ^ ((N : ℝ) / 2) =
          2 ^ ((N : ℝ) / 2) * ((c / 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        congr 1; field_simp
      rw [e1]
      -- compare the exponentials
      have hexp : Real.exp (-(c / 2) * ‖u‖ ^ 2) ≤
          Real.exp (-(c * r ^ 2 / 4)) * Real.exp (-(c / 2 / 2) * ‖u‖ ^ 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have : r ^ 2 ≤ ‖u‖ ^ 2 := by nlinarith
        nlinarith
      have hA : 0 ≤ ((c / 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) := by positivity
      have hP : (0 : ℝ) ≤ 2 ^ ((N : ℝ) / 2) := by positivity
      calc 2 ^ ((N : ℝ) / 2) * ((c / 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
            Real.exp (-(c / 2) * ‖u‖ ^ 2)
          ≤ 2 ^ ((N : ℝ) / 2) * ((c / 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) *
            (Real.exp (-(c * r ^ 2 / 4)) * Real.exp (-(c / 2 / 2) * ‖u‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := by ring
    · simp only [hu, ↓reduceIte, mul_zero]
      exact zero_le
  calc _ ≤ ∫⁻ u : EuclideanSpace ℝ (Fin N),
          ENNReal.ofReal (2 ^ ((N : ℝ) / 2) * Real.exp (-(c * r ^ 2 / 4))) *
            ENNReal.ofReal (gaussT N (c / 2) u 0) := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gaussT N hc2, mul_one]

section Prod

variable (N : ℕ) [NeZero N]

/-- The Gaussian density as an extended real. -/
noncomputable def gaussE (c : ℝ) (v : EuclideanSpace ℝ (Fin N)) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussT N c v 0)

/-- The tail indicator `1[r ≤ |v|]`. -/
noncomputable def tailInd (r : ℝ) (v : EuclideanSpace ℝ (Fin N)) : ℝ≥0∞ :=
  open Classical in if r ≤ ‖v‖ then 1 else 0

/-- The tail mass `q = 2^{N/2} e^{-c r²/4}`. -/
noncomputable def tailQ (c r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ ((N : ℝ) / 2) * Real.exp (-(c * r ^ 2 / 4)))

theorem measurable_gaussE (c : ℝ) : Measurable (gaussE N c) := by
  unfold gaussE gaussT
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_norm.comp (measurable_id.sub_const _)).pow_const 2))))

theorem measurable_tailInd (r : ℝ) : Measurable (tailInd N r) := by
  classical
  unfold tailInd
  exact Measurable.ite (measurableSet_le measurable_const measurable_norm) measurable_const
    measurable_const

theorem lintegral_gaussE_tail {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ v, gaussE N c v * tailInd N r v ≤ tailQ N c r := by
  classical
  exact lintegral_gaussT_tail N hc hr

theorem lintegral_gaussE {c : ℝ} (hc : 0 < c) : ∫⁻ v, gaussE N c v = 1 :=
  lintegral_gaussT N hc

/-- The probability that all the blocks of `T` have `|u_y| ≥ r` is at most `q^{#T}`. -/
theorem lintegral_gauss_prod_ind_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) {ι : Type}
    [Fintype ι] [DecidableEq ι] (T : Finset ι) :
    ∫⁻ u : ι → EuclideanSpace ℝ (Fin N),
        (∏ y, gaussE N c (u y)) * ∏ y ∈ T, tailInd N r (u y)
      ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) ≤
      tailQ N c r ^ T.card := by
  classical
  have h1 : ∀ u : ι → EuclideanSpace ℝ (Fin N),
      (∏ y, gaussE N c (u y)) * ∏ y ∈ T, tailInd N r (u y) =
        ∏ y, (gaussE N c (u y) * (if y ∈ T then tailInd N r (u y) else 1)) := by
    intro u
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h1]
  rw [PiTools.lintegral_fintype_prod_eq_prod ι
    (fun y v => gaussE N c v * (if y ∈ T then tailInd N r v else 1))
    (fun y => by
      by_cases hy : y ∈ T
      · simp only [hy, ↓reduceIte]
        exact (measurable_gaussE N c).mul (measurable_tailInd N r)
      · simp only [hy, ↓reduceIte, mul_one]
        exact measurable_gaussE N c)]
  have h2 : ∀ y : ι, ∫⁻ v, gaussE N c v * (if y ∈ T then tailInd N r v else 1) ≤
      if y ∈ T then tailQ N c r else 1 := by
    intro y
    by_cases hy : y ∈ T
    · simp only [hy, ↓reduceIte]
      exact lintegral_gaussE_tail N hc hr
    · simp only [hy, ↓reduceIte, mul_one]
      exact (lintegral_gaussE N hc).le
  calc _ ≤ ∏ y : ι, (if y ∈ T then tailQ N c r else 1) := Finset.prod_le_prod fun y _ => h2 y
    _ = tailQ N c r ^ T.card := by
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **Union bound over disjoint groups of blocks.**  If `Y_c = {y | col y = c}` are the groups of
blocks of the cubes `c ∈ C`, then
`∫ ∏_y g(u_y) ∏_{c ∈ C} ∑_{y ∈ Y_c} 1[|u_y| ≥ r] ≤ ∏_c (#Y_c) · q^{#C}`. -/
theorem lintegral_gauss_union_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [DecidableEq κ] (col : ι → κ) (C : Finset κ) :
    ∫⁻ u : ι → EuclideanSpace ℝ (Fin N),
        (∏ y, gaussE N c (u y)) *
          ∏ b : ↥C, ∑ y ∈ Finset.univ.filter (fun y => col y = b.1), tailInd N r (u y)
      ∂(Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) ≤
      (∏ b : ↥C, ((Finset.univ.filter (fun y => col y = b.1)).card : ℝ≥0∞)) *
        tailQ N c r ^ C.card := by
  classical
  set Yc : ↥C → Finset ι := fun b => Finset.univ.filter (fun y => col y = b.1) with hYc
  have h1 : ∀ u : ι → EuclideanSpace ℝ (Fin N),
      (∏ y, gaussE N c (u y)) * ∏ b : ↥C, ∑ y ∈ Yc b, tailInd N r (u y) =
        ∑ ch ∈ Fintype.piFinset Yc,
          (∏ y, gaussE N c (u y)) * ∏ b : ↥C, tailInd N r (u (ch b)) := by
    intro u
    rw [Finset.prod_univ_sum, Finset.mul_sum]
  rw [lintegral_congr h1, lintegral_finsetSum]
  · calc _ ≤ ∑ ch ∈ Fintype.piFinset Yc, tailQ N c r ^ C.card := by
          refine Finset.sum_le_sum fun ch hch => ?_
          have hcol : ∀ b : ↥C, col (ch b) = b.1 := fun b => by
            have := (Fintype.mem_piFinset.mp hch) b
            simpa [hYc] using this
          have hinj : Function.Injective ch := by
            intro b b' h
            apply Subtype.ext
            rw [← hcol b, ← hcol b', h]
          have e : ∀ u : ι → EuclideanSpace ℝ (Fin N),
              ∏ b : ↥C, tailInd N r (u (ch b)) =
                ∏ y ∈ Finset.univ.image ch, tailInd N r (u y) := by
            intro u
            rw [Finset.prod_image (fun b _ b' _ h => hinj h)]
          simp_rw [e]
          have := lintegral_gauss_prod_ind_le N hc hr (Finset.univ.image ch)
          rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ,
            Fintype.card_coe] at this
      _ = _ := by
          rw [Finset.sum_const, Fintype.card_piFinset, nsmul_eq_mul]
          push_cast
          rfl
  · intro ch _
    have hm : Measurable (fun u : ι → EuclideanSpace ℝ (Fin N) =>
        (∏ y, gaussE N c (u y)) * ∏ b : ↥C, tailInd N r (u (ch b))) := by
      refine Measurable.mul ?_ ?_
      · exact Finset.measurable_prod _ fun y _ =>
          (measurable_gaussE N c).comp (measurable_pi_apply y)
      · exact Finset.measurable_prod _ fun b _ =>
          (measurable_tailInd N r).comp (measurable_pi_apply (ch b))
    exact hm

end Prod

end Balaban.LargeField
