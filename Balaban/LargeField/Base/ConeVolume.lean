/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Volume of a cone over a subset of the unit ball (a step of `toSphere_eq_graph`)

Let `K` be a finite-dimensional real inner product space.  In the coordinates `(η, a)` of
`K × ℝ` (`η ∈ K`, height `a` along a fixed unit vector `e ⊥ K`), the cone over the graph points
`√(1 - |ξ|²) e + ξ`, `ξ ∈ T ⊆ K`, is `coneSet T`.  We prove

`vol (coneSet T) = (dim K + 1)⁻¹ ∫_T (1 - |ξ|²)^{-1/2} dξ`

by the substitution `ρ = √(a² + |η|²)` (one-variable change of variables), Tonelli, and the
homogeneity of Haar measure `η = ρ ξ`.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Balaban.LargeField.SphereChart

/-- Change of variables `ρ = √(a² + n²)` on `a > 0`. -/
theorem lintegral_sqrt_sq_add (n : ℝ) (hn : 0 ≤ n) {B : Set ℝ} (hB : MeasurableSet B) :
    volume {a : ℝ | 0 < a ∧ Real.sqrt (a ^ 2 + n ^ 2) ∈ B} =
      ∫⁻ ρ in B ∩ Ioi n, ENNReal.ofReal (ρ / Real.sqrt (ρ ^ 2 - n ^ 2)) := by
  set f : ℝ → ℝ := fun a => Real.sqrt (a ^ 2 + n ^ 2) with hf
  set S : Set ℝ := {a : ℝ | 0 < a ∧ f a ∈ B} with hS
  have hfc : Continuous f := by fun_prop
  have hSm : MeasurableSet S := by
    have : S = Ioi 0 ∩ f ⁻¹' B := by ext; simp [hS]
    rw [this]; exact measurableSet_Ioi.inter (hB.preimage hfc.measurable)
  have hfpos : ∀ a, 0 < a → 0 < f a := fun a ha => Real.sqrt_pos.2 (by positivity)
  have hsq : ∀ a, 0 < a → Real.sqrt ((f a) ^ 2 - n ^ 2) = a := by
    intro a ha
    simp only [hf]
    rw [Real.sq_sqrt (by positivity)]
    rw [show a ^ 2 + n ^ 2 - n ^ 2 = a ^ 2 by ring]
    exact Real.sqrt_sq ha.le
  have hd : ∀ a ∈ S, HasDerivWithinAt f (a / f a) S a := by
    intro a ha
    have ha0 : 0 < a := ha.1
    have h1 : HasDerivAt (fun a : ℝ => a ^ 2 + n ^ 2) (2 * a) a := by
      simpa using (hasDerivAt_pow 2 a).add_const (n ^ 2)
    have := h1.sqrt (by positivity)
    have e : 2 * a / (2 * Real.sqrt (a ^ 2 + n ^ 2)) = a / f a := by
      simp only [hf]; field_simp
    rw [e] at this
    exact this.hasDerivWithinAt
  have hinj : InjOn f S := by
    intro a ha b hb h
    have ha0 := ha.1
    have hb0 := hb.1
    have h2 : a ^ 2 + n ^ 2 = b ^ 2 + n ^ 2 := by
      have := congrArg (· ^ 2) h
      simpa [hf, Real.sq_sqrt, (by positivity : (0:ℝ) ≤ a ^ 2 + n ^ 2),
        (by positivity : (0:ℝ) ≤ b ^ 2 + n ^ 2)] using this
    nlinarith
  have himg : f '' S = B ∩ Ioi n := by
    ext ρ
    constructor
    · rintro ⟨a, ⟨ha0, haB⟩, rfl⟩
      refine ⟨haB, ?_⟩
      show n < f a
      simp only [hf]
      apply Real.lt_sqrt_of_sq_lt
      nlinarith
    · rintro ⟨hρB, hρn'⟩
      have hρn : n < ρ := hρn'
      have hρ0 : 0 < ρ := lt_of_le_of_lt hn hρn
      refine ⟨Real.sqrt (ρ ^ 2 - n ^ 2), ⟨?_, ?_⟩, ?_⟩
      · exact Real.sqrt_pos.2 (by nlinarith)
      · have : f (Real.sqrt (ρ ^ 2 - n ^ 2)) = ρ := by
          simp only [hf]
          rw [Real.sq_sqrt (by nlinarith), show ρ ^ 2 - n ^ 2 + n ^ 2 = ρ ^ 2 by ring]
          exact Real.sqrt_sq hρ0.le
        rw [this]; exact hρB
      · simp only [hf]
        rw [Real.sq_sqrt (by nlinarith), show ρ ^ 2 - n ^ 2 + n ^ 2 = ρ ^ 2 by ring]
        exact Real.sqrt_sq hρ0.le
  have key := lintegral_image_eq_lintegral_abs_deriv_mul hSm hd hinj
    (fun ρ => ENNReal.ofReal (ρ / Real.sqrt (ρ ^ 2 - n ^ 2)))
  rw [himg] at key
  rw [key]
  have : ∀ a ∈ S, ENNReal.ofReal |a / f a| * ENNReal.ofReal (f a / Real.sqrt ((f a) ^ 2 - n ^ 2)) = 1 := by
    intro a ha
    have ha0 : 0 < a := ha.1
    have hp := hfpos a ha0
    rw [hsq a ha0, ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by positivity)]
    rw [show a / f a * (f a / a) = 1 by field_simp]
    simp
  rw [setLIntegral_congr_fun hSm this]
  simp


/-- Homogeneity of Haar measure. -/
theorem lintegral_eq_pow_mul_lintegral_smul {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [MeasurableSpace K] [BorelSpace K] [FiniteDimensional ℝ K] (μ : Measure K) [μ.IsAddHaarMeasure]
    {ρ : ℝ} (hρ : 0 < ρ) {H : K → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ η, H η ∂μ = ENNReal.ofReal (ρ ^ Module.finrank ℝ K) * ∫⁻ ξ, H (ρ • ξ) ∂μ := by
  have h1 := lintegral_map hH (measurable_const_smul ρ) (μ := μ)
  rw [Measure.map_addHaar_smul μ hρ.ne', lintegral_smul_measure] at h1
  rw [← h1, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have : ρ ^ Module.finrank ℝ K * |(ρ ^ Module.finrank ℝ K)⁻¹| = 1 := by
    rw [abs_of_pos (by positivity)]; field_simp
  rw [this]; simp


section Cone

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K]

/-- The cone over a subset `T` of the unit ball of `K`, in the coordinates `(η, a)` of
`K × ℝ ≅ K ⊕ ℝ e`. -/
def coneSet (T : Set K) : Set (K × ℝ) :=
  {p | 0 < p.2 ∧ Real.sqrt (p.2 ^ 2 + ‖p.1‖ ^ 2) < 1 ∧
    (Real.sqrt (p.2 ^ 2 + ‖p.1‖ ^ 2))⁻¹ • p.1 ∈ T}

/-- Measurability of the cone. -/
theorem measurableSet_coneSet {T : Set K} (hT : MeasurableSet T) : MeasurableSet (coneSet T) := by
  have h1 : Measurable fun p : K × ℝ => Real.sqrt (p.2 ^ 2 + ‖p.1‖ ^ 2) := by fun_prop
  refine (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt h1 measurable_const).inter (hT.preimage (h1.inv.smul measurable_fst)))

/-- The integrand of the cone volume after the substitution `ρ = √(a² + |η|²)`. -/
noncomputable def coneIntegrand (T : Set K) (q : K × ℝ) : ℝ≥0∞ :=
  Set.indicator {q : K × ℝ | q.2 < 1 ∧ q.2⁻¹ • q.1 ∈ T ∧ ‖q.1‖ < q.2}
    (fun q => ENNReal.ofReal (q.2 / Real.sqrt (q.2 ^ 2 - ‖q.1‖ ^ 2))) q

/-- Measurability of the cone integrand. -/
theorem measurable_coneIntegrand {T : Set K} (hT : MeasurableSet T) :
    Measurable (coneIntegrand T) := by
  refine Measurable.indicator ?_ ?_
  · exact ENNReal.measurable_ofReal.comp (by fun_prop)
  · exact (measurableSet_lt measurable_snd measurable_const).inter
      ((hT.preimage (measurable_snd.inv.smul measurable_fst)).inter
        (measurableSet_lt measurable_fst.norm measurable_snd))

/-- The cone volume as an iterated integral. -/
theorem volume_coneSet {T : Set K} (hT : MeasurableSet T) :
    (volume : Measure (K × ℝ)) (coneSet T) =
      ∫⁻ η : K, ∫⁻ ρ : ℝ, coneIntegrand T (η, ρ) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_coneSet hT)]
  refine lintegral_congr fun η => ?_
  have hB : MeasurableSet {ρ : ℝ | ρ < 1 ∧ ρ⁻¹ • η ∈ T} :=
    (measurableSet_lt measurable_id measurable_const).inter
      (hT.preimage (measurable_inv.smul_const η))
  have e1 : Prod.mk η ⁻¹' coneSet T =
      {a : ℝ | 0 < a ∧ Real.sqrt (a ^ 2 + ‖η‖ ^ 2) ∈ {ρ : ℝ | ρ < 1 ∧ ρ⁻¹ • η ∈ T}} := by
    ext a; simp [coneSet]
  rw [e1, lintegral_sqrt_sq_add ‖η‖ (norm_nonneg η) hB]
  have e2 : {ρ : ℝ | ρ < 1 ∧ ρ⁻¹ • η ∈ T} ∩ Ioi ‖η‖ =
      {ρ : ℝ | (η, ρ) ∈ {q : K × ℝ | q.2 < 1 ∧ q.2⁻¹ • q.1 ∈ T ∧ ‖q.1‖ < q.2}} := by
    ext ρ; simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi]; tauto
  rw [e2, ← lintegral_indicator]
  · rfl
  · exact (measurable_prodMk_left (x := η)) (((measurableSet_lt measurable_snd measurable_const).inter
      ((hT.preimage (measurable_snd.inv.smul measurable_fst)).inter
        (measurableSet_lt measurable_fst.norm measurable_snd))))


/-- `∫_0^1 ρ^m = 1/(m+1)`. -/
theorem lintegral_Ioo_pow (m : ℕ) :
    ∫⁻ ρ in Ioo (0 : ℝ) 1, ENNReal.ofReal (ρ ^ m) = ENNReal.ofReal (1 / (m + 1)) := by
  have hint : IntegrableOn (fun ρ : ℝ => ρ ^ m) (Ioo (0 : ℝ) 1) :=
    (continuous_pow m).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun ρ hρ => pow_nonneg hρ.1.le m))]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, integral_pow]
  simp

/-- The volume of the cone over `T` is `(dim K + 1)⁻¹ ∫_T (1 - |ξ|²)^{-1/2}`. -/
theorem volume_coneSet_eq {T : Set K} (hT : MeasurableSet T) :
    (volume : Measure (K × ℝ)) (coneSet T) =
      ENNReal.ofReal (1 / ((Module.finrank ℝ K : ℝ) + 1)) *
        ∫⁻ ξ in T ∩ ball 0 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) := by
  rw [volume_coneSet hT, lintegral_lintegral_swap (f := fun η ρ => coneIntegrand T (η, ρ))
    (measurable_coneIntegrand hT).aemeasurable]
  set W := ∫⁻ ξ in T ∩ ball 0 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖ξ‖ ^ 2)) with hW
  have hpt : ∀ ρ : ℝ, ∫⁻ η : K, coneIntegrand T (η, ρ) =
      (Ioo (0 : ℝ) 1).indicator (fun ρ => ENNReal.ofReal (ρ ^ Module.finrank ℝ K) * W) ρ := by
    intro ρ
    by_cases hρ : ρ ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hρ]
      have hH : Measurable fun η : K => coneIntegrand T (η, ρ) :=
        (measurable_coneIntegrand hT).comp measurable_prodMk_right
      rw [lintegral_eq_pow_mul_lintegral_smul volume hρ.1 hH]
      congr 1
      rw [hW, ← lintegral_indicator ((hT.inter measurableSet_ball))]
      refine lintegral_congr fun ξ => ?_
      by_cases hξ : ξ ∈ T ∩ ball 0 1
      · rw [indicator_of_mem hξ]
        have hξ1 : ‖ξ‖ < 1 := by simpa using hξ.2
        have hmem : (ρ • ξ, ρ) ∈ {q : K × ℝ | q.2 < 1 ∧ q.2⁻¹ • q.1 ∈ T ∧ ‖q.1‖ < q.2} := by
          refine ⟨hρ.2, ?_, ?_⟩
          · simpa [smul_smul, inv_mul_cancel₀ hρ.1.ne'] using hξ.1
          · rw [norm_smul, Real.norm_of_nonneg hρ.1.le]; nlinarith [hρ.1]
        unfold coneIntegrand
        rw [indicator_of_mem hmem]
        congr 1
        simp only
        rw [norm_smul, Real.norm_of_nonneg hρ.1.le,
          show ρ ^ 2 - (ρ * ‖ξ‖) ^ 2 = ρ ^ 2 * (1 - ‖ξ‖ ^ 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hρ.1.le]
        have : 0 < Real.sqrt (1 - ‖ξ‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [norm_nonneg ξ])
        have hρ0 := hρ.1.ne'
        field_simp
      · rw [indicator_of_notMem hξ]
        have hn : (ρ • ξ, ρ) ∉ {q : K × ℝ | q.2 < 1 ∧ q.2⁻¹ • q.1 ∈ T ∧ ‖q.1‖ < q.2} := by
          rintro ⟨-, h2, h3⟩
          apply hξ
          refine ⟨by simpa [smul_smul, inv_mul_cancel₀ hρ.1.ne'] using h2, ?_⟩
          rw [norm_smul, Real.norm_of_nonneg hρ.1.le] at h3
          simp only [mem_ball, dist_zero_right]
          nlinarith [hρ.1]
        unfold coneIntegrand
        rw [indicator_of_notMem hn]
    · rw [indicator_of_notMem hρ]
      have h0 : ∀ η : K, coneIntegrand T (η, ρ) = 0 := by
        intro η
        have hn : (η, ρ) ∉ {q : K × ℝ | q.2 < 1 ∧ q.2⁻¹ • q.1 ∈ T ∧ ‖q.1‖ < q.2} := by
          rintro ⟨h1, -, h3⟩
          exact hρ ⟨lt_of_le_of_lt (norm_nonneg _) h3, h1⟩
        unfold coneIntegrand
        rw [indicator_of_notMem hn]
      simp [h0]
  simp_rw [hpt]
  rw [lintegral_indicator measurableSet_Ioo, lintegral_mul_const _ (by fun_prop), lintegral_Ioo_pow]

end Cone

end Balaban.LargeField.SphereChart
