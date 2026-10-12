/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gaussian bounds for the truncated density (Lemma III.8.2)

On `EuclideanSpace ℝ (Z × Fin N)` (the variable `ψ_k↾Z₀`, `Z` the blocks of `Z₀`), let
`A` be squeezed between `A₀ + (g/2)‖y‖²` and `A₀ + ‖y‖²` on the region `siteBall r` (`|y(z)| < r` for every block `z`).
Then `∫_{siteBall r} exp(-β A)` lies between `e^{-βA₀} (2/√(Nβ))^{|Z|N} e^{-|Z|}` and
`e^{-βA₀} (2π/(βg))^{|Z|N/2}` (`zeroDensity_bounds`), provided `r² ≥ 1/β`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Real

namespace Balaban.LargeField
variable {ι : Type*} [Fintype ι]

theorem integrable_gaussNorm (b : ℝ) (hb : 0 < b) :
    Integrable (fun y : EuclideanSpace ℝ ι => Real.exp (-b * ‖y‖ ^ 2)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ ι)
    (b := (b : ℂ)) (by simpa using hb) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem integral_gaussNorm (b : ℝ) (hb : 0 < b) :
    ∫ y : EuclideanSpace ℝ ι, Real.exp (-b * ‖y‖ ^ 2) = (π / b) ^ ((Fintype.card ι : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp

/-- the gaussCube -/
def gaussCube (s : ℝ) : Set (EuclideanSpace ℝ ι) := {y | ∀ j, |y j| < s}

theorem volume_gaussCube {s : ℝ} (hs : 0 < s) :
    (volume (gaussCube (ι := ι) s)).toReal = (2 * s) ^ Fintype.card ι := by
  have : gaussCube (ι := ι) s = (WithLp.ofLp) ⁻¹' (Set.univ.pi fun _ : ι => Set.Ioo (-s) s) := by
    ext y; simp [gaussCube, abs_lt]
  rw [this, (PiLp.volume_preserving_ofLp ι).measure_preimage (by
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet)]
  rw [volume_pi_Ioo_toReal (by intro i; simp; linarith)]
  simp [two_mul]

theorem measurableSet_gaussCube (s : ℝ) : MeasurableSet (gaussCube (ι := ι) s) := by
  have : gaussCube (ι := ι) s = ⋂ j, {y : EuclideanSpace ℝ ι | |y j| < s} := by ext y; simp [gaussCube]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_lt (by fun_prop) measurable_const

theorem sq_norm_le_gaussCube {s : ℝ} {y : EuclideanSpace ℝ ι} (hy : y ∈ gaussCube s) : ‖y‖ ^ 2 ≤ Fintype.card ι * s ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : ι, s ^ 2 := Finset.sum_le_sum fun i _ => by
        have := hy i
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this.le 2
    _ = _ := by simp

section Ball
variable {Z : Type*} [Fintype Z] {N : ℕ}

/-- `{y | ∀ z, ∑_i y(z,i)² < r²}`. -/
def siteBall (r : ℝ) : Set (EuclideanSpace ℝ (Z × Fin N)) := {y | ∀ z, ∑ i, y (z, i) ^ 2 < r ^ 2}

theorem isOpen_siteBall (r : ℝ) : IsOpen (siteBall (Z := Z) (N := N) r) := by
  have : siteBall (Z := Z) (N := N) r = ⋂ z, {y : EuclideanSpace ℝ (Z × Fin N) | ∑ i, y (z, i) ^ 2 < r ^ 2} := by
    ext y; simp [siteBall]
  rw [this]
  refine isOpen_iInter_of_finite fun z => isOpen_lt ?_ continuous_const
  fun_prop

theorem star_siteBall {r : ℝ} {y : EuclideanSpace ℝ (Z × Fin N)} (hy : y ∈ siteBall r) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • y ∈ siteBall r := by
  intro z
  have : ∑ i, (t • y) (z, i) ^ 2 = t ^ 2 * ∑ i, y (z, i) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; simp; ring
  rw [this]
  have h1 : t ^ 2 ≤ 1 := by nlinarith
  have h2 : 0 ≤ ∑ i, y (z, i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [hy z]

theorem gaussCube_subset_siteBall [NeZero N] {β r : ℝ} (hβ : 0 < β) (hr : (1 / β) ≤ r ^ 2) :
    gaussCube (ι := Z × Fin N) (1 / Real.sqrt (N * β)) ⊆ siteBall r := by
  intro y hy z
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs2 : (1 / Real.sqrt (N * β)) ^ 2 = 1 / (N * β) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; simp
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
  calc ∑ i, y (z, i) ^ 2 < ∑ _i : Fin N, (1 / Real.sqrt (N * β)) ^ 2 := by
        refine Finset.sum_lt_sum_of_nonempty hne fun i _ => ?_
        have := hy (z, i)
        rw [← sq_abs]
        exact pow_lt_pow_left₀ this (abs_nonneg _) (by norm_num)
    _ = 1 / β := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hs2, nsmul_eq_mul]; field_simp
    _ ≤ r ^ 2 := hr


/-- **Two-sided density bounds** for the truncated exponential of a function squeezed between quadratics. -/
theorem zeroDensity_bounds [NeZero N] {A : EuclideanSpace ℝ (Z × Fin N) → ℝ} {A0 β g r : ℝ} (hβ : 0 < β)
    (hg : 0 < g) (hr : 1 / β ≤ r ^ 2) (hcont : ContinuousOn A (siteBall r))
    (hlow : ∀ y ∈ siteBall (Z := Z) (N := N) r, A0 + g / 2 * ‖y‖ ^ 2 ≤ A y)
    (hup : ∀ y ∈ siteBall (Z := Z) (N := N) r, A y ≤ A0 + ‖y‖ ^ 2) :
    Real.exp (-β * A0) * (2 / Real.sqrt (N * β)) ^ (Fintype.card Z * N) * Real.exp (-(Fintype.card Z : ℝ)) ≤
        ∫ y, (siteBall r).indicator (fun y => Real.exp (-β * A y)) y ∧
      ∫ y, (siteBall r).indicator (fun y => Real.exp (-β * A y)) y ≤
        Real.exp (-β * A0) * (π / (β * g / 2)) ^ ((Fintype.card Z * N : ℝ) / 2) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcardι : Fintype.card (Z × Fin N) = Fintype.card Z * N := by simp
  have hmeas : MeasurableSet (siteBall (Z := Z) (N := N) r) := (isOpen_siteBall r).measurableSet
  have hasm : AEStronglyMeasurable ((siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y)))
      volume := by
    rw [aestronglyMeasurable_indicator_iff hmeas]
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hcont)).aestronglyMeasurable hmeas
  -- upper pointwise bound
  have hb : 0 < β * g / 2 := by positivity
  have hpt : ∀ y, (siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y)) y ≤
      Real.exp (-β * A0) * Real.exp (-(β * g / 2) * ‖y‖ ^ 2) := by
    intro y
    by_cases hy : y ∈ siteBall (Z := Z) (N := N) r
    · rw [Set.indicator_of_mem hy, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := hlow y hy
      nlinarith
    · rw [Set.indicator_of_notMem hy]; positivity
  have hnn : ∀ y, 0 ≤ (siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y)) y := fun y =>
    Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) y
  have hint : Integrable ((siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y))) volume :=
    ((integrable_gaussNorm (ι := Z × Fin N) (β * g / 2) hb).const_mul (Real.exp (-β * A0))).mono' hasm
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]; exact hpt y)
  refine ⟨?_, ?_⟩
  · set s : ℝ := 1 / Real.sqrt (N * β) with hs
    have hspos : 0 < s := by positivity
    have hcsub := gaussCube_subset_siteBall (Z := Z) (N := N) (r := r) hβ hr
    have hs2 : s ^ 2 = 1 / (N * β) := by
      rw [hs, div_pow, Real.sq_sqrt (by positivity)]; simp
    set c : ℝ := Real.exp (-β * A0 - (Fintype.card Z : ℝ)) with hc
    have hpt2 : ∀ y, (gaussCube (ι := Z × Fin N) s).indicator (fun _ => c) y ≤
        (siteBall (Z := Z) (N := N) r).indicator (fun y => Real.exp (-β * A y)) y := by
      intro y
      by_cases hy : y ∈ gaussCube (ι := Z × Fin N) s
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hcsub hy)]
        apply Real.exp_le_exp.2
        have h1 := hup y (hcsub hy)
        have h2 := sq_norm_le_gaussCube hy
        rw [hcardι, hs2] at h2
        have h3 : (Fintype.card Z * N : ℝ) * (1 / (N * β)) = Fintype.card Z / β := by
          field_simp
        have h4 : β * ‖y‖ ^ 2 ≤ Fintype.card Z := by
          push_cast at h2
          have : β * ‖y‖ ^ 2 ≤ β * ((Fintype.card Z * N : ℝ) * (1 / (N * β))) :=
            mul_le_mul_of_nonneg_left h2 hβ.le
          rw [h3] at this
          calc β * ‖y‖ ^ 2 ≤ β * (Fintype.card Z / β) := this
            _ = Fintype.card Z := by field_simp
        nlinarith
      · rw [Set.indicator_of_notMem hy]; exact hnn y
    have hmc : MeasurableSet (gaussCube (ι := Z × Fin N) s) := measurableSet_gaussCube s
    calc Real.exp (-β * A0) * (2 / Real.sqrt (N * β)) ^ (Fintype.card Z * N) * Real.exp (-(Fintype.card Z : ℝ))
        = c * (2 * s) ^ Fintype.card (Z × Fin N) := by
          rw [hcardι, hc, sub_eq_add_neg, Real.exp_add, hs]
          have : 2 / Real.sqrt (N * β) = 2 * (1 / Real.sqrt (N * β)) := by ring
          rw [this]; ring
      _ = ∫ y, (gaussCube (ι := Z × Fin N) s).indicator (fun _ => c) y := by
          rw [integral_indicator_const _ hmc, Measure.real, volume_gaussCube hspos]
          simp [mul_comm]
      _ ≤ _ := integral_mono ((integrable_indicator_iff hmc).2 (integrableOn_const (by
          intro h
          have h1 := volume_gaussCube (ι := Z × Fin N) hspos
          rw [h, ENNReal.toReal_top] at h1
          have h2 : 0 < (2 * s) ^ Fintype.card (Z × Fin N) := by positivity
          linarith))) hint hpt2
  · calc ∫ y, (siteBall r).indicator (fun y => Real.exp (-β * A y)) y
        ≤ ∫ y : EuclideanSpace ℝ (Z × Fin N), Real.exp (-β * A0) * Real.exp (-(β * g / 2) * ‖y‖ ^ 2) :=
          integral_mono hint ((integrable_gaussNorm (ι := Z × Fin N) (β * g / 2) hb).const_mul _) hpt
      _ = _ := by
          rw [integral_const_mul, integral_gaussNorm _ hb, hcardι]; push_cast; rfl

end Ball

end Balaban.LargeField
