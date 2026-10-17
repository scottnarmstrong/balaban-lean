/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.GaussianChangeGeneral
public import Balaban.LargeField.Base.KF0CutoffSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian tail of the large-field blocks of the last integral (W888)

Leaf T-1 of `notes/phase1/FINALPHYS3.md` section 6.  The reference measure of the last integral is
the standard Gaussian `pdGaussian ι W` on the unit variable `ψ` (P4 (6.6)).  It is a product over
the sites, so the weight of a large-field set does not depend on the covariance.

* `pdGaussian_tail_all_le`: for a finite set `Z` of sites,
  `γ{ψ | ∀ x ∈ Z, ρ < ‖ψ x‖} ≤ (2^{dim W/2} e^{-ρ²/4})^{|Z|}`.
* `pdGaussian_tail_exists_le`: for a finite set `B` of sites (one block),
  `γ{ψ | ∃ x ∈ B, ρ < ‖ψ x‖} ≤ |B| 2^{dim W/2} e^{-ρ²/4}`.
* `pdGaussian_tail_compl_box_le`: the complement of the box `{∀ y, ‖ψ y‖ ≤ ρ}` has measure at
  most `|ι| 2^{dim W/2} e^{-ρ²/4}`.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Green

open Balaban.LargeField

section Tail

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

/-- The one-site weight used in the tail bound: `exp(-¼‖u‖²)` on `Z`, `exp(-½‖u‖²)` elsewhere. -/
private noncomputable abbrev tailW (Z : Finset ι) (y : ι) : ℝ := if y ∈ Z then 1 / 4 else 1 / 2

omit [Fintype ι] [SecondCountableTopology W] in
private theorem tail_integral_factor (Z : Finset ι) (y : ι) :
    ∫⁻ u : W, ENNReal.ofReal (Real.exp (-(tailW Z y) * ‖u‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ ((Module.finrank ℝ W : ℝ) / 2) *
        (if y ∈ Z then (2 : ℝ) ^ ((Module.finrank ℝ W : ℝ) / 2) else 1)) := by
  have hb : 0 < tailW Z y := by unfold tailW; split_ifs <;> norm_num
  have h := lintegral_exp_neg_mul_sq_norm (E := W) hb (c := 1) zero_le_one
  simp only [one_mul] at h
  rw [h]
  congr 1
  unfold tailW
  split_ifs with hy
  · rw [show Real.pi / (1 / 4) = 2 * (2 * Real.pi) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
    ring
  · rw [show Real.pi / (1 / 2) = 2 * Real.pi by ring]
    ring

/-- **Tail of a set of sites** (leaf T-1).  For `ρ ≥ 0` and a finite set `Z` of sites,
`γ{ψ | ‖ψ x‖ > ρ for all x ∈ Z} ≤ (2^{dim W/2} e^{-ρ²/4})^{|Z|}`, `γ = pdGaussian ι W`. -/
theorem pdGaussian_tail_all_le (Z : Finset ι) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    pdGaussian ι W {ψ | ∀ x ∈ Z, ρ < ‖ψ x‖} ≤
      ENNReal.ofReal ((2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)) ^ Z.card) := by
  have hms : MeasurableSet {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖} := by
    have : {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖} = ⋂ x ∈ Z, {ψ : ι → W | ρ < ‖ψ x‖} := by
      ext ψ; simp
    rw [this]
    exact Finset.measurableSet_biInter _ fun x _ =>
      measurableSet_lt measurable_const (measurable_norm.comp (measurable_pi_apply x))
  unfold pdGaussian
  rw [withDensity_apply _ hms]
  set k : ℝ := (Module.finrank ℝ W : ℝ) / 2 with hk
  set c : ℝ := (2 * Real.pi) ^ (-(pdDim ι W : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hgm : ∀ y : ι, Measurable fun u : W => ENNReal.ofReal (Real.exp (-(tailW Z y) * ‖u‖ ^ 2)) :=
    fun y => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop))
  have hpt : ∀ ψ ∈ {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖},
      ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) ≤
        ENNReal.ofReal (c * Real.exp (-ρ ^ 2 / 4) ^ Z.card) *
          ∏ y, ENNReal.ofReal (Real.exp (-(tailW Z y) * ‖ψ y‖ ^ 2)) := by
    intro ψ hψ
    rw [← ENNReal.ofReal_prod_of_nonneg (fun y _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_sum, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc0
    have h1 : ∑ y, (-(tailW Z y) * ‖ψ y‖ ^ 2) =
        -(1 / 2) * ∑ x, ‖ψ x‖ ^ 2 + ∑ y ∈ Z, (1 / 4) * ‖ψ y‖ ^ 2 := by
      have : ∀ y, -(tailW Z y) * ‖ψ y‖ ^ 2 =
          -(1 / 2) * ‖ψ y‖ ^ 2 + (if y ∈ Z then (1 / 4) * ‖ψ y‖ ^ 2 else 0) := by
        intro y; unfold tailW; split_ifs <;> ring
      rw [Finset.sum_congr rfl fun y _ => this y, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h2 : ∑ y ∈ Z, ρ ^ 2 / 4 ≤ ∑ y ∈ Z, (1 / 4) * ‖ψ y‖ ^ 2 :=
      Finset.sum_le_sum fun y hy => by
        have := pow_le_pow_left₀ hρ (hψ y hy).le 2
        linarith
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    rw [h1]
    nlinarith
  calc ∫⁻ ψ in {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖}, ENNReal.ofReal (c * Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2))
      ≤ ∫⁻ ψ in {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖}, ENNReal.ofReal (c * Real.exp (-ρ ^ 2 / 4) ^ Z.card) *
          ∏ y, ENNReal.ofReal (Real.exp (-(tailW Z y) * ‖ψ y‖ ^ 2)) :=
        setLIntegral_mono' hms hpt
    _ ≤ ∫⁻ ψ : ι → W, ENNReal.ofReal (c * Real.exp (-ρ ^ 2 / 4) ^ Z.card) *
          ∏ y, ENNReal.ofReal (Real.exp (-(tailW Z y) * ‖ψ y‖ ^ 2)) ∂(pdVol ι W) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (c * Real.exp (-ρ ^ 2 / 4) ^ Z.card) *
          ∏ y, ENNReal.ofReal ((2 * Real.pi) ^ k * (if y ∈ Z then (2 : ℝ) ^ k else 1)) := by
        rw [lintegral_const_mul]
        · rw [LargeField.PiTools.lintegral_fintype_prod_eq_prod ι
            (fun y u => ENNReal.ofReal (Real.exp (-(tailW Z y) * ‖u‖ ^ 2))) hgm]
          simp_rw [tail_integral_factor]
          rfl
        · exact Finset.measurable_prod _ fun y _ => (hgm y).comp (measurable_pi_apply y)
    _ = ENNReal.ofReal ((2 ^ k * Real.exp (-ρ ^ 2 / 4)) ^ Z.card) := by
        rw [← ENNReal.ofReal_prod_of_nonneg (fun y _ => by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite, Finset.prod_const,
          Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.card_univ, mul_pow]
        have hcc : c = ((2 * Real.pi) ^ k) ⁻¹ ^ Fintype.card ι := by
          rw [hc, inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
            ← Real.rpow_neg (by positivity)]
          congr 1
          simp only [pdDim, hk]
          push_cast
          ring
        have hne : ((2 * Real.pi) ^ k) ^ Fintype.card ι ≠ 0 := by positivity
        rw [hcc, inv_pow]
        field_simp

/-- **Tail of one block** (leaf T-1).  `γ{ψ | ∃ x ∈ B, ‖ψ x‖ > ρ} ≤ |B| 2^{dim W/2} e^{-ρ²/4}`. -/
theorem pdGaussian_tail_exists_le (B : Finset ι) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    pdGaussian ι W {ψ | ∃ x ∈ B, ρ < ‖ψ x‖} ≤
      ENNReal.ofReal (B.card * (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by
  have hset : {ψ : ι → W | ∃ x ∈ B, ρ < ‖ψ x‖} = ⋃ x ∈ B, {ψ : ι → W | ∀ y ∈ ({x} : Finset ι), ρ < ‖ψ y‖} := by
    ext ψ; simp
  rw [hset]
  calc pdGaussian ι W (⋃ x ∈ B, {ψ : ι → W | ∀ y ∈ ({x} : Finset ι), ρ < ‖ψ y‖})
      ≤ ∑ x ∈ B, pdGaussian ι W {ψ : ι → W | ∀ y ∈ ({x} : Finset ι), ρ < ‖ψ y‖} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ B, ENNReal.ofReal (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)) :=
        Finset.sum_le_sum fun x _ => by
          simpa using pdGaussian_tail_all_le (ι := ι) (W := W) {x} hρ
    _ = ENNReal.ofReal (B.card * (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg B.card),
          ENNReal.ofReal_natCast]

/-- The complement of the box `{∀ y, ‖ψ y‖ ≤ ρ}` has Gaussian measure at most
`|ι| 2^{dim W/2} e^{-ρ²/4}`. -/
theorem pdGaussian_tail_compl_box_le {ρ : ℝ} (hρ : 0 ≤ ρ) :
    pdGaussian ι W {ψ | ∀ y, ‖ψ y‖ ≤ ρ}ᶜ ≤
      ENNReal.ofReal (Fintype.card ι *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by
  have h := pdGaussian_tail_exists_le (ι := ι) (W := W) Finset.univ hρ
  have hset : {ψ : ι → W | ∀ y, ‖ψ y‖ ≤ ρ}ᶜ = {ψ | ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖} := by
    ext ψ; simp
  rw [hset]
  simpa using h

/-- **The activity bound of one large-field set** (leaf T-1): a function bounded by `B` on the set
`{ψ | ‖ψ x‖ > ρ for all x ∈ Z}` has set integral of norm at most
`B (2^{dim W/2} e^{-ρ²/4})^{|Z|}`. -/
theorem norm_setIntegral_tail_all_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : Finset ι) {ρ : ℝ} (hρ : 0 ≤ ρ) {F : (ι → W) → E} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ ψ ∈ {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖}, ‖F ψ‖ ≤ B) :
    ‖∫ ψ in {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖}, F ψ ∂(pdGaussian ι W)‖ ≤
      B * (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)) ^ Z.card := by
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := pdGaussian ι W)
    (s := {ψ : ι → W | ∀ x ∈ Z, ρ < ‖ψ x‖}) (C := B)
    ((measure_mono (Set.subset_univ _)).trans_lt (by rw [pdGaussian_univ]; exact ENNReal.one_lt_top)) hF
  refine h1.trans ?_
  rw [Measure.real]
  refine mul_le_mul_of_nonneg_left ?_ hB
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (pdGaussian_tail_all_le (ι := ι) (W := W) Z hρ)
  rwa [ENNReal.toReal_ofReal (by positivity)] at this

end Tail

end Balaban.Green
