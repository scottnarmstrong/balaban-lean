/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLargeGas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Boundary and normalized heavy bounds for the last integral

The boundary lemma converts a proved modular-size estimate to the cardinality hypothesis of
the final gas. The normalization lemma pays for dividing by the empty-block probability.
Neither lemma asserts that the physical boundary differences or heavy operators have already
been identified with these inputs.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory

namespace Balaban.Green

/-- A fixed local interaction loses exactly the terms whose support meets the selected bad set.
This is the algebraic part of the new boundary localization, before any hole-dependent
background differences are included. -/
theorem fixed_local_boundary_difference {B : Type*} [Fintype B]
    (f : Finset B → ℂ) (Z : Finset B) :
    (∑ T : Finset B, if Disjoint T Z then f T else 0) -
      (∑ T : Finset B, f T) =
      ∑ T : Finset B, if Disjoint T Z then 0 else -f T := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> ring

/-- An exponential bound in modular size gives the final gas's cardinality decay. The size
comparison is the precise transport premise needed when the physical and final block carriers
have been identified. -/
theorem boundary_card_bound_of_size_comparison
    {B Yt : Type*} [Fintype Yt] (cy : Yt → Finset B) (g : Yt → ℂ)
    (D : Finset B → ℝ) {C fac rate : ℝ}
    (hC : 0 < C) (hfac : 0 ≤ fac) (hrate : 0 ≤ rate)
    (hsize : ∀ y, ((cy y).card : ℝ) ≤ C * (1 + D (cy y)))
    (hmod : ∀ y, ‖g y‖ ≤ fac * Real.exp (-rate * D (cy y))) (y : Yt) :
    ‖g y‖ ≤ (fac * Real.exp rate) *
      Real.exp (-(rate / C) * ((cy y).card : ℝ)) := by
  have hlow : ((cy y).card : ℝ) / C - 1 ≤ D (cy y) := by
    have htmp : ((cy y).card : ℝ) / C ≤ 1 + D (cy y) :=
      (div_le_iff₀ hC).2 (by simpa only [mul_comm] using hsize y)
    linarith
  have hE : Real.exp (-rate * D (cy y)) ≤
      Real.exp rate * Real.exp (-(rate / C) * ((cy y).card : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := mul_nonneg hrate (sub_nonneg.mpr hlow)
    calc
      -rate * D (cy y) ≤ -rate * (((cy y).card : ℝ) / C - 1) := by
        nlinarith
      _ = rate + -(rate / C) * ((cy y).card : ℝ) := by ring
  calc
    ‖g y‖ ≤ fac * Real.exp (-rate * D (cy y)) := hmod y
    _ ≤ fac * (Real.exp rate * Real.exp (-(rate / C) * ((cy y).card : ℝ))) :=
      mul_le_mul_of_nonneg_left hE hfac
    _ = (fac * Real.exp rate) *
        Real.exp (-(rate / C) * ((cy y).card : ℝ)) := by ring

/-- If a raw one-block operator has the Gaussian tail bound, division by the small-block
probability costs at most a factor two. `hRaw` is supplied by the landed Gaussian tail
estimate after the physical operator is identified with that one-block integral. -/
theorem normalized_heavy_bound_of_raw_tail
    {Zt : Type*} (raw τ : Zt → ℂ) (q : Zt → ℝ)
    {b P H t : ℝ}
    (hq : ∀ z, 1 / 2 ≤ q z)
    (hNorm : ∀ z, τ z = raw z / (q z : ℂ))
    (hRaw : ∀ z, ‖raw z‖ ≤ Real.exp b * t)
    (hExponent : 2 * Real.exp b * t ≤ Real.exp (-P - H)) (z : Zt) :
    ‖τ z‖ ≤ Real.exp (-P - H) := by
  have hqpos : 0 < q z := by linarith [hq z]
  have hqnorm : ‖(q z : ℂ)‖ = q z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
  rw [hNorm z, norm_div, hqnorm]
  have h1 : ‖raw z‖ / q z ≤ 2 * ‖raw z‖ := by
    apply (div_le_iff₀ hqpos).2
    nlinarith [norm_nonneg (raw z), hq z]
  calc
    ‖raw z‖ / q z ≤ 2 * ‖raw z‖ := h1
    _ ≤ 2 * (Real.exp b * t) := by gcongr; exact hRaw z
    _ ≤ Real.exp (-P - H) := by simpa only [mul_assoc] using hExponent

/-- The one-block raw operator is bounded by the landed Gaussian tail estimate. Its field
index is the set of sites in that block, so no outside-small restriction is present. -/
theorem raw_one_block_integral_tail_bound
    {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {ρ b : ℝ} (hρ : 0 ≤ ρ) (F : (ι → W) → ℂ)
    (hF : ∀ ψ ∈ {ψ : ι → W | ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖},
      ‖F ψ‖ ≤ Real.exp b) :
    ‖∫ ψ in {ψ : ι → W | ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖},
        F ψ ∂(pdGaussian ι W)‖ ≤
      Real.exp b * ((Fintype.card ι : ℝ) *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := pdGaussian ι W)
    (s := {ψ : ι → W | ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖})
    (C := Real.exp b)
    ((measure_mono (Set.subset_univ _)).trans_lt
      (by rw [pdGaussian_univ]; exact ENNReal.one_lt_top)) hF
  refine h1.trans ?_
  rw [Measure.real]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos b).le
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (pdGaussian_tail_exists_le (ι := ι) (W := W) Finset.univ hρ)
  rwa [ENNReal.toReal_ofReal (by positivity)] at ht

/-- The explicit logarithmic budget pays the Gaussian tail, the block cardinality, and the
factor two from normalization. -/
theorem normalized_one_block_exponent_of_log_budget
    {ι W : Type*} [Fintype ι] [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {mStar : ℕ} (hmStar : 1 ≤ mStar) (hcard : Fintype.card ι ≤ mStar)
    {ρ b P H : ℝ}
    (hBudget : b + P + H ≤ ρ ^ 2 / 4 - Real.log (2 * mStar) -
      (Module.finrank ℝ W : ℝ) / 2 * Real.log 2) :
    2 * Real.exp b * ((Fintype.card ι : ℝ) *
      (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) ≤
      Real.exp (-P - H) := by
  have hm0 : (0 : ℝ) < 2 * mStar := by exact_mod_cast (by omega : 0 < 2 * mStar)
  have hc : (Fintype.card ι : ℝ) ≤ mStar := by exact_mod_cast hcard
  have hp : (2 : ℝ) ^ ((Module.finrank ℝ W : ℝ) / 2) =
      Real.exp ((Module.finrank ℝ W : ℝ) / 2 * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  have heq : ((2 * mStar : ℕ) : ℝ) *
      (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)) =
      Real.exp (-(ρ ^ 2 / 4 - Real.log (2 * mStar) -
        (Module.finrank ℝ W : ℝ) / 2 * Real.log 2)) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, hp]
    have hlog : Real.exp (Real.log (2 * (mStar : ℝ))) = 2 * (mStar : ℝ) :=
      Real.exp_log hm0
    conv_lhs => rw [← hlog]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    2 * Real.exp b * ((Fintype.card ι : ℝ) *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) =
      Real.exp b * ((2 * (Fintype.card ι : ℝ)) *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by ring
    _ ≤ Real.exp b * (((2 * mStar : ℕ) : ℝ) *
        (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) := by
      gcongr
      exact_mod_cast (Nat.mul_le_mul_left 2 hcard)
    _ = Real.exp b * Real.exp (-(ρ ^ 2 / 4 - Real.log (2 * mStar) -
        (Module.finrank ℝ W : ℝ) / 2 * Real.log 2)) := by rw [heq]
    _ ≤ Real.exp (-P - H) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith

/-- The normalized one-block heavy activity from the landed Gaussian tail. The remaining
numerical premise is exactly the exponent comparison after paying the factor two for the
small-block probability. -/
theorem normalized_one_block_integral_bound
    {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {ρ b P H q : ℝ} (hρ : 0 ≤ ρ) (hq : 1 / 2 ≤ q)
    (F : (ι → W) → ℂ)
    (hF : ∀ ψ ∈ {ψ : ι → W | ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖},
      ‖F ψ‖ ≤ Real.exp b)
    (τ : ℂ)
    (hτ : τ = (∫ ψ in {ψ : ι → W |
        ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖}, F ψ ∂(pdGaussian ι W)) / (q : ℂ))
    (hExponent : 2 * Real.exp b * ((Fintype.card ι : ℝ) *
      (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) ≤
      Real.exp (-P - H)) :
    ‖τ‖ ≤ Real.exp (-P - H) := by
  have hRaw := raw_one_block_integral_tail_bound hρ F hF
  exact normalized_heavy_bound_of_raw_tail
    (raw := fun _ : Unit => ∫ ψ in {ψ : ι → W |
      ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖}, F ψ ∂(pdGaussian ι W))
    (τ := fun _ : Unit => τ) (q := fun _ : Unit => q)
    (fun _ => hq) (fun _ => hτ) (fun _ => hRaw) hExponent ()

/-- The Gaussian heavy activity with the explicit exponent budget of Part 2: the radius
`ρ` beats `b + P + H` after paying for the block size, field dimension, and normalization. -/
theorem normalized_one_block_integral_bound_of_log_budget
    {ι W : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {mStar : ℕ} (hmStar : 1 ≤ mStar) (hcard : Fintype.card ι ≤ mStar)
    {ρ b P H q : ℝ} (hρ : 0 ≤ ρ) (hq : 1 / 2 ≤ q)
    (F : (ι → W) → ℂ)
    (hF : ∀ ψ ∈ {ψ : ι → W | ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖},
      ‖F ψ‖ ≤ Real.exp b)
    (τ : ℂ)
    (hτ : τ = (∫ ψ in {ψ : ι → W |
        ∃ x ∈ (Finset.univ : Finset ι), ρ < ‖ψ x‖}, F ψ ∂(pdGaussian ι W)) / (q : ℂ))
    (hBudget : b + P + H ≤ ρ ^ 2 / 4 - Real.log (2 * mStar) -
      (Module.finrank ℝ W : ℝ) / 2 * Real.log 2) :
    ‖τ‖ ≤ Real.exp (-P - H) := by
  exact normalized_one_block_integral_bound hρ hq F hF τ hτ
    (normalized_one_block_exponent_of_log_budget hmStar hcard hBudget)

end Balaban.Green
