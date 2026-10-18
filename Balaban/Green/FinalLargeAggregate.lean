/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLargeActivation

/-!
# Absolute fixed-footprint Mayer bound

The positive cluster majorant in the proof of `mayer_activity_bound` also bounds the sum of
the absolute values of all connected-cluster integrals with a fixed charged footprint.
Consequently a coverage coefficient aggregated at fixed footprint and activation subset
inherits the same estimate. The small-potential hypotheses of Mayer's theorem are explicit.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban.Polymer

namespace Balaban.Green

/-- The sum of absolute connected-cluster coefficients at one footprint has the same
positive majorant used internally by `mayer_activity_bound`. -/
theorem mayer_absolute_cluster_sum_bound
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (H : T → (∀ b, Ω b) → ℂ)
    (dist : Finset B → ℝ) {H0 κ0 κ1 c K0 c1 : ℝ}
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2)
    (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hdist : ∀ Y, 0 ≤ dist Y) (hne : ∀ t, (foot t).Nonempty)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * dist (foot t)))
    (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ foot t),
      Real.exp (-κ0 * dist (foot t)) ≤ K0)
    (hG3 : ∀ C : Finset T, ConnSet foot C →
      dist (unionCs foot C) ≤ ∑ t ∈ C, dist (foot t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (Y : NePoly B) (hG1 : (Y.1.card : ℝ) ≤ c1 * (1 + dist Y.1)) :
    ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
      ‖∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖ ≤
        2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 *
          Real.exp (-(κ1 - 3 / 2) * dist Y.1) := by
  obtain ⟨b0, hb0⟩ := Y.2
  have hK0 : 0 ≤ K0 :=
    le_trans (Finset.sum_nonneg (fun t _ => (Real.exp_pos _).le)) (hG2 b0)
  set q := 2 * H0 * K0 * Real.exp (κ1 * c) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hρ : ∀ t, 0 ≤ mayerRho foot dist κ0 H0 t :=
    mayerRho_nonneg (sup := foot) (d := dist) (κ0 := κ0) hH0
  have hr0 : ∀ t, 0 ≤ mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c) := fun t =>
    mul_nonneg (hρ t) (Real.exp_pos _).le
  have hpre : 0 ≤ Real.exp (-κ1 * dist Y.1) * Real.exp (-κ1 * c) := by positivity
  have hcluster : ∀ C : Finset T,
      ‖∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖ ≤
        ∏ t ∈ C, (mayerRho foot dist κ0 H0 t *
          Real.exp (-κ1 * dist (foot t))) := by
    intro C
    have hpoint : ∀ Φ : ∀ b, Ω b,
        ‖∏ t ∈ C, (Complex.exp (H t Φ) - 1)‖ ≤
          ∏ t ∈ C, (mayerRho foot dist κ0 H0 t *
            Real.exp (-κ1 * dist (foot t))) := by
      intro Φ
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun t _ => norm_nonneg _)
        (fun t _ => norm_expm1_le_rho (sup := foot) (H := H) (d := dist)
          hH0 hH0' hκ0 hκ1 hdist t Φ (hH t Φ))
    have hbound := norm_integral_le_of_norm_le_const (μ := Measure.pi μ)
      (Filter.Eventually.of_forall hpoint)
    simpa using hbound
  calc
    ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
        ‖∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖
      ≤ ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
          ∏ t ∈ C, (mayerRho foot dist κ0 H0 t *
            Real.exp (-κ1 * dist (foot t))) :=
        Finset.sum_le_sum (fun C _ => hcluster C)
    _ ≤ ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
          Real.exp (-κ1 * dist Y.1) * Real.exp (-κ1 * c) *
            ∏ t ∈ C, (mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c)) :=
        Finset.sum_le_sum (fun C hC => by
          have h := mem_Cfam.mp hC
          have hp := prod_a_le hκ1 hρ hG3 h.1
          rwa [h.2.2] at hp)
    _ = Real.exp (-κ1 * dist Y.1) * Real.exp (-κ1 * c) *
          ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
            ∏ t ∈ C, (mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c)) := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (-κ1 * dist Y.1) * Real.exp (-κ1 * c) *
          (Real.exp (∑ t ∈ termsIn foot Y.1,
            mayerRho foot dist κ0 H0 t * Real.exp (κ1 * c)) - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hpre
        refine le_trans ?_ (sum_powerset_erase_le _ hr0 (termsIn foot Y.1))
        exact Finset.sum_le_sum_of_subset_of_nonneg cfam_subset_powerset
          (fun _ _ _ => Finset.prod_nonneg (fun t _ => hr0 t))
    _ ≤ Real.exp (-κ1 * dist Y.1) * Real.exp (-κ1 * c) *
          (Real.exp (q * Y.1.card) - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hpre
        have hs := sum_rho_le (sup := foot) (d := dist) (κ0 := κ0)
          (κ1 := κ1) (c := c) hH0 (Y := Y.1) (fun t _ => hne t) hG2
        have he := Real.exp_le_exp.mpr hs
        dsimp only [q]
        linarith
    _ ≤ _ := mayer_real_bound (q := q) (c1 := c1) (κ1 := κ1) (c := c)
      (D := dist Y.1) (n := (Y.1.card : ℝ)) hq0 hc1 hκ1 hc (hdist _)
      (Nat.cast_nonneg _) hq hG1

/-- Summing all clusters with a fixed parent footprint and coverage subset preserves the
absolute Mayer bound; this is the coefficient shape required by the linked coverage gas. -/
theorem coverage_aggregate_coefficient_bound
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (act : T → B)
    (H : T → (∀ b, Ω b) → ℂ)
    (dist : Finset B → ℝ) {H0 κ0 κ1 c K0 c1 : ℝ}
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2)
    (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hdist : ∀ Y, 0 ≤ dist Y) (hne : ∀ t, (foot t).Nonempty)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * dist (foot t)))
    (hG2 : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t => b ∈ foot t),
      Real.exp (-κ0 * dist (foot t)) ≤ K0)
    (hG3 : ∀ C : Finset T, ConnSet foot C →
      dist (unionCs foot C) ≤ ∑ t ∈ C, dist (foot t) + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (Y : NePoly B) (hG1 : (Y.1.card : ℝ) ≤ c1 * (1 + dist Y.1))
    (S : Finset B) :
    ‖(((-1 : ℤ) ^ (S.card + 1) : ℂ) *
      ∑ C ∈ (Cfam foot (fun _ : Finset T => True) Y.1).filter
        (fun C => S ⊆ C.image act),
        ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ))‖ ≤
      2 * (2 * H0 * K0 * Real.exp (κ1 * c)) * c1 *
        Real.exp (-(κ1 - 3 / 2) * dist Y.1) := by
  have hfull := mayer_absolute_cluster_sum_bound μ foot H dist hH0 hH0' hκ0 hκ1 hc
    hdist hne hH hG2 hG3 hc1 hq Y hG1
  have hsign : ‖(((-1 : ℤ) ^ (S.card + 1) : ℂ))‖ = 1 := by simp
  rw [norm_mul, hsign, one_mul]
  calc
    ‖∑ C ∈ (Cfam foot (fun _ : Finset T => True) Y.1).filter
        (fun C => S ⊆ C.image act),
        ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖
      ≤ ∑ C ∈ (Cfam foot (fun _ : Finset T => True) Y.1).filter
          (fun C => S ⊆ C.image act),
          ‖∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
          ‖∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => norm_nonneg _)
    _ ≤ _ := hfull

end Balaban.Green
