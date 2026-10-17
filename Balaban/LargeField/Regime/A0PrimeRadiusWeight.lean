/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Regime.A0PrimeWeight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The thin transverse radius for the exact mass weight

The source radius is expressed in the dimensionless field variable `h = b / μ`.  The condition
`β μ ∑ (Im h_i)^2 ≤ c²` is the imaginary part of the physical-source tube
`|b - μ h₀|₂ ≤ c √(μ / β)`.  The full complex-disc estimate and the one-coordinate obstruction
are stated separately: no estimate for normalized fluctuation activities is inferred here.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The landed mass-weight inequality on the thin source radius, with its exact per-site constant.
The condition is written in the field variable so it applies to any real centre. -/
theorem raw_mass_weight_bound_thin {ι : Type*} {N : ℕ} (C : Finset ι)
    (φ : ι → Fin N → ℝ) (h : Fin N → ℂ) {μ β c : ℝ}
    (hμ : 0 ≤ μ) (hβ : 0 ≤ β)
    (hsource : β * μ * ∑ i, (h i).im ^ 2 ≤ c ^ 2) :
    ‖Complex.exp (-((β : ℂ) * ((((μ) / 2 : ℝ) : ℂ) *
      ∑ x ∈ C, ∑ i, ((((φ) x i : ℝ) : ℂ) - h i) ^ 2)))‖ ≤
      Real.exp (c ^ 2 * C.card / 2) := by
  have hweight := norm_exp_neg_massTermC_le μ β hμ hβ C φ h
  refine hweight.trans (Real.exp_le_exp.mpr ?_)
  have hn : 0 ≤ (C.card : ℝ) / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hsource hn]

/-- The same bound in the physical source increment `q = b - μ h₀`.
The squared radius `c² μ / β` is the square of `c √(μ / β)`. -/
theorem raw_mass_weight_bound_source_disc {ι : Type*} {N : ℕ} (C : Finset ι)
    (φ : ι → Fin N → ℝ) (h₀ : Fin N → ℝ) (q : Fin N → ℂ)
    {μ β c : ℝ} (hμ : 0 < μ) (hβ : 0 < β)
    (hq : (∑ i, ‖q i‖ ^ 2) ≤ c ^ 2 * μ / β) :
    ‖Complex.exp (-((β : ℂ) * ((((μ) / 2 : ℝ) : ℂ) *
      ∑ x ∈ C, ∑ i, ((((φ) x i : ℝ) : ℂ) - ((h₀ i : ℂ) + q i / μ)) ^ 2)))‖ ≤
      Real.exp (c ^ 2 * C.card / 2) := by
  have him : ∀ i, ((h₀ i : ℂ) + q i / μ).im = (q i).im / μ := by
    intro i
    simp [Complex.add_im, Complex.div_ofReal_im]
  have hcoord : ∀ i, (q i).im ^ 2 ≤ ‖q i‖ ^ 2 := by
    intro i
    nlinarith [Complex.sq_norm_sub_sq_im (q i), sq_nonneg (q i).re]
  have hsum : (∑ i, (q i).im ^ 2) ≤ c ^ 2 * μ / β :=
    (Finset.sum_le_sum fun i _ => hcoord i).trans hq
  have hs : β * μ * ∑ i, (((h₀ i : ℂ) + q i / μ).im) ^ 2 ≤ c ^ 2 := by
    simp only [him]
    have hm2 : 0 ≤ β / μ := by positivity
    have hp := mul_le_mul_of_nonneg_left hsum hm2
    have he : β * μ * ∑ i, ((q i).im / μ) ^ 2 =
        (β / μ) * ∑ i, (q i).im ^ 2 := by
      calc
        _ = ∑ i, β * μ * ((q i).im / μ) ^ 2 := by rw [Finset.mul_sum]
        _ = ∑ i, (β / μ) * (q i).im ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          field_simp
        _ = _ := by rw [Finset.mul_sum]
    have hcancel : β / μ * (c ^ 2 * μ / β) = c ^ 2 := by
      field_simp
    rw [he]
    simpa [hcancel] using hp
  exact raw_mass_weight_bound_thin C φ (fun i => (h₀ i : ℂ) + q i / μ) hμ.le hβ.le hs

/-- Exact modulus on an imaginary transverse coordinate of the one-site mass weight. -/
theorem raw_transverse_imaginary_norm (β m t : ℝ) :
    ‖Complex.exp (-((β : ℂ) * (((t : ℂ) * Complex.I) ^ 2 / (2 * m))))‖ =
      Real.exp (β * t ^ 2 / (2 * m)) := by
  have hs : ((t : ℂ) * Complex.I) ^ 2 = -((t ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  have he : -((β : ℂ) * (((t : ℂ) * Complex.I) ^ 2 / (2 * m))) =
      ((β * t ^ 2 / (2 * m) : ℝ) : ℂ) := by
    rw [hs]
    push_cast
    ring
  rw [he, Complex.norm_exp]
  norm_cast

/-- The scalar example is exactly the raw mass factor of a unit spin at `e₁` in two
components, displaced in the transverse `e₂` source coordinate. -/
theorem raw_unit_spin_transverse_norm (β μ t : ℝ) :
    ‖Complex.exp (-((β : ℂ) * (((μ / 2 : ℝ) : ℂ) *
      ∑ i : Fin 2,
        ((((if i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) -
          (((if i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) -
          (if i = 1 then (t : ℂ) * Complex.I else 0) / μ) ^ 2)))‖ =
      Real.exp (β * t ^ 2 / (2 * μ)) := by
  have he : (((μ / 2 : ℝ) : ℂ) *
      ∑ i : Fin 2,
        ((((if i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) -
          (((if i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) -
          (if i = 1 then (t : ℂ) * Complex.I else 0) / μ) ^ 2) =
      (((t : ℂ) * Complex.I) ^ 2 / (2 * μ)) := by
    simp [Fin.sum_univ_two]
    field_simp
  rw [he]
  exact raw_transverse_imaginary_norm β μ t

/-- No constant bounds the raw one-site transverse weight on a source disc with squared radius
`c² / β` when `β μ ≤ 1`.  Here `q = i t` is one transverse coordinate of an `N = 2` spin,
and the real background spin equals the source centre.  The condition `β t² < c²` is equivalent
to `|q| < c / √β` for positive `β, c, t`. -/
theorem raw_transverse_no_uniform_wide_disc {c : ℝ} (hc : 0 < c) (B M : ℝ) :
    ∃ β μ t : ℝ, B ≤ β ∧ 0 < β ∧ 0 < μ ∧ β * μ = 1 ∧ 0 < t ∧ β * t ^ 2 < c ^ 2 ∧
      Real.exp M <
        ‖Complex.exp (-((β : ℂ) * (((t : ℂ) * Complex.I) ^ 2 / (2 * μ))))‖ := by
  let s : ℝ := 1 + |B| + 8 * (|M| + 1) / c ^ 2
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hs : 1 ≤ s := by
    have hh : 0 ≤ 8 * (|M| + 1) / c ^ 2 := by positivity
    dsimp [s]
    linarith [abs_nonneg B]
  have hs0 : 0 < s := by linarith
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs0
  have hsB : |B| ≤ s := by
    have hh : 0 ≤ 8 * (|M| + 1) / c ^ 2 := by positivity
    dsimp [s]
    linarith
  have hid : c ^ 2 * s / 8 = c ^ 2 * (1 + |B|) / 8 + |M| + 1 := by
    dsimp [s]
    field_simp
    ring
  have hss : s ≤ s ^ 2 := by nlinarith
  have hmono := mul_le_mul_of_nonneg_left hss (show 0 ≤ c ^ 2 / 8 by positivity)
  have hbig : M < c ^ 2 * s ^ 2 / 8 := by
    have hM : M < c ^ 2 * s / 8 := by
      rw [hid]
      have hh : 0 ≤ c ^ 2 * (1 + |B|) / 8 := by positivity
      linarith [le_abs_self M]
    linarith
  refine ⟨s ^ 2, 1 / s ^ 2, c / (2 * s), ?_, hs2, by positivity, ?_, by positivity, ?_, ?_⟩
  · nlinarith [le_abs_self B, hsB, hss]
  · field_simp
  · have hdisc : s ^ 2 * (c / (2 * s)) ^ 2 = c ^ 2 / 4 := by
      field_simp
      ring
    rw [hdisc]
    nlinarith
  · rw [raw_transverse_imaginary_norm]
    have hex : s ^ 2 * (c / (2 * s)) ^ 2 / (2 * (1 / s ^ 2)) =
        c ^ 2 * s ^ 2 / 8 := by
      field_simp
      ring
    rw [hex]
    exact Real.exp_lt_exp.mpr hbig

/-- The wider disc has no uniform raw-weight bound even for one `N = 2` hard spin.
The spin and real centre in the displayed sum are both the unit vector `e₁`. -/
theorem raw_unit_spin_no_uniform_wide_disc {c : ℝ} (hc : 0 < c) (B M : ℝ) :
    ∃ β μ t : ℝ, B ≤ β ∧ 0 < β ∧ 0 < μ ∧ β * μ = 1 ∧ 0 < t ∧ β * t ^ 2 < c ^ 2 ∧
      Real.exp M <
        ‖Complex.exp (-((β : ℂ) * (((μ / 2 : ℝ) : ℂ) *
          ∑ i : Fin 2,
            ((((if i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) -
              (((if i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ) -
              (if i = 1 then (t : ℂ) * Complex.I else 0) / μ) ^ 2)))‖ := by
  obtain ⟨β, μ, t, hB, hβ, hμ, hβμ, ht, hdisc, hbig⟩ :=
    raw_transverse_no_uniform_wide_disc hc B M
  refine ⟨β, μ, t, hB, hβ, hμ, hβμ, ht, hdisc, ?_⟩
  rw [raw_unit_spin_transverse_norm]
  rw [raw_transverse_imaginary_norm] at hbig
  exact hbig

end Balaban.LargeField
